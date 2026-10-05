//! The same public lifecycle trace through the typed executor and native driver.
use cordis::{Context, Plugin, Runtime, ServiceKey};
use cordis_driver::{Driver, HostAction, ServicePort};
use std::future::Future;
use std::sync::{Arc, Mutex};
use std::task::{Context as TaskContext, Poll, Waker};

type Log = Arc<Mutex<Vec<String>>>;
fn settle(runtime: &mut Runtime) {
    assert_eq!(
        std::pin::pin!(runtime.settle())
            .as_mut()
            .poll(&mut TaskContext::from_waker(Waker::noop())),
        Poll::Ready(Ok(()))
    );
}
fn rust_trace(consumer_first: bool) -> Vec<String> {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::<u64>::new("shared-driver-trace");
    let log = Log::default();
    let seen = log.clone();
    let provider = Plugin::new("provider", move |setup| {
        seen.lock().unwrap().push("provider setup".into());
        setup.provide(key, 42)?;
        let seen = seen.clone();
        setup.on_cleanup(move || {
            seen.lock().unwrap().push("provider cleanup".into());
            Ok(())
        });
        Ok(())
    })
    .provides(key);
    let seen = log.clone();
    let consumer = Plugin::new("consumer", move |setup| {
        seen.lock()
            .unwrap()
            .push(format!("consumer setup {}", setup.get(key)?));
        let setup = setup.to_async();
        let cleanup_context = setup.clone();
        let seen = seen.clone();
        setup.on_cleanup(move || {
            seen.lock()
                .unwrap()
                .push(format!("consumer cleanup {}", cleanup_context.get(key)?));
            Ok(())
        })?;
        Ok(())
    })
    .requires(key);
    let provider_id = if consumer_first {
        runtime.mount(&context, None, consumer).unwrap();
        settle(&mut runtime);
        runtime.mount(&context, None, provider).unwrap()
    } else {
        let id = runtime.mount(&context, None, provider).unwrap();
        runtime.mount(&context, None, consumer).unwrap();
        id
    };
    settle(&mut runtime);
    runtime.restart(provider_id).unwrap();
    settle(&mut runtime);
    runtime.dispose(provider_id).unwrap();
    settle(&mut runtime);
    runtime.dispose_all().unwrap();
    settle(&mut runtime);
    let result = log.lock().unwrap().clone();
    result
}
fn native_trace(consumer_first: bool) -> Vec<String> {
    let mut driver = Driver::new().unwrap();
    let port = ServicePort { key: 1, realm: 0 };
    let mut log = Vec::new();
    let (provider, consumer) = if consumer_first {
        let consumer = driver.mount(None, vec![port], vec![]).unwrap();
        assert!(driver.drive().unwrap().is_empty());
        (driver.mount(None, vec![], vec![port]).unwrap(), consumer)
    } else {
        let provider = driver.mount(None, vec![], vec![port]).unwrap();
        (provider, driver.mount(None, vec![port], vec![]).unwrap())
    };
    let pump = |driver: &mut Driver, log: &mut Vec<String>| {
        for _ in 0..32 {
            let actions = driver.drive().unwrap();
            if actions.is_empty() {
                return;
            }
            for action in actions {
                match action {
                    HostAction::Setup { id, ticket } => {
                        if id == provider {
                            log.push("provider setup".into());
                            driver.publish(id, ticket.generation, port, 42).unwrap();
                        } else {
                            let value = driver
                                .resolve(port, Some(id), Some(ticket.generation))
                                .unwrap()
                                .unwrap();
                            log.push(format!(
                                "consumer setup {}",
                                value["value"].as_str().unwrap()
                            ));
                        }
                        driver.complete(ticket, true, None).unwrap();
                    }
                    HostAction::Cleanup { id, ticket } => {
                        if id == provider {
                            log.push("provider cleanup".into());
                        } else {
                            let value = driver
                                .resolve(port, Some(id), Some(ticket.generation))
                                .unwrap()
                                .unwrap();
                            log.push(format!(
                                "consumer cleanup {}",
                                value["value"].as_str().unwrap()
                            ));
                        }
                        driver.complete(ticket, true, None).unwrap();
                    }
                    HostAction::Removed { .. } => {}
                }
            }
        }
        panic!("driver did not settle");
    };
    pump(&mut driver, &mut log);
    driver.restart(provider).unwrap();
    pump(&mut driver, &mut log);
    driver.retire(provider).unwrap();
    pump(&mut driver, &mut log);
    driver.retire(consumer).unwrap();
    pump(&mut driver, &mut log);
    log
}

#[test]
fn dependency_restart_and_retirement_have_the_same_cross_backend_trace() {
    assert_eq!(rust_trace(false), native_trace(false));
}
#[test]
fn pending_consumer_later_provider_has_the_same_cross_backend_trace() {
    assert_eq!(rust_trace(true), native_trace(true));
}
