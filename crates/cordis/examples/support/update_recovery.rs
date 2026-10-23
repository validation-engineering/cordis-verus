//! Shared by the runnable example and its integration test. Fault injection is
//! an explicit raw write; plugin work uses the real managed inverse queue.
use cordis::{
    Context, Plugin, ReversibleValue, Runtime, RuntimeError, ServiceKey, ValueBranch,
    ValueOperation,
};
use serde_json::{json, Value};
use std::{
    future::Future,
    sync::{Arc, Mutex},
    task::{Context as TaskContext, Poll, Waker},
};

fn settle(runtime: &mut Runtime) -> Result<(), RuntimeError> {
    let mut future = std::pin::pin!(runtime.settle());
    match future
        .as_mut()
        .poll(&mut TaskContext::from_waker(Waker::noop()))
    {
        Poll::Ready(result) => result,
        Poll::Pending => panic!("synchronous update scenario unexpectedly needs external work"),
    }
}
fn event(log: &Arc<Mutex<Vec<String>>>, text: impl Into<String>) {
    log.lock().unwrap().push(text.into());
}
fn provider(
    key: ServiceKey<ReversibleValue>,
    value: ReversibleValue,
    version: u64,
    log: Arc<Mutex<Vec<String>>>,
) -> Plugin {
    Plugin::new(format!("provider-v{version}"), move |setup| {
        event(&log, format!("provider:{version}:setup"));
        setup.provide(key, value.clone())?;
        let value = value.clone();
        let log = log.clone();
        setup.on_cleanup(move || {
            assert_eq!(
                value.snapshot().depth(),
                0,
                "provider must wait for real inverses"
            );
            event(&log, format!("provider:{version}:release"));
            Ok(())
        });
        Ok(())
    })
    .provides(key)
}
pub fn run() -> Value {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::<ReversibleValue>::new("update-recovery.value");
    let marker = ServiceKey::<usize>::new("update-recovery.consumer");
    let first = runtime.reversible_value(10);
    let second = runtime.reversible_value(20);
    let log = Arc::new(Mutex::new(Vec::new()));
    let children = Arc::new(Mutex::new(Vec::new()));
    let provider_id = runtime
        .mount(&context, None, provider(key, first.clone(), 1, log.clone()))
        .unwrap();
    let (output, handles) = (log.clone(), children.clone());
    let consumer = runtime
        .mount(
            &context,
            None,
            Plugin::new("consumer", move |setup| {
                event(&output, "consumer:setup");
                let cleanup = output.clone();
                setup.on_cleanup(move || {
                    event(&cleanup, "consumer:restored");
                    Ok(())
                });
                setup.update_reversible(key, ValueOperation::Add(1))?;
                setup.provide(marker, 1)?;
                let child_output = output.clone();
                let handle = setup.mount(
                    Plugin::new("child", move |child| {
                        assert_eq!(*child.get(marker)?, 1);
                        event(&child_output, "child:setup");
                        let cleanup = child_output.clone();
                        child.on_cleanup(move || {
                            event(&cleanup, "child:restored");
                            Ok(())
                        });
                        child.update_reversible(key, ValueOperation::Add(2))?;
                        Ok(())
                    })
                    .requires(key)
                    .requires(marker),
                )?;
                handles.lock().unwrap().push(handle);
                Ok(())
            })
            .requires(key)
            .provides(marker),
        )
        .unwrap();
    settle(&mut runtime).unwrap();
    let child = children.lock().unwrap()[0].id().unwrap();
    assert_eq!(
        (first.snapshot().value(), first.snapshot().depth()),
        (13, 2)
    );
    assert!(runtime
        .committed(consumer)
        .iter()
        .any(|b| b.provider == provider_id));
    assert!(runtime
        .committed(child)
        .iter()
        .any(|b| b.provider == consumer));
    assert!(runtime
        .committed(child)
        .iter()
        .any(|b| b.provider == provider_id));

    let interference = first
        .apply(
            ValueOperation::Add(4),
            ValueBranch {
                matched: None,
                unmatched: None,
            },
        )
        .unwrap();
    runtime
        .update_plugin(provider_id, provider(key, second.clone(), 2, log.clone()))
        .unwrap();
    let error = settle(&mut runtime).unwrap_err();
    assert!(matches!(&error,RuntimeError::Cleanup {plugin,..} if *plugin==child));
    assert_eq!(
        (first.snapshot().value(), first.snapshot().depth()),
        (17, 3)
    );
    assert!(runtime.cleanup_failure(child).is_some());
    assert!(!runtime.cleanup_started(consumer));
    assert!(!runtime.cleanup_started(provider_id));
    assert!(runtime
        .committed(consumer)
        .iter()
        .any(|b| b.provider == provider_id));
    assert!(runtime
        .committed(child)
        .iter()
        .any(|b| b.provider == consumer));
    let blocked = log.lock().unwrap().clone();
    assert!(!blocked
        .iter()
        .any(|line| line.ends_with(":release") || line.ends_with(":restored")));
    assert!(settle(&mut runtime).is_err());
    assert_eq!(*log.lock().unwrap(), blocked);
    event(&log, "update:blocked-by-child-inverse");

    assert!(interference.inverse.restore().is_ok());
    assert_eq!(
        (first.snapshot().value(), first.snapshot().depth()),
        (13, 2)
    );
    runtime.retry_cleanup(child).unwrap();
    assert!(runtime.retry_cleanup(child).is_err());
    event(&log, "child:explicit-retry");
    settle(&mut runtime).unwrap();
    assert_eq!(
        (first.snapshot().value(), first.snapshot().depth()),
        (10, 0)
    );
    assert_eq!(
        (second.snapshot().value(), second.snapshot().depth()),
        (23, 2)
    );
    assert!(!runtime.contains(child));
    let new_child = children.lock().unwrap()[1].id().unwrap();
    assert_ne!(child, new_child);
    assert!(runtime
        .committed(new_child)
        .iter()
        .any(|b| b.provider == consumer));
    assert!(runtime
        .committed(consumer)
        .iter()
        .any(|b| b.provider == provider_id));
    let updated = log.lock().unwrap().clone();
    let index = |entry: &str| updated.iter().position(|s| s == entry).unwrap();
    assert!(index("child:restored") < index("consumer:restored"));
    assert!(index("consumer:restored") < index("provider:1:release"));
    assert!(index("provider:1:release") < index("provider:2:setup"));
    assert_eq!(
        updated
            .iter()
            .filter(|s| s.as_str() == "provider:1:release")
            .count(),
        1
    );
    runtime.dispose_all().unwrap();
    settle(&mut runtime).unwrap();
    assert!(runtime.ids().is_empty());
    assert_eq!(
        (second.snapshot().value(), second.snapshot().depth()),
        (20, 0)
    );
    json!({"schema":"cordis-verus.update-recovery-host/v1","status":"passed","proof":false,
        "provider":provider_id,"consumer":consumer,"oldChild":child,"newChild":new_child,
        "failure":error.to_string(),"oldValueRestored":10,"newValueRestored":20,
        "checks":["actual-inverse-failure","failed-child-pins-consumer-and-provider","no-implicit-retry","fresh-child-after-update","lifo-data-restoration","child-consumer-provider-release-order","final-shutdown"],
        "events":*log.lock().unwrap()})
}
