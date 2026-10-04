use cordis::{Context, Effect, Inverse, Phase, Plugin, Runtime, RuntimeError, ServiceKey};
use std::future::{poll_fn, Future};
use std::pin::Pin;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::task::{Context as TaskContext, Poll, Waker};

fn poll_once(runtime: &mut Runtime) -> Poll<Result<(), RuntimeError>> {
    let mut context = TaskContext::from_waker(Waker::noop());
    Pin::new(&mut runtime.settle()).poll(&mut context)
}

#[test]
fn target_drift_lands_stage_and_its_inverse_before_releasing_provider() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::<()>::new("protocol-provider");
    let log = Arc::new(Mutex::new(Vec::new()));
    let provider_log = log.clone();
    let provider = runtime
        .mount(
            &context,
            None,
            Plugin::new("provider", move |setup| {
                setup.provide(key, ())?;
                let log = provider_log.clone();
                setup.on_cleanup(move || {
                    log.lock().unwrap().push("provider-inverse");
                    Ok(())
                });
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
    let released = Arc::new(AtomicBool::new(false));
    let stage_release = released.clone();
    let stage_log = log.clone();
    let consumer = runtime
        .mount(
            &context,
            None,
            Plugin::new("consumer", move |setup| {
                let released = stage_release.clone();
                let log = stage_log.clone();
                setup.effect(
                    Effect::new()
                        .step(move |stage| async move {
                            stage.get(key)?;
                            poll_fn(|_| {
                                if released.load(Ordering::SeqCst) {
                                    Poll::Ready(())
                                } else {
                                    Poll::Pending
                                }
                            })
                            .await;
                            // The frozen committed view remains readable after
                            // target drift, through both landing and restoration.
                            stage.get(key)?;
                            log.lock().unwrap().push("stage-land");
                            Ok(Inverse::new(move || {
                                stage.get(key)?;
                                log.lock().unwrap().push("stage-inverse");
                                Ok(())
                            }))
                        })
                        .step(|_| async { panic!("continuation after target drift") }),
                )?;
                Ok(())
            })
            .requires(key),
        )
        .unwrap();
    assert_eq!(poll_once(&mut runtime), Poll::Pending);
    assert_eq!(runtime.phase(consumer), Some(Phase::Loading));
    runtime.dispose(provider).unwrap();
    assert_eq!(poll_once(&mut runtime), Poll::Pending);
    assert_eq!(runtime.phase(consumer), Some(Phase::Unloading));
    assert!(!runtime.cleanup_started(consumer));
    assert!(!runtime.cleanup_started(provider));
    assert!(log.lock().unwrap().is_empty());

    released.store(true, Ordering::SeqCst);
    assert_eq!(poll_once(&mut runtime), Poll::Ready(Ok(())));
    assert_eq!(runtime.phase(consumer), Some(Phase::Inactive));
    assert_eq!(
        *log.lock().unwrap(),
        ["stage-land", "stage-inverse", "provider-inverse"]
    );
    assert!(runtime.take_cleanup_errors().is_empty());
}
