use cordis::diagnostics::Blocker;
use cordis::runtime::static_host::{StaticFuture, StaticPlugin};
use cordis::{
    AsyncSetup, CallbackResult, Context, Effect, Inverse, Plugin, Runtime, RuntimeError, ServiceKey,
};
use cordis_kernel::Phase;
use std::future::Future;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::task::{Context as TaskContext, Poll, Waker};

fn poll(runtime: &mut Runtime) -> Poll<Result<(), RuntimeError>> {
    let mut settle = std::pin::pin!(runtime.settle());
    settle
        .as_mut()
        .poll(&mut TaskContext::from_waker(Waker::noop()))
}
fn poll_static(future: &mut StaticFuture) -> Poll<CallbackResult> {
    future
        .as_mut()
        .poll(&mut TaskContext::from_waker(Waker::noop()))
}
async fn gate(open: Arc<AtomicBool>) {
    std::future::poll_fn(move |_| {
        if open.load(Ordering::SeqCst) {
            Poll::Ready(())
        } else {
            Poll::Pending
        }
    })
    .await
}

#[test]
fn failed_retryable_cleanup_pins_provider_and_resumes_lifo_without_replaying_success() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let service = ServiceKey::<usize>::new("dependency");
    let log = Arc::new(Mutex::new(Vec::new()));
    let output = log.clone();
    let provider = runtime
        .mount(
            &context,
            None,
            Plugin::new("provider", move |setup| {
                setup.provide(service, 42)?;
                let output = output.clone();
                setup.on_cleanup(move || {
                    output.lock().unwrap().push("provider");
                    Ok(())
                });
                Ok(())
            })
            .provides(service),
        )
        .unwrap();
    let output = log.clone();
    let consumer = runtime
        .mount(
            &context,
            None,
            Plugin::new("consumer", move |setup| {
                let earlier = output.clone();
                setup.on_cleanup(move || {
                    earlier.lock().unwrap().push("earlier");
                    Ok(())
                });
                let output = output.clone();
                let context = setup.to_async();
                let mut attempt = 0;
                setup.on_cleanup_retryable(move || {
                    assert_eq!(*context.get(service)?, 42);
                    attempt += 1;
                    output
                        .lock()
                        .unwrap()
                        .push(if attempt == 1 { "failed" } else { "recovered" });
                    if attempt == 1 {
                        Err("try again".into())
                    } else {
                        Ok(())
                    }
                });
                Ok(())
            })
            .requires(service),
        )
        .unwrap();
    assert_eq!(poll(&mut runtime), Poll::Ready(Ok(())));
    let output = log.clone();
    runtime
        .on_cleanup(consumer, move || {
            output.lock().unwrap().push("later");
            Ok(())
        })
        .unwrap();
    assert!(runtime.retry_cleanup(consumer).is_err());
    runtime.dispose_all().unwrap();
    assert!(
        matches!(poll(&mut runtime), Poll::Ready(Err(RuntimeError::Cleanup { plugin, .. })) if plugin == consumer)
    );
    assert_eq!(*log.lock().unwrap(), ["later", "failed"]);
    assert_eq!(runtime.committed(consumer)[0].provider, provider);
    assert!(!runtime.cleanup_started(provider));
    assert!(runtime
        .snapshot()
        .plugins
        .iter()
        .find(|p| p.id == consumer)
        .unwrap()
        .blockers
        .iter()
        .any(|b| matches!(b, Blocker::CleanupFailed(_))));
    assert!(matches!(
        poll(&mut runtime),
        Poll::Ready(Err(RuntimeError::Cleanup { .. }))
    ));
    assert_eq!(*log.lock().unwrap(), ["later", "failed"]);
    runtime.retry_cleanup(consumer).unwrap();
    assert!(runtime.retry_cleanup(consumer).is_err());
    assert_eq!(poll(&mut runtime), Poll::Ready(Ok(())));
    assert_eq!(
        *log.lock().unwrap(),
        ["later", "failed", "recovered", "earlier", "provider"]
    );
    assert!(!runtime.contains(provider));
    assert!(!runtime.contains(consumer));
    assert_eq!(runtime.take_cleanup_errors().len(), 1);
}

#[test]
fn pending_retry_future_survives_dropped_settle_and_accepts_a_late_inverse() {
    let mut runtime = Runtime::new();
    let count = Arc::new(AtomicUsize::new(0));
    let open = Arc::new(AtomicBool::new(false));
    let retained = Arc::new(Mutex::new(None::<AsyncSetup>));
    let (calls, ready, capture) = (count.clone(), open.clone(), retained.clone());
    let id = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new("async retry", move |setup| {
                *capture.lock().unwrap() = Some(setup.to_async());
                let (calls, ready) = (calls.clone(), ready.clone());
                setup.on_cleanup_retryable_async(move || {
                    let attempt = calls.fetch_add(1, Ordering::SeqCst);
                    let ready = ready.clone();
                    async move {
                        if attempt == 0 {
                            return Err("offline".into());
                        }
                        gate(ready).await;
                        Ok(())
                    }
                });
                Ok(())
            }),
        )
        .unwrap();
    assert_eq!(poll(&mut runtime), Poll::Ready(Ok(())));
    runtime.dispose(id).unwrap();
    assert!(matches!(
        poll(&mut runtime),
        Poll::Ready(Err(RuntimeError::Cleanup { .. }))
    ));
    runtime.retry_cleanup(id).unwrap();
    assert_eq!(poll(&mut runtime), Poll::Pending);
    assert_eq!(poll(&mut runtime), Poll::Pending);
    assert_eq!(count.load(Ordering::SeqCst), 2);
    assert!(runtime.retry_cleanup(id).is_err());
    let late = Arc::new(AtomicUsize::new(0));
    let counter = late.clone();
    retained
        .lock()
        .unwrap()
        .as_ref()
        .unwrap()
        .on_cleanup(move || {
            counter.fetch_add(1, Ordering::SeqCst);
            Ok(())
        })
        .unwrap();
    open.store(true, Ordering::SeqCst);
    assert_eq!(poll(&mut runtime), Poll::Ready(Ok(())));
    assert_eq!(late.load(Ordering::SeqCst), 1);
    assert_eq!(count.load(Ordering::SeqCst), 2);
    assert!(!runtime.contains(id));
}

#[test]
fn retryable_factory_and_future_panics_retain_the_same_factory_for_explicit_retry() {
    for factory_panic in [false, true] {
        let count = Arc::new(AtomicUsize::new(0));
        let calls = count.clone();
        let mut runtime = Runtime::new();
        let id = runtime
            .mount(
                &Context::new(),
                None,
                Plugin::new("panic retry", move |setup| {
                    let calls = calls.clone();
                    setup.on_cleanup_retryable_async(move || {
                        let first = calls.fetch_add(1, Ordering::SeqCst) == 0;
                        assert!(!(first && factory_panic), "factory panic");
                        async move {
                            assert!(!first, "future panic");
                            Ok(())
                        }
                    });
                    Ok(())
                }),
            )
            .unwrap();
        assert_eq!(poll(&mut runtime), Poll::Ready(Ok(())));
        runtime.dispose(id).unwrap();
        assert!(matches!(
            poll(&mut runtime),
            Poll::Ready(Err(RuntimeError::Cleanup { .. }))
        ));
        assert!(runtime.cleanup_failure(id).unwrap().contains("panic"));
        runtime.retry_cleanup(id).unwrap();
        assert_eq!(poll(&mut runtime), Poll::Ready(Ok(())));
        assert_eq!(count.load(Ordering::SeqCst), 2);
    }
}

#[test]
fn failed_effect_disposal_withdraws_owner_and_keeps_earlier_inverses_until_retry() {
    let mut runtime = Runtime::new();
    let handle = Arc::new(Mutex::new(None));
    let saved = handle.clone();
    let attempts = Arc::new(AtomicUsize::new(0));
    let calls = attempts.clone();
    let earlier = Arc::new(AtomicUsize::new(0));
    let early = earlier.clone();
    let id = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new("effect retry", move |setup| {
                let (calls, early) = (calls.clone(), early.clone());
                let effect = Effect::new()
                    .inverse(Inverse::new(move || {
                        early.fetch_add(1, Ordering::SeqCst);
                        Ok(())
                    }))
                    .inverse(Inverse::retryable(move || {
                        if calls.fetch_add(1, Ordering::SeqCst) == 0 {
                            Err("effect retry".into())
                        } else {
                            Ok(())
                        }
                    }));
                *saved.lock().unwrap() = Some(setup.effect(effect)?);
                Ok(())
            }),
        )
        .unwrap();
    assert_eq!(poll(&mut runtime), Poll::Ready(Ok(())));
    let handle = handle.lock().unwrap().clone().unwrap();
    handle.dispose();
    assert!(matches!(
        poll(&mut runtime),
        Poll::Ready(Err(RuntimeError::Cleanup { .. }))
    ));
    assert_eq!(runtime.phase(id), Some(Phase::Unloading));
    assert!(!handle.finished());
    assert_eq!(earlier.load(Ordering::SeqCst), 0);
    runtime.dispose(id).unwrap();
    runtime.retry_cleanup(id).unwrap();
    assert_eq!(poll(&mut runtime), Poll::Ready(Ok(())));
    assert!(handle.finished());
    assert_eq!(attempts.load(Ordering::SeqCst), 2);
    assert_eq!(earlier.load(Ordering::SeqCst), 1);
}

#[test]
fn retry_waits_for_other_running_callbacks_before_issuing_a_new_episode_attempt() {
    let mut runtime = Runtime::new();
    let open = Arc::new(AtomicBool::new(false));
    let ready = open.clone();
    let count = Arc::new(AtomicUsize::new(0));
    let calls = count.clone();
    let id = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new("concurrent cleanup", move |setup| {
                let calls = calls.clone();
                setup.on_cleanup_retryable(move || {
                    if calls.fetch_add(1, Ordering::SeqCst) == 0 {
                        Err("root failed".into())
                    } else {
                        Ok(())
                    }
                });
                let ready = ready.clone();
                setup.effect(
                    Effect::new().inverse(Inverse::new_async(move || async move {
                        gate(ready).await;
                        Ok(())
                    })),
                )?;
                Ok(())
            }),
        )
        .unwrap();
    assert_eq!(poll(&mut runtime), Poll::Ready(Ok(())));
    runtime.dispose(id).unwrap();
    assert!(matches!(
        poll(&mut runtime),
        Poll::Ready(Err(RuntimeError::Cleanup { .. }))
    ));
    assert!(runtime.retry_cleanup(id).is_err());
    assert_eq!(count.load(Ordering::SeqCst), 1);
    open.store(true, Ordering::SeqCst);
    assert!(matches!(
        poll(&mut runtime),
        Poll::Ready(Err(RuntimeError::Cleanup { .. }))
    ));
    runtime.retry_cleanup(id).unwrap();
    assert_eq!(poll(&mut runtime), Poll::Ready(Ok(())));
    assert_eq!(count.load(Ordering::SeqCst), 2);
}

#[test]
fn shutdown_reports_retained_cleanup_failure_without_implicitly_retrying_it() {
    let mut runtime = Runtime::new();
    let count = Arc::new(AtomicUsize::new(0));
    let calls = count.clone();
    let id = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new("shutdown retry", move |setup| {
                let calls = calls.clone();
                setup.on_cleanup_retryable(move || {
                    if calls.fetch_add(1, Ordering::SeqCst) == 0 {
                        Err("shutdown failed".into())
                    } else {
                        Ok(())
                    }
                });
                Ok(())
            }),
        )
        .unwrap();
    assert_eq!(poll(&mut runtime), Poll::Ready(Ok(())));
    for _ in 0..2 {
        let mut shutdown = std::pin::pin!(runtime.shutdown());
        assert!(matches!(
            shutdown
                .as_mut()
                .poll(&mut TaskContext::from_waker(Waker::noop())),
            Poll::Ready(Err(_))
        ));
    }
    assert_eq!(count.load(Ordering::SeqCst), 1);
    runtime.retry_cleanup(id).unwrap();
    let mut shutdown = std::pin::pin!(runtime.shutdown());
    assert!(matches!(
        shutdown
            .as_mut()
            .poll(&mut TaskContext::from_waker(Waker::noop())),
        Poll::Ready(Ok(()))
    ));
}

#[test]
fn static_retry_requires_explicit_admission_and_retains_values_until_success() {
    let key = ServiceKey::<usize>::new("retained value");
    let count = Arc::new(AtomicUsize::new(0));
    let calls = count.clone();
    let earlier = Arc::new(AtomicUsize::new(0));
    let early = earlier.clone();
    let mut definition = StaticPlugin::new(
        Plugin::new("static retry", move |setup| {
            setup.provide(key, 7)?;
            let early = early.clone();
            setup.on_cleanup(move || {
                early.fetch_add(1, Ordering::SeqCst);
                Ok(())
            });
            let calls = calls.clone();
            setup.on_cleanup_retryable(move || {
                if calls.fetch_add(1, Ordering::SeqCst) == 0 {
                    Err("retry static".into())
                } else {
                    Ok(())
                }
            });
            Ok(())
        })
        .provides(key),
    )
    .unwrap();
    let mut start = definition.begin(1, 1, Context::new(), vec![]).unwrap();
    assert_eq!(poll_static(&mut start.setup), Poll::Ready(Ok(())));
    assert_eq!(
        poll_static(&mut start.episode.cleanup().unwrap()),
        Poll::Ready(Err("retry static".into()))
    );
    assert!(start.episode.can_retry_cleanup());
    assert_eq!(start.episode.cleanup().err().unwrap(), "retry static");
    assert_eq!(earlier.load(Ordering::SeqCst), 0);
    assert_eq!(
        *start.episode.provided().unwrap()[0]
            .1
            .get::<usize>()
            .unwrap(),
        7
    );
    assert!(definition.begin(1, 2, Context::new(), vec![]).is_err());
    let mut retry = start.episode.retry_cleanup().unwrap();
    assert!(!start.episode.can_retry_cleanup());
    assert!(start.episode.retry_cleanup().is_err());
    assert_eq!(poll_static(&mut retry), Poll::Ready(Ok(())));
    assert_eq!(count.load(Ordering::SeqCst), 2);
    assert_eq!(earlier.load(Ordering::SeqCst), 1);
    assert!(start.episode.is_closed());
    assert!(start.episode.retry_cleanup().is_err());
}

#[test]
fn abandoning_a_pending_static_retry_never_promotes_it_to_success_or_another_retry() {
    let calls = Arc::new(AtomicUsize::new(0));
    let count = calls.clone();
    let mut definition = StaticPlugin::new(Plugin::new("abandon retry", move |setup| {
        let calls = calls.clone();
        setup.on_cleanup_retryable_async(move || {
            let attempt = calls.fetch_add(1, Ordering::SeqCst);
            async move {
                if attempt == 0 {
                    Err("first".into())
                } else {
                    std::future::pending().await
                }
            }
        });
        Ok(())
    }))
    .unwrap();
    let mut start = definition.begin(1, 1, Context::new(), vec![]).unwrap();
    assert_eq!(poll_static(&mut start.setup), Poll::Ready(Ok(())));
    assert!(matches!(
        poll_static(&mut start.episode.cleanup().unwrap()),
        Poll::Ready(Err(_))
    ));
    let mut retry = start.episode.retry_cleanup().unwrap();
    assert_eq!(poll_static(&mut retry), Poll::Pending);
    drop(retry);
    assert!(!start.episode.is_closed());
    assert!(!start.episode.can_retry_cleanup());
    assert!(start.episode.retry_cleanup().is_err());
    assert!(start.episode.cleanup().err().unwrap().contains("Abandoned"));
    assert_eq!(count.load(Ordering::SeqCst), 2);
}

struct RegisterOnDrop(AsyncSetup, Arc<AtomicUsize>);
impl Drop for RegisterOnDrop {
    fn drop(&mut self) {
        let called = self.1.clone();
        self.0
            .on_cleanup(move || {
                called.fetch_add(1, Ordering::SeqCst);
                Ok(())
            })
            .unwrap();
    }
}
#[test]
fn successful_retry_factory_is_dropped_outside_journal_locks_before_the_episode_seals() {
    let mut runtime = Runtime::new();
    let late = Arc::new(AtomicUsize::new(0));
    let counter = late.clone();
    let id = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new("reenter destructor", move |setup| {
                let dropper = RegisterOnDrop(setup.to_async(), counter.clone());
                setup.on_cleanup_retryable(move || {
                    let _keep = &dropper;
                    Ok(())
                });
                Ok(())
            }),
        )
        .unwrap();
    assert_eq!(poll(&mut runtime), Poll::Ready(Ok(())));
    runtime.dispose(id).unwrap();
    assert_eq!(poll(&mut runtime), Poll::Ready(Ok(())));
    assert_eq!(late.load(Ordering::SeqCst), 1);
}

struct CleanupCapture(&'static str, Arc<Mutex<Vec<&'static str>>>);
impl Drop for CleanupCapture {
    fn drop(&mut self) {
        self.1.lock().unwrap().push(self.0);
    }
}

#[test]
fn distinct_failed_groups_keep_their_own_factories_and_drop_each_only_after_success() {
    let calls = Arc::new(Mutex::new(Vec::new()));
    let drops = Arc::new(Mutex::new(Vec::new()));
    let (called, dropped) = (calls.clone(), drops.clone());
    let mut runtime = Runtime::new();
    let id = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new("retained payloads", move |setup| {
                for label in ["first", "second"] {
                    let calls = called.clone();
                    let captured = CleanupCapture(label, dropped.clone());
                    let mut attempt = 0;
                    setup.effect(Effect::new().inverse(Inverse::retryable(move || {
                        let _retain = &captured;
                        calls.lock().unwrap().push(captured.0);
                        attempt += 1;
                        if attempt == 1 {
                            Err(format!("{} failed", captured.0))
                        } else {
                            Ok(())
                        }
                    })))?;
                }
                Ok(())
            }),
        )
        .unwrap();
    assert_eq!(poll(&mut runtime), Poll::Ready(Ok(())));
    runtime.dispose(id).unwrap();
    assert!(matches!(
        poll(&mut runtime),
        Poll::Ready(Err(RuntimeError::Cleanup { .. }))
    ));
    assert_eq!(*calls.lock().unwrap(), ["first", "second"]);
    assert!(drops.lock().unwrap().is_empty());
    runtime.retry_cleanup(id).unwrap();
    assert!(runtime.retry_cleanup(id).is_err());
    assert!(drops.lock().unwrap().is_empty());
    assert_eq!(poll(&mut runtime), Poll::Ready(Ok(())));
    assert_eq!(
        *calls.lock().unwrap(),
        ["first", "second", "first", "second"]
    );
    assert_eq!(*drops.lock().unwrap(), ["first", "second"]);
    assert!(!runtime.contains(id));
}
