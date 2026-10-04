use cordis::diagnostics::Blocker;
use cordis::{Context, Plugin, Runtime, ServiceKey};
use std::future::{poll_fn, Future};
use std::pin::pin;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::task::{Context as TaskContext, Poll, Waker};
fn poll<T>(f: impl Future<Output = T>) -> Poll<T> {
    let waker = Waker::noop();
    pin!(f).as_mut().poll(&mut TaskContext::from_waker(waker))
}
fn ready<T>(f: impl Future<Output = T>) -> T {
    match poll(f) {
        Poll::Ready(x) => x,
        Poll::Pending => panic!("unexpected pending"),
    }
}

#[test]
fn snapshots_identify_missing_dependency_and_provider_drain_without_payloads() {
    let mut runtime = Runtime::new();
    let ctx = Context::new();
    let key = ServiceKey::<String>::new("model");
    let release = Arc::new(AtomicBool::new(false));
    let gate = release.clone();
    let consumer = runtime
        .mount(
            &ctx,
            None,
            Plugin::new("agent\"\\\n", move |setup| {
                let bound = setup.get(key)?;
                let gate = gate.clone();
                setup.on_cleanup_async(move || async move {
                    poll_fn(|_| {
                        if gate.load(Ordering::SeqCst) {
                            Poll::Ready(())
                        } else {
                            Poll::Pending
                        }
                    })
                    .await;
                    assert_eq!(&*bound, "private payload");
                    Ok(())
                });
                Ok(())
            })
            .requires(key),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    assert!(matches!(
        &runtime.snapshot().plugins[0].blockers[..],
        [Blocker::MissingDependencies(_)]
    ));
    let provider = runtime
        .mount(
            &ctx,
            None,
            Plugin::new("model", move |setup| {
                setup.provide(key, "private payload".to_owned())?;
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    assert!(!runtime
        .snapshot()
        .to_json()
        .to_string()
        .contains("private payload"));
    assert!(runtime.snapshot().to_dot().contains("agent\\\"\\\\\\n"));
    runtime.dispose(provider).unwrap();
    assert!(poll(runtime.settle()).is_pending());
    let state = runtime.snapshot();
    let p = state.plugins.iter().find(|p| p.id == provider).unwrap();
    assert!(p
        .blockers
        .contains(&Blocker::CommittedConsumers(vec![consumer])));
    let c = state.plugins.iter().find(|p| p.id == consumer).unwrap();
    assert!(c.blockers.contains(&Blocker::CleanupPending));
    let bindings = c.committed.clone();
    runtime.compact();
    assert_eq!(runtime.committed(consumer), bindings);
    assert!(!runtime.cleanup_started(provider));
    release.store(true, Ordering::SeqCst);
    ready(runtime.settle()).unwrap();
    assert!(!runtime.contains(provider));
}

#[test]
fn repeated_reactivation_automatically_reclaims_history_without_rebinding() {
    let mut runtime = Runtime::new();
    let ctx = Context::new();
    let key = ServiceKey::<u64>::new("connection");
    let provider = runtime
        .mount(
            &ctx,
            None,
            Plugin::new("connection", move |s| {
                s.provide(key, 42)?;
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
    let consumer = runtime
        .mount(
            &ctx,
            None,
            Plugin::new("client", move |s| {
                assert_eq!(*s.get(key)?, 42);
                Ok(())
            })
            .requires(key),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    let initial = runtime.committed(consumer);
    for _ in 0..1024 {
        runtime.restart(consumer).unwrap();
        ready(runtime.settle()).unwrap();
    }
    assert_eq!(runtime.committed(consumer), initial);
    assert_eq!(runtime.committed(consumer)[0].provider, provider);
    let stats = runtime.storage_stats();
    assert!(stats.binding_records <= 256, "{stats:?}");
    assert_eq!(stats.live_bindings, 1);
    assert_eq!(stats.identity_slots, 2);
    runtime.dispose_all().unwrap();
    ready(runtime.settle()).unwrap();
    runtime.compact();
    let empty = runtime.storage_stats();
    assert_eq!(empty.binding_records, 0);
    assert_eq!(empty.declaration_records, 0);
    assert_eq!(empty.registered_plugins, 0);
    assert_eq!(empty.identity_slots, 2);
}

#[test]
fn shutdown_reports_cleanup_errors_after_finishing_other_resources() {
    let mut runtime = Runtime::new();
    let ctx = Context::new();
    let closed = Arc::new(AtomicBool::new(false));
    let check = closed.clone();
    runtime
        .mount(
            &ctx,
            None,
            Plugin::new("good", move |s| {
                let closed = closed.clone();
                s.on_cleanup(move || {
                    closed.store(true, Ordering::SeqCst);
                    Ok(())
                });
                Ok(())
            }),
        )
        .unwrap();
    runtime
        .mount(
            &ctx,
            None,
            Plugin::new("bad", |s| {
                s.on_cleanup(|| Err("close failed".into()));
                Ok(())
            }),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    let error = ready(runtime.shutdown()).unwrap_err();
    assert!(error.lifecycle.is_none());
    assert_eq!(error.cleanup.len(), 1);
    assert!(check.load(Ordering::SeqCst));
    assert!(runtime.ids().is_empty());
    assert_eq!(runtime.storage_stats().declaration_records, 0);
    ready(runtime.shutdown()).unwrap();
}
