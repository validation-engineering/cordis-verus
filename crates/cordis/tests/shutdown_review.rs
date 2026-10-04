use cordis::{Context, Plugin, Runtime, RuntimeError};
use std::future::{poll_fn, Future};
use std::pin::pin;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::task::{Context as TaskContext, Poll, Waker};

fn poll<T>(future: impl Future<Output = T>) -> Poll<T> {
    pin!(future)
        .as_mut()
        .poll(&mut TaskContext::from_waker(Waker::noop()))
}
fn ready<T>(future: impl Future<Output = T>) -> T {
    match poll(future) {
        Poll::Ready(value) => value,
        Poll::Pending => panic!("unexpected pending"),
    }
}
async fn wait(gate: Arc<AtomicBool>) {
    poll_fn(|_| {
        if gate.load(Ordering::SeqCst) {
            Poll::Ready(())
        } else {
            Poll::Pending
        }
    })
    .await;
}

#[test]
fn shutdown_reports_existing_setup_failure_before_removing_the_plugin() {
    let mut runtime = Runtime::new();
    let owner = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new("failed", |_| Err("setup failed".into())),
        )
        .unwrap();
    assert!(ready(runtime.settle()).is_err());
    let error = ready(runtime.shutdown()).unwrap_err();
    assert_eq!(
        error.setup,
        vec![RuntimeError::Setup {
            plugin: owner,
            message: "setup failed".into()
        }]
    );
    assert!(error.cleanup.is_empty());
    assert!(runtime.ids().is_empty());
    ready(runtime.shutdown()).unwrap();
}

#[test]
fn setup_failure_landing_during_shutdown_is_reported() {
    let mut runtime = Runtime::new();
    let release = Arc::new(AtomicBool::new(false));
    let setup_gate = release.clone();
    let owner = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new_async("pending setup", move |_| {
                let gate = setup_gate.clone();
                async move {
                    wait(gate).await;
                    Err("late setup failure".into())
                }
            }),
        )
        .unwrap();
    assert!(poll(runtime.settle()).is_pending());
    assert!(poll(runtime.shutdown()).is_pending());
    release.store(true, Ordering::SeqCst);
    let error = ready(runtime.shutdown()).unwrap_err();
    assert_eq!(
        error.setup,
        vec![RuntimeError::Setup {
            plugin: owner,
            message: "late setup failure".into()
        }]
    );
    assert!(runtime.ids().is_empty());
}

#[test]
fn dropped_shutdown_keeps_setup_and_cleanup_failures_until_retry_finishes() {
    let mut runtime = Runtime::new();
    let setup_release = Arc::new(AtomicBool::new(false));
    let cleanup_release = Arc::new(AtomicBool::new(false));
    let setup_gate = setup_release.clone();
    let cleanup_gate = cleanup_release.clone();
    let owner = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new_async("both failures", move |context| {
                let setup_gate = setup_gate.clone();
                let cleanup_gate = cleanup_gate.clone();
                async move {
                    context.on_cleanup_async(move || async move {
                        wait(cleanup_gate).await;
                        Err("cleanup failed".into())
                    })?;
                    wait(setup_gate).await;
                    Err("setup failed after cancellation".into())
                }
            }),
        )
        .unwrap();
    assert!(poll(runtime.settle()).is_pending());
    assert!(poll(runtime.shutdown()).is_pending());
    setup_release.store(true, Ordering::SeqCst);
    // This shutdown is dropped after setup failed but before cleanup completes.
    assert!(poll(runtime.shutdown()).is_pending());
    cleanup_release.store(true, Ordering::SeqCst);
    let error = ready(runtime.shutdown()).unwrap_err();
    assert_eq!(
        error.setup,
        vec![RuntimeError::Setup {
            plugin: owner,
            message: "setup failed after cancellation".into()
        }]
    );
    assert_eq!(
        error.cleanup,
        vec![RuntimeError::Cleanup {
            plugin: owner,
            message: "cleanup failed".into()
        }]
    );
    assert!(runtime.ids().is_empty());
    ready(runtime.shutdown()).unwrap();
}

#[test]
fn setup_failure_recovered_before_shutdown_is_not_reported_again() {
    let mut runtime = Runtime::new();
    let owner = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new("recovered", |_| Err("old failure".into())),
        )
        .unwrap();
    assert!(ready(runtime.settle()).is_err());
    runtime.update(owner, |_| Ok(())).unwrap();
    ready(runtime.settle()).unwrap();
    ready(runtime.shutdown()).unwrap();
}
