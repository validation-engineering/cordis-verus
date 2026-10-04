use cordis::diagnostics::Blocker;
use cordis::{Context, Effect, Inverse, Phase, Plugin, Runtime};
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

#[test]
fn active_effect_cleanup_is_visible_while_its_inverse_is_pending() {
    let mut runtime = Runtime::new();
    let owner = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new("active owner", |_| Ok(())),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    let release = Arc::new(AtomicBool::new(false));
    let gate = release.clone();
    let effect = runtime
        .effect(
            owner,
            Effect::new().inverse(Inverse::new_async(move || async move {
                poll_fn(|_| {
                    if gate.load(Ordering::SeqCst) {
                        Poll::Ready(())
                    } else {
                        Poll::Pending
                    }
                })
                .await;
                Ok(())
            })),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    effect.cancel();
    assert!(poll(runtime.settle()).is_pending());
    let snapshot = runtime.snapshot();
    let plugin = snapshot
        .plugins
        .iter()
        .find(|plugin| plugin.id == owner)
        .unwrap();
    assert_eq!(plugin.phase, Phase::Active);
    assert!(
        plugin.blockers.contains(&Blocker::CleanupPending),
        "{plugin:?}"
    );
    release.store(true, Ordering::SeqCst);
    ready(runtime.settle()).unwrap();
    assert!(effect.finished());
    assert!(!runtime.snapshot().plugins[0]
        .blockers
        .contains(&Blocker::CleanupPending));
}

#[test]
fn dot_names_cannot_emit_raw_control_characters() {
    let mut runtime = Runtime::new();
    let name = "plugin\0\u{0007}\t\u{007f}\"\\\n\r";
    runtime
        .mount(&Context::new(), None, Plugin::new(name, |_| Ok(())))
        .unwrap();
    let snapshot = runtime.snapshot();
    assert_eq!(snapshot.to_json()["plugins"][0]["name"], name);
    let dot = snapshot.to_dot();
    assert!(
        !dot.chars()
            .any(|character| character.is_control() && character != '\n'),
        "raw control character in {dot:?}"
    );
    assert!(dot.contains("\\\"\\\\\\n\\r"));
}
