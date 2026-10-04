use cordis::{Context, Effect, EffectHandle, Inverse, Plugin, Runtime, RuntimeError};
use std::future::{poll_fn, Future};
use std::pin::Pin;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::task::{Context as TaskContext, Poll, Wake, Waker};

fn drive(runtime: &mut Runtime) -> Poll<Result<(), RuntimeError>> {
    Pin::new(&mut runtime.settle()).poll(&mut TaskContext::from_waker(Waker::noop()))
}
fn poll_join(join: &mut cordis::EffectJoin, waker: &Waker) -> Poll<cordis::CallbackResult> {
    Pin::new(join).poll(&mut TaskContext::from_waker(waker))
}
async fn wait(gate: Arc<AtomicBool>) {
    // Manually driven by each test; this gate retains no test waker.
    poll_fn(move |_| {
        if gate.load(Ordering::SeqCst) {
            Poll::Ready(())
        } else {
            Poll::Pending
        }
    })
    .await;
}

struct PendingEffect {
    runtime: Runtime,
    handle: EffectHandle,
    stage: Arc<AtomicBool>,
    cleanup: Arc<AtomicBool>,
    next_stages: Arc<AtomicUsize>,
    inverses: Arc<AtomicUsize>,
}
impl PendingEffect {
    fn new() -> Self {
        let stage = Arc::new(AtomicBool::new(false));
        let cleanup = Arc::new(AtomicBool::new(false));
        let next_stages = Arc::new(AtomicUsize::new(0));
        let inverses = Arc::new(AtomicUsize::new(0));
        let captured = Arc::new(Mutex::new(None));
        let output = captured.clone();
        let setup_gate = stage.clone();
        let cleanup_gate = cleanup.clone();
        let starts = next_stages.clone();
        let restores = inverses.clone();
        let mut runtime = Runtime::new();
        runtime
            .mount(
                &Context::new(),
                None,
                Plugin::new("waiter-owner", move |ctx| {
                    let stage = setup_gate.clone();
                    let cleanup = cleanup_gate.clone();
                    let starts = starts.clone();
                    let restores = restores.clone();
                    let effect = Effect::new()
                        .step(move |_| async move {
                            wait(stage).await;
                            Ok(Inverse::new_async(move || async move {
                                wait(cleanup).await;
                                restores.fetch_add(1, Ordering::SeqCst);
                                Ok(())
                            }))
                        })
                        .step(move |_| async move {
                            starts.fetch_add(1, Ordering::SeqCst);
                            Ok(Inverse::empty())
                        });
                    *output.lock().unwrap() = Some(ctx.effect(effect)?);
                    Ok(())
                }),
            )
            .unwrap();
        assert_eq!(drive(&mut runtime), Poll::Pending);
        let handle = captured.lock().unwrap().take().unwrap();
        Self {
            runtime,
            handle,
            stage,
            cleanup,
            next_stages,
            inverses,
        }
    }
}

struct ReentrantWake {
    handle: EffectHandle,
    wakes: Arc<AtomicUsize>,
    drops: Arc<AtomicUsize>,
}
impl Wake for ReentrantWake {
    fn wake(self: Arc<Self>) {
        // Both operations lock EffectStatus. Invoking this under that lock
        // would deadlock instead of completing the bounded test.
        let _ = self.handle.initialized();
        self.wakes.fetch_add(1, Ordering::SeqCst);
    }
    fn wake_by_ref(self: &Arc<Self>) {
        let _ = self.handle.finished();
        self.wakes.fetch_add(1, Ordering::SeqCst);
    }
}
impl Drop for ReentrantWake {
    fn drop(&mut self) {
        let _ = self.handle.errors();
        self.drops.fetch_add(1, Ordering::SeqCst);
    }
}
fn bounded(action: impl FnOnce() + Send + 'static) {
    let (send, receive) = std::sync::mpsc::channel();
    let thread = std::thread::spawn(move || {
        action();
        send.send(()).unwrap();
    });
    receive
        .recv_timeout(std::time::Duration::from_secs(5))
        .expect("effect waiter operation deadlocked or panicked");
    thread.join().unwrap();
}

#[test]
fn cancelled_joins_release_wakers_without_cancelling_the_pending_effect() {
    bounded(|| {
        let mut pending = PendingEffect::new();
        let wakes = Arc::new(AtomicUsize::new(0));
        let drops = Arc::new(AtomicUsize::new(0));
        for _ in 0..32 {
            let observer = Arc::new(ReentrantWake {
                handle: pending.handle.clone(),
                wakes: wakes.clone(),
                drops: drops.clone(),
            });
            let weak = Arc::downgrade(&observer);
            let waker = Waker::from(observer);
            let mut join = pending.handle.join();
            assert_eq!(poll_join(&mut join, &waker), Poll::Pending);
            drop(waker);
            assert_eq!(weak.strong_count(), 1);
            drop(join);
            assert_eq!(weak.strong_count(), 0);
        }
        assert_eq!(drops.load(Ordering::SeqCst), 32);
        assert_eq!(wakes.load(Ordering::SeqCst), 0);
        assert!(!pending.handle.initialized());
        pending.stage.store(true, Ordering::SeqCst);
        assert_eq!(drive(&mut pending.runtime), Poll::Ready(Ok(())));
        assert_eq!(pending.next_stages.load(Ordering::SeqCst), 1);
        assert!(!pending.handle.finished());
        pending.handle.cancel();
        pending.cleanup.store(true, Ordering::SeqCst);
        assert_eq!(drive(&mut pending.runtime), Poll::Ready(Ok(())));
        assert_eq!(pending.inverses.load(Ordering::SeqCst), 1);
        assert!(pending.handle.finished());
        assert_eq!(wakes.load(Ordering::SeqCst), 0);
    });
}

#[test]
fn repoll_replaces_the_waker_and_unregister_drops_outside_the_status_lock() {
    bounded(|| {
        let pending = PendingEffect::new();
        let wakes = Arc::new(AtomicUsize::new(0));
        let drops = Arc::new(AtomicUsize::new(0));
        let mut join = pending.handle.join();
        for index in 0..2 {
            let waker = Waker::from(Arc::new(ReentrantWake {
                handle: pending.handle.clone(),
                wakes: wakes.clone(),
                drops: drops.clone(),
            }));
            assert_eq!(poll_join(&mut join, &waker), Poll::Pending);
            drop(waker);
            assert_eq!(drops.load(Ordering::SeqCst), index);
        }
        drop(join);
        assert_eq!(drops.load(Ordering::SeqCst), 2);
        assert_eq!(wakes.load(Ordering::SeqCst), 0);
    });
}

#[test]
fn shared_waker_joins_are_independent_and_a_live_join_can_register_again() {
    bounded(|| {
        let mut pending = PendingEffect::new();
        let wakes = Arc::new(AtomicUsize::new(0));
        let drops = Arc::new(AtomicUsize::new(0));
        let observer = Arc::new(ReentrantWake {
            handle: pending.handle.clone(),
            wakes: wakes.clone(),
            drops: drops.clone(),
        });
        let weak = Arc::downgrade(&observer);
        let waker = Waker::from(observer);
        let mut cancelled = pending.handle.join();
        let mut live = pending.handle.join();
        assert_eq!(poll_join(&mut cancelled, &waker), Poll::Pending);
        assert_eq!(poll_join(&mut live, &waker), Poll::Pending);
        drop(cancelled);
        pending.stage.store(true, Ordering::SeqCst);
        assert_eq!(drive(&mut pending.runtime), Poll::Ready(Ok(())));
        assert!(pending.handle.initialized());
        assert_eq!(wakes.load(Ordering::SeqCst), 1);
        // Initialization drained registrations, but cleanup still has to run.
        assert_eq!(poll_join(&mut live, &waker), Poll::Pending);
        drop(waker);
        assert_eq!(weak.strong_count(), 1);
        pending.handle.cancel();
        assert_eq!(drive(&mut pending.runtime), Poll::Pending);
        assert!(!pending.handle.finished());
        pending.cleanup.store(true, Ordering::SeqCst);
        assert_eq!(drive(&mut pending.runtime), Poll::Ready(Ok(())));
        assert_eq!(wakes.load(Ordering::SeqCst), 2);
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        assert_eq!(weak.strong_count(), 0);
        assert_eq!(poll_join(&mut live, Waker::noop()), Poll::Ready(Ok(())));
    });
}

#[test]
fn replacing_the_driver_waker_drops_it_outside_the_status_lock() {
    bounded(|| {
        let mut pending = PendingEffect::new();
        let wakes = Arc::new(AtomicUsize::new(0));
        let drops = Arc::new(AtomicUsize::new(0));
        let observer = Arc::new(ReentrantWake {
            handle: pending.handle.clone(),
            wakes: wakes.clone(),
            drops: drops.clone(),
        });
        let weak = Arc::downgrade(&observer);
        let waker = Waker::from(observer);
        assert_eq!(
            Pin::new(&mut pending.runtime.settle()).poll(&mut TaskContext::from_waker(&waker)),
            Poll::Pending
        );
        drop(waker);
        assert!(weak.strong_count() > 0);
        assert_eq!(drive(&mut pending.runtime), Poll::Pending);
        assert_eq!(weak.strong_count(), 0);
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        assert_eq!(wakes.load(Ordering::SeqCst), 0);
    });
}

#[test]
fn cancelling_an_unpolled_effect_never_constructs_its_first_stage() {
    let constructed = Arc::new(AtomicUsize::new(0));
    let stage_constructions = constructed.clone();
    let captured = Arc::new(Mutex::new(None));
    let output = captured.clone();
    let mut runtime = Runtime::new();
    runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new("cancel-before-admission", move |ctx| {
                let constructions = stage_constructions.clone();
                let handle = ctx.effect(Effect::new().step(move |_| {
                    constructions.fetch_add(1, Ordering::SeqCst);
                    async { Ok(Inverse::empty()) }
                }))?;
                handle.cancel();
                *output.lock().unwrap() = Some(handle);
                Ok(())
            }),
        )
        .unwrap();
    assert_eq!(drive(&mut runtime), Poll::Ready(Ok(())));
    assert_eq!(constructed.load(Ordering::SeqCst), 0);
    assert!(captured.lock().unwrap().as_ref().unwrap().finished());
}
