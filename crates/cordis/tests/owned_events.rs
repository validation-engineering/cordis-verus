use cordis::events::{
    AsyncEvent, AsyncWaterfall, Event, EventOptions, EventScope, ListenerError, Waterfall,
};
use cordis::{Context, Phase, Plugin, Runtime, ServiceKey};
use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Barrier, Mutex};
use std::task::{Context as TaskContext, Poll, Wake, Waker};

fn poll<F: Future + Unpin>(future: &mut F) -> Poll<F::Output> {
    poll_with(future, Waker::noop())
}
fn poll_with<F: Future + Unpin>(future: &mut F, waker: &Waker) -> Poll<F::Output> {
    Pin::new(future).poll(&mut TaskContext::from_waker(waker))
}

#[test]
fn closed_owned_listener_is_skipped_even_in_an_existing_snapshot() {
    let event = Event::<()>::new();
    let started = Arc::new(Barrier::new(2));
    let release = Arc::new(Barrier::new(2));
    let entered = started.clone();
    let leave = release.clone();
    event.once(EventScope::Global, move |_| {
        entered.wait();
        leave.wait();
    });
    let calls = Arc::new(AtomicUsize::new(0));
    let called = calls.clone();
    let owned = event.on_owned(EventScope::Global, move |_| {
        called.fetch_add(1, Ordering::SeqCst);
    });
    std::thread::scope(|scope| {
        scope.spawn(|| event.emit(EventScope::Global, &()));
        started.wait();
        assert!(owned.close());
        assert!(!owned.close());
        assert_eq!(poll(&mut owned.drain()), Poll::Ready(()));
        release.wait();
    });
    assert_eq!(calls.load(Ordering::SeqCst), 0);
}

#[test]
fn drain_waits_for_all_concurrent_synchronous_invocations() {
    let event = Event::<()>::new();
    let started = Arc::new(Barrier::new(4));
    let release = Arc::new(Barrier::new(4));
    let entered = started.clone();
    let leave = release.clone();
    let owned = event.on_owned(EventScope::Global, move |_| {
        entered.wait();
        leave.wait();
    });
    std::thread::scope(|scope| {
        for _ in 0..3 {
            scope.spawn(|| event.emit(EventScope::Global, &()));
        }
        started.wait();
        assert_eq!(owned.in_flight(), 3);
        assert_eq!(poll(&mut owned.drain()), Poll::Pending);
        event.emit(EventScope::Global, &());
        assert_eq!(owned.in_flight(), 3);
        release.wait();
    });
    assert_eq!(poll(&mut owned.drain()), Poll::Ready(()));
}

#[test]
fn async_dispatch_is_admitted_at_factory_and_cancellation_releases_it() {
    let event = AsyncEvent::<()>::new();
    let subscription = event.on_owned(EventScope::Global, |_| std::future::pending());
    let mut dispatch = event.parallel(EventScope::Global, Arc::new(()));
    assert_eq!(subscription.in_flight(), 1);
    assert_eq!(poll(&mut dispatch), Poll::Pending);
    let mut drain = subscription.drain();
    assert_eq!(poll(&mut drain), Poll::Pending);
    assert_eq!(
        poll(&mut event.parallel(EventScope::Global, Arc::new(()))),
        Poll::Ready(Ok(vec![]))
    );
    drop(dispatch);
    assert_eq!(poll(&mut drain), Poll::Ready(()));
}

#[test]
fn close_does_not_cancel_an_admitted_async_callback() {
    let event = AsyncEvent::<(), usize>::new();
    let ready = Arc::new(AtomicBool::new(false));
    let gate = ready.clone();
    let subscription = event.on_owned(EventScope::Global, move |_| {
        let gate = gate.clone();
        std::future::poll_fn(move |_| {
            if gate.load(Ordering::SeqCst) {
                Poll::Ready(Ok(42))
            } else {
                Poll::Pending
            }
        })
    });
    let mut dispatch = event.parallel(EventScope::Global, Arc::new(()));
    subscription.close();
    assert_eq!(poll(&mut dispatch), Poll::Pending);
    ready.store(true, Ordering::SeqCst);
    assert_eq!(poll(&mut dispatch), Poll::Ready(Ok(vec![42])));
    assert_eq!(poll(&mut subscription.drain()), Poll::Ready(()));
}

struct WakeCallback(Box<dyn Fn() + Send + Sync>);
impl Wake for WakeCallback {
    fn wake(self: Arc<Self>) {
        (self.0)();
    }
}

#[test]
fn cancelled_drain_unregisters_waker_and_live_waker_can_reenter_gate() {
    let event = AsyncEvent::<()>::new();
    let subscription = event.on_owned(EventScope::Global, |_| std::future::pending());
    let dispatch = event.parallel(EventScope::Global, Arc::new(()));
    let dead_count = Arc::new(AtomicUsize::new(0));
    let dead_wake = dead_count.clone();
    let dead = Waker::from(Arc::new(WakeCallback(Box::new(move || {
        dead_wake.fetch_add(1, Ordering::SeqCst);
    }))));
    let live_count = Arc::new(AtomicUsize::new(0));
    let live_wake = live_count.clone();
    let nested = subscription.clone();
    let live = Waker::from(Arc::new(WakeCallback(Box::new(move || {
        assert_eq!(nested.in_flight(), 0);
        assert!(nested.is_closed());
        assert_eq!(poll(&mut nested.drain()), Poll::Ready(()));
        live_wake.fetch_add(1, Ordering::SeqCst);
    }))));
    let mut cancelled = subscription.drain();
    assert_eq!(poll_with(&mut cancelled, &dead), Poll::Pending);
    drop(cancelled);
    let mut replaced = subscription.drain();
    assert_eq!(poll_with(&mut replaced, &dead), Poll::Pending);
    assert_eq!(poll_with(&mut replaced, &live), Poll::Pending);
    drop(dispatch);
    assert_eq!(dead_count.load(Ordering::SeqCst), 0);
    assert_eq!(live_count.load(Ordering::SeqCst), 1);
    assert_eq!(poll(&mut replaced), Poll::Ready(()));
}

#[test]
fn dropping_last_owned_handle_closes_but_dropping_a_clone_does_not() {
    let event = Event::<()>::new();
    let subscription = event.on_owned(EventScope::Global, |_| ());
    drop(subscription.clone());
    assert_eq!(event.listener_count(), 1);
    drop(subscription);
    assert_eq!(event.listener_count(), 0);
}

#[test]
fn owned_once_and_bail_keep_the_existing_dispatch_protocol() {
    let event = Event::<(), Option<usize>>::new();
    let once = event.on_owned_with_options(
        EventScope::Global,
        EventOptions {
            once: true,
            prepend: true,
        },
        |_| Some(5),
    );
    let later = event.on_owned(EventScope::Global, |_| Some(9));
    assert_eq!(event.bail(EventScope::Global, &()), Some(5));
    assert_eq!(once.in_flight(), 0);
    assert_eq!(event.bail(EventScope::Global, &()), Some(9));
    later.close();
    assert_eq!(event.bail(EventScope::Global, &()), None);
}

#[test]
fn factory_poll_and_sync_panics_release_admission() {
    let event = AsyncEvent::<()>::new();
    let constructor = event.on_owned(
        EventScope::Global,
        |_| -> std::future::Ready<Result<(), String>> { panic!("factory") },
    );
    let polling = event.on_owned(EventScope::Global, |_| async { panic!("poll") });
    let Poll::Ready(Err(error)) = poll(&mut event.parallel(EventScope::Global, Arc::new(())))
    else {
        panic!("missing errors")
    };
    assert_eq!(error.failures.len(), 2);
    assert!(
        matches!(&error.failures[0].error, ListenerError::Panicked(message) if message == "factory")
    );
    assert_eq!(poll(&mut constructor.drain()), Poll::Ready(()));
    assert_eq!(poll(&mut polling.drain()), Poll::Ready(()));
    let sync = Event::<()>::new();
    let subscriber = sync.on_owned(EventScope::Global, |_| panic!("sync"));
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(
        || sync.emit(EventScope::Global, &())
    ))
    .is_err());
    assert_eq!(poll(&mut subscriber.drain()), Poll::Ready(()));
}

struct PendingDrop {
    dropped: Arc<AtomicBool>,
    panic: bool,
}
impl Future for PendingDrop {
    type Output = Result<(), String>;
    fn poll(self: Pin<&mut Self>, _: &mut TaskContext<'_>) -> Poll<Self::Output> {
        Poll::Pending
    }
}
impl Drop for PendingDrop {
    fn drop(&mut self) {
        self.dropped.store(true, Ordering::SeqCst);
        assert!(!self.panic, "future destructor");
    }
}

#[test]
fn drain_is_released_after_future_destruction_even_if_destructor_panics() {
    for panic in [false, true] {
        let event = AsyncEvent::<()>::new();
        let dropped = Arc::new(AtomicBool::new(false));
        let flag = dropped.clone();
        let subscription = event.on_owned(EventScope::Global, move |_| PendingDrop {
            dropped: flag.clone(),
            panic,
        });
        let dispatch = event.parallel(EventScope::Global, Arc::new(()));
        let observed = dropped.clone();
        let waker = Waker::from(Arc::new(WakeCallback(Box::new(move || {
            assert!(observed.load(Ordering::SeqCst));
        }))));
        let mut drain = subscription.drain();
        assert_eq!(poll_with(&mut drain, &waker), Poll::Pending);
        assert_eq!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| drop(dispatch))).is_err(),
            panic
        );
        assert_eq!(poll(&mut drain), Poll::Ready(()));
    }
}

#[test]
fn serial_closes_unstarted_snapshot_listeners_and_releases_cancelled_current() {
    let event = AsyncEvent::<(), Option<usize>>::new();
    let first = event.on_owned(EventScope::Global, |_| std::future::pending());
    let later = event.on_owned(EventScope::Global, |_| async { Ok(Some(2)) });
    let mut dispatch = Box::pin(event.serial(EventScope::Global, Arc::new(())));
    assert_eq!(first.in_flight(), 0);
    assert_eq!(poll(&mut dispatch), Poll::Pending);
    assert_eq!(first.in_flight(), 1);
    assert_eq!(later.in_flight(), 0);
    assert_eq!(poll(&mut later.drain()), Poll::Ready(()));
    drop(dispatch);
    assert_eq!(poll(&mut first.drain()), Poll::Ready(()));
}

#[test]
fn owned_waterfalls_track_around_body_and_cancel_pending_work() {
    let sync = Waterfall::<(), usize>::new();
    let owned = sync.on_owned(EventScope::Global, |_, next| {
        next.call().map(|value| value + 1)
    });
    assert_eq!(sync.run(EventScope::Global, &(), || Ok(4)), Ok(5));
    owned.close();
    assert_eq!(sync.run(EventScope::Global, &(), || Ok(4)), Ok(4));
    let asynchronous = AsyncWaterfall::<(), usize>::new();
    let subscription =
        asynchronous.on_owned(
            EventScope::Global,
            |_, next| async move { next.call().await },
        );
    let mut dispatch = asynchronous.run(EventScope::Global, Arc::new(()), std::future::pending);
    assert_eq!(poll(&mut dispatch), Poll::Pending);
    assert_eq!(subscription.in_flight(), 1);
    assert_eq!(poll(&mut subscription.drain()), Poll::Pending);
    drop(dispatch);
    assert_eq!(poll(&mut subscription.drain()), Poll::Ready(()));
}

#[test]
fn runtime_provider_cleanup_waits_for_owned_consumer_dispatch_to_land() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let service = ServiceKey::<Arc<AtomicBool>>::new("event resource");
    let live = Arc::new(AtomicBool::new(true));
    let provider_live = live.clone();
    let provider = runtime
        .mount(
            &context,
            None,
            Plugin::new("provider", move |setup| {
                setup.provide(service, provider_live.clone())?;
                let live = provider_live.clone();
                setup.on_cleanup(move || {
                    live.store(false, Ordering::SeqCst);
                    Ok(())
                });
                Ok(())
            })
            .provides(service),
        )
        .unwrap();
    let event = AsyncEvent::<()>::new();
    let channel = event.clone();
    let ready = Arc::new(AtomicBool::new(false));
    let gate = ready.clone();
    let consumer = runtime
        .mount(
            &context,
            None,
            Plugin::new("consumer", move |setup| {
                let live = setup.get(service)?;
                let gate = gate.clone();
                // Dropping the returned handle does not remove owner-bound registration.
                channel.on_in(&setup.to_async(), EventScope::Global, move |_| {
                    let live = live.clone();
                    let gate = gate.clone();
                    std::future::poll_fn(move |_| {
                        assert!(
                            live.load(Ordering::SeqCst),
                            "provider cleaned before callback"
                        );
                        if gate.load(Ordering::SeqCst) {
                            Poll::Ready(Ok(()))
                        } else {
                            Poll::Pending
                        }
                    })
                })?;
                Ok(())
            })
            .requires(service),
        )
        .unwrap();
    assert_eq!(poll(&mut runtime.settle()), Poll::Ready(Ok(())));
    let mut dispatch = event.parallel(EventScope::Global, Arc::new(()));
    assert_eq!(poll(&mut dispatch), Poll::Pending);
    runtime.dispose(provider).unwrap();
    assert_eq!(poll(&mut runtime.settle()), Poll::Pending);
    assert!(live.load(Ordering::SeqCst));
    assert_eq!(runtime.phase(consumer), Some(Phase::Unloading));
    assert_eq!(event.listener_count(), 0);
    ready.store(true, Ordering::SeqCst);
    assert_eq!(poll(&mut dispatch), Poll::Ready(Ok(vec![()])));
    assert_eq!(poll(&mut runtime.settle()), Poll::Ready(Ok(())));
    assert!(!live.load(Ordering::SeqCst));
    assert_eq!(runtime.phase(consumer), Some(Phase::Inactive));
}

#[test]
fn stale_episode_registration_cannot_admit_any_callback() {
    let mut runtime = Runtime::new();
    let saved = Arc::new(Mutex::new(None));
    let capture = saved.clone();
    let owner = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::new("owner", move |setup| {
                *capture.lock().unwrap() = Some(setup.to_async());
                Ok(())
            }),
        )
        .unwrap();
    assert_eq!(poll(&mut runtime.settle()), Poll::Ready(Ok(())));
    runtime.dispose(owner).unwrap();
    assert_eq!(poll(&mut runtime.settle()), Poll::Ready(Ok(())));
    let event = Event::<()>::new();
    assert!(event
        .on_in(
            saved.lock().unwrap().as_ref().unwrap(),
            EventScope::Global,
            |_| panic!("must not run")
        )
        .is_err());
    assert_eq!(event.listener_count(), 0);
}

struct CaptureDrop(Arc<Mutex<Vec<&'static str>>>);
impl CaptureDrop {
    fn touch(&self) {
        assert!(self.0.lock().unwrap().is_empty());
    }
}
impl Drop for CaptureDrop {
    fn drop(&mut self) {
        self.0.lock().unwrap().push("capture-drop");
    }
}

#[test]
fn callback_capture_drops_before_reentrant_drain_wake() {
    let event = Event::<()>::new();
    let log = Arc::new(Mutex::new(Vec::new()));
    let capture = CaptureDrop(log.clone());
    let started = Arc::new(Barrier::new(2));
    let release = Arc::new(Barrier::new(2));
    let entered = started.clone();
    let leave = release.clone();
    let subscription = event.on_owned(EventScope::Global, move |_| {
        capture.touch();
        entered.wait();
        leave.wait();
    });
    let woke_log = log.clone();
    let wake = Waker::from(Arc::new(WakeCallback(Box::new(move || {
        woke_log.lock().unwrap().push("drain-wake");
    }))));
    std::thread::scope(|scope| {
        let emitter = scope.spawn(|| event.emit(EventScope::Global, &()));
        started.wait();
        let mut drain = subscription.drain();
        assert_eq!(poll_with(&mut drain, &wake), Poll::Pending);
        release.wait();
        emitter.join().unwrap();
        assert_eq!(poll(&mut drain), Poll::Ready(()));
    });
    assert_eq!(*log.lock().unwrap(), vec!["capture-drop", "drain-wake"]);
}

#[test]
fn dormant_serial_snapshot_does_not_keep_closed_callback_captures() {
    let event = AsyncEvent::<(), Option<usize>>::new();
    event.on(EventScope::Global, |_| std::future::pending());
    let log = Arc::new(Mutex::new(Vec::new()));
    let capture = CaptureDrop(log.clone());
    let owned = event.on_owned(EventScope::Global, move |_| {
        capture.touch();
        async { Ok(Some(1)) }
    });
    let mut dispatch = Box::pin(event.serial(EventScope::Global, Arc::new(())));
    assert_eq!(poll(&mut dispatch), Poll::Pending);
    assert_eq!(poll(&mut owned.drain()), Poll::Ready(()));
    assert_eq!(*log.lock().unwrap(), vec!["capture-drop"]);
    drop(dispatch);
}

#[test]
fn escaped_next_and_its_unpolled_future_remain_part_of_owner_drain() {
    use cordis::events::AsyncNext;
    for cancel in [false, true] {
        let waterfall = AsyncWaterfall::<(), usize>::new();
        let saved = Arc::new(Mutex::new(None::<AsyncNext<usize>>));
        let save = saved.clone();
        let subscription = waterfall.on_owned(EventScope::Global, move |_, next| {
            *save.lock().unwrap() = Some(next);
            async { Ok(7) }
        });
        let called = Arc::new(AtomicBool::new(false));
        let ran = called.clone();
        let mut dispatch = waterfall.run(EventScope::Global, Arc::new(()), move || async move {
            ran.store(true, Ordering::SeqCst);
            Ok(9)
        });
        assert_eq!(poll(&mut dispatch), Poll::Ready(Ok(7)));
        let mut drain = subscription.drain();
        assert_eq!(poll(&mut drain), Poll::Pending);
        let next = saved.lock().unwrap().take().unwrap();
        let mut continuation = next.call();
        drop(next);
        assert_eq!(poll(&mut drain), Poll::Pending);
        if !cancel {
            assert_eq!(poll(&mut continuation), Poll::Ready(Ok(9)));
        }
        drop(continuation);
        assert_eq!(poll(&mut drain), Poll::Ready(()));
        assert_eq!(called.load(Ordering::SeqCst), !cancel);
    }
}

#[test]
fn unused_escaped_next_releases_admission_when_last_clone_drops() {
    use cordis::events::AsyncNext;
    let waterfall = AsyncWaterfall::<(), usize>::new();
    let saved = Arc::new(Mutex::new(None::<AsyncNext<usize>>));
    let save = saved.clone();
    let subscription = waterfall.on_owned(EventScope::Global, move |_, next| {
        *save.lock().unwrap() = Some(next);
        async { Ok(7) }
    });
    assert_eq!(
        poll(
            &mut waterfall.run(EventScope::Global, Arc::new(()), || async {
                panic!("must not run")
            })
        ),
        Poll::Ready(Ok(7))
    );
    let next = saved.lock().unwrap().take().unwrap();
    let clone = next.clone();
    drop(next);
    let mut drain = subscription.drain();
    assert_eq!(poll(&mut drain), Poll::Pending);
    drop(clone);
    assert_eq!(poll(&mut drain), Poll::Ready(()));
}

struct BlockingCaptureDrop {
    started: Arc<Barrier>,
    release: Arc<Barrier>,
}
impl BlockingCaptureDrop {
    fn touch(&self) {
        let _ = &self.started;
    }
}
impl Drop for BlockingCaptureDrop {
    fn drop(&mut self) {
        self.started.wait();
        self.release.wait();
    }
}
#[test]
fn concurrent_close_cannot_drain_a_callback_destructor_still_running() {
    let event = Event::<()>::new();
    let started = Arc::new(Barrier::new(2));
    let release = Arc::new(Barrier::new(2));
    let capture = BlockingCaptureDrop {
        started: started.clone(),
        release: release.clone(),
    };
    let subscription = event.on_owned(EventScope::Global, move |_| capture.touch());
    std::thread::scope(|scope| {
        let handle = scope.spawn(|| subscription.close());
        started.wait();
        let mut drain = subscription.drain();
        assert_eq!(poll(&mut drain), Poll::Pending);
        release.wait();
        assert!(handle.join().unwrap());
        assert_eq!(poll(&mut drain), Poll::Ready(()));
    });
}

#[test]
fn callback_storing_next_in_its_own_capture_does_not_create_a_self_cycle() {
    use cordis::events::AsyncNext;
    let waterfall = AsyncWaterfall::<(), usize>::new();
    let saved = Arc::new(Mutex::new(None::<AsyncNext<usize>>));
    let save = saved.clone();
    let captured_lifetime = Arc::new(());
    let weak_lifetime = Arc::downgrade(&captured_lifetime);
    let subscription = waterfall.on_owned(EventScope::Global, move |_, next| {
        let _ = &captured_lifetime;
        *save.lock().unwrap() = Some(next);
        async { Ok(7) }
    });
    let mut dispatch = waterfall.run(EventScope::Global, Arc::new(()), || async {
        panic!("must not run")
    });
    assert_eq!(poll(&mut dispatch), Poll::Ready(Ok(7)));
    drop(dispatch);
    drop(saved);
    assert_eq!(poll(&mut subscription.drain()), Poll::Ready(()));
    assert!(weak_lifetime.upgrade().is_none());
}
