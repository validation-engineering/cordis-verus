use cordis::timer::{TimerError, TimerService};
use cordis::{Context, Plugin, Runtime, ServiceKey};
use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{mpsc, Arc, Barrier, Mutex};
use std::task::{Context as TaskContext, Poll, Wake, Waker};
use std::time::Duration;

struct CountWake(AtomicUsize);
impl Wake for CountWake {
    fn wake(self: Arc<Self>) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
}
fn poll<F: Future + Unpin>(future: &mut F) -> Poll<F::Output> {
    let waker = Waker::from(Arc::new(CountWake(AtomicUsize::new(0))));
    Pin::new(future).poll(&mut TaskContext::from_waker(&waker))
}
fn ms(value: u64) -> Duration {
    Duration::from_millis(value)
}

#[test]
fn manual_timeouts_cancel_and_keep_deadline_registration_order() {
    let (timers, clock) = TimerService::manual();
    let log = Arc::new(Mutex::new(Vec::new()));
    let log1 = log.clone();
    let first = timers
        .timeout(ms(10), move || log1.lock().unwrap().push(1))
        .unwrap();
    let log2 = log.clone();
    let second = timers
        .timeout(ms(10), move || log2.lock().unwrap().push(2))
        .unwrap();
    let log3 = log.clone();
    timers
        .timeout(ms(5), move || log3.lock().unwrap().push(3))
        .unwrap();
    assert!(second.cancel());
    assert!(!second.cancel());
    assert_eq!(clock.advance(ms(9)), 1);
    assert_eq!(*log.lock().unwrap(), vec![3]);
    assert_eq!(clock.advance(ms(1)), 1);
    assert_eq!(*log.lock().unwrap(), vec![3, 1]);
    assert!(first.is_finished());
    assert_eq!(timers.pending_count(), 0);
    timers.shutdown().unwrap();
    assert!(matches!(
        timers.timeout(ms(1), || {}),
        Err(TimerError::Cancelled)
    ));
}

#[test]
fn interval_is_fixed_delay_skips_missed_ticks_and_can_cancel_inside_callback() {
    let (timers, clock) = TimerService::manual();
    let count = Arc::new(AtomicUsize::new(0));
    let callback_count = count.clone();
    let handle = timers
        .interval(ms(5), move || {
            callback_count.fetch_add(1, Ordering::SeqCst);
        })
        .unwrap();
    assert_eq!(clock.advance(ms(100)), 1);
    assert_eq!(count.load(Ordering::SeqCst), 1);
    assert_eq!(clock.advance(ms(4)), 0);
    assert_eq!(clock.advance(ms(1)), 1);
    handle.cancel_and_join().unwrap();
    assert_eq!(clock.advance(ms(100)), 0);
    assert_eq!(count.load(Ordering::SeqCst), 2);
    assert!(matches!(
        timers.interval(Duration::ZERO, || {}),
        Err(TimerError::ZeroInterval)
    ));

    let handle_slot = Arc::new(Mutex::new(None::<cordis::timer::TimerHandle>));
    let slot = handle_slot.clone();
    *handle_slot.lock().unwrap() = Some(
        timers
            .interval(ms(1), move || {
                slot.lock()
                    .unwrap()
                    .as_ref()
                    .unwrap()
                    .cancel_and_join()
                    .unwrap();
            })
            .unwrap(),
    );
    assert_eq!(clock.advance(ms(1)), 1);
    assert_eq!(clock.advance(ms(100)), 0);
}

#[test]
fn cancelling_a_due_callback_from_another_callback_prevents_its_start() {
    let (timers, clock) = TimerService::manual();
    let slot = Arc::new(Mutex::new(None::<cordis::timer::TimerHandle>));
    let cancel = slot.clone();
    timers
        .timeout(ms(1), move || {
            cancel.lock().unwrap().as_ref().unwrap().cancel();
        })
        .unwrap();
    *slot.lock().unwrap() = Some(
        timers
            .timeout(ms(1), || panic!("cancelled callback started"))
            .unwrap(),
    );
    assert_eq!(clock.advance(ms(1)), 1);
    assert_eq!(timers.pending_count(), 0);
}

#[test]
fn sleep_wakes_on_completion_and_rejects_owner_cancellation() {
    let (timers, clock) = TimerService::manual();
    let mut sleep = timers.sleep(ms(5));
    let wakes = Arc::new(CountWake(AtomicUsize::new(0)));
    let waker = Waker::from(wakes.clone());
    assert_eq!(
        Pin::new(&mut sleep).poll(&mut TaskContext::from_waker(&waker)),
        Poll::Pending
    );
    clock.advance(ms(5));
    assert_eq!(wakes.0.load(Ordering::SeqCst), 1);
    assert_eq!(poll(&mut sleep), Poll::Ready(Ok(())));
    let mut cancelled = timers.sleep(ms(5));
    assert_eq!(poll(&mut cancelled), Poll::Pending);
    timers.shutdown().unwrap();
    assert_eq!(
        poll(&mut cancelled),
        Poll::Ready(Err(TimerError::Cancelled))
    );
    assert_eq!(
        poll(&mut timers.sleep(ms(1))),
        Poll::Ready(Err(TimerError::Cancelled))
    );
}

#[test]
fn dropping_service_rejects_sleep_and_dropping_sleep_removes_its_timer() {
    let (timers, _) = TimerService::manual();
    let sleep = timers.sleep(ms(10));
    assert_eq!(timers.pending_count(), 1);
    drop(sleep);
    assert_eq!(timers.pending_count(), 0);
    let mut sleep = timers.sleep(ms(10));
    drop(timers);
    assert_eq!(poll(&mut sleep), Poll::Ready(Err(TimerError::Cancelled)));
}

#[test]
fn interval_next_queues_waiters_drops_idle_ticks_and_rejects_on_close() {
    let (timers, clock) = TimerService::manual();
    let interval = timers.ticks(ms(2)).unwrap();
    clock.advance(ms(100)); // no buffered ticks
    let mut first = interval.next();
    let mut second = interval.next();
    assert_eq!(poll(&mut first), Poll::Pending);
    clock.advance(ms(2));
    assert_eq!(poll(&mut first), Poll::Ready(Ok(())));
    assert_eq!(poll(&mut second), Poll::Pending);
    interval.close().unwrap();
    assert_eq!(poll(&mut second), Poll::Ready(Err(TimerError::Cancelled)));
    assert_eq!(
        poll(&mut interval.next()),
        Poll::Ready(Err(TimerError::Cancelled))
    );
    assert_eq!(clock.advance(ms(100)), 0);
}

#[test]
fn dropped_tick_does_not_consume_a_later_waiters_tick() {
    let (timers, clock) = TimerService::manual();
    let interval = timers.ticks(ms(2)).unwrap();
    drop(interval.next());
    let mut next = interval.next();
    clock.advance(ms(2));
    assert_eq!(poll(&mut next), Poll::Ready(Ok(())));
    let mut pending = interval.next();
    timers.shutdown().unwrap();
    assert_eq!(poll(&mut pending), Poll::Ready(Err(TimerError::Cancelled)));
}

#[test]
fn debounce_keeps_latest_payload_and_disposal_stops_calls() {
    let (timers, clock) = TimerService::manual();
    let log = Arc::new(Mutex::new(Vec::new()));
    let called = log.clone();
    let debounce = timers.debounce(ms(10), move |value| called.lock().unwrap().push(value));
    debounce.call(1).unwrap();
    clock.advance(ms(5));
    debounce.call(2).unwrap();
    clock.advance(ms(5));
    assert!(log.lock().unwrap().is_empty());
    clock.advance(ms(5));
    assert_eq!(*log.lock().unwrap(), vec![2]);
    debounce.call(3).unwrap();
    debounce.dispose().unwrap();
    assert_eq!(debounce.call(4), Err(TimerError::Cancelled));
    clock.advance(ms(100));
    assert_eq!(*log.lock().unwrap(), vec![2]);
}

#[test]
fn throttle_runs_leading_and_latest_trailing_payload_and_can_disable_trailing() {
    let (timers, clock) = TimerService::manual();
    let log = Arc::new(Mutex::new(Vec::new()));
    let called = log.clone();
    let throttle = timers.throttle(ms(10), false, move |value| {
        called.lock().unwrap().push(value)
    });
    throttle.call(1).unwrap();
    throttle.call(2).unwrap();
    throttle.call(3).unwrap();
    assert_eq!(*log.lock().unwrap(), vec![1]);
    clock.advance(ms(10));
    assert_eq!(*log.lock().unwrap(), vec![1, 3]);
    throttle.dispose().unwrap();
    assert_eq!(throttle.call(4), Err(TimerError::Cancelled));
    let called = log.clone();
    let leading = timers.throttle(ms(10), true, move |value| {
        called.lock().unwrap().push(value)
    });
    leading.call(5).unwrap();
    leading.call(6).unwrap();
    clock.advance(ms(10));
    assert_eq!(*log.lock().unwrap(), vec![1, 3, 5]);
    timers.shutdown().unwrap();
    assert_eq!(leading.call(7), Err(TimerError::Cancelled));
}

#[test]
fn throttle_can_dispose_itself_without_self_join_deadlock() {
    let (timers, _) = TimerService::manual();
    let slot = Arc::new(Mutex::new(None::<cordis::timer::Throttled<()>>));
    let inside = slot.clone();
    let throttle = timers.throttle(ms(10), false, move |()| {
        inside.lock().unwrap().as_ref().unwrap().dispose().unwrap();
    });
    *slot.lock().unwrap() = Some(throttle.clone());
    throttle.call(()).unwrap();
    assert_eq!(throttle.call(()), Err(TimerError::Cancelled));
}

#[test]
fn callback_panic_is_reported_without_stalling_other_timers() {
    let (timers, clock) = TimerService::manual();
    let panic = timers
        .timeout(ms(1), || panic!("intentional timer failure"))
        .unwrap();
    let count = Arc::new(AtomicUsize::new(0));
    let count2 = count.clone();
    timers
        .timeout(ms(1), move || {
            count2.fetch_add(1, Ordering::SeqCst);
        })
        .unwrap();
    assert_eq!(clock.advance(ms(1)), 2);
    assert_eq!(count.load(Ordering::SeqCst), 1);
    assert_eq!(
        panic.cancel_and_join(),
        Err(TimerError::Panicked("intentional timer failure".to_owned()))
    );
    assert_eq!(
        timers.shutdown(),
        Err(vec![TimerError::Panicked(
            "intentional timer failure".to_owned()
        )])
    );
}

#[test]
fn real_worker_cancel_and_join_waits_for_inflight_callback() {
    let timers = TimerService::new();
    let started = Arc::new(Barrier::new(2));
    let release = Arc::new(Barrier::new(2));
    let finished = Arc::new(AtomicUsize::new(0));
    let entered = started.clone();
    let released = release.clone();
    let done = finished.clone();
    let handle = timers
        .timeout(Duration::ZERO, move || {
            entered.wait();
            released.wait();
            done.store(1, Ordering::SeqCst);
        })
        .unwrap();
    started.wait();
    assert!(!handle.is_finished());
    let (tx, rx) = mpsc::channel();
    let cancel_thread = std::thread::spawn(move || {
        handle.cancel_and_join().unwrap();
        tx.send(()).unwrap();
    });
    assert!(rx.try_recv().is_err());
    release.wait();
    rx.recv_timeout(Duration::from_secs(5)).unwrap();
    assert_eq!(finished.load(Ordering::SeqCst), 1);
    cancel_thread.join().unwrap();
    timers.shutdown().unwrap();
}

#[test]
fn owner_cleanup_cancels_timers_before_dependency_provider_cleanup() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::<()>::new("timer dependency");
    let (timers, clock) = TimerService::manual();
    let service = timers.clone();
    let calls = Arc::new(AtomicUsize::new(0));
    let count = calls.clone();
    let provider_timers = timers.clone();
    let provider = runtime
        .mount(
            &context,
            None,
            Plugin::new("provider", move |setup| {
                setup.provide(key, ())?;
                let timers = provider_timers.clone();
                setup.on_cleanup(move || {
                    assert!(timers.is_shutdown());
                    assert_eq!(timers.pending_count(), 0);
                    Ok(())
                });
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
    runtime
        .mount(
            &context,
            None,
            Plugin::new("timer owner", move |setup| {
                setup.get(key)?;
                service.bind(setup);
                let count = count.clone();
                service
                    .interval(ms(1), move || {
                        count.fetch_add(1, Ordering::SeqCst);
                    })
                    .map_err(|error| error.to_string())?;
                Ok(())
            })
            .requires(key),
        )
        .unwrap();
    assert_eq!(poll(&mut Box::pin(runtime.settle())), Poll::Ready(Ok(())));
    clock.advance(ms(1));
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    runtime.dispose(provider).unwrap();
    assert_eq!(poll(&mut Box::pin(runtime.settle())), Poll::Ready(Ok(())));
    clock.advance(ms(100));
    assert_eq!(calls.load(Ordering::SeqCst), 1);
}

#[test]
fn async_initialization_awaiting_sleep_cancels_without_clock_advance() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let (timers, clock) = TimerService::manual();
    let service = timers.clone();
    let captured = Arc::new(Mutex::new(None));
    let handle_slot = captured.clone();
    let owner = runtime
        .mount(
            &context,
            None,
            Plugin::new_async("async sleeper", move |setup| {
                let service = service.clone();
                let handle_slot = handle_slot.clone();
                async move {
                    *handle_slot.lock().unwrap() = Some(setup.clone());
                    service.bind_async(&setup)?;
                    service
                        .sleep(ms(100))
                        .await
                        .map_err(|error| error.to_string())?;
                    Ok(())
                }
            }),
        )
        .unwrap();
    assert_eq!(poll(&mut Box::pin(runtime.settle())), Poll::Pending);
    runtime.dispose(owner).unwrap();
    assert_eq!(poll(&mut Box::pin(runtime.settle())), Poll::Ready(Ok(())));
    assert!(!runtime.contains(owner));
    assert!(timers.is_shutdown());
    assert_eq!(clock.advance(ms(1000)), 0);
    assert!(captured.lock().unwrap().as_ref().unwrap().timer().is_err());
}

#[test]
fn shutdown_joins_synchronous_throttle_leading_callback() {
    let (timers, _) = TimerService::manual();
    let started = Arc::new(Barrier::new(2));
    let release = Arc::new(Barrier::new(2));
    let done = Arc::new(AtomicUsize::new(0));
    let entered = started.clone();
    let released = release.clone();
    let completed = done.clone();
    let throttle = timers.throttle(ms(10), false, move |()| {
        entered.wait();
        released.wait();
        completed.store(1, Ordering::SeqCst);
    });
    let caller = std::thread::spawn(move || throttle.call(()).unwrap());
    started.wait();
    let (tx, rx) = mpsc::channel();
    let shutdown = std::thread::spawn(move || {
        timers.shutdown().unwrap();
        tx.send(()).unwrap();
    });
    assert!(rx.try_recv().is_err());
    release.wait();
    rx.recv_timeout(Duration::from_secs(5)).unwrap();
    assert_eq!(done.load(Ordering::SeqCst), 1);
    caller.join().unwrap();
    shutdown.join().unwrap();
}

#[test]
fn concurrent_shutdown_calls_both_join_manual_clock_callback() {
    let (timers, clock) = TimerService::manual();
    let started = Arc::new(Barrier::new(2));
    let release = Arc::new(Barrier::new(2));
    let done = Arc::new(AtomicUsize::new(0));
    let entered = started.clone();
    let released = release.clone();
    let completed = done.clone();
    timers
        .timeout(ms(1), move || {
            entered.wait();
            released.wait();
            completed.store(1, Ordering::SeqCst);
        })
        .unwrap();
    let runner = std::thread::spawn(move || clock.advance(ms(1)));
    started.wait();
    let (tx, rx) = mpsc::channel();
    let mut shutdowns = Vec::new();
    for _ in 0..2 {
        let timers = timers.clone();
        let tx = tx.clone();
        let done = done.clone();
        shutdowns.push(std::thread::spawn(move || {
            timers.shutdown().unwrap();
            assert_eq!(done.load(Ordering::SeqCst), 1);
            tx.send(()).unwrap();
        }));
    }
    release.wait();
    for _ in 0..2 {
        rx.recv_timeout(Duration::from_secs(5)).unwrap();
    }
    for shutdown in shutdowns {
        shutdown.join().unwrap();
    }
    assert_eq!(runner.join().unwrap(), 1);
}

#[test]
fn synchronous_owner_binding_cancels_inflight_effect_sleep() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let (timers, _) = TimerService::manual();
    let service = timers.clone();
    let owner = runtime
        .mount(
            &context,
            None,
            Plugin::new("sync timer effect owner", move |setup| {
                service.bind(setup);
                let service = service.clone();
                setup.effect(cordis::Effect::new().step(move |_| async move {
                    service
                        .sleep(ms(100))
                        .await
                        .map_err(|error| error.to_string())?;
                    Ok(cordis::Inverse::empty())
                }))?;
                Ok(())
            }),
        )
        .unwrap();
    assert_eq!(poll(&mut Box::pin(runtime.settle())), Poll::Pending);
    runtime.dispose(owner).unwrap();
    assert_eq!(poll(&mut Box::pin(runtime.settle())), Poll::Ready(Ok(())));
    assert!(!runtime.contains(owner));
    assert!(timers.is_shutdown());
}

#[test]
fn callbacks_can_shutdown_the_same_service_concurrently_without_mutual_join() {
    let (timers, clock) = TimerService::manual();
    let both_running = Arc::new(Barrier::new(2));
    let (tx, rx) = mpsc::channel();
    let gate = both_running.clone();
    let service = timers.clone();
    let timeout_done = tx.clone();
    timers
        .timeout(ms(1), move || {
            gate.wait();
            service.shutdown().unwrap();
            timeout_done.send(()).unwrap();
        })
        .unwrap();
    let gate = both_running.clone();
    let service = timers.clone();
    let throttle = timers.throttle(ms(10), false, move |()| {
        gate.wait();
        service.shutdown().unwrap();
        tx.send(()).unwrap();
    });
    let timer_thread = std::thread::spawn(move || clock.advance(ms(1)));
    let throttle_thread = std::thread::spawn(move || throttle.call(()).unwrap());
    for _ in 0..2 {
        rx.recv_timeout(Duration::from_secs(5)).unwrap();
    }
    timers.shutdown().unwrap(); // external shutdown still waits for both callbacks
    timer_thread.join().unwrap();
    throttle_thread.join().unwrap();
    assert_eq!(timers.pending_count(), 0);
}
