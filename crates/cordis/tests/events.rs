use cordis::events::{Event, EventScope, Subscription};
use cordis::{Context, Plugin, Runtime, ServiceKey};
use std::future::Future;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Barrier, Mutex};
use std::task::{Context as TaskContext, Poll, Waker};

#[test]
fn emit_preserves_registration_order_and_off_is_idempotent() {
    let event = Event::<u32>::new();
    let log = Arc::new(Mutex::new(Vec::new()));
    let first_log = log.clone();
    let first = event.on(EventScope::Global, move |value| {
        first_log.lock().unwrap().push(*value);
    });
    let second_log = log.clone();
    event.on(EventScope::Global, move |value| {
        second_log.lock().unwrap().push(*value + 1);
    });

    event.emit(EventScope::Global, &10);
    assert_eq!(*log.lock().unwrap(), vec![10, 11]);
    assert!(!Event::<u32>::new().off(&first));
    assert!(event.off(&first));
    assert!(!first.dispose());
    event.emit(EventScope::Global, &20);
    assert_eq!(*log.lock().unwrap(), vec![10, 11, 21]);
}

#[test]
fn callback_changes_only_affect_subsequent_dispatch_snapshots() {
    let event = Event::<()>::new();
    let log = Arc::new(Mutex::new(Vec::new()));
    let pending = Arc::new(Mutex::new(None::<Subscription<()>>));
    let pending_for_callback = pending.clone();
    let nested = event.clone();
    let first_log = log.clone();
    event.once(EventScope::Global, move |_| {
        first_log.lock().unwrap().push("first");
        pending_for_callback
            .lock()
            .unwrap()
            .as_ref()
            .unwrap()
            .dispose();
        let added_log = first_log.clone();
        nested.on(EventScope::Global, move |_| {
            added_log.lock().unwrap().push("added")
        });
    });
    let second_log = log.clone();
    *pending.lock().unwrap() = Some(event.on(EventScope::Global, move |_| {
        second_log.lock().unwrap().push("second");
    }));

    event.emit(EventScope::Global, &());
    assert_eq!(*log.lock().unwrap(), vec!["first", "second"]);
    event.emit(EventScope::Global, &());
    assert_eq!(*log.lock().unwrap(), vec!["first", "second", "added"]);
}

#[test]
fn once_is_removed_before_reentrant_dispatch() {
    let event = Event::<usize>::new();
    let nested = event.clone();
    let called = Arc::new(AtomicUsize::new(0));
    let counter = called.clone();
    let subscription = event.once(EventScope::Global, move |value| {
        counter.fetch_add(*value, Ordering::SeqCst);
        assert_eq!(nested.listener_count(), 0);
        nested.emit(EventScope::Global, value);
    });
    event.emit(EventScope::Global, &3);
    event.emit(EventScope::Global, &3);
    assert_eq!(called.load(Ordering::SeqCst), 3);
    assert!(!subscription.dispose());
}

#[test]
fn nested_dispatch_cannot_repeat_a_once_listener_in_the_outer_snapshot() {
    let event = Event::<()>::new();
    let nested = event.clone();
    event.once(EventScope::Global, move |_| {
        nested.emit(EventScope::Global, &())
    });
    let count = Arc::new(AtomicUsize::new(0));
    let counted = count.clone();
    event.once(EventScope::Global, move |_| {
        counted.fetch_add(1, Ordering::SeqCst);
    });

    // Both snapshots contain the second callback; its atomic claim is shared.
    event.emit(EventScope::Global, &());
    assert_eq!(count.load(Ordering::SeqCst), 1);
    assert_eq!(event.listener_count(), 0);
}

#[test]
fn once_claim_is_shared_across_concurrent_dispatches() {
    let event = Event::<()>::new();
    let count = Arc::new(AtomicUsize::new(0));
    let counted = count.clone();
    event.once(EventScope::Global, move |_| {
        counted.fetch_add(1, Ordering::SeqCst);
    });
    let barrier = Arc::new(Barrier::new(3));
    std::thread::scope(|scope| {
        for _ in 0..2 {
            let barrier = barrier.clone();
            let event = event.clone();
            scope.spawn(move || {
                barrier.wait();
                event.emit(EventScope::Global, &());
            });
        }
        barrier.wait();
    });
    assert_eq!(count.load(Ordering::SeqCst), 1);
    assert_eq!(event.listener_count(), 0);
}

#[test]
fn bail_stops_at_some_without_consuming_later_once_listeners() {
    let event = Event::<u32, Option<bool>>::new();
    let count = Arc::new(AtomicUsize::new(0));
    let first = count.clone();
    event.on(EventScope::Global, move |_| {
        first.fetch_add(1, Ordering::SeqCst);
        None
    });
    let winner = event.on(EventScope::Global, |_| Some(false));
    let last = count.clone();
    event.once(EventScope::Global, move |_| {
        last.fetch_add(10, Ordering::SeqCst);
        Some(true)
    });

    assert_eq!(event.bail(EventScope::Global, &0), Some(false));
    assert_eq!(count.load(Ordering::SeqCst), 1);
    assert!(winner.dispose());
    assert_eq!(event.bail(EventScope::Global, &0), Some(true));
    assert_eq!(count.load(Ordering::SeqCst), 12);
    assert_eq!(event.bail(EventScope::Global, &0), None);
    assert_eq!(count.load(Ordering::SeqCst), 13);
}

#[test]
fn relevant_scope_compares_service_and_realm_while_global_bypasses_it() {
    let key = ServiceKey::<()>::new("selected service");
    let other = ServiceKey::<()>::new("unrelated service");
    let root = Context::new();
    let isolated = root.isolate(key);
    let shared = root.share(key, &isolated);
    let event = Event::<()>::new();
    let log = Arc::new(Mutex::new(Vec::new()));
    for (name, scope) in [
        ("root", EventScope::Relevant(root.port(key))),
        ("isolated", EventScope::Relevant(isolated.port(key))),
        ("other", EventScope::Relevant(root.port(other))),
        ("global", EventScope::Global),
    ] {
        let log = log.clone();
        event.on(scope, move |_| log.lock().unwrap().push(name));
    }

    event.emit(EventScope::Relevant(root.port(key)), &());
    assert_eq!(*log.lock().unwrap(), vec!["root", "global"]);
    log.lock().unwrap().clear();
    event.emit(EventScope::Relevant(shared.port(key)), &());
    assert_eq!(*log.lock().unwrap(), vec!["isolated", "global"]);
    log.lock().unwrap().clear();
    event.emit(EventScope::Global, &());
    assert_eq!(
        *log.lock().unwrap(),
        vec!["root", "isolated", "other", "global"]
    );
}

fn settle_sync(runtime: &mut Runtime) {
    let waker = Waker::noop();
    let mut context = TaskContext::from_waker(waker);
    let mut settle = std::pin::pin!(runtime.settle());
    assert_eq!(settle.as_mut().poll(&mut context), Poll::Ready(Ok(())));
}

#[test]
fn runtime_owner_disposal_removes_its_listener_through_owned_cleanup() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::<()>::new("event relevance");
    let event = Event::<usize>::new();
    let channel = event.clone();
    let count = Arc::new(AtomicUsize::new(0));
    let called = count.clone();
    let owner = runtime
        .mount(
            &context,
            None,
            Plugin::new("subscriber", move |setup| {
                let called = called.clone();
                let subscription = channel.on(
                    EventScope::Relevant(setup.context().port(key)),
                    move |value| {
                        called.fetch_add(*value, Ordering::SeqCst);
                    },
                );
                setup.on_cleanup(move || {
                    subscription.dispose();
                    Ok(())
                });
                Ok(())
            }),
        )
        .unwrap();

    settle_sync(&mut runtime);
    event.emit(EventScope::Relevant(context.port(key)), &2);
    assert_eq!(count.load(Ordering::SeqCst), 2);
    runtime.dispose(owner).unwrap();
    settle_sync(&mut runtime);
    assert_eq!(event.listener_count(), 0);
    event.emit(EventScope::Relevant(context.port(key)), &2);
    assert_eq!(count.load(Ordering::SeqCst), 2);
    assert!(!runtime.contains(owner));
}

use cordis::events::{
    AsyncEvent, AsyncWaterfall, EventOptions, ListenerError, Waterfall, WaterfallError,
};
use std::pin::Pin;

fn poll_once<F: Future + Unpin>(future: &mut F) -> Poll<F::Output> {
    let waker = Waker::noop();
    future_pin_poll(Pin::new(future), waker)
}
fn future_pin_poll<F: Future>(future: Pin<&mut F>, waker: &Waker) -> Poll<F::Output> {
    future.poll(&mut TaskContext::from_waker(waker))
}

#[test]
fn prepend_and_custom_predicates_are_snapshot_safe_and_global_bypasses_filter() {
    let event = Event::new();
    let log = Arc::new(Mutex::new(Vec::new()));
    for (id, scope, prepend) in [
        (1, EventScope::Custom(1), false),
        (2, EventScope::Custom(2), false),
        (3, EventScope::Global, true),
    ] {
        let log = log.clone();
        event.on_with_options(
            scope,
            EventOptions {
                prepend,
                once: false,
            },
            move |_: &()| log.lock().unwrap().push(id),
        );
    }
    event.emit_filtered(
        |scope| {
            assert_eq!(event.listener_count(), 3); // the predicate may reenter the registry
            scope == EventScope::Custom(2)
        },
        &(),
    );
    assert_eq!(*log.lock().unwrap(), vec![3, 2]);
}

#[test]
fn parallel_polls_every_listener_and_waits_for_pending_after_errors() {
    let event = AsyncEvent::<(), usize, &'static str>::new();
    let polled = Arc::new(AtomicUsize::new(0));
    let ready = Arc::new(std::sync::atomic::AtomicBool::new(false));
    event.on(EventScope::Global, |_| async { Err("first") });
    let count = polled.clone();
    let gate = ready.clone();
    event.on(EventScope::Global, move |_| {
        let count = count.clone();
        let gate = gate.clone();
        std::future::poll_fn(move |_| {
            count.fetch_add(1, Ordering::SeqCst);
            if gate.load(Ordering::SeqCst) {
                Poll::Ready(Err("second"))
            } else {
                Poll::Pending
            }
        })
    });
    let count = polled.clone();
    event.on(EventScope::Global, move |_| {
        count.fetch_add(10, Ordering::SeqCst);
        async { Ok(3) }
    });
    let mut dispatch = event.parallel(EventScope::Global, Arc::new(()));
    assert_eq!(poll_once(&mut dispatch), Poll::Pending);
    assert_eq!(polled.load(Ordering::SeqCst), 11);
    ready.store(true, Ordering::SeqCst);
    let Poll::Ready(Err(error)) = poll_once(&mut dispatch) else {
        panic!("dispatch did not settle");
    };
    assert_eq!(
        error.failures.iter().map(|f| f.index).collect::<Vec<_>>(),
        vec![0, 1]
    );
    assert_eq!(error.failures[0].error, ListenerError::Callback("first"));
    assert_eq!(error.failures[1].error, ListenerError::Callback("second"));
}

#[test]
fn parallel_reports_constructor_and_poll_panics_without_skipping_later_listeners() {
    let event = AsyncEvent::<(), (), &'static str>::new();
    event.on(
        EventScope::Global,
        |_| -> std::future::Ready<Result<(), &'static str>> {
            panic!("construct");
        },
    );
    event.on(EventScope::Global, |_| async {
        panic!("poll");
    });
    let called = Arc::new(AtomicUsize::new(0));
    let count = called.clone();
    event.on(EventScope::Global, move |_| {
        count.fetch_add(1, Ordering::SeqCst);
        async { Ok(()) }
    });
    let Poll::Ready(Err(error)) = poll_once(&mut event.parallel(EventScope::Global, Arc::new(())))
    else {
        panic!("missing aggregate error");
    };
    assert_eq!(called.load(Ordering::SeqCst), 1);
    assert_eq!(error.failures.len(), 2);
    assert_eq!(
        error.failures[0].error,
        ListenerError::Panicked("construct".to_owned())
    );
    assert_eq!(
        error.failures[1].error,
        ListenerError::Panicked("poll".to_owned())
    );
}

#[test]
fn serial_waits_before_constructing_next_and_preserves_uncalled_once() {
    let event = AsyncEvent::<(), Option<bool>, String>::new();
    let ready = Arc::new(std::sync::atomic::AtomicBool::new(false));
    let gate = ready.clone();
    event.once(EventScope::Global, move |_| {
        let gate = gate.clone();
        std::future::poll_fn(move |_| {
            if gate.load(Ordering::SeqCst) {
                Poll::Ready(Ok(None))
            } else {
                Poll::Pending
            }
        })
    });
    let winner = event.on(EventScope::Global, |_| async { Ok(Some(false)) });
    let called = Arc::new(AtomicUsize::new(0));
    let count = called.clone();
    event.once(EventScope::Global, move |_| {
        count.fetch_add(1, Ordering::SeqCst);
        async { Ok(Some(true)) }
    });
    let mut dispatch = Box::pin(event.serial(EventScope::Global, Arc::new(())));
    assert_eq!(poll_once(&mut dispatch), Poll::Pending);
    assert_eq!(called.load(Ordering::SeqCst), 0);
    ready.store(true, Ordering::SeqCst);
    assert_eq!(poll_once(&mut dispatch), Poll::Ready(Ok(Some(false))));
    assert_eq!(event.listener_count(), 2);
    winner.dispose();
    assert_eq!(
        poll_once(&mut Box::pin(
            event.serial(EventScope::Global, Arc::new(()))
        )),
        Poll::Ready(Ok(Some(true)))
    );
    assert_eq!(called.load(Ordering::SeqCst), 1);
}

#[test]
fn async_once_claim_survives_reentrancy_and_concurrent_dispatch() {
    let event = AsyncEvent::<(), (), String>::new();
    let nested = event.clone();
    let called = Arc::new(AtomicUsize::new(0));
    let count = called.clone();
    event.once(EventScope::Global, move |_| {
        count.fetch_add(1, Ordering::SeqCst);
        assert_eq!(nested.listener_count(), 0);
        assert_eq!(
            poll_once(&mut nested.parallel(EventScope::Global, Arc::new(()))),
            Poll::Ready(Ok(vec![]))
        );
        async { Ok(()) }
    });
    let barrier = Arc::new(Barrier::new(3));
    std::thread::scope(|scope| {
        for _ in 0..2 {
            let event = event.clone();
            let barrier = barrier.clone();
            scope.spawn(move || {
                barrier.wait();
                assert!(matches!(
                    poll_once(&mut event.parallel(EventScope::Global, Arc::new(()))),
                    Poll::Ready(Ok(_))
                ));
            });
        }
        barrier.wait();
    });
    assert_eq!(called.load(Ordering::SeqCst), 1);
}

#[test]
fn waterfall_wraps_transforms_and_rejects_duplicate_next() {
    let waterfall = Waterfall::<(), usize, String>::new();
    let log = Arc::new(Mutex::new(Vec::new()));
    let outer = log.clone();
    waterfall.on(EventScope::Global, move |_, next| {
        outer.lock().unwrap().push("before");
        let result = next.call()?;
        assert_eq!(next.call(), Err(WaterfallError::NextCalledTwice));
        outer.lock().unwrap().push("after");
        Ok(result + 1)
    });
    let inner = log.clone();
    waterfall.on(EventScope::Global, move |_, next| {
        inner.lock().unwrap().push("inner");
        next.call().map(|value| value * 2)
    });
    assert_eq!(waterfall.run(EventScope::Global, &(), || Ok(10)), Ok(21));
    assert_eq!(*log.lock().unwrap(), vec!["before", "inner", "after"]);
}

#[test]
fn waterfall_short_circuit_does_not_claim_later_once() {
    let waterfall = Waterfall::<(), usize, String>::new();
    let first = waterfall.on(EventScope::Global, |_, _| Ok(5));
    waterfall.on_with_options(
        EventScope::Global,
        EventOptions {
            once: true,
            prepend: false,
        },
        |_, next| next.call(),
    );
    assert_eq!(
        waterfall.run(EventScope::Global, &(), || panic!("short-circuit failed")),
        Ok(5)
    );
    assert_eq!(waterfall.listener_count(), 2);
    first.dispose();
    assert_eq!(waterfall.run(EventScope::Global, &(), || Ok(3)), Ok(3));
    assert_eq!(waterfall.listener_count(), 0);
}

#[test]
fn async_waterfall_awaits_inner_and_next_clones_share_claim() {
    let waterfall = AsyncWaterfall::<(), usize, String>::new();
    waterfall.on(EventScope::Global, |_, next| async move {
        let clone = next.clone();
        let result = next.call().await?;
        assert_eq!(clone.call().await, Err(WaterfallError::NextCalledTwice));
        Ok(result + 1)
    });
    let ready = Arc::new(std::sync::atomic::AtomicBool::new(false));
    let gate = ready.clone();
    let mut dispatch = waterfall.run(EventScope::Global, Arc::new(()), move || {
        std::future::poll_fn(move |_| {
            if gate.load(Ordering::SeqCst) {
                Poll::Ready(Ok(10))
            } else {
                Poll::Pending
            }
        })
    });
    assert_eq!(poll_once(&mut dispatch), Poll::Pending);
    ready.store(true, Ordering::SeqCst);
    assert_eq!(poll_once(&mut dispatch), Poll::Ready(Ok(11)));
}
