use cordis::runtime::static_host::{StaticBinding, StaticFuture, StaticPlugin, TypedSlot};
use cordis::{AsyncSetup, CallbackResult, Context, Effect, Plugin, ServiceKey};
use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::task::{Context as TaskContext, Poll, Waker};

fn poll(future: &mut StaticFuture) -> Poll<CallbackResult> {
    future
        .as_mut()
        .poll(&mut TaskContext::from_waker(Waker::noop()))
}
fn finish(mut future: StaticFuture) -> CallbackResult {
    match poll(&mut future) {
        Poll::Ready(result) => result,
        Poll::Pending => panic!("expected an immediately completing operation"),
    }
}
#[derive(Default)]
struct Gate {
    open: AtomicBool,
    waker: Mutex<Option<Waker>>,
}
impl Gate {
    fn release(&self) {
        self.open.store(true, Ordering::SeqCst);
        if let Some(wake) = self.waker.lock().unwrap().take() {
            wake.wake();
        }
    }
}
struct Wait(Arc<Gate>);
impl Future for Wait {
    type Output = ();
    fn poll(self: Pin<&mut Self>, cx: &mut TaskContext<'_>) -> Poll<()> {
        *self.0.waker.lock().unwrap() = Some(cx.waker().clone());
        if self.0.open.load(Ordering::SeqCst) {
            Poll::Ready(())
        } else {
            Poll::Pending
        }
    }
}

#[test]
fn mapped_static_binding_shares_the_actual_arc_through_cleanup() {
    let key = ServiceKey::<AtomicUsize>::new("counter");
    let context = Context::with_realms([(Context::new().port(key).key, 27)]);
    let original = Arc::new(Mutex::new(None));
    let capture = original.clone();
    let mut provider = StaticPlugin::new(
        Plugin::new("provider", move |setup| {
            *capture.lock().unwrap() = Some(setup.provide(key, AtomicUsize::new(7))?);
            Ok(())
        })
        .provides(key),
    )
    .unwrap();
    assert_eq!(provider.declarations().provisions, [context.port(key).key]);
    let start = provider.begin(4, 11, context.clone(), vec![]).unwrap();
    let owner = start.episode;
    finish(start.setup).unwrap();
    assert_eq!(owner.owner(), 4);
    assert_eq!(owner.generation(), 11);
    let published = owner.provided().unwrap();
    assert_eq!(published.len(), 1);
    assert_eq!(published[0].0.realm, 27);
    let expected = original.lock().unwrap().clone().unwrap();
    assert!(Arc::ptr_eq(&published[0].1.get().unwrap(), &expected));
    let erased = published[0].1.value().downcast::<AtomicUsize>().unwrap();
    assert!(Arc::ptr_eq(&erased, &expected));
    assert!(published[0].1.get::<String>().is_none());

    let retained = Arc::new(Mutex::new(None::<AsyncSetup>));
    let capture = retained.clone();
    let observed = expected.clone();
    let mut consumer = StaticPlugin::new(
        Plugin::new("consumer", move |setup| {
            assert!(Arc::ptr_eq(&setup.get(key)?, &observed));
            let context = setup.to_async();
            *capture.lock().unwrap() = Some(context.clone());
            let expected = observed.clone();
            setup.on_cleanup(move || {
                let current = context.get(key)?;
                assert!(Arc::ptr_eq(&current, &expected));
                current.fetch_add(1, Ordering::SeqCst);
                Ok(())
            });
            Ok(())
        })
        .requires(key),
    )
    .unwrap();
    let start = consumer
        .begin(
            9,
            18,
            context,
            vec![StaticBinding {
                port: published[0].0,
                provider: 4,
                slot: published[0].1.clone(),
            }],
        )
        .unwrap();
    let reader = start.episode;
    finish(start.setup).unwrap();
    owner.cancel();
    reader.cancel();
    finish(reader.cleanup().unwrap()).unwrap();
    assert_eq!(expected.load(Ordering::SeqCst), 8);
    assert!(!owner.is_closed());
    finish(owner.cleanup().unwrap()).unwrap();
    assert!(owner.is_closed());
    assert!(owner.provided().is_err());
    let stale = retained.lock().unwrap().take().unwrap();
    assert!(stale.get(key).is_err());
    assert!(stale.on_cleanup(|| Ok(())).is_err());
}

#[test]
fn fn_mut_definition_survives_restart_but_episodes_cannot_overlap() {
    let key = ServiceKey::<usize>::new("sequence");
    let mut sequence = 0;
    let mut definition = StaticPlugin::new(
        Plugin::new("stateful", move |setup| {
            sequence += 1;
            setup.provide(key, sequence)?;
            Ok(())
        })
        .provides(key),
    )
    .unwrap();
    for generation in 1..=3 {
        let start = definition
            .begin(1, generation, Context::new(), vec![])
            .unwrap();
        finish(start.setup).unwrap();
        assert_eq!(
            *start.episode.provided().unwrap()[0]
                .1
                .get::<usize>()
                .unwrap(),
            generation as usize
        );
        assert!(definition
            .begin(1, generation + 1, Context::new(), vec![])
            .is_err());
        finish(start.episode.cleanup().unwrap()).unwrap();
    }
}

#[test]
fn synchronous_partial_failure_and_panic_retain_the_registered_inverse() {
    for panic in [false, true] {
        let cleaned = Arc::new(AtomicUsize::new(0));
        let copy = cleaned.clone();
        let mut definition = StaticPlugin::new(Plugin::new("partial", move |setup| {
            let count = copy.clone();
            setup.on_cleanup(move || {
                count.fetch_add(1, Ordering::SeqCst);
                Ok(())
            });
            if panic {
                panic!("setup failed");
            }
            Err("setup failed".into())
        }))
        .unwrap();
        let start = definition.begin(1, 1, Context::new(), vec![]).unwrap();
        assert!(finish(start.setup).unwrap_err().contains("setup failed"));
        finish(start.episode.cleanup().unwrap()).unwrap();
        assert_eq!(cleaned.load(Ordering::SeqCst), 1);
    }
}

#[test]
fn cancellation_joins_running_setup_and_collects_its_late_inverse() {
    let gate = Arc::new(Gate::default());
    let wait = gate.clone();
    let cleaned = Arc::new(AtomicBool::new(false));
    let copy = cleaned.clone();
    let mut definition = StaticPlugin::new(Plugin::new_async("async", move |setup| {
        let wait = wait.clone();
        let cleaned = copy.clone();
        async move {
            Wait(wait).await;
            assert!(setup.is_cancelled());
            setup.on_cleanup(move || {
                cleaned.store(true, Ordering::SeqCst);
                Ok(())
            })?;
            Ok(())
        }
    }))
    .unwrap();
    let mut start = definition.begin(1, 1, Context::new(), vec![]).unwrap();
    assert!(poll(&mut start.setup).is_pending());
    start.episode.cancel();
    assert_eq!(
        start.episode.cleanup().err().unwrap(),
        "StaticSetupStillRunning"
    );
    assert!(!cleaned.load(Ordering::SeqCst));
    gate.release();
    finish(start.setup).unwrap();
    finish(start.episode.cleanup().unwrap()).unwrap();
    assert!(cleaned.load(Ordering::SeqCst));
}

#[test]
fn cancelling_an_unpolled_async_setup_does_not_enter_its_body() {
    let entered = Arc::new(AtomicBool::new(false));
    let copy = entered.clone();
    let mut definition = StaticPlugin::new(Plugin::new_async("queued", move |_| {
        let copy = copy.clone();
        async move {
            copy.store(true, Ordering::SeqCst);
            Ok(())
        }
    }))
    .unwrap();
    let start = definition.begin(1, 1, Context::new(), vec![]).unwrap();
    start.episode.cancel();
    assert_eq!(finish(start.setup).unwrap_err(), cordis::CANCELLED);
    assert!(!entered.load(Ordering::SeqCst));
    finish(start.episode.cleanup().unwrap()).unwrap();
}

#[test]
fn failing_once_inverse_is_sticky_and_preserves_values_and_earlier_inverses() {
    let earlier = Arc::new(AtomicUsize::new(0));
    let failing = Arc::new(AtomicUsize::new(0));
    let key = ServiceKey::<usize>::new("retained");
    let early = earlier.clone();
    let fail = failing.clone();
    let mut definition = StaticPlugin::new(
        Plugin::new("failing cleanup", move |setup| {
            setup.provide(key, 6)?;
            let early = early.clone();
            setup.on_cleanup(move || {
                early.fetch_add(1, Ordering::SeqCst);
                Ok(())
            });
            let fail = fail.clone();
            setup.on_cleanup(move || {
                fail.fetch_add(1, Ordering::SeqCst);
                Err("cannot replay FnOnce".into())
            });
            Ok(())
        })
        .provides(key),
    )
    .unwrap();
    let start = definition.begin(1, 1, Context::new(), vec![]).unwrap();
    finish(start.setup).unwrap();
    assert_eq!(
        finish(start.episode.cleanup().unwrap()).unwrap_err(),
        "cannot replay FnOnce"
    );
    assert_eq!(
        start.episode.cleanup().err().unwrap(),
        "cannot replay FnOnce"
    );
    assert_eq!(earlier.load(Ordering::SeqCst), 0);
    assert_eq!(failing.load(Ordering::SeqCst), 1);
    assert!(!start.episode.is_closed());
    assert_eq!(
        *start.episode.provided().unwrap()[0]
            .1
            .get::<usize>()
            .unwrap(),
        6
    );
    assert!(definition.begin(1, 2, Context::new(), vec![]).is_err());
}

#[test]
fn cleanup_accepts_late_inverse_before_atomic_seal_and_rejects_it_afterward() {
    let gate = Arc::new(Gate::default());
    let wait = gate.clone();
    let retained = Arc::new(Mutex::new(None::<AsyncSetup>));
    let copy = retained.clone();
    let mut definition = StaticPlugin::new(Plugin::new("late inverse", move |setup| {
        *copy.lock().unwrap() = Some(setup.to_async());
        let wait = wait.clone();
        setup.on_cleanup_async(move || async move {
            Wait(wait).await;
            Ok(())
        });
        Ok(())
    }))
    .unwrap();
    let start = definition.begin(1, 1, Context::new(), vec![]).unwrap();
    finish(start.setup).unwrap();
    let setup = retained.lock().unwrap().clone().unwrap();
    let mut cleanup = start.episode.cleanup().unwrap();
    assert!(poll(&mut cleanup).is_pending());
    assert_eq!(
        start.episode.cleanup().err().unwrap(),
        "StaticCleanupStillRunning"
    );
    let called = Arc::new(AtomicBool::new(false));
    let copy = called.clone();
    setup
        .on_cleanup(move || {
            copy.store(true, Ordering::SeqCst);
            Ok(())
        })
        .unwrap();
    gate.release();
    finish(cleanup).unwrap();
    assert!(called.load(Ordering::SeqCst));
    assert!(setup.on_cleanup(|| Ok(())).is_err());
}

#[test]
fn unsupported_operations_fail_setup_even_if_the_plugin_ignores_their_result() {
    for operation in [
        "set",
        "refresh",
        "provide_checked",
        "publish",
        "mount",
        "effect",
    ] {
        let key = ServiceKey::<usize>::new("service");
        let mut definition = StaticPlugin::new(
            Plugin::new("unsupported", move |setup| {
                match operation {
                    "set" => {
                        let _ = setup.set(key, 1);
                    }
                    "refresh" => {
                        let _ = setup.refresh();
                    }
                    "provide_checked" => {
                        let _ = setup.provide_checked(key, 1, |_, _, _| true);
                    }
                    "publish" => {
                        let _ = setup.publish(key, 1);
                    }
                    "mount" => {
                        let _ = setup.mount(Plugin::new("child", |_| Ok(())));
                    }
                    "effect" => {
                        let _ = setup.effect(Effect::new());
                    }
                    _ => unreachable!(),
                }
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
        let start = definition.begin(1, 1, Context::new(), vec![]).unwrap();
        assert_eq!(
            finish(start.setup).unwrap_err(),
            format!("UnsupportedStaticFeature: {operation}")
        );
        finish(start.episode.cleanup().unwrap()).unwrap();
    }
    let key = ServiceKey::<()>::new("configured");
    assert!(StaticPlugin::new(
        Plugin::new("configured", |_| Ok(())).requires_with_config(key, serde_json::json!({}))
    )
    .is_err());
    assert!(StaticPlugin::new(
        Plugin::new("updated", |_| Ok(())).on_config_update(|_, _, _| Err("unused".into()))
    )
    .is_err());
}

#[test]
fn binding_preflight_rejects_missing_wrong_realm_and_duplicate_imports() {
    let key = ServiceKey::<usize>::new("source");
    let another = ServiceKey::<usize>::new("other");
    let calls = Arc::new(AtomicUsize::new(0));
    let copy = calls.clone();
    let mut definition = StaticPlugin::new(
        Plugin::new("consumer", move |_| {
            copy.fetch_add(1, Ordering::SeqCst);
            Ok(())
        })
        .requires(key)
        .requires(another),
    )
    .unwrap();
    let context = Context::new().isolate(key);
    let binding = StaticBinding {
        port: context.port(key),
        provider: 3,
        slot: TypedSlot::from_arc(Arc::new(5usize)),
    };
    assert!(definition.begin(1, 1, context.clone(), vec![]).is_err());
    assert!(definition
        .begin(
            1,
            1,
            context.clone(),
            vec![binding.clone(), binding.clone()]
        )
        .is_err());
    let mut wrong = binding.clone();
    wrong.port = Context::new().port(key);
    assert!(definition
        .begin(1, 1, context.clone(), vec![binding, wrong])
        .is_err());
    assert!(definition.begin(1, 0, context, vec![]).is_err());
    assert_eq!(calls.load(Ordering::SeqCst), 0);
}

#[test]
fn missing_static_provision_is_a_setup_error_with_restorable_episode() {
    let key = ServiceKey::<usize>::new("missing");
    let mut definition =
        StaticPlugin::new(Plugin::new("missing", |_| Ok(())).provides(key)).unwrap();
    let start = definition.begin(1, 1, Context::new(), vec![]).unwrap();
    assert!(finish(start.setup).unwrap_err().contains("has no value"));
    finish(start.episode.cleanup().unwrap()).unwrap();
}

#[test]
fn abandoned_setup_and_cleanup_cannot_be_misreported_as_restored() {
    let mut definition = StaticPlugin::new(Plugin::new_async("abandoned setup", |_| async {
        std::future::pending::<()>().await;
        Ok(())
    }))
    .unwrap();
    let mut start = definition.begin(1, 1, Context::new(), vec![]).unwrap();
    assert!(poll(&mut start.setup).is_pending());
    drop(start.setup);
    assert!(start
        .episode
        .cleanup()
        .err()
        .unwrap()
        .contains("StaticSetupAbandoned"));
    assert!(definition.begin(1, 2, Context::new(), vec![]).is_err());

    let mut definition = StaticPlugin::new(Plugin::new("abandoned cleanup", |setup| {
        setup.on_cleanup_async(|| async {
            std::future::pending::<()>().await;
            Ok(())
        });
        Ok(())
    }))
    .unwrap();
    let start = definition.begin(1, 1, Context::new(), vec![]).unwrap();
    finish(start.setup).unwrap();
    let mut cleanup = start.episode.cleanup().unwrap();
    assert!(poll(&mut cleanup).is_pending());
    drop(cleanup);
    assert!(start
        .episode
        .cleanup()
        .err()
        .unwrap()
        .contains("StaticCleanupAbandoned"));
    assert!(!start.episode.is_closed());
    assert!(definition.begin(1, 2, Context::new(), vec![]).is_err());
}

#[test]
fn panicking_cleanup_factory_or_future_is_sticky() {
    for factory_panic in [false, true] {
        let calls = Arc::new(AtomicUsize::new(0));
        let copy = calls.clone();
        let mut definition = StaticPlugin::new(Plugin::new("panic cleanup", move |setup| {
            let copy = copy.clone();
            setup.on_cleanup_async(move || {
                copy.fetch_add(1, Ordering::SeqCst);
                assert!(!factory_panic, "cleanup factory panic");
                async { panic!("cleanup poll panic") }
            });
            Ok(())
        }))
        .unwrap();
        let start = definition.begin(1, 1, Context::new(), vec![]).unwrap();
        finish(start.setup).unwrap();
        let error = finish(start.episode.cleanup().unwrap()).unwrap_err();
        assert!(error.contains("panic"));
        assert_eq!(start.episode.cleanup().err().unwrap(), error);
        assert_eq!(calls.load(Ordering::SeqCst), 1);
        assert!(!start.episode.is_closed());
    }
}

struct CountWake(AtomicUsize);
impl std::task::Wake for CountWake {
    fn wake(self: Arc<Self>) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
    fn wake_by_ref(self: &Arc<Self>) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
}

#[test]
fn late_inverse_notifies_current_cleanup_waker_and_close_releases_it() {
    let gate = Arc::new(Gate::default());
    let wait = gate.clone();
    let retained = Arc::new(Mutex::new(None::<AsyncSetup>));
    let copy = retained.clone();
    let mut definition = StaticPlugin::new(Plugin::new("waker", move |setup| {
        *copy.lock().unwrap() = Some(setup.to_async());
        let wait = wait.clone();
        setup.on_cleanup_async(move || async move {
            Wait(wait).await;
            Ok(())
        });
        Ok(())
    }))
    .unwrap();
    let mut start = definition.begin(1, 1, Context::new(), vec![]).unwrap();
    let setup_wake = Arc::new(CountWake(AtomicUsize::new(0)));
    let wake = Waker::from(setup_wake.clone());
    assert!(start
        .setup
        .as_mut()
        .poll(&mut TaskContext::from_waker(&wake))
        .is_ready());
    drop(wake);
    assert_eq!(Arc::strong_count(&setup_wake), 1);
    let mut cleanup = start.episode.cleanup().unwrap();
    let cleanup_wake = Arc::new(CountWake(AtomicUsize::new(0)));
    let wake = Waker::from(cleanup_wake.clone());
    assert!(cleanup
        .as_mut()
        .poll(&mut TaskContext::from_waker(&wake))
        .is_pending());
    retained
        .lock()
        .unwrap()
        .as_ref()
        .unwrap()
        .on_cleanup(|| Ok(()))
        .unwrap();
    assert_eq!(cleanup_wake.0.load(Ordering::SeqCst), 1);
    assert_eq!(setup_wake.0.load(Ordering::SeqCst), 0);
    gate.release();
    assert_eq!(
        cleanup.as_mut().poll(&mut TaskContext::from_waker(&wake)),
        Poll::Ready(Ok(()))
    );
    drop(wake);
    // Gate's last poll also stores its waker; clear that independent registration.
    gate.waker.lock().unwrap().take();
    assert_eq!(Arc::strong_count(&cleanup_wake), 1);
}

#[test]
fn opted_in_service_slots_replace_payload_and_check_the_explicit_consumer() {
    let key = ServiceKey::<usize>::new("live");
    let retained = Arc::new(Mutex::new(None::<AsyncSetup>));
    let capture = retained.clone();
    let mut definition = StaticPlugin::new(
        Plugin::new("live", move |setup| {
            setup.provide_checked(key, 4, move |value, context, config| {
                context.port(key).realm == 17
                    && *value >= config["minimum"].as_u64().unwrap_or(0) as usize
            })?;
            *capture.lock().unwrap() = Some(setup.to_async());
            Ok(())
        })
        .provides(key),
    )
    .unwrap();
    let notifications = Arc::new(AtomicUsize::new(0));
    let count = notifications.clone();
    let start = definition
        .begin_with_service_updates(
            2,
            1,
            Context::new(),
            vec![],
            Arc::new(move || {
                count.fetch_add(1, Ordering::SeqCst);
            }),
        )
        .unwrap();
    finish(start.setup).unwrap();
    let slot = start.episode.provided().unwrap().remove(0).1;
    let original = slot.get::<usize>().unwrap();
    let consumer = Context::with_realms([(Context::new().port(key).key, 17)]);
    assert!(slot.has_check());
    assert!(!slot.accepts(&Context::new(), &serde_json::json!({"minimum": 3})));
    assert!(!slot.accepts(&consumer, &serde_json::json!({"minimum": 5})));
    let handle = retained.lock().unwrap().clone().unwrap();
    handle.set(key, 8).unwrap();
    assert_eq!(*original, 4); // Existing Arc snapshots retain their payload.
    assert_eq!(*slot.get::<usize>().unwrap(), 8); // The committed slot is shared.
    assert!(slot.accepts(&consumer, &serde_json::json!({"minimum": 5})));
    handle.refresh().unwrap();
    assert_eq!(notifications.load(Ordering::SeqCst), 2);
    start.episode.cancel();
    assert!(handle.set(key, 9).is_err());
    assert!(handle.refresh().is_err());
    finish(start.episode.cleanup().unwrap()).unwrap();
    let next = definition
        .begin_with_service_updates(2, 2, Context::new(), vec![], Arc::new(|| {}))
        .unwrap();
    finish(next.setup).unwrap();
    assert!(handle.set(key, 10).is_err());
    assert!(handle.refresh().is_err());
    assert_eq!(
        *next.episode.provided().unwrap()[0]
            .1
            .get::<usize>()
            .unwrap(),
        4
    );
    finish(next.episode.cleanup().unwrap()).unwrap();
}

#[test]
fn opted_in_checked_slot_contains_predicate_panic_and_keeps_other_guards() {
    let key = ServiceKey::<usize>::new("checked");
    let mut definition = StaticPlugin::new(
        Plugin::new("checked", move |setup| {
            setup.provide_checked(key, 1, |_, _, _| panic!("predicate failure"))?;
            Ok(())
        })
        .provides(key),
    )
    .unwrap();
    let start = definition
        .begin_with_service_updates(1, 1, Context::new(), vec![], Arc::new(|| {}))
        .unwrap();
    finish(start.setup).unwrap();
    assert!(!start.episode.provided().unwrap()[0]
        .1
        .accepts(&Context::new(), &serde_json::Value::Null));
    finish(start.episode.cleanup().unwrap()).unwrap();
    let mut definition = StaticPlugin::new(Plugin::new("unsupported", move |setup| {
        let _ignored = setup.publish(key, 1);
        Ok(())
    }))
    .unwrap();
    let start = definition
        .begin_with_service_updates(1, 1, Context::new(), vec![], Arc::new(|| {}))
        .unwrap();
    assert!(finish(start.setup)
        .unwrap_err()
        .contains("UnsupportedStaticFeature: publish"));
    finish(start.episode.cleanup().unwrap()).unwrap();
}

#[test]
fn closed_retained_setup_releases_service_notification_resources_outside_journal_lock() {
    struct NotifyOwner {
        retained: Arc<Mutex<Option<AsyncSetup>>>,
        dropped: Arc<AtomicUsize>,
    }
    impl Drop for NotifyOwner {
        fn drop(&mut self) {
            let handle = self.retained.lock().unwrap().clone().unwrap();
            // This takes the episode lock. Dropping the host callback under
            // that lock would deadlock even though cleanup has completed.
            assert!(handle.is_cancelled());
            self.dropped.fetch_add(1, Ordering::SeqCst);
        }
    }
    let retained = Arc::new(Mutex::new(None::<AsyncSetup>));
    let capture = retained.clone();
    let dropped = Arc::new(AtomicUsize::new(0));
    let owner = NotifyOwner {
        retained: retained.clone(),
        dropped: dropped.clone(),
    };
    let mut definition = StaticPlugin::new(Plugin::new("notifier-owner", move |setup| {
        *capture.lock().unwrap() = Some(setup.to_async());
        Ok(())
    }))
    .unwrap();
    let start = definition
        .begin_with_service_updates(
            1,
            1,
            Context::new(),
            vec![],
            Arc::new(move || {
                std::hint::black_box(&owner);
            }),
        )
        .unwrap();
    finish(start.setup).unwrap();
    assert_eq!(dropped.load(Ordering::SeqCst), 0);
    finish(start.episode.cleanup().unwrap()).unwrap();
    assert_eq!(dropped.load(Ordering::SeqCst), 1);
    let old = retained.lock().unwrap().clone().unwrap();
    assert!(old.refresh().is_err());
    assert_eq!(dropped.load(Ordering::SeqCst), 1);
}
