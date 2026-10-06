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

#[test]
fn configured_dependencies_require_exact_host_declarations_before_callbacks() {
    let key = ServiceKey::<usize>::new("configured");
    let other = ServiceKey::<usize>::new("configured");
    let runs = Arc::new(AtomicUsize::new(0));
    let plugin = |config| {
        let runs = runs.clone();
        Plugin::new("configured", move |setup| {
            assert_eq!(*setup.get(key)?, 7);
            runs.fetch_add(1, Ordering::SeqCst);
            Ok(())
        })
        .requires_with_config(key, config)
    };
    let config = serde_json::json!({"minimum":3,"nested":{"levels":[1,2]}});
    let port = Context::new().port(key);
    let expected = |key, value| [(key, value)].into_iter().collect();
    for declared in [
        expected(
            port.key,
            serde_json::json!({"minimum":3,"nested":{"levels":[2,1]}}),
        ),
        expected(Context::new().port(other).key, config.clone()),
        expected(port.key, serde_json::Value::Null),
        expected(port.key, serde_json::json!({})),
    ] {
        assert!(
            matches!(StaticPlugin::new_with_injection_config(plugin(config.clone()), declared), Err(error) if error == "StaticInjectionConfigurationMismatch")
        );
    }
    assert_eq!(runs.load(Ordering::SeqCst), 0);
    let mut definition =
        StaticPlugin::new_with_injection_config(plugin(config.clone()), expected(port.key, config))
            .unwrap();
    let start = definition
        .begin(
            2,
            1,
            Context::new(),
            vec![StaticBinding {
                port,
                provider: 1,
                slot: TypedSlot::from_arc(Arc::new(7usize)),
            }],
        )
        .unwrap();
    finish(start.setup).unwrap();
    assert_eq!(runs.load(Ordering::SeqCst), 1);
    finish(start.episode.cleanup().unwrap()).unwrap();
    assert!(StaticPlugin::new_with_injection_config(
        plugin(serde_json::Value::Null),
        expected(port.key, serde_json::Value::Null)
    )
    .is_ok());
    assert!(StaticPlugin::new_with_injection_config(
        plugin(serde_json::Value::Null),
        Default::default()
    )
    .is_err());
}

fn dynamic_begin(plugin: &mut StaticPlugin) -> cordis::runtime::static_host::StaticStart {
    let anchor = Context::new().port(ServiceKey::<()>::new("host-owner-anchor"));
    plugin
        .begin_with_dynamic_host(10, 5, Context::new(), vec![], anchor, Arc::new(|| {}))
        .unwrap()
}

#[test]
fn dynamic_publication_retains_real_slot_and_explicit_owner_anchor() {
    let key = ServiceKey::<usize>::new("dynamic");
    let anchor = Context::new().port(ServiceKey::<()>::new("anchor"));
    let handles = Arc::new(Mutex::new(None));
    let capture = handles.clone();
    let mut plugin = StaticPlugin::new(Plugin::new("owner", move |setup| {
        *capture.lock().unwrap() = Some(setup.publish_checked(key, 7, |value, _, config| {
            config.as_u64() == Some(*value as u64)
        })?);
        Ok(())
    }))
    .unwrap();
    let start = plugin
        .begin_with_dynamic_host(10, 5, Context::new(), vec![], anchor, Arc::new(|| {}))
        .unwrap();
    finish(start.setup).unwrap();
    let handle = handles.lock().unwrap().take().unwrap();
    assert_eq!(handle.id(), None);
    assert!(!handle.initialized());
    let mut request = start.episode.drain_child_requests().unwrap().pop().unwrap();
    assert_eq!(request.plugin.declarations().dependencies, vec![anchor.key]);
    assert_eq!(
        request.plugin.declarations().provisions,
        vec![Context::new().port(key).key]
    );
    assert_eq!(request.control.owner(), 10);
    assert_eq!(request.control.generation(), 5);
    assert!(request
        .plugin
        .begin(11, 1, request.context.clone(), vec![])
        .is_err());
    request.control.complete_mount(Ok(11)).unwrap();
    assert_eq!(handle.id(), Some(11));
    assert!(request.control.complete_mount(Ok(12)).is_err());
    let child = request
        .plugin
        .begin_with_service_updates(
            11,
            1,
            request.context,
            vec![StaticBinding {
                port: anchor,
                provider: 10,
                slot: TypedSlot::from_arc(Arc::new(())),
            }],
            Arc::new(|| {}),
        )
        .unwrap();
    finish(child.setup).unwrap();
    request.control.mark_initialized().unwrap();
    assert!(handle.initialized());
    let slot = child.episode.provided().unwrap().pop().unwrap().1;
    assert!(Arc::ptr_eq(
        &slot.get::<usize>().unwrap(),
        &handle.get().unwrap()
    ));
    assert!(slot.accepts(&Context::new(), &serde_json::json!(7)));
    assert!(!slot.accepts(&Context::new(), &serde_json::json!(8)));
    let old = handle.get().unwrap();
    handle.set(8).unwrap();
    assert_eq!(*old, 7);
    assert_eq!(*slot.get::<usize>().unwrap(), 8);
    assert!(slot.accepts(&Context::new(), &serde_json::json!(8)));
    handle.dispose();
    assert!(request.control.retirement_requested());
    assert!(handle.set(9).is_err());
    let mut join = Box::pin(handle.join());
    assert!(join
        .as_mut()
        .poll(&mut TaskContext::from_waker(Waker::noop()))
        .is_pending());
    finish(child.episode.cleanup().unwrap()).unwrap();
    assert!(!handle.finished());
    request.control.removed().unwrap();
    assert_eq!(
        join.as_mut()
            .poll(&mut TaskContext::from_waker(Waker::noop())),
        Poll::Ready(Ok(()))
    );
    finish(start.episode.cleanup().unwrap()).unwrap();
}

#[test]
fn external_child_inverse_waits_for_removed_before_earlier_owner_inverse() {
    let earlier = Arc::new(AtomicBool::new(false));
    let copy = earlier.clone();
    let mut plugin = StaticPlugin::new(Plugin::new("owner", move |setup| {
        let earlier = copy.clone();
        setup.on_cleanup(move || {
            earlier.store(true, Ordering::SeqCst);
            Ok(())
        });
        setup.mount(Plugin::new("child", |_| Ok(())))?;
        Ok(())
    }))
    .unwrap();
    let start = dynamic_begin(&mut plugin);
    finish(start.setup).unwrap();
    let request = start.episode.drain_child_requests().unwrap().pop().unwrap();
    request.control.complete_mount(Ok(20)).unwrap();
    let mut cleanup = start.episode.cleanup().unwrap();
    assert!(poll(&mut cleanup).is_pending());
    assert!(request.control.retirement_requested());
    assert!(!earlier.load(Ordering::SeqCst));
    request.control.removed().unwrap();
    finish(cleanup).unwrap();
    assert!(earlier.load(Ordering::SeqCst));
    assert!(start.episode.is_closed());
}

#[test]
fn child_cleanup_failure_keeps_parent_values_and_original_inverse() {
    let value = ServiceKey::<usize>::new("owner-value");
    let earlier = Arc::new(AtomicBool::new(false));
    let copy = earlier.clone();
    let mut plugin = StaticPlugin::new(
        Plugin::new("owner", move |setup| {
            setup.provide(value, 19)?;
            let earlier = copy.clone();
            setup.on_cleanup(move || {
                earlier.store(true, Ordering::SeqCst);
                Ok(())
            });
            setup.mount(Plugin::new("bad child", |setup| {
                setup.on_cleanup(|| Err("child inverse did not restore".into()));
                Ok(())
            }))?;
            Ok(())
        })
        .provides(value),
    )
    .unwrap();
    let start = dynamic_begin(&mut plugin);
    finish(start.setup).unwrap();
    let mut child = start.episode.drain_child_requests().unwrap().pop().unwrap();
    child.control.complete_mount(Ok(20)).unwrap();
    let child_start = child.plugin.begin(20, 1, child.context, vec![]).unwrap();
    finish(child_start.setup).unwrap();
    let mut cleanup = start.episode.cleanup().unwrap();
    assert!(poll(&mut cleanup).is_pending());
    let error = finish(child_start.episode.cleanup().unwrap()).unwrap_err();
    child.control.cleanup_failed(error);
    assert_eq!(finish(cleanup), Err("child inverse did not restore".into()));
    assert_eq!(
        start.episode.cleanup().err().unwrap(),
        "child inverse did not restore"
    );
    assert_eq!(
        *start.episode.provided().unwrap()[0]
            .1
            .get::<usize>()
            .unwrap(),
        19
    );
    assert!(!start.episode.is_closed());
    assert!(!earlier.load(Ordering::SeqCst));
    assert!(child.control.removed().is_err());
    assert!(!child.control.is_removed());
}

#[test]
fn cancellation_after_drain_keeps_late_allocated_child_until_actual_removal() {
    let context = Arc::new(Mutex::new(None::<AsyncSetup>));
    let capture = context.clone();
    let mut plugin = StaticPlugin::new(Plugin::new("owner", move |setup| {
        *capture.lock().unwrap() = Some(setup.to_async());
        setup.mount(Plugin::new("child", |_| Ok(())))?;
        Ok(())
    }))
    .unwrap();
    let start = dynamic_begin(&mut plugin);
    finish(start.setup).unwrap();
    let child = start.episode.drain_child_requests().unwrap().pop().unwrap();
    start.episode.cancel();
    assert!(child.control.retirement_requested());
    assert!(context
        .lock()
        .unwrap()
        .as_ref()
        .unwrap()
        .mount(Plugin::new("late", |_| Ok(())))
        .is_err());
    let mut cleanup = start.episode.cleanup().unwrap();
    assert!(poll(&mut cleanup).is_pending());
    child.control.complete_mount(Ok(37)).unwrap();
    assert_eq!(child.control.id(), Some(37));
    assert!(poll(&mut cleanup).is_pending());
    child.control.removed().unwrap();
    finish(cleanup).unwrap();
}

#[test]
fn queued_cancelled_publication_never_allocates_or_leaves_join_pending() {
    let key = ServiceKey::<usize>::new("queued");
    let handle = Arc::new(Mutex::new(None));
    let capture = handle.clone();
    let mut plugin = StaticPlugin::new(Plugin::new("owner", move |setup| {
        *capture.lock().unwrap() = Some(setup.publish(key, 1)?);
        Ok(())
    }))
    .unwrap();
    let start = dynamic_begin(&mut plugin);
    finish(start.setup).unwrap();
    let handle = handle.lock().unwrap().take().unwrap();
    start.episode.cancel();
    assert!(handle.set(2).is_err());
    assert!(start.episode.drain_child_requests().unwrap().is_empty());
    assert_eq!(handle.id(), None);
    assert!(handle.finished());
    let mut join = Box::pin(handle.join());
    assert_eq!(
        join.as_mut()
            .poll(&mut TaskContext::from_waker(Waker::noop())),
        Poll::Ready(Ok(()))
    );
    finish(start.episode.cleanup().unwrap()).unwrap();
}

#[test]
fn active_dynamic_handle_notifies_every_change_and_closed_owner_releases_host() {
    let key = ServiceKey::<usize>::new("active");
    let stored = Arc::new(Mutex::new(None::<AsyncSetup>));
    let capture = stored.clone();
    let mut plugin = StaticPlugin::new(Plugin::new("owner", move |setup| {
        *capture.lock().unwrap() = Some(setup.to_async());
        Ok(())
    }))
    .unwrap();
    let notifications = Arc::new(AtomicUsize::new(0));
    let copy = notifications.clone();
    let anchor = Context::new().port(ServiceKey::<()>::new("anchor"));
    let start = plugin
        .begin_with_dynamic_host(
            10,
            5,
            Context::new(),
            vec![],
            anchor,
            Arc::new(move || {
                copy.fetch_add(1, Ordering::SeqCst);
            }),
        )
        .unwrap();
    finish(start.setup).unwrap();
    let retained = stored.lock().unwrap().take().unwrap();
    let handle = retained.publish(key, 1).unwrap();
    let request = start.episode.drain_child_requests().unwrap().pop().unwrap();
    request.control.complete_mount(Ok(11)).unwrap();
    let before = notifications.load(Ordering::SeqCst);
    handle.set(2).unwrap();
    handle.set(3).unwrap();
    handle.refresh();
    assert_eq!(notifications.load(Ordering::SeqCst), before + 3);
    request.control.removed().unwrap();
    finish(start.episode.cleanup().unwrap()).unwrap();
    assert_eq!(Arc::strong_count(&notifications), 1);
    assert!(retained.publish(key, 4).is_err());
    assert!(handle.set(4).is_err());
}

#[test]
fn dynamic_child_preserves_context_realms_and_declared_injection_config() {
    let key = ServiceKey::<usize>::new("configured-child-import");
    let context = Context::new().isolate(key);
    let expected_port = context.port(key);
    let mut plugin = StaticPlugin::new(Plugin::new("owner", move |setup| {
        setup.mount_in(
            &context,
            Plugin::new("child", |_| Ok(()))
                .requires_with_config(key, serde_json::json!({"allow": true})),
        )?;
        Ok(())
    }))
    .unwrap();
    let start = dynamic_begin(&mut plugin);
    finish(start.setup).unwrap();
    let child = start.episode.drain_child_requests().unwrap().pop().unwrap();
    assert_eq!(child.context.port(key), expected_port);
    assert_eq!(
        child.plugin.declarations().injection_config[&expected_port.key],
        serde_json::json!({"allow": true})
    );
    child
        .control
        .complete_mount(Err("host declined unavailable context".into()))
        .unwrap();
    finish(start.episode.cleanup().unwrap()).unwrap();
}

#[test]
fn failed_publication_join_reports_error_without_claiming_finished_or_removal() {
    let key = ServiceKey::<usize>::new("failed-publication");
    let handle = Arc::new(Mutex::new(None));
    let capture = handle.clone();
    let mut plugin = StaticPlugin::new(Plugin::new("owner", move |setup| {
        *capture.lock().unwrap() = Some(setup.publish(key, 1)?);
        Ok(())
    }))
    .unwrap();
    let start = dynamic_begin(&mut plugin);
    finish(start.setup).unwrap();
    let handle = handle.lock().unwrap().take().unwrap();
    let child = start.episode.drain_child_requests().unwrap().pop().unwrap();
    child.control.complete_mount(Ok(11)).unwrap();
    let mut join = Box::pin(handle.join());
    assert!(join
        .as_mut()
        .poll(&mut TaskContext::from_waker(Waker::noop()))
        .is_pending());
    child
        .control
        .cleanup_failed("consumer cannot restore".into());
    assert_eq!(
        join.as_mut()
            .poll(&mut TaskContext::from_waker(Waker::noop())),
        Poll::Ready(Err("consumer cannot restore".into()))
    );
    assert!(!handle.finished());
    assert!(handle.set(9).is_err());
    assert!(!child.control.is_removed());
    assert_eq!(handle.errors(), ["consumer cannot restore"]);
    assert!(child.control.removed().is_err());
    assert_eq!(
        finish(start.episode.cleanup().unwrap()),
        Err("consumer cannot restore".into())
    );
    assert!(!start.episode.is_closed());
}

#[test]
fn rejected_child_batch_resolves_every_original_request_without_running_callbacks() {
    let entered = Arc::new(AtomicUsize::new(0));
    let handles = Arc::new(Mutex::new(Vec::new()));
    let capture = handles.clone();
    let copy = entered.clone();
    let mut plugin = StaticPlugin::new(Plugin::new("owner", move |setup| {
        for updated in [false, true, false] {
            let count = copy.clone();
            let mut child = Plugin::new("child", move |_| {
                count.fetch_add(1, Ordering::SeqCst);
                Ok(())
            });
            if updated {
                child = child.on_config_update(|_, _, _| Err("unused".into()));
            }
            capture.lock().unwrap().push(setup.mount(child)?);
        }
        Ok(())
    }))
    .unwrap();
    let start = dynamic_begin(&mut plugin);
    assert_eq!(
        start.episode.drain_child_requests().err().unwrap(),
        "UnsupportedStaticFeature: config_update"
    );
    assert!(finish(start.setup).is_err());
    assert_eq!(entered.load(Ordering::SeqCst), 0);
    for child in handles.lock().unwrap().iter() {
        assert!(child.error().unwrap().contains("config_update"));
        assert_eq!(child.id(), None);
    }
    finish(start.episode.cleanup().unwrap()).unwrap();
    assert!(start.episode.child_controls().is_empty());
}

#[test]
fn dynamic_service_notifications_reenter_owner_without_episode_or_status_locks() {
    let key = ServiceKey::<usize>::new("reentrant");
    let setup = Arc::new(Mutex::new(None::<AsyncSetup>));
    let capture = setup.clone();
    let mut plugin = StaticPlugin::new(Plugin::new("owner", move |ctx| {
        *capture.lock().unwrap() = Some(ctx.to_async());
        Ok(())
    }))
    .unwrap();
    let callbacks = Arc::new(AtomicUsize::new(0));
    let count = callbacks.clone();
    let copy = setup.clone();
    let anchor = Context::new().port(ServiceKey::<()>::new("anchor"));
    let start = plugin
        .begin_with_dynamic_host(
            10,
            5,
            Context::new(),
            vec![],
            anchor,
            Arc::new(move || {
                let owner = copy.lock().unwrap().clone().unwrap();
                let _ = owner.is_cancelled();
                count.fetch_add(1, Ordering::SeqCst);
            }),
        )
        .unwrap();
    finish(start.setup).unwrap();
    let owner = setup.lock().unwrap().clone().unwrap();
    let handle = owner.publish(key, 1).unwrap();
    handle.set(2).unwrap();
    handle.refresh();
    handle.dispose();
    assert_eq!(callbacks.load(Ordering::SeqCst), 4);
    assert!(start.episode.drain_child_requests().unwrap().is_empty());
    finish(start.episode.cleanup().unwrap()).unwrap();
}

#[test]
fn external_child_inherits_parent_actual_and_child_isolated_ports_without_self_cycle() {
    let key = ServiceKey::<usize>::new("inherited");
    let own = ServiceKey::<usize>::new("own");
    let parent_context = Context::new();
    let child_context = parent_context.isolate(key).isolate(own);
    let parent_port = parent_context.port(key);
    let child_port = child_context.port(key);
    let parent_owned_port = parent_context.port(own);
    let child_owned_port = child_context.port(own);
    let mut child = StaticPlugin::new_with_injection_config(
        Plugin::new("child", move |setup| {
            assert_eq!(*setup.get(key)?, 2);
            setup.provide(own, 3)?;
            Ok(())
        })
        .requires_with_config(key, serde_json::json!("child"))
        .provides(own),
        [(parent_port.key, serde_json::json!("child"))].into(),
    )
    .unwrap();
    child
        .inherit_dependencies(
            &child_context,
            vec![parent_port, parent_owned_port],
            [
                (parent_port.key, serde_json::json!("parent")),
                (parent_owned_port.key, serde_json::json!("inherited")),
            ]
            .into(),
        )
        .unwrap();
    assert_eq!(
        child.inherited_dependencies(),
        &[parent_port, child_port, parent_owned_port]
    );
    assert!(!child.inherited_dependencies().contains(&child_owned_port));
    assert_eq!(
        child.declarations().injection_config[&parent_port.key],
        serde_json::json!("child")
    );
    assert_eq!(
        child.declarations().injection_config[&parent_owned_port.key],
        serde_json::json!("inherited")
    );
    let original = Arc::new(1usize);
    let imports = vec![
        StaticBinding {
            port: parent_port,
            provider: 1,
            slot: TypedSlot::from_arc(original.clone()),
        },
        StaticBinding {
            port: child_port,
            provider: 2,
            slot: TypedSlot::from_arc(Arc::new(2usize)),
        },
        StaticBinding {
            port: parent_owned_port,
            provider: 3,
            slot: TypedSlot::from_arc(Arc::new(3usize)),
        },
    ];
    assert!(child
        .begin(10, 1, child_context.clone(), imports[1..].to_vec())
        .is_err());
    let start = child.begin(10, 1, child_context.clone(), imports).unwrap();
    finish(start.setup).unwrap();
    assert_eq!(Arc::strong_count(&original), 2);
    assert!(child
        .inherit_dependencies(&child_context, vec![], Default::default())
        .is_err());
    finish(start.episode.cleanup().unwrap()).unwrap();
    assert_eq!(Arc::strong_count(&original), 1);
}

#[test]
fn inherited_context_cannot_change_between_definition_and_episode() {
    let dependency = ServiceKey::<usize>::new("inherited");
    let own = ServiceKey::<usize>::new("own");
    let context = Context::new().isolate(dependency);
    let mut child = StaticPlugin::new(
        Plugin::new("child", move |setup| {
            setup.provide(own, 1)?;
            Ok(())
        })
        .provides(own),
    )
    .unwrap();
    child
        .inherit_dependencies(
            &context,
            vec![Context::new().port(dependency)],
            Default::default(),
        )
        .unwrap();
    assert_eq!(
        child
            .inherit_dependencies(&context, vec![], Default::default())
            .unwrap_err(),
        "StaticDependenciesAlreadyInherited"
    );
    let imports = vec![
        StaticBinding {
            port: Context::new().port(dependency),
            provider: 1,
            slot: TypedSlot::from_arc(Arc::new(1usize)),
        },
        StaticBinding {
            port: context.port(dependency),
            provider: 2,
            slot: TypedSlot::from_arc(Arc::new(2usize)),
        },
    ];
    // An inherited-only key is not in declared dependencies. Changing its realm
    // must still reject; merely checking declared imports misses this case.
    assert_eq!(
        child
            .begin(10, 1, context.isolate(dependency), imports.clone())
            .err()
            .unwrap(),
        "StaticInheritedContextChanged"
    );
    // A changed own provision could alter which inherited port was excluded.
    assert_eq!(
        child
            .begin(10, 1, context.isolate(own), imports.clone())
            .err()
            .unwrap(),
        "StaticInheritedContextChanged"
    );
    // A later private owner anchor is independent of the inherited port mapping.
    let anchor_key = ServiceKey::<()>::new("new-private-anchor");
    let anchored_context = context.isolate(anchor_key);
    let anchor = anchored_context.port(anchor_key);
    let start = child
        .begin_with_dynamic_host(10, 1, anchored_context, imports, anchor, Arc::new(|| {}))
        .unwrap();
    finish(start.setup).unwrap();
    finish(start.episode.cleanup().unwrap()).unwrap();
}
