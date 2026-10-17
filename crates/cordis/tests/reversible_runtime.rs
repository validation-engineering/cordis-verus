use cordis::runtime::static_host::{StaticBinding, StaticPlugin, TypedSlot};
use cordis::{
    Context, Plugin, ReversibleValue, Runtime, RuntimeError, ServiceKey, ValueBranch,
    ValueInstruction, ValueOperation, ValueProgram,
};
use std::future::Future;
use std::sync::Arc;
use std::task::{Context as TaskContext, Poll, Waker};

fn ready<F: Future>(future: F) -> F::Output {
    let mut future = std::pin::pin!(future);
    let mut context = TaskContext::from_waker(Waker::noop());
    for _ in 0..1000 {
        if let Poll::Ready(output) = future.as_mut().poll(&mut context) {
            return output;
        }
    }
    panic!("finite, synchronous plugin work did not settle");
}
fn provider(
    runtime: &mut Runtime,
    context: &Context,
    key: ServiceKey<ReversibleValue>,
    value: ReversibleValue,
) -> usize {
    let id = runtime
        .mount(
            context,
            None,
            Plugin::new("value provider", move |setup| {
                setup.provide(key, value.clone())?;
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    id
}

#[test]
fn actual_plugins_keep_dependencies_until_the_value_is_recovered() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::new("reversible config");
    let value = ReversibleValue::new(10);
    let provider = provider(&mut runtime, &context, key, value.clone());
    let first = runtime
        .mount(
            &context,
            None,
            Plugin::new("first update", move |setup| {
                let out = setup.update_reversible(key, ValueOperation::Add(5))?;
                assert_eq!(out.after, 15);
                Ok(())
            })
            .requires(key),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    let second = runtime
        .mount(
            &context,
            None,
            Plugin::new("later update", move |setup| {
                setup.update_reversible(key, ValueOperation::Add(7))?;
                Ok(())
            })
            .requires(key),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    let active = runtime.plugin_execution_snapshot(first).unwrap();
    let escaped = runtime.owner_context(first).unwrap();
    runtime.dispose(first).unwrap();
    assert!(matches!(
        ready(runtime.settle()),
        Err(RuntimeError::Cleanup { .. })
    ));
    let failed = runtime.plugin_execution_snapshot(first).unwrap();
    let _old_prefix = active.refresh();
    let _failed_prefix = failed.refresh();
    assert_eq!(value.snapshot().value(), 22);
    assert!(runtime.contains(first));
    assert!(runtime.contains(provider));
    assert!(escaped
        .update_reversible(key, ValueOperation::Replace(0))
        .is_err());
    assert_eq!(value.snapshot().value(), 22);
    runtime.dispose(provider).unwrap();
    let _ = ready(runtime.settle());
    assert!(runtime.contains(provider));
    assert_eq!(runtime.phase(second), Some(cordis::Phase::Inactive));
    assert_eq!(value.snapshot().value(), 15);
    runtime.retry_cleanup(first).unwrap();
    ready(runtime.settle()).unwrap();
    assert!(!runtime.contains(first));
    assert!(runtime.plugin_execution_snapshot(first).is_none());
    assert_eq!(runtime.phase(second), Some(cordis::Phase::Inactive));
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (10, 0)
    );
    assert!(!runtime.contains(provider));
}

#[test]
fn production_program_uses_the_real_comparison_result() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::new("program state");
    let value = ReversibleValue::new(6);
    provider(&mut runtime, &context, key, value.clone());
    let program = ValueProgram::new(vec![
        ValueInstruction {
            operation: ValueOperation::CompareExchange {
                expected: 5,
                value: 80,
            },
            branch: ValueBranch {
                matched: Some(1),
                unmatched: Some(2),
            },
        },
        ValueInstruction {
            operation: ValueOperation::Replace(99),
            branch: ValueBranch {
                matched: None,
                unmatched: None,
            },
        },
        ValueInstruction {
            operation: ValueOperation::Add(4),
            branch: ValueBranch {
                matched: None,
                unmatched: None,
            },
        },
    ])
    .unwrap();
    let consumer = runtime
        .mount(
            &context,
            None,
            Plugin::new("checked program", move |setup| {
                let outcomes = setup.run_value_program(key, &program)?;
                assert_eq!(outcomes.len(), 2);
                assert!(!outcomes[0].matched);
                assert_eq!(outcomes[1].after, 10);
                Ok(())
            })
            .requires(key),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    assert_eq!(value.snapshot().value(), 10);
    runtime.dispose(consumer).unwrap();
    ready(runtime.settle()).unwrap();
    assert_eq!((value.snapshot().value(), value.snapshot().depth()), (6, 0));
}

#[test]
fn production_program_failure_keeps_the_prefix_for_cleanup() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::new("overflow state");
    let value = ReversibleValue::new(6);
    provider(&mut runtime, &context, key, value.clone());
    let program = ValueProgram::new(vec![
        ValueInstruction {
            operation: ValueOperation::Replace(u64::MAX),
            branch: ValueBranch {
                matched: Some(1),
                unmatched: None,
            },
        },
        ValueInstruction {
            operation: ValueOperation::Add(1),
            branch: ValueBranch {
                matched: None,
                unmatched: None,
            },
        },
    ])
    .unwrap();
    let consumer = runtime
        .mount(
            &context,
            None,
            Plugin::new("failing program", move |setup| {
                setup.run_value_program(key, &program)?;
                Ok(())
            })
            .requires(key),
        )
        .unwrap();
    assert!(ready(runtime.settle()).is_err());
    runtime.dispose(consumer).unwrap();
    let _ = ready(runtime.settle());
    assert_eq!((value.snapshot().value(), value.snapshot().depth()), (6, 0));
}

#[test]
fn static_host_executes_the_same_checked_restore() {
    let value = ReversibleValue::new(3);
    let key = ServiceKey::new("static reversible value");
    let context = Context::new();
    let mut plugin = StaticPlugin::new(
        Plugin::new("static update", move |setup| {
            setup.update_reversible(key, ValueOperation::Xor(7))?;
            Ok(())
        })
        .requires(key),
    )
    .unwrap();
    let start = plugin
        .begin(
            5,
            1,
            context.clone(),
            vec![StaticBinding {
                port: context.port(key),
                provider: 0,
                slot: TypedSlot::from_arc(Arc::new(value.clone())),
            }],
        )
        .unwrap();
    ready(start.setup).unwrap();
    assert_eq!(value.snapshot().value(), 4);
    start.episode.cancel();
    ready(start.episode.cleanup().unwrap()).unwrap();
    assert_eq!((value.snapshot().value(), value.snapshot().depth()), (3, 0));
}

#[test]
fn dynamic_publication_swap_preserves_program_target_and_cleanup() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::new("versioned dynamic scalar");
    let owner = runtime
        .mount(&context, None, Plugin::new("owner", |_| Ok(())))
        .unwrap();
    ready(runtime.settle()).unwrap();
    let original = ReversibleValue::new(10);
    let handle = runtime
        .owner_context(owner)
        .unwrap()
        .publish(key, original.clone())
        .unwrap();
    ready(runtime.settle()).unwrap();
    let consumer = runtime
        .mount(
            &context,
            None,
            Plugin::new("consumer", |_| Ok(())).requires(key),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    let setup = runtime.owner_context(consumer).unwrap();
    let mut cursor = setup
        .start_value_program(
            key,
            ValueProgram::new(vec![ValueInstruction {
                operation: ValueOperation::Add(5),
                branch: ValueBranch {
                    matched: None,
                    unmatched: None,
                },
            }])
            .unwrap(),
        )
        .unwrap();
    assert_eq!(cursor.binding().unwrap().provider(), handle.id().unwrap());
    let replacement = ReversibleValue::new(100);
    handle.set(replacement.clone()).unwrap();
    assert_eq!(
        setup.capture_reversible(key).unwrap().capture().revision(),
        1
    );
    assert_eq!(handle.get().unwrap().snapshot().value(), 100);
    assert_eq!(
        setup
            .advance_value_program(&mut cursor)
            .unwrap()
            .unwrap()
            .after,
        15
    );
    assert_eq!(original.snapshot().value(), 15);
    assert_eq!(replacement.snapshot().value(), 100);
    runtime.dispose(consumer).unwrap();
    ready(runtime.settle()).unwrap();
    assert_eq!(original.snapshot().value(), 10);
    assert_eq!(replacement.snapshot().depth(), 0);
    assert!(setup.advance_value_program(&mut cursor).is_err());
    runtime.dispose(owner).unwrap();
    ready(runtime.settle()).unwrap();
    assert!(handle.finished());
    assert!(handle.set(ReversibleValue::new(999)).is_err());
}

#[test]
fn typed_capture_rejects_equal_object_republication_and_keeps_arc_identity() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::new("republished scalar");
    let original = ReversibleValue::new(10);
    let id = provider(&mut runtime, &context, key, original.clone());
    let setup = runtime.owner_context(id).unwrap();
    let error = setup
        .start_value_program(
            ServiceKey::new("undeclared"),
            ValueProgram::new(vec![]).unwrap(),
        )
        .err()
        .unwrap();
    assert_eq!(
        error.service_read().unwrap().reason,
        cordis::ServiceReadFailure::Undeclared
    );
    let captured = setup.capture_reversible(key).unwrap();
    assert!(Arc::ptr_eq(captured.value(), &setup.get(key).unwrap()));
    assert!(captured.capture().check_result(true).accepted());
    setup.set(key, ReversibleValue::new(10)).unwrap();
    setup.set(key, original.clone()).unwrap();
    assert_eq!(captured.capture().refresh().revision(), 2);
    assert_eq!(captured.value().snapshot().value(), 10);
    assert!(!captured.capture().check_result(true).accepted());
    let current = setup.capture_reversible(key).unwrap();
    assert!(current.capture().check_result(true).accepted());
    assert!(!current.capture().check_result(false).accepted());
    // The explicit static adapter sees the same actual Arc, not a rebuilt value.
    let typed = TypedSlot::from_arc(current.value().clone());
    assert!(Arc::ptr_eq(
        current.value(),
        &typed.get::<ReversibleValue>().unwrap()
    ));
    assert!(Arc::ptr_eq(
        current.value(),
        &typed.value().downcast::<ReversibleValue>().ok().unwrap()
    ));
}

#[test]
fn reentrant_typed_predicate_cannot_admit_with_a_replaced_capture() {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Mutex;
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::new("reentrant checked scalar");
    let owner: Arc<Mutex<Option<cordis::AsyncSetup>>> = Arc::default();
    let retained = owner.clone();
    let changed = Arc::new(AtomicBool::new(false));
    let once = changed.clone();
    runtime
        .mount(
            &context,
            None,
            Plugin::new("provider", move |setup| {
                *retained.lock().unwrap() = Some(setup.to_async());
                let retained = retained.clone();
                let once = once.clone();
                setup.provide_checked(key, ReversibleValue::new(10), move |value, _, _| {
                    if !once.swap(true, Ordering::SeqCst) {
                        let setup = retained.lock().unwrap().as_ref().unwrap().clone();
                        setup.set(key, ReversibleValue::new(0)).unwrap();
                        return true;
                    }
                    value.snapshot().value() == 10
                })?;
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    let consumer = runtime
        .mount(
            &context,
            None,
            Plugin::new("consumer", |_| Ok(())).requires(key),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    assert!(changed.load(Ordering::SeqCst));
    assert_eq!(runtime.phase(consumer), Some(cordis::Phase::Inactive));
    assert_eq!(runtime.get(&context, key).unwrap().snapshot().value(), 0);
    owner
        .lock()
        .unwrap()
        .as_ref()
        .unwrap()
        .set(key, ReversibleValue::new(10))
        .unwrap();
    ready(runtime.settle()).unwrap();
    assert_eq!(runtime.phase(consumer), Some(cordis::Phase::Active));
}

#[test]
fn finite_native_root_failure_restores_its_successful_prefix() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::new("checked root failure");
    let value = runtime.reversible_value(u64::MAX - 1);
    let _provider = provider(&mut runtime, &context, key, value.clone());
    let program = ValueProgram::new(vec![
        ValueInstruction {
            operation: ValueOperation::Add(1),
            branch: ValueBranch {
                matched: Some(1),
                unmatched: Some(1),
            },
        },
        ValueInstruction {
            operation: ValueOperation::Add(1),
            branch: ValueBranch {
                matched: None,
                unmatched: None,
            },
        },
    ])
    .unwrap();
    let failed = runtime
        .mount(
            &context,
            None,
            Plugin::native_value_program("overflowing root", key, program),
        )
        .unwrap();
    assert!(ready(runtime.settle()).is_err());
    assert_eq!(value.snapshot().value(), u64::MAX - 1);
    assert_eq!(value.snapshot().depth(), 0);
    assert!(runtime.owner_context(failed).is_err());
    // An actual value observation is paired with its matching execution trace.
    let (actual, execution) = value.observe_execution();
    assert_eq!(actual.value(), u64::MAX - 1);
    let _later = execution.refresh();
}

#[test]
fn shared_execution_domain_allows_concurrent_objects_slots_and_lifecycle() {
    use cordis_kernel::reversible_value::slot::Slot;
    let mut runtime = Runtime::new();
    let context = Context::new();
    let a = Arc::new(runtime.reversible_value(0));
    let b = Arc::new(runtime.reversible_value(1000));
    let slot = Arc::new(Slot::new(a.clone()));
    let branch = ValueBranch {
        matched: None,
        unmatched: None,
    };
    let writers: Vec<_> = [a.clone(), b.clone()]
        .into_iter()
        .map(|value| {
            std::thread::spawn(move || {
                for _ in 0..100 {
                    let _inverse = value.apply(ValueOperation::Add(1), branch).unwrap().inverse;
                    let _observation = value.observe_execution();
                }
            })
        })
        .collect();
    let replace_slot = slot.clone();
    let (old, new) = (a.clone(), b.clone());
    let replacements = std::thread::spawn(move || {
        for i in 0..100 {
            replace_slot
                .replace(if i % 2 == 0 { new.clone() } else { old.clone() })
                .ok()
                .unwrap();
            let capture = replace_slot.capture();
            let _observed = capture.observe_value();
        }
    });
    for _ in 0..10 {
        let id = runtime
            .mount(
                &context,
                None,
                Plugin::new("concurrent lifecycle", |_| Ok(())),
            )
            .unwrap();
        ready(runtime.settle()).unwrap();
        runtime.dispose(id).unwrap();
        ready(runtime.settle()).unwrap();
    }
    for writer in writers {
        writer.join().unwrap();
    }
    replacements.join().unwrap();
    assert_eq!((a.snapshot().value(), a.snapshot().depth()), (100, 100));
    assert_eq!((b.snapshot().value(), b.snapshot().depth()), (1100, 100));
    let current = slot.capture();
    assert_eq!(current.revision(), 100);
    assert!(Arc::ptr_eq(current.value(), &a));
}

fn finite_add(amount: u64) -> ValueProgram {
    ValueProgram::new(vec![ValueInstruction {
        operation: ValueOperation::Add(amount),
        branch: ValueBranch {
            matched: None,
            unmatched: None,
        },
    }])
    .unwrap()
}

#[test]
fn finite_child_resolves_its_registered_realm_before_inherited_aliases() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::new("registered realm");
    let isolated = context.isolate(key);
    let original = runtime.reversible_value(10);
    let other = runtime.reversible_value(1000);
    provider(&mut runtime, &context, key, original.clone());
    provider(&mut runtime, &isolated, key, other.clone());
    let parent = runtime
        .mount(
            &context,
            None,
            Plugin::new("parent", move |setup| {
                setup.mount_in(
                    &isolated,
                    Plugin::native_value_program("finite Child", key, finite_add(3)),
                )?;
                Ok(())
            })
            .requires(key),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    assert_eq!(
        (original.snapshot().value(), other.snapshot().value()),
        (10, 1003)
    );
    runtime.dispose(parent).unwrap();
    ready(runtime.settle()).unwrap();
    assert_eq!(
        (
            original.snapshot().depth(),
            other.snapshot().value(),
            other.snapshot().depth()
        ),
        (0, 1000, 0)
    );
}

#[test]
fn finite_root_hot_update_restores_previous_body_before_running_the_new_one() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::new("registered update");
    let value = runtime.reversible_value(10);
    provider(&mut runtime, &context, key, value.clone());
    let id = runtime
        .mount(
            &context,
            None,
            Plugin::native_value_program("v1", key, finite_add(5)),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    assert_eq!(value.snapshot().value(), 15);
    runtime
        .update_plugin(id, Plugin::native_value_program("v2", key, finite_add(7)))
        .unwrap();
    ready(runtime.settle()).unwrap();
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (17, 1)
    );
    runtime.dispose(id).unwrap();
    ready(runtime.settle()).unwrap();
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (10, 0)
    );
}

#[test]
fn static_host_rejects_native_registered_body_without_writing_the_value() {
    let key = ServiceKey::new("native only");
    let context = Context::new();
    let value = ReversibleValue::new(10);
    let mut plugin =
        StaticPlugin::new(Plugin::native_value_program("native", key, finite_add(5))).unwrap();
    let start = plugin
        .begin(
            5,
            1,
            context.clone(),
            vec![StaticBinding {
                port: context.port(key),
                provider: 0,
                slot: TypedSlot::from_arc(Arc::new(value.clone())),
            }],
        )
        .unwrap();
    assert!(ready(start.setup)
        .unwrap_err()
        .to_string()
        .contains("native Runtime"));
    start.episode.cancel();
    ready(start.episode.cleanup().unwrap()).unwrap();
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (10, 0)
    );
}

#[test]
fn production_service_checkpoints_overlap_replacement_without_lock_inversion() {
    use std::sync::mpsc;
    use std::time::Duration;
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::new("concurrent publication checkpoint");
    let value = runtime.reversible_value(10);
    let id = provider(&mut runtime, &context, key, value.clone());
    let setup = runtime.owner_context(id).unwrap();
    let captured = setup.capture_reversible(key).unwrap();
    let (done, completion) = mpsc::channel();
    let worker = std::thread::spawn(move || {
        for i in 0..200 {
            // Alternate a same-domain and a foreign object; equal values must
            // still advance the real slot revision and invalidate old checks.
            setup
                .set(
                    key,
                    if i % 2 == 0 {
                        value.clone()
                    } else {
                        ReversibleValue::new(10)
                    },
                )
                .unwrap();
            let selected = setup.capture_reversible(key).unwrap();
            let _ = selected.capture().execution_snapshot();
        }
        done.send(()).unwrap();
    });
    for _ in 0..200 {
        let _ = runtime.execution_snapshot();
        let _ = runtime.plugin_execution_snapshot(id).unwrap();
    }
    completion.recv_timeout(Duration::from_secs(10)).unwrap();
    worker.join().unwrap();
    assert_eq!(captured.capture().refresh().revision(), 200);
    assert!(!captured.capture().check_result(true).accepted());
    let history = captured.capture().execution_snapshot();
    runtime.dispose(id).unwrap();
    ready(runtime.settle()).unwrap();
    assert!(runtime.plugin_execution_snapshot(id).is_none());
    let _ = history.refresh();
}

#[test]
fn effect_status_tracks_real_value_interference_failure_and_retry() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::new("effect recovery status");
    let value = ReversibleValue::new(10);
    let provider = provider(&mut runtime, &context, key, value.clone());
    let owner = runtime
        .mount(
            &context,
            None,
            Plugin::new("effect owner", |_| Ok(())).requires(key),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    let handle = runtime
        .effect(
            owner,
            cordis::Effect::new().step(move |setup| async move {
                setup.update_reversible(key, ValueOperation::Add(5))?;
                Ok(cordis::Inverse::empty())
            }),
        )
        .unwrap();
    assert!(!handle.initialized());
    ready(runtime.settle()).unwrap();
    assert!(handle.initialized());
    assert!(!handle.finished());
    let start = handle.execution_snapshot();
    let interfering = value
        .apply(
            ValueOperation::Add(7),
            ValueBranch {
                matched: None,
                unmatched: None,
            },
        )
        .unwrap();
    handle.cancel();
    assert!(matches!(
        ready(runtime.settle()),
        Err(RuntimeError::Cleanup { .. })
    ));
    assert!(!handle.finished());
    assert_eq!(handle.errors().len(), 1);
    assert_eq!(value.snapshot().value(), 22);
    assert!(runtime.contains(provider));
    let failed = handle.execution_snapshot();
    assert!(interfering.inverse.restore().is_ok());
    runtime.retry_cleanup(owner).unwrap();
    ready(runtime.settle()).unwrap();
    assert!(handle.finished());
    assert_eq!(handle.errors().len(), 1); // Retry retains the actual failed attempt.
    assert!(ready(handle.join()).is_err());
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (10, 0)
    );
    let _ = failed.refresh();
    let _ = start.refresh();
    let _ = handle.execution_snapshot();
}

#[test]
fn ordinary_child_declarations_follow_aliases_replacement_and_retained_cleanup() {
    use std::sync::Mutex;
    let mut runtime = Runtime::new();
    let context = Context::new();
    let left = ServiceKey::new("declared left");
    let right = ServiceKey::new("declared alias");
    let other = ServiceKey::new("independent object");
    let missing = ServiceKey::new("not declared by Child");
    let original = runtime.reversible_value(10);
    let independent = runtime.reversible_value(900);
    let shared = original.clone();
    let separate = independent.clone();
    let provider_id = runtime
        .mount(
            &context,
            None,
            Plugin::new("alias provider", move |setup| {
                setup.provide(left, shared.clone())?;
                setup.provide(right, shared.clone())?;
                setup.provide(other, separate.clone())?;
                Ok(())
            })
            .provides(left)
            .provides(right)
            .provides(other),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    let retained: Arc<Mutex<Option<cordis::AsyncSetup>>> = Arc::default();
    let child_context = retained.clone();
    let parent = runtime
        .mount(
            &context,
            None,
            Plugin::new("ordinary parent", move |setup| {
                let child_context = child_context.clone();
                setup.mount(
                    Plugin::new("ordinary Child", move |child| {
                        assert_eq!(child.observe_reversible(left)?.value(), 10);
                        assert_eq!(
                            child.observe_reversible(missing).err().unwrap().reason,
                            cordis::ServiceReadFailure::Undeclared
                        );
                        child.update_reversible(left, ValueOperation::Add(2))?;
                        assert_eq!(child.observe_reversible(right)?.value(), 12);
                        child.run_value_program(right, &finite_add(3))?;
                        assert_eq!(child.observe_reversible(other)?.value(), 900);
                        *child_context.lock().unwrap() = Some(child.to_async());
                        Ok(())
                    })
                    .requires(left)
                    .requires(right)
                    .requires(other),
                )?;
                Ok(())
            }),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    let child = retained.lock().unwrap().clone().unwrap();
    let selected = child.capture_reversible(left).unwrap();
    let replacement = runtime.reversible_value(100);
    runtime
        .owner_context(provider_id)
        .unwrap()
        .set(left, replacement.clone())
        .unwrap();
    child
        .update_reversible(left, ValueOperation::Add(7))
        .unwrap();
    assert_eq!(child.observe_reversible(left).unwrap().value(), 107);
    assert_eq!(child.observe_reversible(right).unwrap().value(), 15);
    assert_eq!(selected.capture().observe_value().value(), 15);
    assert_eq!(independent.snapshot().depth(), 0);
    runtime.dispose(parent).unwrap();
    ready(runtime.settle()).unwrap();
    assert_eq!(
        (original.snapshot().value(), original.snapshot().depth()),
        (10, 0)
    );
    assert_eq!(
        (
            replacement.snapshot().value(),
            replacement.snapshot().depth()
        ),
        (100, 0)
    );
    assert!(child.observe_reversible(left).is_err());
    runtime.dispose(provider_id).unwrap();
    ready(runtime.settle()).unwrap();
}

#[test]
fn child_multi_service_body_uses_current_slots_and_retains_failed_prefixes() {
    use cordis::{AsyncSetup, ServiceInstruction, ValueBranch};
    use std::sync::Mutex;
    let mut runtime = Runtime::new();
    let context = Context::new();
    let left = ServiceKey::new("multi-service left");
    let alias = ServiceKey::new("multi-service alias");
    let foreign_key = ServiceKey::new("separate Journal");
    let hidden = ServiceKey::new("undeclared branch");
    let original = runtime.reversible_value(10);
    let foreign = ReversibleValue::new(50);
    let shared = original.clone();
    let external = foreign.clone();
    let provider = runtime
        .mount(
            &context,
            None,
            Plugin::new("multi-service provider", move |setup| {
                setup.provide(left, shared.clone())?;
                setup.provide(alias, shared.clone())?;
                setup.provide(foreign_key, external.clone())?;
                Ok(())
            })
            .provides(left)
            .provides(alias)
            .provides(foreign_key),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    let retained: Arc<Mutex<Option<AsyncSetup>>> = Arc::default();
    let child_handle = retained.clone();
    let parent = runtime
        .mount(
            &context,
            None,
            Plugin::new("multi-service parent", move |setup| {
                let child_handle = child_handle.clone();
                setup.mount(
                    Plugin::new("multi-service Child", move |child| {
                        let end = ValueBranch {
                            matched: None,
                            unmatched: None,
                        };
                        assert!(child
                            .run_service_program(&[
                                ServiceInstruction {
                                    key: left,
                                    operation: ValueOperation::Add(100),
                                    branch: end
                                },
                                ServiceInstruction {
                                    key: hidden,
                                    operation: ValueOperation::Add(1),
                                    branch: end
                                },
                            ])
                            .is_err());
                        assert_eq!(child.observe_reversible(left)?.value(), 10);
                        assert!(child
                            .run_service_program(&[ServiceInstruction {
                                key: left,
                                operation: ValueOperation::Add(100),
                                branch: ValueBranch {
                                    matched: Some(0),
                                    unmatched: None
                                }
                            }])
                            .is_err());
                        let out = child.run_service_program(&[
                            ServiceInstruction {
                                key: left,
                                operation: ValueOperation::Add(2),
                                branch: ValueBranch {
                                    matched: Some(1),
                                    unmatched: Some(1),
                                },
                            },
                            ServiceInstruction {
                                key: alias,
                                operation: ValueOperation::CompareExchange {
                                    expected: 0,
                                    value: 99,
                                },
                                branch: ValueBranch {
                                    matched: Some(2),
                                    unmatched: Some(3),
                                },
                            },
                            ServiceInstruction {
                                key: left,
                                operation: ValueOperation::Replace(999),
                                branch: end,
                            },
                            ServiceInstruction {
                                key: foreign_key,
                                operation: ValueOperation::Add(1),
                                branch: end,
                            },
                        ])?;
                        assert_eq!(
                            out.iter().map(|o| o.after).collect::<Vec<_>>(),
                            [12, 12, 51]
                        );
                        assert!(!out[1].matched);
                        *child_handle.lock().unwrap() = Some(child.to_async());
                        Ok(())
                    })
                    .requires(left)
                    .requires(alias)
                    .requires(foreign_key),
                )?;
                Ok(())
            }),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    let child = retained.lock().unwrap().clone().unwrap();
    let old = child.capture_reversible(left).unwrap();
    let replacement = runtime.reversible_value(100);
    runtime
        .owner_context(provider)
        .unwrap()
        .set(left, replacement.clone())
        .unwrap();
    let code = [
        ServiceInstruction {
            key: left,
            operation: ValueOperation::Add(7),
            branch: ValueBranch {
                matched: Some(1),
                unmatched: Some(1),
            },
        },
        ServiceInstruction {
            key: alias,
            operation: ValueOperation::Add(3),
            branch: ValueBranch {
                matched: Some(2),
                unmatched: Some(2),
            },
        },
        ServiceInstruction {
            key: foreign_key,
            operation: ValueOperation::Add(u64::MAX),
            branch: ValueBranch {
                matched: None,
                unmatched: None,
            },
        },
    ];
    assert!(child.run_service_program(&code).is_err());
    assert_eq!(replacement.snapshot().value(), 107);
    assert_eq!(old.capture().observe_value().value(), 15);
    assert_eq!(foreign.snapshot().value(), 51);
    runtime.dispose(parent).unwrap();
    ready(runtime.settle()).unwrap();
    for (value, expected) in [(&original, 10), (&replacement, 100), (&foreign, 50)] {
        assert_eq!(
            (value.snapshot().value(), value.snapshot().depth()),
            (expected, 0)
        );
    }
    assert!(child.run_service_program(&code).is_err());
    runtime.dispose(provider).unwrap();
    ready(runtime.settle()).unwrap();
}

// Ordinary test code deliberately reenters the adapter. It checks lock/lifecycle
// behavior, and does not claim a Verus model law for this callback.
struct ReentrantScalar<F>(F);
impl<F: FnOnce()> cordis::ScalarEffect for ReentrantScalar<F> {
    fn compute(self, input: u64) -> Option<cordis::ScalarDecision> {
        (self.0)();
        Some(cordis::ScalarDecision {
            value: input + 5,
            matched: true,
        })
    }
}

#[test]
fn child_extensible_effects_keep_aliases_old_targets_and_reentrant_failure_prefixes() {
    use cordis::{AsyncSetup, ChooseScalar, ScaleAdd, ThenScalar};
    use std::sync::Mutex;
    let mut runtime = Runtime::new();
    let context = Context::new();
    let left = ServiceKey::new("effect left");
    let alias = ServiceKey::new("effect alias");
    let missing = ServiceKey::<ReversibleValue>::new("effect undeclared");
    let original = runtime.reversible_value(10);
    let value = original.clone();
    let provider = runtime
        .mount(
            &context,
            None,
            Plugin::new("effect provider", move |setup| {
                setup.provide(left, value.clone())?;
                setup.provide(alias, value.clone())?;
                Ok(())
            })
            .provides(left)
            .provides(alias),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    let escaped: Arc<Mutex<Option<AsyncSetup>>> = Arc::default();
    let retained = escaped.clone();
    let parent = runtime
        .mount(
            &context,
            None,
            Plugin::new("effect parent", move |setup| {
                let retained = retained.clone();
                setup.mount(
                    Plugin::new("effect Child", move |child| {
                        assert!(child
                            .update_reversible_with(missing, ValueOperation::Add(100))
                            .is_err());
                        child.update_reversible_with(
                            left,
                            ThenScalar {
                                first: ScaleAdd {
                                    scale: 2,
                                    offset: 1,
                                },
                                then: ValueOperation::Add(3),
                            },
                        )?;
                        assert_eq!(child.observe_reversible(alias)?.value(), 24);
                        child.update_reversible_with(
                            alias,
                            ChooseScalar {
                                predicate: ValueOperation::CompareExchange {
                                    expected: 24,
                                    value: 30,
                                },
                                matched: ValueOperation::Add(2),
                                unmatched: ValueOperation::Add(99),
                            },
                        )?;
                        child.update_reversible_with(
                            left,
                            ChooseScalar {
                                predicate: ValueOperation::CompareExchange {
                                    expected: 999,
                                    value: 0,
                                },
                                matched: ValueOperation::Add(99),
                                unmatched: ValueOperation::Add(1),
                            },
                        )?;
                        assert_eq!(child.observe_reversible(alias)?.value(), 33);
                        *retained.lock().unwrap() = Some(child.to_async());
                        Ok(())
                    })
                    .requires(left)
                    .requires(alias),
                )?;
                Ok(())
            }),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    let child = escaped.lock().unwrap().clone().unwrap();
    let replacement = runtime.reversible_value(100);
    let owner = runtime.owner_context(provider).unwrap();
    let fresh = replacement.clone();
    let reenter = child.clone();
    let result = child
        .update_reversible_with(
            left,
            ReentrantScalar(move || {
                // This read reenters the same host mutex, proving calculation is outside it.
                assert_eq!(reenter.observe_reversible(alias).unwrap().value(), 33);
                owner.set(left, fresh).unwrap();
            }),
        )
        .unwrap();
    assert_eq!((result.before, result.after), (33, 38));
    assert_eq!(child.observe_reversible(left).unwrap().value(), 100);
    assert_eq!(child.observe_reversible(alias).unwrap().value(), 38);
    child
        .update_reversible_with(
            left,
            ScaleAdd {
                scale: 2,
                offset: 0,
            },
        )
        .unwrap();
    let reenter = child.clone();
    assert!(child
        .update_reversible_with(
            alias,
            ReentrantScalar(move || {
                reenter
                    .update_reversible(alias, ValueOperation::Add(1))
                    .unwrap();
            })
        )
        .is_err());
    assert_eq!(
        (original.snapshot().value(), original.snapshot().depth()),
        (39, 5)
    );
    assert!(child
        .update_reversible_with(
            alias,
            ScaleAdd {
                scale: u64::MAX,
                offset: 1
            }
        )
        .is_err());
    assert!(child
        .update_reversible_with(
            alias,
            ReentrantScalar(|| panic!("effect computation panic"))
        )
        .is_err());
    assert_eq!(
        (original.snapshot().value(), original.snapshot().depth()),
        (39, 5)
    );
    runtime.dispose(parent).unwrap();
    ready(runtime.settle()).unwrap();
    assert_eq!(
        (original.snapshot().value(), original.snapshot().depth()),
        (10, 0)
    );
    assert_eq!(
        (
            replacement.snapshot().value(),
            replacement.snapshot().depth()
        ),
        (100, 0)
    );
    assert!(child
        .update_reversible_with(alias, ValueOperation::Add(1))
        .is_err());
    runtime.dispose(provider).unwrap();
    ready(runtime.settle()).unwrap();
}

#[test]
fn registered_multi_service_child_resolves_realms_and_aliases_and_unloads() {
    use cordis::ServiceInstruction;
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::new("multi service realm");
    let alias = ServiceKey::new("multi service alias");
    let isolated = context.isolate(key);
    let original = runtime.reversible_value(10);
    let other = runtime.reversible_value(1000);
    provider(&mut runtime, &context, key, original.clone());
    provider(&mut runtime, &isolated, key, other.clone());
    provider(&mut runtime, &isolated, alias, other.clone());
    let parent = runtime
        .mount(
            &context,
            None,
            Plugin::new("multi service parent", move |setup| {
                let body = Plugin::native_service_program(
                    "registered multi Child",
                    vec![
                        ServiceInstruction {
                            key,
                            operation: ValueOperation::Add(3),
                            branch: ValueBranch {
                                matched: Some(1),
                                unmatched: Some(1),
                            },
                        },
                        ServiceInstruction {
                            key: alias,
                            operation: ValueOperation::CompareExchange {
                                expected: 1003,
                                value: 1007,
                            },
                            branch: ValueBranch {
                                matched: None,
                                unmatched: None,
                            },
                        },
                    ],
                )?;
                setup.mount_in(&isolated, body)?;
                Ok(())
            })
            .requires(key),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    assert_eq!(
        (
            original.snapshot().value(),
            other.snapshot().value(),
            other.snapshot().depth()
        ),
        (10, 1007, 2)
    );
    runtime.dispose(parent).unwrap();
    ready(runtime.settle()).unwrap();
    assert_eq!(
        (
            original.snapshot().depth(),
            other.snapshot().value(),
            other.snapshot().depth()
        ),
        (0, 1000, 0)
    );
}

#[test]
fn registered_multi_service_update_and_failure_restore_the_actual_prefix() {
    use cordis::ServiceInstruction;
    let mut runtime = Runtime::new();
    let context = Context::new();
    let a = ServiceKey::new("registered multi local");
    let b = ServiceKey::new("registered multi foreign");
    let local = runtime.reversible_value(10);
    let foreign = ReversibleValue::new(40);
    provider(&mut runtime, &context, a, local.clone());
    provider(&mut runtime, &context, b, foreign.clone());
    let end = ValueBranch {
        matched: None,
        unmatched: None,
    };
    let next = ValueBranch {
        matched: Some(1),
        unmatched: Some(1),
    };
    let body = |x, y| {
        Plugin::native_service_program(
            "multi root",
            vec![
                ServiceInstruction {
                    key: a,
                    operation: ValueOperation::Add(x),
                    branch: next,
                },
                ServiceInstruction {
                    key: b,
                    operation: ValueOperation::Add(y),
                    branch: end,
                },
            ],
        )
        .unwrap()
    };
    let id = runtime.mount(&context, None, body(5, 3)).unwrap();
    ready(runtime.settle()).unwrap();
    assert_eq!(
        (local.snapshot().value(), foreign.snapshot().value()),
        (15, 43)
    );
    runtime.update_plugin(id, body(7, 4)).unwrap();
    ready(runtime.settle()).unwrap();
    assert_eq!(
        (local.snapshot().value(), foreign.snapshot().value()),
        (17, 44)
    );
    runtime.update_plugin(id, body(9, u64::MAX)).unwrap();
    assert!(ready(runtime.settle()).is_err());
    assert_eq!(
        (
            local.snapshot().value(),
            local.snapshot().depth(),
            foreign.snapshot().value(),
            foreign.snapshot().depth()
        ),
        (10, 0, 40, 0)
    );
    assert!(runtime.owner_context(id).is_err());
}

#[test]
fn registered_service_program_rejects_invalid_branches_and_static_dispatch() {
    use cordis::ServiceInstruction;
    let key = ServiceKey::new("registered finite validation");
    assert!(Plugin::native_service_program(
        "backward",
        vec![ServiceInstruction {
            key,
            operation: ValueOperation::Add(1),
            branch: ValueBranch {
                matched: Some(0),
                unmatched: None
            },
        }]
    )
    .is_err());
    assert!(Plugin::native_service_program(
        "out of bounds",
        vec![ServiceInstruction {
            key,
            operation: ValueOperation::Add(1),
            branch: ValueBranch {
                matched: None,
                unmatched: Some(1)
            },
        }]
    )
    .is_err());
    // Even an empty finite body must not silently become an ordinary callback.
    let mut runtime = Runtime::new();
    let empty = runtime
        .mount(
            &Context::new(),
            None,
            Plugin::native_service_program("empty", vec![]).unwrap(),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    assert!(runtime.owner_context(empty).is_ok());
    runtime.dispose(empty).unwrap();
    ready(runtime.settle()).unwrap();
    let mut plugin =
        StaticPlugin::new(Plugin::native_service_program("native only", vec![]).unwrap()).unwrap();
    let start = plugin.begin(6, 1, Context::new(), vec![]).unwrap();
    assert!(ready(start.setup)
        .unwrap_err()
        .to_string()
        .contains("native Runtime"));
    start.episode.cancel();
    ready(start.episode.cleanup().unwrap()).unwrap();
}
