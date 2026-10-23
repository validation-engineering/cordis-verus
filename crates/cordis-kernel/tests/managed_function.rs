use cordis_kernel::cleanup_groups::payload::Dispatch;
use cordis_kernel::cleanup_queue::completion::CleanupDispatch;
use cordis_kernel::lifecycle_state::native::runtime::NativeRuntime;
use cordis_kernel::lifecycle_state::registration::PluginDefinition;
use cordis_kernel::reversible_value::effect::ScaleAdd;
use cordis_kernel::reversible_value::function::Body;
use cordis_kernel::reversible_value::managed::root::AdmissionError;
use cordis_kernel::reversible_value::managed::{Call, Effect, Error, Function, Owner, Slot};
use cordis_kernel::reversible_value::payload::SharedPayload;
use cordis_kernel::reversible_value::{Branch, ReversibleValue};
use cordis_kernel::setup_work::RootStatus;
use cordis_kernel::Port;
use std::{collections::BTreeMap, sync::Arc};
type Callback = fn(()) -> Result<(), ()>;
type World = NativeRuntime<Body<Callback, Function<ScaleAdd, String>>, (), Slot<String, ()>>;
type Episode = Owner<(), (), (), (), String, (), ()>;
fn port(key: u64) -> Port {
    Port { key, realm: 0 }
}
fn end() -> Branch {
    Branch {
        matched: None,
        unmatched: None,
    }
}
fn mount(
    world: &mut World,
    anchor: u64,
    deps: Vec<u64>,
    provisions: Vec<u64>,
    body: Body<Callback, Function<ScaleAdd, String>>,
) -> usize {
    world
        .register(
            None,
            &BTreeMap::new(),
            port(anchor),
            PluginDefinition::new(deps, provisions, body),
            (),
        )
        .ok()
        .unwrap()
}
fn fixture() -> (World, ReversibleValue, SharedPayload<String>) {
    fixture_with_recording(false)
}
fn fixture_with_recording(record: bool) -> (World, ReversibleValue, SharedPayload<String>) {
    let mut world = if record {
        World::new_recorded(9510, 256)
    } else {
        World::new(9510)
    };
    let scalar = ReversibleValue::new_in(&world.execution_journal(), 10);
    let payload = SharedPayload::new_in(&world.execution_journal(), Arc::new("old".to_owned()));
    let id = mount(
        &mut world,
        100,
        vec![],
        vec![1, 2],
        Body::Callback((|()| Ok(())) as Callback),
    );
    let mut owner: Episode = world.begin_managed_execution(id, 9511).unwrap();
    let invocation = world.admit_managed_root(id, &mut owner, ()).unwrap();
    let receipt = world.call_opaque(id, invocation).ok().unwrap();
    owner.complete_root(receipt).ok().unwrap().unwrap();
    owner
        .provide(
            port(1),
            Arc::new(Slot::new_reversible(Arc::new(scalar.clone()), ())),
        )
        .ok()
        .unwrap();
    owner
        .provide(port(2), Arc::new(Slot::new_opaque(payload.clone(), ())))
        .ok()
        .unwrap();
    world.finish_managed_execution(id, &mut owner).unwrap();
    (world, scalar, payload)
}
fn body(scale: u64) -> Body<Callback, Function<ScaleAdd, String>> {
    Body::Managed(
        Function::new(vec![
            Call {
                key: 1,
                effect: Effect::Scalar(ScaleAdd { scale, offset: 1 }),
                branch: Branch {
                    matched: Some(1),
                    unmatched: Some(1),
                },
            },
            Call {
                key: 2,
                effect: Effect::Replace(Arc::new("checked".to_owned())),
                branch: end(),
            },
        ])
        .ok()
        .unwrap(),
    )
}
#[test]
fn extensible_scalar_effect_runs_with_typed_replacement_and_the_real_mixed_queue() {
    let (mut world, scalar, payload) = fixture();
    let id = mount(&mut world, 101, vec![1, 2], vec![], body(2));
    let mut owner: Episode = world.begin_managed_execution(id, 9512).unwrap();
    let report = world.run_managed_root(id, &mut owner).unwrap();
    let result = report.result.unwrap();
    assert_eq!(result.steps.len(), 2);
    assert!(result.failure.is_none());
    assert_eq!(scalar.snapshot().value(), 21);
    assert_eq!(payload.capture().unwrap().value().as_str(), "checked");
    owner.withdraw();
    let Dispatch::Payload(done) = owner.dispatch_payload_cleanup(0).unwrap().unwrap() else {
        panic!("last typed inverse")
    };
    assert!(done.report.result.is_ok());
    assert_eq!(payload.capture().unwrap().value().as_str(), "old");
    assert_eq!(scalar.snapshot().value(), 21);
    let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
        owner.dispatch_payload_cleanup(0).unwrap().unwrap()
    else {
        panic!("first scalar inverse")
    };
    assert!(completion.report.result.is_ok());
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (10, 0)
    );
    payload.retire();
}
#[test]
fn revision_wrong_owner_and_repeated_invocation_are_checked_before_execution() {
    let (mut world, scalar, payload) = fixture();
    let id = mount(&mut world, 101, vec![1, 2], vec![], body(2));
    let other = mount(&mut world, 102, vec![1, 2], vec![], body(3));
    let mut a: Episode = world.begin_managed_execution(id, 9520).unwrap();
    let mut b: Episode = world.begin_managed_execution(other, 9521).unwrap();
    assert!(matches!(
        world.run_managed_root(id, &mut b),
        Err(AdmissionError::WrongOwner)
    ));
    assert_eq!(b.work().root(), RootStatus::Unissued);
    world.replace(id, body(4)).ok().unwrap();
    let report = world.run_managed_root(id, &mut a).unwrap();
    assert_eq!(report.revision, 1);
    assert!(report.result.unwrap().succeeded());
    assert_eq!(scalar.snapshot().value(), 41);
    assert!(matches!(
        world.run_managed_root(id, &mut a),
        Err(AdmissionError::NotAdmitted)
    ));
    assert_eq!(scalar.snapshot().depth(), 1);
    payload.retire();
}
#[test]
fn unreachable_dependency_is_bound_before_root_issuance() {
    let (mut world, scalar, payload) = fixture();
    let function = Function::new(vec![
        Call {
            key: 1,
            effect: Effect::Scalar(ScaleAdd {
                scale: 2,
                offset: 0,
            }),
            branch: end(),
        },
        Call {
            key: 99,
            effect: Effect::Replace(Arc::new("unreachable".to_owned())),
            branch: end(),
        },
    ])
    .ok()
    .unwrap();
    let id = mount(&mut world, 101, vec![1], vec![], Body::Managed(function));
    let mut owner: Episode = world.begin_managed_execution(id, 9530).unwrap();
    assert!(matches!(
        world.run_managed_root(id, &mut owner),
        Err(AdmissionError::MissingDependency { pc: 1 })
    ));
    assert_eq!(owner.work().root(), RootStatus::Unissued);
    assert_eq!(scalar.snapshot().value(), 10);
    payload.retire();
}
#[test]
fn retired_payload_failure_keeps_the_scalar_prefix_for_real_cleanup() {
    let (mut world, scalar, payload) = fixture();
    let id = mount(&mut world, 101, vec![1, 2], vec![], body(2));
    let mut owner: Episode = world.begin_managed_execution(id, 9540).unwrap();
    payload.retire();
    let report = world
        .run_managed_root(id, &mut owner)
        .unwrap()
        .result
        .unwrap();
    assert_eq!(report.steps.len(), 1);
    let failure = report.failure.unwrap();
    assert_eq!(failure.pc, 1);
    assert!(matches!(
        failure.error,
        Error::Payload(cordis_kernel::cleanup_groups::payload::AccessError::Value(
            cordis_kernel::versioned_value::ReplaceError::Closed
        ))
    ));
    assert!(owner.work().root_failed_now());
    owner.withdraw();
    let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
        owner.dispatch_payload_cleanup(0).unwrap().unwrap()
    else {
        panic!("successful scalar prefix survives")
    };
    assert!(completion.report.result.is_ok());
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (10, 0)
    );
}

#[test]
fn direct_managed_calls_cannot_substitute_a_different_declared_key() {
    let (mut world, scalar, payload) = fixture();
    let id = mount(&mut world, 101, vec![1, 2], vec![], body(2));
    let mut owner: Episode = world.begin_managed_execution(id, 9550).unwrap();
    let function = Function::new(vec![Call {
        key: 1,
        effect: Effect::<ScaleAdd, String>::Scalar(ScaleAdd {
            scale: 2,
            offset: 0,
        }),
        branch: end(),
    }])
    .ok()
    .unwrap();
    assert!(matches!(
        owner.run_function(0, &function, &[port(2)]),
        Err(cordis_kernel::reversible_value::managed::AdmissionError::WrongKey { pc: 0 })
    ));
    assert_eq!(scalar.snapshot().value(), 10);
    assert_eq!(payload.capture().unwrap().value().as_str(), "old");
    payload.retire();
}
#[test]
fn scalar_read_of_typed_storage_reports_the_actual_kind_mismatch() {
    let (mut world, scalar, payload) = fixture();
    let function = Function::new(vec![Call {
        key: 2,
        effect: Effect::<ScaleAdd, String>::Scalar(ScaleAdd {
            scale: 2,
            offset: 0,
        }),
        branch: end(),
    }])
    .ok()
    .unwrap();
    let id = mount(&mut world, 101, vec![2], vec![], Body::Managed(function));
    let mut owner: Episode = world.begin_managed_execution(id, 9560).unwrap();
    let report = world
        .run_managed_root(id, &mut owner)
        .unwrap()
        .result
        .unwrap();
    assert!(report.steps.is_empty());
    assert!(matches!(
        report.failure.unwrap().error,
        Error::Capture(cordis_kernel::reversible_value::cursor::StartError::Read(
            cordis_kernel::reversible_value::slot::ReadError::NotReversible { .. }
        ))
    ));
    assert!(owner.work().root_failed_now());
    assert_eq!(scalar.snapshot().value(), 10);
    assert_eq!(payload.capture().unwrap().value().as_str(), "old");
    payload.retire();
}

fn alias_provider(world: &mut World, scalar: &ReversibleValue, payload: &SharedPayload<String>) {
    let id = mount(
        world,
        110,
        vec![],
        vec![3, 4],
        Body::Callback((|()| Ok(())) as Callback),
    );
    let mut owner: Episode = world.begin_managed_execution(id, 9600).unwrap();
    let invocation = world.admit_managed_root(id, &mut owner, ()).unwrap();
    let receipt = world.call_opaque(id, invocation).ok().unwrap();
    owner.complete_root(receipt).ok().unwrap().unwrap();
    owner
        .provide(
            port(3),
            Arc::new(Slot::new_reversible(Arc::new(scalar.clone()), ())),
        )
        .ok()
        .unwrap();
    owner
        .provide(port(4), Arc::new(Slot::new_opaque(payload.clone(), ())))
        .ok()
        .unwrap();
    world.finish_managed_execution(id, &mut owner).unwrap();
}

#[test]
fn mixed_alias_history_recovers_after_same_value_foreign_write_and_retry() {
    use cordis_kernel::async_completion::await_completion;
    use cordis_kernel::cleanup_groups::payload::Cleanup;
    use cordis_kernel::cleanup_queue::completion::CleanupPolicy;
    use cordis_kernel::lifecycle_state::registration::shared_child::ChildCleanup;
    use cordis_kernel::reversible_value::managed::interleaving::history::lifecycle::callbacks::HostAction;
    use cordis_kernel::reversible_value::payload::restoration::RestoreError;
    use std::future::Future;
    use std::task::{Context, Poll, Waker};
    fn ready<F: Future>(future: F) -> F::Output {
        match Box::pin(future)
            .as_mut()
            .poll(&mut Context::from_waker(Waker::noop()))
        {
            Poll::Ready(value) => value,
            Poll::Pending => panic!("expected ready completion"),
        }
    }

    let (mut world, scalar, payload) = fixture();
    alias_provider(&mut world, &scalar, &payload);
    let effects = vec![
        (
            1,
            Effect::Scalar(ScaleAdd {
                scale: 2,
                offset: 1,
            }),
        ),
        (2, Effect::Replace(Arc::new("alpha".to_owned()))),
        (
            3,
            Effect::Scalar(ScaleAdd {
                scale: 3,
                offset: 2,
            }),
        ),
        (4, Effect::Replace(Arc::new("beta".to_owned()))),
        (
            1,
            Effect::Scalar(ScaleAdd {
                scale: 1,
                offset: 0,
            }),
        ),
    ];
    let count = effects.len();
    let function = Function::new(
        effects
            .into_iter()
            .enumerate()
            .map(|(pc, (key, effect))| {
                let next = (pc + 1 < count).then_some(pc + 1);
                Call {
                    key,
                    effect,
                    branch: Branch {
                        matched: next,
                        unmatched: next,
                    },
                }
            })
            .collect(),
    )
    .ok()
    .unwrap();
    let id = mount(
        &mut world,
        111,
        vec![1, 2, 3, 4],
        vec![],
        Body::Managed(function),
    );
    let initial: Episode = world.begin_managed_execution(id, 9601).unwrap();
    let (mut owner, report) = world.run_recorded_root(id, initial);
    let report = report.unwrap().result.unwrap();
    assert!(report.succeeded());
    assert_eq!(report.steps.len(), 5);
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (65, 3)
    );
    owner.finish(&mut world, id).unwrap();
    // Dynamic work and a subsequent managed call share the original owner.
    // An in-flight cancellation must still retain the returned inverse.
    use cordis_kernel::effect_work::EffectOutput;
    type Action = cordis_kernel::reversible_value::managed::Action<(), (), String, (), ()>;
    let group = owner.enqueue_native_effect(0, 9602, ()).unwrap();
    let item = owner.take_group().unwrap();
    let pending = item.start(|request| std::future::ready(owner.activate_effect(request)));
    assert!(!owner.execution().is_idle());
    owner
        .complete_request(ready(pending.complete()))
        .ok()
        .unwrap()
        .ok()
        .unwrap();
    let mut run = owner.take_effect(group).unwrap();
    let bindings = owner.execution().native_context().unwrap().committed_vec();
    let scope = owner
        .admit_scoped_effect(&mut run, Some(&bindings))
        .unwrap();
    let (returned, reply) = run
        .call_scoped((scope, ()), |(), (_, ())| {
            ((), EffectOutput::<Action, &str>::Pending)
        })
        .ok()
        .unwrap();
    run = returned;
    assert!(owner.land_effect(&mut run, reply).ok().unwrap().is_none());
    // A failed invocation retains its successful prefix. An empty invocation
    // between it and the next write must still preserve the call boundary.
    let partly_failed = Function::new(vec![
        Call {
            key: 1,
            effect: Effect::<ScaleAdd, String>::Scalar(ScaleAdd {
                scale: 1,
                offset: 0,
            }),
            branch: Branch {
                matched: Some(1),
                unmatched: Some(1),
            },
        },
        Call {
            key: 1,
            effect: Effect::Scalar(ScaleAdd {
                scale: u64::MAX,
                offset: 0,
            }),
            branch: end(),
        },
    ])
    .ok()
    .unwrap();
    let failed_report = owner
        .run_function(group, &partly_failed, &[port(1), port(1)])
        .unwrap();
    assert_eq!(failed_report.steps.len(), 1);
    let failure = failed_report.failure.unwrap();
    assert_eq!(failure.pc, 1);
    assert!(matches!(
        failure.error,
        Error::Scalar(cordis_kernel::reversible_value::effect::EffectError::Rejected)
    ));
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (65, 4)
    );
    let empty = Function::<ScaleAdd, String>::new(Vec::new()).ok().unwrap();
    let empty_report = owner.run_function(group, &empty, &[]).unwrap();
    assert!(empty_report.succeeded());
    assert!(empty_report.steps.is_empty());
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (65, 4)
    );
    let later = Function::new(vec![Call {
        key: 1,
        effect: Effect::<ScaleAdd, String>::Scalar(ScaleAdd {
            scale: 1,
            offset: 1,
        }),
        branch: end(),
    }])
    .ok()
    .unwrap();
    let later_report = owner.run_function(group, &later, &[port(1)]).unwrap();
    assert!(later_report.succeeded());
    assert_eq!(later_report.steps.len(), 1);
    assert_eq!(scalar.snapshot().value(), 66);
    let child_token = owner
        .enqueue_owned_child(group, (), ChildCleanup::Callback(Cleanup::Once(())))
        .ok()
        .unwrap();
    let child = owner.take_child().unwrap();
    let child_pending = child.start(|()| std::future::ready(()));
    assert!(!owner.execution().is_idle());
    assert!(owner
        .complete_request(ready(child_pending.complete()))
        .is_ok());
    owner.cancel(group);
    assert!(owner.execution().get(group).unwrap().is_pending());
    assert!(owner.run_function(group, &later, &[port(1)]).is_err());
    let scope = owner.admit_scoped_effect(&mut run, None).unwrap();
    let (returned, reply) = run
        .call_scoped((scope, ()), |(), (_, ())| {
            let applied = scalar
                .apply(cordis_kernel::reversible_value::Operation::Add(2), end())
                .unwrap();
            (
                (),
                EffectOutput::<Action, &str>::Ready(Ok(Some(ChildCleanup::Value(applied.inverse)))),
            )
        })
        .ok()
        .unwrap();
    run = returned;
    let landed = owner.land_effect(&mut run, reply).ok().unwrap().unwrap();
    assert!(!landed.continue_iteration);
    assert!(landed.token.unwrap() > child_token);
    // Retirement must return the actual checked-out runner until all its
    // managed inverses and the paired Child cleanup have completed.
    run = owner.retire_effect(run).err().unwrap();
    let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
        owner.dispatch(group).unwrap().unwrap()
    else {
        panic!("cancelled poll's actual inverse");
    };
    assert!(completion.report.result.is_ok());
    assert_eq!(scalar.snapshot().value(), 66);
    let Dispatch::Other(CleanupDispatch::Host { ticket, action }) =
        owner.dispatch(group).unwrap().unwrap()
    else {
        panic!("paired Child cleanup");
    };
    assert_eq!(ticket.token, child_token);
    assert!(matches!(action, ChildCleanup::Callback(Cleanup::Once(()))));
    assert!(owner
        .complete_result(
            group,
            ticket,
            Ok::<(), ()>(()),
            None,
            CleanupPolicy::RetainFailure
        )
        .is_ok());
    let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
        owner.dispatch(group).unwrap().unwrap()
    else {
        panic!("subsequent managed call's inverse");
    };
    assert!(completion.report.result.is_ok());
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (65, 4)
    );
    let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
        owner.dispatch(group).unwrap().unwrap()
    else {
        panic!("failed invocation's retained prefix");
    };
    assert!(completion.report.result.is_ok());
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (65, 3)
    );
    assert!(owner.retire_effect(run).is_ok());
    assert!(!owner.execution().contains(group));
    assert!(owner.enqueue_native_effect(0, 9602, ()).is_err());
    assert!(owner.run_function(group, &later, &[port(1)]).is_err());
    let stale = payload.capture().unwrap();
    let foreign = payload.apply(stale.value().clone()).ok().unwrap();
    assert_eq!(payload.capture().unwrap().value().as_str(), "beta");
    owner.withdraw(&mut world, id, false).unwrap();
    world
        .settle_managed_execution(id, owner.execution())
        .unwrap();
    let first_cleanup = world.begin_cleanup(id).unwrap();
    let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
        owner.dispatch(0).unwrap().unwrap()
    else {
        panic!("last scalar inverse");
    };
    assert!(completion.report.result.is_ok());
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (65, 2)
    );
    // Append while an earlier managed prefix has already been consumed. The
    // callback and its retries must not reset that prefix or consume its tokens.
    let callback_token = owner
        .register(0, ChildCleanup::Callback(Cleanup::Retryable(())))
        .ok()
        .unwrap();
    let Dispatch::Other(CleanupDispatch::Host { ticket, action }) =
        owner.dispatch(0).unwrap().unwrap()
    else {
        panic!("late callback");
    };
    assert_eq!(ticket.token, callback_token);
    assert!(matches!(
        action,
        ChildCleanup::Callback(Cleanup::Retryable(()))
    ));
    let failed = ready(await_completion(
        ticket,
        std::future::ready(Err::<(), &str>("temporary")),
    ));
    assert!(owner
        .complete_future(
            0,
            failed,
            Some(HostAction::Retryable(())),
            CleanupPolicy::RetainFailure
        )
        .is_ok());
    let retry_ticket = owner.retry(0).unwrap();
    assert!(retry_ticket.attempt > ticket.attempt);
    let Dispatch::Other(CleanupDispatch::Host {
        ticket: current, ..
    }) = owner.dispatch(0).unwrap().unwrap()
    else {
        panic!("retried late callback");
    };
    assert_eq!(current, retry_ticket);
    assert!(owner
        .complete_result(
            0,
            ticket,
            Ok::<(), &str>(()),
            None,
            CleanupPolicy::DrainConsumed
        )
        .is_err());
    let completed = ready(await_completion(
        current,
        std::future::ready(Ok::<(), &str>(())),
    ));
    assert!(owner
        .complete_future(0, completed, None, CleanupPolicy::RetainFailure)
        .is_ok());
    assert!(owner
        .complete_result(
            0,
            current,
            Ok::<(), &str>(()),
            None,
            CleanupPolicy::DrainConsumed
        )
        .is_err());
    let appended = scalar
        .apply(cordis_kernel::reversible_value::Operation::Add(1), end())
        .unwrap();
    let appended_token = owner
        .register(0, ChildCleanup::Value(appended.inverse))
        .ok()
        .unwrap();
    assert!(appended_token > callback_token);
    let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
        owner.dispatch(0).unwrap().unwrap()
    else {
        panic!("late managed inverse");
    };
    assert!(completion.report.result.is_ok());
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (65, 2)
    );
    let Dispatch::Payload(blocked) = owner.dispatch(0).unwrap().unwrap() else {
        panic!("typed inverse");
    };
    assert_eq!(blocked.report.result, Err(RestoreError::Interference));
    assert!(blocked.report.discarded.is_none());
    assert!(owner
        .complete_result(
            0,
            blocked.ticket,
            Ok::<(), &str>(()),
            None,
            CleanupPolicy::DrainConsumed
        )
        .is_err());
    assert!(owner.dispatch(0).unwrap().is_none());
    world.fail_managed_execution(id, owner.execution()).unwrap();
    assert!(owner.release(&mut world, id).0.is_err());
    assert!(foreign.inverse.restore().is_ok());
    assert!(!stale.check_result(true).accepted());
    let retry = owner.retry_native(&mut world, id).unwrap();
    assert_eq!(retry.generation, first_cleanup.generation);
    assert!(retry.action > first_cleanup.action);
    let Dispatch::Payload(restored) = owner.dispatch(0).unwrap().unwrap() else {
        panic!("retried typed inverse");
    };
    assert!(restored.report.result.is_ok());
    assert_eq!(restored.ticket.token, blocked.ticket.token);
    assert!(restored.ticket.attempt > blocked.ticket.attempt);
    assert_eq!(payload.capture().unwrap().value().as_str(), "alpha");
    let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
        owner.dispatch(0).unwrap().unwrap()
    else {
        panic!("aliased scalar inverse");
    };
    assert!(completion.report.result.is_ok());
    assert_eq!(scalar.snapshot().value(), 21);
    let Dispatch::Payload(restored) = owner.dispatch(0).unwrap().unwrap() else {
        panic!("original typed inverse");
    };
    assert!(restored.report.result.is_ok());
    assert_eq!(payload.capture().unwrap().value().as_str(), "old");
    let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
        owner.dispatch(0).unwrap().unwrap()
    else {
        panic!("original scalar inverse");
    };
    assert!(completion.report.result.is_ok());
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (10, 0)
    );
    assert!(owner.dispatch(0).unwrap().is_none());
    let (_, released) = owner.release(&mut world, id).0.unwrap();
    assert_eq!(released.imports.len(), 4);
    assert_eq!(
        owner.execution().phase(),
        cordis_kernel::execution::ExecutionPhase::Closed
    );
    assert!(owner.release(&mut world, id).0.is_err());
    payload.retire();
}

#[test]
fn observed_foreign_owner_restores_failed_prefix_before_native_retry() {
    use cordis_kernel::reversible_value::payload::restoration::RestoreError;
    let (mut world, scalar, payload) = fixture();
    let target_id = mount(&mut world, 102, vec![1, 2], vec![], body(2));
    let execution: Episode = world.begin_managed_execution(target_id, 9701).unwrap();
    let (mut target, root) = world.run_recorded_root(target_id, execution);
    assert!(root.unwrap().result.unwrap().failure.is_none());
    target.finish(&mut world, target_id).unwrap();

    let writer_id = mount(
        &mut world,
        103,
        vec![1, 2],
        vec![],
        Body::Managed(Function::new(vec![]).ok().unwrap()),
    );
    let execution: Episode = world.begin_managed_execution(writer_id, 9702).unwrap();
    let (mut writer, root) = world.run_recorded_root(writer_id, execution);
    assert!(root.unwrap().result.unwrap().steps.is_empty());
    writer.finish(&mut world, writer_id).unwrap();
    let continuation = Branch {
        matched: Some(1),
        unmatched: Some(1),
    };
    let foreign = Function::new(vec![
        Call {
            key: 1,
            effect: Effect::Scalar(ScaleAdd {
                scale: 1,
                offset: 1,
            }),
            branch: continuation,
        },
        Call {
            key: 2,
            effect: Effect::Replace(Arc::new("checked".to_owned())),
            branch: Branch {
                matched: Some(2),
                unmatched: Some(2),
            },
        },
        // The real kind mismatch preserves both earlier writes and inverses.
        Call {
            key: 2,
            effect: Effect::Scalar(ScaleAdd {
                scale: 1,
                offset: 1,
            }),
            branch: end(),
        },
    ])
    .ok()
    .unwrap();
    let report = writer
        .run_function_observed(0, &foreign, &[port(1), port(2), port(2)], &mut target)
        .unwrap();
    assert_eq!(report.steps.len(), 2);
    assert!(report.failure.is_some());
    assert_eq!(scalar.snapshot().value(), 22);
    assert_eq!(payload.capture().unwrap().value().as_str(), "checked");

    target.withdraw(&mut world, target_id, false).unwrap();
    world
        .settle_managed_execution(target_id, target.execution())
        .unwrap();
    let original_cleanup = world.begin_cleanup(target_id).unwrap();
    let Dispatch::Payload(blocked) = target.dispatch_observed(0, &mut writer).unwrap().unwrap()
    else {
        panic!("the older typed inverse must be blocked by the same-value foreign write");
    };
    assert_eq!(blocked.report.result, Err(RestoreError::Interference));
    assert!(target.dispatch_observed(0, &mut writer).unwrap().is_none());
    world
        .fail_managed_execution(target_id, target.execution())
        .unwrap();
    assert!(target.release(&mut world, target_id).0.is_err());

    writer.withdraw(&mut world, writer_id, false).unwrap();
    world
        .settle_managed_execution(writer_id, writer.execution())
        .unwrap();
    world.begin_cleanup(writer_id).unwrap();
    let Dispatch::Payload(restored) = writer.dispatch_observed(0, &mut target).unwrap().unwrap()
    else {
        panic!("foreign typed restoration");
    };
    assert!(restored.report.result.is_ok());
    let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
        writer.dispatch_observed(0, &mut target).unwrap().unwrap()
    else {
        panic!("foreign scalar restoration");
    };
    assert!(completion.report.result.is_ok());
    assert_eq!(scalar.snapshot().value(), 21);
    assert!(writer.release(&mut world, writer_id).0.is_ok());
    assert!(writer.dispatch_observed(0, &mut target).is_err());

    let retry = target.retry_native(&mut world, target_id).unwrap();
    assert!(retry.action > original_cleanup.action);
    let Dispatch::Payload(restored) = target.dispatch(0).unwrap().unwrap() else {
        panic!("retried original typed restoration");
    };
    assert!(restored.report.result.is_ok());
    assert_eq!(restored.ticket.token, blocked.ticket.token);
    assert!(restored.ticket.attempt > blocked.ticket.attempt);
    let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
        target.dispatch(0).unwrap().unwrap()
    else {
        panic!("original scalar restoration");
    };
    assert!(completion.report.result.is_ok());
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (10, 0)
    );
    assert_eq!(payload.capture().unwrap().value().as_str(), "old");
    assert!(target.release(&mut world, target_id).0.is_ok());
}

#[test]
fn typed_restore_cannot_repeat_or_revive_a_retired_allocation() {
    use cordis_kernel::reversible_value::payload::restoration::RestoreError;
    let payload = SharedPayload::new(Arc::new("start".to_owned()));
    let first = payload.apply(Arc::new("first".to_owned())).ok().unwrap();
    assert!(first.inverse.restore().is_ok());
    assert_eq!(
        first.inverse.restore().err().unwrap().error(),
        RestoreError::Interference
    );
    assert_eq!(payload.capture().unwrap().value().as_str(), "start");
    let second = payload.apply(Arc::new("second".to_owned())).ok().unwrap();
    payload.retire();
    assert_eq!(
        second.inverse.restore().err().unwrap().error(),
        RestoreError::Closed
    );
    assert!(payload.capture().is_none());
}

#[test]
fn recorded_raw_sources_cover_interference_restore_and_native_retry() {
    use cordis_kernel::reversible_value::{payload::restoration::RestoreError, Operation};
    let (mut world, scalar, payload) = fixture();
    let id = mount(&mut world, 104, vec![1, 2], vec![], body(2));
    let execution: Episode = world.begin_managed_execution(id, 9801).unwrap();
    let (mut owner, report) = world.run_recorded_root(id, execution);
    assert!(report.unwrap().result.unwrap().failure.is_none());
    owner.finish(&mut world, id).unwrap();

    let first_scalar = owner
        .apply_scalar_observed(&scalar, Operation::Add(1), end())
        .ok()
        .unwrap()
        .inverse;
    let second_scalar = owner
        .apply_scalar_observed(&scalar, Operation::Xor(7), end())
        .ok()
        .unwrap()
        .inverse;
    // Equal contents still create a distinct typed semantic head and obligation.
    let first_payload = owner
        .apply_payload_observed(&payload, Arc::new("checked".to_owned()))
        .ok()
        .unwrap()
        .inverse;
    let second_payload = owner
        .apply_payload_observed(&payload, Arc::new("temporary".to_owned()))
        .ok()
        .unwrap()
        .inverse;
    assert_eq!(scalar.snapshot().value(), 22 ^ 7);
    assert_eq!(payload.capture().unwrap().value().as_str(), "temporary");

    owner.withdraw(&mut world, id, false).unwrap();
    world
        .settle_managed_execution(id, owner.execution())
        .unwrap();
    let cleanup = world.begin_cleanup(id).unwrap();
    let Dispatch::Payload(blocked) = owner.dispatch(0).unwrap().unwrap() else {
        panic!("typed cleanup");
    };
    assert_eq!(blocked.report.result, Err(RestoreError::Interference));
    world.fail_managed_execution(id, owner.execution()).unwrap();
    assert!(owner.release(&mut world, id).0.is_err());

    // Raw failure remains observable and returns the exact scalar inverse.
    let first_scalar = owner.restore_scalar_observed(first_scalar).0.err().unwrap();
    assert!(owner.restore_scalar_observed(second_scalar).0.is_ok());
    assert!(owner.restore_scalar_observed(first_scalar).0.is_ok());
    assert_eq!(scalar.snapshot().value(), 21);
    assert_eq!(
        owner
            .restore_payload_observed(&first_payload)
            .0
            .err()
            .unwrap()
            .error(),
        RestoreError::Interference
    );
    assert!(owner.restore_payload_observed(&second_payload).0.is_ok());
    assert!(owner.restore_payload_observed(&first_payload).0.is_ok());
    assert_eq!(
        owner
            .restore_payload_observed(&first_payload)
            .0
            .err()
            .unwrap()
            .error(),
        RestoreError::Interference
    );
    assert_eq!(payload.capture().unwrap().value().as_str(), "checked");

    let retry = owner.retry_native(&mut world, id).unwrap();
    assert!(retry.action > cleanup.action);
    let Dispatch::Payload(restored) = owner.dispatch(0).unwrap().unwrap() else {
        panic!("typed retry");
    };
    assert!(restored.report.result.is_ok());
    assert!(restored.ticket.attempt > blocked.ticket.attempt);
    let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
        owner.dispatch(0).unwrap().unwrap()
    else {
        panic!("scalar cleanup");
    };
    assert!(completion.report.result.is_ok());
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (10, 0)
    );
    assert_eq!(payload.capture().unwrap().value().as_str(), "old");
    assert!(owner.release(&mut world, id).0.is_ok());
}

#[test]
fn recorded_raw_rejections_and_foreign_journals_keep_original_results() {
    use cordis_kernel::reversible_value::{
        payload::restoration::RestoreError, Operation, ValueError,
    };
    use cordis_kernel::versioned_value::ReplaceError;
    let (mut world, _, _) = fixture();
    let id = mount(
        &mut world,
        105,
        vec![],
        vec![],
        Body::Managed(Function::new(vec![]).ok().unwrap()),
    );
    let execution: Episode = world.begin_managed_execution(id, 9802).unwrap();
    let (mut owner, report) = world.run_recorded_root(id, execution);
    assert!(report.unwrap().result.unwrap().failure.is_none());
    let scalar = ReversibleValue::new(u64::MAX);
    assert_eq!(
        owner
            .apply_scalar_observed(&scalar, Operation::Add(1), end())
            .err(),
        Some(ValueError::Overflow)
    );
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (u64::MAX, 0)
    );
    let inverse = owner
        .apply_scalar_observed(&scalar, Operation::Xor(3), end())
        .ok()
        .unwrap()
        .inverse;
    assert!(owner.restore_scalar_observed(inverse).0.is_ok());
    assert_eq!(scalar.snapshot().value(), u64::MAX);

    let payload = SharedPayload::new(Arc::new("original".to_owned()));
    let inverse = owner
        .apply_payload_observed(&payload, Arc::new("changed".to_owned()))
        .ok()
        .unwrap()
        .inverse;
    payload.retire();
    assert_eq!(
        owner
            .restore_payload_observed(&inverse)
            .0
            .err()
            .unwrap()
            .error(),
        RestoreError::Closed
    );
    let rejected = owner
        .apply_payload_observed(&payload, Arc::new("rejected".to_owned()))
        .err()
        .unwrap();
    assert_eq!(rejected.error, ReplaceError::Closed);
    assert_eq!(rejected.value.as_str(), "rejected");
}

#[test]
fn producer_snapshots_cover_raw_calls_repeated_states_and_retirement() {
    use cordis_kernel::reversible_value::{payload::restoration::RestoreError, Operation};
    let (mut world, scalar, payload) = fixture();
    let id = mount(
        &mut world,
        106,
        vec![],
        vec![],
        Body::Managed(Function::new(vec![]).ok().unwrap()),
    );
    let execution: Episode = world.begin_managed_execution(id, 9803).unwrap();
    let (mut owner, report) = world.run_recorded_root(id, execution);
    assert!(report.unwrap().result.unwrap().failure.is_none());

    // These writes deliberately bypass the recorded facade. Collection reads
    // the real producer, whose complete history also includes the blocked call.
    let first = scalar.apply(Operation::Add(5), end()).ok().unwrap().inverse;
    let second = scalar.apply(Operation::Xor(7), end()).ok().unwrap().inverse;
    let first = first.restore().err().unwrap();
    let snapshot = owner.scalar_source_snapshot(&scalar);
    assert_eq!((snapshot.value(), snapshot.depth()), (15 ^ 7, 2));
    assert!(second.restore().is_ok());
    assert!(first.restore().is_ok());
    // Identical before/after scalar states still have different origin leases.
    for _ in 0..2 {
        let inverse = scalar.apply(Operation::Add(5), end()).ok().unwrap().inverse;
        assert!(inverse.restore().is_ok());
    }
    let snapshot = owner.scalar_source_snapshot(&scalar);
    assert_eq!((snapshot.value(), snapshot.depth()), (10, 0));

    let same = Arc::new("same".to_owned());
    let first = payload.apply(same.clone()).ok().unwrap().inverse;
    assert!(first.restore().is_ok());
    let second = payload.apply(same).ok().unwrap().inverse;
    assert_eq!(
        first.restore().err().unwrap().error(),
        RestoreError::Interference
    );
    assert!(second.restore().is_ok());
    assert_eq!(
        first.restore().err().unwrap().error(),
        RestoreError::Interference
    );
    payload
        .replace(Arc::new("replacement".to_owned()))
        .ok()
        .unwrap();
    let capture = payload.capture().unwrap();
    let references = Arc::strong_count(capture.value());
    let _source = owner.payload_source_snapshot(&payload);
    assert_eq!(Arc::strong_count(capture.value()), references);
    let retired = payload.retire().unwrap();
    assert_eq!(retired.into_value().as_str(), "replacement");
    assert!(payload.capture().is_none());
    // Terminal source collection remains callable and does not revive payloads.
    let _terminal = owner.payload_source_snapshot(&payload);
    let _again = owner.payload_source_snapshot(&payload);
    assert!(payload.capture().is_none());
    assert_eq!(
        second.restore().err().unwrap().error(),
        RestoreError::Closed
    );
}

#[test]
fn invocation_census_collects_raw_aliases_without_retaining_payloads() {
    use cordis_kernel::reversible_value::Operation;
    let (mut world, scalar, payload) = fixture();
    let id = mount(&mut world, 107, vec![1, 2], vec![], body(2));
    let execution: Episode = world.begin_managed_execution(id, 9804).unwrap();
    let (mut owner, report) = world.run_recorded_root(id, execution);
    let report = report.unwrap();
    assert!(report.result.as_ref().unwrap().failure.is_none());
    owner.finish(&mut world, id).unwrap();
    let journal = world.execution_journal();
    let scalar_scope = [scalar.clone(), scalar.clone()];
    let payload_scope = [payload.clone(), payload.clone()];

    // The facade did not observe these calls. Failed scalar cleanup retains the
    // same inverse while a newer raw operation is outstanding.
    let first = scalar.apply(Operation::Add(5), end()).ok().unwrap().inverse;
    let second = scalar.apply(Operation::Xor(3), end()).ok().unwrap().inverse;
    let first = first.restore().err().unwrap();
    let foreign = payload
        .apply(Arc::new("foreign".to_owned()))
        .ok()
        .unwrap()
        .inverse;
    let captured = payload.capture().unwrap();
    let references = Arc::strong_count(captured.value());
    let census =
        owner.capture_invocation_census(&journal, &report, 0, 0, &scalar_scope, &payload_scope);
    assert_eq!(std::mem::size_of_val(&census), 0);
    assert_eq!(Arc::strong_count(captured.value()), references);
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (26 ^ 3, 3)
    );
    assert_eq!(payload.capture().unwrap().value().as_str(), "foreign");

    assert!(second.restore().is_ok());
    assert!(first.restore().is_ok());
    owner.withdraw(&mut world, id, false).unwrap();
    world
        .settle_managed_execution(id, owner.execution())
        .unwrap();
    world.begin_cleanup(id).unwrap();
    let Dispatch::Payload(blocked) = owner.dispatch(0).unwrap().unwrap() else {
        panic!("typed cleanup")
    };
    assert!(blocked.report.result.is_err());
    world.fail_managed_execution(id, owner.execution()).unwrap();
    assert!(foreign.restore().is_ok());
    owner.capture_invocation_census(&journal, &report, 0, 0, &scalar_scope, &payload_scope);
    owner.retry_native(&mut world, id).unwrap();
    let Dispatch::Payload(done) = owner.dispatch(0).unwrap().unwrap() else {
        panic!("typed retry")
    };
    assert!(done.report.result.is_ok());
    let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
        owner.dispatch(0).unwrap().unwrap()
    else {
        panic!("scalar cleanup")
    };
    assert!(completion.report.result.is_ok());
    owner.capture_invocation_census(&journal, &report, 0, 0, &scalar_scope, &payload_scope);
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (10, 0)
    );
    assert_eq!(payload.capture().unwrap().value().as_str(), "old");
    payload.retire();
}

#[test]
fn invocation_census_reads_destructive_and_retired_producers() {
    let (mut world, scalar, payload) = fixture();
    let id = mount(&mut world, 108, vec![1, 2], vec![], body(2));
    let execution: Episode = world.begin_managed_execution(id, 9805).unwrap();
    let (mut owner, report) = world.run_recorded_root(id, execution);
    let report = report.unwrap();
    owner.finish(&mut world, id).unwrap();
    let journal = world.execution_journal();
    let scalar_scope = [scalar];
    let payload_scope = [payload.clone()];
    payload
        .replace(Arc::new("destructive".to_owned()))
        .ok()
        .unwrap();
    owner.capture_invocation_census(&journal, &report, 0, 0, &scalar_scope, &payload_scope);
    assert_eq!(payload.capture().unwrap().value().as_str(), "destructive");
    assert_eq!(
        payload.retire().unwrap().into_value().as_str(),
        "destructive"
    );
    for _ in 0..2 {
        owner.capture_invocation_census(&journal, &report, 0, 0, &scalar_scope, &payload_scope);
        assert!(payload.capture().is_none());
    }
    // Diagnostic variants are erased. Verus checks their exact source-frame
    // contracts; this runtime regression checks safe collection after retirement.
}

#[test]
fn final_recovery_capture_spans_foreign_retry_and_a_later_child_unload() {
    use cordis_kernel::cleanup_queue::completion::CleanupPolicy;
    use cordis_kernel::lifecycle_state::registration::shared_child::{ChildCleanup, ChildDispatch};
    use cordis_kernel::reversible_value::{payload::restoration::RestoreError, Operation};
    use cordis_kernel::Phase;
    type Parent = Owner<ChildDispatch<(), ()>, (), (), (), String, (), ()>;

    let (mut world, scalar, payload) = fixture_with_recording(true);
    let parent = mount(&mut world, 110, vec![1, 2], vec![], body(2));
    let execution: Parent = world.begin_managed_execution(parent, 9901).unwrap();
    let (mut owner, root) = world.run_recorded_root(parent, execution);
    let root = root.unwrap();
    assert_eq!(root.result.as_ref().unwrap().steps.len(), 2);
    owner.finish(&mut world, parent).unwrap();

    let (_handle, child_token) = owner.enqueue_native_child(0, ()).ok().unwrap();
    let reply = owner.take_child().unwrap().run(|request| {
        let ChildDispatch::Native(request) = request else {
            panic!("native child request");
        };
        let (_, child) = request.into_parts();
        world
            .register_shared_child(
                &child,
                &BTreeMap::new(),
                port(111),
                PluginDefinition::new(
                    vec![],
                    vec![3],
                    Body::Managed(Function::new(vec![]).ok().unwrap()),
                ),
                (),
            )
            .result
            .ok()
            .unwrap()
    });
    let child = owner.complete_request(reply).ok().unwrap();
    let mut execution: Episode = world.begin_managed_execution(child, 9902).unwrap();
    execution
        .provide(
            port(3),
            Arc::new(Slot::new_reversible(Arc::new(scalar.clone()), ())),
        )
        .ok()
        .unwrap();
    let (mut child_owner, child_root) = world.run_recorded_root(child, execution);
    assert!(child_root.unwrap().result.unwrap().steps.is_empty());
    child_owner.finish(&mut world, child).unwrap();

    // This real foreign invocation also consumes the Child's publication.
    let foreign = mount(&mut world, 112, vec![1, 2, 3], vec![], body(1));
    let execution: Episode = world.begin_managed_execution(foreign, 9903).unwrap();
    let (mut writer, foreign_root) = world.run_recorded_root(foreign, execution);
    let foreign_root = foreign_root.unwrap();
    assert_eq!(foreign_root.result.as_ref().unwrap().steps.len(), 2);
    writer.finish(&mut world, foreign).unwrap();
    assert_eq!(scalar.snapshot().value(), 22);

    owner.withdraw(&mut world, parent, false).unwrap();
    world
        .settle_managed_execution(parent, owner.execution())
        .unwrap();
    let initial_cleanup = world.begin_cleanup(parent).unwrap();
    let Dispatch::Other(CleanupDispatch::Host { ticket, action }) =
        owner.dispatch(0).unwrap().unwrap()
    else {
        panic!("Child retirement inverse precedes the value inverses");
    };
    assert_eq!(ticket.token, child_token);
    let ChildCleanup::Native(inverse) = action else {
        panic!("paired Child inverse");
    };
    assert_eq!(
        world
            .retire_shared_child(&inverse)
            .result
            .unwrap()
            .unwrap()
            .id(),
        child
    );
    owner
        .complete_result(
            0,
            ticket,
            Ok::<(), ()>(()),
            None,
            CleanupPolicy::RetainFailure,
        )
        .ok()
        .unwrap();
    assert!(world.kernel().retired(child));
    assert!(world.begin_cleanup(child).is_err());

    let Dispatch::Payload(blocked) = owner.dispatch(0).unwrap().unwrap() else {
        panic!("typed interference");
    };
    assert_eq!(blocked.report.result, Err(RestoreError::Interference));
    world
        .fail_managed_execution(parent, owner.execution())
        .unwrap();
    assert!(owner.release(&mut world, parent).0.is_err());

    writer.withdraw(&mut world, foreign, false).unwrap();
    world
        .settle_managed_execution(foreign, writer.execution())
        .unwrap();
    world.begin_cleanup(foreign).unwrap();
    let Dispatch::Payload(restored) = writer.dispatch(0).unwrap().unwrap() else {
        panic!("foreign typed inverse");
    };
    assert!(restored.report.result.is_ok());
    let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
        writer.dispatch(0).unwrap().unwrap()
    else {
        panic!("foreign scalar inverse");
    };
    assert!(completion.report.result.is_ok());
    assert!(writer.release(&mut world, foreign).0.is_ok());

    let retry = owner.retry_native(&mut world, parent).unwrap();
    assert!(retry.action > initial_cleanup.action);
    let Dispatch::Payload(restored) = owner.dispatch(0).unwrap().unwrap() else {
        panic!("parent typed retry");
    };
    assert!(restored.report.result.is_ok());
    assert_eq!(restored.ticket.token, blocked.ticket.token);
    assert!(restored.ticket.attempt > blocked.ticket.attempt);
    let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
        owner.dispatch(0).unwrap().unwrap()
    else {
        panic!("parent scalar inverse");
    };
    assert!(completion.report.result.is_ok());
    let released = owner.release(&mut world, parent);
    assert!(released.0.is_ok());
    assert_eq!(world.kernel().phase(parent), Some(Phase::Inactive));
    assert_eq!(world.kernel().phase(child), Some(Phase::Active));

    let scalars = [scalar.clone(), scalar.clone()];
    let payloads = [payload.clone(), payload.clone()];
    // This cut still has an unresolved original Child. The erased certificate
    // must diagnose it; a parent's Unload is never treated as Child completion.
    let first = owner.capture_release_census(&world, &root, 0, 0, &released, &scalars, &payloads);
    let source = first.control.as_ref().unwrap();
    let commands = source.commands().len();
    assert!(commands > 0);
    let replay = source
        .replay(
            &first.cut,
            &vec![true; commands],
            vstd::prelude::Ghost::assume_new(),
        )
        .unwrap();
    assert_eq!(
        replay.execution.kernel().phase(parent),
        Some(Phase::Inactive)
    );
    assert_eq!(replay.execution.kernel().phase(child), Some(Phase::Active));
    assert_eq!(std::mem::size_of_val(&first.evidence), 0);
    assert_eq!(std::mem::size_of_val(&first.observations), 0);
    assert_eq!(std::mem::size_of_val(&first.observation_issue), 0);
    assert_eq!(scalar.snapshot().value(), 10);
    assert_eq!(payload.capture().unwrap().value().as_str(), "old");

    child_owner.withdraw(&mut world, child, false).unwrap();
    world
        .settle_managed_execution(child, child_owner.execution())
        .unwrap();
    world.begin_cleanup(child).unwrap();
    assert!(child_owner.dispatch(0).unwrap().is_none());
    assert!(child_owner.release(&mut world, child).0.is_ok());
    assert_eq!(world.kernel().phase(child), Some(Phase::Inactive));
    assert!(world.native_value(port(3)).is_none());
    let live = payload.capture().unwrap();
    let references = Arc::strong_count(live.value());
    let complete =
        owner.capture_release_census(&world, &root, 0, 0, &released, &scalars, &payloads);
    assert_eq!(Arc::strong_count(live.value()), references);
    let source = complete.control.as_ref().unwrap();
    assert!(source.commands().len() > commands);
    let replay = source
        .replay(
            &complete.cut,
            &vec![true; source.commands().len()],
            vstd::prelude::Ghost::assume_new(),
        )
        .unwrap();
    assert_eq!(
        replay.execution.kernel().phase(child),
        Some(Phase::Inactive)
    );
    assert_eq!(first.control.as_ref().unwrap().commands().len(), commands);
    world.remove(child).unwrap();
    let removed = owner.capture_release_census(&world, &root, 0, 0, &released, &scalars, &payloads);
    assert!(!world.kernel().contains(child));
    let count = removed.control.as_ref().unwrap().commands().len();
    // The empty selected region retains all controls/effects. Exercise the
    // composed API without substituting another source cut or command list.
    let combined = removed
        .with_deletion(vstd::prelude::Ghost::assume_new())
        .with_effects(vstd::prelude::Ghost::assume_new())
        .replay_control(&vec![true; count])
        .unwrap();
    assert_eq!(
        combined.replay.execution.kernel().ids(),
        world.kernel().ids()
    );

    // A new raw write after Unload belongs to the later common cut as well.
    // Collection is read-only and never silently rolls this foreign write back.
    let later = scalar.apply(Operation::Add(7), end()).unwrap().inverse;
    let pending = owner.capture_release_census(&world, &root, 0, 0, &released, &scalars, &payloads);
    assert_eq!(scalar.snapshot().value(), 17);
    assert!(later.restore().is_ok());
    let retried = owner.capture_release_census(&world, &root, 0, 0, &released, &scalars, &payloads);
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (10, 0)
    );
    payload
        .replace(Arc::new("destructive".to_owned()))
        .ok()
        .unwrap();
    let destructive =
        owner.capture_release_census(&world, &root, 0, 0, &released, &scalars, &payloads);
    assert_eq!(payload.capture().unwrap().value().as_str(), "destructive");
    // Runtime checks exercise host behavior; the classification and common-cut
    // implications are checked by Verus, not by inspecting erased evidence here.
    drop((first, complete, combined, pending, retried, destructive));
}
