use cordis_kernel::cleanup_queue::completion::CleanupDispatch;
use cordis_kernel::execution::Execution;
use cordis_kernel::lifecycle_state::native::runtime::NativeRuntime;
use cordis_kernel::lifecycle_state::registration::shared_child::ChildCleanup;
use cordis_kernel::lifecycle_state::registration::PluginDefinition;
use cordis_kernel::reversible_value::function::{AdmissionError, Body, Function};
use cordis_kernel::reversible_value::program::{Instruction, Program};
use cordis_kernel::reversible_value::slot::ServiceSlot;
use cordis_kernel::reversible_value::{Branch, Operation, ReversibleValue};
use cordis_kernel::setup_work::RootStatus;
use cordis_kernel::Port;
use std::collections::BTreeMap;
use std::sync::Arc;

type Callback = fn(()) -> Result<(), ()>;
type Slot = ServiceSlot<(), ()>;
type World = NativeRuntime<Body<Callback>, (), Slot>;
type Episode = Execution<Slot, (), (), ChildCleanup<(), ()>>;
const KEY: u64 = 1;
fn port(key: u64) -> Port {
    Port { key, realm: 0 }
}
fn callback(_: ()) -> Result<(), ()> {
    Ok(())
}
fn body(key: u64, amount: u64) -> Body<Callback> {
    Body::Value(Function::new(
        key,
        Program::new(vec![Instruction {
            operation: Operation::Add(amount),
            branch: Branch {
                matched: None,
                unmatched: None,
            },
        }])
        .unwrap(),
    ))
}
fn mount(
    world: &mut World,
    anchor: u64,
    dependencies: Vec<u64>,
    provisions: Vec<u64>,
    body: Body<Callback>,
) -> usize {
    world
        .register(
            None,
            &BTreeMap::new(),
            port(anchor),
            PluginDefinition::new(dependencies, provisions, body),
            (),
        )
        .ok()
        .unwrap()
}
fn world() -> (World, ReversibleValue) {
    let mut world = World::new(9200);
    let value = ReversibleValue::new_in(&world.execution_journal(), 10);
    let provider = mount(
        &mut world,
        100,
        vec![],
        vec![KEY],
        Body::Callback(callback as Callback),
    );
    let mut episode: Episode = world.begin_managed_execution(provider, 9201).unwrap();
    let invocation = world
        .admit_managed_root(provider, &mut episode, ())
        .unwrap();
    let receipt = world.call_opaque(provider, invocation).ok().unwrap();
    episode.complete_root(receipt).ok().unwrap().unwrap();
    episode
        .provide(
            port(KEY),
            Arc::new(Slot::new_reversible(Arc::new(value.clone()), ())),
        )
        .ok()
        .unwrap();
    world
        .finish_managed_execution(provider, &mut episode)
        .unwrap();
    (world, value)
}

#[test]
fn registered_body_uses_latest_revision_and_rejects_other_or_repeated_owners() {
    let (mut world, value) = world();
    let first = mount(&mut world, 101, vec![KEY], vec![], body(KEY, 5));
    let second = mount(&mut world, 102, vec![KEY], vec![], body(KEY, 1));
    let mut a: Episode = world.begin_managed_execution(first, 9202).unwrap();
    let mut b: Episode = world.begin_managed_execution(second, 9203).unwrap();
    assert!(matches!(
        world.run_value_root(first, &mut b),
        Err(AdmissionError::WrongOwner)
    ));
    assert_eq!(b.work().root(), RootStatus::Unissued);
    assert_eq!(value.snapshot().value(), 10);
    world.replace(first, body(KEY, 7)).ok().unwrap();
    let report = world.run_value_root(first, &mut a).unwrap();
    assert_eq!(
        (report.origin.id, report.revision, report.port),
        (first, 1, port(KEY))
    );
    assert_eq!(report.result.unwrap().program.outcomes[0].after, 17);
    assert_eq!(a.work().root(), RootStatus::Settled);
    assert!(!a.work().root_failed_now());
    assert!(matches!(
        world.run_value_root(first, &mut a),
        Err(AdmissionError::NotAdmitted)
    ));
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (17, 1)
    );
    a.withdraw();
    let CleanupDispatch::Value { completion, .. } = a.dispatch_cleanup(0).unwrap().unwrap() else {
        panic!("real stored inverse")
    };
    assert!(completion.report.result.is_ok());
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (10, 0)
    );
}

#[test]
fn retired_root_or_missing_registered_dependency_cannot_run() {
    let (mut world, value) = world();
    let missing = mount(&mut world, 101, vec![KEY], vec![], body(2, 7));
    let mut a: Episode = world.begin_managed_execution(missing, 9212).unwrap();
    assert!(matches!(
        world.run_value_root(missing, &mut a),
        Err(AdmissionError::MissingDependency)
    ));
    assert_eq!(a.work().root(), RootStatus::Unissued);
    let retired = mount(&mut world, 102, vec![KEY], vec![], body(KEY, 7));
    let mut b: Episode = world.begin_managed_execution(retired, 9213).unwrap();
    world.retire(retired).unwrap();
    assert!(matches!(
        world.run_value_root(retired, &mut b),
        Err(AdmissionError::NotAdmitted)
    ));
    assert_eq!(b.work().root(), RootStatus::Unissued);
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (10, 0)
    );
}

#[test]
fn opaque_dispatch_rejects_stale_revision_and_finite_bodies() {
    let (mut world, value) = world();
    let id = mount(
        &mut world,
        101,
        vec![KEY],
        vec![],
        Body::Callback(callback as Callback),
    );
    let mut a: Episode = world.begin_managed_execution(id, 9222).unwrap();
    let invocation = world.admit_managed_root(id, &mut a, ()).unwrap();
    world.replace(id, body(KEY, 7)).ok().unwrap();
    assert!(world.call_opaque(id, invocation).is_err());
    assert_eq!(a.work().root(), RootStatus::Queued);
    let finite = mount(&mut world, 102, vec![KEY], vec![], body(KEY, 3));
    let mut b: Episode = world.begin_managed_execution(finite, 9223).unwrap();
    let invocation = world.admit_managed_root(finite, &mut b, ()).unwrap();
    assert!(world.call_opaque(finite, invocation).is_err());
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (10, 0)
    );
}

#[test]
fn joint_episode_observes_dynamic_work_failed_inverse_and_fresh_retry() {
    use cordis_kernel::cleanup_queue::completion::CleanupPolicy;
    use cordis_kernel::effect_work::EffectOutput;

    assert!(Episode::new(9300).observe_execution().is_none());
    let (mut world, value) = world();
    let first = mount(&mut world, 111, vec![KEY], vec![], body(KEY, 5));
    let second = mount(&mut world, 112, vec![KEY], vec![], body(KEY, 7));
    let mut a: Episode = world.begin_managed_execution(first, 9301).unwrap();
    let mut b: Episode = world.begin_managed_execution(second, 9302).unwrap();
    let initial = a.observe_execution().unwrap();
    let report = world.run_value_root(first, &mut a).unwrap().result.unwrap();
    let completed = a.observe_execution_after(report.program.snapshot.joint_execution());
    assert!(a.work().observe_execution().is_some());
    assert!(a.groups().get(0).unwrap().observe_execution().is_some());
    assert_eq!(value.snapshot().value(), 15);

    // A dynamically allocated iterator must join the same domain. Observing
    // while it is checked out also exercises the read-guard release path.
    let group = a.enqueue_effect(0, 9310, vec![], ()).unwrap();
    let item = a.take_group().unwrap();
    let receipt = item.run(|request| a.activate_effect(request));
    assert!(a.complete_request(receipt).ok().unwrap().is_ok());
    let mut runner = a.take_effect(group).unwrap();
    assert!(a.admit_effect(&mut runner, Some(&[])));
    let pending = a.observe_execution_after(&completed);
    assert!(a.groups().get(group).unwrap().is_pending());
    let (mut runner, reply) = runner
        .call((), |payload, ()| {
            (
                payload,
                EffectOutput::<ChildCleanup<(), ()>, ()>::Ready(Ok(None)),
            )
        })
        .ok()
        .unwrap();
    assert!(a.land_effect(&mut runner, reply).ok().unwrap().is_some());
    assert!(a.retire_effect(runner).is_ok());
    assert!(a.groups().get(group).is_none());
    let _retired = a.observe_execution_after(&pending);

    world.run_value_root(second, &mut b).unwrap();
    assert_eq!(value.snapshot().value(), 22);
    a.withdraw();
    let CleanupDispatch::Value {
        ticket: old,
        completion,
    } = a.dispatch_cleanup(0).unwrap().unwrap()
    else {
        panic!("the registered finite body owns a real inverse")
    };
    assert!(completion.report.result.is_err());
    assert!(a.groups().get(0).unwrap().has_failed());
    let failed = a.observe_execution_after(&initial);
    b.withdraw();
    let CleanupDispatch::Value { completion, .. } = b.dispatch_cleanup(0).unwrap().unwrap() else {
        panic!("second registered inverse")
    };
    assert!(completion.report.result.is_ok());
    assert_eq!(value.snapshot().value(), 15);

    let fresh = a.retry(0).unwrap();
    assert_eq!(fresh.token, old.token);
    assert!(fresh.attempt > old.attempt);
    let (ticket, action) = a.pop(0).unwrap().unwrap();
    assert_eq!(ticket, fresh);
    assert!(a
        .complete_result::<()>(0, old, Ok(()), None, CleanupPolicy::RetainFailure)
        .is_err());
    assert!(a.groups().get(0).unwrap().is_issued());
    let ChildCleanup::Value(inverse) = action else {
        panic!("retained original inverse")
    };
    assert!(inverse.restore().is_ok());
    assert!(a
        .complete_result::<()>(0, fresh, Ok(()), None, CleanupPolicy::RetainFailure)
        .is_ok());
    assert!(a
        .complete_result::<()>(0, fresh, Ok(()), None, CleanupPolicy::RetainFailure)
        .is_err());
    let _restored = a.observe_execution_after(&failed);
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (10, 0)
    );
    assert!(!a.groups().get(0).unwrap().has_failed());
    assert!(!a.groups().get(0).unwrap().is_issued());
    assert!(a.groups().get(0).unwrap().is_empty());
}

#[test]
fn native_episode_mixes_registered_write_paths_and_restores_a_failed_prefix() {
    use cordis_kernel::reversible_value::effect::ScaleAdd;
    use cordis_kernel::reversible_value::ValueError;

    let end = Branch {
        matched: None,
        unmatched: None,
    };
    let (mut world, value) = world();
    let plugin = mount(&mut world, 121, vec![KEY], vec![], body(KEY, 5));
    let mut owner: Episode = world.begin_managed_execution(plugin, 9401).unwrap();
    let root = world
        .run_value_root(plugin, &mut owner)
        .unwrap()
        .result
        .unwrap();
    let _after_root = owner.observe_execution_after(root.program.snapshot.joint_execution());
    assert_eq!(
        owner
            .apply_value(0, &value, Operation::Xor(3), end)
            .unwrap()
            .token,
        1
    );
    let prepared = value.prepare_effect(ScaleAdd {
        scale: 2,
        offset: 1,
    });
    assert_eq!(
        owner
            .apply_prepared_effect(0, prepared, end)
            .unwrap()
            .outcome
            .after,
        25
    );
    let program = Program::new(vec![Instruction {
        operation: Operation::Add(7),
        branch: end,
    }])
    .unwrap();
    let mut cursor = owner.begin_value_program(0, &value, program).ok().unwrap();
    assert_eq!(
        owner
            .advance_value_program(0, &mut cursor)
            .unwrap()
            .unwrap()
            .after,
        32
    );
    assert!(owner
        .advance_value_program(0, &mut cursor)
        .unwrap()
        .is_none());

    // Independent Journals remain supported. Their cleanup must not be
    // represented as an edge to an unrelated same-numbered native event.
    let foreign = ReversibleValue::new(40);
    assert_eq!(
        owner
            .apply_value(0, &foreign, Operation::Replace(99), end)
            .unwrap()
            .token,
        4
    );
    let prefix = Program::new(vec![
        Instruction {
            operation: Operation::Add(1),
            branch: Branch {
                matched: Some(1),
                unmatched: Some(1),
            },
        },
        Instruction {
            operation: Operation::Add(u64::MAX),
            branch: end,
        },
    ])
    .unwrap();
    let report = owner.run_value_program(0, &value, &prefix).unwrap();
    assert_eq!(report.outcomes.len(), 1);
    assert_eq!(report.error(), Some(ValueError::Overflow));
    assert_eq!(value.snapshot().value(), 33);
    let before_cleanup = owner.observe_execution_after(report.snapshot.joint_execution());
    owner.withdraw();
    let mut restored = Vec::new();
    while let Some(dispatch) = owner.dispatch_cleanup(0).unwrap() {
        let CleanupDispatch::Value { completion, .. } = dispatch else {
            panic!("value inverse")
        };
        assert!(completion.report.result.is_ok());
        restored.push(completion.restored.unwrap().value());
    }
    assert_eq!(restored, [32, 40, 25, 12, 15, 10]);
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (10, 0)
    );
    assert_eq!(
        (foreign.snapshot().value(), foreign.snapshot().depth()),
        (40, 0)
    );
    let _cleaned = owner.observe_execution_after(&before_cleanup);
}

#[test]
fn service_checkpoint_composes_local_aliases_foreign_targets_slots_and_opaque_payloads() {
    let mut world = World::new(9700);
    let value = Arc::new(ReversibleValue::new_in(&world.execution_journal(), 10));
    let foreign = Arc::new(ReversibleValue::new(50));
    let changed = Arc::new(Slot::new_reversible(value.clone(), ()));
    let alias = Arc::new(Slot::new_reversible(value.clone(), ()));
    let external = Arc::new(Slot::new_reversible(foreign.clone(), ()));
    let opaque = Arc::new(Slot::new_opaque((), ()));
    let provider = mount(
        &mut world,
        9701,
        vec![],
        vec![1, 2, 3, 4],
        Body::Callback(callback as Callback),
    );
    let mut publishing: Episode = world.begin_managed_execution(provider, 9702).unwrap();
    let invocation = world
        .admit_managed_root(provider, &mut publishing, ())
        .unwrap();
    let receipt = world.call_opaque(provider, invocation).ok().unwrap();
    publishing.complete_root(receipt).ok().unwrap().unwrap();
    for (key, service) in [(1, changed.clone()), (2, alias), (3, external), (4, opaque)] {
        publishing.provide(port(key), service).ok().unwrap();
    }
    world
        .finish_managed_execution(provider, &mut publishing)
        .unwrap();
    let consumer = mount(
        &mut world,
        9703,
        vec![1, 2, 3, 4],
        vec![],
        Body::Callback(callback as Callback),
    );
    let execution: Episode = world.begin_managed_execution(consumer, 9704).unwrap();
    let values = execution.native().unwrap();
    let old = values.read_reversible(port(1)).ok().unwrap();
    let _before = world
        .service_episode_snapshot(consumer, &execution)
        .unwrap();
    changed.reversible().unwrap().replace(foreign).ok().unwrap();
    let current = values.read_reversible(port(1)).ok().unwrap();
    let remaining_alias = values.read_reversible(port(2)).ok().unwrap();
    let external = values.read_reversible(port(3)).ok().unwrap();
    assert_eq!(old.capture().observe_value().value(), 10);
    assert_eq!(current.capture().observe_value().value(), 50);
    assert_eq!(remaining_alias.capture().observe_value().value(), 10);
    assert_eq!(external.capture().observe_value().value(), 50);
    assert!(values.read_reversible(port(4)).is_err());
    assert!(values.read(port(4)).unwrap().1.opaque().is_some());
    let _published = world.service_snapshot();
    let _joined = world
        .service_episode_snapshot(consumer, &execution)
        .unwrap();
    let _retained = old.capture().execution_snapshot();
}

#[test]
fn ordinary_native_calls_check_declarations_and_keep_the_actual_failed_prefix() {
    use cordis_kernel::reversible_value::access::Error;
    use cordis_kernel::reversible_value::slot::ReadError;
    use cordis_kernel::reversible_value::ValueError;
    let (mut world, value) = world();
    let consumer = mount(
        &mut world,
        190,
        vec![KEY],
        vec![],
        Body::Callback(callback as Callback),
    );
    let mut episode: Episode = world.begin_managed_execution(consumer, 9590).unwrap();
    let invocation = world
        .admit_managed_root(consumer, &mut episode, ())
        .unwrap();
    let end = Branch {
        matched: None,
        unmatched: None,
    };
    let read = episode
        .native()
        .unwrap()
        .observe_reversible(port(KEY))
        .unwrap();
    assert_eq!((read.binding.provider(), read.snapshot.value()), (0, 10));
    assert!(matches!(
        episode.apply_native_value(0, port(999), Operation::Add(9), end),
        Err(Error::Read(ReadError::Native(_)))
    ));
    assert!(episode
        .native()
        .unwrap()
        .observe_reversible(Port { key: KEY, realm: 1 })
        .is_err());
    assert_eq!(value.snapshot().depth(), 0);
    let write = episode
        .apply_native_value(0, port(KEY), Operation::Add(5), end)
        .unwrap();
    assert_eq!(
        (
            write.binding.port(),
            write.admission.outcome.after,
            write.admission.token
        ),
        (port(KEY), 15, 0)
    );
    let code = Program::new(vec![
        Instruction {
            operation: Operation::Add(2),
            branch: Branch {
                matched: Some(1),
                unmatched: Some(1),
            },
        },
        Instruction {
            operation: Operation::Add(u64::MAX),
            branch: end,
        },
    ])
    .unwrap();
    let report = episode
        .run_native_value_program(0, port(KEY), &code)
        .unwrap();
    assert_eq!(report.program.outcomes.len(), 1);
    assert_eq!(report.program.error, Some(ValueError::Overflow));
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (17, 2)
    );
    episode
        .complete_root(world.call_opaque(consumer, invocation).ok().unwrap())
        .ok()
        .unwrap()
        .unwrap();
    episode.withdraw();
    for expected in [15, 10] {
        let CleanupDispatch::Value { completion, .. } =
            episode.dispatch_cleanup(0).unwrap().unwrap()
        else {
            panic!("actual registered inverse")
        };
        assert!(completion.report.result.is_ok());
        assert_eq!(value.snapshot().value(), expected);
    }
    assert!(matches!(
        episode.apply_native_value(0, port(KEY), Operation::Add(1), end),
        Err(Error::Value(ValueError::Closed))
    ));
    assert_eq!(value.snapshot().depth(), 0);
}

#[test]
fn declared_native_calls_share_the_actual_dynamic_effect_queue() {
    use cordis_kernel::effect_work::EffectOutput;
    let (mut world, value) = world();
    let consumer = mount(
        &mut world,
        191,
        vec![KEY],
        vec![],
        Body::Callback(callback as Callback),
    );
    let mut episode: Episode = world.begin_managed_execution(consumer, 9591).unwrap();
    let invocation = world
        .admit_managed_root(consumer, &mut episode, ())
        .unwrap();
    let group = episode.enqueue_native_effect(0, 9592, ()).unwrap();
    let item = episode.take_group().unwrap();
    let receipt = item.run(|request| episode.activate_effect(request));
    assert!(episode.complete_request(receipt).ok().unwrap().is_ok());
    let mut runner = episode.take_effect(group).unwrap();
    let committed = episode.native().unwrap().setup_context().committed_vec();
    assert!(episode.admit_effect(&mut runner, Some(&committed)));
    let report = episode
        .apply_native_value(
            group,
            port(KEY),
            Operation::Add(4),
            Branch {
                matched: None,
                unmatched: None,
            },
        )
        .unwrap();
    assert_eq!(report.admission.token, 0);
    let (mut runner, reply) = runner
        .call((), |payload, ()| {
            (
                payload,
                EffectOutput::<ChildCleanup<(), ()>, ()>::Ready(Ok(None)),
            )
        })
        .ok()
        .unwrap();
    assert!(episode
        .land_effect(&mut runner, reply)
        .ok()
        .unwrap()
        .is_some());
    assert_eq!(value.snapshot().value(), 14);
    // The root queue did not receive this group's inverse.
    episode
        .complete_root(world.call_opaque(consumer, invocation).ok().unwrap())
        .ok()
        .unwrap()
        .unwrap();
    episode.withdraw();
    assert!(episode.dispatch_cleanup(0).unwrap().is_none());
    let CleanupDispatch::Value { completion, .. } =
        episode.dispatch_cleanup(group).unwrap().unwrap()
    else {
        panic!("group's exact inverse")
    };
    assert!(completion.report.result.is_ok());
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (10, 0)
    );
}

fn service_call(
    key: u64,
    operation: Operation,
    next: Option<usize>,
) -> cordis_kernel::reversible_value::services::Call {
    cordis_kernel::reversible_value::services::Call {
        port: port(key),
        instruction: Instruction {
            operation,
            branch: Branch {
                matched: next,
                unmatched: next,
            },
        },
    }
}

#[test]
fn multi_service_failure_keeps_cross_provider_prefix_and_alias_inverses() {
    use cordis_kernel::reversible_value::{access, services, ValueError};
    let (mut world, first) = world();
    let second = ReversibleValue::new_in(&world.execution_journal(), 40);
    let provider = mount(
        &mut world,
        200,
        vec![],
        vec![2, 3, 4],
        Body::Callback(callback as Callback),
    );
    let mut publishing: Episode = world.begin_managed_execution(provider, 9600).unwrap();
    let invocation = world
        .admit_managed_root(provider, &mut publishing, ())
        .unwrap();
    publishing
        .complete_root(world.call_opaque(provider, invocation).ok().unwrap())
        .ok()
        .unwrap()
        .unwrap();
    for (key, value) in [(2, first.clone()), (3, second.clone())] {
        publishing
            .provide(
                port(key),
                Arc::new(Slot::new_reversible(Arc::new(value), ())),
            )
            .ok()
            .unwrap();
    }
    publishing
        .provide(port(4), Arc::new(Slot::new_opaque((), ())))
        .ok()
        .unwrap();
    world
        .finish_managed_execution(provider, &mut publishing)
        .unwrap();
    let consumer = mount(
        &mut world,
        201,
        vec![1, 2, 3, 4],
        vec![],
        Body::Callback(callback as Callback),
    );
    let mut episode: Episode = world.begin_managed_execution(consumer, 9601).unwrap();
    let invocation = world
        .admit_managed_root(consumer, &mut episode, ())
        .unwrap();
    let mut compare = service_call(
        2,
        Operation::CompareExchange {
            expected: 12,
            value: 20,
        },
        Some(3),
    );
    compare.instruction.branch.unmatched = Some(2);
    let program = services::Program::new(vec![
        service_call(1, Operation::Add(2), Some(1)),
        compare,
        service_call(3, Operation::Replace(999), None),
        service_call(3, Operation::Add(5), Some(4)),
        service_call(1, Operation::Add(u64::MAX), None),
    ])
    .unwrap();
    let result = episode.run_service_program(0, &program).unwrap();
    assert!(!result.succeeded());
    assert_eq!(
        result.steps.iter().map(|s| s.pc).collect::<Vec<_>>(),
        [0, 1, 3]
    );
    assert_eq!(
        result
            .steps
            .iter()
            .map(|s| s.write.admission.token)
            .collect::<Vec<_>>(),
        [0, 1, 2]
    );
    assert_eq!(
        result
            .steps
            .iter()
            .map(|s| s.write.binding.provider())
            .collect::<Vec<_>>(),
        [0, provider, provider]
    );
    let failure = result.failure.unwrap();
    assert_eq!(failure.pc, 4);
    assert!(matches!(
        failure.error,
        access::Error::Value(ValueError::Overflow)
    ));
    assert_eq!(
        (first.snapshot().value(), second.snapshot().value()),
        (20, 45)
    );
    let opaque = services::Program::new(vec![service_call(4, Operation::Add(1), None)]).unwrap();
    let failure = episode
        .run_service_program(0, &opaque)
        .unwrap()
        .failure
        .unwrap();
    assert!(matches!(failure.error, access::Error::Read(_)));
    let _trace = world.service_episode_snapshot(consumer, &episode).unwrap();
    episode
        .complete_root(world.call_opaque(consumer, invocation).ok().unwrap())
        .ok()
        .unwrap()
        .unwrap();
    episode.withdraw();
    let mut restored = Vec::new();
    while let Some(dispatch) = episode.dispatch_cleanup(0).unwrap() {
        let CleanupDispatch::Value { completion, .. } = dispatch else {
            panic!("actual value inverse")
        };
        assert!(completion.report.result.is_ok());
        restored.push(completion.restored.unwrap().value());
    }
    assert_eq!(restored, [40, 12, 10]);
    assert_eq!(
        (first.snapshot().depth(), second.snapshot().depth()),
        (0, 0)
    );
    assert!(matches!(
        episode.run_service_program(0, &program),
        Err(services::AdmissionError::Closed)
    ));
}

#[test]
fn multi_service_preflight_checks_unselected_branches_and_realms_before_writes() {
    use cordis_kernel::reversible_value::services::{AdmissionError, Program};
    let (mut world, value) = world();
    let consumer = mount(
        &mut world,
        202,
        vec![KEY],
        vec![],
        Body::Callback(callback as Callback),
    );
    let mut episode: Episode = world.begin_managed_execution(consumer, 9602).unwrap();
    let empty = Program::new(vec![]).unwrap();
    assert!(episode.run_service_program(0, &empty).unwrap().succeeded());
    let code = Program::new(vec![
        service_call(KEY, Operation::Add(100), None),
        service_call(999, Operation::Add(1), None),
    ])
    .unwrap();
    assert!(matches!(
        episode.run_service_program(0, &code),
        Err(AdmissionError::Undeclared {
            pc: 1,
            port: Port { key: 999, realm: 0 }
        })
    ));
    let mut hidden = service_call(KEY, Operation::Add(1), None);
    hidden.port.realm = 1;
    let code = Program::new(vec![service_call(KEY, Operation::Add(100), None), hidden]).unwrap();
    assert!(matches!(
        episode.run_service_program(0, &code),
        Err(AdmissionError::Undeclared {
            pc: 1,
            port: Port { realm: 1, .. }
        })
    ));
    assert!(Program::new(vec![service_call(KEY, Operation::Add(1), Some(0))]).is_err());
    assert!(Program::new(vec![service_call(KEY, Operation::Add(1), Some(1))]).is_err());
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (10, 0)
    );
    episode.withdraw();
    assert!(episode.dispatch_cleanup(0).unwrap().is_none());
}

#[test]
fn multi_service_body_registers_only_in_its_actual_effect_group() {
    use cordis_kernel::effect_work::EffectOutput;
    use cordis_kernel::reversible_value::services::Program;
    let (mut world, value) = world();
    let consumer = mount(
        &mut world,
        203,
        vec![KEY],
        vec![],
        Body::Callback(callback as Callback),
    );
    let mut episode: Episode = world.begin_managed_execution(consumer, 9603).unwrap();
    let invocation = world
        .admit_managed_root(consumer, &mut episode, ())
        .unwrap();
    let group = episode.enqueue_native_effect(0, 9604, ()).unwrap();
    let receipt = episode
        .take_group()
        .unwrap()
        .run(|request| episode.activate_effect(request));
    assert!(episode.complete_request(receipt).ok().unwrap().is_ok());
    let mut runner = episode.take_effect(group).unwrap();
    let committed = episode.native().unwrap().setup_context().committed_vec();
    assert!(episode.admit_effect(&mut runner, Some(&committed)));
    let program = Program::new(vec![
        service_call(KEY, Operation::Add(2), Some(1)),
        service_call(KEY, Operation::Add(3), None),
    ])
    .unwrap();
    let report = episode.run_service_program(group, &program).unwrap();
    assert!(report.succeeded());
    assert_eq!(value.snapshot().value(), 15);
    let (mut runner, reply) = runner
        .call((), |payload, ()| {
            (
                payload,
                EffectOutput::<ChildCleanup<(), ()>, ()>::Ready(Ok(None)),
            )
        })
        .ok()
        .unwrap();
    assert!(episode
        .land_effect(&mut runner, reply)
        .ok()
        .unwrap()
        .is_some());
    episode
        .complete_root(world.call_opaque(consumer, invocation).ok().unwrap())
        .ok()
        .unwrap()
        .unwrap();
    episode.withdraw();
    assert!(episode.dispatch_cleanup(0).unwrap().is_none());
    for expected in [12, 10] {
        let CleanupDispatch::Value { completion, .. } =
            episode.dispatch_cleanup(group).unwrap().unwrap()
        else {
            panic!("group inverse")
        };
        assert!(completion.report.result.is_ok());
        assert_eq!(value.snapshot().value(), expected);
    }
}

#[test]
fn native_effect_retains_its_object_across_slot_replacement_and_unwinds_both() {
    use cordis_kernel::reversible_value::effect::ScaleAdd;
    let (mut world, original) = world();
    let consumer = mount(
        &mut world,
        211,
        vec![KEY],
        vec![],
        Body::Callback(callback as Callback),
    );
    let mut owner: Episode = world.begin_managed_execution(consumer, 9801).unwrap();
    let invocation = world.admit_managed_root(consumer, &mut owner, ()).unwrap();
    let slot = owner.native().unwrap().read(port(KEY)).unwrap().1.clone();
    let replacement = ReversibleValue::new_in(&world.execution_journal(), 100);
    let capture = owner.capture_native_effect(0, port(KEY)).unwrap();
    let prepared = capture.prepare(ScaleAdd {
        scale: 2,
        offset: 1,
    });
    slot.reversible()
        .unwrap()
        .replace(Arc::new(replacement.clone()))
        .ok()
        .unwrap();
    let branch = Branch {
        matched: Some(7),
        unmatched: Some(9),
    };
    let first = owner.apply_native_effect(0, prepared, branch).unwrap();
    assert_eq!(
        (
            first.admission.outcome.before,
            first.admission.outcome.after,
            first.admission.next,
            first.admission.token
        ),
        (10, 21, Some(7), 0)
    );
    assert_eq!(
        (original.snapshot().value(), replacement.snapshot().value()),
        (21, 100)
    );
    // A new call selects the new slot; the earlier inverse still owns the old allocation.
    let prepared =
        owner
            .capture_native_effect(0, port(KEY))
            .unwrap()
            .prepare(Operation::CompareExchange {
                expected: 999,
                value: 0,
            });
    let second = owner.apply_native_effect(0, prepared, branch).unwrap();
    assert_eq!(
        (
            second.admission.outcome.matched,
            second.admission.next,
            second.admission.token
        ),
        (false, Some(9), 1)
    );
    owner
        .complete_root(world.call_opaque(consumer, invocation).ok().unwrap())
        .ok()
        .unwrap()
        .unwrap();
    owner.withdraw();
    for _ in 0..2 {
        let CleanupDispatch::Value { completion, .. } = owner.dispatch_cleanup(0).unwrap().unwrap()
        else {
            panic!("managed inverse")
        };
        assert!(completion.report.result.is_ok());
    }
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
    assert!(owner.dispatch_cleanup(0).unwrap().is_none());
}

#[test]
fn native_effect_rejects_wrong_owner_interference_and_closed_admission() {
    use cordis_kernel::reversible_value::cursor::StartError;
    use cordis_kernel::reversible_value::effect::{EffectError, ScaleAdd};
    let (mut world, value) = world();
    let a = mount(
        &mut world,
        212,
        vec![KEY],
        vec![],
        Body::Callback(callback as Callback),
    );
    let b = mount(
        &mut world,
        213,
        vec![KEY],
        vec![],
        Body::Callback(callback as Callback),
    );
    let mut owner: Episode = world.begin_managed_execution(a, 9802).unwrap();
    let mut other: Episode = world.begin_managed_execution(b, 9803).unwrap();
    let end = Branch {
        matched: None,
        unmatched: None,
    };
    assert!(matches!(
        owner.capture_native_effect(0, port(999)),
        Err(StartError::Read(_))
    ));
    let prepared = owner
        .capture_native_effect(0, port(KEY))
        .unwrap()
        .prepare(Operation::Add(2));
    assert_eq!(
        other.apply_native_effect(0, prepared, end).err(),
        Some(EffectError::Closed)
    );
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (10, 0)
    );
    let prepared = owner
        .capture_native_effect(0, port(KEY))
        .unwrap()
        .prepare(Operation::Add(2));
    owner
        .apply_native_value(0, port(KEY), Operation::Add(1), end)
        .unwrap();
    assert_eq!(
        owner.apply_native_effect(0, prepared, end).err(),
        Some(EffectError::Interference)
    );
    let prepared = owner
        .capture_native_effect(0, port(KEY))
        .unwrap()
        .prepare(ScaleAdd {
            scale: u64::MAX,
            offset: 1,
        });
    assert_eq!(
        owner.apply_native_effect(0, prepared, end).err(),
        Some(EffectError::Rejected)
    );
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (11, 1)
    );
    let prepared = owner
        .capture_native_effect(0, port(KEY))
        .unwrap()
        .prepare(Operation::Add(2));
    owner.withdraw();
    assert_eq!(
        owner.apply_native_effect(0, prepared, end).err(),
        Some(EffectError::Closed)
    );
    assert!(matches!(
        owner.capture_native_effect(0, port(KEY)),
        Err(StartError::Closed)
    ));
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (11, 1)
    );
}

fn service_body(calls: Vec<(u64, Operation, Branch)>) -> Body<Callback> {
    use cordis_kernel::reversible_value::service_function::{Function, NamedCall};
    Body::Services(
        Function::new(
            calls
                .into_iter()
                .map(|(key, operation, branch)| NamedCall {
                    key,
                    instruction: Instruction { operation, branch },
                })
                .collect(),
        )
        .unwrap(),
    )
}

#[test]
fn registered_multi_service_prefix_keeps_alias_and_foreign_inverses() {
    let (mut world, value) = world();
    let foreign = ReversibleValue::new(40);
    let provider = mount(
        &mut world,
        9930,
        vec![],
        vec![2, 3],
        Body::Callback(callback as Callback),
    );
    let mut source: Episode = world.begin_managed_execution(provider, 9931).unwrap();
    let invocation = world.admit_managed_root(provider, &mut source, ()).unwrap();
    let receipt = world.call_opaque(provider, invocation).ok().unwrap();
    source.complete_root(receipt).ok().unwrap().unwrap();
    for (key, target) in [(2, value.clone()), (3, foreign.clone())] {
        source
            .provide(
                port(key),
                Arc::new(Slot::new_reversible(Arc::new(target), ())),
            )
            .ok()
            .unwrap();
    }
    world
        .finish_managed_execution(provider, &mut source)
        .unwrap();
    let end = Branch {
        matched: None,
        unmatched: None,
    };
    let next = |pc| Branch {
        matched: Some(pc),
        unmatched: Some(pc),
    };
    let id = mount(
        &mut world,
        9932,
        vec![KEY, 2, 3],
        vec![],
        service_body(vec![
            (KEY, Operation::Add(2), next(1)),
            (
                2,
                Operation::CompareExchange {
                    expected: 12,
                    value: 20,
                },
                Branch {
                    matched: Some(2),
                    unmatched: Some(3),
                },
            ),
            (3, Operation::Add(3), next(3)),
            (KEY, Operation::Add(u64::MAX), end),
        ]),
    );
    let mut episode: Episode = world.begin_managed_execution(id, 9933).unwrap();
    let report = world.run_service_root(id, &mut episode).unwrap();
    assert_eq!(report.origin.id, id);
    assert_eq!(report.revision, 0);
    let result = report.result.unwrap();
    assert_eq!(
        result.steps.iter().map(|step| step.pc).collect::<Vec<_>>(),
        [0, 1, 2]
    );
    assert_eq!(
        result
            .steps
            .iter()
            .map(|step| step.write.admission.token)
            .collect::<Vec<_>>(),
        [0, 1, 2]
    );
    assert!(result.steps[1].write.admission.outcome.matched);
    let failure = result.failure.unwrap();
    assert_eq!(failure.pc, 3);
    assert!(matches!(
        failure.error,
        cordis_kernel::reversible_value::access::Error::Value(
            cordis_kernel::reversible_value::ValueError::Overflow
        )
    ));
    assert_eq!(episode.work().root(), RootStatus::Settled);
    assert!(episode.work().root_failed_now());
    assert_eq!(
        (value.snapshot().value(), foreign.snapshot().value()),
        (20, 43)
    );
    episode.withdraw();
    let mut restored = Vec::new();
    while let Some(CleanupDispatch::Value { completion, .. }) = episode.dispatch_cleanup(0).unwrap()
    {
        assert!(completion.report.result.is_ok());
        restored.push(completion.restored.unwrap().value());
    }
    assert_eq!(restored, [40, 12, 10]);
    assert_eq!(
        (value.snapshot().depth(), foreign.snapshot().depth()),
        (0, 0)
    );
}

#[test]
fn registered_service_body_checks_all_keys_owner_revision_and_dispatch_kind() {
    use cordis_kernel::reversible_value::service_function::AdmissionError as ServiceAdmission;
    let (mut world, value) = world();
    let end = Branch {
        matched: None,
        unmatched: None,
    };
    // The unreachable second instruction is still a declaration obligation.
    let missing = mount(
        &mut world,
        9940,
        vec![KEY],
        vec![],
        service_body(vec![
            (KEY, Operation::Add(9), end),
            (2, Operation::Add(1), end),
        ]),
    );
    let mut a: Episode = world.begin_managed_execution(missing, 9941).unwrap();
    assert!(matches!(
        world.run_service_root(missing, &mut a),
        Err(ServiceAdmission::MissingDependency { pc: 1 })
    ));
    assert_eq!(a.work().root(), RootStatus::Unissued);
    assert_eq!(value.snapshot().value(), 10);
    let id = mount(
        &mut world,
        9942,
        vec![KEY],
        vec![],
        service_body(vec![(KEY, Operation::Add(1), end)]),
    );
    let mut b: Episode = world.begin_managed_execution(id, 9943).unwrap();
    assert!(matches!(
        world.run_service_root(id, &mut a),
        Err(ServiceAdmission::WrongOwner)
    ));
    assert!(matches!(
        world.run_value_root(id, &mut b),
        Err(AdmissionError::Opaque)
    ));
    world
        .replace(id, service_body(vec![(KEY, Operation::Add(7), end)]))
        .ok()
        .unwrap();
    let report = world.run_service_root(id, &mut b).unwrap();
    assert_eq!(report.revision, 1);
    assert!(report.result.unwrap().succeeded());
    assert_eq!(value.snapshot().value(), 17);
    assert!(matches!(
        world.run_service_root(id, &mut b),
        Err(ServiceAdmission::NotAdmitted)
    ));
    let retired = mount(
        &mut world,
        9944,
        vec![KEY],
        vec![],
        service_body(vec![(KEY, Operation::Add(8), end)]),
    );
    let mut c: Episode = world.begin_managed_execution(retired, 9945).unwrap();
    world.retire(retired).unwrap();
    assert!(matches!(
        world.run_service_root(retired, &mut c),
        Err(ServiceAdmission::NotAdmitted)
    ));
    assert_eq!(c.work().root(), RootStatus::Unissued);
    assert_eq!(value.snapshot().value(), 17);
    let empty = mount(&mut world, 9946, vec![], vec![], service_body(vec![]));
    let mut d: Episode = world.begin_managed_execution(empty, 9947).unwrap();
    assert!(world
        .run_service_root(empty, &mut d)
        .unwrap()
        .result
        .unwrap()
        .succeeded());
    assert_eq!(d.work().root(), RootStatus::Settled);
    let opaque = mount(
        &mut world,
        9948,
        vec![KEY],
        vec![],
        service_body(vec![(KEY, Operation::Add(8), end)]),
    );
    let mut e: Episode = world.begin_managed_execution(opaque, 9949).unwrap();
    let invocation = world.admit_managed_root(opaque, &mut e, ()).unwrap();
    assert!(world.call_opaque(opaque, invocation).is_err());
    assert_eq!(value.snapshot().value(), 17);
}
