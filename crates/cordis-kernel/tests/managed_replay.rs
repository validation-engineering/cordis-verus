use cordis_kernel::cleanup_groups::payload::Dispatch;
use cordis_kernel::cleanup_queue::completion::CleanupDispatch;
use cordis_kernel::lifecycle_state::native::runtime::NativeRuntime;
use cordis_kernel::lifecycle_state::registration::PluginDefinition;
use cordis_kernel::reversible_value::function::Body;
use cordis_kernel::reversible_value::managed::interleaving::history::lifecycle::RecordedExecution;
use cordis_kernel::reversible_value::managed::replay::inputs::{Operand, Seed, SeedError};
use cordis_kernel::reversible_value::managed::replay::{Destination, StartError, TargetRun};
use cordis_kernel::reversible_value::managed::{Call, Effect, Function, Owner, Slot};
use cordis_kernel::reversible_value::payload::SharedPayload;
use cordis_kernel::reversible_value::{Branch, Operation, ReversibleValue};
use cordis_kernel::{Phase, Port};
use std::{collections::BTreeMap, sync::Arc};

type Callback = fn(()) -> Result<(), ()>;
type World = NativeRuntime<Body<Callback, Function<Operation, String>>, (), Slot<String, ()>>;
type Episode = Owner<(), (), (), (), String, (), ()>;
type Recorded = RecordedExecution<(), (), (), (), String, (), ()>;
type Replay = TargetRun<(), (), (), (), String, (), (), Operation>;
fn port(key: u64) -> Port {
    Port { key, realm: 0 }
}
fn next(pc: Option<usize>) -> Branch {
    Branch {
        matched: pc,
        unmatched: pc,
    }
}
fn mount(
    world: &mut World,
    anchor: u64,
    deps: Vec<u64>,
    provisions: Vec<u64>,
    body: Body<Callback, Function<Operation, String>>,
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
fn program(fail: bool) -> Body<Callback, Function<Operation, String>> {
    let mut calls = vec![
        Call {
            key: 1,
            effect: Effect::Scalar(Operation::Add(7)),
            branch: next(Some(1)),
        },
        Call {
            key: 2,
            effect: Effect::Replace(Arc::new("new".into())),
            branch: next(if fail { Some(2) } else { None }),
        },
    ];
    if fail {
        calls.push(Call {
            key: 1,
            effect: Effect::Scalar(Operation::Add(u64::MAX)),
            branch: next(None),
        });
    }
    Body::Managed(Function::new(calls).ok().unwrap())
}
fn fixture(domain: u64, initial: u64) -> (World, ReversibleValue, SharedPayload<String>) {
    let mut world = World::new_recorded(domain, 256);
    let scalar = ReversibleValue::new_in(&world.execution_journal(), initial);
    let payload = SharedPayload::new_in(&world.execution_journal(), Arc::new("old".to_owned()));
    publish_values(&mut world, &scalar, &payload, domain + 1);
    (world, scalar, payload)
}
fn publish_values(
    world: &mut World,
    scalar: &ReversibleValue,
    payload: &SharedPayload<String>,
    work_domain: u64,
) {
    let provider = mount(
        world,
        100,
        vec![],
        vec![1, 2],
        Body::Callback((|()| Ok(())) as Callback),
    );
    let mut owner: Episode = world
        .begin_managed_execution(provider, work_domain)
        .unwrap();
    let call = world.admit_managed_root(provider, &mut owner, ()).unwrap();
    let reply = world.call_opaque(provider, call).ok().unwrap();
    owner.complete_root(reply).ok().unwrap().unwrap();
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
    world
        .finish_managed_execution(provider, &mut owner)
        .unwrap();
}
fn destination(anchor: u64, work_domain: u64) -> Destination<()> {
    Destination {
        parent: None,
        anchor: port(anchor),
        host: (),
        work_domain,
    }
}
fn drain(owner: &mut Recorded) {
    let Dispatch::Payload(done) = owner.dispatch(0).unwrap().unwrap() else {
        panic!("typed inverse")
    };
    assert!(done.report.result.is_ok());
    let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
        owner.dispatch(0).unwrap().unwrap()
    else {
        panic!("scalar inverse")
    };
    assert!(completion.report.result.is_ok());
}
fn start_cleanup(
    world: &mut World,
    owner: &mut Recorded,
    id: usize,
    retiring: bool,
) -> cordis_kernel::action_ledger::ActionTicket {
    if retiring {
        // Retirement disables future activation; leaving starts this Unload.
        world.retire(id).unwrap();
    }
    owner.withdraw(world, id, false).unwrap();
    world
        .settle_managed_execution(id, owner.execution())
        .unwrap();
    world.begin_cleanup(id).unwrap()
}

#[test]
fn captured_body_runs_on_new_resources_then_uses_real_failure_retry_and_recovery() {
    let (mut original, original_scalar, original_payload) = fixture(41_000, 5);
    let id = mount(&mut original, 101, vec![1, 2], vec![], program(false));
    let execution: Episode = original.begin_managed_execution(id, 41_002).unwrap();
    let (mut owner, captured) = original.run_replayable_root(id, execution);
    let captured = captured.unwrap();
    let source = captured.source;
    assert_eq!(source.source_origin(), captured.report.origin);
    let before = source
        .bind_control(&original)
        .unwrap()
        .source
        .commands()
        .len();
    owner.finish(&mut original, id).unwrap();
    start_cleanup(&mut original, &mut owner, id, true);
    drain(&mut owner);
    assert!(owner.release(&mut original, id).0.is_ok());
    original.remove(id).unwrap();
    assert!(
        source
            .bind_control(&original)
            .unwrap()
            .source
            .commands()
            .len()
            > before
    );
    assert_eq!(original_scalar.snapshot().value(), 5);
    assert_eq!(original_payload.capture().unwrap().value().as_str(), "old");

    let (mut target, scalar, payload) = fixture(42_000, 5);
    mount(
        &mut target,
        102,
        vec![],
        vec![],
        Body::Managed(Function::new(vec![]).ok().unwrap()),
    );
    let mut replay: Replay = source
        .instantiate(&mut target, destination(103, 42_002))
        .unwrap();
    assert_ne!(replay.id, id);
    let root = replay.report.as_ref().unwrap();
    assert!(root.result.as_ref().unwrap().failure.is_none());
    assert_ne!(root.origin, captured.report.origin);
    assert_ne!(root.work, captured.report.work);
    assert_eq!(root.work.domain(), 42_002);
    assert_eq!(scalar.snapshot().value(), 12);
    assert_eq!(payload.capture().unwrap().value().as_str(), "new");
    replay.owner.finish(&mut target, replay.id).unwrap();

    // A second actual invocation interferes, even though its replacement Arc
    // is the same retained source input. Cleanup must check the new version.
    let mut foreign: Replay = source
        .instantiate(&mut target, destination(104, 42_003))
        .unwrap();
    assert!(foreign
        .report
        .as_ref()
        .unwrap()
        .result
        .as_ref()
        .unwrap()
        .failure
        .is_none());
    foreign.owner.finish(&mut target, foreign.id).unwrap();
    assert_eq!(scalar.snapshot().value(), 19);
    let first = start_cleanup(&mut target, &mut replay.owner, replay.id, false);
    let Dispatch::Payload(blocked) = replay.owner.dispatch(0).unwrap().unwrap() else {
        panic!("blocked typed inverse")
    };
    assert!(blocked.report.result.is_err());
    target
        .fail_managed_execution(replay.id, replay.owner.execution())
        .unwrap();
    assert!(replay.owner.release(&mut target, replay.id).0.is_err());
    start_cleanup(&mut target, &mut foreign.owner, foreign.id, false);
    drain(&mut foreign.owner);
    assert!(foreign.owner.release(&mut target, foreign.id).0.is_ok());
    let retry = replay.owner.retry_native(&mut target, replay.id).unwrap();
    assert!(retry.action > first.action);
    let Dispatch::Payload(done) = replay.owner.dispatch(0).unwrap().unwrap() else {
        panic!("typed retry")
    };
    assert!(done.report.result.is_ok());
    assert_eq!(done.ticket.token, blocked.ticket.token);
    assert!(done.ticket.attempt > blocked.ticket.attempt);
    let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
        replay.owner.dispatch(0).unwrap().unwrap()
    else {
        panic!("scalar inverse")
    };
    assert!(completion.report.result.is_ok());
    let released = replay.owner.release(&mut target, replay.id);
    assert!(released.0.is_ok());
    let cut = replay.owner.capture_release_census(
        &target,
        replay.report.as_ref().unwrap(),
        0,
        0,
        &released,
        std::slice::from_ref(&scalar),
        std::slice::from_ref(&payload),
    );
    assert!(cut.control.is_ok());
    assert_eq!(target.kernel().phase(replay.id), Some(Phase::Inactive));
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (5, 0)
    );
    assert_eq!(payload.capture().unwrap().value().as_str(), "old");
    assert_eq!(original_scalar.snapshot().value(), 5);
    assert_eq!(original_payload.capture().unwrap().value().as_str(), "old");
}

#[test]
fn target_computes_from_target_inputs_and_preserves_real_partial_failure() {
    let (mut original, _, _) = fixture(43_000, 5);
    let id = mount(&mut original, 101, vec![1, 2], vec![], program(true));
    let execution: Episode = original.begin_managed_execution(id, 43_002).unwrap();
    let (_, captured) = original.run_replayable_root(id, execution);
    let captured = captured.unwrap();
    let prefix = captured.report.result.as_ref().unwrap();
    assert_eq!(prefix.steps.len(), 2);
    assert_eq!(captured.source.inputs().len(), 2);
    assert_eq!(captured.source.inputs()[1].pc(), 1);
    assert_eq!(prefix.failure.as_ref().unwrap().pc, 2);
    let (mut target, scalar, payload) = fixture(44_000, 30);
    let mut replay: Replay = captured
        .source
        .instantiate(&mut target, destination(101, 44_002))
        .unwrap();
    let actual = replay.report.as_ref().unwrap().result.as_ref().unwrap();
    assert_eq!(actual.steps.len(), 2);
    assert_eq!(actual.failure.as_ref().unwrap().pc, 2);
    assert_eq!(scalar.snapshot().value(), 37);
    assert_eq!(payload.capture().unwrap().value().as_str(), "new");
    start_cleanup(&mut target, &mut replay.owner, replay.id, false);
    drain(&mut replay.owner);
    assert!(replay.owner.release(&mut target, replay.id).0.is_ok());
    assert_eq!(scalar.snapshot().value(), 30);
}

#[test]
fn reused_ticket_domains_and_changed_bindings_do_not_execute_the_body() {
    let (mut original, _, _) = fixture(45_000, 5);
    let id = mount(&mut original, 101, vec![1, 2], vec![], program(false));
    let execution: Episode = original.begin_managed_execution(id, 45_002).unwrap();
    let (_, captured) = original.run_replayable_root(id, execution);
    let captured = captured.unwrap();
    let count = original.len();
    let reused: Result<Replay, _> = captured
        .source
        .instantiate(&mut original, destination(105, 45_003));
    assert!(matches!(reused, Err(StartError::ReusedDomain { .. })));
    assert_eq!(original.len(), count);
    let (mut target, scalar, payload) = fixture(46_000, 5);
    let count = target.len();
    let reused: Result<Replay, _> = captured
        .source
        .instantiate(&mut target, destination(105, 45_002));
    assert!(matches!(reused, Err(StartError::ReusedDomain { .. })));
    assert_eq!(target.len(), count);
    let parent = mount(
        &mut target,
        106,
        vec![3],
        vec![],
        Body::Managed(Function::new(vec![]).ok().unwrap()),
    );
    let mismatch: Result<Replay, _> = captured.source.instantiate(
        &mut target,
        Destination {
            parent: Some(parent),
            ..destination(105, 46_002)
        },
    );
    let Err(StartError::Binding { id }) = mismatch else {
        panic!("different inherited dependency must be rejected")
    };
    assert_eq!(target.kernel().phase(id), Some(Phase::Inactive));
    assert_eq!(scalar.snapshot().value(), 5);
    assert_eq!(payload.capture().unwrap().value().as_str(), "old");
    let mut empty = World::new_recorded(47_000, 32);
    let missing: Result<Replay, _> = captured
        .source
        .instantiate(&mut empty, destination(105, 47_001));
    let Err(StartError::Begin { id, .. }) = missing else {
        panic!("providers are unavailable")
    };
    assert_eq!(empty.kernel().phase(id), Some(Phase::Inactive));
}

#[test]
fn actual_operands_survive_source_changes_and_seed_a_real_target_call() {
    let (mut original, original_scalar, original_payload) = fixture(48_000, 5);
    let id = mount(&mut original, 101, vec![1, 2], vec![], program(false));
    let execution: Episode = original.begin_managed_execution(id, 48_002).unwrap();
    let (mut owner, captured) = original.run_replayable_root(id, execution);
    let source = captured.unwrap().source;
    owner.finish(&mut original, id).unwrap();
    start_cleanup(&mut original, &mut owner, id, true);
    drain(&mut owner);
    assert!(owner.release(&mut original, id).0.is_ok());
    original.remove(id).unwrap();
    // Later mutable storage cannot supply the operands of the earlier call.
    let changed = original_scalar
        .apply(Operation::Replace(99), next(None))
        .ok()
        .unwrap();
    original_payload
        .replace(Arc::new("later".into()))
        .ok()
        .unwrap();
    assert_eq!(original_scalar.snapshot().value(), 99);
    let inputs = source.inputs();
    assert_eq!(inputs.len(), 2);
    assert_eq!((inputs[0].pc(), inputs[0].token()), (0, 0));
    let Operand::Scalar(before) = inputs[0].operand() else {
        panic!("scalar input")
    };
    assert_eq!((before.value, before.depth), (5, 0));
    let Operand::Payload { value, head, depth } = inputs[1].operand() else {
        panic!("payload input")
    };
    assert_eq!((value.as_str(), *head, *depth), ("old", 0, 0));

    let mut target = World::new_recorded(49_000, 256);
    let Seed::Scalar(scalar) = source
        .seed_input(0, &target.execution_journal())
        .ok()
        .unwrap()
    else {
        panic!("scalar seed")
    };
    let Seed::Payload(payload) = source
        .seed_input(1, &target.execution_journal())
        .ok()
        .unwrap()
    else {
        panic!("payload seed")
    };
    assert!(matches!(
        source.seed_input(2, &target.execution_journal()),
        Err(SeedError::MissingStep)
    ));
    publish_values(&mut target, &scalar, &payload, 49_001);
    let mut replay: Replay = source
        .instantiate(&mut target, destination(101, 49_002))
        .unwrap();
    assert!(replay
        .report
        .as_ref()
        .unwrap()
        .result
        .as_ref()
        .unwrap()
        .succeeded());
    assert_eq!(scalar.snapshot().value(), 12);
    assert_eq!(payload.capture().unwrap().value().as_str(), "new");
    replay.owner.finish(&mut target, replay.id).unwrap();
    start_cleanup(&mut target, &mut replay.owner, replay.id, true);
    drain(&mut replay.owner);
    assert!(replay.owner.release(&mut target, replay.id).0.is_ok());
    assert_eq!(scalar.snapshot().value(), 5);
    assert_eq!(payload.capture().unwrap().value().as_str(), "old");
    assert_eq!(original_scalar.snapshot().value(), 99);
    assert_eq!(
        original_payload.capture().unwrap().value().as_str(),
        "later"
    );
    changed.inverse.restore().ok().unwrap();
}

#[test]
fn repeated_object_inputs_preserve_depth_instead_of_fabricating_a_fresh_history() {
    let (mut original, scalar, _) = fixture(50_000, 5);
    let body = Body::Managed(
        Function::new(vec![
            Call {
                key: 1,
                effect: Effect::Scalar(Operation::Add(7)),
                branch: next(Some(1)),
            },
            Call {
                key: 1,
                effect: Effect::Scalar(Operation::Xor(3)),
                branch: next(None),
            },
        ])
        .ok()
        .unwrap(),
    );
    let id = mount(&mut original, 101, vec![1], vec![], body);
    let execution: Episode = original.begin_managed_execution(id, 50_002).unwrap();
    let (mut owner, captured) = original.run_replayable_root(id, execution);
    let source = captured.unwrap().source;
    assert_eq!(scalar.snapshot().value(), 15);
    let inputs = source.inputs();
    assert_eq!(inputs.len(), 2);
    let Operand::Scalar(first) = inputs[0].operand() else {
        panic!("first scalar")
    };
    let Operand::Scalar(second) = inputs[1].operand() else {
        panic!("second scalar")
    };
    assert_eq!(
        (first.value, first.depth, second.value, second.depth),
        (5, 0, 12, 1)
    );
    let target = World::new_recorded(51_000, 64);
    assert!(inputs[0].seed(&target.execution_journal()).is_ok());
    assert!(matches!(
        source.seed_input(1, &target.execution_journal()),
        Err(SeedError::OutstandingScalarHistory)
    ));
    owner.finish(&mut original, id).unwrap();
    start_cleanup(&mut original, &mut owner, id, true);
    for _ in 0..2 {
        let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
            owner.dispatch(0).unwrap().unwrap()
        else {
            panic!("scalar inverse")
        };
        assert!(completion.report.result.is_ok());
    }
    assert!(owner.release(&mut original, id).0.is_ok());
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (5, 0)
    );
}

type Source = cordis_kernel::reversible_value::managed::replay::Source<Operation, String>;
fn capture_shared_pair(
    domain: u64,
    fail_second: bool,
) -> (World, Vec<Source>, Vec<(usize, Recorded)>) {
    let (mut original, scalar, payload) = fixture(domain, 5);
    let alias = mount(
        &mut original,
        110,
        vec![],
        vec![3, 4],
        Body::Callback((|()| Ok(())) as Callback),
    );
    let mut publisher: Episode = original.begin_managed_execution(alias, domain + 2).unwrap();
    let call = original
        .admit_managed_root(alias, &mut publisher, ())
        .unwrap();
    let reply = original.call_opaque(alias, call).ok().unwrap();
    publisher.complete_root(reply).ok().unwrap().unwrap();
    publisher
        .provide(
            port(3),
            Arc::new(Slot::new_reversible(Arc::new(scalar.clone()), ())),
        )
        .ok()
        .unwrap();
    publisher
        .provide(port(4), Arc::new(Slot::new_opaque(payload.clone(), ())))
        .ok()
        .unwrap();
    original
        .finish_managed_execution(alias, &mut publisher)
        .unwrap();

    let first = mount(&mut original, 111, vec![1, 2], vec![], program(false));
    let execution: Episode = original.begin_managed_execution(first, domain + 3).unwrap();
    let (mut first_owner, first_capture) = original.run_replayable_root(first, execution);
    first_owner.finish(&mut original, first).unwrap();
    let mut code = vec![
        Call {
            key: 3,
            effect: Effect::Scalar(Operation::Add(7)),
            branch: next(Some(1)),
        },
        Call {
            key: 4,
            effect: Effect::Replace(Arc::new("second".to_owned())),
            branch: next(if fail_second { Some(2) } else { None }),
        },
    ];
    if fail_second {
        code.push(Call {
            key: 3,
            effect: Effect::Scalar(Operation::Add(u64::MAX)),
            branch: next(None),
        });
    }
    let second = mount(
        &mut original,
        112,
        vec![3, 4],
        vec![],
        Body::Managed(Function::new(code).ok().unwrap()),
    );
    let execution: Episode = original
        .begin_managed_execution(second, domain + 4)
        .unwrap();
    let (mut second_owner, second_capture) = original.run_replayable_root(second, execution);
    if !fail_second {
        second_owner.finish(&mut original, second).unwrap();
    }
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (19, 2)
    );
    (
        original,
        vec![
            first_capture.unwrap().source,
            second_capture.unwrap().source,
        ],
        vec![(first, first_owner), (second, second_owner)],
    )
}

#[test]
fn allocation_identity_distinguishes_journals_and_survives_payload_retirement() {
    use cordis_kernel::reversible_value::joint::Journal;
    let a = Journal::new();
    let b = Journal::new();
    // Both are their Journal's first object: a local allocation index is insufficient.
    let left = ReversibleValue::new_in(&a, 5);
    let right = ReversibleValue::new_in(&b, 5);
    assert_eq!(left.identity().same(&left.clone().identity()), Some(true));
    assert_eq!(left.identity().same(&right.identity()), Some(false));
    let payload = SharedPayload::new_in(&a, Arc::new("old".to_owned()));
    let identity = payload.identity();
    assert!(payload.retire().is_some());
    assert_eq!(identity.same(&payload.identity()), Some(true));
}

#[test]
fn batch_reuses_two_aliased_objects_across_calls_and_preserves_cleanup_retry() {
    use cordis_kernel::reversible_value::managed::replay::batch::{self, Names};
    let (mut original, sources, mut original_owners) = capture_shared_pair(60_000, false);
    for step in 0..2 {
        assert_eq!(
            sources[0].inputs()[step]
                .identity()
                .same(sources[1].inputs()[step].identity()),
            Some(true)
        );
    }
    let Operand::Scalar(second) = sources[1].inputs()[0].operand() else {
        panic!("scalar")
    };
    assert_eq!((second.value, second.depth), (12, 1));
    let mut target = World::new_recorded(61_000, 512);
    let mut replay = batch::run(
        &mut target,
        &original.execution_journal(),
        &sources,
        Names {
            anchor: 900,
            work: 61_010,
        },
    );
    assert!(replay.failure.is_none(), "{:?}", replay.failure);
    assert_eq!(
        (
            replay.bank.len(),
            replay.providers.len(),
            replay.calls.len()
        ),
        (2, 4, 2)
    );
    let Seed::Scalar(scalar) = replay.bank.seed(0).unwrap() else {
        panic!("scalar seed")
    };
    let scalar = scalar.clone();
    let Seed::Payload(payload) = replay.bank.seed(1).unwrap() else {
        panic!("payload seed")
    };
    let payload = payload.clone();
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (19, 2)
    );
    assert_eq!(payload.capture().unwrap().value().as_str(), "second");
    let mut second = replay.calls.pop().unwrap();
    let mut first = replay.calls.pop().unwrap();
    let attempt = start_cleanup(&mut target, &mut first.owner, first.id, true);
    let Dispatch::Payload(blocked) = first.owner.dispatch(0).unwrap().unwrap() else {
        panic!("typed inverse")
    };
    assert!(blocked.report.result.is_err());
    target
        .fail_managed_execution(first.id, first.owner.execution())
        .unwrap();
    assert!(first.owner.release(&mut target, first.id).0.is_err());
    start_cleanup(&mut target, &mut second.owner, second.id, true);
    drain(&mut second.owner);
    assert!(second.owner.release(&mut target, second.id).0.is_ok());
    let retry = first.owner.retry_native(&mut target, first.id).unwrap();
    assert!(retry.action > attempt.action);
    drain(&mut first.owner);
    assert!(first.owner.release(&mut target, first.id).0.is_ok());
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (5, 0)
    );
    assert_eq!(payload.capture().unwrap().value().as_str(), "old");
    // The source's independent owners still restore the original objects.
    while let Some((id, mut owner)) = original_owners.pop() {
        start_cleanup(&mut original, &mut owner, id, true);
        drain(&mut owner);
        assert!(owner.release(&mut original, id).0.is_ok());
    }
}

#[test]
fn batch_derives_call_order_even_when_source_slice_is_reversed() {
    use cordis_kernel::reversible_value::managed::replay::batch::{self, Names};
    let (original, mut sources, _owners) = capture_shared_pair(62_000, false);
    sources.reverse();
    let mut target = World::new_recorded(63_000, 128);
    let replay = batch::run(
        &mut target,
        &original.execution_journal(),
        &sources,
        Names {
            anchor: 900,
            work: 63_010,
        },
    );
    assert!(replay.failure.is_none());
    assert_eq!(replay.order, vec![1, 0]);
    assert_eq!(replay.calls.len(), 2);
    let Seed::Scalar(value) = replay.bank.seed(0).unwrap() else {
        panic!("scalar seed")
    };
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (19, 2)
    );
}

#[test]
fn batch_refuses_to_invent_an_earlier_outstanding_inverse() {
    use cordis_kernel::reversible_value::managed::replay::{
        bank,
        batch::{self, Failure, Names},
    };
    let (original, mut sources, _owners) = capture_shared_pair(62_000, false);
    sources.remove(0);
    let mut target = World::new_recorded(63_000, 128);
    let replay = batch::run(
        &mut target,
        &original.execution_journal(),
        &sources,
        Names {
            anchor: 900,
            work: 63_010,
        },
    );
    assert!(matches!(
        replay.failure,
        Some(Failure::Binding {
            call: 0,
            error: bank::Error::Seed(SeedError::OutstandingScalarHistory)
        })
    ));
    assert!(replay.calls.is_empty() && replay.providers.is_empty() && replay.bank.is_empty());
}

#[test]
fn batch_failure_returns_both_real_invocation_owners_and_successful_prefix() {
    use cordis_kernel::reversible_value::managed::replay::batch::{self, Failure, Names};
    let (original, sources, _owners) = capture_shared_pair(64_000, true);
    let mut target = World::new_recorded(65_000, 512);
    let replay = batch::run(
        &mut target,
        &original.execution_journal(),
        &sources,
        Names {
            anchor: 900,
            work: 65_010,
        },
    );
    assert!(matches!(
        replay.failure,
        Some(Failure::Invocation { call: 1 })
    ));
    assert_eq!(
        (
            replay.bank.len(),
            replay.providers.len(),
            replay.calls.len()
        ),
        (2, 4, 2)
    );
    let report = replay.calls[1]
        .report
        .as_ref()
        .unwrap()
        .result
        .as_ref()
        .unwrap();
    assert_eq!(report.steps.len(), 2);
    assert_eq!(report.failure.as_ref().unwrap().pc, 2);
    let Seed::Scalar(value) = replay.bank.seed(0).unwrap() else {
        panic!("scalar")
    };
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (19, 2)
    );
    for provider in &replay.providers {
        assert!(provider
            .report
            .as_ref()
            .unwrap()
            .result
            .as_ref()
            .unwrap()
            .succeeded());
    }
}

#[test]
fn batch_rejects_a_service_rebound_to_another_source_allocation() {
    use cordis_kernel::reversible_value::managed::replay::batch::{self, Failure, Names};
    let (mut original, mut sources, owners) = capture_shared_pair(66_000, false);
    let replacement = ReversibleValue::new_in(&original.execution_journal(), 5);
    let (_, slot) = owners[0]
        .1
        .execution()
        .native()
        .unwrap()
        .read(port(1))
        .unwrap();
    slot.reversible()
        .unwrap()
        .replace(Arc::new(replacement))
        .ok()
        .unwrap();
    let third = mount(&mut original, 113, vec![1, 2], vec![], program(false));
    let owner: Episode = original.begin_managed_execution(third, 66_005).unwrap();
    let (_owner, captured) = original.run_replayable_root(third, owner);
    sources.truncate(1);
    sources.push(captured.unwrap().source);
    let mut target = World::new_recorded(68_000, 128);
    let replay = batch::run(
        &mut target,
        &original.execution_journal(),
        &sources,
        Names {
            anchor: 900,
            work: 68_010,
        },
    );
    assert!(matches!(
        replay.failure,
        Some(Failure::ReboundPort {
            port: Port { key: 1, realm: 0 }
        })
    ));
    assert!(replay.calls.is_empty() && replay.providers.is_empty());
}

fn scalar_branch_source(
    domain: u64,
) -> (
    World,
    cordis_kernel::reversible_value::managed::replay::Source<Operation, String>,
    Recorded,
) {
    let (mut world, _, _) = fixture(domain, 5);
    let function = Function::new(vec![
        Call {
            key: 1,
            effect: Effect::Scalar(Operation::CompareExchange {
                expected: 5,
                value: 9,
            }),
            branch: Branch {
                matched: Some(1),
                unmatched: None,
            },
        },
        Call {
            key: 1,
            effect: Effect::Scalar(Operation::Add(4)),
            branch: next(None),
        },
    ])
    .ok()
    .unwrap();
    let id = mount(&mut world, 101, vec![1], vec![], Body::Managed(function));
    let execution: Episode = world.begin_managed_execution(id, domain + 2).unwrap();
    let (mut owner, captured) = world.run_replayable_root(id, execution);
    let captured = captured.unwrap();
    assert!(captured.report.result.unwrap().failure.is_none());
    owner.finish(&mut world, id).unwrap();
    (world, captured.source, owner)
}

fn scalar_landing_owner(world: &mut World, anchor: u64, work: u64) -> Episode {
    let id = mount(
        world,
        anchor,
        vec![1],
        vec![],
        Body::Managed(Function::new(Vec::new()).ok().unwrap()),
    );
    let mut owner: Episode = world.begin_managed_execution(id, work).unwrap();
    let report = world.run_managed_root(id, &mut owner).unwrap();
    assert!(report.result.unwrap().failure.is_none());
    owner
}

#[test]
fn source_scalar_landing_derives_branch_depth_and_real_cleanup_inverses() {
    use cordis_kernel::reversible_value::managed::replay::scalar::PrepareError;
    use cordis_kernel::reversible_value::managed::ResultStep;

    let (_original, source, _source_owner) = scalar_branch_source(61_000);
    let (mut target, value, _) = fixture(62_000, 5);
    let mut owner = scalar_landing_owner(&mut target, 101, 62_002);

    // The second input must be produced by the first target operation.
    assert!(matches!(
        source.prepare_scalar(1, &owner, 0),
        Err(PrepareError::InputChanged(_))
    ));
    let first = source
        .prepare_scalar(0, &owner, 0)
        .unwrap()
        .land(&mut owner, 0)
        .ok()
        .unwrap();
    assert_eq!((first.pc, first.next), (0, Some(1)));
    let ResultStep::Scalar { write, .. } = first.result else {
        panic!("scalar step")
    };
    assert_eq!(write.admission.token, 0);
    assert!(write.admission.outcome.matched);
    assert_eq!(write.admission.outcome.after, 9);
    let second = source
        .prepare_scalar(1, &owner, 0)
        .unwrap()
        .land(&mut owner, 0)
        .ok()
        .unwrap();
    assert_eq!((second.pc, second.next), (1, None));
    let ResultStep::Scalar { write, .. } = second.result else {
        panic!("scalar step")
    };
    assert_eq!(write.admission.token, 1);
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (13, 2)
    );
    owner.withdraw();
    for _ in 0..2 {
        let CleanupDispatch::Value { completion, .. } = owner.dispatch_cleanup(0).unwrap().unwrap()
        else {
            panic!("actual queued scalar inverse")
        };
        assert!(completion.report.result.is_ok());
    }
    assert!(owner.dispatch_cleanup(0).unwrap().is_none());
    assert_eq!((value.snapshot().value(), value.snapshot().depth()), (5, 0));
}

#[test]
fn source_scalar_landing_reports_interference_and_retries_after_real_restoration() {
    use cordis_kernel::reversible_value::effect::EffectError;

    let (_original, source, _source_owner) = scalar_branch_source(63_000);
    let (mut target, value, _) = fixture(64_000, 5);
    let mut owner = scalar_landing_owner(&mut target, 101, 64_002);
    let prepared = source.prepare_scalar(0, &owner, 0).unwrap();
    let other = value.apply(Operation::Add(1), next(None)).ok().unwrap();
    assert_eq!(
        prepared.land(&mut owner, 0).err(),
        Some(EffectError::Interference)
    );
    assert!(owner.groups().get(0).unwrap().is_empty());
    assert_eq!((value.snapshot().value(), value.snapshot().depth()), (6, 1));
    // A real restoration, not a forged pre-state, enables a fresh attempt.
    other.inverse.restore().ok().unwrap();
    source
        .prepare_scalar(0, &owner, 0)
        .unwrap()
        .land(&mut owner, 0)
        .ok()
        .unwrap();
    assert!(!owner.groups().get(0).unwrap().is_empty());
    assert_eq!((value.snapshot().value(), value.snapshot().depth()), (9, 1));
}

#[test]
fn source_scalar_capture_checks_inverse_depth_and_missing_steps() {
    use cordis_kernel::reversible_value::managed::replay::scalar::PrepareError;
    use cordis_kernel::reversible_value::ValueState;

    let (_original, source, _source_owner) = scalar_branch_source(65_000);
    let (mut target, value, _) = fixture(66_000, 5);
    let owner = scalar_landing_owner(&mut target, 101, 66_002);
    let other = value.apply(Operation::Add(0), next(None)).ok().unwrap();
    let Err(PrepareError::InputChanged(mismatch)) = source.prepare_scalar(0, &owner, 0) else {
        panic!("equal values do not imply equal inverse depths")
    };
    assert_eq!(mismatch.expected, ValueState { value: 5, depth: 0 });
    assert_eq!(mismatch.observed, ValueState { value: 5, depth: 1 });
    assert!(!owner.has_pending());
    other.inverse.restore().ok().unwrap();
    assert!(source.prepare_scalar(0, &owner, 0).is_ok());
    assert!(matches!(
        source.prepare_scalar(2, &owner, 0),
        Err(PrepareError::MissingStep)
    ));
}

#[test]
fn source_scalar_landing_allows_unrelated_writes_and_rechecks_owner_admission() {
    use cordis_kernel::reversible_value::effect::EffectError;

    let (_original, source, _source_owner) = scalar_branch_source(67_000);
    let (mut target, value, _) = fixture(68_000, 5);
    let mut owner = scalar_landing_owner(&mut target, 101, 68_002);
    let mut wrong = scalar_landing_owner(&mut target, 102, 68_003);
    let prepared = source.prepare_scalar(0, &owner, 0).unwrap();
    assert_eq!(
        prepared.land(&mut wrong, 0).err(),
        Some(EffectError::Closed)
    );
    assert!(!wrong.has_pending());
    let prepared = source.prepare_scalar(0, &owner, 0).unwrap();
    let unrelated = ReversibleValue::new_in(&target.execution_journal(), 100);
    let other = unrelated.apply(Operation::Add(3), next(None)).ok().unwrap();
    assert!(prepared.land(&mut owner, 0).is_ok());
    other.inverse.restore().ok().unwrap();
    let prepared = source.prepare_scalar(1, &owner, 0).unwrap();
    owner.withdraw();
    assert_eq!(
        prepared.land(&mut owner, 0).err(),
        Some(EffectError::Closed)
    );
    assert_eq!((value.snapshot().value(), value.snapshot().depth()), (9, 1));
    let CleanupDispatch::Value { completion, .. } = owner.dispatch_cleanup(0).unwrap().unwrap()
    else {
        panic!("only the successful landing owns an inverse")
    };
    assert!(completion.report.result.is_ok());
    assert!(owner.dispatch_cleanup(0).unwrap().is_none());
}

#[test]
fn typed_source_continuity_uses_retained_histories_after_cleanup() {
    let (mut original, sources, mut owners) = capture_shared_pair(71_000, false);
    assert!(sources[0].position().unwrap() < sources[1].position().unwrap());
    assert_eq!(
        sources[1].inputs()[1].continues_payload(&sources[0].inputs()[1]),
        Some(true)
    );
    assert_eq!(
        sources[0].inputs()[1].continues_payload(&sources[1].inputs()[1]),
        Some(false)
    );
    assert_eq!(
        sources[1].inputs()[0].continues_payload(&sources[0].inputs()[0]),
        None
    );
    while let Some((id, mut owner)) = owners.pop() {
        start_cleanup(&mut original, &mut owner, id, true);
        drain(&mut owner);
        assert!(owner.release(&mut original, id).0.is_ok());
    }
    assert_eq!(
        sources[1].inputs()[1].continues_payload(&sources[0].inputs()[1]),
        Some(true)
    );
}

fn payload_landing_owner(world: &mut World, anchor: u64, work: u64) -> Episode {
    let id = mount(
        world,
        anchor,
        vec![2],
        vec![],
        Body::Managed(Function::new(Vec::new()).ok().unwrap()),
    );
    let mut owner: Episode = world.begin_managed_execution(id, work).unwrap();
    world.run_managed_root(id, &mut owner).unwrap();
    owner
}
#[test]
fn typed_native_landings_chain_actual_versions_and_cleanup_inverses() {
    let (mut world, _, value) = fixture(72_000, 5);
    let mut owner = payload_landing_owner(&mut world, 101, 72_002);
    let capture = owner.capture_native_payload(0, port(2)).unwrap();
    let (first, next) = capture
        .land(&mut owner, 0, Arc::new("first".into()))
        .ok()
        .unwrap();
    assert_eq!(first.token(), 0);
    assert_eq!(next.observation().revision(), 1);
    let (second, last) = next
        .land(&mut owner, 0, Arc::new("second".into()))
        .ok()
        .unwrap();
    assert_eq!(second.token(), 1);
    assert_eq!(last.observation().revision(), 2);
    assert_eq!(value.capture().unwrap().value().as_str(), "second");
    owner.withdraw();
    for _ in 0..2 {
        let Dispatch::Payload(done) = owner.dispatch_payload_cleanup(0).unwrap().unwrap() else {
            panic!("typed inverse")
        };
        assert!(done.report.result.is_ok());
    }
    assert_eq!(value.capture().unwrap().value().as_str(), "old");
    assert_eq!(value.capture().unwrap().revision(), 4);
    assert!(owner.groups().get(0).unwrap().is_empty());
}
#[test]
fn typed_native_landing_rejects_wrong_owner_stale_capture_and_retirement() {
    use cordis_kernel::versioned_value::ReplaceError;
    let (mut world, _, value) = fixture(73_000, 5);
    let mut owner = payload_landing_owner(&mut world, 101, 73_002);
    let mut wrong = payload_landing_owner(&mut world, 102, 73_003);
    let capture = owner.capture_native_payload(0, port(2)).unwrap();
    assert_eq!(
        capture
            .land(&mut wrong, 0, Arc::new("wrong".into()))
            .err()
            .unwrap()
            .0,
        ReplaceError::Closed
    );
    value.replace(Arc::new("outside".into())).ok().unwrap();
    let attempted: Arc<String> = Arc::new("stale".into());
    let error = capture
        .land(&mut owner, 0, attempted.clone())
        .err()
        .unwrap();
    assert_eq!(error.0, ReplaceError::Stale);
    assert!(Arc::ptr_eq(&error.1, &attempted));
    assert!(owner.groups().get(0).unwrap().is_empty());
    let fresh = owner.capture_native_payload(0, port(2)).unwrap();
    value.retire().unwrap();
    assert_eq!(
        fresh
            .land(&mut owner, 0, Arc::new("retired".into()))
            .err()
            .unwrap()
            .0,
        ReplaceError::Closed
    );
    assert!(owner.groups().get(0).unwrap().is_empty());
}
#[test]
fn typed_capture_rejects_stale_revision_even_after_semantic_restoration() {
    use cordis_kernel::versioned_value::ReplaceError;
    struct NoEq(u64);
    let value = SharedPayload::new(Arc::new(NoEq(5)));
    let captured = value.capture().unwrap();
    let (applied, next) = captured.apply(Arc::new(NoEq(8))).0.ok().unwrap();
    applied.inverse.restore().ok().unwrap();
    assert_eq!(value.capture().unwrap().value().0, 5);
    assert_eq!(
        captured.apply(Arc::new(NoEq(9))).0.err().unwrap().error,
        ReplaceError::Stale
    );
    assert_eq!(
        next.apply(Arc::new(NoEq(9))).0.err().unwrap().error,
        ReplaceError::Stale
    );
}

#[test]
fn batch_rejects_different_source_streams_before_provider_creation() {
    use cordis_kernel::reversible_value::managed::replay::{
        batch::{self, Failure, Names},
        order,
    };
    let (original, mut sources, _owners) = capture_shared_pair(74_000, false);
    let (_other, mut other, _other_owners) = capture_shared_pair(75_000, false);
    sources.truncate(1);
    sources.push(other.remove(0));
    let mut target = World::new_recorded(76_000, 128);
    let replay = batch::run(
        &mut target,
        &original.execution_journal(),
        &sources,
        Names {
            anchor: 900,
            work: 76_010,
        },
    );
    assert!(matches!(
        replay.failure,
        Some(Failure::Ordering(order::Error::DifferentStream { call: 1 }))
    ));
    assert!(replay.calls.is_empty() && replay.providers.is_empty() && replay.bank.is_empty());
}

#[test]
fn controlled_sources_execute_mixed_calls_and_restore_real_target_owners() {
    use cordis_kernel::reversible_value::effect::Instruction;
    use cordis_kernel::reversible_value::managed::replay::batch::{self, Names};
    let (mut original, original_scalar, original_payload) = fixture(94_000, 5);
    let mut sources = Vec::new();
    let mut owners = Vec::new();
    for (index, instruction, text) in [
        (0, Instruction::Operation(Operation::Add(7)), "first"),
        (
            1,
            Instruction::ScaleAdd {
                scale: 2,
                offset: 3,
            },
            "second",
        ),
    ] {
        let function = Function::new(vec![
            Call {
                key: 1,
                effect: Effect::Kernel(instruction),
                branch: next(Some(1)),
            },
            Call {
                key: 2,
                effect: Effect::Replace(Arc::new(text.to_owned())),
                branch: next(None),
            },
        ])
        .ok()
        .unwrap();
        assert!(function.is_controlled());
        let id = mount(
            &mut original,
            110 + index,
            vec![1, 2],
            vec![],
            Body::Managed(function),
        );
        let owner: Episode = original
            .begin_managed_execution(id, 94_010 + index)
            .unwrap();
        let (mut owner, captured) = original.run_replayable_root(id, owner);
        let captured = captured.unwrap();
        assert!(captured.source.is_controlled());
        assert!(captured.report.result.as_ref().unwrap().failure.is_none());
        owner.finish(&mut original, id).unwrap();
        sources.push(captured.source);
        owners.push((id, owner));
    }
    assert_eq!(
        (
            original_scalar.snapshot().value(),
            original_scalar.snapshot().depth()
        ),
        (27, 2)
    );
    sources.reverse();
    let mut target = World::new_recorded(95_000, 256);
    let mut batch = batch::run_controlled(
        &mut target,
        &original.execution_journal(),
        &sources,
        Names {
            anchor: 900,
            work: 95_010,
        },
    )
    .ok()
    .unwrap();
    assert!(batch.failure.is_none(), "{:?}", batch.failure);
    assert_eq!(batch.order, vec![1, 0]);
    let Seed::Scalar(scalar) = batch.bank.seed(0).unwrap() else {
        panic!("scalar")
    };
    let scalar = scalar.clone();
    let Seed::Payload(payload) = batch.bank.seed(1).unwrap() else {
        panic!("payload")
    };
    let payload = payload.clone();
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (27, 2)
    );
    assert_eq!(payload.capture().unwrap().value().as_str(), "second");
    while let Some(mut run) = batch.calls.pop() {
        start_cleanup(&mut target, &mut run.owner, run.id, true);
        drain(&mut run.owner);
        assert!(run.owner.release(&mut target, run.id).0.is_ok());
    }
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (5, 0)
    );
    assert_eq!(payload.capture().unwrap().value().as_str(), "old");
    while let Some((id, mut owner)) = owners.pop() {
        start_cleanup(&mut original, &mut owner, id, true);
        drain(&mut owner);
        assert!(owner.release(&mut original, id).0.is_ok());
    }
    assert_eq!(
        (
            original_scalar.snapshot().value(),
            original_scalar.snapshot().depth()
        ),
        (5, 0)
    );
    assert_eq!(original_payload.capture().unwrap().value().as_str(), "old");
}

#[test]
fn controlled_gate_rejects_an_unvisited_callback_before_target_registration() {
    use cordis_kernel::reversible_value::effect::Instruction;
    use cordis_kernel::reversible_value::managed::replay::batch::{self, Names};
    let (mut source, _, _) = fixture(96_000, 5);
    let function = Function::new(vec![
        Call {
            key: 1,
            effect: Effect::Kernel(Instruction::Operation(Operation::Add(1))),
            branch: next(None),
        },
        Call {
            key: 1,
            effect: Effect::Scalar(Operation::Add(10)),
            branch: next(None),
        },
    ])
    .ok()
    .unwrap();
    assert!(!function.is_controlled());
    let id = mount(&mut source, 111, vec![1], vec![], Body::Managed(function));
    let owner: Episode = source.begin_managed_execution(id, 96_010).unwrap();
    let (_, captured) = source.run_replayable_root(id, owner);
    let captured = captured.unwrap();
    assert_eq!(captured.report.result.as_ref().unwrap().steps.len(), 1);
    let mut target = World::new_recorded(97_000, 256);
    let sources = [captured.source];
    let result = batch::run_controlled(
        &mut target,
        &source.execution_journal(),
        &sources,
        Names {
            anchor: 900,
            work: 97_010,
        },
    );
    assert!(matches!(result, Err(0)));
    let exclusive = batch::run_exclusive(
        &mut target,
        &source.execution_journal(),
        &sources,
        Names {
            anchor: 900,
            work: 97_010,
        },
    );
    assert!(matches!(
        exclusive,
        Err(batch::PreflightError::NotScalar { call: 0 })
    ));
    // The first actual registration still receives id zero.
    assert_eq!(
        mount(
            &mut target,
            900,
            vec![],
            vec![],
            Body::Managed(Function::new(Vec::new()).ok().unwrap())
        ),
        0
    );
}

#[test]
fn controlled_rejection_keeps_the_real_successful_prefix_for_cleanup() {
    use cordis_kernel::reversible_value::effect::{EffectError, Instruction};
    let (mut world, scalar, _) = fixture(98_000, 5);
    let function = Function::new(vec![
        Call {
            key: 1,
            effect: Effect::Kernel(Instruction::Operation(Operation::Add(7))),
            branch: next(Some(1)),
        },
        Call {
            key: 1,
            effect: Effect::Kernel(Instruction::ScaleAdd {
                scale: u64::MAX,
                offset: 1,
            }),
            branch: next(None),
        },
    ])
    .ok()
    .unwrap();
    let id = mount(&mut world, 111, vec![1], vec![], Body::Managed(function));
    let mut owner: Episode = world.begin_managed_execution(id, 98_010).unwrap();
    let report = world
        .run_managed_root(id, &mut owner)
        .unwrap()
        .result
        .unwrap();
    assert_eq!(report.steps.len(), 1);
    assert!(matches!(
        report.failure.unwrap().error,
        cordis_kernel::reversible_value::managed::Error::Scalar(EffectError::Rejected)
    ));
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (12, 1)
    );
    owner.withdraw();
    let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
        owner.dispatch_payload_cleanup(0).unwrap().unwrap()
    else {
        panic!("scalar inverse")
    };
    assert!(completion.report.result.is_ok());
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (5, 0)
    );
    assert!(owner.groups().get(0).unwrap().is_empty());
}

#[test]
fn bank_keeps_equal_valued_allocations_distinct_and_reuses_cross_call_aliases() {
    use cordis_kernel::reversible_value::joint::Journal;
    use cordis_kernel::reversible_value::managed::replay::bank::Bank;

    let (first_world, first, _first_owners) = capture_shared_pair(81_000, false);
    let (_second_world, second, _second_owners) = capture_shared_pair(82_000, false);
    let target = Journal::new();
    let mut bank = Bank::new(&first_world.execution_journal(), &target);
    let left = bank.bind(&first[0].inputs()[0]).unwrap();

    // The allocation frontier must allow unrelated real Journal operations.
    let unrelated = ReversibleValue::new_in(&target, 5);
    let right = bank.bind(&second[0].inputs()[0]).unwrap();
    let left_payload = bank.bind(&first[0].inputs()[1]).unwrap();
    let right_payload = bank.bind(&second[0].inputs()[1]).unwrap();
    assert_eq!(bank.len(), 4);
    assert_ne!(left, right);
    assert_ne!(left_payload, right_payload);
    assert_eq!(bank.bind(&first[1].inputs()[0]).unwrap(), left);
    assert_eq!(bank.bind(&second[1].inputs()[0]).unwrap(), right);
    assert_eq!(bank.bind(&first[1].inputs()[1]).unwrap(), left_payload);
    assert_eq!(bank.bind(&second[1].inputs()[1]).unwrap(), right_payload);
    assert_eq!(bank.len(), 4);

    let Seed::Scalar(a) = bank.seed(left).unwrap() else {
        panic!("scalar seed")
    };
    let Seed::Scalar(b) = bank.seed(right).unwrap() else {
        panic!("scalar seed")
    };
    assert_eq!(a.identity().same(&b.identity()), Some(false));
    assert_eq!(a.identity().same(&unrelated.identity()), Some(false));
    assert_eq!(b.identity().same(&unrelated.identity()), Some(false));
    let applied = a.apply(Operation::Add(7), next(None)).unwrap();
    assert_eq!(a.snapshot().value(), 12);
    assert_eq!((b.snapshot().value(), b.snapshot().depth()), (5, 0));
    assert_eq!(unrelated.snapshot().value(), 5);
    assert!(applied.inverse.restore().is_ok());

    let Seed::Payload(a) = bank.seed(left_payload).unwrap() else {
        panic!("payload seed")
    };
    let Seed::Payload(b) = bank.seed(right_payload).unwrap() else {
        panic!("payload seed")
    };
    assert_eq!(a.identity().same(&b.identity()), Some(false));
    assert!(a.retire().is_some());
    assert!(b.capture().is_some());
    assert!(b.retire().is_some());
}

fn capture_kernel_call(
    world: &mut World,
    anchor: u64,
    work: u64,
    instruction: cordis_kernel::reversible_value::effect::Instruction,
) -> (usize, Recorded, Source) {
    let function = Function::new(vec![Call {
        key: 1,
        effect: Effect::Kernel(instruction),
        branch: next(None),
    }])
    .ok()
    .unwrap();
    let id = mount(world, anchor, vec![1], vec![], Body::Managed(function));
    let owner: Episode = world.begin_managed_execution(id, work).unwrap();
    let (mut owner, captured) = world.run_replayable_root(id, owner);
    let captured = captured.unwrap();
    if captured.source.succeeded() {
        owner.finish(world, id).unwrap();
    }
    (id, owner, captured.source)
}

#[test]
fn checked_scalar_batch_matches_actual_calls_and_restores_its_owners() {
    scalar_batch_roundtrip(false);
}
#[test]
fn exclusive_batch_reuses_actual_cells_across_calls_and_releases_for_cleanup() {
    scalar_batch_roundtrip(true);
}
fn scalar_batch_roundtrip(exclusive: bool) {
    use cordis_kernel::reversible_value::effect::Instruction;
    use cordis_kernel::reversible_value::managed::replay::batch::{self, Names};
    let (mut original, _, _) = fixture(110_000, 5);
    let (_first, _first_owner, first) = capture_kernel_call(
        &mut original,
        101,
        110_010,
        Instruction::Operation(Operation::Add(7)),
    );
    let (_second, _second_owner, second) = capture_kernel_call(
        &mut original,
        102,
        110_011,
        Instruction::ScaleAdd {
            scale: 2,
            offset: 3,
        },
    );
    let sources = vec![second, first];
    let mut target = World::new_recorded(111_000, 256);
    let names = Names {
        anchor: 900,
        work: 111_010,
    };
    let mut replay = if exclusive {
        batch::run_exclusive(&mut target, &original.execution_journal(), &sources, names).unwrap()
    } else {
        batch::run_checked_scalar(&mut target, &original.execution_journal(), &sources, names)
            .unwrap()
            .batch
    };
    assert!(replay.failure.is_none(), "{:?}", replay.failure);
    assert_eq!(replay.order, vec![1, 0]);
    assert_eq!(replay.calls.len(), 2);
    let Seed::Scalar(value) = replay.bank.seed(0).unwrap() else {
        panic!("scalar")
    };
    let value = value.clone();
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (27, 2)
    );
    for (position, run) in replay.calls.iter().enumerate() {
        assert_eq!(
            run.check_scalar_observations(&sources[replay.order[position]]),
            Ok(())
        );
        assert_eq!(
            run.check_scalar_replay(
                &sources[replay.order[position]],
                &replay.bank,
                &replay.providers
            ),
            Ok(())
        );
    }
    while let Some(mut run) = replay.calls.pop() {
        start_cleanup(&mut target, &mut run.owner, run.id, true);
        let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
            run.owner.dispatch(0).unwrap().unwrap()
        else {
            panic!("scalar inverse")
        };
        assert!(completion.report.result.is_ok());
        assert!(run.owner.release(&mut target, run.id).0.is_ok());
    }
    assert_eq!((value.snapshot().value(), value.snapshot().depth()), (5, 0));
}

#[test]
fn checked_scalar_preflight_detects_omitted_zero_write_depth_before_target_changes() {
    use cordis_kernel::reversible_value::effect::Instruction;
    use cordis_kernel::reversible_value::managed::replay::{
        batch::{self, Names, PreflightError},
        continuity::{Error, Site},
    };
    let (mut original, value, _) = fixture(112_000, 5);
    let (_, _owner, first) = capture_kernel_call(
        &mut original,
        101,
        112_010,
        Instruction::Operation(Operation::Add(7)),
    );
    let _unrepresented = value.apply(Operation::Add(0), next(None)).unwrap();
    let (_, _other_owner, second) = capture_kernel_call(
        &mut original,
        102,
        112_011,
        Instruction::Operation(Operation::Add(7)),
    );
    let mut target = World::new_recorded(113_000, 128);
    let error = batch::run_checked_scalar(
        &mut target,
        &original.execution_journal(),
        &[first, second],
        Names {
            anchor: 900,
            work: 113_010,
        },
    )
    .err()
    .unwrap();
    assert!(matches!(
        error,
        PreflightError::Continuity(Error::Changed {
            previous: Site { call: 0, step: 0 },
            current: Site { call: 1, step: 0 },
        })
    ));
    assert!(target.registration(0).is_none());
}

#[test]
fn actual_target_input_check_rejects_equal_value_at_wrong_inverse_depth() {
    use cordis_kernel::reversible_value::effect::Instruction;
    use cordis_kernel::reversible_value::managed::replay::observation::Error;
    use cordis_kernel::reversible_value::ValueState;
    let (mut original, _, _) = fixture(114_000, 5);
    let (_, _first_owner, _) = capture_kernel_call(
        &mut original,
        101,
        114_010,
        Instruction::Operation(Operation::Add(7)),
    );
    let (_, _second_owner, source) = capture_kernel_call(
        &mut original,
        102,
        114_011,
        Instruction::Operation(Operation::Add(7)),
    );
    let (mut target, scalar, _) = fixture(115_000, 12);
    let mut run: Replay = source
        .instantiate(&mut target, destination(101, 115_010))
        .unwrap();
    assert!(run
        .report
        .as_ref()
        .unwrap()
        .result
        .as_ref()
        .unwrap()
        .succeeded());
    assert_eq!(scalar.snapshot().value(), 19);
    assert_eq!(
        run.check_scalar_observations(&source),
        Err(Error::State {
            step: 0,
            expected: ValueState {
                value: 12,
                depth: 1
            },
            observed: ValueState {
                value: 12,
                depth: 0
            },
        })
    );
    assert!(!run.owner.execution().groups().get(0).unwrap().is_empty());
    run.owner.finish(&mut target, run.id).unwrap();
    start_cleanup(&mut target, &mut run.owner, run.id, true);
    let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
        run.owner.dispatch(0).unwrap().unwrap()
    else {
        panic!("retained inverse")
    };
    assert!(completion.report.result.is_ok());
    assert!(run.owner.release(&mut target, run.id).0.is_ok());
    assert_eq!(
        (scalar.snapshot().value(), scalar.snapshot().depth()),
        (12, 0)
    );
    // Historical inputs remain available after cleanup. The live-owner replay
    // admission contract no longer applies after its cleanup boundary advances.
    let Operand::Scalar(observed) = run.inputs[0].operand() else {
        panic!("scalar input")
    };
    assert_eq!(
        *observed,
        ValueState {
            value: 12,
            depth: 0
        }
    );
}

#[test]
fn continuity_checks_real_mixed_aliases_without_rereading_source_objects() {
    use cordis_kernel::reversible_value::managed::replay::{continuity, order};
    let (mut original, mut sources, mut owners) = capture_shared_pair(116_000, false);
    sources.reverse();
    let indices = order::plan(&sources).unwrap();
    assert_eq!(indices, vec![1, 0]);
    assert!(continuity::check(&sources, &indices).is_ok());
    while let Some((id, mut owner)) = owners.pop() {
        start_cleanup(&mut original, &mut owner, id, true);
        drain(&mut owner);
        assert!(owner.release(&mut original, id).0.is_ok());
    }
    assert!(continuity::check(&sources, &indices).is_ok());
    assert!(matches!(
        continuity::check(&sources, &[0, 1]),
        Err(continuity::Error::Changed { .. })
    ));
}

#[test]
fn checked_scalar_preflight_rejects_failed_sources_and_other_effect_families() {
    use cordis_kernel::reversible_value::effect::Instruction;
    use cordis_kernel::reversible_value::managed::replay::batch::{self, Names, PreflightError};
    let (mut original, _, _) = fixture(117_000, u64::MAX);
    let (_, _owner, failed) = capture_kernel_call(
        &mut original,
        101,
        117_010,
        Instruction::Operation(Operation::Add(1)),
    );
    assert!(!failed.succeeded());
    let mut target = World::new_recorded(118_000, 128);
    assert!(matches!(
        batch::run_checked_scalar(
            &mut target,
            &original.execution_journal(),
            &[failed],
            Names {
                anchor: 900,
                work: 118_010
            },
        ),
        Err(PreflightError::SourceIncomplete { call: 0 })
    ));
    assert!(target.registration(0).is_none());
    let (mixed, sources, _owners) = capture_shared_pair(119_000, false);
    assert!(matches!(
        batch::run_checked_scalar(
            &mut target,
            &mixed.execution_journal(),
            &sources,
            Names {
                anchor: 900,
                work: 118_010
            },
        ),
        Err(PreflightError::NotScalar { call: 0 })
    ));
    assert!(target.registration(0).is_none());
}

fn prepare_scalar_bank(
    source: &cordis_kernel::reversible_value::managed::replay::Source<Operation, String>,
    source_journal: &cordis_kernel::reversible_value::joint::Journal,
    target: &mut World,
    work: u64,
) -> (
    cordis_kernel::reversible_value::managed::replay::bank::Bank<String>,
    Vec<cordis_kernel::reversible_value::managed::replay::batch::Provider<Operation, String>>,
) {
    use cordis_kernel::reversible_value::managed::replay::{bank::Bank, batch::Provider};
    let mut bank = Bank::new(source_journal, &target.execution_journal());
    let index = bank.bind(&source.inputs()[0]).unwrap();
    let id = mount(
        target,
        900,
        vec![],
        vec![1],
        Body::Managed(Function::new(vec![]).ok().unwrap()),
    );
    let execution: Episode = target.begin_managed_execution(id, work).unwrap();
    let (mut owner, report) = target.run_recorded_root(id, execution);
    assert!(report
        .as_ref()
        .unwrap()
        .result
        .as_ref()
        .unwrap()
        .succeeded());
    owner
        .provide(port(1), bank.slot(index).unwrap())
        .ok()
        .unwrap();
    owner.finish(target, id).unwrap();
    let service = bank.slot(index).unwrap();
    (
        bank,
        vec![Provider {
            id,
            port: port(1),
            index,
            slot: None,
            source_origin: None,
            service,
            owner,
            report,
        }],
    )
}

#[test]
fn mapped_scalar_replay_rejects_same_state_replacement_in_local_and_foreign_journals() {
    use cordis_kernel::reversible_value::effect::Instruction;
    use cordis_kernel::reversible_value::managed::replay::selection;
    let (mut original, _, _) = fixture(120_000, 5);
    let (_, _source_owner, source) = capture_kernel_call(
        &mut original,
        101,
        120_010,
        Instruction::Operation(Operation::Add(7)),
    );
    for (case, foreign) in [false, true].into_iter().enumerate() {
        let domain = 121_000 + 100 * case as u64;
        let mut target = World::new_recorded(domain, 256);
        let (bank, providers) = prepare_scalar_bank(
            &source,
            &original.execution_journal(),
            &mut target,
            domain + 1,
        );
        let replacement = if foreign {
            ReversibleValue::new(5)
        } else {
            ReversibleValue::new_in(&target.execution_journal(), 5)
        };
        let slot = bank.slot(0).unwrap();
        slot.reversible()
            .unwrap()
            .replace(Arc::new(replacement.clone()))
            .ok()
            .unwrap();
        let mut run: Replay = source
            .instantiate(&mut target, destination(901, domain + 2))
            .ok()
            .unwrap();
        assert_eq!(run.check_scalar_observations(&source), Ok(()));
        assert_eq!(
            run.check_scalar_replay(&source, &bank, &providers),
            Err(selection::Error::ReplacedSlot {
                step: 0,
                revision: 1
            })
        );
        assert_eq!(replacement.snapshot().value(), 12);
        let Seed::Scalar(expected) = bank.seed(0).unwrap() else {
            panic!("scalar seed")
        };
        assert_eq!(
            (expected.snapshot().value(), expected.snapshot().depth()),
            (5, 0)
        );
        // The rejected check retains the actual inverse for the object it changed.
        start_cleanup(&mut target, &mut run.owner, run.id, true);
        let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
            run.owner.dispatch(0).unwrap().unwrap()
        else {
            panic!("retained scalar inverse")
        };
        assert!(completion.report.result.is_ok());
        assert_eq!(
            (
                replacement.snapshot().value(),
                replacement.snapshot().depth()
            ),
            (5, 0)
        );
        assert!(run.owner.release(&mut target, run.id).0.is_ok());
    }
}

#[test]
fn mapped_scalar_replay_uses_the_recorded_selection_after_a_later_slot_change() {
    use cordis_kernel::reversible_value::effect::Instruction;
    let (mut original, _, _) = fixture(122_000, 5);
    let (_, _source_owner, source) = capture_kernel_call(
        &mut original,
        101,
        122_010,
        Instruction::Operation(Operation::Add(7)),
    );
    let mut target = World::new_recorded(123_000, 256);
    let (bank, providers) =
        prepare_scalar_bank(&source, &original.execution_journal(), &mut target, 123_001);
    let mut run: Replay = source
        .instantiate(&mut target, destination(901, 123_002))
        .ok()
        .unwrap();
    assert_eq!(run.check_scalar_replay(&source, &bank, &providers), Ok(()));
    let replacement = ReversibleValue::new(5);
    bank.slot(0)
        .unwrap()
        .reversible()
        .unwrap()
        .replace(Arc::new(replacement.clone()))
        .ok()
        .unwrap();
    assert_eq!(run.check_scalar_replay(&source, &bank, &providers), Ok(()));
    let Seed::Scalar(expected) = bank.seed(0).unwrap() else {
        panic!("scalar seed")
    };
    assert_eq!(expected.snapshot().value(), 12);
    start_cleanup(&mut target, &mut run.owner, run.id, true);
    let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
        run.owner.dispatch(0).unwrap().unwrap()
    else {
        panic!("retained scalar inverse")
    };
    assert!(completion.report.result.is_ok());
    assert_eq!(
        (expected.snapshot().value(), expected.snapshot().depth()),
        (5, 0)
    );
    assert_eq!(
        (
            replacement.snapshot().value(),
            replacement.snapshot().depth()
        ),
        (5, 0)
    );
    assert!(run.owner.release(&mut target, run.id).0.is_ok());
}

fn publish_bank_service(
    world: &mut World,
    bank: &cordis_kernel::reversible_value::managed::replay::bank::Bank<String>,
    index: usize,
    key: u64,
    anchor: u64,
    work: u64,
) -> cordis_kernel::reversible_value::managed::replay::batch::Provider<Operation, String> {
    let id = mount(
        world,
        anchor,
        vec![],
        vec![key],
        Body::Managed(Function::new(vec![]).ok().unwrap()),
    );
    let execution: Episode = world.begin_managed_execution(id, work).unwrap();
    let (mut owner, report) = world.run_recorded_root(id, execution);
    assert!(report
        .as_ref()
        .unwrap()
        .result
        .as_ref()
        .unwrap()
        .succeeded());
    owner
        .provide(port(key), bank.slot(index).unwrap())
        .ok()
        .unwrap();
    owner.finish(world, id).unwrap();
    cordis_kernel::reversible_value::managed::replay::batch::Provider {
        id,
        port: port(key),
        index,
        slot: None,
        source_origin: None,
        service: bank.slot(index).unwrap(),
        owner,
        report,
    }
}

fn capture_payload_call(
    world: &mut World,
    anchor: u64,
    work: u64,
    value: &str,
) -> (Recorded, Source) {
    let body = Body::Managed(
        Function::new(vec![Call {
            key: 2,
            effect: Effect::Replace(Arc::new(value.to_owned())),
            branch: next(None),
        }])
        .ok()
        .unwrap(),
    );
    let id = mount(world, anchor, vec![2], vec![], body);
    let execution: Episode = world.begin_managed_execution(id, work).unwrap();
    let (mut owner, captured) = world.run_replayable_root(id, execution);
    let captured = captured.unwrap();
    assert!(captured.source.succeeded());
    owner.finish(world, id).unwrap();
    (owner, captured.source)
}

#[test]
fn source_typed_cursor_renames_real_versions_across_calls_and_restores_old_heads() {
    use cordis_kernel::reversible_value::managed::replay::{bank::Bank, typed::Cursor};
    let (mut original, _, source_value) = fixture(124_000, 5);
    source_value
        .replace(Arc::new("intermediate".to_owned()))
        .ok()
        .unwrap();
    source_value
        .replace(Arc::new("old".to_owned()))
        .ok()
        .unwrap();
    let (_first_owner, first) = capture_payload_call(&mut original, 101, 124_010, "first");
    let (_second_owner, second) = capture_payload_call(&mut original, 102, 124_011, "second");
    assert_eq!(first.inputs()[0].payload_after_head(), Some(3));
    assert_eq!(second.inputs()[0].payload_after_head(), Some(4));
    let mut target = World::new_recorded(125_000, 256);
    let mut bank = Bank::new(&original.execution_journal(), &target.execution_journal());
    let index = bank.bind(&first.inputs()[0]).unwrap();
    assert_eq!(bank.bind(&second.inputs()[0]).unwrap(), index);
    let providers = vec![publish_bank_service(
        &mut target,
        &bank,
        index,
        2,
        900,
        125_001,
    )];
    let mut cursor = Cursor::start(&bank, index).ok().unwrap();
    let mut left = payload_landing_owner(&mut target, 901, 125_010);
    let mut right = payload_landing_owner(&mut target, 902, 125_011);
    assert!(matches!(
        cursor.apply(&second, 0, &mut left, 0, &bank, &providers),
        Err(cordis_kernel::reversible_value::managed::replay::typed::Error::SourceChanged)
    ));
    assert!(left.groups().get(0).unwrap().is_empty());
    cursor
        .apply(&first, 0, &mut left, 0, &bank, &providers)
        .ok()
        .unwrap();
    assert_eq!(cursor.target_revision(), 1);
    cursor
        .apply(&second, 0, &mut right, 0, &bank, &providers)
        .ok()
        .unwrap();
    assert_eq!(cursor.target_revision(), 2);
    let Seed::Payload(value) = bank.seed(index).unwrap() else {
        panic!("payload");
    };
    assert_eq!(value.capture().unwrap().value().as_str(), "second");
    let stale = value.capture().unwrap();
    for owner in [&mut right, &mut left] {
        owner.withdraw();
        let Dispatch::Payload(done) = owner.dispatch_payload_cleanup(0).unwrap().unwrap() else {
            panic!("actual typed inverse");
        };
        assert!(done.report.result.is_ok());
        assert!(owner.groups().get(0).unwrap().is_empty());
    }
    assert_eq!(value.capture().unwrap().value().as_str(), "old");
    assert_eq!(value.capture().unwrap().revision(), 4);
    assert!(!stale.check_result(true).accepted());
    assert_eq!(source_value.capture().unwrap().value().as_str(), "second");
}

#[test]
fn source_typed_cursor_rejects_external_changes_before_registering_an_inverse() {
    use cordis_kernel::reversible_value::managed::replay::{
        bank::Bank,
        typed::{Cursor, Error},
    };
    let (mut original, _, _) = fixture(126_000, 5);
    let (_source_owner, source) = capture_payload_call(&mut original, 101, 126_010, "changed");
    let mut target = World::new_recorded(127_000, 256);
    let mut bank = Bank::new(&original.execution_journal(), &target.execution_journal());
    let index = bank.bind(&source.inputs()[0]).unwrap();
    let providers = vec![publish_bank_service(
        &mut target,
        &bank,
        index,
        2,
        900,
        127_001,
    )];
    let mut cursor = Cursor::start(&bank, index).ok().unwrap();
    let mut owner = payload_landing_owner(&mut target, 901, 127_010);
    let Seed::Payload(value) = bank.seed(index).unwrap() else {
        panic!("payload");
    };
    // Semantic restoration still advances the anti-stale clock.
    let external = value.apply(Arc::new("external".to_owned())).ok().unwrap();
    assert!(external.inverse.restore().is_ok());
    assert_eq!(value.capture().unwrap().value().as_str(), "old");
    assert!(matches!(
        cursor.apply(&source, 0, &mut owner, 0, &bank, &providers),
        Err(Error::TargetClock {
            source: 0,
            target: 2
        })
    ));
    assert!(owner.groups().get(0).unwrap().is_empty());
    assert_eq!(cursor.target_revision(), 0);
    assert!(value.retire().is_some());
    assert!(matches!(
        cursor.apply(&source, 0, &mut owner, 0, &bank, &providers),
        Err(Error::Capture(_))
    ));
    assert!(owner.groups().get(0).unwrap().is_empty());
}

#[test]
fn source_typed_cursor_rejects_initial_unowned_inverse_debt() {
    use cordis_kernel::reversible_value::managed::replay::{
        bank::Bank,
        typed::{Cursor, Error},
    };
    let (mut original, _, payload) = fixture(128_000, 5);
    let external = payload.apply(Arc::new("pending".to_owned())).ok().unwrap();
    let (_owner, source) = capture_payload_call(&mut original, 101, 128_010, "after");
    let mut bank = Bank::new(
        &original.execution_journal(),
        &cordis_kernel::reversible_value::joint::Journal::new(),
    );
    let index = bank.bind(&source.inputs()[0]).unwrap();
    assert!(matches!(
        Cursor::start(&bank, index),
        Err(Error::OutstandingHistory)
    ));
    assert!(external.inverse.restore().is_err());
}

#[test]
fn mapped_prewrite_guard_supports_rebinding_and_retains_old_targets() {
    use cordis_kernel::reversible_value::effect::Instruction;
    use cordis_kernel::reversible_value::managed::replay::{
        bank::Bank,
        binding::{Error, Selection},
    };
    let (mut original, _, _) = fixture(129_000, 5);
    let (_, first_owner, first) = capture_kernel_call(
        &mut original,
        101,
        129_010,
        Instruction::Operation(Operation::Add(7)),
    );
    let replacement = ReversibleValue::new_in(&original.execution_journal(), 9);
    first_owner
        .execution()
        .native()
        .unwrap()
        .read(port(1))
        .unwrap()
        .1
        .reversible()
        .unwrap()
        .replace(Arc::new(replacement))
        .ok()
        .unwrap();
    let (_, _second_owner, second) = capture_kernel_call(
        &mut original,
        102,
        129_011,
        Instruction::Operation(Operation::Add(3)),
    );
    let mut target = World::new_recorded(130_000, 256);
    let mut bank = Bank::new(&original.execution_journal(), &target.execution_journal());
    let a = bank.bind(&first.inputs()[0]).unwrap();
    let b = bank.bind(&second.inputs()[0]).unwrap();
    assert_ne!(a, b);
    let providers = vec![publish_bank_service(&mut target, &bank, a, 1, 900, 130_001)];
    let initial = Selection::initial(&bank, a).unwrap();
    let mut left = scalar_landing_owner(&mut target, 901, 130_010);
    let mut right = scalar_landing_owner(&mut target, 902, 130_011);
    let prepared = first
        .prepare_mapped_scalar(0, &left, 0, &bank, &providers, &initial)
        .unwrap();
    let selected = Selection::replace(&bank, a, b).unwrap();
    assert_eq!(selected.revision(), 1);
    // This call retains A although the live slot now selects B.
    prepared.land(&mut left, 0).unwrap();
    second
        .prepare_mapped_scalar(0, &right, 0, &bank, &providers, &selected)
        .unwrap()
        .land(&mut right, 0)
        .unwrap();
    let Seed::Scalar(av) = bank.seed(a).unwrap() else {
        panic!("scalar");
    };
    let Seed::Scalar(bv) = bank.seed(b).unwrap() else {
        panic!("scalar");
    };
    assert_eq!((av.snapshot().value(), bv.snapshot().value()), (12, 12));
    assert!(matches!(
        first.prepare_mapped_scalar(0, &left, 0, &bank, &providers, &selected),
        Err(Error::SourceObject)
    ));
    for owner in [&mut right, &mut left] {
        owner.withdraw();
        let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
            owner.dispatch_payload_cleanup(0).unwrap().unwrap()
        else {
            panic!("actual scalar inverse");
        };
        assert!(completion.report.result.is_ok());
    }
    assert_eq!((av.snapshot().value(), bv.snapshot().value()), (5, 9));
}

#[test]
fn mapped_prewrite_guard_rejects_same_state_replacement_and_intervening_writes() {
    use cordis_kernel::reversible_value::effect::{EffectError, Instruction};
    use cordis_kernel::reversible_value::managed::replay::binding::{Error, Selection};
    let (mut original, _, _) = fixture(131_000, 5);
    let (_, _source_owner, source) = capture_kernel_call(
        &mut original,
        101,
        131_010,
        Instruction::Operation(Operation::Add(7)),
    );
    let mut target = World::new_recorded(132_000, 256);
    let (bank, providers) =
        prepare_scalar_bank(&source, &original.execution_journal(), &mut target, 132_001);
    let selected = Selection::initial(&bank, 0).unwrap();
    let mut owner = scalar_landing_owner(&mut target, 901, 132_010);
    let prepared = source
        .prepare_mapped_scalar(0, &owner, 0, &bank, &providers, &selected)
        .unwrap();
    let Seed::Scalar(value) = bank.seed(0).unwrap() else {
        panic!("scalar");
    };
    let interference = value.apply(Operation::Add(1), next(None)).unwrap();
    assert!(matches!(
        prepared.land(&mut owner, 0),
        Err(EffectError::Interference)
    ));
    assert_eq!(value.snapshot().value(), 6);
    assert!(owner.groups().get(0).unwrap().is_empty());
    assert!(interference.inverse.restore().is_ok());
    let foreign = ReversibleValue::new(5);
    bank.slot(0)
        .unwrap()
        .reversible()
        .unwrap()
        .replace(Arc::new(foreign.clone()))
        .ok()
        .unwrap();
    assert!(matches!(
        source.prepare_mapped_scalar(0, &owner, 0, &bank, &providers, &selected),
        Err(Error::ChangedVersion)
    ));
    assert_eq!(foreign.snapshot().value(), 5);
    assert!(owner.groups().get(0).unwrap().is_empty());
}

#[test]
fn typed_cursor_resumes_from_a_real_restored_head_with_fresh_revision_names() {
    use cordis_kernel::reversible_value::managed::replay::{bank::Bank, typed::Cursor};
    let (mut original, _, source_value) = fixture(133_000, 5);
    source_value
        .replace(Arc::new("old".to_owned()))
        .ok()
        .unwrap();
    source_value
        .replace(Arc::new("old".to_owned()))
        .ok()
        .unwrap();
    let (mut source_owner, first) = capture_payload_call(&mut original, 101, 133_010, "first");
    let source_id = source_owner.execution().native().unwrap().ticket().id;
    start_cleanup(&mut original, &mut source_owner, source_id, true);
    let Dispatch::Payload(done) = source_owner.dispatch(0).unwrap().unwrap() else {
        panic!("source inverse");
    };
    assert!(done.report.result.is_ok());
    assert_eq!(source_value.capture().unwrap().head(), 2);
    assert_eq!(source_value.capture().unwrap().revision(), 4);
    let (_later_owner, later) = capture_payload_call(&mut original, 102, 133_011, "later");
    let mut target = World::new_recorded(134_000, 256);
    let mut bank = Bank::new(&original.execution_journal(), &target.execution_journal());
    let index = bank.bind(&first.inputs()[0]).unwrap();
    let providers = vec![publish_bank_service(
        &mut target,
        &bank,
        index,
        2,
        900,
        134_001,
    )];
    let mut cursor = Cursor::start(&bank, index).ok().unwrap();
    let mut first_target = payload_landing_owner(&mut target, 901, 134_010);
    cursor
        .apply(&first, 0, &mut first_target, 0, &bank, &providers)
        .ok()
        .unwrap();
    first_target.withdraw();
    let Dispatch::Payload(done) = first_target.dispatch_payload_cleanup(0).unwrap().unwrap() else {
        panic!("target inverse");
    };
    assert!(done.report.result.is_ok());
    let Seed::Payload(value) = bank.seed(index).unwrap() else {
        panic!("payload");
    };
    let restored = value.capture().unwrap();
    assert_eq!(
        (restored.head(), restored.depth(), restored.revision()),
        (0, 0, 2)
    );
    let mut later_target = payload_landing_owner(&mut target, 902, 134_011);
    cursor
        .apply(&later, 0, &mut later_target, 0, &bank, &providers)
        .ok()
        .unwrap();
    assert_eq!(later.inputs()[0].payload_after_head(), Some(5));
    assert_eq!(cursor.target_revision(), 3);
    assert_eq!(value.capture().unwrap().value().as_str(), "later");
    later_target.withdraw();
    let Dispatch::Payload(done) = later_target.dispatch_payload_cleanup(0).unwrap().unwrap() else {
        panic!("later target inverse");
    };
    assert!(done.report.result.is_ok());
    let restored_again = value.capture().unwrap();
    assert_eq!(
        (
            restored_again.head(),
            restored_again.depth(),
            restored_again.revision()
        ),
        (0, 0, 4)
    );
    assert_eq!(restored_again.value().as_str(), "old");
}

#[test]
fn exclusive_partial_batch_releases_locks_and_retains_the_completed_owner() {
    use cordis_kernel::reversible_value::effect::Instruction;
    use cordis_kernel::reversible_value::managed::replay::batch::{self, Failure, Names};
    let (mut original, _, _) = fixture(152_000, 5);
    let (_, _first_owner, first) = capture_kernel_call(
        &mut original,
        101,
        152_010,
        Instruction::Operation(Operation::Add(7)),
    );
    let (_, _second_owner, second) = capture_kernel_call(
        &mut original,
        102,
        152_011,
        Instruction::Operation(Operation::Add(3)),
    );
    let mut target = World::new_recorded(153_000, 256);
    let mut replay = batch::run_exclusive(
        &mut target,
        &original.execution_journal(),
        &[first, second],
        Names {
            anchor: 900,
            work: u64::MAX - 2,
        },
    )
    .unwrap();
    assert!(matches!(replay.failure, Some(Failure::Capacity)));
    assert_eq!(replay.calls.len(), 1);
    let Seed::Scalar(value) = replay.bank.seed(0).unwrap() else {
        panic!("scalar")
    };
    let value = value.clone();
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (12, 1)
    );
    let mut run = replay.calls.pop().unwrap();
    start_cleanup(&mut target, &mut run.owner, run.id, true);
    let Dispatch::Other(CleanupDispatch::Value { completion, .. }) =
        run.owner.dispatch(0).unwrap().unwrap()
    else {
        panic!("retained scalar inverse")
    };
    assert!(completion.report.result.is_ok());
    assert!(run.owner.release(&mut target, run.id).0.is_ok());
    assert_eq!((value.snapshot().value(), value.snapshot().depth()), (5, 0));
}

#[test]
fn exclusive_typed_batch_issues_fresh_versions_and_restores_through_real_cleanup() {
    use cordis_kernel::reversible_value::managed::replay::batch::{self, Names};
    let (mut original, _, source_value) = fixture(154_000, 5);
    source_value
        .replace(Arc::new("old".to_owned()))
        .ok()
        .unwrap();
    source_value
        .replace(Arc::new("old".to_owned()))
        .ok()
        .unwrap();
    let (_first_owner, first) = capture_payload_call(&mut original, 101, 154_010, "first");
    let (_second_owner, second) = capture_payload_call(&mut original, 102, 154_011, "second");
    let mut target = World::new_recorded(155_000, 256);
    let mut replay = batch::run_exclusive_typed(
        &mut target,
        &original.execution_journal(),
        &[second, first],
        Names {
            anchor: 900,
            work: 155_010,
        },
    )
    .unwrap();
    assert!(replay.failure.is_none(), "{:?}", replay.failure);
    assert_eq!(replay.order, vec![1, 0]);
    assert_eq!(replay.calls.len(), 2);
    let Seed::Payload(value) = replay.bank.seed(0).unwrap() else {
        panic!("payload")
    };
    let value = value.clone();
    let stale = value.capture().unwrap();
    assert_eq!(stale.value().as_str(), "second");
    assert_eq!((stale.head(), stale.depth(), stale.revision()), (2, 2, 2));
    assert_eq!(replay.calls[0].inputs[0].payload_after_head(), Some(1));
    assert_eq!(replay.calls[1].inputs[0].payload_after_head(), Some(2));
    while let Some(mut run) = replay.calls.pop() {
        start_cleanup(&mut target, &mut run.owner, run.id, true);
        let Dispatch::Payload(done) = run.owner.dispatch(0).unwrap().unwrap() else {
            panic!("typed inverse")
        };
        assert!(done.report.result.is_ok());
        assert!(run.owner.release(&mut target, run.id).0.is_ok());
    }
    let restored = value.capture().unwrap();
    assert_eq!(restored.value().as_str(), "old");
    assert_eq!(
        (restored.head(), restored.depth(), restored.revision()),
        (0, 0, 4)
    );
    assert!(!stale.check_result(true).accepted());
    assert_eq!(source_value.capture().unwrap().revision(), 4);
}

#[test]
fn exclusive_typed_partial_batch_retains_owner_and_releases_every_guard() {
    use cordis_kernel::reversible_value::managed::replay::batch::{self, Failure, Names};
    let (mut original, _, _) = fixture(156_000, 5);
    let (_a, first) = capture_payload_call(&mut original, 101, 156_010, "first");
    let (_b, second) = capture_payload_call(&mut original, 102, 156_011, "second");
    let mut target = World::new_recorded(157_000, 256);
    let mut replay = batch::run_exclusive_typed(
        &mut target,
        &original.execution_journal(),
        &[first, second],
        Names {
            anchor: 900,
            work: u64::MAX - 2,
        },
    )
    .unwrap();
    assert!(matches!(replay.failure, Some(Failure::Capacity)));
    assert_eq!(replay.calls.len(), 1);
    let Seed::Payload(value) = replay.bank.seed(0).unwrap() else {
        panic!("payload")
    };
    let value = value.clone();
    assert_eq!(value.capture().unwrap().value().as_str(), "first");
    let mut run = replay.calls.pop().unwrap();
    start_cleanup(&mut target, &mut run.owner, run.id, true);
    let Dispatch::Payload(done) = run.owner.dispatch(0).unwrap().unwrap() else {
        panic!("typed inverse")
    };
    assert!(done.report.result.is_ok());
    assert!(run.owner.release(&mut target, run.id).0.is_ok());
    assert_eq!(value.capture().unwrap().revision(), 2);
    assert_eq!(value.capture().unwrap().value().as_str(), "old");
}

#[test]
fn exclusive_typed_batch_rejects_initial_inverse_debt_before_replay_writes() {
    use cordis_kernel::reversible_value::managed::replay::{
        batch::{self, Failure, Names},
        protected::{Error, TypedError},
    };
    let (mut original, _, value) = fixture(158_000, 5);
    let retained = value.apply(Arc::new("unowned".to_owned())).ok().unwrap();
    let (_owner, source) = capture_payload_call(&mut original, 101, 158_010, "changed");
    let mut target = World::new_recorded(159_000, 256);
    let replay = batch::run_exclusive_typed(
        &mut target,
        &original.execution_journal(),
        &[source],
        Names {
            anchor: 900,
            work: 159_010,
        },
    )
    .unwrap();
    assert!(matches!(
        replay.failure,
        Some(Failure::Protection {
            call: None,
            error: Error::Typed(TypedError::OutstandingHistory { entry: 0 })
        })
    ));
    assert!(replay.calls.is_empty());
    let Seed::Payload(target_value) = replay.bank.seed(0).unwrap() else {
        panic!("payload")
    };
    assert_eq!(target_value.capture().unwrap().revision(), 0);
    drop(retained);
}

#[test]
fn exclusive_typed_batch_composes_skipped_branches_and_equal_payload_heads() {
    use cordis_kernel::reversible_value::managed::replay::batch::{self, Names};
    let (mut original, _, source_value) = fixture(160_000, 5);
    source_value
        .replace(Arc::new("old".to_owned()))
        .ok()
        .unwrap();
    source_value
        .replace(Arc::new("old".to_owned()))
        .ok()
        .unwrap();
    let same = Arc::new("same".to_owned());
    let body = Body::Managed(
        Function::new(vec![
            Call {
                key: 2,
                effect: Effect::Replace(same.clone()),
                branch: next(Some(2)),
            },
            Call {
                key: 2,
                effect: Effect::Replace(Arc::new("unvisited".to_owned())),
                branch: next(None),
            },
            Call {
                key: 2,
                effect: Effect::Replace(same),
                branch: next(None),
            },
        ])
        .ok()
        .unwrap(),
    );
    let id = mount(&mut original, 101, vec![2], vec![], body);
    let owner: Episode = original.begin_managed_execution(id, 160_010).unwrap();
    let (mut first_owner, first) = original.run_replayable_root(id, owner);
    let first = first.unwrap().source;
    assert!(first.succeeded());
    assert_eq!(
        first.inputs().iter().map(|x| x.pc()).collect::<Vec<_>>(),
        vec![0, 2]
    );
    assert_eq!(first.inputs()[0].payload_after_head(), Some(3));
    assert_eq!(first.inputs()[1].payload_after_head(), Some(4));
    first_owner.finish(&mut original, id).unwrap();
    let (_second_owner, second) = capture_payload_call(&mut original, 102, 160_011, "last");
    let mut target = World::new_recorded(161_000, 256);
    let mut replay = batch::run_exclusive_typed(
        &mut target,
        &original.execution_journal(),
        &[second, first],
        Names {
            anchor: 900,
            work: 161_010,
        },
    )
    .unwrap();
    assert!(replay.failure.is_none(), "{:?}", replay.failure);
    assert_eq!(replay.order, vec![1, 0]);
    assert_eq!(replay.bank.len(), 1);
    assert_eq!(
        replay.calls[0]
            .inputs
            .iter()
            .map(|x| (x.pc(), x.payload_after_head()))
            .collect::<Vec<_>>(),
        vec![(0, Some(1)), (2, Some(2))]
    );
    let Operand::Payload { head, depth, value } = replay.calls[1].inputs[0].operand() else {
        panic!("payload")
    };
    assert_eq!((*head, *depth, value.as_str()), (2, 2, "same"));
    let Seed::Payload(value) = replay.bank.seed(0).unwrap() else {
        panic!("payload")
    };
    let value = value.clone();
    while let Some(mut run) = replay.calls.pop() {
        start_cleanup(&mut target, &mut run.owner, run.id, true);
        for _ in 0..run.inputs.len() {
            let Dispatch::Payload(done) = run.owner.dispatch(0).unwrap().unwrap() else {
                panic!("typed inverse")
            };
            assert!(done.report.result.is_ok());
        }
        assert!(run.owner.release(&mut target, run.id).0.is_ok());
    }
    let restored = value.capture().unwrap();
    assert_eq!(
        (restored.head(), restored.depth(), restored.revision()),
        (0, 0, 6)
    );
    assert_eq!(restored.value().as_str(), "old");
}
