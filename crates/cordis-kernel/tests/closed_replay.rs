//! Integration through the same root interpreter and native cleanup protocol.
use cordis_kernel::cleanup_groups::payload::Dispatch;
use cordis_kernel::cleanup_queue::completion::CleanupDispatch;
use cordis_kernel::lifecycle_state::native::runtime::NativeRuntime;
use cordis_kernel::lifecycle_state::registration::PluginDefinition;
use cordis_kernel::reversible_value::closed::{self, objects::Table, Kind, Node, Reference, Value};
use cordis_kernel::reversible_value::effect::Instruction;
use cordis_kernel::reversible_value::function::Body;
use cordis_kernel::reversible_value::managed::replay::{batch, session, Source};
use cordis_kernel::reversible_value::managed::{Call, Effect, Function, Owner, Slot};
use cordis_kernel::reversible_value::{Branch, Operation, ReversibleValue};
use cordis_kernel::Port;
use std::{collections::BTreeMap, sync::Arc};

type World = NativeRuntime<Body<(), Function<Operation, Value>>, (), Slot<Value, ()>>;
type Episode = Owner<(), (), (), (), Value, (), ()>;
type Recorded = batch::ProviderOwner<Value>;
type Replay = closed::replay::Session<(), Operation>;
fn port(key: u64) -> Port {
    Port { key, realm: 0 }
}
fn next(pc: Option<usize>) -> Branch {
    Branch {
        matched: pc,
        unmatched: pc,
    }
}
fn data(n: u64) -> Value {
    Value::new(vec![Node::Unsigned(n)], 0).ok().unwrap()
}
fn refs(r: Reference) -> Value {
    Value::new(vec![Node::Reference(r), Node::Sequence(vec![0, 0])], 1)
        .ok()
        .unwrap()
}
fn mount(
    world: &mut World,
    parent: Option<usize>,
    anchor: u64,
    deps: Vec<u64>,
    provisions: Vec<u64>,
    function: Function<Operation, Value>,
) -> usize {
    world
        .register(
            parent,
            &BTreeMap::new(),
            port(anchor),
            PluginDefinition::new(deps, provisions, Body::Managed(function)),
            (),
        )
        .ok()
        .unwrap()
}
fn function(add: u64, value: Value) -> Function<Operation, Value> {
    Function::new(vec![
        Call {
            key: 1,
            effect: Effect::Kernel(Instruction::Operation(Operation::Add(add))),
            branch: next(Some(1)),
        },
        Call {
            key: 2,
            effect: Effect::Replace(Arc::new(value)),
            branch: next(None),
        },
    ])
    .ok()
    .unwrap()
}
fn fixture(domain: u64) -> (World, Table, Reference, Reference, Arc<Slot<Value, ()>>) {
    let mut world = World::new_recorded(domain, 512);
    let mut table = Table::new(&world.execution_journal());
    let scalar = table.allocate_scalar(5).unwrap();
    let payload = table.allocate_payload(refs(scalar)).unwrap();
    let slot = Arc::new(Slot::new_reversible(
        Arc::new(table.scalar(scalar).unwrap().clone()),
        (),
    ));
    let id = mount(
        &mut world,
        None,
        100,
        vec![],
        vec![1, 2],
        Function::new(Vec::new()).ok().unwrap(),
    );
    let owner: Episode = world.begin_managed_execution(id, domain + 1).unwrap();
    let (mut owner, report) = world.run_recorded_root(id, owner);
    assert!(report.is_ok());
    owner.provide(port(1), slot.clone()).ok().unwrap();
    owner
        .provide(
            port(2),
            Arc::new(Slot::new_opaque(
                table.payload(payload).unwrap().clone(),
                (),
            )),
        )
        .ok()
        .unwrap();
    owner.finish(&mut world, id).unwrap();
    (world, table, scalar, payload, slot)
}
fn capture(
    world: &mut World,
    anchor: u64,
    work: u64,
    body: Function<Operation, Value>,
) -> (Source<Operation, Value>, Recorded, usize) {
    let id = mount(world, None, anchor, vec![1, 2], vec![], body);
    let owner: Episode = world.begin_managed_execution(id, work).unwrap();
    let (mut owner, captured) = world.run_replayable_root(id, owner);
    let captured = captured.unwrap();
    assert!(captured.report.result.unwrap().failure.is_none());
    owner.finish(world, id).unwrap();
    (captured.source, owner, id)
}
fn drain<C>(
    owner:&mut cordis_kernel::reversible_value::managed::interleaving::history::lifecycle::RecordedExecution<C,(),(),(),Value,(),()>,
) {
    loop {
        match owner.dispatch(0).unwrap() {
            None => break,
            Some(Dispatch::Payload(done)) => assert!(done.report.result.is_ok()),
            Some(Dispatch::Other(CleanupDispatch::Value { completion, .. })) => {
                assert!(completion.report.result.is_ok())
            }
            _ => panic!("unexpected cleanup action"),
        }
    }
}
fn source_cleanup(world: &mut World, owner: &mut Recorded, id: usize) {
    owner.withdraw(world, id, false).unwrap();
    world
        .settle_managed_execution(id, owner.execution())
        .unwrap();
    world.begin_cleanup(id).unwrap();
    drain(owner);
    assert!(owner.release(world, id).0.is_ok());
}
fn replay(sources: Vec<Source<Operation, Value>>, table: Table, domain: u64) -> Replay {
    Replay::new(
        World::new_recorded(domain, 512),
        sources,
        table,
        batch::Names {
            anchor: 1000,
            work: domain + 1,
        },
    )
    .ok()
    .unwrap()
}
fn invoke(session: &mut Replay, anchor: u64, work: u64) -> session::Outcome<Operation, Value> {
    let out = session
        .invoke_next(port(anchor), work)
        .ok()
        .unwrap()
        .unwrap();
    assert!(out.finished.as_ref().unwrap().is_ok());
    assert!(out
        .run
        .report
        .as_ref()
        .unwrap()
        .result
        .as_ref()
        .unwrap()
        .failure
        .is_none());
    out
}
fn cleanup(session: &mut Replay, out: &mut session::Outcome<Operation, Value>) {
    session
        .begin_cleanup(out.run.id, &mut out.run.owner, false)
        .unwrap();
    drain(&mut out.run.owner);
    assert!(session
        .release(out.run.id, &mut out.run.owner)
        .unwrap()
        .0
        .is_ok());
}

#[test]
fn mixed_calls_restore_history_and_resume_after_failed_cleanup() {
    let (mut source, table, scalar, payload, _) = fixture(301_000);
    let (a, mut owner_a, id_a) = capture(&mut source, 101, 301_002, function(7, refs(scalar)));
    let (b, mut owner_b, id_b) = capture(&mut source, 102, 301_003, function(3, data(20)));
    source_cleanup(&mut source, &mut owner_b, id_b);
    let (c, mut owner_c, id_c) = capture(&mut source, 103, 301_004, function(5, refs(scalar)));
    source_cleanup(&mut source, &mut owner_c, id_c);
    source_cleanup(&mut source, &mut owner_a, id_a);
    let mut session = replay(vec![a, b, c], table, 302_000);
    let value = session
        .objects()
        .target_table()
        .scalar(scalar)
        .unwrap()
        .clone();
    let typed = session
        .objects()
        .target_table()
        .payload(payload)
        .unwrap()
        .clone();
    let mut a = invoke(&mut session, 1101, 302_010);
    let mut b = invoke(&mut session, 1102, 302_011);
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (15, 2)
    );
    let old = typed.capture().unwrap();
    assert_eq!((old.head(), old.depth(), old.revision()), (2, 2, 2));
    let first = session
        .begin_cleanup(a.run.id, &mut a.run.owner, false)
        .unwrap();
    let Dispatch::Payload(failed) = session
        .dispatch_cleanup(&mut a.run.owner, 0)
        .unwrap()
        .unwrap()
        .unwrap()
    else {
        panic!("typed failure")
    };
    assert!(failed.report.result.is_err());
    session.fail_cleanup(a.run.id, &a.run.owner).unwrap();
    assert!(session
        .release(a.run.id, &mut a.run.owner)
        .unwrap()
        .0
        .is_err());
    cleanup(&mut session, &mut b);
    let restored = typed.capture().unwrap();
    assert_eq!(
        (restored.head(), restored.depth(), restored.revision()),
        (1, 1, 3)
    );
    let mut c = invoke(&mut session, 1103, 302_012);
    assert_eq!(value.snapshot().value(), 17);
    assert_eq!(typed.capture().unwrap().revision(), 4);
    cleanup(&mut session, &mut c);
    let retry = session.retry_cleanup(a.run.id, &mut a.run.owner).unwrap();
    assert!(retry.action > first.action);
    let Dispatch::Payload(done) = session
        .dispatch_cleanup(&mut a.run.owner, 0)
        .unwrap()
        .unwrap()
        .unwrap()
    else {
        panic!("typed retry")
    };
    assert!(done.report.result.is_ok());
    assert_eq!(done.ticket.token, failed.ticket.token);
    assert!(done.ticket.attempt > failed.ticket.attempt);
    drain(&mut a.run.owner);
    assert!(session
        .release(a.run.id, &mut a.run.owner)
        .unwrap()
        .0
        .is_ok());
    assert_eq!((value.snapshot().value(), value.snapshot().depth()), (5, 0));
    let restored = typed.capture().unwrap();
    assert_eq!(
        (restored.head(), restored.depth(), restored.revision()),
        (0, 0, 6)
    );
    assert!(session
        .invoke_next(port(1104), 302_013)
        .ok()
        .unwrap()
        .is_none());
}

#[test]
fn dynamic_same_value_replacement_uses_other_allocation_and_retains_old_inverse() {
    let (mut source, mut table, scalar, payload, slot) = fixture(303_000);
    let other = table.allocate_scalar(5).unwrap();
    let (a, mut oa, ia) = capture(&mut source, 101, 303_002, function(7, refs(scalar)));
    slot.reversible()
        .unwrap()
        .replace(Arc::new(table.scalar(other).unwrap().clone()))
        .ok()
        .unwrap();
    let (b, mut ob, ib) = capture(&mut source, 102, 303_003, function(3, refs(other)));
    source_cleanup(&mut source, &mut ob, ib);
    source_cleanup(&mut source, &mut oa, ia);
    let mut session = replay(vec![a, b], table, 304_000);
    let x = session
        .objects()
        .target_table()
        .scalar(scalar)
        .unwrap()
        .clone();
    let y = session
        .objects()
        .target_table()
        .scalar(other)
        .unwrap()
        .clone();
    let typed = session
        .objects()
        .target_table()
        .payload(payload)
        .unwrap()
        .clone();
    let mut a = invoke(&mut session, 1101, 304_010);
    let mut b = session
        .invoke_next_dynamic(port(1102), 304_011, None)
        .ok()
        .unwrap()
        .unwrap();
    assert!(b.finished.as_ref().unwrap().is_ok());
    assert_eq!((x.snapshot().value(), y.snapshot().value()), (12, 8));
    assert!(
        matches!(typed.capture().unwrap().value().node(0),Some(Node::Reference(r)) if *r==other)
    );
    cleanup(&mut session, &mut b);
    assert_eq!((x.snapshot().value(), y.snapshot().value()), (12, 5));
    cleanup(&mut session, &mut a);
    assert_eq!((x.snapshot().value(), y.snapshot().value()), (5, 5));
}

#[test]
fn complete_table_retains_unvisited_live_and_retired_reference_targets() {
    let (mut source, mut table, scalar, _, _) = fixture(305_000);
    let extra = table.allocate_scalar(90).unwrap();
    let retired = table.allocate_payload(data(7)).unwrap();
    table.payload(retired).unwrap().retire().unwrap();
    let (a, _, _) = capture(&mut source, 101, 305_002, function(7, refs(scalar)));
    let session = replay(vec![a], table, 306_000);
    assert_eq!(
        session
            .objects()
            .target_table()
            .scalar(extra)
            .unwrap()
            .snapshot()
            .value(),
        90
    );
    assert!(session
        .objects()
        .target_table()
        .payload(retired)
        .unwrap()
        .capture()
        .is_none());
    assert!(session.accepts(&refs(extra)));
    assert!(session.accepts(&refs(retired)));
    assert!(!session.accepts(&refs(Reference {
        index: extra.index,
        kind: Kind::Payload,
        name: 0
    })));
    assert!(!session.accepts(&refs(Reference {
        index: 9999,
        kind: Kind::Scalar,
        name: 0
    })));
}

#[test]
fn invalid_reference_in_skipped_branch_is_rejected_before_target_registration() {
    let (mut source, table, _, _, _) = fixture(307_000);
    let body = Function::new(vec![
        Call {
            key: 1,
            effect: Effect::Kernel(Instruction::Operation(Operation::Add(1))),
            branch: next(None),
        },
        Call {
            key: 2,
            effect: Effect::Replace(Arc::new(refs(Reference {
                index: 999,
                kind: Kind::Payload,
                name: 0,
            }))),
            branch: next(None),
        },
    ])
    .ok()
    .unwrap();
    let (a, _, _) = capture(&mut source, 101, 307_002, body);
    let failed = Replay::new(
        World::new_recorded(308_000, 512),
        vec![a],
        table,
        batch::Names {
            anchor: 1000,
            work: 308_001,
        },
    );
    assert!(matches!(
        failed,
        Err(closed::replay::InitializationFailure::Data { source: 0, .. })
    ));
}

#[test]
fn closed_graph_checks_unused_nodes_and_transport_preserves_aliases() {
    assert!(Value::new(vec![Node::Sequence(vec![0])], 0).is_err());
    let value = Value::new(
        vec![
            Node::Reference(Reference {
                index: 0,
                kind: Kind::Scalar,
                name: 0,
            }),
            Node::Sequence(vec![0, 0]),
            Node::Reference(Reference {
                index: 2,
                kind: Kind::Scalar,
                name: 0,
            }),
        ],
        1,
    )
    .ok()
    .unwrap();
    let a = Reference {
        index: 0,
        kind: Kind::Scalar,
        name: 0,
    };
    let b = Reference {
        index: 1,
        kind: Kind::Scalar,
        name: 1,
    };
    assert!(!value.check(&[a]));
    assert!(closed::Transport::new(vec![a, b], vec![a], vec![0, 0]).is_none());
    let t = closed::Transport::new(
        vec![a],
        vec![
            Reference {
                index: 0,
                kind: Kind::Payload,
                name: 2,
            },
            b,
        ],
        vec![1],
    )
    .unwrap();
    let moved = t
        .apply(&refs(Reference {
            index: 0,
            kind: Kind::Scalar,
            name: 0,
        }))
        .unwrap();
    assert!(matches!(moved.node(0),Some(Node::Reference(r)) if r.index==1));
    assert!(matches!(moved.node(1),Some(Node::Sequence(s)) if s==&vec![0,0]));
}

#[test]
fn unvisited_object_with_inverse_debt_is_rejected_instead_of_forging_history() {
    let (mut source, mut table, scalar, _, _) = fixture(309_000);
    let other = table.allocate_scalar(5).unwrap();
    let object = table.scalar(other).unwrap().clone();
    let debt = object.apply(Operation::Add(0), next(None)).ok().unwrap();
    let (a, _, _) = capture(&mut source, 101, 309_002, function(7, refs(scalar)));
    let failed = Replay::new(
        World::new_recorded(310_000, 512),
        vec![a],
        table,
        batch::Names {
            anchor: 1000,
            work: 310_001,
        },
    );
    assert!(matches!(
        failed,
        Err(closed::replay::InitializationFailure::References {
            error: closed::objects::Error::History,
            ..
        })
    ));
    debt.inverse.restore().ok().unwrap();
}

#[test]
fn real_publication_cannot_release_early_and_restarts_with_a_fresh_generation() {
    let (mut source, table, scalar, _, _) = fixture(311_000);
    let (a, mut oa, ia) = capture(&mut source, 101, 311_002, function(7, refs(scalar)));
    source_cleanup(&mut source, &mut oa, ia);
    let (b, _, _) = capture(&mut source, 102, 311_003, function(9, refs(scalar)));
    let mut session = replay(vec![a, b], table, 312_000);
    let mut a = invoke(&mut session, 1101, 312_010);
    let position = session
        .providers()
        .iter()
        .position(|p| p.services.iter().any(|s| s.port == port(1)))
        .unwrap();
    let mut provider = session.detach_provider(position).unwrap();
    let generation = provider.report.as_ref().unwrap().origin.generation;
    assert!(session
        .begin_cleanup(provider.id, &mut provider.owner, false)
        .is_err());
    assert!(session
        .release(provider.id, &mut provider.owner)
        .unwrap()
        .0
        .is_err());
    assert!(session
        .republish(provider.id, provider.plan, 312_011)
        .is_err());
    cleanup(&mut session, &mut a);
    session
        .resume_cleanup(provider.id, &provider.owner)
        .unwrap();
    assert!(session
        .release(provider.id, &mut provider.owner)
        .unwrap()
        .0
        .is_ok());
    session
        .republish(provider.id, provider.plan, 312_012)
        .ok()
        .unwrap();
    let current = session
        .providers()
        .iter()
        .find(|p| p.id == provider.id)
        .unwrap();
    assert!(current.report.as_ref().unwrap().origin.generation > generation);
    let mut b = invoke(&mut session, 1102, 312_013);
    assert_eq!(
        session
            .objects()
            .target_table()
            .scalar(scalar)
            .unwrap()
            .snapshot()
            .value(),
        14
    );
    cleanup(&mut session, &mut b);
}

#[test]
fn real_shared_child_request_retirement_and_cleanup_use_the_parent_inverse() {
    use cordis_kernel::cleanup_queue::completion::CleanupPolicy;
    use cordis_kernel::lifecycle_state::registration::shared_child::{ChildCleanup, ChildDispatch};
    let (mut source, table, scalar, _, _) = fixture(313_000);
    let parent_id = mount(
        &mut source,
        None,
        101,
        vec![1, 2],
        vec![],
        function(7, refs(scalar)),
    );
    let owner: Owner<ChildDispatch<(), ()>, (), (), (), Value, (), ()> =
        source.begin_managed_execution(parent_id, 313_002).unwrap();
    let (mut source_parent, captured) = source.run_replayable_root(parent_id, owner);
    let a = captured.unwrap().source;
    source_parent.finish(&mut source, parent_id).unwrap();
    let (source_child, _) = source_parent.enqueue_native_child(0, ()).ok().unwrap();
    let child_id = source
        .register_shared_child(
            &source_child,
            &BTreeMap::new(),
            port(102),
            PluginDefinition::new(vec![1, 2], vec![], Body::Managed(function(3, refs(scalar)))),
            (),
        )
        .result
        .ok()
        .unwrap();
    let owner: Episode = source.begin_managed_execution(child_id, 313_003).unwrap();
    let (mut source_owner, captured) = source.run_replayable_root(child_id, owner);
    source_owner.finish(&mut source, child_id).unwrap();
    let b = captured.unwrap().source;
    let mut session = replay(vec![a, b], table, 314_000);
    let mut parent = invoke(&mut session, 1101, 314_010);
    let (_handle, child_token) = parent.run.owner.enqueue_native_child(0, ()).ok().unwrap();
    let reply = parent.run.owner.take_child().unwrap().run(|request| {
        let ChildDispatch::Native(request) = request else {
            panic!("real native Child request")
        };
        let (_, child) = request.into_parts();
        session
            .invoke_next_shared(port(1102), 314_011, &child)
            .ok()
            .unwrap()
            .unwrap()
    });
    let mut child = parent.run.owner.complete_request(reply).ok().unwrap();
    assert!(child.finished.as_ref().unwrap().is_ok());
    // Ownership does not invent a service dependency. The real Child inverse
    // requests retirement; the assigned episode still has its own cleanup.
    let initial = session
        .begin_cleanup(parent.run.id, &mut parent.run.owner, false)
        .unwrap();
    let Dispatch::Other(CleanupDispatch::Host { ticket, action }) =
        parent.run.owner.dispatch(0).unwrap().unwrap()
    else {
        panic!("paired Child inverse")
    };
    assert_eq!(ticket.token, child_token);
    let ChildCleanup::Native(inverse) = action else {
        panic!("native Child inverse")
    };
    assert_eq!(
        session
            .retire_child(&inverse)
            .0
            .result
            .unwrap()
            .unwrap()
            .id(),
        child.run.id
    );
    parent
        .run
        .owner
        .complete_result(
            0,
            ticket,
            Ok::<(), ()>(()),
            None,
            CleanupPolicy::RetainFailure,
        )
        .ok()
        .unwrap();
    let Dispatch::Payload(blocked) = parent.run.owner.dispatch(0).unwrap().unwrap() else {
        panic!("Child still owns a later payload write")
    };
    assert!(blocked.report.result.is_err());
    session
        .fail_cleanup(parent.run.id, &parent.run.owner)
        .unwrap();
    assert!(session
        .release(parent.run.id, &mut parent.run.owner)
        .unwrap()
        .0
        .is_err());
    cleanup(&mut session, &mut child);
    assert!(
        session
            .retry_cleanup(parent.run.id, &mut parent.run.owner)
            .unwrap()
            .action
            > initial.action
    );
    drain(&mut parent.run.owner);
    assert!(session
        .release(parent.run.id, &mut parent.run.owner)
        .unwrap()
        .0
        .is_ok());
    assert_eq!(
        session
            .objects()
            .target_table()
            .scalar(scalar)
            .unwrap()
            .snapshot()
            .value(),
        5
    );
}

#[test]
fn object_outside_the_closed_table_is_rejected_even_with_valid_data() {
    let (mut source, table, scalar, _, slot) = fixture(315_000);
    let outside = ReversibleValue::new_in(&source.execution_journal(), 5);
    slot.reversible()
        .unwrap()
        .replace(Arc::new(outside))
        .ok()
        .unwrap();
    let (a, _, _) = capture(&mut source, 101, 315_002, function(7, refs(scalar)));
    let failed = Replay::new(
        World::new_recorded(316_000, 512),
        vec![a],
        table,
        batch::Names {
            anchor: 1000,
            work: 316_001,
        },
    );
    assert!(matches!(
        failed,
        Err(closed::replay::InitializationFailure::Data { source: 0, .. })
    ));
}

#[test]
fn unvisited_declared_payload_is_published_with_a_real_cleanup_owner() {
    let (mut source, table, scalar, payload, _) = fixture(321_000);
    let body = Function::new(vec![Call {
        key: 1,
        effect: Effect::Kernel(Instruction::Operation(Operation::Add(4))),
        branch: next(None),
    }])
    .ok()
    .unwrap();
    let (call, _, _) = capture(&mut source, 101, 321_002, body);
    let environment = call.declared_environment().unwrap();
    assert_eq!(environment.observations().len(), 2);
    assert_eq!(call.inputs().len(), 1);
    let mut target = replay(vec![call], table, 322_000);
    assert_eq!(target.providers().len(), 1);
    assert_eq!(target.providers()[0].services.len(), 2);
    assert!(target.providers()[0]
        .services
        .iter()
        .any(|s| s.port == port(2)));
    let mut call = invoke(&mut target, 1101, 322_010);
    assert_eq!(
        target
            .objects()
            .target_table()
            .scalar(scalar)
            .unwrap()
            .snapshot()
            .value(),
        9
    );
    assert_eq!(
        target
            .objects()
            .target_table()
            .payload(payload)
            .unwrap()
            .capture()
            .unwrap()
            .revision(),
        0
    );
    let mut provider = target.detach_provider(0).unwrap();
    assert!(target
        .begin_cleanup(provider.id, &mut provider.owner, false)
        .is_err());
    cleanup(&mut target, &mut call);
    target.resume_cleanup(provider.id, &provider.owner).unwrap();
    drain(&mut provider.owner);
    assert!(target
        .release(provider.id, &mut provider.owner)
        .unwrap()
        .0
        .is_ok());
}

#[test]
fn a_skipped_instruction_does_not_lock_its_retired_payload() {
    let (mut source, table, scalar, payload, _) = fixture(323_000);
    table.payload(payload).unwrap().retire().unwrap();
    let body = Function::new(vec![
        Call {
            key: 1,
            effect: Effect::Kernel(Instruction::Operation(Operation::Add(4))),
            branch: next(None),
        },
        Call {
            key: 2,
            effect: Effect::Replace(Arc::new(refs(scalar))),
            branch: next(None),
        },
    ])
    .ok()
    .unwrap();
    let (call, _, _) = capture(&mut source, 101, 323_002, body);
    assert!(call.visits(0));
    assert!(!call.visits(1));
    let mut target = replay(vec![call], table, 324_000);
    let mut call = invoke(&mut target, 1101, 324_010);
    assert!(target
        .objects()
        .target_table()
        .payload(payload)
        .unwrap()
        .capture()
        .is_none());
    assert_eq!(
        target
            .objects()
            .target_table()
            .scalar(scalar)
            .unwrap()
            .snapshot()
            .value(),
        9
    );
    cleanup(&mut target, &mut call);
}

#[test]
fn independent_service_slots_keep_shared_objects_without_merging_replacements() {
    let mut source = World::new_recorded(325_000, 512);
    let mut table = Table::new(&source.execution_journal());
    let x = table.allocate_scalar(10).unwrap();
    let y = table.allocate_scalar(10).unwrap();
    let left = Arc::new(Slot::new_reversible(
        Arc::new(table.scalar(x).unwrap().clone()),
        (),
    ));
    let right = Arc::new(Slot::new_reversible(
        Arc::new(table.scalar(x).unwrap().clone()),
        (),
    ));
    let id = mount(
        &mut source,
        None,
        100,
        vec![],
        vec![1, 3],
        Function::new(Vec::new()).ok().unwrap(),
    );
    let owner: Episode = source.begin_managed_execution(id, 325_001).unwrap();
    let (mut owner, _) = source.run_recorded_root(id, owner);
    owner.provide(port(1), left.clone()).ok().unwrap();
    owner.provide(port(3), right.clone()).ok().unwrap();
    owner.finish(&mut source, id).unwrap();
    let body = || {
        Function::new(vec![
            Call {
                key: 1,
                effect: Effect::Kernel(Instruction::Operation(Operation::Add(2))),
                branch: next(Some(1)),
            },
            Call {
                key: 3,
                effect: Effect::Kernel(Instruction::Operation(Operation::Add(3))),
                branch: next(None),
            },
        ])
        .ok()
        .unwrap()
    };
    let id_a = mount(&mut source, None, 101, vec![1, 3], vec![], body());
    let a: Episode = source.begin_managed_execution(id_a, 325_002).unwrap();
    let (mut oa, a) = source.run_replayable_root(id_a, a);
    let a = a.unwrap();
    oa.finish(&mut source, id_a).unwrap();
    left.reversible()
        .unwrap()
        .replace(Arc::new(table.scalar(y).unwrap().clone()))
        .ok()
        .unwrap();
    let id_b = mount(&mut source, None, 102, vec![1, 3], vec![], body());
    let b: Episode = source.begin_managed_execution(id_b, 325_003).unwrap();
    let (mut ob, b) = source.run_replayable_root(id_b, b);
    let b = b.unwrap();
    ob.finish(&mut source, id_b).unwrap();
    source_cleanup(&mut source, &mut ob, id_b);
    source_cleanup(&mut source, &mut oa, id_a);
    let mut session = replay(vec![a.source, b.source], table, 326_000);
    let target_x = session.objects().target_table().scalar(x).unwrap().clone();
    let target_y = session.objects().target_table().scalar(y).unwrap().clone();
    let mut a = invoke(&mut session, 1101, 326_010);
    assert_eq!(
        (target_x.snapshot().value(), target_x.snapshot().depth()),
        (15, 2)
    );
    let mut b = invoke(&mut session, 1102, 326_011);
    assert_eq!(
        (target_x.snapshot().value(), target_y.snapshot().value()),
        (18, 12)
    );
    let p = session
        .providers()
        .iter()
        .flat_map(|p| p.services.iter())
        .find(|p| p.port == port(1))
        .unwrap();
    let q = session
        .providers()
        .iter()
        .flat_map(|p| p.services.iter())
        .find(|p| p.port == port(3))
        .unwrap();
    assert_eq!(p.service.reversible().unwrap().capture().revision(), 1);
    assert_eq!(q.service.reversible().unwrap().capture().revision(), 0);
    cleanup(&mut session, &mut b);
    assert_eq!(
        (target_x.snapshot().value(), target_y.snapshot().value()),
        (15, 10)
    );
    cleanup(&mut session, &mut a);
    assert_eq!(
        (target_x.snapshot().value(), target_y.snapshot().value()),
        (10, 10)
    );
}

#[test]
fn shared_source_slot_keeps_one_target_slot_and_reuses_unchanged_versions() {
    let mut source = World::new_recorded(327_000, 512);
    let mut table = Table::new(&source.execution_journal());
    let object = table.allocate_scalar(10).unwrap();
    let shared = Arc::new(Slot::new_reversible(
        Arc::new(table.scalar(object).unwrap().clone()),
        (),
    ));
    let provider = mount(
        &mut source,
        None,
        100,
        vec![],
        vec![1, 3],
        Function::new(Vec::new()).ok().unwrap(),
    );
    let owner: Episode = source.begin_managed_execution(provider, 327_001).unwrap();
    let (mut owner, _) = source.run_recorded_root(provider, owner);
    owner.provide(port(1), shared.clone()).ok().unwrap();
    owner.provide(port(3), shared).ok().unwrap();
    owner.finish(&mut source, provider).unwrap();
    let mut sources = Vec::new();
    for i in 0..2 {
        let body = Function::new(vec![
            Call {
                key: 1,
                effect: Effect::Kernel(Instruction::Operation(Operation::Add(1))),
                branch: next(Some(1)),
            },
            Call {
                key: 3,
                effect: Effect::Kernel(Instruction::Operation(Operation::Add(1))),
                branch: next(None),
            },
        ])
        .ok()
        .unwrap();
        let id = mount(&mut source, None, 101 + i, vec![1, 3], vec![], body);
        let owner: Episode = source.begin_managed_execution(id, 327_002 + i).unwrap();
        let (mut owner, captured) = source.run_replayable_root(id, owner);
        owner.finish(&mut source, id).unwrap();
        sources.push(captured.unwrap().source);
    }
    let mut session = replay(sources, table, 328_000);
    let mut a = invoke(&mut session, 1101, 328_010);
    let mut b = invoke(&mut session, 1102, 328_011);
    let p = session
        .providers()
        .iter()
        .flat_map(|p| p.services.iter())
        .find(|p| p.port == port(1))
        .unwrap();
    let q = session
        .providers()
        .iter()
        .flat_map(|p| p.services.iter())
        .find(|p| p.port == port(3))
        .unwrap();
    assert!(Arc::ptr_eq(&p.service, &q.service));
    assert_eq!(p.service.reversible().unwrap().capture().revision(), 0);
    cleanup(&mut session, &mut b);
    cleanup(&mut session, &mut a);
    assert_eq!(
        session
            .objects()
            .target_table()
            .scalar(object)
            .unwrap()
            .snapshot()
            .value(),
        10
    );
}

#[test]
fn retained_root_publishes_multiple_services_with_its_single_actual_cleanup_owner() {
    let mut source = World::new_recorded(329_000, 512);
    let mut table = Table::new(&source.execution_journal());
    let scalar = table.allocate_scalar(5).unwrap();
    let payload = table.allocate_payload(refs(scalar)).unwrap();
    let id = mount(
        &mut source,
        None,
        100,
        vec![],
        vec![1, 2],
        Function::new(Vec::new()).ok().unwrap(),
    );
    let mut owner: Episode = source.begin_managed_execution(id, 329_001).unwrap();
    owner
        .provide(
            port(1),
            Arc::new(Slot::new_reversible(
                Arc::new(table.scalar(scalar).unwrap().clone()),
                (),
            )),
        )
        .ok()
        .unwrap();
    owner
        .provide(
            port(2),
            Arc::new(Slot::new_opaque(
                table.payload(payload).unwrap().clone(),
                (),
            )),
        )
        .ok()
        .unwrap();
    let (mut owner, provided) = source.run_replayable_root(id, owner);
    let provided = provided.unwrap();
    owner.finish(&mut source, id).unwrap();
    let (consumer, _, _) = capture(&mut source, 101, 329_002, function(7, refs(scalar)));
    let mut session = replay(vec![provided.source, consumer], table, 330_000);
    assert!(session.providers().is_empty());
    assert!(session.additional_providers().is_empty());
    let mut provider = invoke(&mut session, 1101, 330_010);
    let a = provider.run.owner.read(port(1)).unwrap();
    let b = provider.run.owner.read(port(2)).unwrap();
    assert_eq!(a.0, provider.run.id);
    assert_eq!(b.0, provider.run.id);
    let mut consumer = invoke(&mut session, 1102, 330_011);
    assert_eq!(
        session
            .objects()
            .target_table()
            .scalar(scalar)
            .unwrap()
            .snapshot()
            .value(),
        12
    );
    assert!(session
        .begin_cleanup(provider.run.id, &mut provider.run.owner, false)
        .is_err());
    assert!(session
        .release(provider.run.id, &mut provider.run.owner)
        .unwrap()
        .0
        .is_err());
    cleanup(&mut session, &mut consumer);
    session
        .resume_cleanup(provider.run.id, &provider.run.owner)
        .unwrap();
    assert!(session
        .release(provider.run.id, &mut provider.run.owner)
        .unwrap()
        .0
        .is_ok());
    assert_eq!(
        session
            .objects()
            .target_table()
            .scalar(scalar)
            .unwrap()
            .snapshot()
            .value(),
        5
    );
}

#[test]
fn own_unvisited_service_is_admitted_and_published_from_the_complete_object_table() {
    let mut source = World::new_recorded(331_000, 512);
    let mut table = Table::new(&source.execution_journal());
    let object = table.allocate_scalar(55).unwrap();
    let id = mount(
        &mut source,
        None,
        100,
        vec![],
        vec![7],
        Function::new(Vec::new()).ok().unwrap(),
    );
    let mut owner: Episode = source.begin_managed_execution(id, 331_001).unwrap();
    owner
        .provide(
            port(7),
            Arc::new(Slot::new_reversible(
                Arc::new(table.scalar(object).unwrap().clone()),
                (),
            )),
        )
        .ok()
        .unwrap();
    let (mut owner, captured) = source.run_replayable_root(id, owner);
    let captured = captured.unwrap();
    owner.finish(&mut source, id).unwrap();
    let mut session = replay(vec![captured.source], table, 332_000);
    let mut provider = invoke(&mut session, 1101, 332_010);
    let (_, slot) = provider.run.owner.read(port(7)).unwrap();
    assert_eq!(
        slot.reversible()
            .unwrap()
            .capture()
            .value()
            .snapshot()
            .value(),
        55
    );
    assert!(session.additional_providers().is_empty());
    cleanup(&mut session, &mut provider);
}

#[test]
fn references_reject_foreign_tables_with_the_same_index_and_kind() {
    let a = World::new_recorded(335_000, 512);
    let b = World::new_recorded(336_000, 512);
    let mut left = Table::new(&a.execution_journal());
    let mut right = Table::new(&b.execution_journal());
    let x = left.allocate_scalar(7).unwrap();
    let y = right.allocate_scalar(7).unwrap();
    assert_eq!(x.index, y.index);
    assert_eq!(x.kind, y.kind);
    assert_ne!(x.name, y.name);
    assert!(right.scalar(x).is_none());
    assert!(!refs(x).check(&right.reference_list()));
    assert!(matches!(
        right.allocate_payload(refs(x)),
        Err(closed::objects::Error::Reference)
    ));
    let transport =
        closed::Transport::new(left.reference_list(), right.reference_list(), vec![0]).unwrap();
    let moved = transport.apply(&refs(x)).unwrap();
    assert!(moved.check(&right.reference_list()));
    assert!(matches!(moved.node(0),Some(Node::Reference(r)) if *r==y));
}

#[test]
fn unvisited_service_slots_preserve_independent_and_shared_aliases() {
    let (mut source, table, scalar, _, shared) = fixture(337_000);
    let independent = Arc::new(Slot::new_reversible(
        Arc::new(table.scalar(scalar).unwrap().clone()),
        (),
    ));
    let provider = mount(
        &mut source,
        None,
        105,
        vec![],
        vec![3, 4, 5],
        Function::new(Vec::new()).ok().unwrap(),
    );
    let owner: Episode = source.begin_managed_execution(provider, 337_002).unwrap();
    let (mut owner, _) = source.run_recorded_root(provider, owner);
    owner.provide(port(3), shared).ok().unwrap();
    owner.provide(port(4), independent.clone()).ok().unwrap();
    owner.provide(port(5), independent).ok().unwrap();
    owner.finish(&mut source, provider).unwrap();
    let id = mount(
        &mut source,
        None,
        101,
        vec![1, 2, 3, 4, 5],
        vec![],
        function(1, refs(scalar)),
    );
    let owner: Episode = source.begin_managed_execution(id, 337_003).unwrap();
    let (mut owner, call) = source.run_replayable_root(id, owner);
    let call = call.unwrap();
    owner.finish(&mut source, id).unwrap();
    let mut target = replay(vec![call.source], table, 338_000);
    let one = target
        .providers()
        .iter()
        .flat_map(|p| p.services.iter())
        .find(|p| p.port == port(1))
        .unwrap()
        .service
        .clone();
    let three = target
        .providers()
        .iter()
        .flat_map(|p| p.services.iter())
        .find(|p| p.port == port(3))
        .unwrap()
        .service
        .clone();
    let four = target
        .providers()
        .iter()
        .flat_map(|p| p.services.iter())
        .find(|p| p.port == port(4))
        .unwrap()
        .service
        .clone();
    let five = target
        .providers()
        .iter()
        .flat_map(|p| p.services.iter())
        .find(|p| p.port == port(5))
        .unwrap()
        .service
        .clone();
    assert!(Arc::ptr_eq(&one, &three));
    assert!(Arc::ptr_eq(&four, &five));
    assert!(!Arc::ptr_eq(&one, &four));
    let mut call = invoke(&mut target, 1101, 338_010);
    assert_eq!(
        three
            .reversible()
            .unwrap()
            .capture()
            .observe_value()
            .value(),
        6
    );
    assert_eq!(
        four.reversible().unwrap().capture().observe_value().value(),
        6
    );
    cleanup(&mut target, &mut call);
}

#[test]
fn retiring_a_previously_used_payload_does_not_block_an_unrelated_later_call() {
    let (mut source, table, scalar, payload, _) = fixture(339_000);
    let (a, mut owner_a, id_a) = capture(&mut source, 101, 339_002, function(2, refs(scalar)));
    source_cleanup(&mut source, &mut owner_a, id_a);
    table.payload(payload).unwrap().retire().unwrap();
    let body = Function::new(vec![Call {
        key: 1,
        effect: Effect::Kernel(Instruction::Operation(Operation::Add(4))),
        branch: next(None),
    }])
    .ok()
    .unwrap();
    let (b, _, _) = capture(&mut source, 102, 339_003, body);
    let mut target = replay(vec![a, b], table, 340_000);
    let mut first = invoke(&mut target, 1101, 340_010);
    cleanup(&mut target, &mut first);
    target
        .objects()
        .target_table()
        .payload(payload)
        .unwrap()
        .retire()
        .unwrap();
    let mut second = invoke(&mut target, 1102, 340_011);
    assert!(target
        .objects()
        .target_table()
        .payload(payload)
        .unwrap()
        .capture()
        .is_none());
    assert!(target.accepts(&refs(payload)));
    assert_eq!(
        target
            .objects()
            .target_table()
            .scalar(scalar)
            .unwrap()
            .snapshot()
            .value(),
        9
    );
    cleanup(&mut target, &mut second);
}

#[test]
fn post_root_provides_are_recorded_at_real_finish_and_replayed_in_the_same_phase() {
    let mut source = World::new_recorded(341_000, 512);
    let mut table = Table::new(&source.execution_journal());
    let scalar = table.allocate_scalar(5).unwrap();
    let payload = table.allocate_payload(refs(scalar)).unwrap();
    let id = mount(
        &mut source,
        None,
        100,
        vec![],
        vec![1, 2],
        Function::new(Vec::new()).ok().unwrap(),
    );
    let owner: Episode = source.begin_managed_execution(id, 341_001).unwrap();
    let (mut owner, captured) = source.run_replayable_root(id, owner);
    let mut captured = captured.unwrap();
    assert!(captured
        .source
        .owned_observations()
        .unwrap()
        .observations()
        .iter()
        .all(|e| e.result.is_err()));
    assert!(captured.source.finish(&mut source, &mut owner).is_err());
    assert!(captured.source.published_observations().is_none());
    owner
        .provide(
            port(1),
            Arc::new(Slot::new_reversible(
                Arc::new(table.scalar(scalar).unwrap().clone()),
                (),
            )),
        )
        .ok()
        .unwrap();
    owner
        .provide(
            port(2),
            Arc::new(Slot::new_opaque(
                table.payload(payload).unwrap().clone(),
                (),
            )),
        )
        .ok()
        .unwrap();
    captured.source.finish(&mut source, &mut owner).unwrap();
    assert!(captured
        .source
        .published_observations()
        .unwrap()
        .observations()
        .iter()
        .all(|e| e.result.is_ok()));
    let (consumer, _, _) = capture(&mut source, 101, 341_002, function(7, refs(scalar)));
    let mut target = replay(vec![captured.source, consumer], table, 342_000);
    assert!(target.providers().is_empty());
    let mut provider = invoke(&mut target, 1101, 342_010);
    assert_eq!(provider.provided, 2);
    assert_eq!(provider.run.owner.read(port(1)).unwrap().0, provider.run.id);
    assert_eq!(provider.run.owner.read(port(2)).unwrap().0, provider.run.id);
    let mut consumer = invoke(&mut target, 1102, 342_011);
    assert!(target
        .begin_cleanup(provider.run.id, &mut provider.run.owner, false)
        .is_err());
    cleanup(&mut target, &mut consumer);
    target
        .resume_cleanup(provider.run.id, &provider.run.owner)
        .unwrap();
    drain(&mut provider.run.owner);
    assert!(target
        .release(provider.run.id, &mut provider.run.owner)
        .unwrap()
        .0
        .is_ok());
}

#[test]
fn actual_provider_generations_reuse_one_target_registration_and_all_service_names() {
    let mut source = World::new_recorded(343_000, 512);
    let mut table = Table::new(&source.execution_journal());
    let x = table.allocate_scalar(5).unwrap();
    let y = table.allocate_scalar(10).unwrap();
    let payload = table.allocate_payload(refs(x)).unwrap();
    let provider_id = mount(
        &mut source,
        None,
        100,
        vec![],
        vec![1, 2],
        Function::new(Vec::new()).ok().unwrap(),
    );
    let owner: Episode = source
        .begin_managed_execution(provider_id, 343_001)
        .unwrap();
    let (mut owner, report) = source.run_recorded_root(provider_id, owner);
    assert!(report.is_ok());
    owner
        .provide(
            port(1),
            Arc::new(Slot::new_reversible(
                Arc::new(table.scalar(x).unwrap().clone()),
                (),
            )),
        )
        .ok()
        .unwrap();
    owner
        .provide(
            port(2),
            Arc::new(Slot::new_opaque(
                table.payload(payload).unwrap().clone(),
                (),
            )),
        )
        .ok()
        .unwrap();
    owner.finish(&mut source, provider_id).unwrap();
    let (a, mut owner_a, id_a) = capture(&mut source, 101, 343_002, function(7, refs(x)));
    source_cleanup(&mut source, &mut owner_a, id_a);
    source_cleanup(&mut source, &mut owner, provider_id);
    let owner: Episode = source
        .begin_managed_execution(provider_id, 343_003)
        .unwrap();
    let (mut owner, report) = source.run_recorded_root(provider_id, owner);
    assert!(report.is_ok());
    owner
        .provide(
            port(1),
            Arc::new(Slot::new_reversible(
                Arc::new(table.scalar(y).unwrap().clone()),
                (),
            )),
        )
        .ok()
        .unwrap();
    owner
        .provide(
            port(2),
            Arc::new(Slot::new_opaque(
                table.payload(payload).unwrap().clone(),
                (),
            )),
        )
        .ok()
        .unwrap();
    owner.finish(&mut source, provider_id).unwrap();
    let (b, _, _) = capture(&mut source, 102, 343_004, function(3, refs(y)));
    let mut target = replay(vec![b, a], table, 344_000); // Actual source positions determine order.
    assert_eq!(target.planned_provider_count(), 2);
    assert_eq!(target.providers().len(), 1);
    let first_origin = target.planned_provider_origin(0).unwrap();
    let second_origin = target.planned_provider_origin(1).unwrap();
    assert_eq!(first_origin.id, second_origin.id);
    assert!(second_origin.generation > first_origin.generation);
    let mut a = invoke(&mut target, 1101, 344_010);
    cleanup(&mut target, &mut a);
    let mut provider = target.detach_provider(0).unwrap();
    assert_eq!(provider.services.len(), 2);
    let generation = provider.report.as_ref().unwrap().origin.generation;
    target
        .begin_cleanup(provider.id, &mut provider.owner, false)
        .unwrap();
    drain(&mut provider.owner);
    assert!(target
        .release(provider.id, &mut provider.owner)
        .unwrap()
        .0
        .is_ok());
    target.republish(provider.id, 1, 344_011).ok().unwrap();
    assert_eq!(target.providers()[0].id, provider.id);
    assert_eq!(target.providers()[0].source_origin, second_origin);
    assert!(
        target.providers()[0]
            .report
            .as_ref()
            .unwrap()
            .origin
            .generation
            > generation
    );
    let mut b = invoke(&mut target, 1102, 344_012);
    assert_eq!(
        target
            .objects()
            .target_table()
            .scalar(x)
            .unwrap()
            .snapshot()
            .value(),
        5
    );
    assert_eq!(
        target
            .objects()
            .target_table()
            .scalar(y)
            .unwrap()
            .snapshot()
            .value(),
        13
    );
    cleanup(&mut target, &mut b);
}

#[test]
fn unvisited_dependency_slot_replacement_follows_chronology_even_with_reversed_sources() {
    let mut source = World::new_recorded(345_000, 512);
    let mut table = Table::new(&source.execution_journal());
    let x = table.allocate_scalar(5).unwrap();
    let y = table.allocate_scalar(10).unwrap();
    let shared = Arc::new(Slot::new_reversible(
        Arc::new(table.scalar(x).unwrap().clone()),
        (),
    ));
    let provider = mount(
        &mut source,
        None,
        100,
        vec![],
        vec![7],
        Function::new(Vec::new()).ok().unwrap(),
    );
    let owner: Episode = source.begin_managed_execution(provider, 345_001).unwrap();
    let (mut owner, _) = source.run_recorded_root(provider, owner);
    owner.provide(port(7), shared.clone()).ok().unwrap();
    owner.finish(&mut source, provider).unwrap();
    let mut sources = Vec::new();
    for i in 0..2 {
        if i == 1 {
            shared
                .reversible()
                .unwrap()
                .replace(Arc::new(table.scalar(y).unwrap().clone()))
                .ok()
                .unwrap();
        }
        let id = mount(
            &mut source,
            None,
            101 + i,
            vec![7],
            vec![],
            Function::new(Vec::new()).ok().unwrap(),
        );
        let owner: Episode = source.begin_managed_execution(id, 345_002 + i).unwrap();
        let (mut owner, captured) = source.run_replayable_root(id, owner);
        owner.finish(&mut source, id).unwrap();
        sources.push(captured.unwrap().source);
    }
    sources.reverse();
    let mut target = replay(sources, table, 346_000);
    let service = target.providers()[0].services[0].service.clone();
    let mut a = invoke(&mut target, 1101, 346_010);
    assert_eq!(
        service
            .reversible()
            .unwrap()
            .capture()
            .observe_value()
            .value(),
        5
    );
    let first = service.reversible().unwrap().capture();
    let mut b = invoke(&mut target, 1102, 346_011);
    let second = service.reversible().unwrap().capture();
    assert_eq!(second.observe_value().value(), 10);
    assert!(second.revision() > first.revision());
    assert!(Arc::ptr_eq(&service, b.run.owner.read(port(7)).unwrap().1));
    cleanup(&mut target, &mut b);
    cleanup(&mut target, &mut a);
}

#[test]
fn own_unvisited_slot_is_synchronized_before_its_actual_finish_publication() {
    let mut source = World::new_recorded(347_000, 512);
    let mut table = Table::new(&source.execution_journal());
    let x = table.allocate_scalar(5).unwrap();
    let y = table.allocate_scalar(15).unwrap();
    let shared = Arc::new(Slot::new_reversible(
        Arc::new(table.scalar(x).unwrap().clone()),
        (),
    ));
    let provider = mount(
        &mut source,
        None,
        100,
        vec![],
        vec![7],
        Function::new(Vec::new()).ok().unwrap(),
    );
    let mut owner: Episode = source.begin_managed_execution(provider, 347_001).unwrap();
    owner.provide(port(7), shared.clone()).ok().unwrap();
    let (mut owner, captured) = source.run_replayable_root(provider, owner);
    let mut captured = captured.unwrap();
    shared
        .reversible()
        .unwrap()
        .replace(Arc::new(table.scalar(y).unwrap().clone()))
        .ok()
        .unwrap();
    captured.source.finish(&mut source, &mut owner).unwrap();
    let mut target = replay(vec![captured.source], table, 348_000);
    let mut provider = invoke(&mut target, 1101, 348_010);
    let (id, service) = provider.run.owner.read(port(7)).unwrap();
    assert_eq!(id, provider.run.id);
    assert_eq!(
        service
            .reversible()
            .unwrap()
            .capture()
            .observe_value()
            .value(),
        15
    );
    assert_eq!(provider.provided, 0);
    cleanup(&mut target, &mut provider);
}

#[test]
fn unvisited_slot_external_replacement_is_rejected_before_begin() {
    let mut source = World::new_recorded(349_000, 512);
    let mut table = Table::new(&source.execution_journal());
    let x = table.allocate_scalar(5).unwrap();
    let y = table.allocate_scalar(5).unwrap();
    let shared = Arc::new(Slot::new_reversible(
        Arc::new(table.scalar(x).unwrap().clone()),
        (),
    ));
    let provider = mount(
        &mut source,
        None,
        100,
        vec![],
        vec![7],
        Function::new(Vec::new()).ok().unwrap(),
    );
    let owner: Episode = source.begin_managed_execution(provider, 349_001).unwrap();
    let (mut owner, _) = source.run_recorded_root(provider, owner);
    owner.provide(port(7), shared).ok().unwrap();
    owner.finish(&mut source, provider).unwrap();
    let id = mount(
        &mut source,
        None,
        101,
        vec![7],
        vec![],
        Function::new(Vec::new()).ok().unwrap(),
    );
    let owner: Episode = source.begin_managed_execution(id, 349_002).unwrap();
    let (mut owner, captured) = source.run_replayable_root(id, owner);
    owner.finish(&mut source, id).unwrap();
    let mut target = replay(vec![captured.unwrap().source], table, 350_000);
    let service = target.providers()[0].services[0].service.clone();
    service
        .reversible()
        .unwrap()
        .replace(Arc::new(
            target.objects().target_table().scalar(y).unwrap().clone(),
        ))
        .ok()
        .unwrap();
    assert!(matches!(
        target.invoke_next(port(1101), 350_010),
        Err(closed::replay::Error::Declarations {
            error: closed::objects::Error::History,
            ..
        })
    ));
    assert_eq!(service.reversible().unwrap().capture().revision(), 1);
}

#[test]
fn repeated_source_episodes_reuse_the_target_fiber_and_change_the_action_generation() {
    let (mut source, table, scalar, _, _) = fixture(351_000);
    let (a, mut owner, id) = capture(&mut source, 101, 351_002, function(7, refs(scalar)));
    source_cleanup(&mut source, &mut owner, id);
    let owner: Episode = source.begin_managed_execution(id, 351_003).unwrap();
    let (mut owner, captured) = source.run_replayable_root(id, owner);
    owner.finish(&mut source, id).unwrap();
    let b = captured.unwrap().source;
    let mut target = replay(vec![a, b], table, 352_000);
    let mut first = invoke(&mut target, 1101, 352_010);
    let id = first.run.id;
    let generation = first.run.report.as_ref().unwrap().origin.generation;
    cleanup(&mut target, &mut first);
    let mut second = invoke(&mut target, 1102, 352_011);
    assert_eq!(second.run.id, id);
    assert!(second.run.report.as_ref().unwrap().origin.generation > generation);
    assert_eq!(
        target
            .objects()
            .target_table()
            .scalar(scalar)
            .unwrap()
            .snapshot()
            .value(),
        12
    );
    cleanup(&mut target, &mut second);
}

#[test]
fn a_source_root_cannot_be_silently_reparented_as_a_target_child() {
    let (mut source, table, scalar, _, _) = fixture(353_000);
    let (a, _, _) = capture(&mut source, 101, 353_002, function(7, refs(scalar)));
    let mut target = replay(vec![a], table, 354_000);
    assert!(matches!(
        target.invoke_next_dynamic(port(1101), 354_010, Some(123)),
        Err(closed::replay::Error::Parent {
            expected: None,
            actual: Some(123),
            ..
        })
    ));
    assert_eq!(
        target
            .objects()
            .target_table()
            .scalar(scalar)
            .unwrap()
            .snapshot()
            .value(),
        5
    );
    let mut root = invoke(&mut target, 1101, 354_011);
    cleanup(&mut target, &mut root);
}
