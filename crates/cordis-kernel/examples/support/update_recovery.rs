//! Production native owners, real stored roots and inverse queues. No replay
//! assumption or expected ghost state is supplied by this ordinary Rust case.
use cordis_kernel::{
    action_ledger::ActionTicket,
    cleanup_groups::payload::Dispatch,
    cleanup_queue::completion::{CleanupDispatch, CleanupPolicy},
    lifecycle_state::{
        native::runtime::NativeRuntime,
        registration::{
            shared_child::{ChildCleanup, ChildDispatch, SharedChild},
            PluginDefinition,
        },
    },
    reversible_value::{
        effect::Instruction,
        function::Body,
        managed::{
            interleaving::history::lifecycle::RecordedExecution, Call, Effect, Function, Owner,
            Slot,
        },
        Branch, Operation, ReversibleValue,
    },
    Port,
};
use std::{collections::BTreeMap, sync::Arc};
type World = NativeRuntime<Body<(), Function<Operation, ()>>, (), Slot<(), ()>>;
type Starting = Owner<ChildDispatch<(), ()>, (), (), (), (), (), ()>;
type Recorded = RecordedExecution<ChildDispatch<(), ()>, (), (), (), (), (), ()>;
fn port(key: u64) -> Port {
    Port { key, realm: 0 }
}
fn body(add: Option<u64>) -> Body<(), Function<Operation, ()>> {
    Body::Managed(
        Function::new(
            add.map(|amount| {
                vec![Call {
                    key: 1,
                    effect: Effect::Kernel(Instruction::Operation(Operation::Add(amount))),
                    branch: Branch {
                        matched: None,
                        unmatched: None,
                    },
                }]
            })
            .unwrap_or_default(),
        )
        .ok()
        .unwrap(),
    )
}
fn register(
    world: &mut World,
    anchor: u64,
    deps: Vec<u64>,
    provisions: Vec<u64>,
    add: Option<u64>,
) -> usize {
    world
        .register(
            None,
            &BTreeMap::new(),
            port(anchor),
            PluginDefinition::new(deps, provisions, body(add)),
            (),
        )
        .ok()
        .unwrap()
}
fn start(world: &mut World, id: usize, work: u64) -> Recorded {
    let owner: Starting = world.begin_managed_execution(id, work).unwrap();
    let (owner, report) = world.run_recorded_root(id, owner);
    assert!(report.unwrap().result.unwrap().succeeded());
    owner
}
fn publish(owner: &mut Recorded, key: u64, value: &ReversibleValue) {
    owner
        .provide(
            port(key),
            Arc::new(Slot::new_reversible(Arc::new(value.clone()), ())),
        )
        .ok()
        .unwrap();
}
fn scalar_restore(owner: &mut Recorded) -> (cordis_kernel::cleanup_journal::RestoreTicket, bool) {
    let Dispatch::Other(CleanupDispatch::Value { ticket, completion }) =
        owner.dispatch(0).unwrap().unwrap()
    else {
        panic!("real scalar inverse")
    };
    (ticket, completion.report.result.is_ok())
}
fn withdraw(world: &mut World, id: usize, owner: &mut Recorded) {
    owner.withdraw(world, id, false).unwrap();
    world
        .settle_managed_execution(id, owner.execution())
        .unwrap();
}
fn release(world: &mut World, id: usize, owner: &mut Recorded) {
    assert!(owner.dispatch(0).unwrap().is_none());
    assert!(owner.release(world, id).0.is_ok());
    assert!(world.kernel().committed(id).is_empty());
}
fn child(
    world: &mut World,
    parent: usize,
    owner: &mut Recorded,
    work: u64,
) -> (SharedChild, usize, Recorded) {
    let (handle, _) = owner.enqueue_native_child(0, ()).unwrap();
    let reply = owner.take_child().unwrap().run(|request| {
        let ChildDispatch::Native(request) = request else {
            panic!("native child")
        };
        let (_, child) = request.into_parts();
        let id = world
            .register_shared_child(
                &child,
                &BTreeMap::new(),
                port(102),
                PluginDefinition::new(vec![1, 2], vec![], body(Some(2))),
                (),
            )
            .result
            .ok()
            .unwrap();
        let mut owner = start(world, id, work);
        owner.finish(world, id).unwrap();
        (id, owner)
    });
    let (id, child_owner) = owner.complete_request(reply).ok().unwrap();
    assert_eq!(world.registration(id).unwrap().parent(), Some(parent));
    assert!(world
        .kernel()
        .committed(id)
        .iter()
        .any(|b| b.provider == parent));
    (handle, id, child_owner)
}
fn consume_child_inverse(world: &mut World, owner: &mut Recorded, child_id: usize) {
    let Dispatch::Other(CleanupDispatch::Host {
        ticket,
        action: ChildCleanup::Native(handle),
    }) = owner.dispatch(0).unwrap().unwrap()
    else {
        panic!("original Child inverse")
    };
    let result = world.retire_shared_child(&handle).result.unwrap();
    assert_eq!(result.unwrap().id(), child_id);
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
    assert!(owner
        .complete_result(
            0,
            ticket,
            Ok::<(), ()>(()),
            None,
            CleanupPolicy::RetainFailure
        )
        .is_err());
}
#[derive(Debug)]
pub struct Report {
    pub initial: ActionTicket,
    pub retry: ActionTicket,
    pub old_child: usize,
    pub new_child: usize,
    pub final_value: u64,
}
pub fn run() -> Report {
    let mut world = World::new_recorded(750_000, 1024);
    let first = ReversibleValue::new_in(&world.execution_journal(), 10);
    let second = ReversibleValue::new_in(&world.execution_journal(), 20);
    let marker = ReversibleValue::new_in(&world.execution_journal(), 0);
    let provider = register(&mut world, 100, vec![], vec![1], None);
    let mut p = start(&mut world, provider, 750_001);
    publish(&mut p, 1, &first);
    p.finish(&mut world, provider).unwrap();
    let consumer = register(&mut world, 101, vec![1], vec![2], Some(1));
    let mut c = start(&mut world, consumer, 750_002);
    publish(&mut c, 2, &marker);
    c.finish(&mut world, consumer).unwrap();
    let (handle, old_child, mut d) = child(&mut world, consumer, &mut c, 750_003);
    assert_eq!(
        (first.snapshot().value(), first.snapshot().depth()),
        (13, 2)
    );
    let interference = first
        .apply(
            Operation::Add(4),
            Branch {
                matched: None,
                unmatched: None,
            },
        )
        .unwrap();
    // The replacement is installed, but its next Begin must await old owners.
    world.replace(provider, body(None)).ok().unwrap();
    withdraw(&mut world, provider, &mut p);
    withdraw(&mut world, consumer, &mut c);
    world.retire_shared_child(&handle).result.unwrap();
    withdraw(&mut world, old_child, &mut d);
    assert!(world.begin_cleanup(provider).is_err());
    assert!(world.begin_cleanup(consumer).is_err());
    let initial = world.begin_cleanup(old_child).unwrap();
    let (failed, success) = scalar_restore(&mut d);
    assert!(!success);
    world
        .fail_managed_execution(old_child, d.execution())
        .unwrap();
    assert!(d.release(&mut world, old_child).0.is_err());
    assert!(world.begin_cleanup(provider).is_err());
    assert!(world.begin_cleanup(consumer).is_err());
    assert!(d
        .complete_result(
            0,
            failed,
            Ok::<(), ()>(()),
            None,
            CleanupPolicy::RetainFailure
        )
        .is_err());
    assert_eq!(
        (first.snapshot().value(), first.snapshot().depth()),
        (17, 3)
    );
    assert!(world
        .begin_managed_execution::<ChildDispatch<(), ()>, (), ()>(provider, 750_004)
        .is_err());
    assert!(interference.inverse.restore().is_ok());
    let retry = d.retry_native(&mut world, old_child).unwrap();
    assert_eq!(initial.generation, retry.generation);
    assert!(retry.action > initial.action);
    assert!(d.retry_native(&mut world, old_child).is_err());
    assert!(d
        .complete_result(
            0,
            failed,
            Ok::<(), ()>(()),
            None,
            CleanupPolicy::RetainFailure
        )
        .is_err());
    let (restored, success) = scalar_restore(&mut d);
    assert!(success);
    assert_eq!(restored.token, failed.token);
    assert!(restored.attempt > failed.attempt);
    assert_eq!(
        (first.snapshot().value(), first.snapshot().depth()),
        (11, 1)
    );
    release(&mut world, old_child, &mut d);
    world.begin_cleanup(consumer).unwrap();
    consume_child_inverse(&mut world, &mut c, old_child);
    assert!(scalar_restore(&mut c).1);
    release(&mut world, consumer, &mut c);
    world.remove(old_child).ok().unwrap();
    assert_eq!(
        (first.snapshot().value(), first.snapshot().depth()),
        (10, 0)
    );
    world.begin_cleanup(provider).unwrap();
    release(&mut world, provider, &mut p);
    // Actual new episodes reuse the registrations; Child gets a fresh identity.
    let mut p = start(&mut world, provider, 750_010);
    publish(&mut p, 1, &second);
    p.finish(&mut world, provider).unwrap();
    let mut c = start(&mut world, consumer, 750_011);
    publish(&mut c, 2, &marker);
    c.finish(&mut world, consumer).unwrap();
    let (handle, new_child, mut d) = child(&mut world, consumer, &mut c, 750_012);
    assert_ne!(new_child, old_child);
    assert_eq!(
        (second.snapshot().value(), second.snapshot().depth()),
        (23, 2)
    );
    // A previous episode's managed reply cannot affect this new owner's queue.
    assert!(d
        .complete_result(
            0,
            failed,
            Ok::<(), ()>(()),
            None,
            CleanupPolicy::RetainFailure
        )
        .is_err());
    world.retire_shared_child(&handle).result.unwrap();
    withdraw(&mut world, new_child, &mut d);
    world.begin_cleanup(new_child).unwrap();
    assert!(scalar_restore(&mut d).1);
    release(&mut world, new_child, &mut d);
    withdraw(&mut world, consumer, &mut c);
    world.begin_cleanup(consumer).unwrap();
    consume_child_inverse(&mut world, &mut c, new_child);
    assert!(scalar_restore(&mut c).1);
    release(&mut world, consumer, &mut c);
    world.remove(new_child).ok().unwrap();
    world.retire(consumer).unwrap();
    world.remove(consumer).ok().unwrap();
    withdraw(&mut world, provider, &mut p);
    world.begin_cleanup(provider).unwrap();
    release(&mut world, provider, &mut p);
    world.retire(provider).unwrap();
    world.remove(provider).ok().unwrap();
    assert_eq!(
        (second.snapshot().value(), second.snapshot().depth()),
        (20, 0)
    );
    Report {
        initial,
        retry,
        old_child,
        new_child,
        final_value: second.snapshot().value(),
    }
}
