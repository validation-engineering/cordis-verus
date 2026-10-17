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
    let mut world = World::new(9510);
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
