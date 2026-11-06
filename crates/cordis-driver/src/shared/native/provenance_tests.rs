use super::test_support::*;
use super::*;
use cordis_kernel::execution::ExecutionPhase;
use cordis_kernel::reversible_value::managed::interleaving::history::lifecycle::callbacks::HostAction;
use cordis_kernel::Phase;

#[test]
fn foreign_execution_cannot_consume_root_publish_or_release_with_reused_numbers() {
    let (mut a, aid) = world::<String>();
    let (mut b, bid) = world::<String>();
    let mut ar: Core<String, ()> = a.begin_managed_execution(aid, 7301).unwrap();
    let mut br: Core<String, ()> = b.begin_managed_execution(bid, 7301).unwrap();
    assert!(b.state.matches_execution(bid, &ar)); // Numeric ownership alone collides.
    assert!(!b.owns_execution(bid, &ar));
    assert!(b.episode_snapshot(bid, &ar).is_none());
    let argument = Arc::new("retained argument");
    let rejected = b
        .admit_managed_root(bid, &mut ar, argument.clone())
        .err()
        .unwrap();
    assert!(Arc::ptr_eq(&argument, &rejected));
    let call = a.admit_managed_root(aid, &mut ar, aid).unwrap();
    let reply = a.call_root(aid, call).ok().unwrap();
    ar.complete_root(reply).ok().unwrap().unwrap();
    assert!(matches!(
        b.finish_managed_execution(bid, &mut ar),
        Err(Error::InvalidState)
    ));
    assert_eq!(
        (a.phase(aid), b.phase(bid)),
        (Some(Phase::Loading), Some(Phase::Loading))
    );
    a.finish_managed_execution(aid, &mut ar).unwrap();
    let call = b.admit_managed_root(bid, &mut br, bid).unwrap();
    let reply = b.call_root(bid, call).ok().unwrap();
    br.complete_root(reply).ok().unwrap().unwrap();
    b.finish_managed_execution(bid, &mut br).unwrap();
    assert!(matches!(
        b.withdraw_managed_execution(bid, &mut ar, true),
        Err(Error::InvalidState)
    ));
    assert_eq!(ar.phase(), ExecutionPhase::Active);
    assert!(!b.retired(bid));
    a.withdraw_managed_execution(aid, &mut ar, false).unwrap();
    b.withdraw_managed_execution(bid, &mut br, false).unwrap();
    assert!(matches!(
        b.settle_managed_execution(bid, &ar),
        Err(Error::InvalidState)
    ));
    a.settle_managed_execution(aid, &ar).unwrap();
    b.settle_managed_execution(bid, &br).unwrap();
    a.begin_cleanup(aid).unwrap();
    b.begin_cleanup(bid).unwrap();
    let pending = b.pending_action(bid);
    assert!(matches!(
        b.release_managed_execution(bid, &mut ar),
        Err(Error::InvalidState)
    ));
    assert_eq!(b.pending_action(bid), pending);
    assert_eq!(ar.phase(), ExecutionPhase::Restoring);
    a.release_managed_execution(aid, &mut ar).unwrap();
    b.release_managed_execution(bid, &mut br).unwrap();
    assert_eq!(
        (a.phase(aid), b.phase(bid)),
        (Some(Phase::Inactive), Some(Phase::Inactive))
    );
    let standalone: Core<String, ()> = Execution::new(7301);
    assert!(!b.owns_execution(bid, &standalone));
}

#[test]
fn recorded_foreign_execution_preserves_failure_and_both_ready_release_owners() {
    let (mut a, aid) = world::<Slot<u64, ()>>();
    let (mut b, bid) = world::<Slot<u64, ()>>();
    let mut ac = a.poll_control::<&'static str>(aid).unwrap();
    let mut bc = b.poll_control::<&'static str>(bid).unwrap();
    let mut ar: ManagedCore = activate(&mut a, aid, &mut ac);
    let mut br: ManagedCore = activate(&mut b, bid, &mut bc);
    fail(
        &mut a,
        aid,
        &mut ar,
        &mut ac,
        HostAction::Retryable(()).into_action(),
    );
    fail(
        &mut b,
        bid,
        &mut br,
        &mut bc,
        HostAction::Retryable(()).into_action(),
    );
    let pending = b.pending_action(bid);
    assert!(matches!(
        b.fail_managed_execution(bid, &ar),
        Err(Error::InvalidState)
    ));
    assert!(matches!(
        b.retry_managed_execution(bid, &mut ar),
        Err(Error::InvalidState)
    ));
    assert!(matches!(
        b.retry_controlled_execution(bid, &mut ar, &mut bc),
        Err(Error::InvalidState)
    ));
    assert_eq!(b.pending_action(bid), pending);
    assert!(ar.has_failed());
    assert_eq!(bc.cleanup_failure(), Some(&"retained"));
    let mut ar = Managed::new(ar);
    let mut br = Managed::new(br);
    assert!(matches!(
        b.finish_recorded_execution(bid, &mut ar),
        Err(Error::InvalidState)
    ));
    assert!(matches!(
        b.withdraw_recorded_execution(bid, &mut ar, false),
        Err(Error::InvalidState)
    ));
    assert!(matches!(
        b.retry_recorded_controlled(bid, &mut ar, &mut bc),
        Err(Error::InvalidState)
    ));
    assert_eq!(b.pending_action(bid), pending);
    assert_eq!(bc.cleanup_failure(), Some(&"retained"));
    a.retry_recorded_controlled(aid, &mut ar, &mut ac).unwrap();
    b.retry_recorded_controlled(bid, &mut br, &mut bc).unwrap();
    complete_recorded(&mut ar);
    complete_recorded(&mut br);
    let pending = b.pending_action(bid);
    assert!(matches!(
        b.release_recorded_controlled(bid, &mut ar, &mut bc),
        Err(Error::InvalidState)
    ));
    assert!(matches!(
        b.release_recorded_controlled_observed(bid, &mut ar, &mut bc)
            .0,
        Err(Error::InvalidState)
    ));
    assert_eq!(b.pending_action(bid), pending);
    assert_eq!(ar.execution().phase(), ExecutionPhase::Restoring);
    assert_eq!(
        (a.phase(aid), b.phase(bid)),
        (Some(Phase::Unloading), Some(Phase::Unloading))
    );
    a.release_recorded_controlled(aid, &mut ar, &mut ac)
        .unwrap();
    b.release_recorded_controlled(bid, &mut br, &mut bc)
        .unwrap();
}

#[test]
fn scopes_authenticate_the_live_queue_and_do_not_retain_the_journal() {
    let (mut a, aid) = world::<Slot<u64, ()>>();
    let (mut b, bid) = world::<Slot<u64, ()>>();
    let mut ac = a.poll_control::<()>(aid).unwrap();
    let mut bc = b.poll_control::<()>(bid).unwrap();
    let ar: ManagedCore = activate(&mut a, aid, &mut ac);
    let br: ManagedCore = activate(&mut b, bid, &mut bc);
    let ascope = ar.root_scope().unwrap();
    let bscope = br.root_scope().unwrap();
    assert!(ascope.belongs(&br)); // Even every selector field is identical.
    assert!(!b.owns_setup_scope(bid, &br, &ascope));
    assert!(b.owns_setup_scope(bid, &br, &bscope.clone()));
    assert!(b.service_episode_snapshot(bid, &ar).is_none());
    assert!(b
        .controlled_service_episode_snapshot(bid, &ar, &bc)
        .is_none());
    assert!(b
        .scoped_service_episode_snapshot(bid, &ar, &bc, &ascope)
        .is_none());
    assert!(b
        .scoped_payload_service_episode_snapshot(bid, &ar, &bc, &ascope)
        .is_none());
    assert!(b
        .scoped_service_episode_snapshot(bid, &br, &bc, &ascope)
        .is_none());
    assert!(b
        .scoped_payload_service_episode_snapshot(bid, &br, &bc, &ascope)
        .is_none());
    assert!(b
        .scoped_service_episode_snapshot(bid, &br, &bc, &bscope)
        .is_some());
    assert!(b
        .scoped_payload_service_episode_snapshot(bid, &br, &bc, &bscope)
        .is_some());
    let journal = Arc::downgrade(a.state.execution_domain().runtime_identity());
    drop(ar);
    drop(ac);
    drop(a);
    assert!(journal.upgrade().is_none()); // Retaining the scope retains only its identity.
    let (mut replacement, id) = world::<Slot<u64, ()>>();
    let mut control = replacement.poll_control::<()>(id).unwrap();
    let run: ManagedCore = activate(&mut replacement, id, &mut control);
    assert!(ascope.belongs(&run));
    assert!(!replacement.owns_setup_scope(id, &run, &ascope));
}

#[test]
fn configuration_checkpoints_require_the_actual_journal_not_equal_contents() {
    type Configuration = cordis_kernel::configuration_recorded::Recorded<u64, (), (), (), (), ()>;
    let (a, _) = world::<String>();
    let (b, _) = world::<String>();
    let first: Configuration = a.configuration(7);
    let second: Configuration = b.configuration(7);
    assert_eq!(first.current(), second.current());
    assert!(!b.owns_configuration(&first));
    assert!(b.configuration_snapshot(&first).is_none());
    assert!(a.configuration_snapshot(&first).is_some());
    assert!(b.configuration_snapshot(&second).is_some());
    let journal = a.execution_journal();
    let shared: Configuration = Configuration::new_in(&journal.clone(), 9);
    let moved = a;
    assert!(moved.owns_configuration(&shared));
    assert!(moved.configuration_snapshot(&shared).is_some());
    let standalone: Configuration = Configuration::new(7);
    assert!(moved.configuration_snapshot(&standalone).is_none());
    drop(moved);
    let (replacement, _) = world::<String>();
    assert!(replacement.configuration_snapshot(&first).is_none());
}

type TypedWorld = NativeDriver<
    cordis_kernel::reversible_value::function::Body<
        Callback,
        cordis_kernel::reversible_value::managed::Function<
            cordis_kernel::reversible_value::effect::ScaleAdd,
            u64,
        >,
    >,
    (),
    Slot<u64, ()>,
>;
fn typed_world() -> (TypedWorld, usize) {
    use cordis_kernel::reversible_value::{function::Body, managed::Function};
    let mut world = NativeDriver {
        state: NativeRuntime::new(7300),
    };
    let id = world
        .register_plugin(
            None,
            &BTreeMap::new(),
            Port { key: 1, realm: 0 },
            PluginDefinition::new(
                vec![],
                vec![],
                Body::Managed(Function::new(vec![]).ok().unwrap()),
            ),
            (),
        )
        .ok()
        .unwrap();
    (world, id)
}

#[test]
fn typed_root_rejection_returns_the_owner_without_consuming_admission() {
    use cordis_kernel::reversible_value::{function, managed::root, service_function};
    let (mut a, aid) = typed_world();
    let (mut b, bid) = typed_world();
    let mut ar: ManagedCore = a.begin_managed_execution(aid, 7301).unwrap();
    let br: ManagedCore = b.begin_managed_execution(bid, 7301).unwrap();
    assert!(matches!(
        b.run_managed_root(bid, &mut ar),
        Err(root::AdmissionError::WrongOwner)
    ));
    let (mut ar, rejected) = b.run_recorded_root(bid, ar);
    assert!(matches!(rejected, Err(root::AdmissionError::WrongOwner)));
    assert!(matches!(
        b.run_recorded_value_root(bid, &mut ar),
        Err(function::AdmissionError::WrongOwner)
    ));
    assert!(matches!(
        b.run_recorded_service_root(bid, &mut ar),
        Err(service_function::AdmissionError::WrongOwner)
    ));
    let argument = Arc::new("still owned");
    let rejected = b
        .admit_recorded_root(bid, &mut ar, argument.clone())
        .err()
        .unwrap();
    assert!(Arc::ptr_eq(&rejected, &argument));
    assert!(a.admit_recorded_root(aid, &mut ar, argument).is_ok());
    let (mut br, result) = b.run_recorded_root(bid, br);
    assert!(result.ok().unwrap().result.is_ok());
    b.finish_recorded_execution(bid, &mut br).unwrap();

    // The raw value/service entry points reject before selecting a recipe too.
    type Plain = Core<
        Slot<u64, ()>,
        cordis_kernel::lifecycle_state::registration::shared_child::ChildCleanup<(), ()>,
    >;
    let (mut a, aid) = typed_world();
    let (mut b, bid) = typed_world();
    let mut ar: Plain = a.begin_managed_execution(aid, 7301).unwrap();
    let _br: Plain = b.begin_managed_execution(bid, 7301).unwrap();
    assert!(matches!(
        b.run_value_root(bid, &mut ar),
        Err(function::AdmissionError::WrongOwner)
    ));
    assert!(matches!(
        b.run_service_root(bid, &mut ar),
        Err(service_function::AdmissionError::WrongOwner)
    ));
    assert!(a.admit_managed_root(aid, &mut ar, ()).is_ok());
}
