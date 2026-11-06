use super::test_support::*;
use super::*;
use cordis_kernel::cleanup_queue::completion::CleanupPolicy;
use cordis_kernel::reversible_value::managed::interleaving::history::lifecycle::callbacks::HostAction;
use cordis_kernel::Phase;

#[test]
fn foreign_control_cannot_observe_begin_or_clear_failure_with_reused_numbers() {
    let (a, aid) = world::<String>();
    let (mut b, bid) = world::<String>();
    assert_eq!((a.domain(), aid), (b.domain(), bid));
    let mut control = a.poll_control::<Arc<str>>(aid).unwrap();
    assert!(a.owns_poll_control(&control));
    assert!(!b.owns_poll_control(&control));
    assert_eq!(b.decision_with_control(bid, &control, true), None);
    assert_eq!(
        b.observe_decision(bid, &control, || panic!("foreign predicate")),
        None
    );
    assert!(matches!(
        b.begin_controlled_execution::<(), (), (), _>(bid, 7301, &mut control),
        Err(Error::InvalidState)
    ));
    assert_eq!(b.phase(bid), Some(Phase::Inactive));
    let payload: Arc<str> = Arc::from("original setup failure");
    control.record_setup_failure(payload.clone());
    assert!(matches!(
        b.request_restart(&mut control),
        Err(Error::InvalidState)
    ));
    assert!(Arc::ptr_eq(control.failed().unwrap(), &payload));
    // A normal move retains provenance; dropping the origin cannot authorize a
    // replacement Runtime that reuses its domain and first plugin ID.
    let moved = a;
    assert!(moved.owns_poll_control(&control));
    let released = moved.request_restart(&mut control).unwrap().unwrap();
    assert!(Arc::ptr_eq(&released, &payload));
    drop(moved);
    let (replacement, id) = world::<String>();
    assert_eq!(id, aid);
    assert!(!replacement.owns_poll_control(&control));
    assert_eq!(replacement.decision_with_control(id, &control, true), None);
}

#[test]
fn foreign_control_cannot_retry_or_release_an_identically_numbered_episode() {
    let (mut a, aid) = world::<String>();
    let (mut b, bid) = world::<String>();
    let mut ac = a.poll_control::<&'static str>(aid).unwrap();
    let mut bc = b.poll_control::<&'static str>(bid).unwrap();
    let mut ar: Core<String, ()> = activate(&mut a, aid, &mut ac);
    let mut br: Core<String, ()> = activate(&mut b, bid, &mut bc);
    assert!(ac.matches_execution(&br)); // Numeric tickets really collide.
    fail(&mut a, aid, &mut ar, &mut ac, ());
    fail(&mut b, bid, &mut br, &mut bc, ());
    let pending = b.pending_action(bid);
    assert!(matches!(
        b.retry_controlled_execution(bid, &mut br, &mut ac),
        Err(Error::InvalidState)
    ));
    assert_eq!(b.pending_action(bid), pending);
    assert_eq!(ac.cleanup_failure(), Some(&"retained"));
    assert_eq!(bc.cleanup_failure(), Some(&"retained"));
    b.retry_controlled_execution(bid, &mut br, &mut bc).unwrap();
    let (ticket, ()) = br.pop(0).unwrap().unwrap();
    br.complete_result(
        0,
        ticket,
        Ok::<_, &str>(()),
        None,
        CleanupPolicy::RetainFailure,
    )
    .unwrap();
    let pending = b.pending_action(bid);
    assert!(matches!(
        b.release_controlled_execution(bid, &mut br, &mut ac),
        Err(Error::InvalidState)
    ));
    assert_eq!(b.pending_action(bid), pending);
    assert_eq!(b.phase(bid), Some(Phase::Unloading));
    assert!(ac.matches_execution(&ar));
    b.release_controlled_execution(bid, &mut br, &mut bc)
        .unwrap();
    a.retry_controlled_execution(aid, &mut ar, &mut ac).unwrap();
    let (ticket, ()) = ar.pop(0).unwrap().unwrap();
    ar.complete_result(
        0,
        ticket,
        Ok::<_, &str>(()),
        None,
        CleanupPolicy::RetainFailure,
    )
    .unwrap();
    a.release_controlled_execution(aid, &mut ar, &mut ac)
        .unwrap();
    assert_eq!(
        (a.phase(aid), b.phase(bid)),
        (Some(Phase::Inactive), Some(Phase::Inactive))
    );
}

#[test]
fn foreign_control_cannot_certify_or_finish_a_recorded_owner() {
    let (mut a, aid) = world::<Slot<u64, ()>>();
    let (mut b, bid) = world::<Slot<u64, ()>>();
    let mut ac = a.poll_control::<&'static str>(aid).unwrap();
    let mut bc = b.poll_control::<&'static str>(bid).unwrap();
    let mut ar: ManagedCore = activate(&mut a, aid, &mut ac);
    let mut br: ManagedCore = activate(&mut b, bid, &mut bc);
    assert!(ac.matches_execution(&br));
    let scope = br.root_scope().unwrap();
    assert!(b
        .controlled_service_episode_snapshot(bid, &br, &ac)
        .is_none());
    assert!(b
        .scoped_service_episode_snapshot(bid, &br, &ac, &scope)
        .is_none());
    assert!(b
        .scoped_payload_service_episode_snapshot(bid, &br, &ac, &scope)
        .is_none());
    assert!(b
        .controlled_service_episode_snapshot(bid, &br, &bc)
        .is_some());
    assert!(b
        .scoped_service_episode_snapshot(bid, &br, &bc, &scope)
        .is_some());
    assert!(b
        .scoped_payload_service_episode_snapshot(bid, &br, &bc, &scope)
        .is_some());
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
    let mut ar = Managed::new(ar);
    let mut br = Managed::new(br);
    let pending = b.pending_action(bid);
    assert!(matches!(
        b.retry_recorded_controlled(bid, &mut br, &mut ac),
        Err(Error::InvalidState)
    ));
    assert_eq!(b.pending_action(bid), pending);
    assert_eq!(ac.cleanup_failure(), Some(&"retained"));
    b.retry_recorded_controlled(bid, &mut br, &mut bc).unwrap();
    complete_recorded(&mut br);
    let pending = b.pending_action(bid);
    assert!(matches!(
        b.release_recorded_controlled(bid, &mut br, &mut ac),
        Err(Error::InvalidState)
    ));
    assert!(matches!(
        b.release_recorded_controlled_observed(bid, &mut br, &mut ac)
            .0,
        Err(Error::InvalidState)
    ));
    assert_eq!(b.pending_action(bid), pending);
    assert_eq!(b.phase(bid), Some(Phase::Unloading));
    assert!(ac.matches_execution(ar.execution()));
    b.release_recorded_controlled_observed(bid, &mut br, &mut bc)
        .0
        .unwrap();
    a.retry_recorded_controlled(aid, &mut ar, &mut ac).unwrap();
    complete_recorded(&mut ar);
    a.release_recorded_controlled(aid, &mut ar, &mut ac)
        .unwrap();
    assert_eq!(
        (a.phase(aid), b.phase(bid)),
        (Some(Phase::Inactive), Some(Phase::Inactive))
    );
}
