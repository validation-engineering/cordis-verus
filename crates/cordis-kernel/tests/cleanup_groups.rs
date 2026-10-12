use cordis_kernel::async_completion::await_completion;
use cordis_kernel::cleanup_groups::CleanupGroups;
use cordis_kernel::cleanup_journal::RestoreOutcome;
use cordis_kernel::cleanup_queue::completion::CleanupPolicy;
use std::future::Future;
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};
use std::task::{Context, Poll, Waker};

fn ready<F: Future>(future: F) -> F::Output {
    match Box::pin(future)
        .as_mut()
        .poll(&mut Context::from_waker(Waker::noop()))
    {
        Poll::Ready(out) => out,
        Poll::Pending => panic!("expected ready callback"),
    }
}

#[test]
fn sealing_checks_every_group_and_keeps_late_inverse_and_issued_callback() {
    let mut groups = CleanupGroups::<String>::new(10);
    let id = groups.add_iterator(11, vec![]).unwrap();
    assert!(!groups.can_seal()); // An unstarted iterator still owns its continuation.
    assert!(groups.admit(id, Some(&[])));
    assert!(groups.has_pending());
    groups.cancel(id);
    assert!(!groups.remove(id));
    assert!(!groups.seal()); // The root is empty; the admitted child group is not done.
    let landed = groups
        .land_result::<()>(id, Ok(Some("late inverse".into())))
        .ok()
        .unwrap();
    assert!(!landed.continue_iteration);
    assert!(!groups.has_pending());
    assert!(!groups.seal());
    let (ticket, inverse) = groups.pop(id).unwrap().unwrap();
    assert_eq!(inverse, "late inverse");
    assert!(!groups.remove(id));
    assert!(!groups.seal()); // Moving the callback out did not make its receipt disappear.
    assert!(groups
        .complete(id, ticket, RestoreOutcome::Succeeded, None)
        .is_ok());
    assert!(groups.remove(id));
    assert!(groups.add_iterator(11, vec![]).is_err()); // Never reuse a removed domain.
    assert!(groups.seal());
    assert_eq!(
        groups.register(0, "escaped context".into()).unwrap_err(),
        "escaped context"
    );
    assert!(groups.add_iterator(12, vec![]).is_err());
}

#[test]
fn independent_failures_retry_together_and_reject_wrong_or_old_receipts() {
    let mut groups = CleanupGroups::new(20);
    let id = groups.add_iterator(21, vec![]).unwrap();
    groups.register(0, "root factory").unwrap();
    assert!(groups.admit(id, Some(&[])));
    assert!(groups
        .land_result::<()>(id, Ok(Some("other factory")))
        .is_ok());
    groups.cancel(id);
    let (a, pa) = groups.pop(0).unwrap().unwrap();
    let (b, pb) = groups.pop(id).unwrap().unwrap();
    let completion = ready(await_completion(a, async { Err::<(), _>("root failure") }));
    let (completion, retry) = groups
        .complete_future(id, completion, Some(pa), CleanupPolicy::RetainFailure)
        .err()
        .unwrap();
    let a_report = groups
        .complete_future(0, completion, retry, CleanupPolicy::RetainFailure)
        .ok()
        .unwrap();
    assert_eq!(a_report.outcome, RestoreOutcome::Failed);
    let b_report = groups
        .complete_failure(
            id,
            b,
            "other failure",
            Some(pb),
            CleanupPolicy::RetainFailure,
        )
        .ok()
        .unwrap();
    assert_eq!(b_report.outcome, RestoreOutcome::Failed);
    assert!(groups.has_failed());
    assert!(!groups.seal());
    assert!(groups.can_retry_all());
    assert!(groups.retry_all());
    assert!(!groups.has_failed());
    // Retry selection preserves both actual payloads and does not itself issue them.
    assert!(!groups.seal());
    for (group, previous, expected) in [(id, b, "other factory"), (0, a, "root factory")] {
        let (ticket, payload) = groups.pop(group).unwrap().unwrap();
        assert!(ticket.attempt > previous.attempt);
        assert_eq!(payload, expected);
        assert!(groups
            .complete(group, previous, RestoreOutcome::Succeeded, None)
            .is_err());
        assert!(groups
            .complete(group, ticket, RestoreOutcome::Succeeded, None)
            .is_ok());
        assert!(groups
            .complete(group, ticket, RestoreOutcome::Succeeded, None)
            .is_err());
    }
    assert!(groups.seal());
}

#[test]
fn nonretryable_failure_blocks_all_group_retry_without_changing_other_attempts() {
    let mut groups = CleanupGroups::new(30);
    let id = groups.add_iterator(31, vec![]).unwrap();
    groups.register(0, 1).unwrap();
    assert!(groups.admit(id, Some(&[])));
    assert!(groups.land_result::<()>(id, Ok(Some(2))).is_ok());
    groups.cancel(id);
    let (a, pa) = groups.pop(0).unwrap().unwrap();
    let (b, _) = groups.pop(id).unwrap().unwrap();
    assert!(groups
        .complete_failure(0, a, "retryable", Some(pa), CleanupPolicy::RetainFailure)
        .is_ok());
    assert!(groups
        .complete_failure(
            id,
            b,
            "consumed but retained",
            None,
            CleanupPolicy::RetainFailure
        )
        .is_ok());
    assert!(!groups.can_retry_all());
    assert!(!groups.retry_all());
    assert!(groups.pop(0).unwrap().is_none());
    assert!(!groups.seal());
    let retry = groups.retry(0).unwrap();
    assert_eq!(retry.attempt, a.attempt + 1); // Failed bulk preflight consumed no attempt.
}

#[test]
fn sealing_never_drops_queued_or_executing_user_payloads() {
    struct Payload(Arc<AtomicUsize>);
    impl Drop for Payload {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }
    let drops = Arc::new(AtomicUsize::new(0));
    let mut groups = CleanupGroups::new(40);
    assert!(groups.register(0, Payload(drops.clone())).is_ok());
    assert!(!groups.seal());
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    let (ticket, payload) = groups.pop(0).unwrap().unwrap();
    assert!(!groups.seal());
    let completion = ready(await_completion(ticket, async { Ok::<(), ()>(()) }));
    let report = groups
        .complete_future(0, completion, Some(payload), CleanupPolicy::RetainFailure)
        .ok()
        .unwrap();
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    assert!(groups.seal());
    assert_eq!(drops.load(Ordering::SeqCst), 0); // Discarding a factory belongs to the unlocked caller.
    drop(report.discarded);
    assert_eq!(drops.load(Ordering::SeqCst), 1);
}

#[test]
fn retired_groups_leave_no_historical_slots_and_old_domains_stay_rejected() {
    let mut groups = CleanupGroups::<()>::new(50);
    let mut previous_id = 0;
    for domain in 51..1051 {
        let id = groups.add_iterator(domain, vec![]).unwrap();
        assert!(id > previous_id);
        previous_id = id;
        groups.cancel(id);
        assert!(groups.remove(id));
        assert_eq!(groups.len(), 1); // Only the live root, regardless of historical IDs.
    }
    assert!(groups.add_iterator(51, vec![]).is_err());
    assert!(!groups.contains(previous_id));
    assert!(groups.seal());
    assert!(groups.is_empty());
}
