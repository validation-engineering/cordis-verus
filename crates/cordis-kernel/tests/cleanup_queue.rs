use cordis_kernel::cleanup_journal::{RestoreOutcome, RestoreTicket};
use cordis_kernel::cleanup_queue::CleanupQueue;
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};

// Neither Clone nor Debug: real callback payloads need neither trait.
struct Payload {
    value: usize,
    drops: Arc<AtomicUsize>,
}
impl Drop for Payload {
    fn drop(&mut self) {
        self.drops.fetch_add(1, Ordering::SeqCst);
    }
}
fn payload(value: usize, drops: &Arc<AtomicUsize>) -> Box<Payload> {
    Box::new(Payload {
        value,
        drops: drops.clone(),
    })
}

#[test]
fn retained_payload_returns_from_the_same_slot_before_late_and_earlier_work() {
    let drops = Arc::new(AtomicUsize::new(0));
    let mut queue = CleanupQueue::scope(10);
    queue.register(payload(1, &drops));
    queue.register(payload(2, &drops));
    let (first, mut selected) = queue.pop().unwrap().unwrap();
    let address = std::ptr::from_ref(selected.as_ref());
    assert_eq!(selected.value, 2);
    assert!(queue.pop().unwrap().is_none());
    queue.register(payload(3, &drops));
    selected.value = 20; // A factory may retain mutable state between attempts.
    assert!(queue
        .complete(first, RestoreOutcome::Failed, Some(selected))
        .is_ok());
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    assert!(queue.pop().unwrap().is_none());
    let retry = queue.retry().unwrap();
    assert_eq!(retry.token, first.token);
    assert!(retry.attempt > first.attempt);
    assert!(queue
        .complete(retry, RestoreOutcome::Succeeded, None)
        .is_err()); // Not issued yet.
    let (issued, selected) = queue.pop().unwrap().unwrap();
    assert_eq!(issued, retry);
    assert_eq!(std::ptr::from_ref(selected.as_ref()), address);
    assert_eq!(selected.value, 20);
    let wrong = payload(99, &drops);
    let wrong_address = std::ptr::from_ref(wrong.as_ref());
    let rejected = queue
        .complete(first, RestoreOutcome::Failed, Some(wrong))
        .unwrap_err()
        .unwrap();
    assert_eq!(std::ptr::from_ref(rejected.as_ref()), wrong_address);
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    drop(rejected);
    assert!(queue
        .complete(retry, RestoreOutcome::Succeeded, None)
        .is_ok());
    drop(selected);
    for value in [3, 1] {
        let (ticket, selected) = queue.pop().unwrap().unwrap();
        assert_eq!(selected.value, value);
        assert!(queue
            .complete(ticket, RestoreOutcome::Succeeded, None)
            .is_ok());
        drop(selected);
    }
    assert!(queue.is_empty());
    assert_eq!(drops.load(Ordering::SeqCst), 4);
}

#[test]
fn foreign_and_duplicate_completions_return_payloads_without_overwriting_live_work() {
    let drops = Arc::new(AtomicUsize::new(0));
    let mut left = CleanupQueue::scope(20);
    let mut right = CleanupQueue::scope(21);
    left.register(payload(1, &drops));
    right.register(payload(2, &drops));
    let (a, pa) = left.pop().unwrap().unwrap();
    let (b, pb) = right.pop().unwrap().unwrap();
    assert_eq!((a.token, a.attempt), (b.token, b.attempt));
    let rejected = right
        .complete(a, RestoreOutcome::Failed, Some(pa))
        .unwrap_err()
        .unwrap();
    assert_eq!(rejected.value, 1);
    assert!(!right.is_empty());
    assert!(right.pop().unwrap().is_none());
    assert!(right.complete(b, RestoreOutcome::Failed, Some(pb)).is_ok());
    let rejected = right
        .complete(b, RestoreOutcome::Failed, Some(rejected))
        .unwrap_err()
        .unwrap();
    let retry = right.retry().unwrap();
    let (ticket, restored) = right.pop().unwrap().unwrap();
    assert_eq!(ticket, retry);
    assert_eq!(restored.value, 2);
    assert!(right
        .complete(ticket, RestoreOutcome::Succeeded, None)
        .is_ok());
    assert!(left.complete(a, RestoreOutcome::Succeeded, None).is_ok());
    drop((rejected, restored));
    assert_eq!(drops.load(Ordering::SeqCst), 2);
}

#[test]
fn consumed_failure_cannot_issue_an_empty_retry_or_skip_waiting_work() {
    let mut queue = CleanupQueue::scope(30);
    queue.register(1);
    queue.register(2);
    let (ticket, value) = queue.pop().unwrap().unwrap();
    assert_eq!(value, 2);
    assert!(queue.complete(ticket, RestoreOutcome::Failed, None).is_ok());
    assert!(queue.has_failed());
    assert!(!queue.can_retry());
    assert!(queue.retry().is_err());
    assert!(queue.pop().unwrap().is_none());
    assert!(!queue.is_empty());
    assert!(queue
        .complete(ticket, RestoreOutcome::Succeeded, None)
        .is_err());
}

#[test]
fn cancelled_stage_lands_its_real_payload_and_rejected_landing_returns_ownership() {
    let drops = Arc::new(AtomicUsize::new(0));
    let mut queue = CleanupQueue::iterator(40, vec![]);
    assert!(queue.admit(Some(&[])));
    queue.register(payload(1, &drops));
    queue.cancel();
    assert!(queue.pop().unwrap().is_none());
    assert!(queue.land(payload(2, &drops)).is_ok());
    let rejected = queue.land(payload(3, &drops)).unwrap_err();
    assert_eq!(rejected.value, 3);
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    drop(rejected);
    for value in [2, 1] {
        let (ticket, selected) = queue.pop().unwrap().unwrap();
        assert_eq!(selected.value, value);
        assert!(queue
            .complete(ticket, RestoreOutcome::Succeeded, None)
            .is_ok());
        drop(selected);
    }
    assert!(queue.is_empty());
    assert_eq!(drops.load(Ordering::SeqCst), 3);
}

#[test]
fn success_cannot_silently_drop_a_supplied_retry_payload() {
    let drops = Arc::new(AtomicUsize::new(0));
    let mut queue = CleanupQueue::scope(50);
    queue.register(payload(1, &drops));
    let (ticket, selected) = queue.pop().unwrap().unwrap();
    let selected = queue
        .complete(ticket, RestoreOutcome::Succeeded, Some(selected))
        .unwrap_err()
        .unwrap();
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    let foreign = RestoreTicket {
        token: usize::MAX,
        ..ticket
    };
    let selected = queue
        .complete(foreign, RestoreOutcome::Failed, Some(selected))
        .unwrap_err()
        .unwrap();
    assert_eq!(selected.value, 1);
    assert!(!queue.is_empty());
    assert!(queue
        .complete(ticket, RestoreOutcome::Drained, None)
        .is_ok());
    drop(selected);
    assert!(queue.is_empty());
    assert_eq!(drops.load(Ordering::SeqCst), 1);
}
