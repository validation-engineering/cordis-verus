use cordis_kernel::cleanup_groups::CleanupGroups;
use cordis_kernel::cleanup_journal::RestoreOutcome;
use cordis_kernel::setup_work::{RootStatus, SetupWork};
use std::future::Future;
use std::pin::Pin;
use std::sync::{
    atomic::{AtomicBool, AtomicUsize, Ordering},
    Arc,
};
use std::task::{Context, Poll, Waker};

fn poll<F: Future>(future: Pin<&mut F>) -> Poll<F::Output> {
    future.poll(&mut Context::from_waker(Waker::noop()))
}
fn complete_root<C, G>(work: &mut SetupWork<C, G>) {
    let item = work.issue_root(()).ok().unwrap();
    let result = item.run(|()| Ok::<(), String>(()));
    assert!(work.complete_root(result).ok().unwrap().is_ok());
}

#[test]
fn real_root_result_gates_publication_and_failed_setup_still_drains() {
    let mut groups = CleanupGroups::<()>::new(901);
    let mut work = SetupWork::<(), ()>::new(901);
    assert!(!work.seal(&mut groups));
    let argument = Box::new(String::from("actual configuration"));
    let address = (&*argument as *const String) as usize;
    let item = work.issue_root(argument).ok().unwrap();
    assert_eq!(work.root(), RootStatus::Queued);
    assert!(!work.can_finish(&groups, &[]));
    let receipt = item.run(|argument| {
        assert_eq!((&*argument as *const String) as usize, address);
        Err::<(), _>(argument)
    });
    let error = work.complete_root(receipt).ok().unwrap().unwrap_err();
    assert_eq!((&*error as *const String) as usize, address);
    assert!(!work.can_finish(&groups, &[]));
    assert!(work.issue_root(()).is_err());
    assert!(work.seal(&mut groups));
    assert!(work.enqueue_child(()).is_err());
}

#[test]
fn a_started_root_cannot_be_cancelled_and_actual_future_completion_unblocks_it() {
    let mut groups = CleanupGroups::<()>::new(902);
    let mut work = SetupWork::<(), ()>::new(902);
    let item = work.issue_root(Box::new(37)).ok().unwrap();
    let ticket = item.ticket();
    let ready = Arc::new(AtomicBool::new(false));
    let gate = ready.clone();
    let calls = Arc::new(AtomicUsize::new(0));
    let count = calls.clone();
    let pending = item.start(move |argument| {
        count.fetch_add(1, Ordering::SeqCst);
        std::future::poll_fn(move |_| {
            assert_eq!(*argument, 37);
            if gate.load(Ordering::SeqCst) {
                Poll::Ready(Ok::<(), String>(()))
            } else {
                Poll::Pending
            }
        })
    });
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert!(work.start_root(ticket));
    let mut future = Box::pin(pending.complete());
    assert!(poll(future.as_mut()).is_pending());
    work.withdraw();
    assert!(!work.cancel_queued_root(ticket));
    assert!(!work.seal(&mut groups));
    ready.store(true, Ordering::SeqCst);
    let receipt = match poll(future.as_mut()) {
        Poll::Ready(receipt) => receipt,
        _ => unreachable!(),
    };
    assert!(work.complete_root(receipt).ok().unwrap().is_ok());
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert!(work.seal(&mut groups));
}

#[test]
fn withdrawal_can_skip_only_an_unpolled_root_and_abandonment_never_confirms_drain() {
    let mut groups = CleanupGroups::<()>::new(903);
    let mut work = SetupWork::<(), ()>::new(903);
    let item = work.issue_root(()).ok().unwrap();
    let ticket = item.ticket();
    assert!(!work.cancel_queued_root(ticket));
    work.withdraw();
    assert!(work.cancel_queued_root(ticket));
    assert!(work
        .complete_root(item.run(|()| Ok::<(), String>(())))
        .is_err());
    assert!(work.seal(&mut groups));

    let mut groups = CleanupGroups::<()>::new(904);
    let mut work = SetupWork::<(), ()>::new(904);
    let item = work
        .issue_root(Box::new(String::from("abandoned argument")))
        .ok()
        .unwrap();
    let ticket = item.ticket();
    assert!(work.start_root(ticket));
    drop(item);
    work.abandon_root();
    assert_eq!(work.root(), RootStatus::Abandoned);
    assert!(!work.is_idle());
    assert!(!work.seal(&mut groups));
    assert!(work.fail_root(ticket, "late invented failure").is_err());
}

#[test]
fn issued_requests_remain_blocking_until_their_own_actual_call_returns() {
    let mut groups = CleanupGroups::<()>::new(905);
    let mut work = SetupWork::<Box<String>, u64>::new(905);
    complete_root(&mut work);
    assert!(work.enqueue_child(Box::new("child-a".into())).is_ok());
    assert!(work.enqueue_child(Box::new("child-b".into())).is_ok());
    assert!(work.enqueue_group(79).is_ok());
    let a = work.take_child().unwrap();
    let b = work.take_child().unwrap();
    let group = work.take_group().unwrap();
    assert_eq!(work.child_count(), 0);
    assert_eq!(work.group_count(), 0);
    assert_eq!(work.pending_count(), 3);
    assert!(!work.is_idle());
    assert!(!work.seal(&mut groups));
    let b = b.run(|value| {
        assert_eq!(&**value, "child-b");
        value
    });
    let mut other = SetupWork::<(), ()>::new(906);
    complete_root(&mut other);
    let b = other.complete_request(b).err().unwrap();
    assert_eq!(&**work.complete_request(b).ok().unwrap(), "child-b");
    assert_eq!(work.complete_request(group.run(|n| n + 1)).ok(), Some(80));
    assert!(!work.seal(&mut groups));
    let a = a.run(|value| {
        assert_eq!(&**value, "child-a");
        value
    });
    assert_eq!(&**work.complete_request(a).ok().unwrap(), "child-a");
    assert!(work.can_finish(&groups, &[]));
    assert!(work.seal(&mut groups));
}

#[test]
fn child_request_and_its_actual_inverse_are_admitted_together() {
    let mut groups = CleanupGroups::<String>::new(907);
    let mut work = SetupWork::<Box<String>, ()>::new(907);
    complete_root(&mut work);
    let rejected = work
        .enqueue_owned_child(&mut groups, 99, Box::new("child".into()), "inverse".into())
        .err()
        .unwrap();
    assert_eq!(work.child_count(), 0);
    assert!(groups.get(0).unwrap().is_empty());
    assert_eq!(
        work.enqueue_owned_child(&mut groups, 0, rejected.0, rejected.1)
            .ok(),
        Some(0)
    );
    let request = work.take_child().unwrap();
    work.withdraw();
    assert!(work.enqueue_child(Box::new("too late".into())).is_err());
    assert!(work.complete_request(request.run(|v| v)).is_ok());
    assert!(!work.seal(&mut groups));
    let (ticket, inverse) = groups.pop(0).unwrap().unwrap();
    assert_eq!(inverse, "inverse");
    assert!(!work.seal(&mut groups));
    assert!(groups
        .complete(0, ticket, RestoreOutcome::Succeeded, None)
        .is_ok());
    assert!(work.seal(&mut groups));
}

#[test]
fn cleanup_state_from_another_episode_cannot_satisfy_the_guard() {
    let mut own = CleanupGroups::<()>::new(908);
    let mut other = CleanupGroups::<()>::new(909);
    let mut work = SetupWork::<(), ()>::new(908);
    complete_root(&mut work);
    assert!(!work.can_finish(&other, &[]));
    assert!(!work.seal(&mut other));
    assert!(work.enqueue_owned_child(&mut other, 0, (), ()).is_err());
    assert_eq!(work.child_count(), 0);
    assert!(work.seal(&mut own));
    assert!(!other.is_empty());
}
