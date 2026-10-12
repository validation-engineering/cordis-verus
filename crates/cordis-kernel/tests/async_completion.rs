use cordis_kernel::async_completion::{await_completion, witnessed_completion};
use cordis_kernel::cleanup_journal::RestoreOutcome;
use cordis_kernel::cleanup_queue::{completion::CleanupPolicy, CleanupQueue};
use std::future::{poll_fn, Future};
use std::pin::Pin;
use std::sync::{
    atomic::{AtomicBool, AtomicUsize, Ordering},
    Arc,
};
use std::task::{Context, Poll, Waker};

fn poll<F: Future>(future: Pin<&mut F>) -> Poll<F::Output> {
    future.poll(&mut Context::from_waker(Waker::noop()))
}
fn ready<F: Future>(future: F) -> F::Output {
    match poll(Box::pin(future).as_mut()) {
        Poll::Ready(value) => value,
        Poll::Pending => panic!("expected completion"),
    }
}

#[test]
fn out_of_order_real_futures_keep_origin_result_and_retry_payload_together() {
    let mut a = CleanupQueue::scope(61);
    let mut b = CleanupQueue::scope(62);
    a.register(String::from("a-retry"));
    b.register(String::from("b-retry"));
    let (ta, pa) = a.pop().unwrap().unwrap();
    let (tb, pb) = b.pop().unwrap().unwrap();
    let gate = Arc::new(AtomicBool::new(false));
    let opened = gate.clone();
    let mut first = Box::pin(await_completion(
        ta,
        poll_fn(move |_| {
            if opened.load(Ordering::SeqCst) {
                Poll::Ready(Err::<(), _>(String::from("a failed")))
            } else {
                Poll::Pending
            }
        }),
    ));
    assert!(poll(first.as_mut()).is_pending());
    let second = ready(await_completion(tb, async { Ok::<(), String>(()) }));
    let report = b
        .complete_future(second, Some(pb), CleanupPolicy::RetainFailure)
        .ok()
        .unwrap();
    assert_eq!(report.outcome, RestoreOutcome::Succeeded);
    assert_eq!(report.discarded.as_deref(), Some("b-retry"));
    assert!(b.is_empty());
    assert!(!a.is_empty());
    gate.store(true, Ordering::SeqCst);
    let completion = match poll(first.as_mut()) {
        Poll::Ready(c) => c,
        _ => unreachable!(),
    };
    // A real completed Future sent to the wrong group returns ownership intact.
    let (completion, retry) = b
        .complete_future(completion, Some(pa), CleanupPolicy::RetainFailure)
        .err()
        .unwrap();
    assert_eq!(*completion.argument_ref(), ta);
    let report = a
        .complete_future(completion, retry, CleanupPolicy::RetainFailure)
        .ok()
        .unwrap();
    assert_eq!(report.result, Err(String::from("a failed")));
    assert_eq!(report.outcome, RestoreOutcome::Failed);
    let retry = a.retry().unwrap();
    let (issued, payload) = a.pop().unwrap().unwrap();
    assert_eq!(issued, retry);
    assert!(retry.attempt > ta.attempt);
    assert_eq!(payload, "a-retry");
    let old = ready(await_completion(ta, async { Ok::<(), String>(()) }));
    assert!(a
        .complete_future(old, None, CleanupPolicy::RetainFailure)
        .is_err());
    let actual = ready(await_completion(issued, async { Ok::<(), String>(()) }));
    assert!(a
        .complete_future(actual, Some(payload), CleanupPolicy::RetainFailure)
        .is_ok());
    assert!(a.is_empty());
}

#[test]
fn actual_failures_preserve_the_two_host_policies_and_cannot_be_success() {
    for (policy, expected) in [
        (CleanupPolicy::RetainFailure, RestoreOutcome::Failed),
        (CleanupPolicy::DrainConsumed, RestoreOutcome::Drained),
    ] {
        let mut queue = CleanupQueue::scope(63);
        queue.register(());
        let (ticket, ()) = queue.pop().unwrap().unwrap();
        let actual = ready(await_completion(ticket, async {
            Err::<(), _>("external failure")
        }));
        let report = queue.complete_future(actual, None, policy).ok().unwrap();
        assert_eq!(report.outcome, expected);
        assert_eq!(report.result, Err("external failure"));
        assert_eq!(queue.is_empty(), policy == CleanupPolicy::DrainConsumed);
        assert!(!queue.can_retry());
        let mut queue = CleanupQueue::scope(64);
        queue.register(());
        let (ticket, ()) = queue.pop().unwrap().unwrap();
        let report = queue
            .complete_failure(ticket, "poll panicked", None, policy)
            .ok()
            .unwrap();
        assert_eq!(report.outcome, expected);
        assert_eq!(report.result, Err("poll panicked"));
    }
}

#[test]
fn successful_completion_returns_factory_for_destruction_outside_the_queue() {
    struct Factory(Arc<AtomicUsize>);
    impl Drop for Factory {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }
    let drops = Arc::new(AtomicUsize::new(0));
    let mut queue = CleanupQueue::scope(65);
    queue.register(Factory(drops.clone()));
    let (ticket, factory) = queue.pop().unwrap().unwrap();
    let completion = ready(await_completion(ticket, async { Ok::<(), ()>(()) }));
    let report = queue
        .complete_future(completion, Some(factory), CleanupPolicy::RetainFailure)
        .ok()
        .unwrap();
    assert_eq!(drops.load(Ordering::SeqCst), 0);
    assert!(queue.is_empty());
    drop(report.discarded);
    assert_eq!(drops.load(Ordering::SeqCst), 1);
}

#[test]
fn executable_caller_derives_output_from_the_actual_input() {
    let completion = ready(witnessed_completion(123));
    assert_eq!(completion.into_parts(), (123, 123 ^ 37));
}

#[test]
fn actual_factory_runs_once_before_poll_and_receives_the_owned_argument() {
    use cordis_kernel::async_completion::{invoke, invoke_future, witnessed_invocation};
    assert_eq!(witnessed_invocation(17), 17 ^ 37);
    let input = Box::new(String::from("actual input"));
    let address = std::ptr::from_ref(input.as_ref());
    let output = invoke(input, |value| {
        assert_eq!(std::ptr::from_ref(value.as_ref()), address);
        value
    })
    .into_result();
    assert_eq!(*output, "actual input");
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = calls.clone();
    let awaiting = invoke_future(84_u64, output, move |input| {
        observed.fetch_add(1, Ordering::SeqCst);
        async move { Err::<(), _>(input) }
    });
    assert_eq!(calls.load(Ordering::SeqCst), 1); // Factory invocation is not deferred to first poll.
    let completion = ready(awaiting.complete());
    let (origin, result) = completion.into_parts();
    assert_eq!(origin, 84);
    assert_eq!(*result.unwrap_err(), "actual input");
    assert_eq!(calls.load(Ordering::SeqCst), 1);
}

#[test]
fn factory_panic_is_caught_at_invocation_and_never_becomes_a_completion() {
    use cordis_kernel::async_completion::invoke_future;
    let result = std::panic::catch_unwind(|| {
        invoke_future(85_u64, (), |()| -> std::future::Ready<()> {
            panic!("factory failed before returning a Future");
        })
    });
    assert!(result.is_err());
}
