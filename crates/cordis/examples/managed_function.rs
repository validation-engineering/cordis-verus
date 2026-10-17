//! Run with `cargo run -p cordis-verus --example managed_function --offline`.
//! One stored function mixes scalar and typed effects. A later writer blocks
//! cleanup; the real provider remains retained until restoration and retry.
use cordis::{
    Context, ManagedInstruction as I, Plugin, Runtime, ServiceKey, ValueBranch as Branch,
    ValueOperation as Op,
};
use std::future::Future;
use std::task::{Context as TaskContext, Poll, Waker};

fn ready<F: Future>(future: F) -> F::Output {
    let mut future = std::pin::pin!(future);
    let mut cx = TaskContext::from_waker(Waker::noop());
    for _ in 0..1000 {
        if let Poll::Ready(value) = future.as_mut().poll(&mut cx) {
            return value;
        }
    }
    panic!("synchronous example did not settle");
}
fn end() -> Branch {
    Branch {
        matched: None,
        unmatched: None,
    }
}
fn main() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let count = ServiceKey::new("request budget");
    let label = ServiceKey::new("request label");
    let value = runtime.reversible_value(10);
    let supplied = value.clone();
    let provider = runtime
        .mount(
            &context,
            None,
            Plugin::new("provider", move |setup| {
                setup.provide(count, supplied.clone())?;
                setup.provide(label, "original".to_owned())?;
                Ok(())
            })
            .provides(count)
            .provides(label),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();

    let consumer = runtime
        .mount(
            &context,
            None,
            Plugin::native_function(
                "consumer",
                vec![
                    I::scalar(
                        count,
                        Op::CompareExchange {
                            expected: 10,
                            value: 13,
                        },
                        Branch {
                            matched: Some(1),
                            unmatched: Some(2),
                        },
                    ),
                    I::replace(label, "selected".to_owned(), end()),
                    I::replace(label, "unmatched".to_owned(), end()),
                ],
            )
            .unwrap(),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    assert_eq!(value.snapshot().value(), 13);
    assert_eq!(runtime.get(&context, label).unwrap().as_str(), "selected");
    println!("Stored function: budget 10 -> 13; actual result selected the typed replacement");

    runtime
        .mount(
            &context,
            None,
            Plugin::new("later writer", move |setup| {
                setup.replace_service(label, "later".to_owned())
            })
            .requires(label),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    runtime.dispose(consumer).unwrap();
    let error = ready(runtime.settle()).unwrap_err();
    assert_eq!(value.snapshot().value(), 13);
    assert_eq!(runtime.get(&context, label).unwrap().as_str(), "later");
    println!("Conflicting replacement blocks cleanup; earlier scalar inverse is retained: {error}");

    runtime.dispose(provider).unwrap();
    let _ = ready(runtime.settle());
    assert!(runtime.contains(provider));
    assert!(!runtime.cleanup_started(provider));
    println!("Later writer restored; provider still cannot release before the failed consumer");

    runtime.retry_cleanup(consumer).unwrap();
    ready(runtime.settle()).unwrap();
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (10, 0)
    );
    assert!(!runtime.contains(consumer));
    assert!(!runtime.contains(provider));
    println!(
        "Explicit retry restores typed then scalar effects; budget is 10 and provider is released"
    );
}
