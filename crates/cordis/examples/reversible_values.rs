//! Run with `cargo run -p cordis-verus --example reversible_values`.
use cordis::{Context, Plugin, ReversibleValue, Runtime, ServiceKey, ValueOperation};
use std::future::Future;
use std::task::{Context as TaskContext, Poll, Waker};

fn ready<F: Future>(future: F) -> F::Output {
    let mut future = std::pin::pin!(future);
    let mut context = TaskContext::from_waker(Waker::noop());
    for _ in 0..1000 {
        if let Poll::Ready(output) = future.as_mut().poll(&mut context) {
            return output;
        }
    }
    panic!("synchronous example did not settle");
}
fn main() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::new("configuration limit");
    let value = ReversibleValue::new(10);
    let supplied = value.clone();
    let provider = runtime
        .mount(
            &context,
            None,
            Plugin::new("configuration", move |setup| {
                setup.provide(key, supplied.clone())?;
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    let first = runtime
        .mount(
            &context,
            None,
            Plugin::new("first update", move |setup| {
                setup.update_reversible(key, ValueOperation::Add(5))?;
                Ok(())
            })
            .requires(key),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    let second = runtime
        .mount(
            &context,
            None,
            Plugin::new("second update", move |setup| {
                setup.update_reversible(key, ValueOperation::Add(7))?;
                Ok(())
            })
            .requires(key),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    println!("applied both updates: value={}", value.snapshot().value());
    runtime.dispose(first).unwrap();
    let blocked = ready(runtime.settle()).unwrap_err();
    println!("first cleanup blocked: {blocked}");
    assert_eq!(value.snapshot().value(), 22);
    runtime.dispose(provider).unwrap();
    let _ = ready(runtime.settle());
    assert_eq!(runtime.phase(second), Some(cordis::Phase::Inactive));
    assert!(runtime.contains(provider));
    assert_eq!(value.snapshot().value(), 15);
    println!("later update restored: value=15; provider retained while first cleanup is failed");
    runtime.retry_cleanup(first).unwrap();
    ready(runtime.settle()).unwrap();
    assert_eq!(value.snapshot().value(), 10);
    assert!(!runtime.contains(provider));
    println!("retry restored value=10; provider released");
}
