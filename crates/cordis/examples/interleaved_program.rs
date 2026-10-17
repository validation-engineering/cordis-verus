//! Run with `cargo run -p cordis-verus --example interleaved_program --offline`.
//! A real Child keeps its continuation across another plugin's update. The
//! same cleanup queue then blocks, retains its first inverse, and retries.
use cordis::{
    Context, Plugin, Runtime, ServiceKey, ValueBranch, ValueInstruction, ValueOperation,
    ValueProgram,
};
use std::future::Future;
use std::sync::{Arc, Mutex};
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

fn addition(amount: u64) -> ValueProgram {
    ValueProgram::new(vec![ValueInstruction {
        operation: ValueOperation::Add(amount),
        branch: ValueBranch {
            matched: None,
            unmatched: None,
        },
    }])
    .unwrap()
}

fn main() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::new("shared limit");
    let alias = ServiceKey::new("alias of shared limit");
    let value = runtime.reversible_value(10);
    let supplied = value.clone();
    let provider = runtime
        .mount(
            &context,
            None,
            Plugin::new("limit provider", move |setup| {
                setup.provide(key, supplied.clone())?;
                setup.provide(alias, supplied.clone())?;
                Ok(())
            })
            .provides(key)
            .provides(alias),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();

    let child_handle = Arc::new(Mutex::new(None));
    let retained = child_handle.clone();
    let parent = runtime
        .mount(
            &context,
            None,
            Plugin::new("parent", move |setup| {
                *retained.lock().unwrap() = Some(setup.mount(Plugin::native_value_program(
                    "program child",
                    key,
                    addition(5),
                ))?);
                Ok(())
            }),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    let child = child_handle.lock().unwrap().as_ref().unwrap().id().unwrap();
    let child_setup = runtime.owner_context(child).unwrap();
    let terminal = ValueBranch {
        matched: None,
        unmatched: None,
    };
    let program = ValueProgram::new(vec![
        ValueInstruction {
            operation: ValueOperation::CompareExchange {
                expected: 15,
                value: 99,
            },
            branch: ValueBranch {
                matched: Some(1),
                unmatched: Some(2),
            },
        },
        ValueInstruction {
            operation: ValueOperation::Replace(999),
            branch: terminal,
        },
        ValueInstruction {
            operation: ValueOperation::Add(1),
            branch: terminal,
        },
    ])
    .unwrap();
    let mut cursor = child_setup.start_value_program(key, program).unwrap();
    assert_eq!(value.snapshot().value(), 15);
    let beginning = runtime.execution_snapshot();

    let other = runtime
        .mount(
            &context,
            None,
            Plugin::native_value_program("interleaved writer", key, addition(7)),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    let foreign = runtime.owner_context(other).unwrap();
    assert!(foreign.advance_value_program(&mut cursor).is_err());
    assert_eq!(cursor.position(), Some(0));
    assert_eq!(value.snapshot().value(), 22);
    // Replacing the live slot must not retarget the cursor or queued inverses.
    let selected = cursor.binding().unwrap();
    assert_eq!(selected.provider(), provider);
    assert_eq!(selected.capture().revision(), 0);
    let replacement = runtime.reversible_value(1000);
    runtime.set(provider, key, replacement.clone()).unwrap();
    let current = child_setup.capture_reversible(key).unwrap();
    assert_eq!(current.capture().revision(), 1);
    assert_eq!(current.value().snapshot().value(), 1000);
    assert!(!selected.capture().check_result(true).accepted());
    let later = selected.capture().refresh();
    assert_eq!(later.revision(), 1);
    assert_eq!(selected.value().snapshot().value(), 22);
    assert_eq!(runtime.get(&context, alias).unwrap().snapshot().value(), 22);
    println!(
        "Live slot advanced to version 1 / value 1000; cursor and alias retain version 0's object"
    );
    let branch = child_setup
        .advance_value_program(&mut cursor)
        .unwrap()
        .unwrap();
    assert!(!branch.matched);
    assert_eq!(cursor.position(), Some(2));
    assert_eq!(
        child_setup
            .advance_value_program(&mut cursor)
            .unwrap()
            .unwrap()
            .after,
        23
    );
    assert_eq!(
        child_setup.advance_value_program(&mut cursor).unwrap(),
        None
    );
    println!("Child continuation observed the intervening write: 10 -> 15 -> 22 -> 23");

    // This alias has its own slot and still selects the original allocation.
    // All aliases of that allocation observe its writes, including restoration.
    assert_eq!(runtime.get(&context, alias).unwrap().snapshot().value(), 23);
    assert_eq!(runtime.get(&context, key).unwrap().snapshot().value(), 1000);
    println!("Old alias observes 23 while the replaced port still observes 1000");

    runtime.dispose(parent).unwrap();
    let failure = ready(runtime.settle()).unwrap_err();
    assert_eq!(value.snapshot().value(), 22);
    assert!(runtime.contains(child));
    assert!(runtime.contains(provider));
    cursor.observe();
    assert_eq!(cursor.observation().value(), 22);
    println!("Child restored its later steps; first inverse retained: {failure}");

    runtime.dispose(provider).unwrap();
    let _ = ready(runtime.settle());
    assert_eq!(value.snapshot().value(), 15);
    assert!(runtime.contains(provider));
    assert!(child_setup.advance_value_program(&mut cursor).is_err());
    println!("Interleaved writer restored; provider remains blocked by the Child's failed cleanup");

    runtime.retry_cleanup(child).unwrap();
    ready(runtime.settle()).unwrap();
    cursor.observe();
    assert_eq!(cursor.observation().value(), 10);
    assert_eq!(cursor.observation().depth(), 0);
    assert!(!runtime.contains(child));
    assert!(!runtime.contains(parent));
    assert!(!runtime.contains(provider));
    assert_eq!(replacement.snapshot().value(), 1000);
    assert_eq!(replacement.snapshot().depth(), 0);
    assert_eq!(cursor.binding().unwrap().capture().revision(), 0);
    println!("Retry restored the original object to 10 at depth 0; replacement remains 1000; all owners released");
    let _completed_execution = beginning.refresh();
    let (_actual_value, _matching_execution) = value.observe_execution();
}
