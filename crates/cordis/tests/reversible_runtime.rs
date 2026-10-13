use cordis::runtime::static_host::{StaticBinding, StaticPlugin, TypedSlot};
use cordis::{
    Context, Plugin, ReversibleValue, Runtime, RuntimeError, ServiceKey, ValueBranch,
    ValueInstruction, ValueOperation, ValueProgram,
};
use std::future::Future;
use std::sync::Arc;
use std::task::{Context as TaskContext, Poll, Waker};

fn ready<F: Future>(future: F) -> F::Output {
    let mut future = std::pin::pin!(future);
    let mut context = TaskContext::from_waker(Waker::noop());
    for _ in 0..1000 {
        if let Poll::Ready(output) = future.as_mut().poll(&mut context) {
            return output;
        }
    }
    panic!("finite, synchronous plugin work did not settle");
}
fn provider(
    runtime: &mut Runtime,
    context: &Context,
    key: ServiceKey<ReversibleValue>,
    value: ReversibleValue,
) -> usize {
    let id = runtime
        .mount(
            context,
            None,
            Plugin::new("value provider", move |setup| {
                setup.provide(key, value.clone())?;
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    id
}

#[test]
fn actual_plugins_keep_dependencies_until_the_value_is_recovered() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::new("reversible config");
    let value = ReversibleValue::new(10);
    let provider = provider(&mut runtime, &context, key, value.clone());
    let first = runtime
        .mount(
            &context,
            None,
            Plugin::new("first update", move |setup| {
                let out = setup.update_reversible(key, ValueOperation::Add(5))?;
                assert_eq!(out.after, 15);
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
            Plugin::new("later update", move |setup| {
                setup.update_reversible(key, ValueOperation::Add(7))?;
                Ok(())
            })
            .requires(key),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    let escaped = runtime.owner_context(first).unwrap();
    runtime.dispose(first).unwrap();
    assert!(matches!(
        ready(runtime.settle()),
        Err(RuntimeError::Cleanup { .. })
    ));
    assert_eq!(value.snapshot().value(), 22);
    assert!(runtime.contains(first));
    assert!(runtime.contains(provider));
    assert!(escaped
        .update_reversible(key, ValueOperation::Replace(0))
        .is_err());
    assert_eq!(value.snapshot().value(), 22);
    runtime.dispose(provider).unwrap();
    let _ = ready(runtime.settle());
    assert!(runtime.contains(provider));
    assert_eq!(runtime.phase(second), Some(cordis::Phase::Inactive));
    assert_eq!(value.snapshot().value(), 15);
    runtime.retry_cleanup(first).unwrap();
    ready(runtime.settle()).unwrap();
    assert!(!runtime.contains(first));
    assert_eq!(runtime.phase(second), Some(cordis::Phase::Inactive));
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (10, 0)
    );
    assert!(!runtime.contains(provider));
}

#[test]
fn production_program_uses_the_real_comparison_result() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::new("program state");
    let value = ReversibleValue::new(6);
    provider(&mut runtime, &context, key, value.clone());
    let program = ValueProgram::new(vec![
        ValueInstruction {
            operation: ValueOperation::CompareExchange {
                expected: 5,
                value: 80,
            },
            branch: ValueBranch {
                matched: Some(1),
                unmatched: Some(2),
            },
        },
        ValueInstruction {
            operation: ValueOperation::Replace(99),
            branch: ValueBranch {
                matched: None,
                unmatched: None,
            },
        },
        ValueInstruction {
            operation: ValueOperation::Add(4),
            branch: ValueBranch {
                matched: None,
                unmatched: None,
            },
        },
    ])
    .unwrap();
    let consumer = runtime
        .mount(
            &context,
            None,
            Plugin::new("checked program", move |setup| {
                let outcomes = setup.run_value_program(key, &program)?;
                assert_eq!(outcomes.len(), 2);
                assert!(!outcomes[0].matched);
                assert_eq!(outcomes[1].after, 10);
                Ok(())
            })
            .requires(key),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    assert_eq!(value.snapshot().value(), 10);
    runtime.dispose(consumer).unwrap();
    ready(runtime.settle()).unwrap();
    assert_eq!((value.snapshot().value(), value.snapshot().depth()), (6, 0));
}

#[test]
fn production_program_failure_keeps_the_prefix_for_cleanup() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::new("overflow state");
    let value = ReversibleValue::new(6);
    provider(&mut runtime, &context, key, value.clone());
    let program = ValueProgram::new(vec![
        ValueInstruction {
            operation: ValueOperation::Replace(u64::MAX),
            branch: ValueBranch {
                matched: Some(1),
                unmatched: None,
            },
        },
        ValueInstruction {
            operation: ValueOperation::Add(1),
            branch: ValueBranch {
                matched: None,
                unmatched: None,
            },
        },
    ])
    .unwrap();
    let consumer = runtime
        .mount(
            &context,
            None,
            Plugin::new("failing program", move |setup| {
                setup.run_value_program(key, &program)?;
                Ok(())
            })
            .requires(key),
        )
        .unwrap();
    assert!(ready(runtime.settle()).is_err());
    runtime.dispose(consumer).unwrap();
    let _ = ready(runtime.settle());
    assert_eq!((value.snapshot().value(), value.snapshot().depth()), (6, 0));
}

#[test]
fn static_host_executes_the_same_checked_restore() {
    let value = ReversibleValue::new(3);
    let key = ServiceKey::new("static reversible value");
    let context = Context::new();
    let mut plugin = StaticPlugin::new(
        Plugin::new("static update", move |setup| {
            setup.update_reversible(key, ValueOperation::Xor(7))?;
            Ok(())
        })
        .requires(key),
    )
    .unwrap();
    let start = plugin
        .begin(
            5,
            1,
            context.clone(),
            vec![StaticBinding {
                port: context.port(key),
                provider: 0,
                slot: TypedSlot::from_arc(Arc::new(value.clone())),
            }],
        )
        .unwrap();
    ready(start.setup).unwrap();
    assert_eq!(value.snapshot().value(), 4);
    start.episode.cancel();
    ready(start.episode.cleanup().unwrap()).unwrap();
    assert_eq!((value.snapshot().value(), value.snapshot().depth()), (3, 0));
}
