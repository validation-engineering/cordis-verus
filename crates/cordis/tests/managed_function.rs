use cordis::{
    Context, ManagedInstruction as I, Plugin, ReversibleValue, Runtime, RuntimeError, ServiceKey,
    ValueBranch as Branch, ValueOperation as Op,
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
    panic!("synchronous native function did not settle");
}
fn end() -> Branch {
    Branch {
        matched: None,
        unmatched: None,
    }
}
fn next(pc: usize) -> Branch {
    Branch {
        matched: Some(pc),
        unmatched: Some(pc),
    }
}
struct Fixture {
    runtime: Runtime,
    context: Context,
    provider: usize,
    key: ServiceKey<ReversibleValue>,
    alias: ServiceKey<ReversibleValue>,
    foreign: ServiceKey<ReversibleValue>,
    text: ServiceKey<String>,
    local: ReversibleValue,
    remote: ReversibleValue,
}
fn fixture() -> Fixture {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::new("mixed value");
    let alias = ServiceKey::new("mixed alias");
    let foreign = ServiceKey::new("mixed foreign");
    let text = ServiceKey::new("mixed text");
    let local = runtime.reversible_value(10);
    let remote = ReversibleValue::new(40);
    let a = local.clone();
    let b = remote.clone();
    let provider = runtime
        .mount(
            &context,
            None,
            Plugin::new("mixed provider", move |setup| {
                setup.provide(key, a.clone())?;
                setup.provide(alias, a.clone())?;
                setup.provide(foreign, b.clone())?;
                setup.provide(text, "old".to_owned())?;
                Ok(())
            })
            .provides(key)
            .provides(alias)
            .provides(foreign)
            .provides(text),
        )
        .unwrap();
    ready(runtime.settle()).unwrap();
    Fixture {
        runtime,
        context,
        provider,
        key,
        alias,
        foreign,
        text,
        local,
        remote,
    }
}
#[test]
fn mixed_root_selects_real_outcomes_across_aliases_and_a_b_a_journals() {
    let mut f = fixture();
    let body = Plugin::native_function(
        "mixed root",
        vec![
            I::scalar(
                f.key,
                Op::CompareExchange {
                    expected: 10,
                    value: 12,
                },
                Branch {
                    matched: Some(1),
                    unmatched: Some(4),
                },
            ),
            I::scalar(f.foreign, Op::Add(5), next(2)),
            I::replace(f.text, "chosen".to_owned(), next(3)),
            I::scalar(f.alias, Op::Add(1), end()),
            I::replace(f.text, "wrong branch".to_owned(), end()),
        ],
    )
    .unwrap();
    let id = f.runtime.mount(&f.context, None, body).unwrap();
    ready(f.runtime.settle()).unwrap();
    assert_eq!(
        (f.local.snapshot().value(), f.remote.snapshot().value()),
        (13, 45)
    );
    assert_eq!(
        f.runtime.get(&f.context, f.text).unwrap().as_str(),
        "chosen"
    );
    f.runtime.dispose(id).unwrap();
    ready(f.runtime.settle()).unwrap();
    assert_eq!(
        (
            f.local.snapshot().value(),
            f.local.snapshot().depth(),
            f.remote.snapshot().value(),
            f.remote.snapshot().depth()
        ),
        (10, 0, 40, 0)
    );
    assert_eq!(f.runtime.get(&f.context, f.text).unwrap().as_str(), "old");
}
#[test]
fn false_comparison_selects_typed_child_continuation() {
    let mut f = fixture();
    let key = f.key;
    let text = f.text;
    let parent = f
        .runtime
        .mount(
            &f.context,
            None,
            Plugin::new("parent", move |setup| {
                setup.mount(Plugin::native_function(
                    "mixed Child",
                    vec![
                        I::scalar(
                            key,
                            Op::CompareExchange {
                                expected: 999,
                                value: 12,
                            },
                            Branch {
                                matched: Some(1),
                                unmatched: Some(2),
                            },
                        ),
                        I::replace(text, "wrong".to_owned(), end()),
                        I::replace(text, "selected".to_owned(), end()),
                    ],
                )?)?;
                Ok(())
            })
            .requires(key)
            .requires(text),
        )
        .unwrap();
    ready(f.runtime.settle()).unwrap();
    assert_eq!(f.local.snapshot().value(), 10);
    assert_eq!(
        f.runtime.get(&f.context, f.text).unwrap().as_str(),
        "selected"
    );
    f.runtime.dispose(parent).unwrap();
    ready(f.runtime.settle()).unwrap();
    assert_eq!(f.local.snapshot().depth(), 0);
    assert_eq!(f.runtime.get(&f.context, f.text).unwrap().as_str(), "old");
}
#[test]
fn late_rejection_recovers_the_whole_mixed_prefix() {
    let mut f = fixture();
    let id = f
        .runtime
        .mount(
            &f.context,
            None,
            Plugin::native_function(
                "failed body",
                vec![
                    I::replace(f.text, "temporary".to_owned(), next(1)),
                    I::scalar(f.key, Op::Add(2), next(2)),
                    I::scalar(f.foreign, Op::Add(u64::MAX), end()),
                ],
            )
            .unwrap(),
        )
        .unwrap();
    let error = ready(f.runtime.settle()).unwrap_err();
    assert!(error.to_string().contains("instruction 2"));
    assert_eq!(
        (
            f.local.snapshot().value(),
            f.local.snapshot().depth(),
            f.remote.snapshot().value()
        ),
        (10, 0, 40)
    );
    assert_eq!(f.runtime.get(&f.context, f.text).unwrap().as_str(), "old");
    assert!(f.runtime.owner_context(id).is_err());
}
#[test]
fn typed_conflict_blocks_earlier_scalar_inverse_and_provider_release_until_retry() {
    let mut f = fixture();
    let text = f.text;
    let first = f
        .runtime
        .mount(
            &f.context,
            None,
            Plugin::native_function(
                "first",
                vec![
                    I::scalar(f.key, Op::Add(3), next(1)),
                    I::replace(text, "first".to_owned(), end()),
                ],
            )
            .unwrap(),
        )
        .unwrap();
    ready(f.runtime.settle()).unwrap();
    let stale = f.runtime.owner_context(first).unwrap();
    f.runtime
        .mount(
            &f.context,
            None,
            Plugin::new("later replacement", move |setup| {
                setup.replace_service(text, "second".to_owned())
            })
            .requires(text),
        )
        .unwrap();
    ready(f.runtime.settle()).unwrap();
    f.runtime.dispose(first).unwrap();
    assert!(matches!(
        ready(f.runtime.settle()),
        Err(RuntimeError::Cleanup { .. })
    ));
    assert_eq!(f.local.snapshot().value(), 13);
    assert_eq!(f.runtime.get(&f.context, text).unwrap().as_str(), "second");
    assert!(stale.replace_service(text, "stale".to_owned()).is_err());
    f.runtime.dispose(f.provider).unwrap();
    let _ = ready(f.runtime.settle());
    assert!(f.runtime.contains(f.provider));
    assert!(!f.runtime.cleanup_started(f.provider));
    assert_eq!(f.local.snapshot().value(), 13);
    f.runtime.retry_cleanup(first).unwrap();
    ready(f.runtime.settle()).unwrap();
    assert!(!f.runtime.contains(first));
    assert!(!f.runtime.contains(f.provider));
    assert_eq!(
        (f.local.snapshot().value(), f.local.snapshot().depth()),
        (10, 0)
    );
}
#[test]
fn replacement_recipe_uses_new_arguments_after_restoring_old_body() {
    let mut f = fixture();
    let key = f.key;
    let text = f.text;
    let body = |amount, value: &str| {
        Plugin::native_function(
            "versioned body",
            vec![
                I::scalar(key, Op::Add(amount), next(1)),
                I::replace(text, value.to_owned(), end()),
            ],
        )
        .unwrap()
    };
    let id = f.runtime.mount(&f.context, None, body(2, "v1")).unwrap();
    ready(f.runtime.settle()).unwrap();
    f.runtime.update_plugin(id, body(7, "v2")).unwrap();
    ready(f.runtime.settle()).unwrap();
    assert_eq!(f.local.snapshot().value(), 17);
    assert_eq!(f.runtime.get(&f.context, text).unwrap().as_str(), "v2");
    f.runtime.dispose(id).unwrap();
    ready(f.runtime.settle()).unwrap();
    assert_eq!(f.local.snapshot().value(), 10);
    assert_eq!(f.runtime.get(&f.context, text).unwrap().as_str(), "old");
}
#[test]
fn malformed_branches_and_static_dispatch_are_rejected() {
    let key = ServiceKey::<ReversibleValue>::new("invalid");
    assert!(
        Plugin::native_function("backward", vec![I::scalar(key, Op::Add(1), next(0))]).is_err()
    );
    assert!(Plugin::native_function("outside", vec![I::scalar(key, Op::Add(1), next(1))]).is_err());
    let mut static_plugin = cordis::runtime::static_host::StaticPlugin::new(
        Plugin::native_function("native only", vec![]).unwrap(),
    )
    .unwrap();
    let start = static_plugin.begin(6, 1, Context::new(), vec![]).unwrap();
    assert!(ready(start.setup)
        .unwrap_err()
        .to_string()
        .contains("native Runtime"));
    start.episode.cancel();
    ready(start.episode.cleanup().unwrap()).unwrap();
}
