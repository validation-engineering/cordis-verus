use cordis::{AsyncSetup, Context, Phase, Plugin, Runtime, ServiceKey, ServiceReadFailure};
use std::future::Future;
use std::pin::pin;
use std::sync::{Arc, Mutex};
use std::task::{Context as TaskContext, Poll, Waker};

fn finish<T>(future: impl Future<Output = T>) -> T {
    match pin!(future)
        .as_mut()
        .poll(&mut TaskContext::from_waker(Waker::noop()))
    {
        Poll::Ready(value) => value,
        Poll::Pending => panic!("unexpected pending"),
    }
}
fn provider(key: ServiceKey<String>, value: &'static str) -> Plugin {
    Plugin::new("provider", move |ctx| {
        ctx.provide(key, value.to_owned())?;
        Ok(())
    })
    .provides(key)
}

#[test]
fn one_description_gates_reads_and_reloads_with_committed_cleanup_values() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::<String>::of();
    let log = Arc::new(Mutex::new(Vec::new()));
    let output = log.clone();
    let consumer = runtime
        .mount(
            &context,
            None,
            Plugin::with_dependencies("consumer", (key, key)).setup(move |ctx, (a, b)| {
                assert!(Arc::ptr_eq(&a, &b));
                output.lock().unwrap().push(format!("start:{a}"));
                let output = output.clone();
                let episode = ctx.to_async();
                ctx.on_cleanup(move || {
                    // A restoration read must retain this episode's provider.
                    output
                        .lock()
                        .unwrap()
                        .push(format!("stop:{}", episode.require(key)?));
                    Ok(())
                });
                Ok(())
            }),
        )
        .unwrap();
    finish(runtime.join(consumer)).unwrap();
    assert_eq!(runtime.phase(consumer), Some(Phase::Inactive));
    assert!(log.lock().unwrap().is_empty());
    let old = runtime.mount(&context, None, provider(key, "old")).unwrap();
    finish(runtime.settle()).unwrap();
    assert_eq!(runtime.committed(consumer).len(), 1);
    runtime.dispose(old).unwrap();
    finish(runtime.settle()).unwrap();
    runtime.mount(&context, None, provider(key, "new")).unwrap();
    finish(runtime.settle()).unwrap();
    finish(runtime.shutdown()).unwrap();
    assert_eq!(
        *log.lock().unwrap(),
        ["start:old", "stop:old", "start:new", "stop:new"]
    );
}

#[test]
fn canonical_named_and_fresh_keys_have_explicit_identity_rules() {
    let root = Context::new();
    assert_eq!(
        root.port(ServiceKey::<String>::of()),
        root.port(ServiceKey::<String>::of())
    );
    assert_eq!(
        root.port(ServiceKey::<String>::named("one")),
        root.port(ServiceKey::<String>::named("one"))
    );
    assert_ne!(
        root.port(ServiceKey::<String>::named("one")),
        root.port(ServiceKey::<u64>::named("one"))
    );
    assert_ne!(
        root.port(ServiceKey::<String>::named("one")),
        root.port(ServiceKey::<String>::named("two"))
    );
    assert_ne!(
        root.port(ServiceKey::<String>::of()),
        root.port(ServiceKey::<String>::named(std::any::type_name::<String>()))
    );
    assert_ne!(
        root.port(ServiceKey::<String>::new("one")),
        root.port(ServiceKey::<String>::new("one"))
    );
    assert_ne!(
        root.port(ServiceKey::<String>::new("one")),
        root.port(ServiceKey::<String>::named("one"))
    );
}

#[test]
fn async_typed_setup_uses_isolation_and_availability_config() {
    let mut runtime = Runtime::new();
    let key = ServiceKey::<String>::new("scoped");
    let outer = Context::new();
    let inner = outer.isolate(key);
    runtime.mount(&outer, None, provider(key, "outer")).unwrap();
    runtime
        .mount(
            &inner,
            None,
            Plugin::new("checked", move |ctx| {
                ctx.provide_checked(key, "inner".to_owned(), |_, _, config| config == "accepted")?;
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
    let seen = Arc::new(Mutex::new(Vec::new()));
    let output = seen.clone();
    runtime
        .mount(
            &inner,
            None,
            Plugin::with_dependencies("allowed", key.with_config("accepted".into())).setup_async(
                move |_, value| {
                    let output = output.clone();
                    async move {
                        output.lock().unwrap().push((*value).clone());
                        Ok(())
                    }
                },
            ),
        )
        .unwrap();
    let blocked = runtime
        .mount(
            &inner,
            None,
            Plugin::with_dependencies("blocked", key.with_config("denied".into()))
                .setup(|_, _| panic!("a rejected dependency must not run setup")),
        )
        .unwrap();
    finish(runtime.settle()).unwrap();
    assert_eq!(*seen.lock().unwrap(), ["inner"]);
    assert_eq!(runtime.phase(blocked), Some(Phase::Inactive));
    finish(runtime.shutdown()).unwrap();
}

#[test]
fn structured_reads_preserve_caller_and_episode_identity() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let key = ServiceKey::<String>::new("message");
    let held: Arc<Mutex<Option<AsyncSetup>>> = Arc::default();
    let output = held.clone();
    let owner = runtime
        .mount(
            &context,
            None,
            Plugin::new("owner", move |ctx| {
                let missing = ctx.require(key).unwrap_err();
                assert_eq!(missing.reason, ServiceReadFailure::MissingValue);
                assert_eq!(missing.provider, Some(ctx.owner()));
                ctx.provide(key, "hello".into())?;
                *output.lock().unwrap() = Some(ctx.to_async());
                Ok(())
            })
            .provides(key),
        )
        .unwrap();
    finish(runtime.settle()).unwrap();
    let setup = held.lock().unwrap().clone().unwrap();
    let generation = runtime.episode_generation(owner).unwrap();
    let unknown = ServiceKey::<u64>::new("unknown");
    let line = line!() + 1;
    let error = setup.require(unknown).unwrap_err();
    assert_eq!(error.location.line(), line);
    assert!(error.location.file().ends_with("typed_dependencies.rs"));
    assert_eq!(error.reason, ServiceReadFailure::Undeclared);
    assert_eq!(error.plugin, owner);
    assert_eq!(error.generation, generation);
    assert_eq!(error.port, context.port(unknown));
    assert!(error.provider.is_none());
    assert_eq!(
        setup.get(unknown).unwrap_err().reason,
        ServiceReadFailure::Undeclared
    );
    assert!(error.to_string().contains("generation"));
    finish(runtime.shutdown()).unwrap();
    assert_eq!(
        setup.require(key).unwrap_err().reason,
        ServiceReadFailure::ClosedEpisode
    );
}

#[test]
fn tuple_parameters_remain_heterogeneous_and_interoperate_with_manual_plugins() {
    let mut runtime = Runtime::new();
    let context = Context::new();
    let number = ServiceKey::<u64>::new("number");
    let text = ServiceKey::<String>::new("text");
    runtime
        .mount(
            &context,
            None,
            Plugin::new("manual", move |ctx| {
                ctx.provide(number, 42)?;
                ctx.provide(text, "answer".into())?;
                Ok(())
            })
            .provides(number)
            .provides(text),
        )
        .unwrap();
    runtime
        .mount(
            &context,
            None,
            Plugin::with_dependencies("typed", (number, text)).setup(|_, (number, text)| {
                assert_eq!(*number, 42);
                assert_eq!(*text, "answer");
                Ok(())
            }),
        )
        .unwrap();
    runtime
        .mount(
            &context,
            None,
            Plugin::with_dependencies("empty", ()).setup_async(|_, ()| async { Ok(()) }),
        )
        .unwrap();
    finish(runtime.settle()).unwrap();
    finish(runtime.shutdown()).unwrap();
}

#[test]
fn nested_tuples_share_one_configuration_and_conflicts_fail_before_admission() {
    let key = ServiceKey::<String>::new("configured twice");
    let mut runtime = Runtime::new();
    let bad = Plugin::with_dependencies(
        "ambiguous",
        (key.with_config("one".into()), key.with_config("two".into())),
    )
    .setup(|_, _| panic!("invalid declaration must not activate"));
    assert!(matches!(
        runtime.mount(&Context::new(), None, bad),
        Err(cordis::RuntimeError::DependencyConflict {
            service: "configured twice",
            ..
        })
    ));
    assert!(runtime.ids().is_empty());
    runtime
        .mount(&Context::new(), None, provider(key, "value"))
        .unwrap();
    let plugin = Plugin::with_dependencies(
        "nested",
        (
            key.with_config("same".into()),
            key.with_config("same".into()),
            (key, key, key, key, key, key, key, key),
        ),
    )
    .setup(|_, (a, b, values)| {
        assert!(Arc::ptr_eq(&a, &b));
        assert!(Arc::ptr_eq(&a, &values.0));
        assert!(Arc::ptr_eq(&a, &values.7));
        Ok(())
    });
    let id = runtime.mount(&Context::new(), None, plugin).unwrap();
    finish(runtime.settle()).unwrap();
    assert_eq!(runtime.committed(id).len(), 1);
    finish(runtime.shutdown()).unwrap();
}
