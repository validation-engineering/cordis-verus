//! Cross-feature regression tests: live configuration, shared service slots and
//! consumer-specific availability must compose without replacing live recipes.
use cordis::config::{ConfigUpdate, ConfigUpdatePlan, Field, Schema};
use cordis::loader::{ConfigTree, FactoryRegistry, Loader};
use cordis::{AsyncSetup, Context, Phase, Plugin, ServiceKey};
use serde_json::{json, Value};
use std::future::Future;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::task::{Context as TaskContext, Poll, Waker};

fn run<F: Future>(future: F) -> F::Output {
    let mut future = std::pin::pin!(future);
    let mut cx = TaskContext::from_waker(Waker::noop());
    for _ in 0..10_000 {
        if let Poll::Ready(value) = future.as_mut().poll(&mut cx) {
            return value;
        }
        std::thread::yield_now();
    }
    panic!("lifecycle did not settle");
}

fn tree(version: u64, enabled: bool) -> ConfigTree {
    ConfigTree::from_json(
        &json!([
            {"id":"model","name":"model","config":{"version":version,"enabled":enabled}},
            {"id":"agent","name":"agent","inject":{"model":{"tenant":"alpha"}}}
        ])
        .to_string(),
    )
    .unwrap()
}

#[test]
fn accepted_provider_update_changes_live_reads_and_rechecks_consumers() {
    let model = ServiceKey::<Value>::new("model");
    let reads = Arc::new(Mutex::new(Vec::<AsyncSetup>::new()));
    let starts = Arc::new(AtomicUsize::new(0));
    let mut registry = FactoryRegistry::new();
    registry.register_service("model", model);
    registry.register(
        "model",
        Schema::object([
            ("version", Field::required(Schema::integer(1, 10))),
            ("enabled", Field::required(Schema::Boolean)),
        ]),
        move |config, _| {
            let config = config.clone();
            Ok(Plugin::new("model", move |setup| {
                setup.provide_checked(model, config.clone(), |value, _, injection| {
                    value["enabled"] == true && injection["tenant"] == "alpha"
                })?;
                Ok(())
            })
            .provides(model)
            .on_config_update(move |setup, previous, next| {
                let forward = setup.clone();
                Ok(ConfigUpdate::Apply(ConfigUpdatePlan::new(
                    move || forward.set(model, next),
                    move || setup.set(model, previous.clone()),
                )))
            }))
        },
    );
    let output = reads.clone();
    let count = starts.clone();
    registry.register("agent", Schema::Any, move |_, _| {
        let output = output.clone();
        let count = count.clone();
        Ok(Plugin::new("agent", move |setup| {
            setup.get(model)?;
            output.lock().unwrap().push(setup.to_async());
            count.fetch_add(1, Ordering::SeqCst);
            Ok(())
        }))
    });
    let mut loader = Loader::new(Context::new(), registry);
    run(loader.apply(tree(1, true))).unwrap();
    let provider = loader.id("model").unwrap();
    let consumer = loader.id("agent").unwrap();
    let active = reads.lock().unwrap()[0].clone();
    let old_value = active.get(model).unwrap();

    run(loader.apply(tree(2, true))).unwrap();
    assert_eq!(loader.id("model"), Some(provider));
    assert_eq!(loader.id("agent"), Some(consumer));
    assert_eq!(starts.load(Ordering::SeqCst), 1);
    assert_eq!(old_value["version"], 1);
    assert_eq!(active.get(model).unwrap()["version"], 2);

    run(loader.apply(tree(3, false))).unwrap();
    assert_eq!(loader.runtime().phase(consumer), Some(Phase::Inactive));
    assert!(active.get(model).is_err());
    run(loader.apply(tree(4, true))).unwrap();
    assert_eq!(loader.id("model"), Some(provider));
    assert_eq!(loader.id("agent"), Some(consumer));
    assert_eq!(starts.load(Ordering::SeqCst), 2);
    assert_eq!(reads.lock().unwrap()[1].get(model).unwrap()["version"], 4);
    run(loader.dispose()).unwrap();
}

#[test]
fn repeated_updates_use_live_handler_then_restart_adopts_new_recipe() {
    let model = ServiceKey::<Arc<AtomicU64>>::new("model");
    let mut registry = FactoryRegistry::new();
    registry.register("model", Schema::Any, move |config, _| {
        // Every preconstructed candidate has distinct state. An accepted update
        // must keep invoking the handler paired with the currently live state.
        let state = Arc::new(AtomicU64::new(config["version"].as_u64().unwrap()));
        let setup_state = state.clone();
        Ok(Plugin::new("model", move |setup| {
            setup.provide(model, setup_state.clone())?;
            Ok(())
        })
        .provides(model)
        .on_config_update(move |_, previous, next| {
            let forward = state.clone();
            let restore = state.clone();
            let previous = previous["version"].as_u64().unwrap();
            let next = next["version"].as_u64().unwrap();
            Ok(ConfigUpdate::Apply(ConfigUpdatePlan::new(
                move || {
                    forward.store(next, Ordering::SeqCst);
                    Ok(())
                },
                move || {
                    restore.store(previous, Ordering::SeqCst);
                    Ok(())
                },
            )))
        }))
    });
    let config = |version| {
        ConfigTree::from_json(
            &json!([{"id":"model","name":"model","config":{"version":version}}]).to_string(),
        )
        .unwrap()
    };
    let context = Context::new();
    let mut loader = Loader::new(context.clone(), registry);
    run(loader.apply(config(1))).unwrap();
    let owner = loader.id("model").unwrap();
    let first = loader.runtime().get(&context, model).unwrap();
    run(loader.apply(config(2))).unwrap();
    run(loader.apply(config(3))).unwrap();
    assert_eq!(first.load(Ordering::SeqCst), 3);
    assert_eq!(loader.id("model"), Some(owner));
    loader.runtime_mut().restart(owner).unwrap();
    run(loader.runtime_mut().settle()).unwrap();
    let restarted = loader.runtime().get(&context, model).unwrap();
    assert!(!Arc::ptr_eq(&first, &restarted));
    assert_eq!(restarted.load(Ordering::SeqCst), 3);
    run(loader.apply(config(4))).unwrap();
    assert_eq!(restarted.load(Ordering::SeqCst), 4);
    assert_eq!(first.load(Ordering::SeqCst), 3);
    run(loader.dispose()).unwrap();
}
