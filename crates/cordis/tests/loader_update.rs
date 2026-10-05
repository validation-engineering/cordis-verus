use cordis::config::{ConfigUpdate, ConfigUpdatePlan, Field, Schema};
use cordis::loader::{ConfigTree, Entry, FactoryRegistry, Loader, LoaderError};
use cordis::{Context, Phase, Plugin, ServiceKey};
use serde_json::{json, Value};
use std::future::{poll_fn, Future};
use std::pin::Pin;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::task::{Context as TaskContext, Poll, Waker};

fn poll<F: Future>(future: Pin<&mut F>) -> Poll<F::Output> {
    future.poll(&mut TaskContext::from_waker(Waker::noop()))
}
fn run<F: Future>(future: F) -> F::Output {
    let mut future = Box::pin(future);
    for _ in 0..10_000 {
        if let Poll::Ready(result) = poll(future.as_mut()) {
            return result;
        }
    }
    panic!("future did not settle");
}
fn schema() -> Schema {
    Schema::object([("value", Field::required(Schema::integer(0, 100)))])
}
fn tree(value: usize) -> ConfigTree {
    ConfigTree {
        entries: vec![Entry::plugin("worker", "worker", json!({"value": value}))],
    }
}

#[test]
fn accepted_updates_keep_owner_children_and_live_handler_then_restart_latest_recipe() {
    let context = Context::new();
    let key = ServiceKey::<AtomicUsize>::new("setting");
    let starts = Arc::new(AtomicUsize::new(0));
    let mut registry = FactoryRegistry::new();
    let starts_in = starts.clone();
    registry.register("worker", schema(), move |config, _| {
        let initial = config["value"].as_u64().unwrap() as usize;
        // Each factory invocation owns distinct state. Replacing the active hook
        // with this new recipe's hook would update the wrong instance next time.
        let state = Arc::new(AtomicUsize::new(initial));
        let start_state = state.clone();
        let starts = starts_in.clone();
        Ok(Plugin::new("worker", move |setup| {
            starts.fetch_add(1, Ordering::SeqCst);
            setup.provide(key, AtomicUsize::new(start_state.load(Ordering::SeqCst)))?;
            Ok(())
        })
        .provides(key)
        .on_config_update(move |setup, previous, next| {
            let before = previous["value"].as_u64().unwrap() as usize;
            let after = next["value"].as_u64().unwrap() as usize;
            let payload = setup.get(key)?;
            let rollback_payload = payload.clone();
            let forward = state.clone();
            let backward = state.clone();
            Ok(ConfigUpdate::Apply(ConfigUpdatePlan::new(
                move || {
                    // The live closure's state must match the committed config.
                    assert_eq!(forward.load(Ordering::SeqCst), before);
                    forward.store(after, Ordering::SeqCst);
                    payload.store(after, Ordering::SeqCst);
                    Ok(())
                },
                move || {
                    backward.store(before, Ordering::SeqCst);
                    rollback_payload.store(before, Ordering::SeqCst);
                    Ok(())
                },
            )))
        }))
    });
    let mut loader = Loader::new(context.clone(), registry);
    let mut initial = tree(1);
    initial.entries[0]
        .children
        .push(Entry::group("child", vec![]));
    run(loader.apply(initial.clone())).unwrap();
    let owner = loader.id("worker").unwrap();
    let child = loader.id("worker/child");
    for value in [2, 3] {
        let mut next = initial.clone();
        next.entries[0].config = json!({"value": value});
        let report = run(loader.apply(next)).unwrap();
        assert_eq!(report.updated, ["worker"]);
        assert_eq!(loader.id("worker"), Some(owner));
        assert_eq!(loader.id("worker/child"), child);
        assert_eq!(
            loader
                .runtime()
                .get(&context, key)
                .unwrap()
                .load(Ordering::SeqCst),
            value
        );
    }
    assert_eq!(starts.load(Ordering::SeqCst), 1);
    loader.runtime_mut().restart(owner).unwrap();
    run(loader.reload()).unwrap();
    assert_eq!(loader.id("worker"), Some(owner));
    assert_eq!(starts.load(Ordering::SeqCst), 2);
    assert_eq!(
        loader
            .runtime()
            .get(&context, key)
            .unwrap()
            .load(Ordering::SeqCst),
        3
    );
    let mut next = initial;
    next.entries[0].config = json!({"value": 4});
    run(loader.apply(next)).unwrap();
    assert_eq!(
        loader
            .runtime()
            .get(&context, key)
            .unwrap()
            .load(Ordering::SeqCst),
        4
    );
}

fn counting_registry(plans: Arc<AtomicUsize>, applies: Arc<AtomicUsize>) -> FactoryRegistry {
    let mut registry = FactoryRegistry::new();
    registry.register("worker", schema(), move |_, _| {
        let (plans, applies) = (plans.clone(), applies.clone());
        Ok(
            Plugin::new("worker", |_| Ok(())).on_config_update(move |_, _, _| {
                plans.fetch_add(1, Ordering::SeqCst);
                let applies = applies.clone();
                Ok(ConfigUpdate::Apply(ConfigUpdatePlan::new(
                    move || {
                        applies.fetch_add(1, Ordering::SeqCst);
                        Ok(())
                    },
                    || Ok(()),
                )))
            }),
        )
    });
    registry
}

#[test]
fn full_validation_and_factory_construction_precede_update_planning() {
    let plans = Arc::new(AtomicUsize::new(0));
    let applies = Arc::new(AtomicUsize::new(0));
    let mut loader = Loader::new(
        Context::new(),
        counting_registry(plans.clone(), applies.clone()),
    );
    run(loader.apply(tree(1))).unwrap();
    assert!(run(loader.apply(tree(101))).is_err());
    loader
        .registry_mut()
        .register("bad", Schema::Any, |_, _| Err("construction failed".into()));
    let mut next = tree(2);
    next.entries.push(Entry::plugin("bad", "bad", json!({})));
    assert!(run(loader.apply(next)).is_err());
    assert_eq!(plans.load(Ordering::SeqCst), 0);
    assert_eq!(applies.load(Ordering::SeqCst), 0);
    assert_eq!(loader.tree(), &tree(1));
}

#[test]
fn unrelated_setup_failure_does_not_start_preplanned_updates() {
    let plans = Arc::new(AtomicUsize::new(0));
    let applies = Arc::new(AtomicUsize::new(0));
    let mut loader = Loader::new(
        Context::new(),
        counting_registry(plans.clone(), applies.clone()),
    );
    run(loader.apply(tree(1))).unwrap();
    let id = loader.id("worker");
    loader.registry_mut().register("bad", Schema::Any, |_, _| {
        Ok(Plugin::new("bad", |_| Err("setup failed".into())))
    });
    let mut next = tree(2);
    next.entries.push(Entry::plugin("bad", "bad", json!({})));
    assert!(matches!(
        run(loader.apply(next)),
        Err(LoaderError::Apply { rollback: None, .. })
    ));
    assert_eq!(plans.load(Ordering::SeqCst), 1);
    assert_eq!(applies.load(Ordering::SeqCst), 0);
    assert_eq!(loader.tree(), &tree(1));
    assert_eq!(loader.id("worker"), id);
}

#[test]
fn failure_rolls_back_started_updates_in_reverse_and_skips_later_plans() {
    let trace = Arc::new(Mutex::new(Vec::new()));
    let mut registry = FactoryRegistry::new();
    for name in ["a", "b", "c"] {
        let trace = trace.clone();
        registry.register(name, schema(), move |_, _| {
            let trace = trace.clone();
            Ok(
                Plugin::new(name, |_| Ok(())).on_config_update(move |_, _, _| {
                    let apply = trace.clone();
                    let undo = trace.clone();
                    Ok(ConfigUpdate::Apply(ConfigUpdatePlan::new(
                        move || {
                            apply.lock().unwrap().push(format!("apply:{name}"));
                            if name == "b" {
                                Err("partial apply failed".into())
                            } else {
                                Ok(())
                            }
                        },
                        move || {
                            undo.lock().unwrap().push(format!("undo:{name}"));
                            Ok(())
                        },
                    )))
                }),
            )
        });
    }
    let make = |value| ConfigTree {
        entries: ["a", "b", "c"]
            .into_iter()
            .map(|name| Entry::plugin(name, name, json!({"value": value})))
            .collect(),
    };
    let mut loader = Loader::new(Context::new(), registry);
    run(loader.apply(make(1))).unwrap();
    let ids = loader.runtime().ids();
    assert!(matches!(
        run(loader.apply(make(2))),
        Err(LoaderError::Apply { rollback: None, .. })
    ));
    assert_eq!(
        *trace.lock().unwrap(),
        ["apply:a", "apply:b", "undo:b", "undo:a"]
    );
    assert_eq!(loader.runtime().ids(), ids);
    assert_eq!(loader.tree(), &make(1));
}

#[test]
fn cancelled_apply_lands_before_inverse_and_failed_inverse_is_retryable() {
    let gate = Arc::new(AtomicBool::new(false));
    let value = Arc::new(AtomicUsize::new(1));
    let applied = Arc::new(AtomicUsize::new(0));
    let rollbacks = Arc::new(AtomicUsize::new(0));
    let mut registry = FactoryRegistry::new();
    let (g, v, a, r) = (
        gate.clone(),
        value.clone(),
        applied.clone(),
        rollbacks.clone(),
    );
    registry.register("worker", schema(), move |_, _| {
        let (gate, value, applied, rollbacks) = (g.clone(), v.clone(), a.clone(), r.clone());
        Ok(
            Plugin::new("worker", |_| Ok(())).on_config_update(move |_, previous, next| {
                let before = previous["value"].as_u64().unwrap() as usize;
                let after = next["value"].as_u64().unwrap() as usize;
                let (gate, apply_value, applied) = (gate.clone(), value.clone(), applied.clone());
                let (undo_value, rollbacks) = (value.clone(), rollbacks.clone());
                Ok(ConfigUpdate::Apply(ConfigUpdatePlan::new_async(
                    move || async move {
                        applied.fetch_add(1, Ordering::SeqCst);
                        poll_fn(|_| {
                            if gate.load(Ordering::SeqCst) {
                                Poll::Ready(())
                            } else {
                                Poll::Pending
                            }
                        })
                        .await;
                        apply_value.store(after, Ordering::SeqCst);
                        Ok(())
                    },
                    move || {
                        let (undo_value, rollbacks) = (undo_value.clone(), rollbacks.clone());
                        async move {
                            if rollbacks.fetch_add(1, Ordering::SeqCst) == 0 {
                                return Err("temporary rollback failure".into());
                            }
                            undo_value.store(before, Ordering::SeqCst);
                            Ok(())
                        }
                    },
                )))
            }),
        )
    });
    let mut loader = Loader::new(Context::new(), registry);
    run(loader.apply(tree(1))).unwrap();
    let mut change = Box::pin(loader.apply(tree(2)));
    assert!(poll(change.as_mut()).is_pending());
    drop(change);
    assert!(loader.recovery_pending());
    assert_eq!(applied.load(Ordering::SeqCst), 1);
    let mut recovery = Box::pin(loader.recover());
    assert!(poll(recovery.as_mut()).is_pending());
    drop(recovery);
    assert_eq!(rollbacks.load(Ordering::SeqCst), 0);
    gate.store(true, Ordering::SeqCst);
    assert!(run(loader.recover()).is_err());
    assert_eq!(value.load(Ordering::SeqCst), 2);
    assert!(loader.recovery_pending());
    run(loader.recover()).unwrap();
    assert_eq!(value.load(Ordering::SeqCst), 1);
    assert_eq!(applied.load(Ordering::SeqCst), 1);
    assert_eq!(rollbacks.load(Ordering::SeqCst), 2);
    assert_eq!(loader.tree(), &tree(1));
}

#[test]
fn explicit_restart_and_declaration_changes_fall_back_to_replacement() {
    let plans = Arc::new(AtomicUsize::new(0));
    let mut registry = FactoryRegistry::new();
    let calls = plans.clone();
    let key = ServiceKey::<usize>::new("conditional");
    registry.register("worker", schema(), move |config, _| {
        let conditional = config["value"] == 3;
        let calls = calls.clone();
        let plugin = Plugin::new("worker", move |setup| {
            if conditional {
                setup.provide(key, 3)?;
            }
            Ok(())
        })
        .on_config_update(move |_, _, _| {
            calls.fetch_add(1, Ordering::SeqCst);
            Ok(ConfigUpdate::Restart)
        });
        Ok(if conditional {
            plugin.provides(key)
        } else {
            plugin
        })
    });
    let mut loader = Loader::new(Context::new(), registry);
    run(loader.apply(tree(1))).unwrap();
    let first = loader.id("worker");
    assert!(run(loader.apply(tree(2))).unwrap().updated.is_empty());
    assert_ne!(loader.id("worker"), first);
    assert_eq!(plans.load(Ordering::SeqCst), 1);
    run(loader.apply(tree(3))).unwrap();
    assert_eq!(plans.load(Ordering::SeqCst), 1);
}

#[test]
fn changed_provider_forces_consumer_replacement_without_stale_update_plan() {
    let key = ServiceKey::<usize>::new("model");
    let plans = Arc::new(AtomicUsize::new(0));
    let applies = Arc::new(AtomicUsize::new(0));
    let mut registry = counting_registry(plans.clone(), applies.clone());
    registry.register_service("model", key);
    registry.register("provider", schema(), move |config, _| {
        let value = config["value"].as_u64().unwrap() as usize;
        Ok(Plugin::new("provider", move |setup| {
            setup.provide(key, value)?;
            Ok(())
        })
        .provides(key))
    });
    let make = |value| {
        let mut tree = tree(value);
        tree.entries[0].inject.push("model".into());
        tree.entries.insert(
            0,
            Entry::plugin("model", "provider", json!({"value": value})),
        );
        tree
    };
    let mut loader = Loader::new(Context::new(), registry);
    run(loader.apply(make(1))).unwrap();
    let old = loader.id("worker");
    run(loader.apply(make(2))).unwrap();
    assert_ne!(loader.id("worker"), old);
    assert_eq!(plans.load(Ordering::SeqCst), 0);
    assert_eq!(applies.load(Ordering::SeqCst), 0);
}

#[test]
fn injection_object_config_reaches_predicate_and_scope_with_child_override() {
    let key = ServiceKey::<usize>::new("model");
    let mut registry = FactoryRegistry::new();
    registry.register_service("model", key);
    registry.register("model", Schema::Any, move |_, _| {
        Ok(Plugin::new("model", move |setup| {
            setup.provide_checked(key, 7, |_, _, config| {
                config.is_null() || config["capability"] == "chat"
            })?;
            Ok(())
        })
        .provides(key))
    });
    registry.register("consumer", Schema::Any, |_, scope| {
        assert!(scope.injection("model").is_some());
        Ok(Plugin::new("consumer", |_| Ok(())))
    });
    let tree = ConfigTree::from_json(
        r#"[
        {"id":"model","name":"model"},
        {"id":"group","inject":["model"],"children":[
            {"id":"allowed","name":"consumer","inject":{"model":{"capability":"chat"}}},
            {"id":"denied","name":"consumer","inject":{"model":{"capability":"image"}}}
        ]}
    ]"#,
    )
    .unwrap();
    assert_eq!(tree.entries[1].inject.get("model"), Some(&Value::Null));
    assert_eq!(
        ConfigTree::from_json(&tree.to_json().unwrap()).unwrap(),
        tree
    );
    let mut loader = Loader::new(Context::new(), registry);
    run(loader.apply(tree)).unwrap();
    assert_eq!(
        loader.runtime().phase(loader.id("group/allowed").unwrap()),
        Some(Phase::Active)
    );
    assert_eq!(
        loader.runtime().phase(loader.id("group/denied").unwrap()),
        Some(Phase::Inactive)
    );
    assert_eq!(
        loader.scope("group/allowed").unwrap().injection("model"),
        Some(&json!({"capability":"chat"}))
    );
    assert_eq!(
        loader.scope("group").unwrap().injection("model"),
        Some(&Value::Null)
    );
}

#[test]
fn post_commit_activation_failure_reports_accepted_configuration() {
    let key = ServiceKey::<bool>::new("availability");
    let mut registry = FactoryRegistry::new();
    registry.register_service("availability", key);
    registry.register("provider", Schema::Boolean, move |config, _| {
        let enabled = config.as_bool().unwrap();
        Ok(Plugin::new("provider", move |setup| {
            setup.provide_checked(key, enabled, |enabled, _, _| *enabled)?;
            Ok(())
        })
        .provides(key)
        .on_config_update(move |setup, before, after| {
            let forward = setup.clone();
            Ok(ConfigUpdate::Apply(ConfigUpdatePlan::new(
                move || forward.set(key, after.as_bool().unwrap()),
                move || setup.set(key, before.as_bool().unwrap()),
            )))
        }))
    });
    registry.register("consumer", Schema::Any, |_, _| {
        Ok(Plugin::new("consumer", |_| Err("activation failed".into())))
    });
    let make = |enabled| {
        ConfigTree::from_json(
            &json!([
                {"id":"provider","name":"provider","config":enabled},
                {"id":"consumer","name":"consumer","inject":["availability"]}
            ])
            .to_string(),
        )
        .unwrap()
    };
    let mut loader = Loader::new(Context::new(), registry);
    run(loader.apply(make(false))).unwrap();
    let id = loader.id("provider");
    assert!(matches!(
        run(loader.apply(make(true))),
        Err(LoaderError::PostCommit { revision: 2, .. })
    ));
    assert_eq!(loader.tree(), &make(true));
    assert_eq!(loader.revision(), 2);
    assert_eq!(loader.id("provider"), id);
    assert!(!loader.recovery_pending());
    run(loader.recover()).unwrap();
    assert_eq!(loader.tree(), &make(true));
}

#[test]
fn cancellation_during_post_commit_propagation_keeps_config_and_reconciles_children() {
    let key = ServiceKey::<bool>::new("availability");
    let gate = Arc::new(AtomicBool::new(false));
    let mut registry = FactoryRegistry::new();
    registry.register_service("availability", key);
    registry.register("provider", Schema::Boolean, move |config, _| {
        let enabled = config.as_bool().unwrap();
        Ok(Plugin::new("provider", move |setup| {
            setup.provide_checked(key, enabled, |enabled, _, _| *enabled)?;
            Ok(())
        })
        .provides(key)
        .on_config_update(move |setup, before, after| {
            let forward = setup.clone();
            Ok(ConfigUpdate::Apply(ConfigUpdatePlan::new(
                move || forward.set(key, after.as_bool().unwrap()),
                move || setup.set(key, before.as_bool().unwrap()),
            )))
        }))
    });
    let cleanup_gate = gate.clone();
    registry.register("consumer", Schema::Any, move |_, _| {
        let gate = cleanup_gate.clone();
        Ok(Plugin::new("consumer", move |setup| {
            let gate = gate.clone();
            setup.on_cleanup_async(move || async move {
                poll_fn(|_| {
                    if gate.load(Ordering::SeqCst) {
                        Poll::Ready(())
                    } else {
                        Poll::Pending
                    }
                })
                .await;
                Ok(())
            });
            Ok(())
        }))
    });
    let make = |enabled| {
        ConfigTree::from_json(&json!([
        {"id":"provider","name":"provider","config":enabled},
        {"id":"consumer","name":"consumer","inject":["availability"],"children":[{"id":"child"}]}
    ]).to_string()).unwrap()
    };
    let mut loader = Loader::new(Context::new(), registry);
    let source =
        std::env::temp_dir().join(format!("cordis-update-source-{}.json", std::process::id()));
    std::fs::write(&source, make(true).to_json().unwrap()).unwrap();
    run(loader.load_file(&source)).unwrap();
    assert_eq!(loader.watched_files().count(), 1);
    let previous_child = loader.id("consumer/child");
    let json = make(false).to_json().unwrap();
    let mut change = Box::pin(loader.load_json(&json));
    assert!(poll(change.as_mut()).is_pending());
    drop(change);
    assert!(!loader.recovery_pending());
    assert_eq!(loader.watched_files().count(), 0);
    std::fs::remove_file(source).unwrap();
    assert_eq!(loader.tree(), &make(false));
    gate.store(true, Ordering::SeqCst);
    run(loader.reload()).unwrap();
    let child = loader.id("consumer/child").unwrap();
    assert_ne!(Some(child), previous_child);
    assert_eq!(loader.runtime().phase(child), Some(Phase::Inactive));
    assert_eq!(loader.tree(), &make(false));
}

#[test]
fn replaced_dynamic_service_owner_forces_dependent_update_to_restart() {
    let key = ServiceKey::<usize>::new("dynamic-model");
    let plans = Arc::new(AtomicUsize::new(0));
    let applies = Arc::new(AtomicUsize::new(0));
    let mut registry = counting_registry(plans.clone(), applies.clone());
    registry.register_service("model", key);
    registry.register("provider", schema(), move |config, _| {
        let value = config["value"].as_u64().unwrap() as usize;
        Ok(Plugin::new("provider", move |setup| {
            setup.publish(key, value)?;
            Ok(())
        }))
    });
    let make = |value| {
        let mut tree = tree(value);
        tree.entries[0].inject.push("model".into());
        tree.entries.insert(
            0,
            Entry::plugin("model", "provider", json!({"value": value})),
        );
        tree
    };
    let mut loader = Loader::new(Context::new(), registry);
    run(loader.apply(make(1))).unwrap();
    let old = loader.id("worker");
    assert_eq!(loader.runtime().ids().len(), 3);
    run(loader.apply(make(2))).unwrap();
    assert_ne!(loader.id("worker"), old);
    assert_eq!(plans.load(Ordering::SeqCst), 0);
    assert_eq!(applies.load(Ordering::SeqCst), 0);
    assert_eq!(loader.runtime().ids().len(), 3);
}
