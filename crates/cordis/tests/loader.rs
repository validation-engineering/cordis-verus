use cordis::config::{Field, Schema};
use cordis::loader::{ConfigTree, Entry, FactoryRegistry, Loader, LoaderError};
use cordis::{Context, Phase, Plugin, ServiceKey};
use serde_json::{json, Value};
use std::future::Future;
use std::path::PathBuf;
use std::pin::Pin;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::task::{Context as TaskContext, Poll, Waker};

fn poll<F: Future>(future: Pin<&mut F>) -> Poll<F::Output> {
    let waker = Waker::noop();
    future.poll(&mut TaskContext::from_waker(waker))
}
fn run<F: Future>(future: F) -> F::Output {
    let mut future = Box::pin(future);
    for _ in 0..10000 {
        if let Poll::Ready(result) = poll(future.as_mut()) {
            return result;
        }
        std::thread::yield_now();
    }
    panic!("future did not finish");
}
type Log = Arc<Mutex<Vec<String>>>;
fn schema() -> Schema {
    Schema::object([("value", Field::defaulted(Schema::integer(0, 100), 1))])
}
fn registry(log: &Log) -> FactoryRegistry {
    let mut registry = FactoryRegistry::new();
    let log = log.clone();
    registry.register("worker", schema(), move |config, _| {
        let value = config["value"].as_i64().unwrap();
        let log = log.clone();
        Ok(Plugin::new("worker", move |setup| {
            log.lock().unwrap().push(format!("start:{value}"));
            let log = log.clone();
            setup.on_cleanup(move || {
                log.lock().unwrap().push(format!("stop:{value}"));
                Ok(())
            });
            if value == 13 {
                return Err("unlucky setup".into());
            }
            Ok(())
        }))
    });
    registry
}
fn tree(value: i64) -> ConfigTree {
    ConfigTree {
        entries: vec![
            Entry::group(
                "group",
                vec![Entry::plugin("worker", "worker", json!({"value":value}))],
            ),
            Entry::plugin("unrelated", "worker", json!({"value":9})),
        ],
    }
}

#[test]
fn unchanged_nodes_keep_ids_and_only_changed_subtrees_are_revised() {
    let log = Log::default();
    let mut loader = Loader::new(Context::new(), registry(&log));
    run(loader.apply(tree(1))).unwrap();
    let group = loader.id("group").unwrap();
    let old = loader.id("group/worker").unwrap();
    let unrelated = loader.id("unrelated").unwrap();
    let report = run(loader.apply(tree(1))).unwrap();
    assert!(report.is_unchanged());
    assert_eq!(report.retained, 3);
    assert_eq!(log.lock().unwrap().len(), 2);
    let report = run(loader.apply(tree(2))).unwrap();
    assert_eq!(report.changed, vec!["group/worker"]);
    assert_eq!(loader.id("group"), Some(group));
    assert_eq!(loader.id("unrelated"), Some(unrelated));
    assert!(loader.id("group/worker").unwrap() > old);
    assert!(!loader.runtime().contains(old));
    assert_eq!(
        *log.lock().unwrap(),
        vec!["start:1", "start:9", "stop:1", "start:2"]
    );
    run(loader.dispose()).unwrap();
    assert!(loader.runtime().ids().is_empty());
}

#[test]
fn validation_and_all_factory_construction_precede_retirement() {
    let log = Log::default();
    let mut loader = Loader::new(Context::new(), registry(&log));
    run(loader.apply(tree(1))).unwrap();
    let old = loader.id("group/worker");
    let mut invalid = tree(2);
    invalid
        .entries
        .push(Entry::plugin("bad", "worker", json!({"typo":1})));
    assert!(run(loader.apply(invalid)).is_err());
    loader
        .registry_mut()
        .register("broken", Schema::Any, |_, _| Err("cannot construct".into()));
    let mut failed = tree(2);
    failed
        .entries
        .push(Entry::plugin("bad", "broken", json!({})));
    assert!(matches!(
        run(loader.apply(failed)),
        Err(LoaderError::Factory { .. })
    ));
    assert_eq!(loader.id("group/worker"), old);
    assert_eq!(loader.tree(), &tree(1));
    assert_eq!(log.lock().unwrap().len(), 2);
    assert!(!loader.recovery_pending());
}

#[test]
fn failed_setup_cleans_new_resources_and_restores_old_recipe() {
    let log = Log::default();
    let mut loader = Loader::new(Context::new(), registry(&log));
    run(loader.apply(tree(1))).unwrap();
    let old = loader.id("group/worker").unwrap();
    let unrelated = loader.id("unrelated");
    assert!(matches!(
        run(loader.apply(tree(13))),
        Err(LoaderError::Apply { rollback: None, .. })
    ));
    assert_eq!(loader.tree(), &tree(1));
    assert_eq!(loader.id("unrelated"), unrelated);
    assert!(loader.id("group/worker").unwrap() > old);
    assert_eq!(loader.runtime().ids().len(), 3);
    assert_eq!(
        *log.lock().unwrap(),
        vec!["start:1", "start:9", "stop:1", "start:13", "stop:13", "start:1"]
    );
    assert!(!loader.recovery_pending());
    run(loader.apply(tree(2))).unwrap();
}

#[test]
fn code_revision_restores_captured_factory_when_new_setup_fails() {
    let log = Log::default();
    let mut loader = Loader::new(Context::new(), registry(&log));
    run(loader.apply(tree(1))).unwrap();
    loader.registry_mut().register("worker", schema(), |_, _| {
        Ok(Plugin::new(
            "broken code",
            |_| Err("new code failed".into()),
        ))
    });
    assert!(matches!(
        run(loader.reload()),
        Err(LoaderError::Apply { rollback: None, .. })
    ));
    assert_eq!(
        loader.runtime().phase(loader.id("group/worker").unwrap()),
        Some(Phase::Active)
    );
    assert_eq!(
        loader.runtime().name(loader.id("group/worker").unwrap()),
        Some("worker")
    );
    assert_eq!(loader.runtime().ids().len(), 3);
    assert!(!loader.recovery_pending());
    loader.registry_mut().register("worker", schema(), |_, _| {
        Ok(Plugin::new("new code", |_| Ok(())))
    });
    let before = loader.id("group/worker").unwrap();
    run(loader.reload()).unwrap();
    assert!(loader.id("group/worker").unwrap() > before);
    assert_eq!(
        loader.runtime().name(loader.id("group/worker").unwrap()),
        Some("new code")
    );
    assert!(run(loader.reload()).unwrap().is_unchanged());
}

#[derive(Default)]
struct Gate {
    open: AtomicBool,
    waker: Mutex<Option<Waker>>,
}
impl Gate {
    fn release(&self) {
        self.open.store(true, Ordering::SeqCst);
        if let Some(waker) = self.waker.lock().unwrap().take() {
            waker.wake();
        }
    }
}
struct Wait(Arc<Gate>);
impl Future for Wait {
    type Output = ();
    fn poll(self: Pin<&mut Self>, cx: &mut TaskContext<'_>) -> Poll<()> {
        if self.0.open.load(Ordering::SeqCst) {
            Poll::Ready(())
        } else {
            *self.0.waker.lock().unwrap() = Some(cx.waker().clone());
            Poll::Pending
        }
    }
}
fn slow_registry(
    gate: Arc<Gate>,
    starts: Arc<AtomicUsize>,
    stops: Arc<AtomicUsize>,
) -> FactoryRegistry {
    let mut registry = FactoryRegistry::new();
    registry.register("slow", Schema::Any, move |_, _| {
        let (gate, starts, stops) = (gate.clone(), starts.clone(), stops.clone());
        Ok(Plugin::new("slow", move |setup| {
            let (gate, starts, stops) = (gate.clone(), starts.clone(), stops.clone());
            setup.on_cleanup_async(move || async move {
                starts.fetch_add(1, Ordering::SeqCst);
                Wait(gate).await;
                stops.fetch_add(1, Ordering::SeqCst);
                Ok(())
            });
            Ok(())
        }))
    });
    registry
}

#[test]
fn group_disable_waits_for_all_concurrent_children_and_is_idempotent() {
    let gate = Arc::new(Gate::default());
    let starts = Arc::new(AtomicUsize::new(0));
    let stops = Arc::new(AtomicUsize::new(0));
    let mut loader = Loader::new(
        Context::new(),
        slow_registry(gate.clone(), starts.clone(), stops.clone()),
    );
    let config = ConfigTree {
        entries: vec![Entry::group(
            "g",
            vec![
                Entry::plugin("a", "slow", json!({})),
                Entry::plugin("b", "slow", json!({})),
            ],
        )],
    };
    run(loader.apply(config)).unwrap();
    let mut disable = Box::pin(loader.set_enabled("g", false));
    assert!(poll(disable.as_mut()).is_pending());
    assert_eq!(starts.load(Ordering::SeqCst), 2);
    assert_eq!(stops.load(Ordering::SeqCst), 0);
    gate.release();
    assert!(matches!(poll(disable.as_mut()), Poll::Ready(Ok(_))));
    drop(disable);
    assert_eq!(stops.load(Ordering::SeqCst), 2);
    assert!(loader.runtime().ids().is_empty());
    assert!(run(loader.set_enabled("g", false)).unwrap().is_unchanged());
    run(loader.set_enabled("g", true)).unwrap();
    assert_eq!(loader.runtime().ids().len(), 3);
}

#[test]
fn cancelled_disable_recovers_with_fresh_ids_after_cleanup() {
    let gate = Arc::new(Gate::default());
    let starts = Arc::new(AtomicUsize::new(0));
    let stops = Arc::new(AtomicUsize::new(0));
    let mut loader = Loader::new(
        Context::new(),
        slow_registry(gate.clone(), starts.clone(), stops.clone()),
    );
    let config = ConfigTree {
        entries: vec![Entry::plugin("a", "slow", json!({}))],
    };
    run(loader.apply(config.clone())).unwrap();
    let old = loader.id("a").unwrap();
    {
        let mut disable = Box::pin(loader.set_enabled("a", false));
        assert!(poll(disable.as_mut()).is_pending());
    }
    assert!(loader.recovery_pending());
    assert_eq!(
        loader.prepare_save().unwrap_err().kind,
        cordis::persistence::SaveErrorKind::RecoveryPending
    );
    assert!(loader.runtime().retired(old));
    {
        let mut recovery = Box::pin(loader.recover());
        assert!(poll(recovery.as_mut()).is_pending());
    }
    gate.release();
    run(loader.recover()).unwrap();
    assert!(!loader.recovery_pending());
    assert_eq!(loader.tree(), &config);
    assert!(loader.id("a").unwrap() > old);
    assert_eq!(starts.load(Ordering::SeqCst), 1);
    assert_eq!(stops.load(Ordering::SeqCst), 1);
    assert_eq!(loader.runtime().ids().len(), 1);
}

#[test]
fn scopes_isolate_services_inherit_injection_and_apply_interception() {
    let service = ServiceKey::<i64>::new("model");
    let values = Arc::new(Mutex::new(Vec::new()));
    let mut registry = FactoryRegistry::new();
    registry.register_service("model", service);
    registry.register("model", schema(), move |config, scope| {
        assert!(scope.json_metadata("tenant").is_some());
        let value = config["value"].as_i64().unwrap();
        Ok(Plugin::new("model", move |setup| {
            setup.provide(service, value)?;
            Ok(())
        })
        .provides(service))
    });
    let observed = values.clone();
    registry.register("agent", Schema::Any, move |_, _| {
        let observed = observed.clone();
        Ok(Plugin::new("agent", move |setup| {
            observed.lock().unwrap().push(*setup.get(service)?);
            Ok(())
        }))
    });
    let mut alpha = Entry::group(
        "alpha",
        vec![
            Entry::plugin("provider", "model", json!({"value":1})),
            Entry::group("agents", vec![Entry::plugin("worker", "agent", json!({}))]),
        ],
    );
    alpha.isolate.push("model".into());
    alpha.metadata.insert("tenant".into(), json!("alpha"));
    alpha.intercept.insert("model".into(), json!({"value":7}));
    alpha.children[1].inject.push("model".into());
    let mut beta = alpha.clone();
    beta.id = "beta".into();
    beta.intercept.insert("model".into(), json!({"value":8}));
    beta.metadata.insert("tenant".into(), json!("beta"));
    let root = Context::new();
    let mut loader = Loader::new(root.clone(), registry);
    run(loader.apply(ConfigTree {
        entries: vec![alpha, beta],
    }))
    .unwrap();
    assert_eq!(*values.lock().unwrap(), vec![7, 8]);
    assert!(loader.runtime().get(&root, service).is_none());
    let alpha_scope = loader.scope("alpha").unwrap().context().clone();
    let beta_scope = loader.scope("beta").unwrap().context().clone();
    assert_ne!(alpha_scope.port(service), beta_scope.port(service));
    assert_eq!(*loader.runtime().get(&alpha_scope, service).unwrap(), 7);
    assert_eq!(*loader.runtime().get(&beta_scope, service).unwrap(), 8);
    let consumer = loader.id("alpha/agents/worker").unwrap();
    assert_eq!(
        loader.runtime().committed(consumer)[0].provider,
        loader.id("alpha/provider").unwrap()
    );
    assert!(run(loader.reload()).unwrap().is_unchanged());
    assert_eq!(
        alpha_scope.port(service),
        loader.scope("alpha").unwrap().context().port(service)
    );
}

static NEXT_DIR: AtomicUsize = AtomicUsize::new(0);
struct Files(PathBuf);
impl Files {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "cordis-loader-{}-{}",
            std::process::id(),
            NEXT_DIR.fetch_add(1, Ordering::SeqCst)
        ));
        std::fs::create_dir_all(&path).unwrap();
        Self(path)
    }
    fn write(&self, name: &str, value: Value) {
        std::fs::write(self.0.join(name), value.to_string()).unwrap();
    }
}
impl Drop for Files {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[test]
fn include_poll_reload_reads_nested_content_and_preserves_invalid_file_state() {
    let files = Files::new();
    files.write("root.json",json!([{"id":"included","include":"child.json"},{"id":"untouched","name":"worker","config":{"value":9}}]));
    files.write(
        "child.json",
        json!([{"id":"child","name":"worker","config":{"value":1}}]),
    );
    let log = Log::default();
    let mut loader = Loader::new(Context::new(), registry(&log));
    run(loader.load_file(files.0.join("root.json"))).unwrap();
    assert_eq!(loader.watched_files().count(), 2);
    let child = loader.id("included/child").unwrap();
    let group = loader.id("included");
    let untouched = loader.id("untouched");
    assert!(run(loader.poll_reload()).unwrap().is_unchanged());
    files.write(
        "child.json",
        json!([{"id":"child","name":"worker","config":{"value":2}}]),
    );
    assert_eq!(
        run(loader.poll_reload()).unwrap().changed,
        vec!["included/child"]
    );
    let revised = loader.id("included/child").unwrap();
    assert!(revised > child);
    assert_eq!(loader.id("included"), group);
    assert_eq!(loader.id("untouched"), untouched);
    std::fs::write(files.0.join("child.json"), "invalid JSON").unwrap();
    assert!(run(loader.poll_reload()).is_err());
    assert_eq!(loader.id("included/child"), Some(revised));
    std::fs::remove_file(files.0.join("child.json")).unwrap();
    assert!(run(loader.poll_reload()).is_err());
    assert_eq!(loader.id("included/child"), Some(revised));
    files.write(
        "child.json",
        json!([{"id":"child","name":"worker","config":{"value":3}}]),
    );
    run(loader.poll_reload()).unwrap();
    assert!(loader.id("included/child").unwrap() > revised);
    assert_eq!(loader.id("untouched"), untouched);
}

#[test]
fn include_cycles_use_canonical_sources_and_duplicate_includes_are_scoped() {
    let files = Files::new();
    files.write("root.json", json!([{"id":"outer","include":"a.json"}]));
    files.write("a.json", json!([{"id":"inner","include":"./root.json"}]));
    let log = Log::default();
    let mut loader = Loader::new(Context::new(), registry(&log));
    assert!(matches!(
        run(loader.load_file(files.0.join("root.json"))),
        Err(LoaderError::IncludeCycle(_))
    ));
    assert!(loader.runtime().ids().is_empty());
    files.write("a.json", json!([{"id":"worker","name":"worker"}]));
    files.write(
        "root.json",
        json!([{"id":"a","include":"a.json"},{"id":"b","include":"./a.json"}]),
    );
    run(loader.load_file(files.0.join("root.json"))).unwrap();
    assert_ne!(loader.id("a/worker"), loader.id("b/worker"));
    assert_eq!(loader.watched_files().count(), 2);
}

#[test]
fn invalid_identifiers_unknown_services_and_unknown_factories_are_rejected() {
    let mut loader = Loader::new(Context::new(), FactoryRegistry::new());
    for text in [
        r#"[{"id":"same"},{"id":"same"}]"#,
        r#"[{"id":"a/b"}]"#,
        r#"[{"id":"unknown","name":"missing"}]"#,
        r#"[{"id":"unknown","inject":["missing"]}]"#,
        r#"[{"id":"unknown","isolate":["missing"]}]"#,
        r#"[{"id":"include","include":"file.json"}]"#,
    ] {
        assert!(run(loader.load_json(text)).is_err(), "{text}");
        assert!(loader.runtime().ids().is_empty());
    }
}

#[test]
fn missing_injection_keeps_entry_inactive_and_provider_arrival_activates_it() {
    let key = ServiceKey::<u32>::new("llm");
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = calls.clone();
    let mut registry = FactoryRegistry::new();
    registry.register_service("llm", key);
    registry.register("agent", Schema::Any, move |_, _| {
        let calls = observed.clone();
        Ok(Plugin::new("agent", move |setup| {
            assert_eq!(*setup.get(key)?, 42);
            calls.fetch_add(1, Ordering::SeqCst);
            Ok(())
        }))
    });
    registry.register("llm", Schema::Any, move |_, _| {
        Ok(Plugin::new("llm", move |setup| {
            setup.provide(key, 42)?;
            Ok(())
        })
        .provides(key))
    });
    let mut agent = Entry::plugin("agent", "agent", json!({}));
    agent.inject.push("llm".into());
    let mut tree = ConfigTree {
        entries: vec![agent],
    };
    let mut loader = Loader::new(Context::new(), registry);
    run(loader.apply(tree.clone())).unwrap();
    let id = loader.id("agent").unwrap();
    assert_eq!(loader.runtime().phase(id), Some(Phase::Inactive));
    tree.entries.push(Entry::plugin("model", "llm", json!({})));
    run(loader.apply(tree)).unwrap();
    assert_eq!(loader.id("agent"), Some(id));
    assert_eq!(loader.runtime().phase(id), Some(Phase::Active));
    assert_eq!(calls.load(Ordering::SeqCst), 1);
}

#[test]
fn cancelled_async_revision_reclaims_new_ids_and_restores_old_factory() {
    let log = Log::default();
    let mut loader = Loader::new(Context::new(), registry(&log));
    let config = ConfigTree {
        entries: vec![Entry::plugin("worker", "worker", json!({"value":1}))],
    };
    run(loader.apply(config.clone())).unwrap();
    let old = loader.id("worker").unwrap();
    let gate = Arc::new(Gate::default());
    let cleaned = Arc::new(AtomicUsize::new(0));
    let setup_gate = gate.clone();
    let setup_cleaned = cleaned.clone();
    loader
        .registry_mut()
        .register("worker", schema(), move |_, _| {
            let gate = setup_gate.clone();
            let cleaned = setup_cleaned.clone();
            Ok(Plugin::new_async("async replacement", move |setup| {
                let gate = gate.clone();
                let cleaned = cleaned.clone();
                async move {
                    setup.on_cleanup(move || {
                        cleaned.fetch_add(1, Ordering::SeqCst);
                        Ok(())
                    })?;
                    Wait(gate).await;
                    Ok(())
                }
            }))
        });
    {
        let mut revision = Box::pin(loader.reload());
        assert!(poll(revision.as_mut()).is_pending());
    }
    assert!(loader.recovery_pending());
    assert!(!loader.runtime().contains(old));
    let replacement = loader.runtime().ids()[0];
    gate.release();
    run(loader.recover()).unwrap();
    assert_eq!(loader.tree(), &config);
    assert!(!loader.runtime().contains(replacement));
    assert_eq!(
        loader.runtime().name(loader.id("worker").unwrap()),
        Some("worker")
    );
    assert_eq!(cleaned.load(Ordering::SeqCst), 1);
    assert_eq!(loader.runtime().ids().len(), 1);
}

#[test]
fn failed_rollback_remains_explicit_and_can_be_recovered_later() {
    let unavailable = Arc::new(AtomicBool::new(false));
    let factory_unavailable = unavailable.clone();
    let mut registry = FactoryRegistry::new();
    registry.register("worker", Schema::Any, move |_, _| {
        if factory_unavailable.load(Ordering::SeqCst) {
            return Err("factory temporarily unavailable".into());
        }
        Ok(Plugin::new("old worker", |_| Ok(())))
    });
    let mut loader = Loader::new(Context::new(), registry);
    let config = ConfigTree {
        entries: vec![Entry::plugin("worker", "worker", json!({}))],
    };
    run(loader.apply(config.clone())).unwrap();
    unavailable.store(true, Ordering::SeqCst);
    loader
        .registry_mut()
        .register("worker", Schema::Any, |_, _| {
            Ok(Plugin::new(
                "failed revision",
                |_| Err("setup fails".into()),
            ))
        });
    assert!(matches!(
        run(loader.reload()),
        Err(LoaderError::Apply {
            rollback: Some(_),
            ..
        })
    ));
    assert!(loader.recovery_pending());
    unavailable.store(false, Ordering::SeqCst);
    run(loader.recover()).unwrap();
    assert!(!loader.recovery_pending());
    assert_eq!(loader.tree(), &config);
    assert_eq!(
        loader.runtime().name(loader.id("worker").unwrap()),
        Some("old worker")
    );
}

#[test]
fn dispose_detaches_file_polling_and_does_not_resurrect_entries() {
    let files = Files::new();
    files.write("root.json", json!([{"id":"a","name":"worker"}]));
    let mut loader = Loader::new(Context::new(), registry(&Log::default()));
    run(loader.load_file(files.0.join("root.json"))).unwrap();
    run(loader.dispose()).unwrap();
    assert_eq!(loader.watched_files().count(), 0);
    assert!(run(loader.poll_reload()).unwrap().is_unchanged());
    assert!(loader.runtime().ids().is_empty());
}

#[test]
fn provider_revision_rebuilds_indirectly_retired_owned_children() {
    let key = ServiceKey::<i64>::new("model");
    let observations = Arc::new(Mutex::new(Vec::new()));
    let mut registry = FactoryRegistry::new();
    registry.register_service("model", key);
    registry.register("model", schema(), move |config, _| {
        let value = config["value"].as_i64().unwrap();
        Ok(Plugin::new("model", move |setup| {
            setup.provide(key, value)?;
            Ok(())
        })
        .provides(key))
    });
    for name in ["parent", "child"] {
        let observations = observations.clone();
        registry.register(name, Schema::Any, move |_, _| {
            let observations = observations.clone();
            Ok(Plugin::new(name, move |setup| {
                observations.lock().unwrap().push((name, *setup.get(key)?));
                Ok(())
            }))
        });
    }
    let mut owner = Entry::plugin("owner", "parent", json!({}));
    owner.inject.push("model".into());
    owner
        .children
        .push(Entry::plugin("child", "child", json!({})));
    let mut config = ConfigTree {
        entries: vec![Entry::plugin("model", "model", json!({"value":1})), owner],
    };
    let mut loader = Loader::new(Context::new(), registry);
    run(loader.apply(config.clone())).unwrap();
    let parent = loader.id("owner").unwrap();
    let old_child = loader.id("owner/child").unwrap();
    config.entries[0].config = json!({"value":2});
    let report = run(loader.apply(config)).unwrap();
    assert_eq!(loader.id("owner"), Some(parent));
    assert!(loader.id("owner/child").unwrap() > old_child);
    assert_eq!(report.changed, vec!["model", "owner/child"]);
    assert_eq!(report.retained, 1);
    assert_eq!(
        *observations.lock().unwrap(),
        vec![("parent", 1), ("child", 1), ("parent", 2), ("child", 2)]
    );
}

#[test]
fn reload_reconciles_children_retired_by_an_external_owner_restart() {
    let mut loader = Loader::new(Context::new(), registry(&Log::default()));
    run(loader.apply(tree(1))).unwrap();
    let owner = loader.id("group").unwrap();
    let child = loader.id("group/worker").unwrap();
    loader.runtime_mut().restart(owner).unwrap();
    let report = run(loader.reload()).unwrap();
    assert_eq!(loader.id("group"), Some(owner));
    assert!(loader.id("group/worker").unwrap() > child);
    assert_eq!(report.changed, vec!["group/worker"]);
}

#[test]
fn paper_leaf_projection_requires_resolution_and_preserves_raw_configuration() {
    let mut tree = ConfigTree::from_json(
        r#"[{"id":"parent","enabled":false,"children":[{
            "id":"worker","name":"worker-factory","config":{"value":4},
            "isolate":["cache"],"intercept":{"worker-factory":{"value":8}}
        }]}]"#,
    )
    .unwrap();
    let parent = &tree.entries[0];
    assert!(parent.as_paper_entry(|_| Some("module://group")).is_none());
    let child = &parent.children[0];
    assert!(child.as_paper_entry::<&str>(|_| None).is_none());
    let paper = child
        .as_paper_entry(|name| (name == "worker-factory").then_some("module://worker-v1"))
        .unwrap();
    assert_eq!(paper.id, "worker");
    assert_eq!(paper.url, "module://worker-v1");
    assert_eq!(paper.isolate, &["cache"]);
    assert_eq!(paper.intercept["worker-factory"]["value"], 8);
    assert_eq!(paper.config["value"], 4);
    // The parent's effective disablement is not this record's administrative bit.
    assert!(paper.enabled());
    let child = &mut tree.entries[0].children[0];
    child.enabled = false;
    assert!(
        child
            .as_paper_entry(|_| Some("module://worker-v1"))
            .unwrap()
            .disabled
    );
    child.include = Some(PathBuf::from("children.json"));
    assert!(child
        .as_paper_entry(|_| Some("module://worker-v1"))
        .is_none());
}
