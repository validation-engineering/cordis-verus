//! A real Loader -> managed Child -> failed cleanup -> recovery -> source save.
//! Run with `cargo run -p cordis-verus --example r2_production --offline`.
use cordis::config::{ConfigScope, Field, Schema};
use cordis::loader::{ConfigTree, Entry, FactoryRegistry, Loader};
use cordis::persistence::SaveErrorKind;
use cordis::{
    Context, ManagedInstruction as I, Plugin, ReversibleValue, Runtime, ServiceKey,
    ValueBranch as Branch, ValueOperation as Op,
};
use serde_json::json;
use std::future::Future;
use std::path::PathBuf;
use std::task::{Context as TaskContext, Poll, Waker};

fn ready<F: Future>(future: F) -> F::Output {
    let mut future = std::pin::pin!(future);
    let mut cx = TaskContext::from_waker(Waker::noop());
    for _ in 0..1000 {
        if let Poll::Ready(value) = future.as_mut().poll(&mut cx) {
            return value;
        }
    }
    panic!("synchronous acceptance case did not settle");
}
fn end() -> Branch {
    Branch {
        matched: None,
        unmatched: None,
    }
}
fn provider(
    count: ServiceKey<ReversibleValue>,
    label: ServiceKey<String>,
    value: ReversibleValue,
) -> Plugin {
    Plugin::new("provider", move |setup| {
        setup.provide(count, value.clone())?;
        setup.provide(label, "original".to_owned())?;
        Ok(())
    })
    .provides(count)
    .provides(label)
}
struct Directory(PathBuf);
impl Drop for Directory {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
fn main() {
    let context = Context::new();
    let mut runtime = Runtime::new();
    let count = ServiceKey::new("acceptance budget");
    let label = ServiceKey::new("acceptance label");
    let value = runtime.reversible_value(10);
    let first_provider = runtime
        .mount(&context, None, provider(count, label, value.clone()))
        .unwrap();
    ready(runtime.settle()).unwrap();
    let mut registry = FactoryRegistry::new();
    registry.register(
        "worker",
        Schema::object([("amount", Field::defaulted(Schema::integer(1, 9), 3))]),
        move |config, _| {
            let amount = config["amount"].as_u64().unwrap();
            Plugin::native_function(
                "configured worker",
                vec![
                    I::scalar(
                        count,
                        Op::Add(amount),
                        Branch {
                            matched: Some(1),
                            unmatched: None,
                        },
                    ),
                    I::replace(label, format!("selected:{amount}"), end()),
                ],
            )
            .map_err(|error| error.to_string())
        },
    );
    let mut loader =
        Loader::with_runtime(runtime, ConfigScope::new(context.clone()), registry, None);
    let directory = Directory(std::env::temp_dir().join(
        format!("cordis-r2-{}-{}", std::process::id(),
        std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()),
    ));
    std::fs::create_dir(&directory.0).unwrap();
    let source = directory.0.join("cordis.json");
    let tree = ConfigTree {
        entries: vec![Entry::group(
            "group",
            vec![Entry::plugin("worker", "worker", json!({}))],
        )],
    };
    std::fs::write(&source, serde_json::to_vec_pretty(&tree).unwrap()).unwrap();
    ready(loader.load_file(&source)).unwrap();
    let old_group = loader.id("group").unwrap();
    let old_child = loader.id("group/worker").unwrap();
    assert_eq!(value.snapshot().value(), 13);
    assert_eq!(
        loader.runtime().get(&context, label).unwrap().as_str(),
        "selected:3"
    );
    let stale = loader.runtime().owner_context(old_child).unwrap();
    let _loaded = loader.execution_snapshot();

    let later_writer = loader
        .runtime_mut()
        .mount(
            &context,
            None,
            Plugin::new("later writer", move |setup| {
                setup.replace_service(label, "conflict".to_owned())
            })
            .requires(label),
        )
        .unwrap();
    ready(loader.runtime_mut().settle()).unwrap();
    assert!(ready(loader.set_enabled("group", false)).is_err());
    assert!(loader.recovery_pending());
    assert_eq!(loader.tree(), &tree);
    assert_eq!(
        loader.save().unwrap_err().kind,
        SaveErrorKind::RecoveryPending
    );
    assert_eq!(value.snapshot().value(), 13);
    assert_eq!(
        loader.runtime().get(&context, label).unwrap().as_str(),
        "conflict"
    );
    assert!(stale.replace_service(label, "stale".to_owned()).is_err());
    let _blocked = loader.execution_snapshot();
    loader.runtime_mut().dispose(later_writer).unwrap();
    loader.runtime_mut().dispose(first_provider).unwrap();
    let _failure = ready(loader.runtime_mut().settle());
    assert!(loader.runtime().contains(first_provider));
    assert!(!loader.runtime().cleanup_started(first_provider));
    let _retained = loader.execution_snapshot();
    loader.runtime_mut().retry_cleanup(old_child).unwrap();
    ready(loader.runtime_mut().settle()).unwrap();
    assert!(!loader.runtime().contains(first_provider));
    assert!(!loader.runtime().contains(old_child));
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (10, 0)
    );
    let _drained = loader.execution_snapshot();

    let next_provider = loader
        .runtime_mut()
        .mount(&context, None, provider(count, label, value.clone()))
        .unwrap();
    ready(loader.runtime_mut().settle()).unwrap();
    ready(loader.recover()).unwrap();
    assert!(!loader.recovery_pending());
    assert_eq!(loader.tree(), &tree);
    assert!(loader.id("group").unwrap() > old_group);
    assert!(loader.id("group/worker").unwrap() > old_child);
    assert_eq!(value.snapshot().value(), 13);
    let _recovered = loader.execution_snapshot();
    let mut updated = tree;
    updated.entries[0].children[0].config = json!({"amount":5});
    ready(loader.apply(updated.clone())).unwrap();
    assert_eq!(value.snapshot().value(), 15);
    assert_eq!(
        loader.runtime().get(&context, label).unwrap().as_str(),
        "selected:5"
    );
    let _updated = loader.execution_snapshot();
    let saved = loader.save().unwrap();
    assert_eq!(saved.written.len(), 1);
    let disk: ConfigTree = serde_json::from_slice(&std::fs::read(&source).unwrap()).unwrap();
    assert_eq!(disk, updated);
    assert_eq!(loader.save().unwrap().unchanged.len(), 1);
    let _saved = loader.execution_snapshot();
    ready(loader.dispose()).unwrap();
    loader.runtime_mut().dispose(next_provider).unwrap();
    ready(loader.runtime_mut().settle()).unwrap();
    assert!(loader.runtime().ids().is_empty());
    assert_eq!(
        (value.snapshot().value(), value.snapshot().depth()),
        (10, 0)
    );
    let _released = loader.execution_snapshot();
    println!(
        "R2_NATIVE_ACCEPTANCE {}",
        json!({"stages":["loaded","blocked","retained","drained","recovered","updated","saved","released"],"initial":10,"updated":15,"restored":10})
    );
}
