//! Run with: cargo run -p cordis --example config_reload
use cordis::config::{Field, Schema};
use cordis::loader::{FactoryRegistry, Loader};
use cordis::{Context, Plugin, ServiceKey};
use serde_json::json;
use std::future::Future;
use std::sync::Arc;
use std::task::{Context as TaskContext, Poll, Wake, Waker};

struct ThreadWake(std::thread::Thread);
impl Wake for ThreadWake {
    fn wake(self: Arc<Self>) {
        self.0.unpark();
    }
    fn wake_by_ref(self: &Arc<Self>) {
        self.0.unpark();
    }
}
fn block_on<F: Future>(future: F) -> F::Output {
    let waker = Waker::from(Arc::new(ThreadWake(std::thread::current())));
    let mut context = TaskContext::from_waker(&waker);
    let mut future = Box::pin(future);
    loop {
        match future.as_mut().poll(&mut context) {
            Poll::Ready(result) => return result,
            Poll::Pending => std::thread::park(),
        }
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let dir = std::env::temp_dir().join(format!("cordis-config-example-{}", std::process::id()));
    std::fs::create_dir_all(&dir)?;
    let root_file = dir.join("root.json");
    let model_file = dir.join("model.json");
    std::fs::write(
        &root_file,
        json!([
            {"id":"workspace","isolate":["model"],"include":"model.json","children":[
                {"id":"agent","name":"agent","inject":["model"]}
            ]}
        ])
        .to_string(),
    )?;
    let write_model = |name: &str| {
        std::fs::write(
            &model_file,
            json!([
                {"id":"model","name":"model","config":{"name":name}}
            ])
            .to_string(),
        )
    };
    write_model("model-v1")?;

    let model = ServiceKey::<String>::new("model");
    let mut registry = FactoryRegistry::new();
    registry.register_service("model", model);
    registry.register(
        "model",
        Schema::object([("name", Field::required(Schema::String))]),
        move |config, _| {
            let name = config["name"].as_str().unwrap().to_owned();
            Ok(Plugin::new("model", move |setup| {
                setup.provide(model, name.clone())?;
                let name = name.clone();
                println!("model started: {name}");
                setup.on_cleanup(move || {
                    println!("model stopped: {name}");
                    Ok(())
                });
                Ok(())
            })
            .provides(model))
        },
    );
    registry.register("agent", Schema::Any, move |_, _| {
        Ok(Plugin::new("agent", move |setup| {
            let name = setup.get(model)?;
            println!("agent bound to {name}");
            setup.on_cleanup(move || {
                println!("agent released {name}");
                Ok(())
            });
            Ok(())
        }))
    });
    let mut loader = Loader::new(Context::new(), registry);
    block_on(loader.load_file(&root_file))?;
    let old = loader.id("workspace/model").unwrap();
    write_model("model-v2")?;
    let report = block_on(loader.poll_reload())?;
    let next = loader.id("workspace/model").unwrap();
    assert!(next > old);
    assert!(block_on(loader.poll_reload())?.is_unchanged());
    println!(
        "committed revision {}: model fiber {old} -> {next}",
        report.revision
    );
    block_on(loader.set_enabled("workspace", false))?;
    assert!(loader.runtime().ids().is_empty());
    block_on(loader.dispose())?;
    std::fs::remove_dir_all(dir)?;
    Ok(())
}
