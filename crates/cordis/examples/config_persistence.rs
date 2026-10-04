//! Explicit saves preserve concurrent edits; reload is a separate runtime action.
use cordis::loader::{FactoryRegistry, Loader};
use cordis::Context;
use serde_json::json;
use std::future::Future;
use std::task::{Context as TaskContext, Poll, Waker};

fn run<F: Future>(future: F) -> F::Output {
    let mut future = Box::pin(future);
    let waker = Waker::noop();
    loop {
        if let Poll::Ready(value) = future.as_mut().poll(&mut TaskContext::from_waker(waker)) {
            return value;
        }
        std::thread::yield_now();
    }
}
fn main() -> Result<(), Box<dyn std::error::Error>> {
    let root = std::env::temp_dir().join(format!("cordis-save-example-{}", std::process::id()));
    std::fs::create_dir(&root)?;
    struct Cleanup(std::path::PathBuf);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
    let _cleanup = Cleanup(root.clone());
    let path = root.join("config.json");
    std::fs::write(
        &path,
        json!([{"id":"workspace","config":{"local":1,"external":1}}]).to_string(),
    )?;
    let mut loader = Loader::new(Context::new(), FactoryRegistry::new());
    run(loader.load_file(&path))?;
    let mut tree = loader.tree().clone();
    tree.entries[0].config["local"] = json!(2);
    run(loader.apply(tree))?;
    // Simulate a different editor changing another field before the explicit save.
    std::fs::write(
        &path,
        json!([{"id":"workspace","config":{"local":1,"external":2}}]).to_string(),
    )?;
    let plan = loader.prepare_save()?;
    println!(
        "plan: {} file(s), {} replacement(s)",
        plan.files().len(),
        plan.files().iter().filter(|file| file.will_write()).count()
    );
    let report = loader.commit_save(plan)?;
    assert_eq!(report.written.len(), 1);
    assert_eq!(report.merged_external.len(), 1);
    assert_eq!(loader.tree().entries[0].config["external"], 1);
    run(loader.poll_reload())?;
    assert_eq!(
        loader.tree().entries[0].config,
        json!({"local":2,"external":2})
    );
    println!("saved and reloaded both independent edits");
    run(loader.dispose())?;
    Ok(())
}
