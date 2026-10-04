#![cfg(unix)]
use cordis::loader::{FactoryRegistry, Loader};
use cordis::persistence::SaveErrorKind;
use cordis::Context;
use serde_json::json;
use std::future::Future;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::task::{Context as TaskContext, Poll, Waker};

fn run<F: Future>(future: F) -> F::Output {
    let mut future = Box::pin(future);
    for _ in 0..10000 {
        if let Poll::Ready(value) = future
            .as_mut()
            .poll(&mut TaskContext::from_waker(Waker::noop()))
        {
            return value;
        }
    }
    panic!("future did not settle");
}
static NEXT_DIR: AtomicUsize = AtomicUsize::new(0);
struct Files(std::path::PathBuf);
impl Drop for Files {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
fn scenario() -> (Files, Loader) {
    let directory = std::env::temp_dir().join(format!(
        "cordis-source-links-{}-{}",
        std::process::id(),
        NEXT_DIR.fetch_add(1, Ordering::SeqCst)
    ));
    std::fs::create_dir(&directory).unwrap();
    let files = Files(directory);
    std::fs::write(
        files.0.join("root.json"),
        json!([{"id":"a","include":"alias.json"},{"id":"b","include":"b.json"}]).to_string(),
    )
    .unwrap();
    for name in ["a.json", "b.json"] {
        std::fs::write(files.0.join(name), r#"[{"id":"child","config":{"n":1}}]"#).unwrap();
    }
    std::os::unix::fs::symlink("a.json", files.0.join("alias.json")).unwrap();
    let mut loader = Loader::new(Context::new(), FactoryRegistry::new());
    run(loader.load_file(files.0.join("root.json"))).unwrap();
    let mut tree = loader.tree().clone();
    // Matching edits in both instances would conceal alias retargeting if save
    // re-resolved source ownership instead of pinning the successful read.
    for group in &mut tree.entries {
        group.children[0].config["n"] = json!(2);
    }
    run(loader.apply(tree)).unwrap();
    (files, loader)
}
fn retarget(files: &Files) {
    std::fs::remove_file(files.0.join("alias.json")).unwrap();
    std::os::unix::fs::symlink("b.json", files.0.join("alias.json")).unwrap();
}
fn unchanged(files: &Files) {
    for name in ["a.json", "b.json"] {
        assert_eq!(
            std::fs::read_to_string(files.0.join(name)).unwrap(),
            r#"[{"id":"child","config":{"n":1}}]"#
        );
    }
}
#[test]
fn retargeted_include_cannot_redirect_projection_to_another_loaded_source() {
    let (files, mut loader) = scenario();
    retarget(&files);
    let error = loader.save().unwrap_err();
    assert!(matches!(error.kind, SaveErrorKind::Topology(_)));
    assert!(error.report.written.is_empty());
    unchanged(&files);
}
#[test]
fn include_retargeting_after_review_invalidates_commit_before_any_write() {
    let (files, mut loader) = scenario();
    let plan = loader.prepare_save().unwrap();
    retarget(&files);
    let error = loader.commit_save(plan).unwrap_err();
    assert!(matches!(error.kind, SaveErrorKind::Topology(_)));
    assert!(error.report.written.is_empty());
    assert_eq!(error.report.remaining.len(), 3);
    unchanged(&files);
}

#[test]
fn parent_directory_redirection_after_planning_does_not_redirect_writes() {
    let directory = std::env::temp_dir().join(format!(
        "cordis-parent-links-{}-{}",
        std::process::id(),
        NEXT_DIR.fetch_add(1, Ordering::SeqCst)
    ));
    std::fs::create_dir(&directory).unwrap();
    let files = Files(directory);
    for name in ["data", "different"] {
        std::fs::create_dir(files.0.join(name)).unwrap();
        std::fs::write(
            files.0.join(name).join("root.json"),
            r#"[{"id":"a","config":{"n":1}}]"#,
        )
        .unwrap();
    }
    let mut loader = Loader::new(Context::new(), FactoryRegistry::new());
    run(loader.load_file(files.0.join("data/root.json"))).unwrap();
    let mut tree = loader.tree().clone();
    tree.entries[0].config["n"] = json!(2);
    run(loader.apply(tree)).unwrap();
    let plan = loader.prepare_save().unwrap();
    std::fs::rename(files.0.join("data"), files.0.join("original")).unwrap();
    std::os::unix::fs::symlink("different", files.0.join("data")).unwrap();
    let error = loader.commit_save(plan).unwrap_err();
    assert_eq!(error.kind, SaveErrorKind::SourceChanged);
    assert!(error.report.written.is_empty());
    for name in ["original", "different"] {
        assert_eq!(
            std::fs::read_to_string(files.0.join(name).join("root.json")).unwrap(),
            r#"[{"id":"a","config":{"n":1}}]"#
        );
    }
}
