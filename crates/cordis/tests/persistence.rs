use cordis::loader::{ConfigTree, Entry, FactoryRegistry, Loader};
use cordis::persistence::SaveErrorKind;
use cordis::Context;
use serde_json::{json, Value};
use std::future::Future;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::task::{Context as TaskContext, Poll, Waker};

fn run<F: Future>(future: F) -> F::Output {
    let mut future = Box::pin(future);
    let waker = Waker::noop();
    for _ in 0..10000 {
        if let Poll::Ready(result) = future.as_mut().poll(&mut TaskContext::from_waker(waker)) {
            return result;
        }
        std::thread::yield_now();
    }
    panic!("future did not settle");
}
static NEXT_DIR: AtomicUsize = AtomicUsize::new(0);
struct Files(PathBuf);
impl Files {
    fn new() -> Self {
        let path = std::env::temp_dir().join(format!(
            "cordis-persistence-{}-{}",
            std::process::id(),
            NEXT_DIR.fetch_add(1, Ordering::SeqCst)
        ));
        std::fs::create_dir_all(&path).unwrap();
        Self(std::fs::canonicalize(path).unwrap())
    }
    fn path(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }
    fn write(&self, name: &str, value: Value) {
        std::fs::write(self.path(name), value.to_string()).unwrap();
    }
    fn read(&self, name: &str) -> Value {
        serde_json::from_str(&std::fs::read_to_string(self.path(name)).unwrap()).unwrap()
    }
    fn loader(&self, root: &str) -> Loader {
        let mut loader = Loader::new(Context::new(), FactoryRegistry::new());
        run(loader.load_file(self.path(root))).unwrap();
        loader
    }
    fn no_temporary_files(&self) {
        assert!(std::fs::read_dir(&self.0).unwrap().all(|entry| !entry
            .unwrap()
            .file_name()
            .to_string_lossy()
            .starts_with(".cordis-save-")));
    }
}
impl Drop for Files {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
fn edit(loader: &mut Loader, path: &str, key: &str, value: Value) {
    let mut tree = loader.tree().clone();
    tree.entry_mut(path).unwrap().config[key] = value;
    run(loader.apply(tree)).unwrap();
}

#[test]
fn saving_requires_file_source_and_memory_apply_never_writes() {
    let mut loader = Loader::new(Context::new(), FactoryRegistry::new());
    assert_eq!(loader.save().unwrap_err().kind, SaveErrorKind::NoFileSource);
    let files = Files::new();
    files.write("root.json", json!([{"id":"a","config":{"n":1}}]));
    let mut loader = files.loader("root.json");
    edit(&mut loader, "a", "n", json!(2));
    assert_eq!(files.read("root.json")[0]["config"]["n"], 1);
    let report = loader.save().unwrap();
    assert_eq!(report.written, vec![files.path("root.json")]);
    assert_eq!(files.read("root.json")[0]["config"]["n"], 2);
    run(loader.load_json("[]")).unwrap();
    assert_eq!(loader.save().unwrap_err().kind, SaveErrorKind::NoFileSource);
    files.no_temporary_files();
}

#[test]
fn unchanged_save_preserves_bytes_and_modified_save_preserves_permissions() {
    let files = Files::new();
    let original = "[ {\"id\": \"a\"} ]\n";
    std::fs::write(files.path("root.json"), original).unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(
            files.path("root.json"),
            std::fs::Permissions::from_mode(0o640),
        )
        .unwrap();
    }
    let mut loader = files.loader("root.json");
    let report = loader.save().unwrap();
    assert!(report.written.is_empty());
    assert_eq!(report.unchanged, vec![files.path("root.json")]);
    assert_eq!(
        std::fs::read_to_string(files.path("root.json")).unwrap(),
        original
    );
    edit(&mut loader, "a", "n", json!(2));
    loader.save().unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        assert_eq!(
            std::fs::metadata(files.path("root.json"))
                .unwrap()
                .permissions()
                .mode()
                & 0o777,
            0o640
        );
    }
    files.no_temporary_files();
}

#[test]
fn include_sources_keep_topology_and_round_trip_without_duplicate_children() {
    let files = Files::new();
    files.write(
        "root.json",
        json!({"entries":[{"id":"group","include":"child.json","children":[{"id":"inline"}]}]}),
    );
    files.write(
        "child.json",
        json!([{"id":"nested","include":"grand.json"}]),
    );
    files.write("grand.json", json!([{"id":"worker","config":{"n":1}}]));
    let mut loader = files.loader("root.json");
    edit(&mut loader, "group/nested/worker", "n", json!(2));
    let plan = loader.prepare_save().unwrap();
    assert_eq!(plan.files().len(), 3);
    assert_eq!(
        plan.files().iter().filter(|file| file.will_write()).count(),
        1
    );
    let report = loader.commit_save(plan).unwrap();
    assert_eq!(report.written, vec![files.path("grand.json")]);
    assert_eq!(
        files.read("root.json")["entries"][0]["include"],
        "child.json"
    );
    assert_eq!(
        files.read("root.json")["entries"][0]["children"]
            .as_array()
            .unwrap()
            .len(),
        1
    );
    assert_eq!(files.read("child.json")[0]["include"], "grand.json");
    assert_eq!(files.read("grand.json")[0]["config"]["n"], 2);
    assert!(run(loader.poll_reload()).unwrap().is_unchanged());
    assert_eq!(loader.tree().entries[0].children.len(), 2);
}

#[test]
fn repeated_save_retains_external_fields_without_changing_the_runtime() {
    let files = Files::new();
    files.write(
        "root.json",
        json!([{"id":"a","config":{"local":1,"remote":1,"nested":{"a":1,"b":1}}}]),
    );
    let mut loader = files.loader("root.json");
    files.write(
        "root.json",
        json!([{"id":"a","config":{"local":1,"remote":2,"nested":{"a":1,"b":2},"new":"external"}}]),
    );
    edit(&mut loader, "a", "local", json!(2));
    edit(&mut loader, "a", "nested", json!({"a":2,"b":1}));
    let report = loader.save().unwrap();
    assert_eq!(report.merged_external, vec![files.path("root.json")]);
    assert_eq!(loader.tree().entries[0].config["remote"], 1);
    assert_eq!(
        files.read("root.json")[0]["config"],
        json!({"local":2,"remote":2,"nested":{"a":2,"b":2},"new":"external"})
    );
    edit(&mut loader, "a", "local", json!(3));
    loader.save().unwrap();
    assert_eq!(
        files.read("root.json")[0]["config"],
        json!({"local":3,"remote":2,"nested":{"a":2,"b":2},"new":"external"})
    );
    run(loader.poll_reload()).unwrap();
    assert_eq!(loader.tree().entries[0].config["remote"], 2);
    assert_eq!(loader.tree().entries[0].config["new"], "external");
}

#[test]
fn conflicting_field_in_any_file_prevents_all_writes() {
    let files = Files::new();
    files.write(
        "a-root.json",
        json!([{"id":"g","include":"z-child.json","config":{"n":1}}]),
    );
    files.write("z-child.json", json!([{"id":"c","config":{"n":1}}]));
    let mut loader = files.loader("a-root.json");
    edit(&mut loader, "g", "n", json!(2));
    edit(&mut loader, "g/c", "n", json!(2));
    files.write("z-child.json", json!([{"id":"c","config":{"n":3}}]));
    let error = loader.save().unwrap_err();
    assert!(matches!(error.kind, SaveErrorKind::Conflict(ref paths) if paths == &["$/c/config/n"]));
    assert!(error.report.written.is_empty());
    assert_eq!(files.read("a-root.json")[0]["config"]["n"], 1);
    assert_eq!(files.read("z-child.json")[0]["config"]["n"], 3);
    files.no_temporary_files();
}

#[test]
fn partial_commit_reports_progress_and_retry_uses_each_completed_checkpoint() {
    let files = Files::new();
    files.write(
        "a-root.json",
        json!([{"id":"g","include":"z-child.json","config":{"n":1,"remote":1}}]),
    );
    files.write("z-child.json", json!([{"id":"c","config":{"n":1}}]));
    let mut loader = files.loader("a-root.json");
    edit(&mut loader, "g", "n", json!(2));
    edit(&mut loader, "g/c", "n", json!(2));
    let plan = loader.prepare_save().unwrap();
    std::fs::remove_file(files.path("z-child.json")).unwrap();
    std::fs::create_dir(files.path("z-child.json")).unwrap();
    let error = loader.commit_save(plan).unwrap_err();
    assert_eq!(error.report.written, vec![files.path("a-root.json")]);
    assert_eq!(error.report.remaining, vec![files.path("z-child.json")]);
    assert!(matches!(error.kind, SaveErrorKind::Io(_)));
    std::fs::remove_dir(files.path("z-child.json")).unwrap();
    files.write("z-child.json", json!([{"id":"c","config":{"n":1}}]));
    let mut disk = files.read("a-root.json");
    disk[0]["config"]["remote"] = json!(3);
    files.write("a-root.json", disk);
    edit(&mut loader, "g", "n", json!(4));
    let report = loader.save().unwrap();
    assert_eq!(report.written.len(), 2);
    assert!(report.remaining.is_empty());
    assert_eq!(
        files.read("a-root.json")[0]["config"],
        json!({"n":4,"remote":3})
    );
    assert_eq!(files.read("z-child.json")[0]["config"]["n"], 2);
    files.no_temporary_files();
}

#[test]
fn disk_edit_invalidates_reviewed_plan_without_overwrite() {
    let files = Files::new();
    files.write("root.json", json!([{"id":"a","config":{"n":1}}]));
    let mut loader = files.loader("root.json");
    edit(&mut loader, "a", "n", json!(2));
    let plan = loader.prepare_save().unwrap();
    files.write("root.json", json!([{"id":"a","config":{"n":3}}]));
    let error = loader.commit_save(plan).unwrap_err();
    assert_eq!(error.kind, SaveErrorKind::SourceChanged);
    assert!(error.report.written.is_empty());
    assert_eq!(files.read("root.json")[0]["config"]["n"], 3);
    files.no_temporary_files();
}

#[test]
fn loader_edit_invalidates_reviewed_plan_without_write() {
    let files = Files::new();
    files.write("root.json", json!([{"id":"a","config":{"n":1}}]));
    let mut loader = files.loader("root.json");
    edit(&mut loader, "a", "n", json!(2));
    let plan = loader.prepare_save().unwrap();
    edit(&mut loader, "a", "n", json!(3));
    assert_eq!(
        loader.commit_save(plan).unwrap_err().kind,
        SaveErrorKind::StalePlan
    );
    assert_eq!(files.read("root.json")[0]["config"]["n"], 1);
}

#[test]
fn shared_include_requires_consistent_instance_edits() {
    let files = Files::new();
    files.write(
        "root.json",
        json!([{"id":"a","include":"child.json"},{"id":"b","include":"./child.json"}]),
    );
    files.write("child.json", json!([{"id":"c","config":{"n":1}}]));
    let mut loader = files.loader("root.json");
    edit(&mut loader, "a/c", "n", json!(2));
    assert!(matches!(
        loader.save().unwrap_err().kind,
        SaveErrorKind::Topology(_)
    ));
    assert_eq!(files.read("child.json")[0]["config"]["n"], 1);
    edit(&mut loader, "b/c", "n", json!(2));
    loader.save().unwrap();
    assert_eq!(files.read("child.json")[0]["config"]["n"], 2);
}

#[test]
fn ambiguous_include_addition_and_cross_boundary_reorder_are_rejected() {
    let files = Files::new();
    files.write(
        "root.json",
        json!([{"id":"g","include":"child.json","children":[{"id":"inline"}]}]),
    );
    files.write("child.json", json!([{"id":"external"}]));
    let mut loader = files.loader("root.json");
    let mut tree = loader.tree().clone();
    tree.entries[0].children.push(Entry::group("new", vec![]));
    run(loader.apply(tree)).unwrap();
    assert!(matches!(
        loader.save().unwrap_err().kind,
        SaveErrorKind::Topology(_)
    ));
    run(loader.poll_reload()).unwrap();
    let mut tree = loader.tree().clone();
    tree.entries[0].children.swap(0, 1);
    run(loader.apply(tree)).unwrap();
    assert!(matches!(
        loader.save().unwrap_err().kind,
        SaveErrorKind::Topology(_)
    ));
}

#[test]
fn external_include_topology_changes_require_reload() {
    let files = Files::new();
    files.write("root.json", json!([{"id":"g","include":"child.json"}]));
    files.write("child.json", json!([{"id":"c"}]));
    let mut loader = files.loader("root.json");
    edit(&mut loader, "g/c", "n", json!(2));
    files.write("root.json", json!([{"id":"g","include":"different.json"}]));
    assert!(matches!(
        loader.save().unwrap_err().kind,
        SaveErrorKind::Topology(_)
    ));
    assert_eq!(files.read("child.json"), json!([{"id":"c"}]));
}

#[test]
fn entry_deletion_and_external_update_conflict_and_disjoint_entry_edits_merge() {
    let files = Files::new();
    files.write(
        "root.json",
        json!([{"id":"a","config":{"n":1}},{"id":"b","config":{"n":1}}]),
    );
    let mut loader = files.loader("root.json");
    edit(&mut loader, "a", "n", json!(2));
    files.write(
        "root.json",
        json!([{"id":"a","config":{"n":1}},{"id":"b","config":{"n":2}}]),
    );
    loader.save().unwrap();
    assert_eq!(files.read("root.json")[0]["config"]["n"], 2);
    assert_eq!(files.read("root.json")[1]["config"]["n"], 2);
    let mut tree = loader.tree().clone();
    tree.entries.remove(1);
    run(loader.apply(tree)).unwrap();
    assert!(matches!(
        loader.save().unwrap_err().kind,
        SaveErrorKind::Conflict(_)
    ));
}

#[test]
fn explicit_object_root_and_new_inline_entries_round_trip() {
    let files = Files::new();
    files.write("root.json", json!({"entries":[{"id":"a"}]}));
    let mut loader = files.loader("root.json");
    let mut tree = loader.tree().clone();
    tree.entries[0].children.push(Entry::group("new", vec![]));
    tree.entries.push(Entry::group("b", vec![]));
    run(loader.apply(tree)).unwrap();
    loader.save().unwrap();
    assert!(files.read("root.json").is_object());
    assert!(run(loader.poll_reload()).unwrap().is_unchanged());
    assert!(loader.id("a/new").is_some());
    assert!(loader.id("b").is_some());
}

#[cfg(unix)]
#[test]
fn replacing_a_canonical_source_with_a_symlink_is_rejected() {
    let files = Files::new();
    files.write("root.json", json!([{"id":"a"}]));
    files.write("other.json", json!([{"id":"other"}]));
    let mut loader = files.loader("root.json");
    edit(&mut loader, "a", "n", json!(2));
    std::fs::remove_file(files.path("root.json")).unwrap();
    std::os::unix::fs::symlink(files.path("other.json"), files.path("root.json")).unwrap();
    assert!(matches!(
        loader.save().unwrap_err().kind,
        SaveErrorKind::Io(_)
    ));
    assert_eq!(files.read("other.json"), json!([{"id":"other"}]));
}

#[test]
fn malformed_and_missing_sources_do_not_create_replacement_files() {
    let files = Files::new();
    files.write("root.json", json!([{"id":"a"}]));
    let mut loader = files.loader("root.json");
    edit(&mut loader, "a", "n", json!(2));
    std::fs::write(files.path("root.json"), "not JSON").unwrap();
    assert!(loader.save().is_err());
    assert_eq!(
        std::fs::read_to_string(files.path("root.json")).unwrap(),
        "not JSON"
    );
    std::fs::remove_file(files.path("root.json")).unwrap();
    assert!(loader.save().is_err());
    assert!(!files.path("root.json").exists());
    files.no_temporary_files();
}

#[test]
fn tree_serialization_does_not_resolve_includes_or_write_implicitly() {
    let parsed = ConfigTree::from_json(r#"[{"id":"a","include":"child.json"}]"#).unwrap();
    assert_eq!(
        parsed.entries[0].include.as_deref(),
        Some(Path::new("child.json"))
    );
    assert!(parsed.to_json().unwrap().contains("child.json"));
}

#[test]
fn merged_configuration_is_validated_before_any_file_is_written() {
    let files = Files::new();
    files.write("root.json", json!([{"id":"a","config":{"n":1}}]));
    let mut loader = files.loader("root.json");
    edit(&mut loader, "a", "n", json!(2));
    files.write(
        "root.json",
        json!([{"id":"a","name":"unregistered","config":{"n":1}}]),
    );
    let error = loader.save().unwrap_err();
    assert!(matches!(
        error.kind,
        SaveErrorKind::InvalidMergedConfiguration(_)
    ));
    assert!(error.report.written.is_empty());
    assert_eq!(files.read("root.json")[0]["config"]["n"], 1);
    assert_eq!(files.read("root.json")[0]["name"], "unregistered");
}
