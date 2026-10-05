//! Real executable transport and lifecycle tests. Fixture scripts use only POSIX
//! shell builtins and are directly exec'd; the adapter never invokes a shell.
#![cfg(unix)]
use cordis::config::Schema;
use cordis::loader::{ConfigTree, Entry, FactoryRegistry, Loader, LoaderError};
use cordis::process_plugin::{ProcessClient, ProcessError, ProcessPlugin, ProcessPluginWatcher};
use cordis::{Context, Runtime, ServiceKey};
use serde_json::{json, Value};
use std::future::Future;
use std::os::unix::fs::PermissionsExt;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::task::{Context as TaskContext, Poll, Wake, Waker};
use std::time::{Duration, Instant};

static NEXT: AtomicU64 = AtomicU64::new(1);
struct Fixture {
    directory: PathBuf,
    executable: PathBuf,
}
impl Fixture {
    fn new(body: &str) -> Self {
        let directory = std::env::temp_dir().join(format!(
            "cordis-process-test-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&directory).unwrap();
        let fixture = Self {
            executable: directory.join("external plugin"),
            directory,
        };
        fixture.write(body);
        fixture
    }
    fn write(&self, body: &str) {
        // Atomic replacement leaves already running code on its previous inode.
        let next = self.directory.join("next");
        std::fs::write(&next, format!("#!/bin/sh\nwhile IFS= read -r request; do\n rest=${{request#*\\\"id\\\":}}\n id=${{rest%%,*}}\n{body}\ndone\n")).unwrap();
        std::fs::set_permissions(&next, std::fs::Permissions::from_mode(0o700)).unwrap();
        std::fs::rename(next, &self.executable).unwrap();
    }
    fn recipe(&self) -> ProcessPlugin {
        ProcessPlugin::new(&self.executable)
            .startup_timeout(Duration::from_secs(10))
            .request_timeout(Duration::from_secs(2))
            .cleanup_timeout(Duration::from_secs(1))
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.directory);
    }
}
fn version(value: u64) -> String {
    format!("printf '{{\"jsonrpc\":\"2.0\",\"id\":%s,\"result\":{value}}}\\n' \"$id\"")
}
struct ThreadWake(std::thread::Thread);
impl Wake for ThreadWake {
    fn wake(self: Arc<Self>) {
        self.0.unpark();
    }
    fn wake_by_ref(self: &Arc<Self>) {
        self.0.unpark();
    }
}
fn run<F: Future>(future: F) -> F::Output {
    let waker = Waker::from(Arc::new(ThreadWake(std::thread::current())));
    let mut context = TaskContext::from_waker(&waker);
    let mut future = Box::pin(future);
    loop {
        match future.as_mut().poll(&mut context) {
            Poll::Ready(result) => return result,
            Poll::Pending => std::thread::park_timeout(Duration::from_millis(10)),
        }
    }
}
fn tree() -> ConfigTree {
    ConfigTree {
        entries: vec![Entry::plugin("model", "model", json!({"temperature":0.2}))],
    }
}

#[test]
fn directly_executes_paths_and_literal_args_and_serializes_concurrent_calls() {
    let fixture = Fixture::new(
        "printf '{\"jsonrpc\":\"2.0\",\"id\":%s,\"result\":\"%s\"}\\n' \"$id\" \"$1\"",
    );
    let client = fixture
        .recipe()
        .arg("$(no-shell); literal argument")
        .spawn()
        .unwrap();
    let threads: Vec<_> = (0..4)
        .map(|_| {
            let client = client.clone();
            std::thread::spawn(move || client.call("complete", json!({"prompt":"hello"})).unwrap())
        })
        .collect();
    for thread in threads {
        assert_eq!(
            thread.join().unwrap(),
            json!("$(no-shell); literal argument")
        );
    }
    client.shutdown().unwrap();
    client.shutdown().unwrap();
    assert!(matches!(
        client.call("complete", Value::Null),
        Err(ProcessError::Closed)
    ));
}

#[test]
fn remote_application_errors_do_not_poison_transport() {
    let fixture = Fixture::new("case \"$request\" in\n *fail*) printf '{\"jsonrpc\":\"2.0\",\"id\":%s,\"error\":{\"code\":-32001,\"message\":\"model busy\",\"data\":7}}\\n' \"$id\";;\n *) printf '{\"jsonrpc\":\"2.0\",\"id\":%s,\"result\":null}\\n' \"$id\";;\nesac");
    let client = fixture.recipe().spawn().unwrap();
    assert!(matches!(
        client.call("fail", Value::Null),
        Err(ProcessError::Remote {
            code: -32001,
            data: Some(Value::Number(_)),
            ..
        })
    ));
    assert_eq!(client.call("works", Value::Null).unwrap(), Value::Null);
    assert!(!client.is_closed());
}

#[test]
fn owner_cleanup_closes_retained_handles_and_reaps_direct_child() {
    let fixture =
        Fixture::new("printf '{\"jsonrpc\":\"2.0\",\"id\":%s,\"result\":%s}\\n' \"$id\" \"$$\"");
    let key = ServiceKey::<ProcessClient>::new("external-model");
    let context = Context::new();
    let mut runtime = Runtime::new();
    let id = runtime
        .mount(&context, None, fixture.recipe().plugin("model", key))
        .unwrap();
    run(runtime.settle()).unwrap();
    let client = runtime.get(&context, key).unwrap();
    let pid = client.call("pid", Value::Null).unwrap().as_u64().unwrap();
    runtime.dispose(id).unwrap();
    run(runtime.settle()).unwrap();
    assert!(client.is_closed());
    assert!(matches!(
        client.call("pid", Value::Null),
        Err(ProcessError::Closed)
    ));
    let status = std::process::Command::new("kill")
        .args(["-0", &pid.to_string()])
        .stderr(std::process::Stdio::null())
        .status()
        .unwrap();
    assert!(
        !status.success(),
        "direct child must have exited and been reaped"
    );
}

#[test]
fn initialization_and_request_timeouts_close_hung_children() {
    let startup = Fixture::new("IFS= read -r ignored");
    let start = Instant::now();
    assert!(matches!(
        startup
            .recipe()
            .startup_timeout(Duration::from_millis(100))
            .spawn(),
        Err(ProcessError::Timeout { .. })
    ));
    assert!(start.elapsed() < Duration::from_secs(2));
    let active = Fixture::new(&format!(
        "case \"$request\" in\n *initialize*) {};;\n *) IFS= read -r ignored;;\nesac",
        version(1)
    ));
    let client = active
        .recipe()
        .request_timeout(Duration::from_millis(100))
        .spawn()
        .unwrap();
    let start = Instant::now();
    assert!(matches!(
        client.call("hang", Value::Null),
        Err(ProcessError::Timeout { phase: "request" })
    ));
    assert!(client.is_closed());
    assert!(start.elapsed() < Duration::from_secs(2));
}

#[test]
fn malformed_mismatched_and_oversized_responses_are_fatal() {
    for body in [
        "printf 'not-json\\n'",
        "printf '{\"jsonrpc\":\"2.0\",\"id\":999,\"result\":1}\\n'",
        "printf '{\"jsonrpc\":\"2.0\",\"id\":%s,\"result\":1,\"error\":null}\\n' \"$id\"",
    ] {
        let fixture = Fixture::new(&format!(
            "case \"$request\" in\n *initialize*) {};;\n *) {body};;\nesac",
            version(1)
        ));
        let client = fixture.recipe().spawn().unwrap();
        assert!(matches!(
            client.call("request", Value::Null),
            Err(ProcessError::Protocol(_))
        ));
        assert!(client.is_closed());
    }
    let fixture = Fixture::new(&format!(
        "case \"$request\" in\n *initialize*) {};;\n *) printf '%0200d\\n' 1;;\nesac",
        version(1)
    ));
    let client = fixture.recipe().max_frame_bytes(128).spawn().unwrap();
    assert!(matches!(
        client.call("request", Value::Null),
        Err(ProcessError::FrameTooLarge { limit: 128 })
    ));
    assert!(client.is_closed());
}

#[test]
fn outbound_frame_limit_does_not_break_an_untouched_transport() {
    let fixture = Fixture::new(&version(1));
    let client = fixture.recipe().max_frame_bytes(128).spawn().unwrap();
    assert!(matches!(
        client.call("request", json!("a".repeat(512))),
        Err(ProcessError::FrameTooLarge { .. })
    ));
    assert_eq!(client.call("request", Value::Null).unwrap(), json!(1));
}

#[test]
fn executable_replacement_reloads_and_failed_revision_restores_exact_old_code() {
    let fixture = Fixture::new(&version(1));
    let key = ServiceKey::<ProcessClient>::new("model");
    let mut registry = FactoryRegistry::new();
    registry.register_service("model", key);
    let mut watcher = ProcessPluginWatcher::new();
    watcher
        .register(&mut registry, "model", Schema::Any, fixture.recipe(), key)
        .unwrap();
    let context = Context::new();
    let mut loader = Loader::new(context.clone(), registry);
    run(loader.apply(tree())).unwrap();
    let first_id = loader.id("model").unwrap();
    let first = loader.runtime().get(&context, key).unwrap();
    assert_eq!(first.call("complete", Value::Null).unwrap(), json!(1));
    assert!(watcher.poll(loader.registry_mut()).unwrap().is_empty());
    fixture.write(&version(2));
    assert_eq!(watcher.poll(loader.registry_mut()).unwrap(), ["model"]);
    run(loader.reload()).unwrap();
    let second_id = loader.id("model").unwrap();
    assert_ne!(first_id, second_id);
    assert!(first.is_closed());
    let second = loader.runtime().get(&context, key).unwrap();
    assert_eq!(second.call("complete", Value::Null).unwrap(), json!(2));
    fixture.write("printf '{\"jsonrpc\":\"2.0\",\"id\":%s,\"error\":{\"code\":-32001,\"message\":\"broken new binary\"}}\\n' \"$id\"");
    assert_eq!(watcher.poll(loader.registry_mut()).unwrap(), ["model"]);
    assert!(matches!(
        run(loader.reload()),
        Err(LoaderError::Apply { rollback: None, .. })
    ));
    assert!(second.is_closed());
    let restored = loader.runtime().get(&context, key).unwrap();
    assert_eq!(
        restored.call("complete", Value::Null).unwrap(),
        json!(2),
        "rollback must execute old bytes, not the broken file still on disk"
    );
    assert_ne!(loader.id("model").unwrap(), second_id);
    run(loader.dispose()).unwrap();
    assert!(restored.is_closed());
}

#[test]
fn watched_dependencies_are_snapshotted_and_missing_changes_are_transactional() {
    let fixture = Fixture::new("IFS= read -r version < version.txt\nprintf '{\"jsonrpc\":\"2.0\",\"id\":%s,\"result\":%s}\\n' \"$id\" \"$version\"");
    let dependency = fixture.directory.join("version.txt");
    std::fs::write(&dependency, "1\n").unwrap();
    let key = ServiceKey::<ProcessClient>::new("model");
    let mut watcher = ProcessPluginWatcher::new();
    let mut registry = FactoryRegistry::new();
    watcher
        .register(
            &mut registry,
            "model",
            Schema::Any,
            fixture.recipe().watch_file("version.txt"),
            key,
        )
        .unwrap();
    let context = Context::new();
    let mut loader = Loader::new(context.clone(), registry);
    run(loader.apply(tree())).unwrap();
    let first = loader.runtime().get(&context, key).unwrap();
    std::fs::write(&dependency, "2\n").unwrap();
    assert_eq!(
        first.call("complete", Value::Null).unwrap(),
        json!(1),
        "live revision reads its captured dependency"
    );
    let revision = loader.registry().revision("model");
    let bytes = std::fs::read(&fixture.executable).unwrap();
    std::fs::remove_file(&fixture.executable).unwrap();
    assert!(watcher.poll(loader.registry_mut()).is_err());
    assert_eq!(loader.registry().revision("model"), revision);
    assert!(!first.is_closed());
    std::fs::write(&fixture.executable, bytes).unwrap();
    std::fs::set_permissions(&fixture.executable, std::fs::Permissions::from_mode(0o700)).unwrap();
    assert_eq!(watcher.poll(loader.registry_mut()).unwrap(), ["model"]);
    run(loader.reload()).unwrap();
    assert!(first.is_closed());
    let next = loader.runtime().get(&context, key).unwrap();
    assert_eq!(next.call("complete", Value::Null).unwrap(), json!(2));
    run(loader.dispose()).unwrap();
}

#[test]
fn child_mutating_its_working_files_cannot_corrupt_rollback_artifacts() {
    let fixture = Fixture::new("case \"$request\" in\n *mutate*) printf '99\\n' > version.txt;;\nesac\nIFS= read -r version < version.txt\nprintf '{\"jsonrpc\":\"2.0\",\"id\":%s,\"result\":%s}\\n' \"$id\" \"$version\"");
    let dependency = fixture.directory.join("version.txt");
    std::fs::write(&dependency, "1\n").unwrap();
    let key = ServiceKey::<ProcessClient>::new("model");
    let mut watcher = ProcessPluginWatcher::new();
    let mut registry = FactoryRegistry::new();
    watcher
        .register(
            &mut registry,
            "model",
            Schema::Any,
            fixture.recipe().watch_file("version.txt"),
            key,
        )
        .unwrap();
    let context = Context::new();
    let mut loader = Loader::new(context.clone(), registry);
    run(loader.apply(tree())).unwrap();
    let original = loader.runtime().get(&context, key).unwrap();
    assert_eq!(original.call("version", Value::Null).unwrap(), json!(1));
    assert_eq!(original.call("mutate", Value::Null).unwrap(), json!(99));
    assert_eq!(std::fs::read_to_string(&dependency).unwrap(), "1\n");
    fixture.write("printf '{\"jsonrpc\":\"2.0\",\"id\":%s,\"error\":{\"code\":-32000,\"message\":\"bad revision\"}}\\n' \"$id\"");
    assert_eq!(watcher.poll(loader.registry_mut()).unwrap(), ["model"]);
    assert!(matches!(
        run(loader.reload()),
        Err(LoaderError::Apply { rollback: None, .. })
    ));
    assert!(original.is_closed());
    let restored = loader.runtime().get(&context, key).unwrap();
    assert_eq!(restored.call("version", Value::Null).unwrap(), json!(1), "rollback must rebuild from captured bytes, not from the prior child's mutated working directory");
    run(loader.dispose()).unwrap();
}

#[test]
fn deadline_interrupts_a_child_that_stops_reading_requests() {
    let fixture = Fixture::new(&format!("{}\nkill -STOP \"$$\"", version(1)));
    let client = fixture
        .recipe()
        .request_timeout(Duration::from_millis(100))
        .spawn()
        .unwrap();
    let start = Instant::now();
    assert!(matches!(
        client.call("large", json!("x".repeat(512 * 1024))),
        Err(ProcessError::Timeout { phase: "request" })
    ));
    assert!(client.is_closed());
    assert!(
        start.elapsed() < Duration::from_secs(2),
        "blocked child stdin must not make call or cleanup hang"
    );
    client.shutdown().unwrap();
}
