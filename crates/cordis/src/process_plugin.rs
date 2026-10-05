//! External executable plugins using bounded, serialized JSON-RPC over stdio.
//!
//! This host adapter is ordinary Rust, not a proof of subprocesses or I/O. A
//! child must answer `initialize` before its client is published as a service.
//! Calls are blocking; use an application's blocking executor when appropriate.
use crate::config::Schema;
use crate::loader::FactoryRegistry;
use crate::{Plugin, ServiceKey};
use serde_json::{json, Value};
use std::collections::BTreeMap;
use std::ffi::{OsStr, OsString};
use std::fmt;
use std::fs::{self, Permissions};
use std::io::{BufRead, BufReader, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::mpsc::{self, RecvTimeoutError, SyncSender, TrySendError};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

const TICK: Duration = Duration::from_millis(2);
const MAX_ARTIFACT_BYTES: usize = 256 * 1024 * 1024;
static NEXT_ARTIFACT: AtomicU64 = AtomicU64::new(1);

/// A transport or remote application failure. Remote errors leave the transport
/// usable; timeouts after admission and malformed responses close it.
#[derive(Debug)]
pub enum ProcessError {
    Io {
        operation: &'static str,
        message: String,
    },
    Protocol(String),
    Remote {
        code: i64,
        message: String,
        data: Option<Value>,
    },
    Timeout {
        phase: &'static str,
    },
    Closed,
    FrameTooLarge {
        limit: usize,
    },
    InvalidConfig(String),
}
impl fmt::Display for ProcessError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io { operation, message } => write!(f, "process plugin {operation}: {message}"),
            Self::Protocol(message) => write!(f, "process plugin protocol: {message}"),
            Self::Remote { code, message, .. } => {
                write!(f, "process plugin remote error {code}: {message}")
            }
            Self::Timeout { phase } => write!(f, "process plugin {phase} timed out"),
            Self::Closed => f.write_str("process plugin is closed"),
            Self::FrameTooLarge { limit } => {
                write!(f, "process plugin frame exceeds {limit} bytes")
            }
            Self::InvalidConfig(message) => write!(f, "process plugin configuration: {message}"),
        }
    }
}
impl std::error::Error for ProcessError {}
fn io_error(operation: &'static str, error: impl fmt::Display) -> ProcessError {
    ProcessError::Io {
        operation,
        message: error.to_string(),
    }
}
fn lock<T>(mutex: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    mutex
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// An executable recipe. `Command` receives a path and separate arguments: no
/// shell expansion or command-string evaluation is performed by this adapter.
#[derive(Clone)]
pub struct ProcessPlugin {
    executable: PathBuf,
    args: Vec<OsString>,
    working_directory: Option<PathBuf>,
    dependencies: Vec<PathBuf>,
    initialize: Value,
    startup_timeout: Duration,
    request_timeout: Duration,
    cleanup_timeout: Duration,
    max_frame_bytes: usize,
    artifact: Option<Arc<Artifact>>,
}
impl ProcessPlugin {
    pub fn new(executable: impl Into<PathBuf>) -> Self {
        Self {
            executable: executable.into(),
            args: Vec::new(),
            working_directory: None,
            dependencies: Vec::new(),
            initialize: Value::Null,
            startup_timeout: Duration::from_secs(10),
            request_timeout: Duration::from_secs(30),
            cleanup_timeout: Duration::from_secs(2),
            max_frame_bytes: 1024 * 1024,
            artifact: None,
        }
    }
    pub fn arg(mut self, arg: impl AsRef<OsStr>) -> Self {
        self.args.push(arg.as_ref().to_owned());
        self
    }
    pub fn working_directory(mut self, path: impl Into<PathBuf>) -> Self {
        self.working_directory = Some(path.into());
        self
    }
    /// Watch and snapshot another regular file below the executable's directory.
    /// Relative paths are resolved against that directory, not the process cwd.
    pub fn watch_file(mut self, path: impl Into<PathBuf>) -> Self {
        self.dependencies.push(path.into());
        self
    }
    pub fn initialize(mut self, params: Value) -> Self {
        self.initialize = params;
        self
    }
    pub fn startup_timeout(mut self, timeout: Duration) -> Self {
        self.startup_timeout = timeout;
        self
    }
    pub fn request_timeout(mut self, timeout: Duration) -> Self {
        self.request_timeout = timeout;
        self
    }
    pub fn cleanup_timeout(mut self, timeout: Duration) -> Self {
        self.cleanup_timeout = timeout;
        self
    }
    pub fn max_frame_bytes(mut self, limit: usize) -> Self {
        self.max_frame_bytes = limit;
        self
    }
    fn validate(&self) -> Result<(), ProcessError> {
        if self.max_frame_bytes == 0 || self.max_frame_bytes > MAX_ARTIFACT_BYTES {
            return Err(ProcessError::InvalidConfig(
                "frame limit must be between 1 byte and 256 MiB".into(),
            ));
        }
        for timeout in [
            self.startup_timeout,
            self.request_timeout,
            self.cleanup_timeout,
        ] {
            if timeout.is_zero() || Instant::now().checked_add(timeout).is_none() {
                return Err(ProcessError::InvalidConfig(
                    "timeouts must be positive and representable".into(),
                ));
            }
        }
        Ok(())
    }
    /// Construct a provider; the process starts inside setup, never in a factory.
    /// Cleanup closes admission before killing and reaping the direct child.
    pub fn plugin(self, name: impl Into<String>, key: ServiceKey<ProcessClient>) -> Plugin {
        Plugin::new(name, move |setup| {
            let client = self.spawn().map_err(|error| error.to_string())?;
            let cleanup = client.clone();
            setup.on_cleanup(move || cleanup.shutdown().map_err(|error| error.to_string()));
            setup.provide(key, client)?;
            Ok(())
        })
        .provides(key)
    }
    /// Start a child and complete the mandatory `initialize` request. Dropping
    /// the last client also closes and reaps it, including failed initialization.
    pub fn spawn(&self) -> Result<ProcessClient, ProcessError> {
        self.validate()?;
        // Each launch gets its own copy. A child modifying its working files
        // cannot alter the bytes retained by the factory for a later rollback.
        match &self.artifact {
            Some(artifact) => {
                snapshot(self, &artifact.directory, &artifact.sources)?.spawn_captured()
            }
            None => self.spawn_captured(),
        }
    }
    fn spawn_captured(&self) -> Result<ProcessClient, ProcessError> {
        let mut command = Command::new(&self.executable);
        command
            .args(&self.args)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit());
        if let Some(directory) = &self.working_directory {
            command.current_dir(directory);
        }
        let mut child = command.spawn().map_err(|error| io_error("spawn", error))?;
        // Piped handles are guaranteed by the Command setup above.
        let mut stdin = child.stdin.take().expect("piped child stdin");
        let stdout = child.stdout.take().expect("piped child stdout");
        let child = Arc::new(Mutex::new(Some(child)));
        let closed = Arc::new(AtomicBool::new(false));
        let (sender, receiver) = mpsc::sync_channel::<Request>(0);
        let worker_child = child.clone();
        let worker_closed = closed.clone();
        let limit = self.max_frame_bytes;
        let cleanup_timeout = self.cleanup_timeout;
        let worker = std::thread::Builder::new().name("cordis-process-rpc".into()).spawn(move || {
            let mut stdout = BufReader::new(stdout);
            while let Ok(request) = receiver.recv() {
                if worker_closed.load(Ordering::Acquire) { break; }
                let result = (|| {
                    stdin.write_all(&request.frame).map_err(|error| io_error("write request", error))?;
                    stdin.flush().map_err(|error| io_error("flush request", error))?;
                    let mut frame = Vec::new();
                    (&mut stdout).take(limit as u64 + 1).read_until(b'\n', &mut frame)
                        .map_err(|error| io_error("read response", error))?;
                    if frame.len() > limit { return Err(ProcessError::FrameTooLarge { limit }); }
                    if frame.last() != Some(&b'\n') {
                        return Err(ProcessError::Protocol("child exited or closed stdout before a complete response".into()));
                    }
                    parse_response(&frame, request.id)
                })();
                let fatal = matches!(&result, Err(error) if !matches!(error, ProcessError::Remote { .. }));
                if fatal { worker_closed.store(true, Ordering::Release); }
                let _ = request.response.send(result);
                if fatal {
                    let _ = terminate(&worker_child, cleanup_timeout);
                    break;
                }
            }
        });
        if let Err(error) = worker {
            closed.store(true, Ordering::Release);
            let _ = terminate(&child, self.cleanup_timeout);
            return Err(io_error("start transport worker", error));
        }
        let client = ProcessClient {
            inner: Arc::new(ClientInner {
                sender: Mutex::new(Some(sender)),
                child,
                closed,
                next_id: AtomicU64::new(1),
                request_timeout: self.request_timeout,
                cleanup_timeout: self.cleanup_timeout,
                max_frame_bytes: self.max_frame_bytes,
                _artifact: self.artifact.clone(),
            }),
        };
        client.call_with_timeout(
            "initialize",
            self.initialize.clone(),
            self.startup_timeout,
            "initialization",
        )?;
        Ok(client)
    }
}
struct Request {
    id: u64,
    frame: Vec<u8>,
    response: SyncSender<Result<Value, ProcessError>>,
}
struct ClientInner {
    sender: Mutex<Option<SyncSender<Request>>>,
    child: Arc<Mutex<Option<Child>>>,
    closed: Arc<AtomicBool>,
    next_id: AtomicU64,
    request_timeout: Duration,
    cleanup_timeout: Duration,
    max_frame_bytes: usize,
    _artifact: Option<Arc<Artifact>>,
}
impl Drop for ClientInner {
    fn drop(&mut self) {
        self.closed.store(true, Ordering::Release);
        let _ = terminate(&self.child, self.cleanup_timeout);
        // Preserve eventual reaping if the OS did not acknowledge termination
        // within the caller's bound. The worker never owns ClientInner.
        if let Some(mut child) = lock(&self.child).take() {
            let _ = std::thread::Builder::new()
                .name("cordis-process-reaper".into())
                .spawn(move || {
                    let _ = child.kill();
                    let _ = child.wait();
                });
        }
    }
}
/// Cloneable service handle. Retained handles reject new calls after owner
/// cleanup; they cannot keep an already closed provider serving requests.
#[derive(Clone)]
pub struct ProcessClient {
    inner: Arc<ClientInner>,
}
impl ProcessClient {
    pub fn is_closed(&self) -> bool {
        self.inner.closed.load(Ordering::Acquire)
    }
    /// Serialized, blocking request with a bounded queue and response deadline.
    /// A response timeout invalidates the transport to prevent late responses
    /// being confused with another request. Remote application errors do not.
    pub fn call(&self, method: &str, params: Value) -> Result<Value, ProcessError> {
        self.call_with_timeout(method, params, self.inner.request_timeout, "request")
    }
    fn call_with_timeout(
        &self,
        method: &str,
        params: Value,
        timeout: Duration,
        phase: &'static str,
    ) -> Result<Value, ProcessError> {
        if self.is_closed() {
            return Err(ProcessError::Closed);
        }
        let id = self
            .inner
            .next_id
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
            .map_err(|_| ProcessError::Protocol("request id space exhausted".into()))?;
        let mut frame = serde_json::to_vec(
            &json!({"jsonrpc":"2.0", "id":id, "method":method, "params":params}),
        )
        .map_err(|error| ProcessError::Protocol(error.to_string()))?;
        frame.push(b'\n');
        if frame.len() > self.inner.max_frame_bytes {
            return Err(ProcessError::FrameTooLarge {
                limit: self.inner.max_frame_bytes,
            });
        }
        let deadline = Instant::now() + timeout;
        let (sender, receiver) = mpsc::sync_channel(1);
        let transport = lock(&self.inner.sender)
            .clone()
            .ok_or(ProcessError::Closed)?;
        let mut request = Request {
            id,
            frame,
            response: sender,
        };
        loop {
            if self.is_closed() {
                return Err(ProcessError::Closed);
            }
            if Instant::now() >= deadline {
                return Err(ProcessError::Timeout {
                    phase: "request queue",
                });
            }
            match transport.try_send(request) {
                Ok(()) => break,
                Err(TrySendError::Disconnected(_)) => return Err(ProcessError::Closed),
                Err(TrySendError::Full(value)) => request = value,
            }
            if Instant::now() >= deadline {
                return Err(ProcessError::Timeout {
                    phase: "request queue",
                });
            }
            std::thread::sleep(TICK.min(deadline.saturating_duration_since(Instant::now())));
        }
        match receiver.recv_timeout(deadline.saturating_duration_since(Instant::now())) {
            Ok(result) => result,
            Err(RecvTimeoutError::Disconnected) => Err(ProcessError::Closed),
            Err(RecvTimeoutError::Timeout) => {
                let _ = self.shutdown();
                Err(ProcessError::Timeout { phase })
            }
        }
    }
    /// Immediately close request admission, then kill and reap the direct child.
    /// Idempotent; reports a cleanup failure rather than waiting indefinitely.
    pub fn shutdown(&self) -> Result<(), ProcessError> {
        self.inner.closed.store(true, Ordering::Release);
        lock(&self.inner.sender).take();
        terminate(&self.inner.child, self.inner.cleanup_timeout)
    }
}
fn terminate(child: &Mutex<Option<Child>>, timeout: Duration) -> Result<(), ProcessError> {
    let mut slot = lock(child);
    let Some(process) = slot.as_mut() else {
        return Ok(());
    };
    if process
        .try_wait()
        .map_err(|error| io_error("check child exit", error))?
        .is_some()
    {
        *slot = None;
        return Ok(());
    }
    if let Err(error) = process.kill() {
        // A child may exit normally between try_wait and kill.
        if process
            .try_wait()
            .map_err(|error| io_error("check child exit", error))?
            .is_some()
        {
            *slot = None;
            return Ok(());
        }
        return Err(io_error("kill child", error));
    }
    let deadline = Instant::now() + timeout;
    loop {
        if process
            .try_wait()
            .map_err(|error| io_error("reap child", error))?
            .is_some()
        {
            *slot = None;
            return Ok(());
        }
        if Instant::now() >= deadline {
            return Err(ProcessError::Timeout { phase: "cleanup" });
        }
        std::thread::sleep(TICK.min(deadline.saturating_duration_since(Instant::now())));
    }
}
fn parse_response(frame: &[u8], id: u64) -> Result<Value, ProcessError> {
    let response: Value =
        serde_json::from_slice(frame).map_err(|error| ProcessError::Protocol(error.to_string()))?;
    if response.get("jsonrpc").and_then(Value::as_str) != Some("2.0")
        || response.get("id").and_then(Value::as_u64) != Some(id)
    {
        return Err(ProcessError::Protocol(
            "response must carry jsonrpc 2.0 and the matching request id".into(),
        ));
    }
    match (response.get("result"), response.get("error")) {
        (Some(result), None) => Ok(result.clone()),
        (None, Some(error)) => {
            let code = error.get("code").and_then(Value::as_i64);
            let message = error.get("message").and_then(Value::as_str);
            match (code, message) {
                (Some(code), Some(message)) => Err(ProcessError::Remote {
                    code,
                    message: message.to_owned(),
                    data: error.get("data").cloned(),
                }),
                _ => Err(ProcessError::Protocol(
                    "error response needs an integer code and string message".into(),
                )),
            }
        }
        _ => Err(ProcessError::Protocol(
            "response needs exactly one of result or error".into(),
        )),
    }
}

#[derive(Clone)]
struct SourceFile {
    path: PathBuf,
    relative: PathBuf,
    bytes: Arc<[u8]>,
    permissions: Permissions,
}
struct Artifact {
    directory: PathBuf,
    sources: Vec<SourceFile>,
}
impl Drop for Artifact {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.directory);
    }
}
struct Watched {
    recipe: ProcessPlugin,
    schema: Schema,
    key: ServiceKey<ProcessClient>,
    sources: Vec<SourceFile>,
}
/// Explicit polling for executable code revisions. Every revision keeps private
/// copies of its executable and declared files, so Loader rollback can restore
/// the actual previous code after the source path has changed.
#[derive(Default)]
pub struct ProcessPluginWatcher {
    entries: BTreeMap<String, Watched>,
}
impl ProcessPluginWatcher {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn register(
        &mut self,
        registry: &mut FactoryRegistry,
        name: impl Into<String>,
        schema: Schema,
        recipe: ProcessPlugin,
        key: ServiceKey<ProcessClient>,
    ) -> Result<(), ProcessError> {
        let name = name.into();
        recipe.validate()?;
        let (root, sources) = read_sources(&recipe)?;
        let revision = snapshot(&recipe, &root, &sources)?;
        register_revision(registry, &name, schema.clone(), revision, key);
        self.entries.insert(
            name,
            Watched {
                recipe,
                schema,
                key,
                sources,
            },
        );
        Ok(())
    }
    /// Prepare all changed artifacts before changing any factory registrations.
    /// Missing/invalid files leave registry and running processes untouched.
    /// After a nonempty result, the caller must await `loader.reload()`.
    pub fn poll(&mut self, registry: &mut FactoryRegistry) -> Result<Vec<String>, ProcessError> {
        let mut prepared = Vec::new();
        for (name, watched) in &self.entries {
            let (root, sources) = read_sources(&watched.recipe)?;
            if !same_sources(&sources, &watched.sources) {
                let revision = snapshot(&watched.recipe, &root, &sources)?;
                prepared.push((name.clone(), sources, revision));
            }
        }
        let mut changed = Vec::new();
        for (name, sources, revision) in prepared {
            let watched = self.entries.get_mut(&name).expect("prepared watch entry");
            register_revision(
                registry,
                &name,
                watched.schema.clone(),
                revision,
                watched.key,
            );
            watched.sources = sources;
            changed.push(name);
        }
        Ok(changed)
    }
}
fn register_revision(
    registry: &mut FactoryRegistry,
    name: &str,
    schema: Schema,
    recipe: ProcessPlugin,
    key: ServiceKey<ProcessClient>,
) {
    let plugin_name = name.to_owned();
    registry.register(name, schema, move |config, _| {
        Ok(recipe
            .clone()
            .initialize(config.clone())
            .plugin(plugin_name.clone(), key))
    });
}
fn read_sources(recipe: &ProcessPlugin) -> Result<(PathBuf, Vec<SourceFile>), ProcessError> {
    let executable = fs::canonicalize(&recipe.executable)
        .map_err(|error| io_error("resolve executable", error))?;
    let root = executable
        .parent()
        .ok_or_else(|| ProcessError::InvalidConfig("executable needs a parent directory".into()))?
        .to_owned();
    let mut paths = vec![executable];
    for path in &recipe.dependencies {
        let path = fs::canonicalize(if path.is_absolute() {
            path.clone()
        } else {
            root.join(path)
        })
        .map_err(|error| io_error("resolve dependency", error))?;
        if !path.starts_with(&root) {
            return Err(ProcessError::InvalidConfig(
                "watched dependencies must be below the executable directory".into(),
            ));
        }
        if !paths.contains(&path) {
            paths.push(path);
        }
    }
    let mut remaining = MAX_ARTIFACT_BYTES;
    let mut sources = Vec::new();
    for (index, path) in paths.into_iter().enumerate() {
        let metadata = fs::metadata(&path).map_err(|error| io_error("inspect artifact", error))?;
        if !metadata.is_file() {
            return Err(ProcessError::InvalidConfig(
                "artifacts must be regular files".into(),
            ));
        }
        #[cfg(unix)]
        if index == 0 {
            use std::os::unix::fs::PermissionsExt;
            if metadata.permissions().mode() & 0o111 == 0 {
                return Err(ProcessError::InvalidConfig(
                    "plugin executable has no execute permission".into(),
                ));
            }
        }
        #[cfg(not(unix))]
        let _ = index;
        let mut bytes = Vec::new();
        fs::File::open(&path)
            .map_err(|error| io_error("open artifact", error))?
            .take(remaining as u64 + 1)
            .read_to_end(&mut bytes)
            .map_err(|error| io_error("read artifact", error))?;
        if bytes.len() > remaining {
            return Err(ProcessError::InvalidConfig(
                "plugin artifact files exceed 256 MiB".into(),
            ));
        }
        remaining -= bytes.len();
        let relative = path
            .strip_prefix(&root)
            .expect("artifact root checked")
            .to_owned();
        sources.push(SourceFile {
            path,
            relative,
            bytes: bytes.into(),
            permissions: metadata.permissions(),
        });
    }
    Ok((root, sources))
}
fn same_sources(left: &[SourceFile], right: &[SourceFile]) -> bool {
    left.len() == right.len()
        && left.iter().zip(right).all(|(left, right)| {
            let same = left.path == right.path
                && left.relative == right.relative
                && left.bytes == right.bytes
                && left.permissions.readonly() == right.permissions.readonly();
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                same && left.permissions.mode() == right.permissions.mode()
            }
            #[cfg(not(unix))]
            {
                same
            }
        })
}
fn snapshot(
    recipe: &ProcessPlugin,
    root: &Path,
    sources: &[SourceFile],
) -> Result<ProcessPlugin, ProcessError> {
    let directory = loop {
        let id = NEXT_ARTIFACT.fetch_add(1, Ordering::Relaxed);
        let directory =
            std::env::temp_dir().join(format!("cordis-process-{}-{id}", std::process::id()));
        #[cfg(unix)]
        let result = {
            use std::os::unix::fs::DirBuilderExt;
            fs::DirBuilder::new().mode(0o700).create(&directory)
        };
        #[cfg(not(unix))]
        let result = fs::create_dir(&directory);
        match result {
            Ok(()) => break directory,
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(io_error("create artifact directory", error)),
        }
    };
    let artifact = Arc::new(Artifact {
        directory: fs::canonicalize(&directory)
            .map_err(|error| io_error("resolve artifact directory", error))?,
        sources: sources.to_vec(),
    });
    for source in sources {
        let path = artifact.directory.join(&source.relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent)
                .map_err(|error| io_error("create artifact subdirectory", error))?;
        }
        fs::write(&path, &*source.bytes).map_err(|error| io_error("write artifact", error))?;
        fs::set_permissions(&path, source.permissions.clone())
            .map_err(|error| io_error("set artifact permissions", error))?;
    }
    let mut revision = recipe.clone();
    revision.executable = artifact.directory.join(&sources[0].relative);
    for arg in &mut revision.args {
        if Path::new(arg).is_absolute() {
            if let Some(source) = sources.iter().find(|source| {
                source.path == Path::new(arg) || root.join(&source.relative) == Path::new(arg)
            }) {
                *arg = artifact.directory.join(&source.relative).into_os_string();
            }
        }
    }
    revision.working_directory = Some(match &recipe.working_directory {
        None => artifact.directory.clone(),
        Some(directory) => {
            let directory = fs::canonicalize(if directory.is_absolute() {
                directory.clone()
            } else {
                root.join(directory)
            })
            .map_err(|error| io_error("resolve working directory", error))?;
            let relative = directory.strip_prefix(root).map_err(|_| {
                ProcessError::InvalidConfig(
                    "watched working directory must be below executable directory".into(),
                )
            })?;
            let directory = artifact.directory.join(relative);
            fs::create_dir_all(&directory)
                .map_err(|error| io_error("create working directory", error))?;
            directory
        }
    });
    revision.artifact = Some(artifact);
    Ok(revision)
}
