//! Version-bound native factories. This adapter holds no second Cordis graph.
//! Libraries stay mapped for process lifetime; releasing a session only asks
//! its originating SDK to destroy objects after real cleanup has succeeded.

#[path = "dynamic_ffi.rs"]
mod ffi;
use super::{
    CancellationToken, FactoryDescriptor, FactoryRegistry, PluginContext, PluginFactory,
    PluginFuture, PluginInstance, PluginResult,
};
use cordis_plugin_api::WakeV1;
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::{
    collections::BTreeMap,
    fs::{self, File, OpenOptions},
    future::Future,
    io::{Read, Write},
    path::{Path, PathBuf},
    pin::Pin,
    sync::{
        atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering},
        Arc, Mutex, OnceLock,
    },
    task::{Context, Poll, Waker},
    time::{SystemTime, UNIX_EPOCH},
};

static NEXT_MODULE: AtomicU64 = AtomicU64::new(1);
static NEXT_WAKE: AtomicU64 = AtomicU64::new(1);
static WAKES: OnceLock<Mutex<BTreeMap<u64, Waker>>> = OnceLock::new();

fn wakes() -> &'static Mutex<BTreeMap<u64, Waker>> {
    WAKES.get_or_init(|| Mutex::new(BTreeMap::new()))
}
fn allocate(counter: &AtomicU64, error: &str) -> PluginResult<u64> {
    counter
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |v| v.checked_add(1))
        .map_err(|_| error.to_owned())
}
extern "C" fn wake(token: u64) {
    // The callback lives in the resident host, and carries no dereferenceable
    // pointer. Late callbacks simply find no token. Wake outside the map lock.
    let waker = wakes()
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .get(&token)
        .cloned();
    if let Some(waker) = waker {
        if let Err(payload) =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| waker.wake()))
        {
            std::mem::forget(payload);
        }
    }
}
fn quiet_wake() -> WakeV1 {
    WakeV1 { token: 0, wake }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Description {
    module_id: String,
    version: String,
    factories: Vec<FactoryDescriptor>,
}

pub(crate) struct Module {
    id: String,
    path: PathBuf,
    sha256: String,
    description: Description,
    image: ffi::Image,
    instances: AtomicUsize,
    jobs: AtomicUsize,
    retained_instances: AtomicUsize,
    retained_jobs: AtomicUsize,
}
impl Module {
    fn request(&self, request: Value) -> PluginResult<Value> {
        self.image.invoke(&request, quiet_wake())
    }
    fn factory_ref(&self, name: &str) -> String {
        format!("@cordis/dynamic/{}/{}", self.id, name)
    }
    pub(crate) fn info(&self) -> Value {
        let factories: Vec<_> = self
            .description
            .factories
            .iter()
            .map(|descriptor| {
                let mut value = json!(descriptor);
                value["ref"] = json!(self.factory_ref(&descriptor.name));
                value
            })
            .collect();
        json!({"module":self.id,"pluginId":self.description.module_id,
            "buildId":self.description.version,"abi":1,"path":self.path,
            "sha256":self.sha256,"retained":true,"unloadSupported":false,
            "factories":factories,"resources":{
                "instances":self.instances.load(Ordering::Acquire),
                "jobs":self.jobs.load(Ordering::Acquire),
                "retainedInstances":self.retained_instances.load(Ordering::Acquire),
                "retainedJobs":self.retained_jobs.load(Ordering::Acquire)}})
    }
}

/// Validate and snapshot the exact main image bytes before native code executes.
/// Shared OS dependencies and arbitrary plugin top-level I/O are not isolated.
pub(crate) fn load(path: &str, expected: &str) -> PluginResult<Arc<Module>> {
    let id = allocate(&NEXT_MODULE, "NativeModuleCapacity")?.to_string();
    let (path, sha256) = snapshot(Path::new(path), expected, &id)?;
    let image = ffi::Image::load(&path)?;
    let raw = image.invoke(&json!({"op":"describe"}), quiet_wake())?;
    // SDK descriptor types reject unknown capability fields and method kinds.
    // The existing host descriptor remains backwards-compatible for statics.
    let _: Vec<cordis_plugin_api::FactoryDescriptor> = serde_json::from_value(
        raw.get("factories")
            .cloned()
            .ok_or("NativeModuleDescriptor")?,
    )
    .map_err(|e| format!("NativeModuleUnsupportedCapability: {e}"))?;
    let description: Description =
        serde_json::from_value(raw).map_err(|e| format!("NativeModuleDescriptor: {e}"))?;
    validate(&description)?;
    Ok(Arc::new(Module {
        id,
        path,
        sha256,
        description,
        image,
        instances: AtomicUsize::new(0),
        jobs: AtomicUsize::new(0),
        retained_instances: AtomicUsize::new(0),
        retained_jobs: AtomicUsize::new(0),
    }))
}

fn validate(description: &Description) -> PluginResult<()> {
    if description.module_id.is_empty()
        || description.version.is_empty()
        || description.factories.is_empty()
    {
        return Err("NativeModuleEmptyDescriptor".into());
    }
    let mut registry = FactoryRegistry::new();
    for descriptor in &description.factories {
        if !descriptor.inject.is_empty()
            || descriptor
                .services
                .iter()
                .flat_map(|s| &s.methods)
                .any(|m| !matches!(m.kind, super::MethodKind::Sync | super::MethodKind::Async))
        {
            return Err("NativeModuleUnsupportedCapability".into());
        }
        // Reuse the same duplicate/name validation as ordinary Rust factories.
        registry.register(DescriptorOnly(descriptor.clone()))?;
    }
    Ok(())
}
struct DescriptorOnly(FactoryDescriptor);
impl PluginFactory for DescriptorOnly {
    fn descriptor(&self) -> FactoryDescriptor {
        self.0.clone()
    }
    fn create(&self, _: Value) -> PluginResult<Arc<dyn PluginInstance>> {
        Err("DescriptorOnly".into())
    }
}

pub(crate) fn verify(path: &str, expected: &str) -> PluginResult<()> {
    verified_bytes(Path::new(path), expected).map(|_| ())
}
fn verified_bytes(source: &Path, expected: &str) -> PluginResult<(Vec<u8>, String)> {
    if !source.is_absolute() {
        return Err("NativeModulePathMustBeAbsolute".into());
    }
    if expected.len() != 64
        || !expected
            .bytes()
            .all(|c| c.is_ascii_digit() || (b'a'..=b'f').contains(&c))
    {
        return Err("NativeModuleInvalidSha256".into());
    }
    // Metadata and bytes are read from the same opened file, not a path checked
    // before reopening. Renaming an artifact while loading cannot change them.
    let mut file = File::open(source).map_err(|e| format!("NativeModuleRead: {e}"))?;
    if !file.metadata().map_err(|e| e.to_string())?.is_file() {
        return Err("NativeModuleNotRegularFile".into());
    }
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes).map_err(|e| e.to_string())?;
    let digest = format!("{:x}", Sha256::digest(&bytes));
    if digest != expected {
        return Err("NativeModuleDigestMismatch".into());
    }
    Ok((bytes, digest))
}
fn snapshot(source: &Path, expected: &str, id: &str) -> PluginResult<(PathBuf, String)> {
    let (bytes, digest) = verified_bytes(source, expected)?;
    let stamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|e| e.to_string())?
        .as_nanos();
    let dir =
        std::env::temp_dir().join(format!("cordis-native-{}-{stamp}-{id}", std::process::id()));
    let mut builder = fs::DirBuilder::new();
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;
        builder.mode(0o700);
    }
    builder
        .create(&dir)
        .map_err(|e| format!("NativeModuleSnapshot: {e}"))?;
    let extension = source.extension().and_then(|e| e.to_str()).unwrap_or("bin");
    let target = dir.join(format!("image-{digest}.{extension}"));
    let mut copy = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&target)
        .map_err(|e| e.to_string())?;
    copy.write_all(&bytes)
        .and_then(|_| copy.sync_all())
        .map_err(|e| e.to_string())?;
    let mut permissions = copy.metadata().map_err(|e| e.to_string())?.permissions();
    permissions.set_readonly(true);
    fs::set_permissions(&target, permissions).map_err(|e| e.to_string())?;
    drop(copy);
    // These intentionally retained files accompany process-lifetime images.
    Ok((target, digest))
}

struct Factory {
    module: Arc<Module>,
    descriptor: FactoryDescriptor,
}
impl PluginFactory for Factory {
    fn descriptor(&self) -> FactoryDescriptor {
        let mut descriptor = self.descriptor.clone();
        descriptor.name = self.module.factory_ref(&descriptor.name);
        descriptor
    }
    fn create(&self, config: Value) -> PluginResult<Arc<dyn PluginInstance>> {
        let value = self
            .module
            .request(json!({"op":"create","factory":self.descriptor.name,"config":config}))?;
        let handle = handle(&value, "instance")?;
        self.module.instances.fetch_add(1, Ordering::AcqRel);
        Ok(Arc::new(Instance {
            lease: Arc::new(InstanceLease {
                module: self.module.clone(),
                handle,
                destroyed: AtomicBool::new(false),
            }),
            services: self
                .descriptor
                .services
                .iter()
                .map(|s| s.name.clone())
                .collect(),
        }))
    }
}
struct InstanceLease {
    module: Arc<Module>,
    handle: u64,
    destroyed: AtomicBool,
}
impl InstanceLease {
    fn destroy(&self) -> PluginResult<()> {
        if !self.destroyed.load(Ordering::Acquire) {
            self.module
                .request(json!({"op":"destroy","instance":self.handle}))?;
            self.destroyed.store(true, Ordering::Release);
        }
        Ok(())
    }
}
impl Drop for InstanceLease {
    fn drop(&mut self) {
        // destroy is resource destruction, never a replacement for cleanup.
        // The SDK rejects it for effects, pending jobs, or failed cleanup.
        if self.destroy().is_err() {
            self.module
                .retained_instances
                .fetch_add(1, Ordering::AcqRel);
        }
        self.module.instances.fetch_sub(1, Ordering::AcqRel);
    }
}
struct Instance {
    lease: Arc<InstanceLease>,
    services: Vec<String>,
}
impl Instance {
    fn job(&self, request: Value, cancellation: CancellationToken) -> PluginResult<Job> {
        let token = allocate(&NEXT_WAKE, "NativeModuleWakeCapacity")?;
        let result = self.lease.module.request(request)?;
        let handle = handle(&result, "job")?;
        self.lease.module.jobs.fetch_add(1, Ordering::AcqRel);
        Ok(Job {
            lease: self.lease.clone(),
            handle,
            token,
            cancellation,
            cancelled: false,
            ready: false,
            dropped: false,
        })
    }
}
fn handle(value: &Value, key: &str) -> PluginResult<u64> {
    value
        .get(key)
        .and_then(Value::as_u64)
        .filter(|v| *v != 0)
        .ok_or_else(|| format!("NativeModuleInvalidHandle: {key}"))
}
impl PluginInstance for Instance {
    fn setup(&self, ctx: PluginContext) -> PluginFuture {
        let job = self.job(
            json!({"op":"setup","instance":self.lease.handle}),
            ctx.cancellation(),
        );
        let services = self.services.clone();
        Box::pin(async move {
            let result = job?.await?;
            for service in services {
                ctx.provide(&service).await?;
            }
            Ok(result)
        })
    }
    fn cleanup(&self, ctx: PluginContext) -> PluginFuture {
        let job = self.job(
            json!({"op":"cleanup","instance":self.lease.handle}),
            ctx.cancellation(),
        );
        let lease = self.lease.clone();
        Box::pin(async move {
            let result = job?.await?;
            // Destruction is part of successful finalization. A destructor
            // failure must be visible before the graph accepts cleanup.
            lease.destroy()?;
            Ok(result)
        })
    }
    fn call_sync(&self, service: &str, method: &str, args: Value) -> PluginResult<Value> {
        let result = self
            .lease
            .module
            .request(json!({"op":"call_sync","instance":self.lease.handle,
            "service":service,"method":method,"args":args}))?;
        result
            .get("value")
            .cloned()
            .ok_or("NativeModuleInvalidCallResult".into())
    }
    fn call_async(
        &self,
        ctx: PluginContext,
        service: &str,
        method: &str,
        args: Value,
    ) -> PluginFuture {
        let job = self.job(
            json!({"op":"call_async","instance":self.lease.handle,
            "service":service,"method":method,"args":args}),
            ctx.cancellation(),
        );
        Box::pin(async move { job?.await })
    }
}
struct Job {
    lease: Arc<InstanceLease>,
    handle: u64,
    token: u64,
    cancellation: CancellationToken,
    cancelled: bool,
    ready: bool,
    dropped: bool,
}
impl Future for Job {
    type Output = PluginResult<Value>;
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self.ready {
            return Poll::Ready(Err("NativeModuleJobAlreadyReady".into()));
        }
        wakes()
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .insert(self.token, cx.waker().clone());
        if self.cancellation.is_cancelled() && !self.cancelled {
            self.cancelled = true;
            if let Err(error) = self
                .lease
                .module
                .request(json!({"op":"cancel","job":self.handle}))
            {
                return Poll::Ready(Err(error));
            }
        }
        let reply = self.lease.module.image.invoke(
            &json!({"op":"poll","job":self.handle}),
            WakeV1 {
                token: self.token,
                wake,
            },
        );
        let value = match reply {
            Ok(v) => v,
            Err(e) => return Poll::Ready(Err(e)),
        };
        match value.get("state").and_then(Value::as_str) {
            Some("pending") => Poll::Pending,
            Some("ready") => {
                self.ready = true;
                // Surface a failed native job release before reporting action
                // success, especially for cleanup. Never hide it in Drop.
                if let Err(error) = self
                    .lease
                    .module
                    .request(json!({"op":"drop_job","job":self.handle}))
                {
                    return Poll::Ready(Err(error));
                }
                self.dropped = true;
                let Some(result) = value
                    .get("result")
                    .and_then(Value::as_object)
                    .filter(|v| v.len() == 1)
                else {
                    return Poll::Ready(Err("NativeModuleInvalidJobResult".into()));
                };
                if let Some(value) = result.get("ok") {
                    return Poll::Ready(Ok(value.clone()));
                }
                Poll::Ready(Err(result
                    .get("error")
                    .and_then(Value::as_str)
                    .unwrap_or("NativeModuleInvalidJobResult")
                    .to_owned()))
            }
            _ => Poll::Ready(Err("NativeModuleInvalidJobState".into())),
        }
    }
}
impl Drop for Job {
    fn drop(&mut self) {
        wakes()
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .remove(&self.token);
        // Backend finalization cancels host tokens but cannot poll abandoned
        // futures again. Forward cooperative cancellation before retaining the
        // unresolved native job. No map/backend/native job lock is held here;
        // late wakes already have no destination. This is not completion.
        if !self.dropped && !self.cancelled {
            let _ = self
                .lease
                .module
                .request(json!({"op":"cancel","job":self.handle}));
        }
        // A faulted or abandoned native job cannot be called completed merely
        // because its Rust wrapper was dropped. Its originating image persists.
        if !self.dropped {
            self.lease
                .module
                .retained_jobs
                .fetch_add(1, Ordering::AcqRel);
        }
        self.lease.module.jobs.fetch_sub(1, Ordering::AcqRel);
    }
}

impl super::Backend {
    pub(crate) fn install_module(&mut self, module: Arc<Module>) -> PluginResult<Value> {
        let mut prepared = FactoryRegistry::new();
        for descriptor in &module.description.factories {
            let factory = Factory {
                module: module.clone(),
                descriptor: descriptor.clone(),
            };
            if self
                .registry
                .factories
                .contains_key(&factory.descriptor().name)
            {
                return Err("DuplicateOrEmptyFactory".into());
            }
            prepared.register(factory)?;
        }
        // No native plugin code runs between validation and this single commit.
        self.registry.factories.append(&mut prepared.factories);
        let result = module.info();
        self.modules.insert(module.id.clone(), module);
        Ok(result)
    }
    pub(crate) fn cached_module(&self, digest: &str) -> Option<Arc<Module>> {
        self.modules
            .values()
            .find(|module| module.sha256 == digest)
            .cloned()
    }
    pub(crate) fn module_info(&self) -> Value {
        json!({"modules":self.modules.values().map(|m|m.info()).collect::<Vec<_>>(),
            "retained":true,"unloadSupported":false,
            "retainedImageCount":ffi::image_count(),"retainedImageLimit":ffi::IMAGE_LIMIT})
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn rejects_unversioned_paths_and_digests_before_loading() {
        assert!(
            snapshot(Path::new("relative.dylib"), &"0".repeat(64), "test")
                .unwrap_err()
                .contains("Absolute")
        );
        assert!(snapshot(Path::new("/missing"), "abc", "test")
            .unwrap_err()
            .contains("Sha256"));
    }
    #[test]
    fn rejects_unsupported_capabilities_and_duplicate_factories() {
        let mut description = Description {
            module_id: "test".into(),
            version: "1".into(),
            factories: vec![FactoryDescriptor {
                name: "test".into(),
                inject: vec!["js".into()],
                services: vec![],
            }],
        };
        assert!(validate(&description)
            .unwrap_err()
            .contains("UnsupportedCapability"));
        description.factories[0].inject.clear();
        description.factories.push(description.factories[0].clone());
        assert!(validate(&description).unwrap_err().contains("Duplicate"));
    }
    #[test]
    fn snapshot_pins_verified_bytes_when_source_changes() {
        let id = allocate(&NEXT_MODULE, "test capacity").unwrap().to_string();
        let source =
            std::env::temp_dir().join(format!("cordis-native-source-{}-{id}", std::process::id()));
        fs::write(&source, b"version one").unwrap();
        let expected = format!("{:x}", Sha256::digest(b"version one"));
        let (copy, digest) = snapshot(&source, &expected, &id).unwrap();
        assert_eq!(digest, expected);
        assert_ne!(copy, source);
        fs::write(&source, b"version two").unwrap();
        assert_eq!(fs::read(&copy).unwrap(), b"version one");
        assert!(verify(source.to_str().unwrap(), &expected)
            .unwrap_err()
            .contains("DigestMismatch"));
        assert!(copy.metadata().unwrap().permissions().readonly());
        fs::remove_file(source).unwrap();
        fs::remove_dir_all(copy.parent().unwrap()).unwrap();
    }
    #[test]
    fn abandoned_job_forwards_cancel_after_retiring_wake_and_remains_unresolved() {
        let module = Arc::new(Module {
            id: "probe".into(),
            path: PathBuf::new(),
            sha256: String::new(),
            description: Description {
                module_id: "probe".into(),
                version: "1".into(),
                factories: vec![],
            },
            image: ffi::cancellation_probe(),
            instances: AtomicUsize::new(1),
            jobs: AtomicUsize::new(1),
            retained_instances: AtomicUsize::new(0),
            retained_jobs: AtomicUsize::new(0),
        });
        let lease = Arc::new(InstanceLease {
            module: module.clone(),
            handle: 1,
            destroyed: AtomicBool::new(true),
        });
        let token = allocate(&NEXT_WAKE, "probe wake").unwrap();
        wakes().lock().unwrap().insert(token, Waker::noop().clone());
        ffi::set_probe_token(token);
        drop(Job {
            lease,
            handle: 7,
            token,
            cancellation: CancellationToken::default(),
            cancelled: false,
            ready: false,
            dropped: false,
        });
        assert_eq!(ffi::probe_observation(), (1, true, true));
        assert!(!wakes().lock().unwrap().contains_key(&token));
        assert_eq!(module.jobs.load(Ordering::Acquire), 0);
        assert_eq!(module.retained_jobs.load(Ordering::Acquire), 1);
    }
    #[test]
    fn empty_domain_reports_no_module_resources_and_process_budget() {
        let backend = super::super::Backend::new(FactoryRegistry::new(), Arc::new(|| {}));
        let report = backend.module_info();
        assert_eq!(report["modules"], json!([]));
        assert_eq!(report["retainedImageLimit"], 128);
        assert_eq!(report["unloadSupported"], false);
        assert!(backend.cached_module(&"0".repeat(64)).is_none());
    }
    #[test]
    fn late_wakes_are_safe_after_token_retirement() {
        wake(u64::MAX);
        wake(0);
    }
}
