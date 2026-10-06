//! Version-bound native factories. This adapter holds no second Cordis graph.
//! Libraries stay mapped for process lifetime; releasing a session only asks
//! its originating SDK to destroy objects after real cleanup has succeeded.

#[path = "dynamic_checkpoint.rs"]
pub(crate) mod checkpoint;
#[cfg(test)]
#[path = "dynamic_checkpoint_tests.rs"]
mod checkpoint_tests;
#[path = "dynamic_children.rs"]
pub(crate) mod children;
#[cfg(test)]
#[path = "dynamic_children_tests.rs"]
mod children_tests;
#[path = "dynamic_ffi.rs"]
mod ffi;
#[path = "dynamic_resources.rs"]
mod resources;
#[path = "dynamic_reverse.rs"]
mod reverse;
#[cfg(test)]
#[path = "dynamic_reverse_tests.rs"]
mod reverse_tests;
use super::{
    CancellationToken, FactoryDescriptor, FactoryRegistry, PluginContext, PluginFactory,
    PluginFuture, PluginInstance, PluginResult,
};
use cordis_plugin_api::{
    ReverseCall, WakeV1, MAX_MESSAGE_BYTES, MAX_PENDING_CALLS, MAX_VALUE_DEPTH,
};
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
    #[serde(default)]
    checkpoint_schemas: BTreeMap<String, cordis_plugin_api::CheckpointSchema>,
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
    reverse_calls: AtomicUsize,
    retained_reverse_calls: AtomicUsize,
    streams: AtomicUsize,
    objects: AtomicUsize,
    retained_streams: AtomicUsize,
    retained_objects: AtomicUsize,
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
                let mut value = children::metadata(descriptor, &self.factory_ref(&descriptor.name));
                if let Some(schema) = self.description.checkpoint_schemas.get(&descriptor.name) {
                    value["checkpointSchema"] = json!(schema);
                }
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
                "retainedJobs":self.retained_jobs.load(Ordering::Acquire),
                "reverseCalls":self.reverse_calls.load(Ordering::Acquire),
                "retainedReverseCalls":self.retained_reverse_calls.load(Ordering::Acquire),
                "streams":self.streams.load(Ordering::Acquire),
                "objects":self.objects.load(Ordering::Acquire),
                "retainedStreams":self.retained_streams.load(Ordering::Acquire),
                "retainedObjects":self.retained_objects.load(Ordering::Acquire)}})
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
        reverse_calls: AtomicUsize::new(0),
        retained_reverse_calls: AtomicUsize::new(0),
        streams: AtomicUsize::new(0),
        objects: AtomicUsize::new(0),
        retained_streams: AtomicUsize::new(0),
        retained_objects: AtomicUsize::new(0),
    }))
}

fn validate(description: &Description) -> PluginResult<()> {
    if description.module_id.is_empty()
        || description.version.is_empty()
        || description.factories.is_empty()
    {
        return Err("NativeModuleEmptyDescriptor".into());
    }
    for (factory, schema) in &description.checkpoint_schemas {
        schema.validate()?;
        if !description.factories.iter().any(|d| &d.name == factory) {
            return Err("NativeCheckpointUnknownFactory".into());
        }
    }
    let mut registry = FactoryRegistry::new();
    for descriptor in &description.factories {
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
    children: Arc<children::Children>,
    checkpoints: Arc<checkpoint::Journal>,
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
                cleaned: AtomicBool::new(false),
                finalization: Finalization::default(),
                children: self.children.clone(),
                checkpoint: checkpoint::InstanceState::new(
                    self.checkpoints.clone(),
                    &self.module,
                    &self.descriptor.name,
                    true,
                ),
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
    cleaned: AtomicBool,
    finalization: Finalization,
    children: Arc<children::Children>,
    checkpoint: Arc<checkpoint::InstanceState>,
}

/// A native cleanup hook may finish before the host journal can finish. Keep
/// that phase and its original action id so an explicit retry drains the old
/// obligation using the new cleanup context, without repeating the native hook.
#[derive(Default)]
struct Finalization(Mutex<Option<u64>>);
impl Finalization {
    fn begin(&self, context: &PluginContext) {
        *self.0.lock().unwrap() = Some(context.job);
    }
    fn pending(&self) -> bool {
        self.0.lock().unwrap().is_some()
    }
    async fn drain(&self, context: &PluginContext, retry: bool) -> PluginResult<()> {
        let job = *self.0.lock().unwrap();
        if let Some(job) = job {
            context.drain_js_resources(Some(job), retry).await?;
            *self.0.lock().unwrap() = None;
        }
        Ok(())
    }
}
impl InstanceLease {
    fn destroy(&self) -> PluginResult<()> {
        if self.finalization.pending() {
            return Err("NativeModuleFinalizationPending".into());
        }
        if !self.destroyed.load(Ordering::Acquire) {
            self.module
                .request(json!({"op":"destroy","instance":self.handle}))?;
            self.destroyed.store(true, Ordering::Release);
            self.checkpoint.destroyed();
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
    fn job(&self, request: Value, context: PluginContext) -> PluginResult<Job> {
        self.lease.job(request, context)
    }
}
impl InstanceLease {
    fn job(self: &Arc<Self>, request: Value, context: PluginContext) -> PluginResult<Job> {
        let token = allocate(&NEXT_WAKE, "NativeModuleWakeCapacity")?;
        let result = self.module.request(request)?;
        let handle = handle(&result, "job")?;
        self.module.jobs.fetch_add(1, Ordering::AcqRel);
        Ok(Job {
            lease: self.clone(),
            handle,
            token,
            cancellation: context.cancellation(),
            context: Some(context),
            calls: BTreeMap::new(),
            resources: reverse::Resources::default(),
            last_request: 0,
            failure: None,
            cancelled: false,
            ready: false,
            native_result: None,
            drain: None,
            draining: false,
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
        self.lease.checkpoint.bind(ctx.session);
        let lease = self.lease.clone();
        let services = self.services.clone();
        Box::pin(async move {
            lease.checkpoint.restore(&lease.module, lease.handle)?;
            let result = lease
                .job(json!({"op":"setup","instance":lease.handle}), ctx.clone())?
                .await?;
            for service in services {
                ctx.provide(&service).await?;
            }
            lease.checkpoint.setup_done();
            Ok(result)
        })
    }
    fn cleanup(&self, ctx: PluginContext) -> PluginFuture {
        let lease = self.lease.clone();
        Box::pin(async move {
            lease.finalization.drain(&ctx, true).await?;
            if !lease.cleaned.load(Ordering::Acquire) {
                lease.checkpoint.capture(&lease.module, lease.handle)?;
                let job =
                    lease.job(json!({"op":"cleanup","instance":lease.handle}), ctx.clone())?;
                lease.finalization.begin(&ctx);
                let result = job.await;
                if result.is_ok() {
                    lease.cleaned.store(true, Ordering::Release);
                }
                lease.finalization.drain(&ctx, false).await?;
                result?;
            }
            // Destruction follows both native cleanup and actual JS resource
            // finalization. Neither Drop nor retry may bypass the journal.
            lease.destroy()?;
            Ok(Value::Null)
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
    fn open_stream(
        &self,
        service: &str,
        method: &str,
        args: Value,
    ) -> PluginResult<Arc<dyn super::PluginStream>> {
        resources::open_stream(self.lease.clone(), service, method, args)
    }
    fn open_object(
        &self,
        service: &str,
        method: &str,
        args: Value,
    ) -> PluginResult<Arc<dyn super::PluginObject>> {
        resources::open_object(self.lease.clone(), service, method, args)
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
            ctx.clone(),
        );
        Box::pin(async move { job?.await })
    }
}
struct Job {
    lease: Arc<InstanceLease>,
    handle: u64,
    token: u64,
    cancellation: CancellationToken,
    context: Option<PluginContext>,
    calls: BTreeMap<u64, reverse::ReverseFuture>,
    resources: reverse::Resources,
    last_request: u64,
    failure: Option<String>,
    cancelled: bool,
    ready: bool,
    native_result: Option<PluginResult<Value>>,
    drain: Option<PluginFuture>,
    draining: bool,
    dropped: bool,
}
/// Check application data before putting it inside a wire envelope. A rejected
/// JS result still resolves its native request; it never becomes a transport
/// error which could strand an already completed external call.
fn bounded_reverse_result(result: PluginResult<Value>) -> PluginResult<Value> {
    let value = match result {
        Err(error) if error.len() > 4096 => return Err("PluginErrorTooLarge".into()),
        result => result?,
    };
    let mut pending = vec![(&value, 0)];
    while let Some((value, depth)) = pending.pop() {
        match value {
            Value::Array(items) => {
                if depth == MAX_VALUE_DEPTH {
                    return Err("ValueTooDeep".into());
                }
                pending.extend(items.iter().map(|value| (value, depth + 1)));
            }
            Value::Object(items) => {
                if depth == MAX_VALUE_DEPTH {
                    return Err("ValueTooDeep".into());
                }
                pending.extend(items.values().map(|value| (value, depth + 1)));
            }
            _ => {}
        }
    }
    if serde_json::to_vec(&value).map_or(true, |bytes| bytes.len() > MAX_MESSAGE_BYTES / 2) {
        return Err("ResultTooLarge".into());
    }
    Ok(value)
}
impl Job {
    fn poll_drain(&mut self, cx: &mut Context<'_>) -> Poll<()> {
        if let Some(drain) = &mut self.drain {
            if drain.as_mut().poll(cx).is_pending() {
                return Poll::Pending;
            }
            // A failure remains in the resident journal. The outer action (or
            // the explicit native cleanup phase) propagates it without retry.
            self.drain = None;
        }
        Poll::Ready(())
    }
    fn finish_native(&mut self, cx: &mut Context<'_>) -> Poll<PluginResult<Value>> {
        if self.poll_drain(cx).is_pending() {
            return Poll::Pending;
        }
        Poll::Ready(
            self.native_result
                .take()
                .unwrap_or_else(|| Err("NativeModuleJobAlreadyReady".into())),
        )
    }
    fn receive_calls(&mut self, value: Option<&Value>) -> PluginResult<()> {
        let Some(value) = value else {
            return Ok(());
        };
        let calls: Vec<ReverseCall> =
            serde_json::from_value(value.clone()).map_err(|_| "NativeModuleInvalidReverseCalls")?;
        if self.calls.len() + calls.len() > MAX_PENDING_CALLS {
            return Err("NativeModuleReverseCallCapacity".into());
        }
        // Validate the whole batch before polling any external operation. IDs
        // are monotonic per native job, so a duplicate cannot dispatch twice.
        let mut last = self.last_request;
        for call in &calls {
            if call.request <= last {
                return Err("NativeModuleDuplicateReverseCall".into());
            }
            last = call.request;
        }
        let context = self.context.as_ref().ok_or("NativeModuleMissingContext")?;
        for call in calls {
            let request = call.request;
            let future = self
                .resources
                .dispatch(self.lease.clone(), context.clone(), call);
            self.calls.insert(request, future);
            self.lease
                .module
                .reverse_calls
                .fetch_add(1, Ordering::AcqRel);
        }
        self.last_request = last;
        Ok(())
    }
    fn poll_calls(&mut self, cx: &mut Context<'_>) {
        let mut completed = Vec::new();
        for (&request, future) in &mut self.calls {
            if let Poll::Ready(result) = future.as_mut().poll(cx) {
                completed.push((request, result));
            }
        }
        for (request, result) in completed {
            self.calls.remove(&request);
            self.lease
                .module
                .reverse_calls
                .fetch_sub(1, Ordering::AcqRel);
            if let Err(error) = self.lease.module.request(json!({"op":"resolve_call",
                "job":self.handle,"request":request,"result":self.resources.resolve(result)}))
            {
                self.lease
                    .module
                    .retained_reverse_calls
                    .fetch_add(1, Ordering::AcqRel);
                self.failure.get_or_insert(error);
            }
        }
    }
    fn fail_after_drain(
        &mut self,
        error: String,
        cx: &mut Context<'_>,
    ) -> Poll<PluginResult<Value>> {
        self.failure.get_or_insert(error);
        self.poll_calls(cx);
        if self.calls.is_empty() {
            Poll::Ready(Err(self.failure.take().unwrap()))
        } else {
            Poll::Pending
        }
    }
}
impl Future for Job {
    type Output = PluginResult<Value>;
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self.ready {
            return self.finish_native(cx);
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
                return self.fail_after_drain(error, cx);
            }
        }
        self.poll_calls(cx);
        let _ = self.poll_drain(cx);
        if let Some(error) = self.failure.clone() {
            return self.fail_after_drain(error, cx);
        }
        let reply = self.lease.module.image.invoke(
            &json!({"op":"poll","job":self.handle}),
            WakeV1 {
                token: self.token,
                wake,
            },
        );
        let value = match reply {
            Ok(value) => value,
            Err(error) => return self.fail_after_drain(error, cx),
        };
        if let Err(error) = self.receive_calls(value.get("calls")) {
            return self.fail_after_drain(error, cx);
        }
        match value.get("state").and_then(Value::as_str) {
            Some("pending") => {
                // Creation of these futures only uses the existing host RPC
                // queue. JavaScript executes after the native poll releases its
                // borrows, and completion wakes this exact action's task.
                self.poll_calls(cx);
                if value.get("draining") == Some(&Value::Bool(true))
                    && value.get("queuedCalls") != Some(&Value::Bool(true))
                    && !self.draining
                {
                    self.draining = true;
                    if let Some(mut context) = self.context.clone() {
                        context.cleanup = true;
                        let job = context.job;
                        self.drain = Some(Box::pin(async move {
                            context.drain_js_resources(Some(job), false).await
                        }));
                    }
                }
                let _ = self.poll_drain(cx);
                if let Some(error) = self.failure.clone() {
                    self.fail_after_drain(error, cx)
                } else {
                    Poll::Pending
                }
            }
            Some("ready") => {
                if !self.calls.is_empty() {
                    return self.fail_after_drain("NativeModuleReadyWithReverseCalls".into(), cx);
                }
                self.ready = true;
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
                    .filter(|value| value.len() == 1)
                else {
                    return Poll::Ready(Err("NativeModuleInvalidJobResult".into()));
                };
                self.native_result = Some(if let Some(value) = result.get("ok") {
                    Ok(value.clone())
                } else {
                    Err(result
                        .get("error")
                        .and_then(Value::as_str)
                        .unwrap_or("NativeModuleInvalidJobResult")
                        .to_owned())
                });
                self.finish_native(cx)
            }
            _ => self.fail_after_drain("NativeModuleInvalidJobState".into(), cx),
        }
    }
}

impl Drop for Job {
    fn drop(&mut self) {
        wakes()
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .remove(&self.token);
        if !self.calls.is_empty() {
            self.lease
                .module
                .reverse_calls
                .fetch_sub(self.calls.len(), Ordering::AcqRel);
            self.lease
                .module
                .retained_reverse_calls
                .fetch_add(self.calls.len(), Ordering::AcqRel);
        }
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
                children: self.native_children.clone(),
                checkpoints: self.native_checkpoints.clone(),
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
            "retainedImageCount":ffi::image_count(),"retainedImageLimit":ffi::IMAGE_LIMIT,"checkpoints":self.native_checkpoints.info()})
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
            checkpoint_schemas: BTreeMap::new(),
            factories: vec![FactoryDescriptor {
                name: "test".into(),
                inject: vec!["js".into()],
                services: vec![],
            }],
        };
        validate(&description).unwrap();
        description.factories[0].inject.push("js".into());
        assert!(validate(&description)
            .unwrap_err()
            .contains("DuplicateOrEmptyInjection"));
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
                checkpoint_schemas: BTreeMap::new(),
            },
            image: ffi::cancellation_probe(),
            instances: AtomicUsize::new(1),
            jobs: AtomicUsize::new(1),
            retained_instances: AtomicUsize::new(0),
            retained_jobs: AtomicUsize::new(0),
            reverse_calls: AtomicUsize::new(0),
            retained_reverse_calls: AtomicUsize::new(0),
            streams: AtomicUsize::new(0),
            objects: AtomicUsize::new(0),
            retained_streams: AtomicUsize::new(0),
            retained_objects: AtomicUsize::new(0),
        });
        let lease = Arc::new(InstanceLease {
            module: module.clone(),
            handle: 1,
            destroyed: AtomicBool::new(true),
            cleaned: AtomicBool::new(false),
            finalization: Finalization::default(),
            children: Arc::new(children::Children::new(Arc::new(|| {}))),
            checkpoint: checkpoint::InstanceState::new(
                Arc::new(checkpoint::Journal::default()),
                &module,
                "probe",
                true,
            ),
        });
        let token = allocate(&NEXT_WAKE, "probe wake").unwrap();
        wakes().lock().unwrap().insert(token, Waker::noop().clone());
        ffi::set_probe_token(token);
        drop(Job {
            lease,
            handle: 7,
            token,
            cancellation: CancellationToken::default(),
            context: None,
            calls: BTreeMap::new(),
            resources: reverse::Resources::default(),
            last_request: 0,
            failure: None,
            cancelled: false,
            ready: false,
            native_result: None,
            drain: None,
            draining: false,
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
    pub(super) fn reverse_backend() -> (super::super::Backend, Arc<Module>, u64) {
        reverse_backend_config(Value::Null)
    }
    pub(super) fn reverse_backend_config(
        config: Value,
    ) -> (super::super::Backend, Arc<Module>, u64) {
        let image = ffi::reverse_probe();
        let description = serde_json::from_value(
            image
                .invoke(&json!({"op":"describe"}), quiet_wake())
                .unwrap(),
        )
        .unwrap();
        let module = Arc::new(Module {
            id: allocate(&NEXT_MODULE, "probe").unwrap().to_string(),
            path: PathBuf::new(),
            sha256: String::new(),
            description,
            image,
            instances: AtomicUsize::new(0),
            jobs: AtomicUsize::new(0),
            retained_instances: AtomicUsize::new(0),
            retained_jobs: AtomicUsize::new(0),
            reverse_calls: AtomicUsize::new(0),
            retained_reverse_calls: AtomicUsize::new(0),
            streams: AtomicUsize::new(0),
            objects: AtomicUsize::new(0),
            retained_streams: AtomicUsize::new(0),
            retained_objects: AtomicUsize::new(0),
        });
        let mut backend = super::super::Backend::new(FactoryRegistry::new(), Arc::new(|| {}));
        backend.install_module(module.clone()).unwrap();
        let start = backend
            .start(1, 1, &module.factory_ref("reverse"), config)
            .unwrap();
        let session = number(&start, "session");
        let poll = backend.poll();
        assert_eq!(poll["calls"][0]["method"], "setup");
        assert_eq!(poll["calls"][0]["restoring"], false);
        backend
            .reply(number(&poll["calls"][0], "request"), Ok(Value::Null))
            .unwrap();
        let mut complete = false;
        for _ in 0..10 {
            let poll = backend.poll();
            for call in poll["calls"].as_array().unwrap() {
                assert_eq!(call["kind"], "provide");
                backend
                    .reply(
                        number(call, "request"),
                        Ok(json!({"publication":"3","port":{"key":"4","realm":"0"}})),
                    )
                    .unwrap();
            }
            if !poll["jobs"].as_array().unwrap().is_empty() {
                assert_eq!(poll["jobs"][0]["success"], true);
                complete = true;
                break;
            }
        }
        assert!(complete);
        (backend, module, session)
    }
    pub(super) fn number(value: &Value, name: &str) -> u64 {
        value[name].as_str().unwrap().parse().unwrap()
    }
    pub(super) fn cleanup_reverse(
        backend: &mut super::super::Backend,
        module: &Module,
        session: u64,
    ) {
        backend.cleanup(session).unwrap();
        let mut complete = false;
        let mut observed_cleanup = false;
        for _ in 0..10 {
            let poll = backend.poll();
            for call in poll["calls"].as_array().unwrap() {
                if call["kind"] == "call" {
                    assert_eq!(call["method"], "cleanup");
                    assert_eq!(call["restoring"], true);
                    observed_cleanup = true;
                }
                backend
                    .reply(number(call, "request"), Ok(Value::Null))
                    .unwrap();
            }
            if !poll["jobs"].as_array().unwrap().is_empty() {
                assert_eq!(poll["jobs"][0]["success"], true, "{poll}");
                complete = true;
                break;
            }
        }
        assert!(complete && observed_cleanup);
        backend.release(session).unwrap();
        assert!(module.info()["resources"]
            .as_object()
            .unwrap()
            .values()
            .all(|count| count == 0));
    }
    pub(super) fn call_result(backend: &mut super::super::Backend) -> Value {
        for _ in 0..10 {
            let poll = backend.poll();
            if let Some(result) = poll["jobs"].as_array().unwrap().first() {
                return result.clone();
            }
            assert_eq!(poll["calls"], json!([]));
        }
        panic!("native call did not finish after its actual replies");
    }
    #[test]
    fn reverse_calls_wait_for_out_of_order_js_completion() {
        let (mut backend, module, session) = reverse_backend();
        let started = backend
            .call(session, "native", "parallel", json!([]), false, false)
            .unwrap();
        let poll = backend.poll();
        assert_eq!(poll["calls"].as_array().unwrap().len(), 2);
        assert_eq!(module.info()["resources"]["reverseCalls"], 2);
        let first = number(&poll["calls"][0], "request");
        let second = number(&poll["calls"][1], "request");
        backend.reply(second, Ok(json!("second"))).unwrap();
        assert_eq!(backend.poll()["jobs"], json!([]));
        assert_eq!(module.info()["resources"]["reverseCalls"], 1);
        backend.reply(first, Ok(json!("first"))).unwrap();
        assert!(backend
            .reply(first, Ok(Value::Null))
            .unwrap_err()
            .contains("StaleRequest"));
        let result = call_result(&mut backend);
        assert_eq!(result["job"], started["job"]);
        assert_eq!(result["value"], json!(["first", "second"]));
        cleanup_reverse(&mut backend, &module, session);
    }
    #[test]
    fn identical_native_request_numbers_stay_isolated_between_jobs() {
        let (mut backend, module, session) = reverse_backend();
        let first = backend
            .call(session, "native", "forward", json!(["first"]), false, false)
            .unwrap();
        let second = backend
            .call(
                session,
                "native",
                "forward",
                json!(["second"]),
                false,
                false,
            )
            .unwrap();
        let poll = backend.poll();
        let calls = poll["calls"].as_array().unwrap();
        assert_eq!(calls.len(), 2);
        assert_ne!(calls[0]["request"], calls[1]["request"]);
        assert_eq!(calls[0]["job"], first["job"]);
        assert_eq!(calls[1]["job"], second["job"]);
        backend
            .reply(number(&calls[1], "request"), Ok(json!("second result")))
            .unwrap();
        let result = call_result(&mut backend);
        assert_eq!(result["job"], second["job"]);
        assert_eq!(result["value"], "second result");
        assert_eq!(module.info()["resources"]["reverseCalls"], 1);
        backend
            .reply(number(&calls[0], "request"), Ok(json!("first result")))
            .unwrap();
        let result = call_result(&mut backend);
        assert_eq!(result["job"], first["job"]);
        assert_eq!(result["value"], "first result");
        cleanup_reverse(&mut backend, &module, session);
    }
    #[test]
    fn dropped_reverse_future_and_cancellation_still_wait_for_real_js_reply() {
        let (mut backend, module, session) = reverse_backend();
        let started = backend
            .call(session, "native", "dropped", json!([]), false, false)
            .unwrap();
        let poll = backend.poll();
        let request = number(&poll["calls"][0], "request");
        backend.cancel_job(number(&started, "job")).unwrap();
        assert_eq!(backend.poll()["jobs"], json!([]));
        assert_eq!(module.info()["resources"]["reverseCalls"], 1);
        assert!(backend.cleanup(session).is_err());
        backend
            .reply(request, Ok(json!("actual completion")))
            .unwrap();
        let result = call_result(&mut backend);
        assert_eq!(result["success"], true);
        assert_eq!(result["value"], "returned");
        cleanup_reverse(&mut backend, &module, session);
    }
    #[test]
    fn reverse_reply_bounds_are_application_errors_and_do_not_strand_native_jobs() {
        let (mut backend, module, session) = reverse_backend();
        let near = Value::String("x".repeat(MAX_MESSAGE_BYTES / 2 - 2));
        let mut deep = Value::Null;
        for _ in 0..MAX_VALUE_DEPTH + 1 {
            deep = json!([deep]);
        }
        for (reply, expected) in [
            (Ok(near.clone()), Ok(near)),
            (
                Ok(Value::String("x".repeat(MAX_MESSAGE_BYTES))),
                Err("ResultTooLarge"),
            ),
            (Ok(deep), Err("ValueTooDeep")),
            (
                Err("x".repeat(MAX_MESSAGE_BYTES)),
                Err("PluginErrorTooLarge"),
            ),
        ] {
            backend
                .call(session, "native", "forward", json!([]), false, false)
                .unwrap();
            let poll = backend.poll();
            backend
                .reply(number(&poll["calls"][0], "request"), reply)
                .unwrap();
            let result = call_result(&mut backend);
            match expected {
                Ok(value) => {
                    assert_eq!(result["success"], true);
                    assert_eq!(result["value"], value);
                }
                Err(error) => {
                    assert_eq!(result["success"], false);
                    assert_eq!(result["error"], error);
                }
            }
            assert_eq!(module.info()["resources"]["jobs"], 0);
            assert_eq!(module.info()["resources"]["reverseCalls"], 0);
            assert_eq!(module.info()["resources"]["retainedJobs"], 0);
        }
        cleanup_reverse(&mut backend, &module, session);
    }
    pub(super) fn resource_call(backend: &mut super::super::Backend, method: &str) -> Value {
        for _ in 0..10 {
            let poll = backend.poll();
            assert_eq!(poll["jobs"], json!([]), "{poll}");
            if let Some(call) = poll["calls"].as_array().unwrap().first() {
                assert_eq!(poll["calls"].as_array().unwrap().len(), 1);
                assert_eq!(call["method"], method);
                return call.clone();
            }
        }
        panic!("native resource did not issue {method}");
    }
    #[test]
    fn native_stream_close_joins_reverse_pull_and_retries_failed_close() {
        let (mut backend, module, session) = reverse_backend();
        let stream = number(
            &backend
                .call(session, "native", "stream", json!([]), false, false)
                .unwrap(),
            "stream",
        );
        assert_eq!(module.info()["resources"]["streams"], 1);
        backend.stream_next(session, stream, false, false).unwrap();
        let pull = resource_call(&mut backend, "streamNext");
        backend.stream_close(session, stream).unwrap();
        assert_eq!(backend.poll()["jobs"], json!([]));
        assert!(backend.cleanup(session).is_err());
        backend
            .reply(number(&pull, "request"), Ok(json!("landed")))
            .unwrap();
        assert_eq!(call_result(&mut backend)["value"]["value"], "landed");
        let close = resource_call(&mut backend, "streamClose");
        assert_eq!(close["restoring"], true);
        backend
            .reply(number(&close, "request"), Err("retry native close".into()))
            .unwrap();
        assert_eq!(call_result(&mut backend)["success"], false);
        assert_eq!(module.info()["resources"]["streams"], 1);
        assert!(backend.stream_next(session, stream, false, false).is_err());
        backend.stream_close(session, stream).unwrap();
        let close = resource_call(&mut backend, "streamClose");
        backend
            .reply(number(&close, "request"), Ok(Value::Null))
            .unwrap();
        assert_eq!(call_result(&mut backend)["success"], true);
        assert_eq!(module.info()["resources"]["streams"], 0);
        cleanup_reverse(&mut backend, &module, session);
    }
    #[test]
    fn native_object_releases_borrowed_reference_without_user_close_and_retries_owned() {
        let (mut backend, module, session) = reverse_backend();
        let borrowed = number(
            &backend
                .call(
                    session,
                    "native",
                    "object",
                    json!(["borrowed"]),
                    false,
                    false,
                )
                .unwrap(),
            "object",
        );
        backend.object_close(session, borrowed).unwrap();
        assert_eq!(call_result(&mut backend)["success"], true);
        assert_eq!(module.info()["resources"]["objects"], 0);
        let object = number(
            &backend
                .call(session, "native", "object", json!([]), false, false)
                .unwrap(),
            "object",
        );
        backend
            .object_call(session, object, "call", json!([1]), false, false)
            .unwrap();
        let first = resource_call(&mut backend, "objectCall");
        backend
            .object_call(session, object, "call", json!([2]), false, false)
            .unwrap();
        let second = resource_call(&mut backend, "objectCall");
        backend.object_close(session, object).unwrap();
        assert_eq!(backend.poll()["jobs"], json!([]));
        backend
            .reply(number(&second, "request"), Ok(json!(2)))
            .unwrap();
        assert_eq!(call_result(&mut backend)["value"], 2);
        assert_eq!(backend.poll()["calls"], json!([]));
        backend
            .reply(number(&first, "request"), Ok(json!(1)))
            .unwrap();
        assert_eq!(call_result(&mut backend)["value"], 1);
        let close = resource_call(&mut backend, "objectClose");
        assert_eq!(close["restoring"], true);
        backend
            .reply(number(&close, "request"), Err("retry native close".into()))
            .unwrap();
        assert_eq!(call_result(&mut backend)["success"], false);
        assert_eq!(module.info()["resources"]["objects"], 1);
        backend.object_close(session, object).unwrap();
        let close = resource_call(&mut backend, "objectClose");
        backend
            .reply(number(&close, "request"), Ok(Value::Null))
            .unwrap();
        assert_eq!(call_result(&mut backend)["success"], true);
        cleanup_reverse(&mut backend, &module, session);
    }
    #[test]
    fn native_object_destructor_failure_cannot_report_release_or_cleanup_success() {
        let (mut backend, module, session) = reverse_backend();
        let object = number(
            &backend
                .call(
                    session,
                    "native",
                    "object",
                    json!(["panic-drop"]),
                    false,
                    false,
                )
                .unwrap(),
            "object",
        );
        backend.object_close(session, object).unwrap();
        let close = resource_call(&mut backend, "objectClose");
        backend
            .reply(number(&close, "request"), Ok(Value::Null))
            .unwrap();
        let result = call_result(&mut backend);
        assert_eq!(result["success"], false);
        assert_eq!(module.info()["resources"]["objects"], 1);
        assert!(backend.cleanup(session).is_err());
        backend.object_close(session, object).unwrap();
        assert_eq!(call_result(&mut backend)["success"], false);
        drop(backend);
        let resources = module.info()["resources"].clone();
        assert_eq!(resources["objects"], 0);
        assert_eq!(resources["retainedObjects"], 1);
        assert_eq!(resources["retainedInstances"], 1);
    }
}
