//! Versioned native plugin boundary. Rust values and futures stay in their
//! creating library; only borrowed bytes, integer handles and C callbacks cross.
//!
//! Native plugins are trusted code. The protocol contains lifecycle mistakes,
//! not memory corruption, process aborts or arbitrary side effects. See the
//! crate README for the FFI safety and authoring contracts.

use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::c_void;
use std::future::Future;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::pin::Pin;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, OnceLock};
use std::task::{Context, Poll, Wake, Waker};

pub const ABI_MAGIC: [u8; 8] = *b"CRDSPLG1";
pub const ABI_VERSION: u32 = 1;
pub const MAX_MESSAGE_BYTES: usize = 1024 * 1024;
/// Maximum nested array/object containers in a service or job result. Leaves
/// room for the ABI envelope under the host JSON parser's recursion limit.
pub const MAX_VALUE_DEPTH: usize = 64;
pub const STATUS_OK: u32 = 0;
pub const STATUS_INVALID_BUFFER: u32 = 1;
pub type PluginResult<T> = Result<T, String>;
pub type PluginFuture = Pin<Box<dyn Future<Output = PluginResult<Value>> + Send + 'static>>;

/// Host-owned wake trampoline. `wake` must remain callable for the process
/// lifetime and safely ignore expired tokens. It must never unwind.
#[repr(C)]
#[derive(Clone, Copy)]
pub struct WakeV1 {
    pub token: u64,
    pub wake: extern "C" fn(u64),
}
/// Synchronous output callback. Bytes belong to the plugin and are valid only
/// during this callback. The host must copy them before returning, without
/// unwinding. `context` is passed through unchanged and never dereferenced here.
pub type OutputV1 = unsafe extern "C" fn(*mut c_void, *const u8, usize);
pub type InvokeV1 = unsafe extern "C" fn(*const u8, usize, OutputV1, *mut c_void, WakeV1) -> u32;

/// Header and function table returned by `cordis_plugin_v1`.
///
/// The host validates magic, version and exact structure size before reading
/// `invoke`. Both sides must use the same native architecture and C ABI.
#[repr(C)]
pub struct PluginApiV1 {
    pub magic: [u8; 8],
    pub abi_version: u32,
    pub struct_size: u32,
    pub invoke: InvokeV1,
}

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum MethodKind {
    Sync,
    Async,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MethodDescriptor {
    pub name: String,
    pub kind: MethodKind,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ServiceDescriptor {
    pub name: String,
    pub methods: Vec<MethodDescriptor>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct FactoryDescriptor {
    pub name: String,
    /// Reserved for a later reverse-call ABI; must be empty in version 1.
    pub inject: Vec<String>,
    pub services: Vec<ServiceDescriptor>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ModuleDescriptor {
    pub module_id: String,
    pub version: String,
    pub factories: Vec<FactoryDescriptor>,
}

/// Creation must be free of externally visible effects. Acquire resources in
/// `setup`, and retain enough state to clean up partial or cancelled setup.
pub trait PluginFactory: Send + Sync + 'static {
    fn descriptor(&self) -> FactoryDescriptor;
    fn create(&self, config: Value) -> PluginResult<Arc<dyn PluginInstance>>;
}
/// Every resource and background task must be joined by `cleanup`. Returning
/// success asserts that this happened; the SDK cannot prove arbitrary I/O.
///
/// Futures own their state and must not borrow this object. Cancellation is
/// cooperative; the host continues polling until the actual future lands.
pub trait PluginInstance: Send + Sync + 'static {
    fn setup(&self, ctx: PluginContext) -> PluginFuture;
    fn cleanup(&self, _ctx: PluginContext) -> PluginFuture {
        Box::pin(async { Ok(Value::Null) })
    }
    fn call_sync(&self, _service: &str, _method: &str, _args: Value) -> PluginResult<Value> {
        Err("UnknownSyncMethod".into())
    }
    fn call_async(
        &self,
        _ctx: PluginContext,
        _service: &str,
        _method: &str,
        _args: Value,
    ) -> PluginFuture {
        Box::pin(async { Err("UnknownAsyncMethod".into()) })
    }
}

#[derive(Default)]
struct CancellationState {
    cancelled: AtomicBool,
    waiters: Mutex<Vec<Waker>>,
}
#[derive(Clone, Default)]
pub struct CancellationToken(Arc<CancellationState>);
impl CancellationToken {
    pub fn is_cancelled(&self) -> bool {
        self.0.cancelled.load(Ordering::Acquire)
    }
    pub fn check(&self) -> PluginResult<()> {
        if self.is_cancelled() {
            Err("Cancelled".into())
        } else {
            Ok(())
        }
    }
    pub async fn cancelled(&self) {
        std::future::poll_fn(|cx| {
            let mut waiters = self.0.waiters.lock().unwrap();
            if self.is_cancelled() {
                Poll::Ready(())
            } else {
                if !waiters.iter().any(|waiter| waiter.will_wake(cx.waker())) {
                    waiters.push(cx.waker().clone());
                }
                Poll::Pending
            }
        })
        .await;
    }
    fn cancel(&self) {
        self.0.cancelled.store(true, Ordering::Release);
        let waiters = std::mem::take(&mut *self.0.waiters.lock().unwrap());
        for waiter in waiters {
            waiter.wake();
        }
    }
}
#[derive(Clone, Default)]
pub struct PluginContext {
    pub cancellation: CancellationToken,
}
impl PluginContext {
    pub fn is_cancelled(&self) -> bool {
        self.cancellation.is_cancelled()
    }
    pub async fn cancelled(&self) {
        self.cancellation.cancelled().await;
    }
}

/// A module exports one or more factories through one retained library image.
pub struct Module {
    id: String,
    version: String,
    factories: Vec<Arc<dyn PluginFactory>>,
}
impl Module {
    pub fn new(id: impl Into<String>, version: impl Into<String>) -> Self {
        Self {
            id: id.into(),
            version: version.into(),
            factories: Vec::new(),
        }
    }
    pub fn factory(mut self, factory: impl PluginFactory) -> Self {
        self.factories.push(Arc::new(factory));
        self
    }
}

#[derive(Deserialize)]
#[serde(tag = "op", rename_all = "snake_case", deny_unknown_fields)]
enum Request {
    Describe {},
    Create {
        factory: String,
        config: Value,
    },
    Setup {
        instance: u64,
    },
    Cleanup {
        instance: u64,
    },
    CallSync {
        instance: u64,
        service: String,
        method: String,
        args: Value,
    },
    CallAsync {
        instance: u64,
        service: String,
        method: String,
        args: Value,
    },
    Poll {
        job: u64,
    },
    Cancel {
        job: u64,
    },
    DropJob {
        job: u64,
    },
    Destroy {
        instance: u64,
    },
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Phase {
    Created,
    Setup,
    Active,
    SetupFailed,
    Cleanup,
    CleanupFailed,
    Cleaned,
    Destroyed,
    Faulted,
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum JobKind {
    Setup,
    Call,
    Cleanup,
}
struct InstanceState {
    phase: Phase,
    jobs: BTreeSet<u64>,
}
struct InstanceEntry {
    value: Mutex<Option<Arc<dyn PluginInstance>>>,
    descriptor: FactoryDescriptor,
    state: Mutex<InstanceState>,
    gate: Mutex<()>,
}
struct JobState {
    future: Option<PluginFuture>,
    landed: bool,
    faulted: bool,
}
struct JobEntry {
    owner: Arc<InstanceEntry>,
    kind: JobKind,
    cancellation: CancellationToken,
    wake: Arc<HostWake>,
    state: Mutex<JobState>,
}
struct Records {
    next: u64,
    instances: BTreeMap<u64, Arc<InstanceEntry>>,
    jobs: BTreeMap<u64, Arc<JobEntry>>,
}
/// Public only for the export macro. Hosts use the C table, not this Rust type.
#[doc(hidden)]
pub struct Runtime {
    descriptor: ModuleDescriptor,
    factories: BTreeMap<String, Arc<dyn PluginFactory>>,
    records: Mutex<Records>,
}
impl Runtime {
    fn new(module: Module) -> PluginResult<Self> {
        if module.id.is_empty() || module.version.is_empty() {
            return Err("EmptyModuleIdentity".into());
        }
        let mut factories = BTreeMap::new();
        let mut descriptors = Vec::new();
        for factory in module.factories {
            let descriptor = factory.descriptor();
            if descriptor.name.is_empty() || factories.contains_key(&descriptor.name) {
                return Err("DuplicateOrEmptyFactory".into());
            }
            if !descriptor.inject.is_empty() {
                return Err("UnsupportedNativeInjection".into());
            }
            let mut services = BTreeSet::new();
            for service in &descriptor.services {
                if service.name.is_empty() || !services.insert(service.name.clone()) {
                    return Err("DuplicateOrEmptyService".into());
                }
                let mut methods = BTreeSet::new();
                for method in &service.methods {
                    if method.name.is_empty() || !methods.insert(method.name.clone()) {
                        return Err("DuplicateOrEmptyMethod".into());
                    }
                }
            }
            factories.insert(descriptor.name.clone(), factory);
            descriptors.push(descriptor);
        }
        let descriptor = ModuleDescriptor {
            module_id: module.id,
            version: module.version,
            factories: descriptors,
        };
        if serde_json::to_vec(&descriptor)
            .map_err(|_| "InvalidDescriptor")?
            .len()
            > MAX_MESSAGE_BYTES / 2
        {
            return Err("DescriptorTooLarge".into());
        }
        Ok(Self {
            descriptor,
            factories,
            records: Mutex::new(Records {
                next: 1,
                instances: BTreeMap::new(),
                jobs: BTreeMap::new(),
            }),
        })
    }
    fn allocate(&self) -> PluginResult<u64> {
        let mut records = self.records.lock().unwrap();
        let id = records.next;
        records.next = id.checked_add(1).ok_or("HandleSpaceExhausted")?;
        Ok(id)
    }
    fn instance(&self, id: u64) -> PluginResult<Arc<InstanceEntry>> {
        self.records
            .lock()
            .unwrap()
            .instances
            .get(&id)
            .cloned()
            .ok_or_else(|| "UnknownInstance".into())
    }
    fn job(&self, id: u64) -> PluginResult<Arc<JobEntry>> {
        self.records
            .lock()
            .unwrap()
            .jobs
            .get(&id)
            .cloned()
            .ok_or_else(|| "UnknownJob".into())
    }
    fn handle(&self, request: Request, wake: WakeV1) -> PluginResult<Value> {
        match request {
            Request::Describe {} => {
                serde_json::to_value(&self.descriptor).map_err(|_| "InvalidDescriptor".into())
            }
            Request::Create { factory, config } => {
                let factory_impl = self.factories.get(&factory).ok_or("UnknownFactory")?;
                let id = self.allocate()?;
                let value = catch_user(|| factory_impl.create(config))??;
                let descriptor = self
                    .descriptor
                    .factories
                    .iter()
                    .find(|entry| entry.name == factory)
                    .unwrap()
                    .clone();
                let entry = Arc::new(InstanceEntry {
                    value: Mutex::new(Some(value)),
                    descriptor,
                    state: Mutex::new(InstanceState {
                        phase: Phase::Created,
                        jobs: BTreeSet::new(),
                    }),
                    gate: Mutex::new(()),
                });
                self.records.lock().unwrap().instances.insert(id, entry);
                Ok(json!({ "instance": id }))
            }
            Request::Setup { instance } => self.begin(instance, JobKind::Setup, None),
            Request::Cleanup { instance } => self.begin(instance, JobKind::Cleanup, None),
            Request::CallAsync {
                instance,
                service,
                method,
                args,
            } => self.begin(instance, JobKind::Call, Some((service, method, args))),
            Request::CallSync {
                instance,
                service,
                method,
                args,
            } => {
                let entry = self.instance(instance)?;
                let _gate = entry.gate.try_lock().map_err(|_| "InstanceBusy")?;
                if entry.state.lock().unwrap().phase != Phase::Active {
                    return Err("InstanceNotActive".into());
                }
                check_method(&entry.descriptor, &service, &method, MethodKind::Sync)?;
                let value = entry.value.lock().unwrap().as_ref().unwrap().clone();
                match catch_user(|| value.call_sync(&service, &method, args)) {
                    Ok(result) => bounded_result(result).map(|value| json!({ "value": value })),
                    Err(error) => {
                        entry.state.lock().unwrap().phase = Phase::Faulted;
                        Err(error)
                    }
                }
            }
            Request::Poll { job } => self.poll(job, wake),
            Request::Cancel { job } => {
                let entry = self.job(job)?;
                // Waking executes external code; never hold SDK locks here.
                entry.cancellation.cancel();
                Ok(Value::Null)
            }
            Request::DropJob { job } => {
                let entry = self.job(job)?;
                let state = entry.state.try_lock().map_err(|_| "JobBusy")?;
                if state.faulted {
                    return Err("JobFaulted".into());
                }
                if !state.landed {
                    return Err("JobStillPending".into());
                }
                if self.records.lock().unwrap().jobs.remove(&job).is_none() {
                    return Err("UnknownJob".into());
                }
                entry.owner.state.lock().unwrap().jobs.remove(&job);
                Ok(Value::Null)
            }
            Request::Destroy { instance } => {
                let entry = self.instance(instance)?;
                let _gate = entry.gate.try_lock().map_err(|_| "InstanceBusy")?;
                {
                    let mut state = entry.state.lock().unwrap();
                    if !state.jobs.is_empty() {
                        return Err("InstanceHasJobs".into());
                    }
                    if !matches!(state.phase, Phase::Created | Phase::Cleaned) {
                        return Err("InstanceNotCleaned".into());
                    }
                    state.phase = Phase::Destroyed;
                }
                let value = entry.value.lock().unwrap().take();
                if let Err(error) = catch_user(|| drop(value)) {
                    entry.state.lock().unwrap().phase = Phase::Faulted;
                    return Err(error);
                }
                self.records.lock().unwrap().instances.remove(&instance);
                Ok(Value::Null)
            }
        }
    }
    fn begin(
        &self,
        instance: u64,
        kind: JobKind,
        call: Option<(String, String, Value)>,
    ) -> PluginResult<Value> {
        let entry = self.instance(instance)?;
        let _gate = entry.gate.try_lock().map_err(|_| "InstanceBusy")?;
        let id = self.allocate()?;
        {
            let mut state = entry.state.lock().unwrap();
            match kind {
                JobKind::Setup if state.phase == Phase::Created => state.phase = Phase::Setup,
                JobKind::Call if state.phase == Phase::Active => {
                    let (service, method, _) = call.as_ref().unwrap();
                    check_method(&entry.descriptor, service, method, MethodKind::Async)?;
                }
                JobKind::Cleanup
                    if matches!(
                        state.phase,
                        Phase::Active | Phase::SetupFailed | Phase::CleanupFailed
                    ) && state.jobs.is_empty() =>
                {
                    state.phase = Phase::Cleanup
                }
                _ => return Err("InvalidLifecycleState".into()),
            }
            state.jobs.insert(id);
        }
        let cancellation = CancellationToken::default();
        let context = PluginContext {
            cancellation: cancellation.clone(),
        };
        let value = entry.value.lock().unwrap().as_ref().unwrap().clone();
        let future = catch_user(|| match kind {
            JobKind::Setup => value.setup(context),
            JobKind::Cleanup => value.cleanup(context),
            JobKind::Call => {
                let (service, method, args) = call.unwrap();
                value.call_async(context, &service, &method, args)
            }
        });
        let future = match future {
            Ok(future) => future,
            Err(error) => {
                // Keep the reservation and fault: construction may have had
                // side effects and cannot be represented as successful cleanup.
                entry.state.lock().unwrap().phase = Phase::Faulted;
                return Err(error);
            }
        };
        self.records.lock().unwrap().jobs.insert(
            id,
            Arc::new(JobEntry {
                owner: entry.clone(),
                kind,
                cancellation,
                wake: Arc::new(HostWake(Mutex::new(None))),
                state: Mutex::new(JobState {
                    future: Some(future),
                    landed: false,
                    faulted: false,
                }),
            }),
        );
        Ok(json!({ "job": id }))
    }
    fn poll(&self, job: u64, wake: WakeV1) -> PluginResult<Value> {
        let entry = self.job(job)?;
        let mut state = entry.state.try_lock().map_err(|_| "JobBusy")?;
        if state.faulted {
            return Err("JobFaulted".into());
        }
        if state.landed {
            return Err("JobResultConsumed".into());
        }
        *entry.wake.0.lock().unwrap() = Some(wake);
        let waker = Waker::from(entry.wake.clone());
        let mut context = Context::from_waker(&waker);
        let result = catch_user(|| state.future.as_mut().unwrap().as_mut().poll(&mut context));
        match result {
            Ok(Poll::Pending) => Ok(json!({ "state": "pending" })),
            Ok(Poll::Ready(result)) => {
                let future = state.future.take();
                if let Err(error) = catch_user(|| drop(future)) {
                    state.faulted = true;
                    entry.owner.state.lock().unwrap().phase = Phase::Faulted;
                    return Err(error);
                }
                let result = bounded_result(result);
                state.landed = true;
                let mut owner = entry.owner.state.lock().unwrap();
                if owner.phase != Phase::Faulted {
                    match entry.kind {
                        JobKind::Setup => {
                            owner.phase = if result.is_ok() {
                                Phase::Active
                            } else {
                                Phase::SetupFailed
                            }
                        }
                        JobKind::Cleanup => {
                            owner.phase = if result.is_ok() {
                                Phase::Cleaned
                            } else {
                                Phase::CleanupFailed
                            }
                        }
                        JobKind::Call => {}
                    }
                }
                Ok(json!({ "state": "ready", "result": response(result) }))
            }
            Err(error) => {
                state.faulted = true;
                entry.owner.state.lock().unwrap().phase = Phase::Faulted;
                Err(error)
            }
        }
    }
}
fn check_method(
    descriptor: &FactoryDescriptor,
    service: &str,
    method: &str,
    kind: MethodKind,
) -> PluginResult<()> {
    if descriptor.services.iter().any(|entry| {
        entry.name == service
            && entry
                .methods
                .iter()
                .any(|entry| entry.name == method && entry.kind == kind)
    }) {
        Ok(())
    } else {
        Err("UnknownOrMismatchedMethod".into())
    }
}
struct HostWake(Mutex<Option<WakeV1>>);
impl HostWake {
    fn notify(&self) {
        let wake = *self.0.lock().unwrap();
        if let Some(wake) = wake {
            (wake.wake)(wake.token);
        }
    }
}
impl Wake for HostWake {
    fn wake(self: Arc<Self>) {
        self.notify();
    }
    fn wake_by_ref(self: &Arc<Self>) {
        self.notify();
    }
}
fn catch_user<T>(action: impl FnOnce() -> T) -> PluginResult<T> {
    catch_unwind(AssertUnwindSafe(action)).map_err(|payload| {
        // A user-defined panic payload can panic again on Drop. Retaining the
        // payload makes containment reliable for unwind panics, at bounded
        // per-fault leakage. Abort and foreign exceptions are not catchable.
        std::mem::forget(payload);
        "PluginPanic".into()
    })
}
fn has_valid_depth(value: &Value) -> bool {
    let mut pending = vec![(value, 0)];
    while let Some((value, depth)) = pending.pop() {
        match value {
            Value::Array(items) => {
                if depth == MAX_VALUE_DEPTH {
                    return false;
                }
                pending.extend(items.iter().map(|item| (item, depth + 1)));
            }
            Value::Object(items) => {
                if depth == MAX_VALUE_DEPTH {
                    return false;
                }
                pending.extend(items.values().map(|item| (item, depth + 1)));
            }
            _ => {}
        }
    }
    true
}
fn discard_deep_value(value: Value) {
    // Dropping an arbitrarily deep rejected serde Value recursively can itself
    // overflow the stack. Dismantle its containers with an explicit worklist.
    let mut pending = vec![value];
    while let Some(value) = pending.pop() {
        match value {
            Value::Array(items) => pending.extend(items),
            Value::Object(items) => pending.extend(items.into_values()),
            _ => {}
        }
    }
}
fn bounded_result(result: PluginResult<Value>) -> PluginResult<Value> {
    match result {
        Ok(value) if !has_valid_depth(&value) => {
            discard_deep_value(value);
            Err("ValueTooDeep".into())
        }
        Ok(value)
            if serde_json::to_vec(&value)
                .map_or(true, |bytes| bytes.len() > MAX_MESSAGE_BYTES / 2) =>
        {
            Err("ResultTooLarge".into())
        }
        Err(error) if error.len() > 4096 => Err("PluginErrorTooLarge".into()),
        result => result,
    }
}
fn response(result: PluginResult<Value>) -> Value {
    match result {
        Ok(value) => json!({"ok": value}),
        Err(error) => json!({"error": error}),
    }
}

/// Implementation detail used by [`export_plugin!`].
///
/// # Safety
/// `request` must address `length` initialized bytes for this call, or may be
/// null only when length is zero. `output` and the wake trampoline must obey
/// their type's documented lifetime and no-unwind contract. `context` must be
/// valid for the callback according to the host's own convention. Calls may be
/// concurrent; reentrant operations on the same instance/job return Busy.
#[doc(hidden)]
pub unsafe fn invoke_export(
    runtime: &OnceLock<PluginResult<Runtime>>,
    module: impl FnOnce() -> Module,
    request: *const u8,
    length: usize,
    output: OutputV1,
    context: *mut c_void,
    wake: WakeV1,
) -> u32 {
    if length > MAX_MESSAGE_BYTES || (request.is_null() && length != 0) {
        return STATUS_INVALID_BUFFER;
    }
    // SAFETY: guaranteed by the host contract above; empty slices need no pointer.
    let bytes = if length == 0 {
        &[]
    } else {
        unsafe { std::slice::from_raw_parts(request, length) }
    };
    let result = catch_user(|| {
        let runtime =
            runtime.get_or_init(|| catch_user(|| Runtime::new(module())).and_then(|result| result));
        match runtime {
            Err(error) => Err(error.clone()),
            Ok(runtime) => match serde_json::from_slice(bytes) {
                Ok(request) => runtime.handle(request, wake),
                Err(_) => Err("InvalidRequest".into()),
            },
        }
    })
    .and_then(|result| result);
    // User values were already bounded before a ready job was committed, and
    // descriptors at module construction. Those 512 KiB limits leave room for
    // every protocol envelope below the 1 MiB wire limit. Do not reapply the
    // user-value limit to an envelope: losing its Ready would strand a consumed
    // completion. Factory/initialization errors still need their string cap.
    let result = match result {
        Err(error) if error.len() > 4096 => Err("PluginErrorTooLarge".into()),
        result => result,
    };
    let encoded = serde_json::to_vec(&response(result))
        .unwrap_or_else(|_| b"{\"error\":\"EncodingFailure\"}".to_vec());
    // SAFETY: callback and context are host-owned, called exactly once and only
    // while the encoded bytes are alive. Host callbacks must not unwind.
    unsafe { output(context, encoded.as_ptr(), encoded.len()) };
    STATUS_OK
}

/// Export a module constructor as the version 1 native ABI entrypoint.
///
/// The constructor is lazy, called once, and must return [`Module`]. Library
/// images containing these exports must remain loaded for the process lifetime.
#[macro_export]
macro_rules! export_plugin {
    ($module:path) => {
        static CORDIS_PLUGIN_RUNTIME: ::std::sync::OnceLock<$crate::PluginResult<$crate::Runtime>> =
            ::std::sync::OnceLock::new();
        unsafe extern "C" fn cordis_plugin_invoke(
            request: *const u8,
            length: usize,
            output: $crate::OutputV1,
            context: *mut ::std::ffi::c_void,
            wake: $crate::WakeV1,
        ) -> u32 {
            // SAFETY: the loader is required to uphold the version 1 ABI contract.
            unsafe {
                $crate::invoke_export(
                    &CORDIS_PLUGIN_RUNTIME,
                    $module,
                    request,
                    length,
                    output,
                    context,
                    wake,
                )
            }
        }
        static CORDIS_PLUGIN_API: $crate::PluginApiV1 = $crate::PluginApiV1 {
            magic: $crate::ABI_MAGIC,
            abi_version: $crate::ABI_VERSION,
            struct_size: ::std::mem::size_of::<$crate::PluginApiV1>() as u32,
            invoke: cordis_plugin_invoke,
        };
        #[unsafe(no_mangle)]
        pub extern "C" fn cordis_plugin_v1() -> *const $crate::PluginApiV1 {
            &CORDIS_PLUGIN_API
        }
    };
}

#[cfg(test)]
mod tests;
