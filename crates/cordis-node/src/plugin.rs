//! Extensible Rust factories for the same graph driven by [`crate::NativeDriver`].
//!
//! Services have named, explicit JSON DTO methods. This module never attempts to
//! serialize an arbitrary Rust value or JavaScript object. Futures are polled
//! outside the Driver borrow; calls into JavaScript are returned as requests.
// The backend-only test target imports this module without the NAPI router;
// actual dynamic library execution is covered by the native integration suite.
#[cfg_attr(test, allow(dead_code))]
#[path = "dynamic.rs"]
pub(crate) mod dynamic;
#[path = "typed.rs"]
mod typed;
pub(crate) use typed::ResolvedImport;
pub use typed::{TypedFactory, TypedService};
#[path = "objects.rs"]
mod objects;
use objects::{ForeignObject, ObjectAction, RustObject};
pub use objects::{JsCallback, JsObject, ObjectDescriptor, ObjectOwnership, PluginObject};
#[path = "streams.rs"]
mod streams;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::{BTreeMap, VecDeque};
use std::future::Future;
use std::pin::Pin;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll, Wake, Waker};
use streams::{ForeignStream, Landing, RustStream, StreamAction};
pub use streams::{JsStream, PluginStream, StreamFuture};

pub type PluginResult<T> = Result<T, String>;
pub type PluginFuture = Pin<Box<dyn Future<Output = PluginResult<Value>> + Send + 'static>>;
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MethodKind {
    Sync,
    Async,
    Stream,
    Object,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MethodDescriptor {
    pub name: String,
    pub kind: MethodKind,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ServiceDescriptor {
    pub name: String,
    pub methods: Vec<MethodDescriptor>,
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FactoryDescriptor {
    pub name: String,
    pub inject: Vec<String>,
    pub services: Vec<ServiceDescriptor>,
}

/// A factory uses the resident Rust interface. Dynamic plugins adapt their
/// versioned C ABI into this trait; no Rust ABI or vtable crosses a library.
/// Each activation creates a fresh instance.
pub trait PluginFactory: Send + Sync + 'static {
    fn descriptor(&self) -> FactoryDescriptor;
    fn create(&self, config: Value) -> PluginResult<Arc<dyn PluginInstance>>;
}
/// Plugins keep typed implementation state. JSON DTO conversion occurs only at
/// the deliberately declared service interface. Sync methods must be bounded
/// and must not block waiting for JavaScript or another lifecycle operation.
pub trait PluginInstance: Send + Sync + 'static {
    fn setup(&self, ctx: PluginContext) -> PluginFuture;
    fn cleanup(&self, _ctx: PluginContext) -> PluginFuture {
        Box::pin(async { Ok(Value::Null) })
    }
    fn call_sync(&self, _service: &str, _method: &str, _args: Value) -> PluginResult<Value> {
        Err("UnknownSyncMethod".into())
    }
    fn open_stream(
        &self,
        _service: &str,
        _method: &str,
        _args: Value,
    ) -> PluginResult<Arc<dyn PluginStream>> {
        Err("UnknownStreamMethod".into())
    }
    fn open_object(
        &self,
        _service: &str,
        _method: &str,
        _args: Value,
    ) -> PluginResult<Arc<dyn PluginObject>> {
        Err("UnknownObjectMethod".into())
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
#[derive(Clone)]
enum RegisteredFactory {
    Native(Arc<dyn PluginFactory>),
    Typed(Arc<TypedFactory>),
}
#[derive(Default)]
pub struct FactoryRegistry {
    factories: BTreeMap<String, (FactoryDescriptor, RegisteredFactory)>,
}
impl FactoryRegistry {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn register(&mut self, factory: impl PluginFactory) -> PluginResult<()> {
        let descriptor = factory.descriptor();
        self.insert(descriptor, RegisteredFactory::Native(Arc::new(factory)))
    }
    pub fn register_typed(&mut self, factory: TypedFactory) -> PluginResult<()> {
        let descriptor = factory.descriptor()?;
        self.insert(descriptor, RegisteredFactory::Typed(Arc::new(factory)))
    }
    fn insert(
        &mut self,
        descriptor: FactoryDescriptor,
        factory: RegisteredFactory,
    ) -> PluginResult<()> {
        let mut names = std::collections::BTreeSet::new();
        if descriptor.name.is_empty() || self.factories.contains_key(&descriptor.name) {
            return Err("DuplicateOrEmptyFactory".into());
        }
        for name in &descriptor.inject {
            if name.is_empty() || !names.insert(name) {
                return Err("DuplicateOrEmptyInjection".into());
            }
        }
        names.clear();
        for service in &descriptor.services {
            if service.name.is_empty() || !names.insert(&service.name) {
                return Err("DuplicateOrEmptyService".into());
            }
            let mut methods = std::collections::BTreeSet::new();
            for method in &service.methods {
                if method.name.is_empty() || !methods.insert(&method.name) {
                    return Err("DuplicateOrEmptyMethod".into());
                }
            }
        }
        self.factories
            .insert(descriptor.name.clone(), (descriptor, factory));
        Ok(())
    }
}
#[derive(Default)]
struct CancellationState {
    cancelled: AtomicBool,
    waiters: Mutex<Vec<Waker>>,
}
/// Cooperative cancellation does not claim a future or external RPC has landed.
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
        std::future::poll_fn(|ctx| {
            let mut waiters = self.0.waiters.lock().unwrap();
            if self.is_cancelled() {
                return Poll::Ready(());
            }
            if !waiters.iter().any(|w| w.will_wake(ctx.waker())) {
                waiters.push(ctx.waker().clone());
            }
            Poll::Pending
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
struct ReplyState {
    result: Option<PluginResult<Value>>,
    waker: Option<Waker>,
}
struct RequestFuture {
    state: Arc<Mutex<ReplyState>>,
}
impl Future for RequestFuture {
    type Output = PluginResult<Value>;
    fn poll(self: Pin<&mut Self>, ctx: &mut Context<'_>) -> Poll<Self::Output> {
        let mut state = self.state.lock().unwrap();
        if let Some(result) = state.result.take() {
            Poll::Ready(result)
        } else {
            state.waker = Some(ctx.waker().clone());
            Poll::Pending
        }
    }
}
#[derive(Serialize)]
pub(crate) struct HostRequest {
    pub request: String,
    pub session: String,
    pub job: String,
    pub kind: &'static str,
    pub service: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub method: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub args: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stream: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub object: Option<String>,
    pub restoring: bool,
}
struct PendingRequest {
    job: u64,
    session: u64,
    kind: &'static str,
    service: String,
    stream: Option<String>,
    object: Option<String>,
    restoring: bool,
    state: Arc<Mutex<ReplyState>>,
}
enum ResourceReference {
    Stream(String),
    Object(String),
}
#[derive(Default)]
struct Transport {
    next: u64,
    requests: VecDeque<HostRequest>,
    pending: BTreeMap<u64, PendingRequest>,
    foreign_streams: BTreeMap<String, ForeignStream>,
    foreign_objects: BTreeMap<String, ForeignObject>,
    object_order: u64,
    waiters: Vec<Waker>,
}
/// A capability limited to one managed action. Escaped clones cannot admit work
/// after the action completes. Cleanup can read its committed JS services.
#[derive(Clone)]
pub struct PluginContext {
    session: u64,
    job: u64,
    descriptor: FactoryDescriptor,
    transport: Arc<Mutex<Transport>>,
    cancellation: CancellationToken,
    alive: Arc<AtomicBool>,
    cleanup: bool,
    notify: Arc<dyn Fn() + Send + Sync>,
    join_blocked: Arc<Mutex<std::collections::BTreeSet<usize>>>,
    setup: bool,
}
impl PluginContext {
    pub fn cancellation(&self) -> CancellationToken {
        self.cancellation.clone()
    }
    pub async fn provide(&self, service: &str) -> PluginResult<Value> {
        self.provide_with_check(service, false).await
    }
    async fn provide_with_check(&self, service: &str, checked: bool) -> PluginResult<Value> {
        if self.cleanup {
            return Err("CleanupCannotPublish".into());
        }
        self.cancellation.check()?;
        if !self.descriptor.services.iter().any(|s| s.name == service) {
            return Err("UndeclaredService".into());
        }
        self.request(
            "provide",
            service,
            None,
            Some(serde_json::json!({"checked": checked})),
        )?
        .await
    }
    pub async fn call(&self, service: &str, method: &str, args: Value) -> PluginResult<Value> {
        if !self.cleanup {
            self.cancellation.check()?;
        }
        if !self.descriptor.inject.iter().any(|s| s == service) {
            return Err("UndeclaredInjection".into());
        }
        self.request("call", service, Some(method.to_owned()), Some(args))?
            .await
    }
    fn request(
        &self,
        kind: &'static str,
        service: &str,
        method: Option<String>,
        args: Option<Value>,
    ) -> PluginResult<RequestFuture> {
        if !self.alive.load(Ordering::Acquire) {
            return Err("ActionClosed".into());
        }
        let mut transport = self.transport.lock().unwrap();
        // Check again under the queue lock used when closing an action.
        if !self.alive.load(Ordering::Acquire) {
            return Err("ActionClosed".into());
        }
        let reply = self.enqueue(&mut transport, kind, service, method, args, None)?;
        drop(transport);
        (self.notify)();
        Ok(reply)
    }
    fn enqueue(
        &self,
        transport: &mut Transport,
        kind: &'static str,
        service: &str,
        method: Option<String>,
        args: Option<Value>,
        resource: Option<ResourceReference>,
    ) -> PluginResult<RequestFuture> {
        let (stream, object) = match resource {
            Some(ResourceReference::Stream(id)) => (Some(id), None),
            Some(ResourceReference::Object(id)) => (None, Some(id)),
            None => (None, None),
        };
        transport.next = transport.next.checked_add(1).ok_or("RequestCapacity")?;
        let request = transport.next;
        let state = Arc::new(Mutex::new(ReplyState {
            result: None,
            waker: None,
        }));
        transport.pending.insert(
            request,
            PendingRequest {
                job: self.job,
                session: self.session,
                kind,
                service: service.into(),
                stream: stream.clone(),
                object: object.clone(),
                restoring: self.cleanup,
                state: state.clone(),
            },
        );
        transport.requests.push_back(HostRequest {
            request: request.to_string(),
            session: self.session.to_string(),
            job: self.job.to_string(),
            kind,
            service: service.into(),
            method,
            args,
            stream,
            object,
            restoring: self.cleanup,
        });
        Ok(RequestFuture { state })
    }
}

struct JobWake {
    ready: AtomicBool,
    notify: Arc<dyn Fn() + Send + Sync>,
}
impl Wake for JobWake {
    fn wake(self: Arc<Self>) {
        self.wake_by_ref();
    }
    fn wake_by_ref(self: &Arc<Self>) {
        if !self.ready.swap(true, Ordering::AcqRel) {
            (self.notify)();
        }
    }
}
#[derive(Clone, Copy, PartialEq)]
enum JobKind {
    Setup,
    Cleanup,
    Call,
    ResourceClose,
}
struct Job {
    session: u64,
    kind: JobKind,
    wait_source: Option<(usize, u64)>,
    join_blocked: std::collections::BTreeSet<usize>,
    future: PluginFuture,
    wake: Arc<JobWake>,
    alive: Arc<AtomicBool>,
    cancellation: CancellationToken,
    restoring: bool,
    result: Option<PluginResult<Value>>,
    context: PluginContext,
    finalizing: bool,
    main_result: Option<PluginResult<Value>>,
    landing: Arc<Landing>,
    stream: Option<StreamAction>,
    object: Option<ObjectAction>,
}
struct Session {
    pub id: usize,
    pub generation: u64,
    descriptor: FactoryDescriptor,
    instance: Arc<dyn PluginInstance>,
    typed: Option<Arc<typed::Instance>>,
    cancellation: CancellationToken,
    cleanup_done: bool,
    publications: BTreeMap<String, (usize, cordis_driver::ServicePort)>,
    ports: BTreeMap<String, cordis_driver::ServicePort>,
    inherited: Vec<(String, cordis_driver::ServicePort)>,
}
#[derive(Serialize)]
pub(crate) struct CompletedJob {
    pub job: String,
    pub session: String,
    pub success: bool,
    pub value: Value,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<String>,
}
/// The host owns this executor separately from the lifecycle Driver borrow.
pub(crate) struct Backend {
    registry: FactoryRegistry,
    modules: BTreeMap<String, Arc<dynamic::Module>>,
    native_children: Arc<dynamic::children::Children>,
    native_checkpoints: Arc<dynamic::checkpoint::Journal>,
    typed_mounts: BTreeMap<usize, typed::Mount>,
    typed_children: BTreeMap<String, typed::Child>,
    next_typed_child: u64,
    typed_failures: Vec<(u64, String)>,
    typed_realms: BTreeMap<(u64, u64), u64>,
    service_notifications: Arc<AtomicBool>,
    child_notifications: Arc<AtomicBool>,
    sessions: BTreeMap<u64, Session>,
    jobs: BTreeMap<u64, Job>,
    next_session: u64,
    next_job: u64,
    next_stream: u64,
    streams: BTreeMap<u64, RustStream>,
    next_object: u64,
    objects: BTreeMap<u64, RustObject>,
    owned_objects: Vec<std::sync::Weak<dyn PluginObject>>,
    transport: Arc<Mutex<Transport>>,
    notify: Arc<dyn Fn() + Send + Sync>,
}
impl Backend {
    pub fn new(registry: FactoryRegistry, notify: Arc<dyn Fn() + Send + Sync>) -> Self {
        Self {
            registry,
            modules: BTreeMap::new(),
            native_checkpoints: Arc::new(dynamic::checkpoint::Journal::default()),
            native_children: Arc::new(dynamic::children::Children::new(notify.clone())),
            typed_mounts: BTreeMap::new(),
            typed_children: BTreeMap::new(),
            next_typed_child: 0,
            typed_failures: Vec::new(),
            typed_realms: BTreeMap::new(),
            service_notifications: Arc::new(AtomicBool::new(false)),
            child_notifications: Arc::new(AtomicBool::new(false)),
            sessions: BTreeMap::new(),
            jobs: BTreeMap::new(),
            next_session: 0,
            next_job: 0,
            next_stream: 0,
            streams: BTreeMap::new(),
            next_object: 0,
            objects: BTreeMap::new(),
            owned_objects: Vec::new(),
            transport: Arc::new(Mutex::new(Transport::default())),
            notify,
        }
    }
    pub fn info(&self) -> Value {
        let factories = self
            .registry
            .factories
            .values()
            .map(|(descriptor, factory)| {
                let mut value = serde_json::json!(descriptor);
                if let RegisteredFactory::Typed(factory) = factory {
                    value = factory.metadata().expect("validated typed factory");
                    let config = factory.injection_config();
                    if !config.is_empty() {
                        value["injectConfig"] = serde_json::json!(config);
                    }
                }
                value
            })
            .collect::<Vec<_>>();
        serde_json::json!({"abi":1,"factories":factories})
    }
    pub fn owner(&self, session: u64) -> PluginResult<(usize, u64)> {
        let s = self.sessions.get(&session).ok_or("UnknownSession")?;
        Ok((s.id, s.generation))
    }
    pub fn binding(
        &self,
        session: u64,
        service: &str,
    ) -> PluginResult<(usize, cordis_driver::ServicePort)> {
        self.sessions
            .get(&session)
            .ok_or("UnknownSession")?
            .publications
            .get(service)
            .copied()
            .ok_or("ServiceNotPublished".into())
    }
    pub fn busy(&self) -> bool {
        !self.jobs.is_empty()
    }
    pub fn can_close(&self) -> bool {
        self.sessions.is_empty() && self.jobs.is_empty()
    }
    pub fn authority(&self, session: u64, job: u64) -> PluginResult<(usize, u64, bool)> {
        let job = self.jobs.get(&job).ok_or("StaleAuthority")?;
        if job.session != session {
            return Err("InvalidAuthority".into());
        }
        let (owner, generation) = self.owner(session)?;
        Ok((owner, generation, job.restoring))
    }
    pub fn request_authority(
        &self,
        session: u64,
        job: u64,
        request: u64,
    ) -> PluginResult<(usize, u64, bool)> {
        self.authority(session, job)?;
        let transport = self.transport.lock().unwrap();
        let request = transport.pending.get(&request).ok_or("StaleAuthority")?;
        if request.session != session || request.job != job {
            return Err("InvalidAuthority".into());
        }
        let (id, generation) = self.owner(session)?;
        Ok((id, generation, request.restoring))
    }
    pub fn is_resource_method(
        &self,
        session: u64,
        service: &str,
        method: &str,
    ) -> PluginResult<bool> {
        let descriptor = &self
            .sessions
            .get(&session)
            .ok_or("UnknownSession")?
            .descriptor;
        Ok(descriptor
            .services
            .iter()
            .find(|s| s.name == service)
            .and_then(|s| s.methods.iter().find(|m| m.name == method))
            .is_some_and(|m| matches!(m.kind, MethodKind::Stream | MethodKind::Object)))
    }
    fn context(&self, session: u64, job: u64, cleanup: bool) -> PluginResult<PluginContext> {
        let s = self.sessions.get(&session).ok_or("UnknownSession")?;
        Ok(PluginContext {
            session,
            job,
            descriptor: s.descriptor.clone(),
            transport: self.transport.clone(),
            cancellation: CancellationToken::default(),
            alive: Arc::new(AtomicBool::new(true)),
            cleanup,
            setup: false,
            notify: self.notify.clone(),
            join_blocked: Arc::new(Mutex::new(Default::default())),
        })
    }
    fn job_id(&mut self) -> PluginResult<u64> {
        self.next_job = self.next_job.checked_add(1).ok_or("JobCapacity")?;
        Ok(self.next_job)
    }
    fn add_job(&mut self, context: PluginContext, kind: JobKind, future: PluginFuture) {
        self.jobs.insert(
            context.job,
            Job {
                session: context.session,
                kind,
                wait_source: None,
                join_blocked: std::collections::BTreeSet::new(),
                future,
                wake: Arc::new(JobWake {
                    ready: AtomicBool::new(true),
                    notify: self.notify.clone(),
                }),
                alive: context.alive.clone(),
                cancellation: context.cancellation.clone(),
                restoring: context.cleanup,
                result: None,
                context,
                finalizing: false,
                main_result: None,
                landing: Arc::new(Landing::default()),
                stream: None,
                object: None,
            },
        );
    }
    pub fn start(
        &mut self,
        id: usize,
        generation: u64,
        factory: &str,
        config: Value,
    ) -> PluginResult<Value> {
        self.start_resolved(id, generation, factory, config, BTreeMap::new(), vec![])
    }
    pub fn start_resolved(
        &mut self,
        id: usize,
        generation: u64,
        factory: &str,
        config: Value,
        ports: BTreeMap<String, cordis_driver::ServicePort>,
        imports: Vec<ResolvedImport>,
    ) -> PluginResult<Value> {
        if self
            .sessions
            .values()
            .any(|s| s.id == id && s.generation == generation)
        {
            return Err("EpisodeAlreadyStarted".into());
        }
        let (descriptor, factory) = if let Some(mount) = self.typed_mounts.get(&id) {
            if mount.factory != factory {
                return Err("TypedMountDefinitionChanged".into());
            }
            (
                mount.adapter.descriptor()?,
                RegisteredFactory::Typed(mount.adapter.clone()),
            )
        } else {
            let (descriptor, registered) = self
                .registry
                .factories
                .get(factory)
                .ok_or("UnknownFactory")?;
            match registered {
                RegisteredFactory::Typed(factory) if factory.dynamic_children => {
                    let adapter = Arc::new(factory.with_native_anchor(&ports)?);
                    (adapter.descriptor()?, RegisteredFactory::Typed(adapter))
                }
                _ => (descriptor.clone(), registered.clone()),
            }
        };
        // Reserve numeric capacity before running real legacy setup callbacks.
        let session = self.next_session.checked_add(1).ok_or("SessionCapacity")?;
        let job = self.next_job.checked_add(1).ok_or("JobCapacity")?;
        if matches!(factory, RegisteredFactory::Native(_)) && self.typed_mounts.contains_key(&id) {
            return Err("TypedMountDefinitionChanged".into());
        }
        let typed = match &factory {
            RegisteredFactory::Typed(factory) => Some(self.typed_instance(
                id,
                generation,
                factory.clone(),
                config.clone(),
                ports,
                imports,
            )?),
            RegisteredFactory::Native(_) => None,
        };
        let instance: Arc<dyn PluginInstance> = match factory {
            RegisteredFactory::Native(factory) => factory.create(config)?,
            RegisteredFactory::Typed(_) => typed.as_ref().unwrap().clone(),
        };
        self.next_job = job;
        self.next_session = session;
        self.sessions.insert(
            session,
            Session {
                id,
                generation,
                descriptor,
                instance: instance.clone(),
                typed: typed.clone(),
                cancellation: CancellationToken::default(),
                cleanup_done: false,
                publications: BTreeMap::new(),
                ports: BTreeMap::new(),
                inherited: Vec::new(),
            },
        );
        let mut ctx = self.context(session, job, false)?;
        ctx.setup = true;
        let future = instance.setup(ctx.clone());
        self.add_job(ctx, JobKind::Setup, future);
        Ok(
            serde_json::json!({"session":session.to_string(),"job":job.to_string(),"persistent":typed.is_some(),"realms":typed.as_ref().map(|instance| instance.realm_metadata())}),
        )
    }
    pub fn cleanup(&mut self, session: u64) -> PluginResult<Value> {
        if self.jobs.values().any(|j| j.session == session)
            || self.streams.values().any(|s| s.session == session)
            || self.objects.values().any(|o| o.session == session)
        {
            return Err("SessionBusy".into());
        }
        let instance = self.sessions.get(&session).ok_or("UnknownSession")?;
        if instance.cleanup_done {
            return Err("CleanupAlreadyComplete".into());
        }
        let instance = instance.instance.clone();
        let job = self.job_id()?;
        let ctx = self.context(session, job, true)?;
        let cleanup_ctx = ctx.clone();
        let future = Box::pin(async move {
            cleanup_ctx
                .request("close_orphans", "", None, None)?
                .await?;
            cleanup_ctx.drain_js_resources(None, true).await?;
            instance.cleanup(cleanup_ctx).await
        });
        self.add_job(ctx, JobKind::Cleanup, future);
        Ok(serde_json::json!({"job":job.to_string()}))
    }
    pub fn call(
        &mut self,
        session: u64,
        service: &str,
        method: &str,
        args: Value,
        restoring: bool,
        continuing: bool,
    ) -> PluginResult<Value> {
        let s = self.sessions.get(&session).ok_or("UnknownSession")?;
        if s.cleanup_done {
            return Err("ActionClosed".into());
        }
        if !restoring && !continuing {
            s.cancellation.check()?;
        }
        let cancelled = s.cancellation.is_cancelled();
        let kind = s
            .descriptor
            .services
            .iter()
            .find(|s| s.name == service)
            .and_then(|s| s.methods.iter().find(|m| m.name == method))
            .ok_or("UndeclaredMethod")?
            .kind
            .clone();
        let instance = s.instance.clone();
        match kind {
            MethodKind::Sync => {
                let value = instance.call_sync(service, method, args)?;
                let notifications = self.typed_notifications();
                let children = self.typed_child_actions();
                Ok(
                    serde_json::json!({"value": value, "serviceNotifications": notifications,"children":children}),
                )
            }
            MethodKind::Stream => self.open_rust_stream(session, service, method, args),
            MethodKind::Object => self.open_rust_object(session, service, method, args),
            MethodKind::Async => {
                let job = self.job_id()?;
                let ctx = self.context(session, job, restoring)?;
                if cancelled && !restoring {
                    ctx.cancellation.cancel();
                }
                let future = instance.call_async(ctx.clone(), service, method, args);
                self.add_job(ctx, JobKind::Call, future);
                Ok(serde_json::json!({"job":job.to_string()}))
            }
        }
    }
    pub fn cancel(&mut self, session: u64) -> PluginResult<()> {
        if let Some(typed) = self.sessions.get(&session).and_then(|s| s.typed.as_ref()) {
            typed.cancel();
        }
        self.sessions
            .get(&session)
            .ok_or("UnknownSession")?
            .cancellation
            .cancel();
        for job in self
            .jobs
            .values()
            .filter(|j| j.session == session && matches!(j.kind, JobKind::Setup | JobKind::Call))
        {
            job.cancellation.cancel();
            job.wake.wake_by_ref();
        }
        let jobs = self
            .jobs
            .iter()
            .filter(|(_, j)| {
                j.session == session && matches!(j.kind, JobKind::Setup | JobKind::Call)
            })
            .map(|(&id, _)| id)
            .collect::<Vec<_>>();
        for job in jobs {
            self.cancel_foreign_streams(job)?;
        }
        Ok(())
    }
    pub fn cancel_job(&mut self, job: u64) -> PluginResult<()> {
        if job == 0 || job > self.next_job {
            return Err("UnknownJob".into());
        }
        if let Some(job) = self.jobs.get(&job) {
            if job.kind != JobKind::Call {
                return Err("NotCallJob".into());
            }
            job.cancellation.cancel();
            job.wake.wake_by_ref();
        }
        self.cancel_foreign_streams(job)?;
        Ok(())
    }
    pub fn release(&mut self, session: u64) -> PluginResult<()> {
        let s = self.sessions.get(&session).ok_or("UnknownSession")?;
        if !s.cleanup_done
            || self.jobs.values().any(|j| j.session == session)
            || self.streams.values().any(|s| s.session == session)
            || self.objects.values().any(|o| o.session == session)
            || self
                .transport
                .lock()
                .unwrap()
                .foreign_streams
                .values()
                .any(|s| s.session == session)
            || self
                .transport
                .lock()
                .unwrap()
                .foreign_objects
                .values()
                .any(|o| o.session == session)
        {
            return Err("SessionBusy".into());
        }
        self.sessions.remove(&session);
        self.native_children.release_session(session);
        self.native_checkpoints.release_session(session);
        Ok(())
    }
    pub fn reply(&mut self, request: u64, result: PluginResult<Value>) -> PluginResult<()> {
        let pending = self
            .transport
            .lock()
            .unwrap()
            .pending
            .remove(&request)
            .ok_or("StaleRequest")?;
        let result = if pending.kind == "stream_close" {
            result.and_then(|value| {
                if value.get("done").and_then(Value::as_bool) != Some(true) {
                    Err("StreamCloseIncomplete".into())
                } else {
                    Ok(value)
                }
            })
        } else if pending.kind == "object_close" {
            result.and_then(|value| {
                if value.get("closed").and_then(Value::as_bool) == Some(true) {
                    Ok(value)
                } else {
                    Err("ObjectCloseIncomplete".into())
                }
            })
        } else {
            result
        };
        let result = match pending.kind {
            "object_open" => result.and_then(|value| {
                let id = value
                    .get("object")
                    .and_then(Value::as_str)
                    .filter(|s| !s.is_empty())
                    .ok_or("InvalidObjectReply")?;
                let descriptor = ObjectDescriptor::from_value(
                    value
                        .get("descriptor")
                        .cloned()
                        .ok_or("InvalidObjectReply")?,
                )?;
                let mut transport = self.transport.lock().unwrap();
                if transport.foreign_objects.contains_key(id) {
                    return Err("DuplicateObjectIdentity".into());
                }
                transport.object_order = transport
                    .object_order
                    .checked_add(1)
                    .ok_or("ObjectCapacity")?;
                let order = transport.object_order;
                transport.foreign_objects.insert(
                    id.into(),
                    ForeignObject {
                        session: pending.session,
                        job: pending.job,
                        service: pending.service.clone(),
                        descriptor,
                        order,
                        closing: false,
                        close_pending: false,
                        failed: None,
                    },
                );
                Ok(value)
            }),
            "object_close" => {
                let mut transport = self.transport.lock().unwrap();
                if let Some(id) = &pending.object {
                    if result.is_ok() {
                        transport.foreign_objects.remove(id);
                    } else if let Some(object) = transport.foreign_objects.get_mut(id) {
                        object.close_pending = false;
                        object.failed = result.as_ref().err().cloned();
                    }
                }
                result
            }
            "stream_open" => result.and_then(|value| {
                let id = value
                    .get("stream")
                    .and_then(Value::as_str)
                    .filter(|s| !s.is_empty())
                    .ok_or("InvalidStreamReply")?;
                let mut transport = self.transport.lock().unwrap();
                if transport.foreign_streams.contains_key(id) {
                    return Err("DuplicateStreamIdentity".into());
                }
                transport.foreign_streams.insert(
                    id.into(),
                    ForeignStream {
                        session: pending.session,
                        job: pending.job,
                        service: pending.service.clone(),
                        pull: false,
                        closing: false,
                        close_pending: false,
                        failed: None,
                    },
                );
                Ok(value)
            }),
            "stream_next" | "stream_close" => {
                let mut transport = self.transport.lock().unwrap();
                if let Some(id) = &pending.stream {
                    if pending.kind == "stream_close" && result.is_ok() {
                        transport.foreign_streams.remove(id);
                    } else if let Some(stream) = transport.foreign_streams.get_mut(id) {
                        if pending.kind == "stream_next" {
                            stream.pull = false;
                        } else {
                            stream.close_pending = false;
                            stream.failed = result.as_ref().err().cloned();
                        }
                    }
                }
                result
            }
            _ => result,
        };
        let result = if pending.kind == "provide" {
            result.and_then(|value| {
                let publication = value
                    .get("publication")
                    .and_then(Value::as_str)
                    .ok_or("InvalidPublicationReply")?
                    .parse::<usize>()
                    .map_err(|_| "InvalidPublicationReply")?;
                let port = serde_json::from_value::<cordis_driver::ServicePort>(
                    value
                        .get("port")
                        .cloned()
                        .ok_or("InvalidPublicationReply")?,
                )
                .map_err(|_| "InvalidPublicationReply")?;
                let session = self
                    .sessions
                    .get_mut(&pending.session)
                    .ok_or("UnknownSession")?;
                if let Some(typed) = &session.typed {
                    typed.check_publication(&pending.service, port)?;
                }
                session
                    .publications
                    .insert(pending.service, (publication, port));
                Ok(Value::Null)
            })
        } else {
            result
        };
        let waiters = std::mem::take(&mut self.transport.lock().unwrap().waiters);
        for waiter in waiters {
            waiter.wake();
        }
        if pending.kind == "stream_open"
            && self
                .jobs
                .get(&pending.job)
                .is_some_and(|job| job.cancellation.is_cancelled())
        {
            self.cancel_foreign_streams(pending.job)?;
        }
        let wake = {
            let mut state = pending.state.lock().unwrap();
            state.result = Some(result);
            state.waker.take()
        };
        if let Some(wake) = wake {
            wake.wake();
        }
        // A future may have already returned after dropping an RPC future. Its
        // result still cannot land until every dispatched external call lands.
        if let Some(job) = self.jobs.get(&pending.job) {
            job.wake.wake_by_ref();
        }
        Ok(())
    }
    pub fn poll(&mut self) -> Value {
        let mut completed = Vec::new();
        for (&id, job) in &mut self.jobs {
            if job.result.is_none() && job.wake.ready.swap(false, Ordering::AcqRel) {
                let waker = Waker::from(job.wake.clone());
                if let Poll::Ready(result) =
                    cordis::runtime::static_host::with_child_join_guard(&job.join_blocked, || {
                        job.future.as_mut().poll(&mut Context::from_waker(&waker))
                    })
                {
                    let _transport = self.transport.lock().unwrap();
                    job.alive.store(false, Ordering::Release);
                    job.result = Some(result);
                }
            }
            if job.result.is_some() {
                let needs_finalization = {
                    let transport = self.transport.lock().unwrap();
                    transport
                        .foreign_streams
                        .values()
                        .any(|s| s.session == job.session && s.job == id)
                        || transport
                            .foreign_objects
                            .values()
                            .any(|o| o.session == job.session && o.job == id)
                        || transport
                            .pending
                            .values()
                            .any(|r| r.job == id && matches!(r.kind, "stream_open" | "object_open"))
                };
                if !job.finalizing && needs_finalization {
                    job.main_result = job.result.take();
                    let mut ctx = job.context.clone();
                    ctx.cleanup = true;
                    ctx.alive = Arc::new(AtomicBool::new(true));
                    job.alive = ctx.alive.clone();
                    job.context = ctx.clone();
                    job.restoring = true;
                    job.finalizing = true;
                    job.future =
                        Box::pin(async move { ctx.drain_js_resources(Some(id), false).await });
                    job.wake.wake_by_ref();
                    continue;
                }
                if !self
                    .transport
                    .lock()
                    .unwrap()
                    .pending
                    .values()
                    .any(|r| r.job == id)
                {
                    completed.push(id);
                }
            }
        }
        let mut jobs = Vec::new();
        for id in completed {
            let job = self.jobs.remove(&id).unwrap();
            let result = match (job.main_result, job.result.unwrap()) {
                (Some(main), Ok(_)) => main,
                (_, result) => result,
            };
            if let Some(action) = job.stream {
                self.stream_landed(action, result.is_ok());
            }
            if let Some(action) = job.object {
                self.object_landed(action, id, result.is_ok());
            }
            job.landing.finish();
            if job.kind == JobKind::Cleanup && result.is_ok() {
                self.sessions.get_mut(&job.session).unwrap().cleanup_done = true;
            }
            let (success, value, error) = match result {
                Ok(v) => (true, v, None),
                Err(e) => (false, Value::Null, Some(e)),
            };
            jobs.push(CompletedJob {
                job: id.to_string(),
                session: job.session.to_string(),
                success,
                value,
                error,
            });
        }
        let calls = self
            .transport
            .lock()
            .unwrap()
            .requests
            .drain(..)
            .collect::<Vec<_>>();
        let notifications = self.typed_notifications();
        let mut children = self.typed_child_actions();
        children.extend(self.native_child_actions());
        serde_json::json!({"calls":calls,"jobs":jobs,"serviceNotifications":notifications,"children":children})
    }
}
/// User-defined Drop implementations must not unwind across Node's finalizer.
/// Panic payloads are intentionally forgotten: their destructors may also panic.
fn contain_panic(action: impl FnOnce()) {
    if let Err(payload) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(action)) {
        std::mem::forget(payload);
    }
}
fn contain_drop(value: impl Sized) {
    contain_panic(|| drop(value));
}
impl Drop for Backend {
    fn drop(&mut self) {
        // A fault may prevent JavaScript from replying. Close admission under
        // the same lock used to enqueue requests, then unblock every worker
        // outside that lock before dropping instances which may join workers.
        let (pending, waiters) = {
            let mut transport = self
                .transport
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            for job in self.jobs.values() {
                job.alive.store(false, Ordering::Release);
            }
            transport.requests.clear();
            (
                std::mem::take(&mut transport.pending),
                std::mem::take(&mut transport.waiters),
            )
        };
        for waiter in waiters {
            contain_panic(|| waiter.wake());
        }
        for (_, pending) in pending {
            let wake = {
                let mut state = pending
                    .state
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
                state.result = Some(Err("ActionClosed".into()));
                state.waker.take()
            };
            if let Some(wake) = wake {
                contain_panic(|| wake.wake());
            }
        }
        for (_, job) in std::mem::take(&mut self.jobs) {
            contain_panic(|| job.cancellation.cancel());
            contain_drop(job);
        }
        for (_, stream) in std::mem::take(&mut self.streams) {
            contain_drop(stream);
        }
        for (_, object) in std::mem::take(&mut self.objects) {
            contain_drop(object);
        }
        for (_, session) in std::mem::take(&mut self.sessions) {
            contain_drop(session);
        }
        for (_, mount) in std::mem::take(&mut self.typed_mounts) {
            contain_drop(mount);
        }
        for (_, child) in std::mem::take(&mut self.typed_children) {
            contain_drop(child);
        }
        for (_, factory) in std::mem::take(&mut self.registry.factories) {
            contain_drop(factory);
        }
    }
}
