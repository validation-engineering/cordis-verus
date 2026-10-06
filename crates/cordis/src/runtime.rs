//! Typed, cooperatively polled host adapter for the verified lifecycle kernel.
//!
//! The kernel proves lifecycle and committed dependency safety. Futures, user
//! callbacks, shared values and the host scheduler are ordinary Rust, not proofs
//! of arbitrary effects. An in-flight setup stage is always allowed to land so
//! its inverse can be collected; cancellation stops subsequent stages.
pub mod static_host;

use crate::diagnostics::{Blocker, Compaction, PluginSnapshot, RuntimeSnapshot, StorageStats};
use crate::future_support::poll_catching_unwind;
use cordis_driver::shared::{Decision, HostStatus, LifecycleDriver};
use cordis_kernel::episode::StageProtocol;
use cordis_kernel::{Binding, Error as KernelError, Phase, Port};
use std::any::Any;
use std::collections::BTreeMap;
use std::fmt;
use std::future::Future;
use std::marker::PhantomData;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::pin::Pin;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, MutexGuard};
use std::task::{Context as TaskContext, Poll, Waker};

pub type PluginId = usize;
pub type CallbackResult = Result<(), String>;
/// Reserved cooperative-abort result. It is treated as cancellation only after
/// the owner/group is cancelled; an active callback returning it still fails.
pub const CANCELLED: &str = "owner episode cancelled";
type Value = Arc<dyn Any + Send + Sync>;
type ServiceCheck = Arc<dyn Fn(&Value, &Context, &serde_json::Value) -> bool + Send + Sync>;
struct ServiceSlot {
    value: Mutex<Value>,
    check: Option<ServiceCheck>,
}
type SharedSlot = Arc<ServiceSlot>;
type Values = BTreeMap<(PluginId, u64, u64), SharedSlot>;
type ConfigUpdateCallback = Box<
    dyn FnMut(
            AsyncSetup,
            serde_json::Value,
            serde_json::Value,
        ) -> Result<crate::config::ConfigUpdate, String>
        + Send,
>;

impl ServiceSlot {
    fn new(value: Value, check: Option<ServiceCheck>) -> SharedSlot {
        Arc::new(Self {
            value: Mutex::new(value),
            check,
        })
    }
    fn get<T: Any + Send + Sync>(&self) -> Option<Arc<T>> {
        lock(&self.value).clone().downcast::<T>().ok()
    }
    fn accepts(&self, context: &Context, config: &serde_json::Value) -> bool {
        let Some(check) = &self.check else {
            return true;
        };
        let value = lock(&self.value).clone();
        // A user availability predicate never runs under host bookkeeping locks.
        catch_unwind(AssertUnwindSafe(|| check(&value, context, config))).unwrap_or(false)
    }
    fn replace(&self, value: Value) -> Value {
        // Callers serialize episode/handle liveness with this swap, then drop
        // the previous payload after releasing every bookkeeping lock.
        std::mem::replace(&mut *lock(&self.value), value)
    }
}
fn typed_check<T: Any + Send + Sync>(
    check: impl Fn(&T, &Context, &serde_json::Value) -> bool + Send + Sync + 'static,
) -> ServiceCheck {
    Arc::new(move |value, context, config| {
        value
            .downcast_ref::<T>()
            .is_some_and(|value| check(value, context, config))
    })
}
type CleanupFuture = Pin<Box<dyn Future<Output = CallbackResult> + Send>>;
type Cleanup = Box<dyn FnOnce() -> CleanupFuture + Send>;
type SetupFuture = Pin<Box<dyn Future<Output = CallbackResult> + Send>>;
type SetupCallback = Box<dyn FnMut(&mut Setup<'_>) -> CallbackResult + Send>;
type AsyncCallback = Box<dyn FnMut(AsyncSetup) -> SetupFuture + Send>;
type StageFuture = Pin<Box<dyn Future<Output = Result<Inverse, String>> + Send>>;
type Stage = Box<dyn FnOnce(AsyncSetup) -> StageFuture + Send>;

fn lock<T>(value: &Mutex<T>) -> MutexGuard<'_, T> {
    // A user panic cannot permanently poison the host bookkeeping.
    value.lock().unwrap_or_else(|error| error.into_inner())
}
fn panic_message(panic: Box<dyn Any + Send>) -> String {
    if let Some(message) = panic.downcast_ref::<&str>() {
        format!("panic: {message}")
    } else if let Some(message) = panic.downcast_ref::<String>() {
        format!("panic: {message}")
    } else {
        "panic with non-string payload".into()
    }
}

/// One landed effect's inverse. Its factory and future are both panic-isolated.
pub struct Inverse(Cleanup);
impl Inverse {
    pub fn new(cleanup: impl FnOnce() -> CallbackResult + Send + 'static) -> Self {
        Self::new_async(move || async move { cleanup() })
    }
    pub fn new_async<F, Fut>(cleanup: F) -> Self
    where
        F: FnOnce() -> Fut + Send + 'static,
        Fut: Future<Output = CallbackResult> + Send + 'static,
    {
        Self(Box::new(move || Box::pin(cleanup())))
    }
    pub fn empty() -> Self {
        Self::new(|| Ok(()))
    }
}

enum CleanupAction {
    Callback(Cleanup),
    Child(ChildHandle),
}
struct Cleanups {
    protocol: StageProtocol,
    payloads: Vec<Option<CleanupAction>>,
}
impl Cleanups {
    fn new() -> Self {
        Self {
            protocol: StageProtocol::scope(),
            payloads: Vec::new(),
        }
    }
    fn iterator(committed: Vec<Binding>) -> Self {
        Self {
            protocol: StageProtocol::iterator(committed),
            payloads: Vec::new(),
        }
    }
    fn push(&mut self, cleanup: CleanupAction) {
        let token = self.payloads.len();
        self.payloads.push(Some(cleanup));
        self.protocol.register(token);
    }
    fn land(&mut self, inverse: Inverse) {
        let token = self.payloads.len();
        // Both the payload and its verified token become visible under the
        // episode lock before the outstanding stage is marked settled.
        self.payloads.push(Some(CleanupAction::Callback(inverse.0)));
        assert!(self.protocol.land(token), "only admitted stages may land");
    }
    fn pop(&mut self) -> Option<CleanupAction> {
        self.protocol
            .pop()
            .map(|token| self.payloads[token].take().expect("unique cleanup token"))
    }
    fn is_empty(&self) -> bool {
        self.protocol.is_empty()
    }
}

/// An asynchronous effect iterator. `poll_next` is one stage: after it returns
/// Pending the runtime retains it until that stage lands, even when cancelled.
/// Each Ready(Some(inverse)) is collected before another stage can start.
/// Implementations must not start unrelated background stages themselves.
pub trait EffectIterator: Send + Unpin + 'static {
    fn poll_next(
        &mut self,
        cx: &mut TaskContext<'_>,
        setup: &AsyncSetup,
    ) -> Poll<Option<Result<Inverse, String>>>;
}

/// A finite multi-stage effect. Stages run sequentially; independent Effects run
/// concurrently. Their landed inverses restore in reverse order within a group.
#[derive(Default)]
pub struct Effect {
    stages: std::collections::VecDeque<Stage>,
    running: Option<StageFuture>,
}
impl Effect {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn step<F, Fut>(mut self, stage: F) -> Self
    where
        F: FnOnce(AsyncSetup) -> Fut + Send + 'static,
        Fut: Future<Output = Result<Inverse, String>> + Send + 'static,
    {
        self.stages
            .push_back(Box::new(move |setup| Box::pin(stage(setup))));
        self
    }
    pub fn inverse(mut self, inverse: Inverse) -> Self {
        self.stages
            .push_back(Box::new(move |_| Box::pin(async move { Ok(inverse) })));
        self
    }
}
impl EffectIterator for Effect {
    fn poll_next(
        &mut self,
        cx: &mut TaskContext<'_>,
        setup: &AsyncSetup,
    ) -> Poll<Option<Result<Inverse, String>>> {
        if self.running.is_none() {
            let Some(stage) = self.stages.pop_front() else {
                return Poll::Ready(None);
            };
            self.running = Some(stage(setup.clone()));
        }
        match self.running.as_mut().unwrap().as_mut().poll(cx) {
            Poll::Pending => Poll::Pending,
            Poll::Ready(result) => {
                self.running = None;
                Poll::Ready(Some(result))
            }
        }
    }
}

#[derive(Default)]
struct EffectStatus {
    cancelled: bool,
    initialized: bool,
    finished: bool,
    errors: Vec<String>,
    next_waiter: u64,
    wakers: BTreeMap<u64, Waker>,
    driver: Option<Waker>,
}
fn wake_waiters(wakers: BTreeMap<u64, Waker>) {
    for waker in wakers.into_values() {
        waker.wake();
    }
}
fn finish_service(service: &EffectHandle) {
    let (waiters, driver) = {
        let mut status = lock(&service.status);
        status.finished = true;
        (std::mem::take(&mut status.wakers), status.driver.take())
    };
    drop(driver);
    wake_waiters(waiters);
}
/// A cancellation/join handle for one owner-bound effect group. Cancellation is
/// idempotent; join completes after the in-flight stage and every inverse land.
#[derive(Clone)]
pub struct EffectHandle {
    status: Arc<Mutex<EffectStatus>>,
}
impl EffectHandle {
    pub fn cancel(&self) {
        let mut status = lock(&self.status);
        status.cancelled = true;
        let driver = status.driver.take();
        drop(status);
        if let Some(waker) = driver {
            waker.wake();
        }
    }
    pub fn dispose(&self) {
        self.cancel();
    }
    pub fn initialized(&self) -> bool {
        lock(&self.status).initialized
    }
    pub fn finished(&self) -> bool {
        lock(&self.status).finished
    }
    pub fn errors(&self) -> Vec<String> {
        lock(&self.status).errors.clone()
    }
    pub fn join(&self) -> EffectJoin {
        EffectJoin {
            handle: self.clone(),
            waiter: None,
        }
    }
}
/// Wait for an effect's stage and inverses to finish. Dropping this wait removes
/// its waker registration; it does not cancel the effect itself.
#[must_use = "poll or await join to wait for effect cleanup"]
pub struct EffectJoin {
    handle: EffectHandle,
    waiter: Option<u64>,
}
impl Future for EffectJoin {
    type Output = CallbackResult;
    fn poll(self: Pin<&mut Self>, cx: &mut TaskContext<'_>) -> Poll<Self::Output> {
        let this = self.get_mut();
        // A custom waker can reenter an effect handle from clone or Drop too.
        let mut waker = Some(cx.waker().clone());
        let (result, previous) = {
            let mut status = lock(&this.handle.status);
            if status.finished {
                let result = if status.errors.is_empty() {
                    Ok(())
                } else {
                    Err(status.errors.join("; "))
                };
                let previous = this.waiter.take().and_then(|id| status.wakers.remove(&id));
                (Poll::Ready(result), previous)
            } else {
                let id = *this.waiter.get_or_insert_with(|| {
                    let id = status.next_waiter;
                    status.next_waiter =
                        id.checked_add(1).expect("effect join identities exhausted");
                    id
                });
                (
                    Poll::Pending,
                    status.wakers.insert(id, waker.take().unwrap()),
                )
            }
        };
        drop(previous);
        result
    }
}
impl Drop for EffectJoin {
    fn drop(&mut self) {
        let previous = self
            .waiter
            .take()
            .and_then(|id| lock(&self.handle.status).wakers.remove(&id));
        drop(previous);
    }
}

/// A child request becomes an ID after the current callback's poll returns.
#[derive(Clone)]
pub struct ChildHandle {
    state: Arc<Mutex<Result<Option<PluginId>, String>>>,
}
impl ChildHandle {
    pub fn id(&self) -> Option<PluginId> {
        lock(&self.state).as_ref().ok().copied().flatten()
    }
    pub fn error(&self) -> Option<String> {
        lock(&self.state).as_ref().err().cloned()
    }
}

static NEXT_KEY: AtomicU64 = AtomicU64::new(1);
static NEXT_REALM: AtomicU64 = AtomicU64::new(1);
static NEXT_EPISODE: AtomicU64 = AtomicU64::new(1);
fn fresh(counter: &AtomicU64) -> u64 {
    counter
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |n| n.checked_add(1))
        .expect("service or realm identity space exhausted")
}
pub struct ServiceKey<T> {
    id: u64,
    name: &'static str,
    marker: PhantomData<fn() -> T>,
}
impl<T> Copy for ServiceKey<T> {}
impl<T> Clone for ServiceKey<T> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T> fmt::Debug for ServiceKey<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("ServiceKey")
            .field(&self.name)
            .field(&self.id)
            .finish()
    }
}
impl<T> ServiceKey<T> {
    pub fn new(name: &'static str) -> Self {
        Self {
            id: fresh(&NEXT_KEY),
            name,
            marker: PhantomData,
        }
    }
    pub fn name(self) -> &'static str {
        self.name
    }
}
#[derive(Clone, Debug, Default)]
pub struct Context {
    realms: BTreeMap<u64, u64>,
}
impl Context {
    /// Explicit realm mapping for an externally driven typed episode. The host
    /// must validate these identities in its own graph before constructing it.
    pub fn with_realms(realms: impl IntoIterator<Item = (u64, u64)>) -> Self {
        Self {
            realms: realms.into_iter().collect(),
        }
    }
    pub fn new() -> Self {
        Self::default()
    }
    pub fn isolate<T>(&self, key: ServiceKey<T>) -> Self {
        let mut next = self.clone();
        next.realms.insert(key.id, fresh(&NEXT_REALM));
        next
    }
    pub fn share<T>(&self, key: ServiceKey<T>, source: &Context) -> Self {
        let mut next = self.clone();
        next.realms.insert(key.id, source.port(key).realm);
        next
    }
    pub fn port<T>(&self, key: ServiceKey<T>) -> Port {
        Port {
            key: key.id,
            realm: self.realms.get(&key.id).copied().unwrap_or(0),
        }
    }
}

enum Callback {
    Sync(SetupCallback),
    Async(AsyncCallback),
}
pub struct Plugin {
    name: String,
    dependencies: Vec<u64>,
    provisions: Vec<u64>,
    setup: Callback,
    injection_config: BTreeMap<u64, serde_json::Value>,
    config_update: Option<ConfigUpdateCallback>,
}
impl Plugin {
    pub fn new(
        name: impl Into<String>,
        setup: impl FnMut(&mut Setup<'_>) -> CallbackResult + Send + 'static,
    ) -> Self {
        Self {
            name: name.into(),
            dependencies: Vec::new(),
            provisions: Vec::new(),
            injection_config: BTreeMap::new(),
            config_update: None,
            setup: Callback::Sync(Box::new(setup)),
        }
    }
    pub fn new_async<F, Fut>(name: impl Into<String>, mut setup: F) -> Self
    where
        F: FnMut(AsyncSetup) -> Fut + Send + 'static,
        Fut: Future<Output = CallbackResult> + Send + 'static,
    {
        Self {
            name: name.into(),
            dependencies: Vec::new(),
            provisions: Vec::new(),
            injection_config: BTreeMap::new(),
            config_update: None,
            setup: Callback::Async(Box::new(move |ctx| Box::pin(setup(ctx)))),
        }
    }
    pub fn requires<T>(mut self, key: ServiceKey<T>) -> Self {
        if !self.dependencies.contains(&key.id) {
            self.dependencies.push(key.id);
        }
        self
    }
    /// Require a service with configuration passed to its availability predicate.
    pub fn requires_with_config<T>(
        mut self,
        key: ServiceKey<T>,
        config: serde_json::Value,
    ) -> Self {
        self = self.requires(key);
        self.injection_config.insert(key.id, config);
        self
    }
    /// Plan a reversible in-place configuration update. Planning must not mutate
    /// resources; the loader runs the returned apply/rollback operations.
    pub fn on_config_update(
        mut self,
        handler: impl FnMut(
                AsyncSetup,
                serde_json::Value,
                serde_json::Value,
            ) -> Result<crate::config::ConfigUpdate, String>
            + Send
            + 'static,
    ) -> Self {
        self.config_update = Some(Box::new(handler));
        self
    }
    pub fn provides<T>(mut self, key: ServiceKey<T>) -> Self {
        if !self.provisions.contains(&key.id) {
            self.provisions.push(key.id);
        }
        self
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum EpisodePhase {
    Loading,
    Active,
    Restoring,
    Closed,
}
struct ChildRequest {
    context: Context,
    plugin: Plugin,
    handle: ChildHandle,
    service: Option<EffectHandle>,
}
struct GroupRequest {
    group: usize,
    iterator: Box<dyn EffectIterator>,
    handle: EffectHandle,
}
struct Episode {
    phase: EpisodePhase,
    values: Values,
    cleanups: BTreeMap<usize, Cleanups>,
    groups: Vec<GroupRequest>,
    children: Vec<ChildRequest>,
    next_group: usize,
    cancelled_groups: std::collections::BTreeSet<usize>,
    driver: Option<Waker>,
    static_only: bool,
    service_updates: Option<Arc<dyn Fn() + Send + Sync>>,
    unsupported: Option<String>,
}
/// Owned setup context suitable for futures. Dependency slots belong to the
/// episode's committed providers; cloning never changes those identities.
/// Subsequent reads see payload updates within each committed provider slot.
/// A context from a completed episode rejects further mutation.
#[derive(Clone)]
pub struct AsyncSetup {
    generation: u64,
    owner: PluginId,
    context: Context,
    bindings: Vec<Binding>,
    provisions: Vec<Port>,
    anchor: Port,
    state: Arc<Mutex<Episode>>,
    group: usize,
}
impl AsyncSetup {
    fn require_dynamic(&self, feature: &str) -> CallbackResult {
        let mut state = lock(&self.state);
        Self::check_live(&state)?;
        if !state.static_only
            || (state.service_updates.is_some()
                && matches!(feature, "provide_checked" | "set" | "refresh"))
        {
            return Ok(());
        }
        let message = format!("UnsupportedStaticFeature: {feature}");
        if state.unsupported.is_none() {
            state.unsupported = Some(message.clone());
        }
        Err(message)
    }
    /// Check whether this episode still accepts new effects (Loading or Active).
    /// In-flight setup may register its inverse after cancellation, but new
    /// timer, event or child resource acquisition should use this guard first.
    pub fn ensure_active(&self) -> CallbackResult {
        let state = lock(&self.state);
        if state.cancelled_groups.contains(&self.group) || !state.cleanups.contains_key(&self.group)
        {
            return Err(CANCELLED.into());
        }
        match state.phase {
            EpisodePhase::Loading | EpisodePhase::Active => Ok(()),
            EpisodePhase::Restoring => Err(CANCELLED.into()),
            EpisodePhase::Closed => Err("owner episode has completed".into()),
        }
    }
    pub fn is_cancelled(&self) -> bool {
        let state = lock(&self.state);
        matches!(state.phase, EpisodePhase::Restoring | EpisodePhase::Closed)
            || state.cancelled_groups.contains(&self.group)
            || !state.cleanups.contains_key(&self.group)
    }
    pub fn owner(&self) -> PluginId {
        self.owner
    }
    pub fn context(&self) -> &Context {
        &self.context
    }
    fn check_live(state: &Episode) -> CallbackResult {
        if state.phase == EpisodePhase::Closed {
            Err("owner episode has completed".into())
        } else {
            Ok(())
        }
    }
    pub fn get<T: Any + Send + Sync>(&self, key: ServiceKey<T>) -> Result<Arc<T>, String> {
        let state = lock(&self.state);
        Self::check_live(&state)?;
        let port = self.context.port(key);
        let provider = if self.provisions.contains(&port) {
            self.owner
        } else {
            self.bindings
                .iter()
                .find(|b| b.key == port.key && b.realm == port.realm)
                .map(|b| b.provider)
                .ok_or_else(|| format!("undeclared dependency: {}", key.name))?
        };
        let value = state.values.get(&(provider, port.key, port.realm)).cloned();
        drop(state);
        value
            .and_then(|slot| slot.get::<T>())
            .ok_or_else(|| format!("service has no value: {}", key.name))
    }
    pub fn provide<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
        value: T,
    ) -> Result<Arc<T>, String> {
        self.provide_inner(key, value, None)
    }
    /// Publish a declared service with a pure per-consumer availability check.
    /// Panics make the dependency unavailable. Call `refresh` after external
    /// predicate state changes to wake a pending lifecycle driver.
    pub fn provide_checked<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
        value: T,
        check: impl Fn(&T, &Context, &serde_json::Value) -> bool + Send + Sync + 'static,
    ) -> Result<Arc<T>, String> {
        self.require_dynamic("provide_checked")?;
        self.provide_inner(key, value, Some(typed_check(check)))
    }
    fn provide_inner<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
        value: T,
        check: Option<ServiceCheck>,
    ) -> Result<Arc<T>, String> {
        let value = Arc::new(value);
        self.provide_slot(key, ServiceSlot::new(value.clone(), check))?;
        Ok(value)
    }
    fn provide_slot<T>(&self, key: ServiceKey<T>, value: SharedSlot) -> CallbackResult {
        let mut state = lock(&self.state);
        Self::check_live(&state)?;
        let port = self.context.port(key);
        if !self.provisions.contains(&port) {
            return Err(format!("undeclared provision: {}", key.name));
        }
        let slot = (self.owner, port.key, port.realm);
        if state.values.contains_key(&slot) {
            return Err(format!("duplicate value: {}", key.name));
        }
        state.values.insert(slot, value);
        let waker = state.driver.take();
        drop(state);
        if let Some(waker) = waker {
            waker.wake();
        }
        Ok(())
    }
    pub fn set<T: Any + Send + Sync>(&self, key: ServiceKey<T>, value: T) -> CallbackResult {
        self.require_dynamic("set")?;
        let mut state = lock(&self.state);
        Self::check_live(&state)?;
        let port = self.context.port(key);
        let slot = (self.owner, port.key, port.realm);
        if !self.provisions.contains(&port) {
            return Err(format!("service is not owned here: {}", key.name));
        }
        let slot = state
            .values
            .get(&slot)
            .cloned()
            .ok_or_else(|| format!("service is not owned here: {}", key.name))?;
        if state.service_updates.is_some()
            && !matches!(state.phase, EpisodePhase::Loading | EpisodePhase::Active)
        {
            return Err(CANCELLED.into());
        }
        let previous = slot.replace(Arc::new(value));
        let notify = state.service_updates.clone();
        let waker = state.driver.take();
        drop(state);
        drop(previous);
        if let Some(notify) = notify {
            notify();
        }
        if let Some(waker) = waker {
            waker.wake();
        }
        Ok(())
    }
    /// Notify the driver after changing external service-check state.
    pub fn refresh(&self) -> CallbackResult {
        self.require_dynamic("refresh")?;
        let mut state = lock(&self.state);
        Self::check_live(&state)?;
        if state.service_updates.is_some()
            && !matches!(state.phase, EpisodePhase::Loading | EpisodePhase::Active)
        {
            return Err(CANCELLED.into());
        }
        let notify = state.service_updates.clone();
        let waker = state.driver.take();
        drop(state);
        if let Some(notify) = notify {
            notify();
        }
        if let Some(waker) = waker {
            waker.wake();
        }
        Ok(())
    }
    /// Dynamically publish a service through an owned provider child. Its
    /// explicit owner-anchor dependency keeps owner resources alive until all
    /// consumers drain. It becomes available after owner initialization lands.
    pub fn publish<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
        value: T,
    ) -> Result<ServiceHandle<T>, String> {
        self.publish_inner(key, value, None)
    }
    pub fn publish_checked<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
        value: T,
        check: impl Fn(&T, &Context, &serde_json::Value) -> bool + Send + Sync + 'static,
    ) -> Result<ServiceHandle<T>, String> {
        self.publish_inner(key, value, Some(typed_check(check)))
    }
    fn publish_inner<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
        value: T,
        check: Option<ServiceCheck>,
    ) -> Result<ServiceHandle<T>, String> {
        self.require_dynamic("publish")?;
        self.ensure_active()?;
        let slot = ServiceSlot::new(Arc::new(value), check);
        let supplied = slot.clone();
        let mut plugin = Plugin::new(format!("service:{}", key.name), move |setup| {
            setup.inner.provide_slot(key, supplied.clone())
        })
        .provides(key);
        plugin.dependencies.push(self.anchor.key);
        let status = EffectHandle {
            status: Arc::new(Mutex::new(EffectStatus::default())),
        };
        let child = self.mount_request(&self.context, plugin, Some(status.clone()))?;
        Ok(ServiceHandle {
            child,
            slot,
            status,
            marker: PhantomData,
        })
    }
    pub fn on_cleanup(
        &self,
        cleanup: impl FnOnce() -> CallbackResult + Send + 'static,
    ) -> CallbackResult {
        self.on_cleanup_async(move || async move { cleanup() })
    }
    pub fn on_cleanup_async<F, Fut>(&self, cleanup: F) -> CallbackResult
    where
        F: FnOnce() -> Fut + Send + 'static,
        Fut: Future<Output = CallbackResult> + Send + 'static,
    {
        let mut state = lock(&self.state);
        Self::check_live(&state)?;
        let group = state
            .cleanups
            .get_mut(&self.group)
            .ok_or("effect group has completed")?;
        group.push(CleanupAction::Callback(Box::new(move || {
            Box::pin(cleanup())
        })));
        let waker = state.driver.take();
        drop(state);
        if let Some(waker) = waker {
            waker.wake();
        }
        Ok(())
    }
    pub fn mount(&self, plugin: Plugin) -> Result<ChildHandle, String> {
        self.mount_in(&self.context, plugin)
    }
    pub fn mount_in(&self, context: &Context, plugin: Plugin) -> Result<ChildHandle, String> {
        self.mount_request(context, plugin, None)
    }
    fn mount_request(
        &self,
        context: &Context,
        plugin: Plugin,
        service: Option<EffectHandle>,
    ) -> Result<ChildHandle, String> {
        self.require_dynamic("mount")?;
        let mut state = lock(&self.state);
        Self::check_live(&state)?;
        if state.phase == EpisodePhase::Restoring || state.cancelled_groups.contains(&self.group) {
            return Err(CANCELLED.into());
        }
        let handle = ChildHandle {
            state: Arc::new(Mutex::new(Ok(None))),
        };
        state
            .cleanups
            .get_mut(&self.group)
            .ok_or("effect group has completed")?
            .push(CleanupAction::Child(handle.clone()));
        state.children.push(ChildRequest {
            context: context.clone(),
            plugin,
            handle: handle.clone(),
            service,
        });
        let waker = state.driver.take();
        drop(state);
        if let Some(waker) = waker {
            waker.wake();
        }
        Ok(handle)
    }
    pub fn effect(&self, effect: impl EffectIterator) -> Result<EffectHandle, String> {
        self.require_dynamic("effect")?;
        let mut state = lock(&self.state);
        Self::check_live(&state)?;
        if state.phase == EpisodePhase::Restoring || state.cancelled_groups.contains(&self.group) {
            return Err(CANCELLED.into());
        }
        if !state.cleanups.contains_key(&self.group) {
            return Err("effect group has completed".into());
        }
        let group = state.next_group;
        state.next_group += 1;
        let handle = EffectHandle {
            status: Arc::new(Mutex::new(EffectStatus::default())),
        };
        state
            .cleanups
            .insert(group, Cleanups::iterator(self.bindings.clone()));
        state.groups.push(GroupRequest {
            group,
            iterator: Box::new(effect),
            handle: handle.clone(),
        });
        let waker = state.driver.take();
        drop(state);
        if let Some(waker) = waker {
            waker.wake();
        }
        Ok(handle)
    }
}
/// A dynamically published service. Dropping a handle does not revoke it;
/// owner cleanup or explicit `dispose` does. `join` observes cleanup and must be
/// polled alongside the runtime driver, like an effect join.
pub struct ServiceHandle<T> {
    child: ChildHandle,
    slot: SharedSlot,
    status: EffectHandle,
    marker: PhantomData<fn() -> T>,
}
impl<T> Clone for ServiceHandle<T> {
    fn clone(&self) -> Self {
        Self {
            child: self.child.clone(),
            slot: self.slot.clone(),
            status: self.status.clone(),
            marker: PhantomData,
        }
    }
}
impl<T: Any + Send + Sync> ServiceHandle<T> {
    pub fn id(&self) -> Option<PluginId> {
        self.child.id()
    }
    pub fn initialized(&self) -> bool {
        self.status.initialized()
    }
    pub fn finished(&self) -> bool {
        self.status.finished()
    }
    pub fn errors(&self) -> Vec<String> {
        self.status.errors()
    }
    pub fn get(&self) -> Result<Arc<T>, String> {
        self.slot
            .get()
            .ok_or_else(|| "service value type mismatch".into())
    }
    pub fn set(&self, value: T) -> CallbackResult {
        let mut status = lock(&self.status.status);
        if status.cancelled || status.finished {
            return Err(CANCELLED.into());
        }
        let previous = self.slot.replace(Arc::new(value));
        let driver = status.driver.take();
        drop(status);
        drop(previous);
        if let Some(driver) = driver {
            driver.wake();
        }
        Ok(())
    }
    pub fn refresh(&self) {
        let driver = lock(&self.status.status).driver.take();
        if let Some(driver) = driver {
            driver.wake();
        }
    }
    pub fn dispose(&self) {
        self.status.cancel();
    }
    pub fn join(&self) -> EffectJoin {
        self.status.join()
    }
}
/// Borrowed synchronous context. `to_async` is an episode-bound owned handle.
pub struct Setup<'a> {
    inner: &'a AsyncSetup,
}
impl Setup<'_> {
    pub fn owner(&self) -> PluginId {
        self.inner.owner()
    }
    pub fn context(&self) -> &Context {
        self.inner.context()
    }
    pub fn to_async(&self) -> AsyncSetup {
        self.inner.clone()
    }
    pub fn get<T: Any + Send + Sync>(&self, key: ServiceKey<T>) -> Result<Arc<T>, String> {
        self.inner.get(key)
    }
    pub fn provide<T: Any + Send + Sync>(
        &mut self,
        key: ServiceKey<T>,
        value: T,
    ) -> Result<Arc<T>, String> {
        self.inner.provide(key, value)
    }
    pub fn provide_checked<T: Any + Send + Sync>(
        &mut self,
        key: ServiceKey<T>,
        value: T,
        check: impl Fn(&T, &Context, &serde_json::Value) -> bool + Send + Sync + 'static,
    ) -> Result<Arc<T>, String> {
        self.inner.provide_checked(key, value, check)
    }
    pub fn publish<T: Any + Send + Sync>(
        &mut self,
        key: ServiceKey<T>,
        value: T,
    ) -> Result<ServiceHandle<T>, String> {
        self.inner.publish(key, value)
    }
    pub fn publish_checked<T: Any + Send + Sync>(
        &mut self,
        key: ServiceKey<T>,
        value: T,
        check: impl Fn(&T, &Context, &serde_json::Value) -> bool + Send + Sync + 'static,
    ) -> Result<ServiceHandle<T>, String> {
        self.inner.publish_checked(key, value, check)
    }
    pub fn refresh(&self) -> CallbackResult {
        self.inner.refresh()
    }
    pub fn set<T: Any + Send + Sync>(&mut self, key: ServiceKey<T>, value: T) -> CallbackResult {
        self.inner.set(key, value)
    }
    pub fn on_cleanup(&mut self, cleanup: impl FnOnce() -> CallbackResult + Send + 'static) {
        self.inner
            .on_cleanup(cleanup)
            .expect("live synchronous setup");
    }
    pub fn on_cleanup_async<F, Fut>(&mut self, cleanup: F)
    where
        F: FnOnce() -> Fut + Send + 'static,
        Fut: Future<Output = CallbackResult> + Send + 'static,
    {
        self.inner
            .on_cleanup_async(cleanup)
            .expect("live synchronous setup");
    }
    pub fn mount(&mut self, plugin: Plugin) -> Result<ChildHandle, String> {
        self.inner.mount(plugin)
    }
    pub fn mount_in(&mut self, context: &Context, plugin: Plugin) -> Result<ChildHandle, String> {
        self.inner.mount_in(context, plugin)
    }
    pub fn effect(&mut self, effect: impl EffectIterator) -> Result<EffectHandle, String> {
        self.inner.effect(effect)
    }
}

struct Group {
    id: usize,
    iterator: Option<Box<dyn EffectIterator>>,
    running: Option<CleanupFuture>,
    handle: EffectHandle,
}

/// Only a queued future may be discarded on withdrawal. Once its first poll
/// begins, the runtime owns it until it lands and can register its inverse.
enum RootSetup {
    Dormant,
    Queued(SetupFuture),
    Running(SetupFuture),
    Done,
}
impl RootSetup {
    fn is_pending(&self) -> bool {
        matches!(self, Self::Queued(_) | Self::Running(_))
    }
    fn is_done(&self) -> bool {
        matches!(self, Self::Done)
    }
    fn poll(
        &mut self,
        withdrawing: bool,
        cx: &mut TaskContext<'_>,
    ) -> Option<Poll<CallbackResult>> {
        match std::mem::replace(self, Self::Done) {
            Self::Queued(_) if withdrawing => None,
            Self::Queued(mut future) | Self::Running(mut future) => {
                Some(match poll_catching_unwind(future.as_mut(), cx) {
                    Ok(Poll::Pending) => {
                        *self = Self::Running(future);
                        Poll::Pending
                    }
                    Ok(Poll::Ready(result)) => Poll::Ready(result),
                    Err(panic) => Poll::Ready(Err(panic_message(panic))),
                })
            }
            state => {
                *self = state;
                None
            }
        }
    }
}
fn initialize_callback(callback: &mut Callback, episode: &AsyncSetup) -> Result<RootSetup, String> {
    catch_unwind(AssertUnwindSafe(|| match callback {
        Callback::Sync(callback) => {
            callback(&mut Setup { inner: episode })?;
            Ok(RootSetup::Done)
        }
        Callback::Async(callback) => Ok(RootSetup::Queued(callback(episode.clone()))),
    }))
    .unwrap_or_else(|panic| Err(panic_message(panic)))
}
fn initialize_cleanup(cleanup: Cleanup) -> Result<CleanupFuture, String> {
    catch_unwind(AssertUnwindSafe(cleanup)).map_err(panic_message)
}
fn poll_cleanup_callback(
    future: &mut CleanupFuture,
    cx: &mut TaskContext<'_>,
) -> Poll<CallbackResult> {
    match poll_catching_unwind(future.as_mut(), cx) {
        Ok(result) => result,
        Err(panic) => Poll::Ready(Err(panic_message(panic))),
    }
}
struct Mounted {
    next_config_update: Option<Option<ConfigUpdateCallback>>,
    anchor: Port,
    service: Option<EffectHandle>,
    injection_config: BTreeMap<u64, serde_json::Value>,
    config_update: Option<ConfigUpdateCallback>,
    declared_dependencies: Vec<u64>,
    declared_injection_config: BTreeMap<u64, serde_json::Value>,
    name: String,
    parent: Option<PluginId>,
    context: Context,
    dependencies: Vec<Port>,
    provisions: Vec<Port>,
    setup: Callback,
    episode: Option<AsyncSetup>,
    root_setup: RootSetup,
    groups: BTreeMap<usize, Group>,
    root_running: Option<CleanupFuture>,
    failed: Option<String>,
    restart: bool,
    // Children externally mounted while inactive become owner-bound on begin.
    owned: Vec<PluginId>,
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeError {
    Kernel(String),
    UnknownPlugin(PluginId),
    Retired(PluginId),
    UnloadingOwner(PluginId),
    InactiveOwner(PluginId),
    Setup { plugin: PluginId, message: String },
    Cleanup { plugin: PluginId, message: String },
    Stalled,
}
impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}
impl std::error::Error for RuntimeError {}
/// A shutdown runs every registered inverse it can, reporting both lifecycle
/// failure and all unconsumed cleanup failures instead of silently discarding them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShutdownError {
    pub lifecycle: Option<RuntimeError>,
    pub cleanup: Vec<RuntimeError>,
    pub setup: Vec<RuntimeError>,
}
impl fmt::Display for ShutdownError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "shutdown failed: lifecycle={:?}, {} setup and {} cleanup error(s)",
            self.lifecycle,
            self.setup.len(),
            self.cleanup.len()
        )
    }
}
impl std::error::Error for ShutdownError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.lifecycle
            .as_ref()
            .or(self.setup.first())
            .or(self.cleanup.first())
            .map(|error| error as _)
    }
}
fn kernel_error(error: impl fmt::Debug) -> RuntimeError {
    RuntimeError::Kernel(format!("{error:?}"))
}

pub struct Runtime {
    kernel: LifecycleDriver,
    mounted: BTreeMap<PluginId, Mounted>,
    values: Values,
    cleanup_errors: Vec<RuntimeError>,
    maintenance_changes: usize,
    shutdown_failures: Option<BTreeMap<PluginId, String>>,
}
impl Default for Runtime {
    fn default() -> Self {
        Self::new()
    }
}
impl Runtime {
    pub fn new() -> Self {
        Self {
            kernel: LifecycleDriver::new().expect("lifecycle domain identity exhausted"),
            mounted: BTreeMap::new(),
            values: BTreeMap::new(),
            cleanup_errors: Vec::new(),
            maintenance_changes: 0,
            shutdown_failures: None,
        }
    }
    /// Reclaim obsolete binding/declaration records without changing any live
    /// identity, episode, payload, target or cleanup order. Identity tombstones
    /// remain allocated so an old PluginId can never refer to a new plugin.
    pub fn compact(&mut self) -> Compaction {
        let result = Compaction {
            removed_bindings: self.kernel.compact_bindings(),
            removed_declarations: self.kernel.compact_declarations(),
        };
        self.maintenance_changes = 0;
        result
    }
    pub fn storage_stats(&self) -> StorageStats {
        StorageStats {
            registered_plugins: self.mounted.len(),
            identity_slots: self.kernel.identity_slots(),
            declaration_records: self.kernel.declaration_records(),
            binding_records: self.kernel.binding_records(),
            live_bindings: self
                .mounted
                .keys()
                .map(|id| self.committed(*id).len())
                .sum(),
            published_values: self.values.len(),
        }
    }
    /// Inspect blocked initialization/restoration without polling user code or
    /// cloning service payloads. Snapshot order is stable by plugin identity.
    pub fn snapshot(&self) -> RuntimeSnapshot {
        let mut plugins = Vec::new();
        for (&id, owner) in &self.mounted {
            let phase = self.phase(id).expect("registered mounted plugin");
            let target = self.kernel.target(id);
            let committed = self.committed(id);
            let mut blockers = Vec::new();
            if let Some(message) = &owner.failed {
                blockers.push(Blocker::Failed(message.clone()));
            }
            if phase == Phase::Inactive && !self.retired(id) {
                let missing: Vec<_> = owner
                    .dependencies
                    .iter()
                    .copied()
                    .filter(|port| self.kernel.resolve(*port).is_none())
                    .collect();
                if !missing.is_empty() {
                    blockers.push(Blocker::MissingDependencies(missing));
                }
            }
            if matches!(phase, Phase::Loading | Phase::Active) && !self.coherent(id) {
                blockers.push(Blocker::TargetChanged);
            }
            if owner.root_setup.is_pending() {
                blockers.push(Blocker::SetupPending);
            }
            let groups: Vec<_> = owner
                .groups
                .iter()
                .filter(|(_, g)| g.iterator.is_some())
                .map(|(&id, _)| id)
                .collect();
            if !groups.is_empty() {
                blockers.push(Blocker::EffectsPending(groups));
            }
            if phase == Phase::Unloading {
                let consumers: Vec<_> = self
                    .mounted
                    .keys()
                    .copied()
                    .filter(|consumer| self.committed(*consumer).iter().any(|b| b.provider == id))
                    .collect();
                if !consumers.is_empty() {
                    blockers.push(Blocker::CommittedConsumers(consumers));
                }
            }
            if self.cleanup_started(id)
                || owner.root_running.is_some()
                || owner.groups.values().any(|group| group.running.is_some())
            {
                blockers.push(Blocker::CleanupPending);
            }
            let children: Vec<_> = self
                .kernel
                .children(id)
                .into_iter()
                .filter(|child| self.retired(*child))
                .collect();
            if !children.is_empty() {
                blockers.push(Blocker::RetiringChildren(children));
            }
            plugins.push(PluginSnapshot {
                id,
                name: owner.name.clone(),
                parent: owner.parent,
                phase,
                retired: self.retired(id),
                restoring: self.cleanup_started(id),
                dependencies: owner.dependencies.clone(),
                provisions: owner.provisions.clone(),
                committed,
                target,
                blockers,
            });
        }
        RuntimeSnapshot {
            plugins,
            storage: self.storage_stats(),
        }
    }
    pub fn mount(
        &mut self,
        context: &Context,
        parent: Option<PluginId>,
        plugin: Plugin,
    ) -> Result<PluginId, RuntimeError> {
        self.mount_inner(context, parent, plugin, true)
    }
    fn mount_inner(
        &mut self,
        context: &Context,
        parent: Option<PluginId>,
        plugin: Plugin,
        register_inverse: bool,
    ) -> Result<PluginId, RuntimeError> {
        if let Some(parent) = parent {
            if !self.kernel.contains(parent) {
                return Err(RuntimeError::UnknownPlugin(parent));
            }
            if self.kernel.retired(parent) {
                return Err(RuntimeError::Retired(parent));
            }
            if self.kernel.phase(parent) == Some(Phase::Unloading) {
                return Err(RuntimeError::UnloadingOwner(parent));
            }
        }
        let port = |key| Port {
            key,
            realm: context.realms.get(&key).copied().unwrap_or(0),
        };
        let declared_dependencies = plugin.dependencies.clone();
        let declared_injection_config = plugin.injection_config.clone();
        let mut injection_config = parent
            .map(|parent| self.mounted[&parent].injection_config.clone())
            .unwrap_or_default();
        injection_config.extend(plugin.injection_config);
        let mut dependencies: Vec<_> = plugin.dependencies.into_iter().map(port).collect();
        let provisions: Vec<_> = plugin.provisions.into_iter().map(port).collect();
        // Inherit the parent's *actual ports*, including realms. This adds real
        // kernel dependencies, so a child cannot outlive a captured dependency.
        // A child's own provision is omitted: ownership is not a service cycle.
        if let Some(parent) = parent {
            for dependency in &self.mounted[&parent].dependencies {
                // Keep the inherited provider alive, and also resolve the key
                // in the child's realm when it has explicitly isolated it.
                for inherited in [*dependency, port(dependency.key)] {
                    if !provisions.contains(&inherited) && !dependencies.contains(&inherited) {
                        dependencies.push(inherited);
                    }
                }
            }
        }
        let anchor = Port {
            key: fresh(&NEXT_KEY),
            realm: 0,
        };
        let mut kernel_provisions = provisions.clone();
        kernel_provisions.push(anchor);
        let id = self
            .kernel
            .insert(parent, dependencies.clone(), kernel_provisions)
            .map_err(kernel_error)?;
        self.mounted.insert(
            id,
            Mounted {
                next_config_update: None,
                anchor,
                service: None,
                injection_config,
                config_update: plugin.config_update,
                declared_dependencies,
                declared_injection_config,
                name: plugin.name,
                parent,
                context: context.clone(),
                dependencies,
                provisions,
                setup: plugin.setup,
                episode: None,
                root_setup: RootSetup::Dormant,
                groups: BTreeMap::new(),
                root_running: None,
                failed: None,
                restart: false,
                owned: Vec::new(),
            },
        );
        if register_inverse {
            if let Some(parent) = parent {
                let owner = self.mounted.get_mut(&parent).unwrap();
                if let Some(episode) = &owner.episode {
                    lock(&episode.state)
                        .cleanups
                        .get_mut(&0)
                        .unwrap()
                        .push(CleanupAction::Child(ChildHandle {
                            state: Arc::new(Mutex::new(Ok(Some(id)))),
                        }));
                } else {
                    owner.owned.push(id);
                }
            }
        }
        Ok(id)
    }
    pub fn phase(&self, id: PluginId) -> Option<Phase> {
        self.kernel.phase(id)
    }
    pub fn contains(&self, id: PluginId) -> bool {
        self.kernel.contains(id)
    }
    pub fn ids(&self) -> Vec<PluginId> {
        self.kernel.ids()
    }
    pub fn retired(&self, id: PluginId) -> bool {
        self.kernel.retired(id)
    }
    pub fn name(&self, id: PluginId) -> Option<&str> {
        self.mounted.get(&id).map(|p| p.name.as_str())
    }
    pub fn context(&self, id: PluginId) -> Option<&Context> {
        self.mounted.get(&id).map(|p| &p.context)
    }
    pub fn failure(&self, id: PluginId) -> Option<&str> {
        self.mounted.get(&id)?.failed.as_deref()
    }
    pub fn committed(&self, id: PluginId) -> Vec<Binding> {
        self.kernel.committed(id)
    }
    /// Identity of the current activation, for rejecting stale update plans.
    pub fn episode_generation(&self, id: PluginId) -> Option<u64> {
        self.mounted
            .get(&id)?
            .episode
            .as_ref()
            .map(|episode| episode.generation)
    }
    pub fn cleanup_started(&self, id: PluginId) -> bool {
        self.kernel.cleanup_started(id)
    }
    pub fn get<T: Any + Send + Sync>(
        &self,
        context: &Context,
        key: ServiceKey<T>,
    ) -> Option<Arc<T>> {
        let port = context.port(key);
        let provider = self.kernel.resolve(port)?;
        let slot = self.values.get(&(provider, port.key, port.realm))?;
        slot.get::<T>()
    }
    /// Dynamic owner API; stale/retired owners cannot acquire more resources.
    pub fn owner_context(&self, id: PluginId) -> Result<AsyncSetup, RuntimeError> {
        if !self.contains(id) {
            return Err(RuntimeError::UnknownPlugin(id));
        }
        if self.retired(id) {
            return Err(RuntimeError::Retired(id));
        }
        if self.phase(id) == Some(Phase::Unloading) {
            return Err(RuntimeError::UnloadingOwner(id));
        }
        self.mounted[&id]
            .episode
            .clone()
            .ok_or(RuntimeError::InactiveOwner(id))
    }
    pub fn on_cleanup(
        &mut self,
        id: PluginId,
        cleanup: impl FnOnce() -> CallbackResult + Send + 'static,
    ) -> Result<(), RuntimeError> {
        self.owner_context(id)?
            .on_cleanup(cleanup)
            .map_err(|message| RuntimeError::Setup {
                plugin: id,
                message,
            })
    }
    pub fn on_cleanup_async<F, Fut>(&mut self, id: PluginId, cleanup: F) -> Result<(), RuntimeError>
    where
        F: FnOnce() -> Fut + Send + 'static,
        Fut: Future<Output = CallbackResult> + Send + 'static,
    {
        self.owner_context(id)?
            .on_cleanup_async(cleanup)
            .map_err(|message| RuntimeError::Setup {
                plugin: id,
                message,
            })
    }
    pub fn effect(
        &mut self,
        id: PluginId,
        effect: impl EffectIterator,
    ) -> Result<EffectHandle, RuntimeError> {
        self.owner_context(id)?
            .effect(effect)
            .map_err(|message| RuntimeError::Setup {
                plugin: id,
                message,
            })
    }
    pub fn set<T: Any + Send + Sync>(
        &mut self,
        id: PluginId,
        key: ServiceKey<T>,
        value: T,
    ) -> Result<(), RuntimeError> {
        self.owner_context(id)?
            .set(key, value)
            .map_err(|message| RuntimeError::Setup {
                plugin: id,
                message,
            })?;
        self.publish(id);
        Ok(())
    }
    /// Idempotent retirement. Children retire at their owned inverse, except a
    /// child relying on this owner's service must depart first to release it.
    pub fn dispose(&mut self, id: PluginId) -> Result<(), RuntimeError> {
        if !self.contains(id) {
            return Ok(());
        }
        self.kernel.retire(id).map_err(kernel_error)?;
        if let Some(service) = &self.mounted[&id].service {
            lock(&service.status).cancelled = true;
        }
        if let Some(episode) = &self.mounted[&id].episode {
            lock(&episode.state).phase = EpisodePhase::Restoring;
        }
        if self.phase(id) == Some(Phase::Inactive) {
            for child in self.kernel.children(id) {
                self.dispose(child)?;
            }
        }
        Ok(())
    }
    pub fn cancel(&mut self, id: PluginId) -> Result<(), RuntimeError> {
        self.dispose(id)
    }
    /// Drive the runtime until this owner's setup/restoration settles. Unlike
    /// settle(), unrelated pending plugins do not delay this join.
    pub fn join(&mut self, id: PluginId) -> Join<'_> {
        Join { runtime: self, id }
    }
    pub fn dispose_all(&mut self) -> Result<(), RuntimeError> {
        for id in self.kernel.ids() {
            self.dispose(id)?;
        }
        Ok(())
    }
    /// Retire every plugin, await all restoration, and return accumulated cleanup
    /// errors. Dropping this future pauses shutdown; calling it again resumes.
    /// Futures that never complete still require application cooperation.
    pub async fn shutdown(&mut self) -> Result<(), ShutdownError> {
        if self.shutdown_failures.is_none() {
            self.shutdown_failures = Some(
                self.mounted
                    .iter()
                    .filter_map(|(&id, plugin)| plugin.failed.clone().map(|message| (id, message)))
                    .collect(),
            );
        }
        let lifecycle = match self.dispose_all() {
            Ok(()) => self.settle().await.err(),
            Err(error) => Some(error),
        };
        self.compact();
        let cleanup = self.take_cleanup_errors();
        let setup = self
            .shutdown_failures
            .take()
            .unwrap_or_default()
            .into_iter()
            .map(|(plugin, message)| RuntimeError::Setup { plugin, message })
            .collect::<Vec<_>>();
        if lifecycle.is_none() && cleanup.is_empty() && setup.is_empty() {
            Ok(())
        } else {
            Err(ShutdownError {
                lifecycle,
                cleanup,
                setup,
            })
        }
    }
    pub fn restart(&mut self, id: PluginId) -> Result<(), RuntimeError> {
        if self.kernel.retired(id) {
            return Err(RuntimeError::Retired(id));
        }
        let plugin = self
            .mounted
            .get_mut(&id)
            .ok_or(RuntimeError::UnknownPlugin(id))?;
        plugin.failed = None;
        plugin.restart = self.kernel.phase(id) != Some(Phase::Inactive);
        Ok(())
    }
    pub fn update(
        &mut self,
        id: PluginId,
        setup: impl FnMut(&mut Setup<'_>) -> CallbackResult + Send + 'static,
    ) -> Result<(), RuntimeError> {
        if self.kernel.retired(id) {
            return Err(RuntimeError::Retired(id));
        }
        self.mounted
            .get_mut(&id)
            .ok_or(RuntimeError::UnknownPlugin(id))?
            .setup = Callback::Sync(Box::new(setup));
        self.restart(id)
    }
    pub fn update_async<F, Fut>(&mut self, id: PluginId, mut setup: F) -> Result<(), RuntimeError>
    where
        F: FnMut(AsyncSetup) -> Fut + Send + 'static,
        Fut: Future<Output = CallbackResult> + Send + 'static,
    {
        if self.kernel.retired(id) {
            return Err(RuntimeError::Retired(id));
        }
        self.mounted
            .get_mut(&id)
            .ok_or(RuntimeError::UnknownPlugin(id))?
            .setup = Callback::Async(Box::new(move |ctx| Box::pin(setup(ctx))));
        self.restart(id)
    }
    /// Ask a live plugin to plan an in-place update without applying it.
    pub fn prepare_config_update(
        &mut self,
        id: PluginId,
        previous: serde_json::Value,
        next: serde_json::Value,
    ) -> Result<crate::config::ConfigUpdate, RuntimeError> {
        let context = self.owner_context(id)?;
        if self.phase(id) != Some(Phase::Active) || !self.coherent(id) {
            return Ok(crate::config::ConfigUpdate::Restart);
        }
        let Some(handler) = self.mounted.get_mut(&id).unwrap().config_update.as_mut() else {
            return Ok(crate::config::ConfigUpdate::Restart);
        };
        catch_unwind(AssertUnwindSafe(|| handler(context, previous, next)))
            .unwrap_or_else(|panic| Err(panic_message(panic)))
            .map_err(|message| RuntimeError::Setup {
                plugin: id,
                message,
            })
    }
    pub(crate) fn config_recipe_compatible(&self, id: PluginId, plugin: &Plugin) -> bool {
        let Some(mounted) = self.mounted.get(&id) else {
            return false;
        };
        let provisions: Vec<_> = plugin
            .provisions
            .iter()
            .map(|key| Port {
                key: *key,
                realm: mounted.context.realms.get(key).copied().unwrap_or(0),
            })
            .collect();
        mounted.declared_dependencies == plugin.dependencies
            && mounted.provisions == provisions
            && mounted.declared_injection_config == plugin.injection_config
    }
    /// Adopt accepted configurations atomically after validating every target.
    /// Live hooks retain their current episode's captured state; new hooks are
    /// promoted together with the new setup recipe at the next activation.
    pub(crate) fn adopt_config_recipes(
        &mut self,
        recipes: Vec<(PluginId, Plugin)>,
    ) -> Result<(), RuntimeError> {
        for (id, plugin) in &recipes {
            self.owner_context(*id)?;
            if !self.config_recipe_compatible(*id, plugin) {
                return Err(RuntimeError::Setup {
                    plugin: *id,
                    message: "in-place update changed service declarations".into(),
                });
            }
        }
        let mut previous = Vec::new();
        for (id, plugin) in recipes {
            let mounted = self.mounted.get_mut(&id).unwrap();
            mounted.name = plugin.name;
            let setup = std::mem::replace(&mut mounted.setup, plugin.setup);
            let handler = mounted.next_config_update.replace(plugin.config_update);
            previous.push((setup, handler));
        }
        // Drop captured user state only after every recipe is installed.
        drop(previous);
        Ok(())
    }
    pub async fn replace(
        &mut self,
        id: PluginId,
        plugin: Plugin,
    ) -> Result<PluginId, RuntimeError> {
        let old = self
            .mounted
            .get(&id)
            .ok_or(RuntimeError::UnknownPlugin(id))?;
        let context = old.context.clone();
        let parent = old.parent;
        self.dispose(id)?;
        self.settle().await?;
        let replacement = self.mount(&context, parent, plugin)?;
        self.settle().await?;
        Ok(replacement)
    }
    pub fn settle(&mut self) -> Settle<'_> {
        Settle { runtime: self }
    }
    pub fn take_cleanup_errors(&mut self) -> Vec<RuntimeError> {
        std::mem::take(&mut self.cleanup_errors)
    }

    fn services_available(&self, id: PluginId) -> bool {
        let Some(bindings) = self.kernel.target(id) else {
            return false;
        };
        let plugin = &self.mounted[&id];
        bindings.iter().all(|binding| {
            // Anchors carry lifecycle identity, not user service values.
            if self
                .mounted
                .get(&binding.provider)
                .is_some_and(|provider| provider.anchor.key == binding.key)
            {
                return true;
            }
            self.values
                .get(&(binding.provider, binding.key, binding.realm))
                .is_some_and(|slot| {
                    slot.accepts(
                        &plugin.context,
                        plugin
                            .injection_config
                            .get(&binding.key)
                            .unwrap_or(&serde_json::Value::Null),
                    )
                })
        })
    }
    fn coherent(&self, id: PluginId) -> bool {
        self.kernel.coherent(id, self.mounted[&id].restart)
    }
    fn decision(&self, id: PluginId) -> Option<Decision> {
        let plugin = &self.mounted[&id];
        // Keep availability predicates at the executor's existing observation
        // points: arbitrary checks must not run while removing retired nodes.
        let available = match self.phase(id) {
            Some(Phase::Loading | Phase::Active) if self.coherent(id) => {
                self.services_available(id)
            }
            Some(Phase::Inactive) if !self.retired(id) && plugin.failed.is_none() => {
                self.services_available(id)
            }
            _ => false,
        };
        self.kernel.decision(
            id,
            HostStatus {
                available,
                failed: plugin.failed.is_some(),
                restart: plugin.restart,
            },
        )
    }
    fn leave(&mut self, id: PluginId) -> Result<(), RuntimeError> {
        self.kernel.leave(id).map_err(kernel_error)?;
        if let Some(episode) = &self.mounted[&id].episode {
            lock(&episode.state).phase = EpisodePhase::Restoring;
        }
        // True service dependents must unwind before the owner can restore. Do
        // not add an implicit child->parent edge or await child removal here.
        for child in self.kernel.ids() {
            if self
                .committed(child)
                .iter()
                .any(|binding| binding.provider == id)
                && self.is_descendant(child, id)
            {
                self.dispose(child)?;
            }
        }
        Ok(())
    }
    fn is_descendant(&self, mut child: PluginId, owner: PluginId) -> bool {
        while let Some(parent) = self.mounted.get(&child).and_then(|mounted| mounted.parent) {
            if parent == owner {
                return true;
            }
            child = parent;
        }
        false
    }
    fn latch(&mut self, id: PluginId, message: String) {
        if let Some(failures) = &mut self.shutdown_failures {
            failures.entry(id).or_insert_with(|| message.clone());
        }
        if self.mounted[&id].failed.is_none() {
            self.mounted.get_mut(&id).unwrap().failed = Some(message);
        }
    }
    fn publish(&mut self, id: PluginId) {
        if self.phase(id) != Some(Phase::Active) {
            return;
        }
        if let Some(episode) = &self.mounted[&id].episode {
            let values: Vec<_> = lock(&episode.state)
                .values
                .iter()
                .filter(|(slot, _)| slot.0 == id)
                .map(|(slot, value)| (*slot, value.clone()))
                .collect();
            // Replacing the last published Arc can execute a service destructor.
            // Release the episode lock before dropping any previous values.
            for (slot, value) in values {
                self.values.insert(slot, value);
            }
        }
    }
    fn start(&mut self, id: PluginId, cx: &mut TaskContext<'_>) {
        let bindings = self.kernel.committed(id);
        let values = bindings
            .iter()
            .filter_map(|binding| {
                let slot = (binding.provider, binding.key, binding.realm);
                self.values.get(&slot).map(|value| (slot, value.clone()))
            })
            .collect();
        let plugin = self.mounted.get_mut(&id).unwrap();
        if let Some(handler) = plugin.next_config_update.take() {
            plugin.config_update = handler;
        }
        let mut state = Episode {
            phase: EpisodePhase::Loading,
            // Retain precisely the committed dependencies until restoration
            // finishes; unrelated services must not gain implicit Arc owners.
            values,
            cleanups: BTreeMap::new(),
            groups: Vec::new(),
            children: Vec::new(),
            next_group: 1,
            cancelled_groups: Default::default(),
            driver: Some(cx.waker().clone()),
            static_only: false,
            service_updates: None,
            unsupported: None,
        };
        let mut root = Cleanups::new();
        for child in plugin.owned.drain(..) {
            root.push(CleanupAction::Child(ChildHandle {
                state: Arc::new(Mutex::new(Ok(Some(child)))),
            }));
        }
        state.cleanups.insert(0, root);
        let episode = AsyncSetup {
            generation: fresh(&NEXT_EPISODE),
            owner: id,
            context: plugin.context.clone(),
            bindings,
            provisions: plugin.provisions.clone(),
            anchor: plugin.anchor,
            state: Arc::new(Mutex::new(state)),
            group: 0,
        };
        plugin.episode = Some(episode.clone());
        plugin.root_setup = RootSetup::Done;
        match initialize_callback(&mut plugin.setup, &episode) {
            Ok(root) => plugin.root_setup = root,
            Err(message) => self.latch(id, message),
        }
    }
    fn drain_requests(&mut self, id: PluginId) -> Result<bool, RuntimeError> {
        let Some(episode) = self.mounted[&id].episode.clone() else {
            return Ok(false);
        };
        let (children, groups) = {
            let mut state = lock(&episode.state);
            (
                std::mem::take(&mut state.children),
                std::mem::take(&mut state.groups),
            )
        };
        let progress = !children.is_empty() || !groups.is_empty();
        for request in children {
            if request
                .service
                .as_ref()
                .is_some_and(|service| lock(&service.status).cancelled)
            {
                if let Some(service) = &request.service {
                    finish_service(service);
                }
                continue;
            }
            let result = self.mount_inner(&request.context, Some(id), request.plugin, false);
            match result {
                Ok(child) => {
                    *lock(&request.handle.state) = Ok(Some(child));
                    self.mounted.get_mut(&child).unwrap().service = request.service;
                }
                Err(error) => {
                    let message = error.to_string();
                    *lock(&request.handle.state) = Err(message.clone());
                    if let Some(service) = &request.service {
                        lock(&service.status).errors.push(message);
                        finish_service(service);
                    } else {
                        self.latch(id, message);
                    }
                }
            }
        }
        for request in groups {
            self.mounted.get_mut(&id).unwrap().groups.insert(
                request.group,
                Group {
                    id: request.group,
                    iterator: Some(request.iterator),
                    running: None,
                    handle: request.handle,
                },
            );
        }
        Ok(progress)
    }
    fn record_cleanup(&mut self, id: PluginId, group: Option<&EffectHandle>, message: String) {
        if let Some(handle) = group {
            lock(&handle.status).errors.push(message.clone());
        }
        self.cleanup_errors.push(RuntimeError::Cleanup {
            plugin: id,
            message,
        });
    }
    // A single inverse is started/polled at a time in each group. Other groups
    // still get polled when this one is Pending.
    fn poll_cleanup(
        &mut self,
        id: PluginId,
        group: usize,
        running: &mut Option<CleanupFuture>,
        handle: Option<&EffectHandle>,
        cx: &mut TaskContext<'_>,
    ) -> (bool, bool) {
        let episode = self.mounted[&id].episode.as_ref().unwrap().clone();
        let mut progress = false;
        if running.is_none() {
            let action = lock(&episode.state)
                .cleanups
                .get_mut(&group)
                .and_then(Cleanups::pop);
            if let Some(action) = action {
                progress = true;
                match action {
                    CleanupAction::Child(child) => {
                        if let Some(child) = child.id() {
                            if let Err(error) = self.dispose(child) {
                                self.record_cleanup(id, handle, error.to_string());
                            }
                        }
                    }
                    CleanupAction::Callback(cleanup) => match initialize_cleanup(cleanup) {
                        Ok(future) => *running = Some(future),
                        Err(message) => self.record_cleanup(id, handle, message),
                    },
                }
            }
        }
        if let Some(future) = running {
            match poll_cleanup_callback(future, cx) {
                Poll::Pending => return (progress, true),
                Poll::Ready(result) => {
                    *running = None;
                    progress = true;
                    if let Err(message) = result {
                        self.record_cleanup(id, handle, message);
                    }
                }
            }
        }
        (progress, false)
    }
    fn poll_groups(
        &mut self,
        id: PluginId,
        unloading: bool,
        cleanup_allowed: bool,
        cx: &mut TaskContext<'_>,
    ) -> (bool, bool) {
        let mut progress = false;
        let mut pending = false;
        let keys: Vec<_> = self.mounted[&id].groups.keys().copied().collect();
        for key in keys {
            // Another provider may have departed earlier in this same driver
            // pass. Recheck immediately before a fresh iterator stage.
            let can_start = matches!(self.phase(id), Some(Phase::Active | Phase::Loading))
                && self.coherent(id)
                && self.services_available(id)
                && self.mounted[&id].failed.is_none();
            let mut group = self
                .mounted
                .get_mut(&id)
                .unwrap()
                .groups
                .remove(&key)
                .unwrap();
            let driver = cx.waker().clone();
            let (cancelled, previous) = {
                let mut status = lock(&group.handle.status);
                let previous = status.driver.replace(driver);
                if unloading || !can_start {
                    status.cancelled = true;
                }
                (status.cancelled, previous)
            };
            drop(previous);
            if cancelled {
                let mut state = lock(&self.mounted[&id].episode.as_ref().unwrap().state);
                state.cancelled_groups.insert(group.id);
                // Completed iterators also pass through abstract Leave before
                // their accumulator is restored. In-flight cancellation still
                // keeps the delayed abstract Reloading state until landing.
                state.cleanups.get_mut(&group.id).unwrap().protocol.cancel();
            }
            if group.iterator.is_some() {
                let mut setup = self.mounted[&id].episode.as_ref().unwrap().clone();
                setup.group = group.id;
                let target = if can_start {
                    self.kernel.target(id)
                } else {
                    None
                };
                let admitted = {
                    let mut state = lock(&setup.state);
                    let protocol = &mut state.cleanups.get_mut(&group.id).unwrap().protocol;
                    protocol.admit(target.as_deref())
                };
                if !admitted {
                    group.iterator = None;
                    progress = true;
                } else {
                    let result = catch_unwind(AssertUnwindSafe(|| {
                        group.iterator.as_mut().unwrap().poll_next(cx, &setup)
                    }));
                    match result {
                        Ok(Poll::Pending) => {
                            pending = true;
                        }
                        Ok(Poll::Ready(Some(Ok(inverse)))) => {
                            lock(&setup.state)
                                .cleanups
                                .get_mut(&group.id)
                                .unwrap()
                                .land(inverse);
                            progress = true;
                            if cancelled {
                                group.iterator = None;
                            }
                        }
                        Ok(Poll::Ready(Some(Err(message)))) => {
                            assert!(lock(&setup.state)
                                .cleanups
                                .get_mut(&group.id)
                                .unwrap()
                                .protocol
                                .end());
                            if !(cancelled && message == CANCELLED) {
                                lock(&group.handle.status).errors.push(message.clone());
                                self.latch(id, message);
                            }
                            group.iterator = None;
                            progress = true;
                        }
                        Ok(Poll::Ready(None)) => {
                            assert!(lock(&setup.state)
                                .cleanups
                                .get_mut(&group.id)
                                .unwrap()
                                .protocol
                                .end());
                            group.iterator = None;
                            progress = true;
                        }
                        Err(panic) => {
                            assert!(lock(&setup.state)
                                .cleanups
                                .get_mut(&group.id)
                                .unwrap()
                                .protocol
                                .end());
                            let message = panic_message(panic);
                            if !(cancelled && message == CANCELLED) {
                                lock(&group.handle.status).errors.push(message.clone());
                                self.latch(id, message);
                            }
                            group.iterator = None;
                            progress = true;
                        }
                    }
                }
            }
            if group.iterator.is_none() {
                let mut status = lock(&group.handle.status);
                if !status.initialized {
                    status.initialized = true;
                    let wakers = std::mem::take(&mut status.wakers);
                    drop(status);
                    wake_waiters(wakers);
                }
            }
            if cancelled
                && group.iterator.is_none()
                && ((can_start && !unloading) || cleanup_allowed)
            {
                let (did, waiting) =
                    self.poll_cleanup(id, group.id, &mut group.running, Some(&group.handle), cx);
                progress |= did;
                pending |= waiting;
                let episode = self.mounted[&id].episode.as_ref().unwrap().clone();
                let mut state = lock(&episode.state);
                let empty = state.cleanups.get(&group.id).is_none_or(Cleanups::is_empty);
                if group.running.is_none() && empty {
                    // Seal under the same lock used by inverse registration.
                    // An escaped context either registers before sealing, or
                    // observes a completed group and receives an error.
                    state.cleanups.remove(&group.id);
                    drop(state);
                    let mut status = lock(&group.handle.status);
                    status.finished = true;
                    let wakers = std::mem::take(&mut status.wakers);
                    drop(status);
                    wake_waiters(wakers);
                    progress = true;
                    continue;
                }
            }
            self.mounted.get_mut(&id).unwrap().groups.insert(key, group);
        }
        (progress, pending)
    }
    fn poll_settle(&mut self, cx: &mut TaskContext<'_>) -> Poll<Result<(), RuntimeError>> {
        for _ in 0..1024 {
            if self.maintenance_changes >= 256 {
                self.compact();
            }
            let mut progress = false;
            let mut pending = false;
            // Dynamic service disposal is a normal verified provider retirement.
            for id in self.kernel.ids() {
                if let Some(service) = self.mounted[&id].service.clone() {
                    let driver = cx.waker().clone();
                    let (cancelled, previous) = {
                        let mut status = lock(&service.status);
                        (status.cancelled, status.driver.replace(driver))
                    };
                    drop(previous);
                    if cancelled && !self.retired(id) {
                        if let Err(error) = self.dispose(id) {
                            return Poll::Ready(Err(error));
                        }
                        progress = true;
                    }
                }
            }
            // Withdraw stale services before allowing any inverse to start.
            for id in self.kernel.ids() {
                if self.decision(id) == Some(Decision::Withdraw) {
                    if let Err(error) = self.leave(id) {
                        return Poll::Ready(Err(error));
                    }
                    progress = true;
                }
            }
            for id in self.kernel.ids() {
                if self.decision(id) == Some(Decision::Withdraw) {
                    if let Err(error) = self.leave(id) {
                        return Poll::Ready(Err(error));
                    }
                    progress = true;
                }
                let phase = self.phase(id).unwrap();
                if !matches!(phase, Phase::Loading | Phase::Active | Phase::Unloading) {
                    continue;
                }
                let Some(episode) = self.mounted[&id].episode.clone() else {
                    continue;
                };
                let driver = cx.waker().clone();
                let previous = lock(&episode.state).driver.replace(driver);
                drop(previous);
                let root_poll = self
                    .mounted
                    .get_mut(&id)
                    .unwrap()
                    .root_setup
                    .poll(phase == Phase::Unloading, cx);
                match root_poll {
                    Some(Poll::Pending) => pending = true,
                    Some(Poll::Ready(result)) => {
                        progress = true;
                        if let Err(message) = result {
                            if !(phase == Phase::Unloading && message == CANCELLED) {
                                self.latch(id, message);
                            }
                        }
                    }
                    None => {}
                }
                match self.drain_requests(id) {
                    Ok(did) => progress |= did,
                    Err(error) => return Poll::Ready(Err(error)),
                }
                let unloading = phase == Phase::Unloading;
                if unloading
                    && self.mounted[&id].root_setup.is_done()
                    && !self.kernel.cleanup_started(id)
                {
                    // Do not restore any resource while any group has a setup
                    // poll outstanding: it may still rely on that resource.
                    let in_flight = lock(&episode.state)
                        .cleanups
                        .values()
                        .any(|group| group.protocol.is_pending());
                    if !in_flight {
                        if let Err(error) = self.kernel.settle_setup(id) {
                            return Poll::Ready(Err(kernel_error(error)));
                        }
                        match self.kernel.begin_cleanup(id) {
                            Ok(()) => progress = true,
                            Err(KernelError::Relied) => {}
                            Err(error) => return Poll::Ready(Err(kernel_error(error))),
                        }
                    }
                }
                let cleanup_allowed = unloading && self.kernel.cleanup_started(id);
                let (did, waiting) = self.poll_groups(
                    id,
                    unloading || self.mounted[&id].failed.is_some(),
                    cleanup_allowed,
                    cx,
                );
                progress |= did;
                pending |= waiting;
                match self.drain_requests(id) {
                    Ok(did) => progress |= did,
                    Err(error) => return Poll::Ready(Err(error)),
                }
                if unloading && cleanup_allowed && self.mounted[&id].root_setup.is_done() {
                    let mut running = self.mounted.get_mut(&id).unwrap().root_running.take();
                    let (did, waiting) = self.poll_cleanup(id, 0, &mut running, None, cx);
                    self.mounted.get_mut(&id).unwrap().root_running = running;
                    progress |= did;
                    pending |= waiting;
                    let mut state = lock(&episode.state);
                    let root_empty = state.cleanups.get(&0).is_none_or(Cleanups::is_empty);
                    if self.mounted[&id].root_running.is_none()
                        && root_empty
                        && self.mounted[&id].groups.is_empty()
                    {
                        let ticket = self
                            .kernel
                            .pending_action(id)
                            .cloned()
                            .expect("restoration owns its cleanup action");
                        if let Err(error) = self.kernel.complete_action(&ticket) {
                            return Poll::Ready(Err(kernel_error(error)));
                        }
                        if let Err(error) = self.kernel.finish_cleanup(id) {
                            return Poll::Ready(Err(kernel_error(error)));
                        }
                        self.maintenance_changes += 1;
                        state.phase = EpisodePhase::Closed;
                        // Services commonly retain their setup context. Empty the
                        // closed episode to break value -> context -> value cycles,
                        // but only after all consumer inverses have completed.
                        let episode_values = std::mem::take(&mut state.values);
                        drop(state);
                        let plugin = self.mounted.get_mut(&id).unwrap();
                        plugin.episode = None;
                        plugin.root_setup = RootSetup::Dormant;
                        plugin.restart = false;
                        self.values.retain(|(owner, _, _), _| *owner != id);
                        drop(episode_values);
                        progress = true;
                    }
                } else if phase == Phase::Loading
                    && self.mounted[&id].root_setup.is_done()
                    && self.mounted[&id]
                        .groups
                        .values()
                        .all(|group| group.iterator.is_none())
                    && self.mounted[&id].failed.is_none()
                {
                    let mut state = lock(&episode.state);
                    // Serialize the Loading -> Active boundary with registration
                    // through escaped contexts. Requests admitted during Loading
                    // are initialized before the service becomes observable.
                    if !state.groups.is_empty() || !state.children.is_empty() {
                        progress = true;
                        continue;
                    }
                    let target = self.kernel.target(id);
                    if !state.cleanups.iter().all(|(group, cleanups)| {
                        *group == 0
                            || target
                                .as_ref()
                                .is_some_and(|target| cleanups.protocol.can_finish(target))
                    }) {
                        // The protocol rejects publication while any admitted
                        // stage remains outstanding or its target has drifted.
                        drop(state);
                        if let Err(error) = self.leave(id) {
                            return Poll::Ready(Err(error));
                        }
                        progress = true;
                        continue;
                    }
                    let missing = self.mounted[&id]
                        .provisions
                        .iter()
                        .find(|port| !state.values.contains_key(&(id, port.key, port.realm)))
                        .copied();
                    if let Some(port) = missing {
                        drop(state);
                        self.latch(id, format!("declared service {} has no value", port.key));
                        progress = true;
                    } else {
                        if let Err(error) = self.kernel.settle_setup(id) {
                            return Poll::Ready(Err(kernel_error(error)));
                        }
                        let finished = self.kernel.finish(id);
                        if finished.is_ok() {
                            state.phase = EpisodePhase::Active;
                        }
                        drop(state);
                        match finished {
                            Ok(()) => {
                                self.publish(id);
                                if let Some(service) = &self.mounted[&id].service {
                                    lock(&service.status).initialized = true;
                                }
                            }
                            Err(KernelError::Changed) => {
                                if let Err(error) = self.leave(id) {
                                    return Poll::Ready(Err(error));
                                }
                            }
                            Err(error) => return Poll::Ready(Err(kernel_error(error))),
                        }
                        progress = true;
                    }
                } else if phase == Phase::Active {
                    self.publish(id);
                }
            }
            for id in self.kernel.ids().into_iter().rev() {
                if self.retired(id)
                    && self.phase(id) == Some(Phase::Inactive)
                    && self.decision(id) == Some(Decision::Remove)
                {
                    if let Err(error) = self.kernel.remove(id) {
                        return Poll::Ready(Err(kernel_error(error)));
                    }
                    self.maintenance_changes += 1;
                    if let Some(service) = &self.mounted[&id].service {
                        finish_service(service);
                    }
                    self.mounted.remove(&id);
                    self.values.retain(|(owner, _, _), _| *owner != id);
                    progress = true;
                }
            }
            for id in self.kernel.ids() {
                if self.phase(id) != Some(Phase::Inactive)
                    || self.decision(id) != Some(Decision::Begin)
                {
                    continue;
                }
                match self.kernel.begin(id) {
                    Ok(()) => {}
                    Err(KernelError::MissingDependency) => continue,
                    Err(error) => return Poll::Ready(Err(kernel_error(error))),
                }
                self.start(id, cx);
                progress = true;
            }
            if progress {
                continue;
            }
            if pending {
                return Poll::Pending;
            }
            if self
                .kernel
                .ids()
                .iter()
                .any(|id| matches!(self.phase(*id), Some(Phase::Loading | Phase::Unloading)))
            {
                return Poll::Ready(Err(RuntimeError::Stalled));
            }
            if let Some((&id, plugin)) = self
                .mounted
                .iter()
                .find(|(_, plugin)| plugin.failed.is_some())
            {
                return Poll::Ready(Err(RuntimeError::Setup {
                    plugin: id,
                    message: plugin.failed.clone().unwrap(),
                }));
            }
            return Poll::Ready(Ok(()));
        }
        cx.waker().wake_by_ref();
        Poll::Pending
    }
}
/// Dropping Settle only pauses the driver; it never cancels setup or cleanup.
pub struct Settle<'a> {
    runtime: &'a mut Runtime,
}
impl Future for Settle<'_> {
    type Output = Result<(), RuntimeError>;
    fn poll(mut self: Pin<&mut Self>, cx: &mut TaskContext<'_>) -> Poll<Self::Output> {
        self.runtime.poll_settle(cx)
    }
}

/// A targeted lifecycle join. Dropping it pauses polling without cancellation.
pub struct Join<'a> {
    runtime: &'a mut Runtime,
    id: PluginId,
}
impl Future for Join<'_> {
    type Output = Result<(), RuntimeError>;
    fn poll(mut self: Pin<&mut Self>, cx: &mut TaskContext<'_>) -> Poll<Self::Output> {
        let driven = self.runtime.poll_settle(cx);
        let id = self.id;
        let Some(owner) = self.runtime.mounted.get(&id) else {
            return Poll::Ready(Ok(()));
        };
        let ready = matches!(
            self.runtime.phase(id),
            Some(Phase::Inactive | Phase::Active)
        ) && !self.runtime.retired(id)
            && !owner.restart
            && !owner.root_setup.is_pending()
            && owner
                .groups
                .values()
                .all(|group| group.iterator.is_none() && !lock(&group.handle.status).cancelled)
            && owner
                .episode
                .as_ref()
                .is_none_or(|episode| lock(&episode.state).groups.is_empty())
            && !self
                .runtime
                .kernel
                .children(id)
                .iter()
                .any(|child| self.runtime.retired(*child));
        if ready {
            return Poll::Ready(match &owner.failed {
                Some(message) => Err(RuntimeError::Setup {
                    plugin: id,
                    message: message.clone(),
                }),
                None => Ok(()),
            });
        }
        match driven {
            Poll::Ready(Err(error)) => Poll::Ready(Err(error)),
            _ => Poll::Pending,
        }
    }
}

#[cfg(test)]
mod setup_cancellation_tests {
    use super::*;
    use std::sync::atomic::AtomicBool;
    struct RootFuture {
        setup: AsyncSetup,
        ready: Arc<AtomicBool>,
        log: Arc<Mutex<Vec<&'static str>>>,
    }
    impl Future for RootFuture {
        type Output = CallbackResult;
        fn poll(self: Pin<&mut Self>, _: &mut TaskContext<'_>) -> Poll<Self::Output> {
            lock(&self.log).push("poll");
            if !self.ready.load(Ordering::SeqCst) {
                return Poll::Pending;
            }
            lock(&self.log).push("land");
            let log = self.log.clone();
            self.setup
                .on_cleanup(move || {
                    lock(&log).push("landed-inverse");
                    Ok(())
                })
                .unwrap();
            Poll::Ready(Ok(()))
        }
    }
    impl Drop for RootFuture {
        fn drop(&mut self) {
            lock(&self.log).push("future-drop");
        }
    }
    struct QueuedRoot {
        runtime: Runtime,
        owner: PluginId,
        ready: Arc<AtomicBool>,
        log: Arc<Mutex<Vec<&'static str>>>,
    }
    impl QueuedRoot {
        fn new() -> Self {
            let mut runtime = Runtime::new();
            let log = Arc::new(Mutex::new(Vec::new()));
            let ready = Arc::new(AtomicBool::new(false));
            let output = log.clone();
            let gate = ready.clone();
            let owner = runtime
                .mount(
                    &Context::new(),
                    None,
                    Plugin::new_async("root-cancellation", move |setup| {
                        lock(&output).push("factory");
                        let log = output.clone();
                        setup
                            .on_cleanup(move || {
                                lock(&log).push("factory-inverse");
                                Ok(())
                            })
                            .unwrap();
                        RootFuture {
                            setup,
                            ready: gate.clone(),
                            log: output.clone(),
                        }
                    }),
                )
                .unwrap();
            // Stop at the driver's real Begin/start boundary, before the next
            // pass may poll the returned future. This makes both cancellation
            // schedules explicit without relying on the driver's loop budget.
            runtime.kernel.begin(owner).unwrap();
            runtime.start(owner, &mut TaskContext::from_waker(Waker::noop()));
            Self {
                runtime,
                owner,
                ready,
                log,
            }
        }
        fn drive(&mut self) -> Poll<Result<(), RuntimeError>> {
            Pin::new(&mut self.runtime.settle()).poll(&mut TaskContext::from_waker(Waker::noop()))
        }
    }

    #[test]
    fn withdrawing_unpolled_setup_keeps_factory_registered_inverses() {
        let mut root = QueuedRoot::new();
        assert_eq!(*lock(&root.log), vec!["factory"]);
        root.runtime.dispose(root.owner).unwrap();
        assert_eq!(root.drive(), Poll::Ready(Ok(())));
        assert_eq!(
            *lock(&root.log),
            vec!["factory", "future-drop", "factory-inverse"]
        );
        assert!(!root.runtime.contains(root.owner));
    }

    #[test]
    fn withdrawing_pending_setup_keeps_future_and_collects_its_late_inverse() {
        let mut root = QueuedRoot::new();
        assert_eq!(root.drive(), Poll::Pending);
        root.runtime.dispose(root.owner).unwrap();
        assert_eq!(root.drive(), Poll::Pending);
        assert!(!root.runtime.cleanup_started(root.owner));
        assert!(lock(&root.log)
            .iter()
            .all(|entry| !entry.contains("inverse")));
        assert!(!lock(&root.log).contains(&"future-drop"));
        root.ready.store(true, Ordering::SeqCst);
        assert_eq!(root.drive(), Poll::Ready(Ok(())));
        assert!(lock(&root.log).ends_with(&[
            "land",
            "future-drop",
            "landed-inverse",
            "factory-inverse",
        ]));
        assert!(!root.runtime.contains(root.owner));
    }
}
