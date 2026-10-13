//! Typed, cooperatively polled host adapter for the verified lifecycle kernel.
//!
//! The kernel proves lifecycle and committed dependency safety. Futures, user
//! callbacks, shared values and the host scheduler are ordinary Rust, not proofs
//! of arbitrary effects. An in-flight setup stage is always allowed to land so
//! its inverse can be collected; cancellation stops subsequent stages.
pub mod static_host;

use crate::diagnostics::{Blocker, Compaction, PluginSnapshot, RuntimeSnapshot, StorageStats};
use crate::future_support::poll_catching_unwind;
use crate::service_error::{ServiceReadError, ServiceReadFailure};
use crate::CallbackError;
use cordis_driver::shared::native::NativeDriver;
use cordis_driver::shared::{Decision, HostStatus};
use cordis_kernel::async_completion::{invoke_future, Completion};
use cordis_kernel::cleanup_journal::{RestoreOutcome, RestoreTicket};
use cordis_kernel::cleanup_queue::completion::{
    CleanupDispatch, CleanupPolicy, CleanupReport, ValueCleanupReport,
};
use cordis_kernel::execution::{Execution, ExecutionPhase as EpisodePhase};
use cordis_kernel::lifecycle_state::registration::shared_child::{
    ChildCleanup, ChildDispatch, SharedChild,
};
use cordis_kernel::lifecycle_state::registration::{ChildIdentity, PluginDefinition};
use cordis_kernel::lifecycle_state::services::NativeValueError;
use cordis_kernel::poll_result::{normalize_effect_poll, normalize_poll};
use cordis_kernel::publication::values::ValueCell;
pub use cordis_kernel::reversible_value::program::{
    Instruction as ValueInstruction, Program as ValueProgram,
};
pub use cordis_kernel::reversible_value::Branch as ValueBranch;
use cordis_kernel::reversible_value::ValueError;
pub use cordis_kernel::reversible_value::{
    Operation as ValueOperation, Outcome as ValueOutcome, ReversibleValue,
};
use cordis_kernel::setup_work::{RootDispatch, RootOutput, WorkReceipt, WorkTicket};
use cordis_kernel::{Binding, Error as KernelError, Phase, Port};
use std::any::{Any, TypeId};
use std::collections::BTreeMap;
use std::fmt;
use std::future::Future;
use std::marker::PhantomData;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::pin::Pin;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, LazyLock, Mutex, MutexGuard};
use std::task::{Context as TaskContext, Poll, Waker};

pub type PluginId = usize;
pub type CallbackResult = Result<(), CallbackError>;
/// Reserved cooperative-abort result. It is treated as cancellation only after
/// the owner/group is cancelled; an active callback returning it still fails.
pub const CANCELLED: &str = "owner episode cancelled";
type Value = Arc<dyn Any + Send + Sync>;
type ServiceCheck = Arc<dyn Fn(&Value, &Context, &serde_json::Value) -> bool + Send + Sync>;
struct ServiceSlot {
    value: Mutex<ValueCell<Value>>,
    check: Option<ServiceCheck>,
}
type SharedSlot = Arc<ServiceSlot>;
type Values = BTreeMap<(PluginId, u64, u64), SharedSlot>;
// Values supplied by static embeddings retain their explicit host contract.
#[derive(Default)]
struct EpisodeValues(Values);
impl EpisodeValues {
    fn own(&self, owner: PluginId, port: Port) -> Option<&SharedSlot> {
        self.0.get(&(owner, port.key, port.realm))
    }
    fn provide(
        &mut self,
        owner: PluginId,
        provisions: &[Port],
        port: Port,
        value: SharedSlot,
    ) -> Result<(), (NativeValueError, SharedSlot)> {
        if !provisions.contains(&port) {
            return Err((NativeValueError::Undeclared, value));
        }
        let key = (owner, port.key, port.realm);
        if self.0.contains_key(&key) {
            return Err((NativeValueError::Duplicate, value));
        }
        self.0.insert(key, value);
        Ok(())
    }
}
type ConfigUpdateCallback = Box<
    dyn FnMut(
            AsyncSetup,
            serde_json::Value,
            serde_json::Value,
        ) -> Result<crate::config::ConfigUpdate, CallbackError>
        + Send,
>;

impl ServiceSlot {
    fn new(value: Value, check: Option<ServiceCheck>) -> SharedSlot {
        Arc::new(Self {
            value: Mutex::new(ValueCell::new(value)),
            check,
        })
    }
    fn get<T: Any + Send + Sync>(&self) -> Option<Arc<T>> {
        lock(&self.value).get().clone().downcast::<T>().ok()
    }
    fn accepts(&self, context: &Context, config: &serde_json::Value) -> bool {
        let Some(check) = &self.check else {
            return true;
        };
        let value = lock(&self.value).get().clone();
        // A user availability predicate never runs under host bookkeeping locks.
        catch_unwind(AssertUnwindSafe(|| check(&value, context, config))).unwrap_or(false)
    }
    fn replace(&self, value: Value) -> Value {
        // Callers serialize episode/handle liveness with this swap, then drop
        // the previous payload after releasing every bookkeeping lock.
        lock(&self.value).replace(value)
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
type RetryCleanup = Box<dyn FnMut() -> CleanupFuture + Send>;
type SetupFuture = Pin<Box<dyn Future<Output = CallbackResult> + Send>>;
type StageFuture = Pin<Box<dyn Future<Output = Result<Inverse, CallbackError>> + Send>>;
type Stage = Box<dyn FnOnce(AsyncSetup) -> StageFuture + Send>;

fn lock<T>(value: &Mutex<T>) -> MutexGuard<'_, T> {
    // A user panic cannot permanently poison the host bookkeeping.
    value.lock().unwrap_or_else(|error| error.into_inner())
}
fn value_error(error: ValueError) -> CallbackError {
    match error {
        ValueError::Closed => CANCELLED.into(),
        ValueError::Overflow => "reversible value arithmetic overflow".into(),
        ValueError::Capacity => "reversible value nesting exhausted".into(),
        ValueError::Interference => {
            "reversible value has a later write; restore it before retrying".into()
        }
    }
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

/// One landed effect's inverse. Factories and futures are panic-isolated.
pub struct Inverse(CleanupCallback);
impl Inverse {
    pub fn new(cleanup: impl FnOnce() -> CallbackResult + Send + 'static) -> Self {
        Self::new_async(move || async move { cleanup() })
    }
    pub fn new_async<F, Fut>(cleanup: F) -> Self
    where
        F: FnOnce() -> Fut + Send + 'static,
        Fut: Future<Output = CallbackResult> + Send + 'static,
    {
        Self(CleanupCallback::Once(Box::new(move || Box::pin(cleanup()))))
    }
    /// Retain this factory after an error/panic. The author must make another
    /// attempt safe after partial work; retry does not imply idempotence.
    pub fn retryable(mut cleanup: impl FnMut() -> CallbackResult + Send + 'static) -> Self {
        Self::retryable_async(move || std::future::ready(cleanup()))
    }
    /// Each explicit retry creates a fresh future. A pending future remains
    /// owned by Runtime even when its Settle/Join future is dropped.
    pub fn retryable_async<F, Fut>(mut cleanup: F) -> Self
    where
        F: FnMut() -> Fut + Send + 'static,
        Fut: Future<Output = CallbackResult> + Send + 'static,
    {
        Self(CleanupCallback::Retryable(Box::new(move || {
            Box::pin(cleanup())
        })))
    }
    pub fn empty() -> Self {
        Self::new(|| Ok(()))
    }
}

enum CleanupCallback {
    Once(Cleanup),
    Retryable(RetryCleanup),
}
type CleanupAction = ChildCleanup<CleanupCallback, ChildHandle>;
type EpisodeExecution = Execution<ServiceSlot, ChildRequest, GroupState, CleanupAction>;
struct Cleanups {
    protocol: EpisodeExecution,
}
impl Cleanups {
    fn new() -> Self {
        Self {
            protocol: Execution::new(fresh(&NEXT_CLEANUP)),
        }
    }
    fn contains(&self, group: usize) -> bool {
        self.protocol.contains(group)
    }
    fn push(&mut self, group: usize, cleanup: CleanupAction) {
        let accepted = self.protocol.register(group, cleanup);
        assert!(
            accepted.is_ok(),
            "only live groups accept cleanup registration"
        );
    }
    fn pop(&mut self, group: usize) -> Option<CleanupDispatch<CleanupCallback, ChildHandle>> {
        self.protocol
            .dispatch_cleanup(group)
            .expect("live cleanup group and available attempt identity")
    }
    #[allow(clippy::type_complexity)]
    fn complete_result(
        &mut self,
        group: usize,
        ticket: RestoreTicket,
        result: CallbackResult,
        retry: Option<RetryCleanup>,
        policy: CleanupPolicy,
    ) -> Result<
        CleanupReport<CallbackError, CleanupAction>,
        (RestoreTicket, CallbackResult, Option<CleanupAction>),
    > {
        self.protocol.complete_result(
            group,
            ticket,
            result,
            retry.map(|retry| CleanupAction::Callback(CleanupCallback::Retryable(retry))),
            policy,
        )
    }
    fn complete_reply(
        &mut self,
        group: usize,
        reply: CleanupReply,
        retry: Option<RetryCleanup>,
        policy: CleanupPolicy,
    ) -> Result<CleanupReport<CallbackError, CleanupAction>, RejectedCleanup> {
        let retry =
            retry.map(|factory| CleanupAction::Callback(CleanupCallback::Retryable(factory)));
        match reply {
            CleanupReply::Awaited(completion) => self
                .protocol
                .complete_future(group, completion, retry, policy)
                .map_err(|(completion, retry)| RejectedCleanup::Awaited(completion, retry)),
            CleanupReply::Failed(ticket, error) => self
                .protocol
                .complete_failure(group, ticket, error, retry, policy)
                .map_err(|(ticket, error, retry)| RejectedCleanup::Failed(ticket, error, retry)),
        }
    }
    fn can_retry(&self, group: usize) -> bool {
        self.protocol
            .get(group)
            .is_some_and(|queue| queue.can_retry())
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
    ) -> Poll<Option<Result<Inverse, CallbackError>>>;
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
        Fut: Future<Output = Result<Inverse, CallbackError>> + Send + 'static,
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
    ) -> Poll<Option<Result<Inverse, CallbackError>>> {
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
    errors: Vec<CallbackError>,
    terminal_error: Option<CallbackError>,
    external_child_id: Option<PluginId>,
    next_waiter: u64,
    wakers: BTreeMap<u64, Waker>,
    driver: Option<Waker>,
    notify: Option<Arc<dyn Fn() + Send + Sync>>,
}
fn wake_waiters(wakers: BTreeMap<u64, Waker>) {
    for waker in wakers.into_values() {
        waker.wake();
    }
}
fn finish_service(service: &EffectHandle) {
    let (waiters, driver, notify) = {
        let mut status = lock(&service.status);
        status.finished = true;
        (
            std::mem::take(&mut status.wakers),
            status.driver.take(),
            status.notify.take(),
        )
    };
    drop(driver);
    drop(notify);
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
        let notify = status.notify.clone();
        drop(status);
        if let Some(notify) = notify {
            notify();
        }
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
    pub fn errors(&self) -> Vec<CallbackError> {
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
            if status.finished || status.terminal_error.is_some() {
                let result = if status.errors.is_empty() {
                    Ok(())
                } else {
                    Err(CallbackError::multiple(status.errors.clone()))
                };
                let previous = this.waiter.take().and_then(|id| status.wakers.remove(&id));
                (Poll::Ready(result), previous)
            } else if status
                .external_child_id
                .is_some_and(static_host::child_join_blocked)
            {
                // A pending join cannot retain a provider whose removal it
                // awaits. This rejects only this wait, not the child's cleanup.
                let previous = this.waiter.take().and_then(|id| status.wakers.remove(&id));
                (Poll::Ready(Err("ReentrantServiceJoin".into())), previous)
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

#[derive(Clone)]
enum ChildState {
    Native {
        slot: SharedChild,
        error: Arc<Mutex<Option<String>>>,
    },
    External(Arc<Mutex<Result<Option<PluginId>, String>>>),
}
impl ChildState {
    fn id(&self) -> Option<PluginId> {
        match self {
            Self::Native { slot, .. } => slot.snapshot().identity().map(|child| child.id()),
            Self::External(result) => lock(result).as_ref().ok().copied().flatten(),
        }
    }
    fn error(&self) -> Option<String> {
        match self {
            Self::Native { error, .. } => lock(error).clone(),
            Self::External(result) => lock(result).as_ref().err().cloned(),
        }
    }
}

/// A child request becomes an ID after the current callback's poll returns.
#[derive(Clone)]
pub struct ChildHandle {
    state: ChildState,
    external: Option<static_host::StaticChildControl>,
}
impl ChildHandle {
    pub fn id(&self) -> Option<PluginId> {
        self.state.id()
    }
    pub fn error(&self) -> Option<String> {
        self.state.error()
    }
}

static NEXT_KEY: AtomicU64 = AtomicU64::new(1);
type SharedKeys = BTreeMap<(TypeId, Option<&'static str>), u64>;
static SHARED_KEYS: LazyLock<Mutex<SharedKeys>> = LazyLock::new(|| Mutex::new(BTreeMap::new()));
static NEXT_REALM: AtomicU64 = AtomicU64::new(1);
static NEXT_EPISODE: AtomicU64 = AtomicU64::new(1);
static NEXT_CLEANUP: AtomicU64 = AtomicU64::new(1);
fn fresh(counter: &AtomicU64) -> u64 {
    counter
        .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |n| n.checked_add(1))
        .expect("service or realm identity space exhausted")
}
/// A typed service identity. `new` is fresh; `of` and `named` share an identity
/// within this linked host. Names on fresh keys are diagnostic labels only.
/// Keys are invariant in their payload type, including function-pointer types.
///
/// ```compile_fail
/// use cordis::ServiceKey;
/// fn change_type(key: ServiceKey<fn(&str)>) -> ServiceKey<fn(&'static str)> {
///     key
/// }
/// ```
pub struct ServiceKey<T> {
    id: u64,
    name: &'static str,
    marker: PhantomData<fn(T) -> T>,
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
impl<T: 'static> ServiceKey<T> {
    /// The canonical service key for this Rust type in this linked host.
    /// This is not a cross-process or dynamic-library ABI identity.
    pub fn of() -> Self {
        Self::shared(None, std::any::type_name::<T>())
    }
    /// A canonical named instance of a service type. Unlike `new`, repeated
    /// calls with the same type and name return the same identity.
    pub fn named(name: &'static str) -> Self {
        Self::shared(Some(name), name)
    }
    fn shared(qualifier: Option<&'static str>, name: &'static str) -> Self {
        let id = *lock(&SHARED_KEYS)
            .entry((TypeId::of::<T>(), qualifier))
            .or_insert_with(|| fresh(&NEXT_KEY));
        Self {
            id,
            name,
            marker: PhantomData,
        }
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

type RootReply = RootOutput<CallbackResult, SetupFuture>;
type Callback = Box<dyn FnMut(AsyncSetup) -> RootReply + Send>;
fn sync_recipe(
    mut setup: impl FnMut(&mut Setup<'_>) -> CallbackResult + Send + 'static,
) -> Callback {
    Box::new(move |argument| RootOutput::Ready(setup(&mut Setup { inner: &argument })))
}
fn async_recipe<F, Fut>(mut setup: F) -> Callback
where
    F: FnMut(AsyncSetup) -> Fut + Send + 'static,
    Fut: Future<Output = CallbackResult> + Send + 'static,
{
    Box::new(move |argument| RootOutput::Pending(Box::pin(setup(argument))))
}
pub struct Plugin {
    name: String,
    dependencies: Vec<u64>,
    provisions: Vec<u64>,
    setup: Callback,
    injection_config: BTreeMap<u64, serde_json::Value>,
    config_update: Option<ConfigUpdateCallback>,
    dependency_conflict: Option<(u64, &'static str)>,
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
            dependency_conflict: None,
            setup: sync_recipe(setup),
        }
    }
    pub fn new_async<F, Fut>(name: impl Into<String>, setup: F) -> Self
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
            dependency_conflict: None,
            setup: async_recipe(setup),
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
        if self
            .injection_config
            .get(&key.id)
            .is_some_and(|previous| previous != &config)
        {
            self.dependency_conflict.get_or_insert((key.id, key.name));
        }
        self.injection_config.insert(key.id, config);
        self
    }
    fn validate(&self) -> Result<(), RuntimeError> {
        match self.dependency_conflict {
            Some((key, service)) => Err(RuntimeError::DependencyConflict { key, service }),
            None => Ok(()),
        }
    }
    /// Plan a reversible in-place configuration update. Planning must not mutate
    /// resources; the loader runs the returned apply/rollback operations.
    pub fn on_config_update(
        mut self,
        handler: impl FnMut(
                AsyncSetup,
                serde_json::Value,
                serde_json::Value,
            ) -> Result<crate::config::ConfigUpdate, CallbackError>
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

type ChildRequest = ChildDispatch<NativeChildInput, ExternalChildRequest>;
struct NativeChildInput {
    context: Context,
    plugin: Plugin,
    service: Option<EffectHandle>,
    error: Arc<Mutex<Option<String>>>,
}
struct ExternalChildRequest {
    context: Context,
    plugin: Plugin,
    handle: ChildHandle,
}
struct Episode {
    values: EpisodeValues,
    cleanups: Cleanups,
    driver: Option<Waker>,
    static_only: bool,
    dynamic_host: Option<Arc<dyn Fn() + Send + Sync>>,
    external_children: Vec<static_host::StaticChildControl>,
    service_updates: Option<Arc<dyn Fn() + Send + Sync>>,
    unsupported: Option<String>,
}
impl Episode {
    fn phase(&self) -> EpisodePhase {
        self.cleanups.protocol.phase()
    }
    fn withdraw(&mut self) {
        self.cleanups.protocol.withdraw();
    }
    fn seal(&mut self) -> bool {
        self.cleanups.protocol.seal_external()
    }
    fn can_finish(&self, target: &[Binding]) -> bool {
        self.cleanups.protocol.can_finish(target)
    }
    fn own(&self, owner: PluginId, port: Port) -> Option<&SharedSlot> {
        match self.cleanups.protocol.native() {
            Some(values) if values.ticket().id == owner => values.own(port),
            Some(_) => None,
            None => self.values.own(owner, port),
        }
    }
    fn provide(
        &mut self,
        owner: PluginId,
        provisions: &[Port],
        port: Port,
        value: SharedSlot,
    ) -> Result<(), (NativeValueError, SharedSlot)> {
        if self.cleanups.protocol.native().is_some() {
            self.cleanups.protocol.provide(port, value)
        } else {
            self.values.provide(owner, provisions, port, value)
        }
    }
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
            || (state.dynamic_host.is_some() && matches!(feature, "publish" | "mount"))
            || (state.service_updates.is_some()
                && matches!(feature, "provide_checked" | "set" | "refresh"))
        {
            return Ok(());
        }
        let message = format!("UnsupportedStaticFeature: {feature}");
        if state.unsupported.is_none() {
            state.unsupported = Some(message.clone());
        }
        Err(message.into())
    }
    /// Check whether this episode still accepts new effects (Loading or Active).
    /// In-flight setup may register its inverse after cancellation, but new
    /// timer, event or child resource acquisition should use this guard first.
    pub fn ensure_active(&self) -> CallbackResult {
        let state = lock(&self.state);
        if !state.cleanups.protocol.accepts_acquisition(self.group) {
            return Err(CANCELLED.into());
        }
        match state.phase() {
            EpisodePhase::Loading | EpisodePhase::Active => Ok(()),
            EpisodePhase::Restoring => Err(CANCELLED.into()),
            EpisodePhase::Closed => Err("owner episode has completed".into()),
        }
    }
    pub fn is_cancelled(&self) -> bool {
        let state = lock(&self.state);
        matches!(
            state.phase(),
            EpisodePhase::Restoring | EpisodePhase::Closed
        ) || !state.cleanups.protocol.accepts_acquisition(self.group)
    }
    pub fn owner(&self) -> PluginId {
        self.owner
    }
    pub fn context(&self) -> &Context {
        &self.context
    }
    fn check_live(state: &Episode) -> CallbackResult {
        if state.phase() == EpisodePhase::Closed {
            Err("owner episode has completed".into())
        } else {
            Ok(())
        }
    }
    #[track_caller]
    pub fn get<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
    ) -> Result<Arc<T>, ServiceReadError> {
        self.require(key)
    }
    /// Read the episode-committed provider, with structured call-site errors.
    /// Reads remain valid during restoration and reject a completed episode.
    #[track_caller]
    pub fn require<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
    ) -> Result<Arc<T>, ServiceReadError> {
        let port = self.context.port(key);
        let location = std::panic::Location::caller();
        let error = |reason, provider| ServiceReadError {
            reason,
            provider,
            port,
            location,
            service: key.name,
            value_type: std::any::type_name::<T>(),
            plugin: self.owner,
            generation: self.generation,
        };
        let state = lock(&self.state);
        if state.phase() == EpisodePhase::Closed {
            return Err(error(ServiceReadFailure::ClosedEpisode, None));
        }
        let (provider, value) = match state.cleanups.protocol.native() {
            Some(values) => {
                let (provider, slot) = values.read(port).map_err(|failure| {
                    let reason = match failure.reason {
                        NativeValueError::Closed => ServiceReadFailure::ClosedEpisode,
                        NativeValueError::Undeclared => ServiceReadFailure::Undeclared,
                        _ => ServiceReadFailure::MissingValue,
                    };
                    error(reason, failure.provider)
                })?;
                (provider, Some(slot.clone()))
            }
            None => {
                let values = &state.values.0;
                let provider = if self.provisions.contains(&port) {
                    self.owner
                } else {
                    self.bindings
                        .iter()
                        .find(|binding| binding.key == port.key && binding.realm == port.realm)
                        .map(|binding| binding.provider)
                        .ok_or_else(|| error(ServiceReadFailure::Undeclared, None))?
                };
                (
                    provider,
                    values.get(&(provider, port.key, port.realm)).cloned(),
                )
            }
        };
        drop(state);
        let slot = value.ok_or_else(|| error(ServiceReadFailure::MissingValue, Some(provider)))?;
        slot.get::<T>()
            .ok_or_else(|| error(ServiceReadFailure::TypeMismatch, Some(provider)))
    }
    pub fn provide<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
        value: T,
    ) -> Result<Arc<T>, CallbackError> {
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
    ) -> Result<Arc<T>, CallbackError> {
        self.require_dynamic("provide_checked")?;
        self.provide_inner(key, value, Some(typed_check(check)))
    }
    fn provide_inner<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
        value: T,
        check: Option<ServiceCheck>,
    ) -> Result<Arc<T>, CallbackError> {
        let value = Arc::new(value);
        self.provide_slot(key, ServiceSlot::new(value.clone(), check))?;
        Ok(value)
    }
    fn provide_slot<T>(&self, key: ServiceKey<T>, value: SharedSlot) -> CallbackResult {
        let mut state = lock(&self.state);
        Self::check_live(&state)?;
        let port = self.context.port(key);
        let result = state.provide(self.owner, &self.provisions, port, value);
        let waker = if result.is_ok() {
            state.driver.take()
        } else {
            None
        };
        drop(state);
        result.map_err(|(reason, rejected)| {
            drop(rejected);
            match reason {
                NativeValueError::Closed => "owner episode has completed".to_owned(),
                NativeValueError::Undeclared => format!("undeclared provision: {}", key.name),
                NativeValueError::Duplicate => format!("duplicate value: {}", key.name),
                NativeValueError::Missing => format!("missing value: {}", key.name),
            }
        })?;
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
        if !self.provisions.contains(&port) {
            return Err(format!("service is not owned here: {}", key.name).into());
        }
        let slot = state
            .own(self.owner, port)
            .cloned()
            .ok_or_else(|| format!("service is not owned here: {}", key.name))?;
        if state.service_updates.is_some()
            && !matches!(state.phase(), EpisodePhase::Loading | EpisodePhase::Active)
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
    /// Apply a checked operation to a declared shared service. Its actual
    /// inverse enters this episode's cleanup queue before the call returns.
    /// Interference blocks restoration and keeps that inverse for retry.
    pub fn update_reversible(
        &self,
        key: ServiceKey<ReversibleValue>,
        operation: ValueOperation,
    ) -> Result<ValueOutcome, CallbackError> {
        let value = self.get(key)?;
        let mut state = lock(&self.state);
        Self::check_live(&state)?;
        let result = state.cleanups.protocol.apply_value(
            self.group,
            &value,
            operation,
            ValueBranch {
                matched: None,
                unmatched: None,
            },
        );
        let wake = if result.is_ok() {
            state.driver.take()
        } else {
            None
        };
        drop(state);
        if let Some(wake) = wake {
            wake.wake();
        }
        result.map(|admitted| admitted.outcome).map_err(value_error)
    }
    /// Run a finite program without interleaved writes to this value. Every
    /// successful prefix remains registered even if a later operation fails.
    pub fn run_value_program(
        &self,
        key: ServiceKey<ReversibleValue>,
        program: &ValueProgram,
    ) -> Result<Vec<ValueOutcome>, CallbackError> {
        let value = self.get(key)?;
        let mut state = lock(&self.state);
        Self::check_live(&state)?;
        let result = state
            .cleanups
            .protocol
            .run_value_program(self.group, &value, program);
        let wake = if result.is_ok() {
            state.driver.take()
        } else {
            None
        };
        drop(state);
        if let Some(wake) = wake {
            wake.wake();
        }
        let report = result.map_err(value_error)?;
        match report.error {
            Some(error) => Err(value_error(error)),
            None => Ok(report.outcomes),
        }
    }
    /// Notify the driver after changing external service-check state.
    pub fn refresh(&self) -> CallbackResult {
        self.require_dynamic("refresh")?;
        let mut state = lock(&self.state);
        Self::check_live(&state)?;
        if state.service_updates.is_some()
            && !matches!(state.phase(), EpisodePhase::Loading | EpisodePhase::Active)
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
    ) -> Result<ServiceHandle<T>, CallbackError> {
        self.publish_inner(key, value, None)
    }
    pub fn publish_checked<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
        value: T,
        check: impl Fn(&T, &Context, &serde_json::Value) -> bool + Send + Sync + 'static,
    ) -> Result<ServiceHandle<T>, CallbackError> {
        self.publish_inner(key, value, Some(typed_check(check)))
    }
    fn publish_inner<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
        value: T,
        check: Option<ServiceCheck>,
    ) -> Result<ServiceHandle<T>, CallbackError> {
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
            status: Arc::new(Mutex::new(EffectStatus {
                notify: lock(&self.state).dynamic_host.clone(),
                ..EffectStatus::default()
            })),
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
        self.register_inverse(Inverse::new_async(cleanup))
    }
    pub fn on_cleanup_retryable(
        &self,
        cleanup: impl FnMut() -> CallbackResult + Send + 'static,
    ) -> CallbackResult {
        self.register_inverse(Inverse::retryable(cleanup))
    }
    pub fn on_cleanup_retryable_async<F, Fut>(&self, cleanup: F) -> CallbackResult
    where
        F: FnMut() -> Fut + Send + 'static,
        Fut: Future<Output = CallbackResult> + Send + 'static,
    {
        self.register_inverse(Inverse::retryable_async(cleanup))
    }
    fn register_inverse(&self, inverse: Inverse) -> CallbackResult {
        let mut state = lock(&self.state);
        Self::check_live(&state)?;
        if !state.cleanups.contains(self.group) {
            return Err("effect group has completed".into());
        }
        state
            .cleanups
            .push(self.group, CleanupAction::Callback(inverse.0));
        let waker = state.driver.take();
        drop(state);
        if let Some(waker) = waker {
            waker.wake();
        }
        Ok(())
    }
    pub fn mount(&self, plugin: Plugin) -> Result<ChildHandle, CallbackError> {
        self.mount_in(&self.context, plugin)
    }
    pub fn mount_in(
        &self,
        context: &Context,
        plugin: Plugin,
    ) -> Result<ChildHandle, CallbackError> {
        self.mount_request(context, plugin, None)
    }
    fn mount_request(
        &self,
        context: &Context,
        plugin: Plugin,
        service: Option<EffectHandle>,
    ) -> Result<ChildHandle, CallbackError> {
        self.require_dynamic("mount")?;
        let mut state = lock(&self.state);
        Self::check_live(&state)?;
        if state.phase() == EpisodePhase::Restoring
            || !state.cleanups.protocol.accepts_acquisition(self.group)
        {
            return Err(CANCELLED.into());
        }
        if !state.cleanups.contains(self.group) {
            return Err("effect group has completed".into());
        }
        let handle = if state.cleanups.protocol.lifecycle_ticket().is_some() {
            let error = Arc::new(Mutex::new(None));
            let request = NativeChildInput {
                context: context.clone(),
                plugin,
                service,
                error: error.clone(),
            };
            match state
                .cleanups
                .protocol
                .enqueue_native_child(self.group, request)
            {
                Ok((slot, _token)) => ChildHandle {
                    state: ChildState::Native { slot, error },
                    external: None,
                },
                Err(rejected) => {
                    drop(state);
                    drop(rejected);
                    return Err("child request admission is closed or exhausted".into());
                }
            }
        } else {
            let identity = ChildState::External(Arc::new(Mutex::new(Ok(None))));
            let external = state.dynamic_host.as_ref().map(|notify| {
                static_host::StaticChildControl::new(
                    self.owner,
                    self.generation,
                    identity.clone(),
                    service.clone(),
                    notify.clone(),
                )
            });
            let handle = ChildHandle {
                state: identity,
                external,
            };
            let request = ChildDispatch::External(ExternalChildRequest {
                context: context.clone(),
                plugin,
                handle: handle.clone(),
            });
            if let Err(rejected) = state.cleanups.protocol.enqueue_owned_child(
                self.group,
                request,
                CleanupAction::External(handle.clone()),
            ) {
                drop(state);
                drop(rejected);
                return Err("child request admission is closed or exhausted".into());
            }
            handle
        };
        if let Some(control) = &handle.external {
            state.external_children.push(control.clone());
        }
        let notify = state.dynamic_host.clone();
        let waker = state.driver.take();
        drop(state);
        if let Some(notify) = notify {
            notify();
        }
        if let Some(waker) = waker {
            waker.wake();
        }
        Ok(handle)
    }
    pub fn effect(&self, effect: impl EffectIterator) -> Result<EffectHandle, CallbackError> {
        self.require_dynamic("effect")?;
        let mut state = lock(&self.state);
        Self::check_live(&state)?;
        if state.phase() == EpisodePhase::Restoring
            || !state.cleanups.protocol.accepts_acquisition(self.group)
        {
            return Err(CANCELLED.into());
        }
        if !state.cleanups.contains(self.group) {
            return Err("effect group has completed".into());
        }
        let handle = EffectHandle {
            status: Arc::new(Mutex::new(EffectStatus::default())),
        };
        let payload = GroupState {
            iterator: Some(Box::new(effect)),
            running: None,
            handle: handle.clone(),
        };
        if let Err(rejected) = state.cleanups.protocol.enqueue_effect(
            self.group,
            fresh(&NEXT_CLEANUP),
            self.bindings.clone(),
            payload,
        ) {
            drop(state);
            drop(rejected);
            return Err("effect request admission is closed or exhausted".into());
        }
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
    pub fn errors(&self) -> Vec<CallbackError> {
        self.status.errors()
    }
    pub fn get(&self) -> Result<Arc<T>, CallbackError> {
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
        let notify = status.notify.clone();
        drop(status);
        drop(previous);
        if let Some(notify) = notify {
            notify();
        }
        if let Some(driver) = driver {
            driver.wake();
        }
        Ok(())
    }
    pub fn refresh(&self) {
        let (driver, notify) = {
            let mut status = lock(&self.status.status);
            (status.driver.take(), status.notify.clone())
        };
        if let Some(notify) = notify {
            notify();
        }
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
    #[track_caller]
    pub fn get<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
    ) -> Result<Arc<T>, ServiceReadError> {
        self.inner.get(key)
    }
    /// Read the same committed binding as `get`, with an explicit required-read name.
    #[track_caller]
    pub fn require<T: Any + Send + Sync>(
        &self,
        key: ServiceKey<T>,
    ) -> Result<Arc<T>, ServiceReadError> {
        self.inner.require(key)
    }
    pub fn provide<T: Any + Send + Sync>(
        &mut self,
        key: ServiceKey<T>,
        value: T,
    ) -> Result<Arc<T>, CallbackError> {
        self.inner.provide(key, value)
    }
    pub fn provide_checked<T: Any + Send + Sync>(
        &mut self,
        key: ServiceKey<T>,
        value: T,
        check: impl Fn(&T, &Context, &serde_json::Value) -> bool + Send + Sync + 'static,
    ) -> Result<Arc<T>, CallbackError> {
        self.inner.provide_checked(key, value, check)
    }
    pub fn publish<T: Any + Send + Sync>(
        &mut self,
        key: ServiceKey<T>,
        value: T,
    ) -> Result<ServiceHandle<T>, CallbackError> {
        self.inner.publish(key, value)
    }
    pub fn publish_checked<T: Any + Send + Sync>(
        &mut self,
        key: ServiceKey<T>,
        value: T,
        check: impl Fn(&T, &Context, &serde_json::Value) -> bool + Send + Sync + 'static,
    ) -> Result<ServiceHandle<T>, CallbackError> {
        self.inner.publish_checked(key, value, check)
    }
    pub fn refresh(&self) -> CallbackResult {
        self.inner.refresh()
    }
    pub fn update_reversible(
        &mut self,
        key: ServiceKey<ReversibleValue>,
        operation: ValueOperation,
    ) -> Result<ValueOutcome, CallbackError> {
        self.inner.update_reversible(key, operation)
    }
    pub fn run_value_program(
        &mut self,
        key: ServiceKey<ReversibleValue>,
        program: &ValueProgram,
    ) -> Result<Vec<ValueOutcome>, CallbackError> {
        self.inner.run_value_program(key, program)
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
    pub fn on_cleanup_retryable(
        &mut self,
        cleanup: impl FnMut() -> CallbackResult + Send + 'static,
    ) {
        self.inner
            .on_cleanup_retryable(cleanup)
            .expect("live synchronous setup");
    }
    pub fn on_cleanup_retryable_async<F, Fut>(&mut self, cleanup: F)
    where
        F: FnMut() -> Fut + Send + 'static,
        Fut: Future<Output = CallbackResult> + Send + 'static,
    {
        self.inner
            .on_cleanup_retryable_async(cleanup)
            .expect("live synchronous setup");
    }
    pub fn mount(&mut self, plugin: Plugin) -> Result<ChildHandle, CallbackError> {
        self.inner.mount(plugin)
    }
    pub fn mount_in(
        &mut self,
        context: &Context,
        plugin: Plugin,
    ) -> Result<ChildHandle, CallbackError> {
        self.inner.mount_in(context, plugin)
    }
    pub fn effect(&mut self, effect: impl EffectIterator) -> Result<EffectHandle, CallbackError> {
        self.inner.effect(effect)
    }
}

struct GroupState {
    iterator: Option<Box<dyn EffectIterator>>,
    running: Option<RunningCleanup>,
    handle: EffectHandle,
}

/// Only a queued future may be discarded on withdrawal. Once its first poll
/// begins, the runtime owns it until it lands and can register its inverse.
type RootFuture = Pin<Box<dyn Future<Output = WorkReceipt<CallbackResult>> + Send>>;
enum RootSetup {
    Dormant,
    Queued(WorkTicket, RootFuture),
    Running(WorkTicket, RootFuture),
    Done,
}
impl RootSetup {
    fn is_pending(&self) -> bool {
        matches!(self, Self::Queued(..) | Self::Running(..))
    }
    fn is_done(&self) -> bool {
        matches!(self, Self::Done)
    }
    fn poll(
        &mut self,
        withdrawing: bool,
        episode: &AsyncSetup,
        cx: &mut TaskContext<'_>,
    ) -> Option<Poll<CallbackResult>> {
        match std::mem::replace(self, Self::Done) {
            Self::Queued(ticket, future) if withdrawing => {
                {
                    let mut state = lock(&episode.state);
                    state.cleanups.protocol.withdraw();
                    assert!(
                        state.cleanups.protocol.cancel_queued_root(ticket),
                        "only an unpolled root is discarded"
                    );
                }
                drop(future);
                None
            }
            Self::Queued(ticket, mut future) | Self::Running(ticket, mut future) => {
                assert!(
                    lock(&episode.state).cleanups.protocol.start_root(ticket),
                    "exact admitted root"
                );
                Some(
                    match normalize_poll(poll_catching_unwind(future.as_mut(), cx), |panic| {
                        CallbackError::panic(panic_message(panic))
                    }) {
                        Poll::Pending => {
                            *self = Self::Running(ticket, future);
                            Poll::Pending
                        }
                        Poll::Ready(Ok(receipt)) => {
                            let completed = lock(&episode.state)
                                .cleanups
                                .protocol
                                .complete_root(receipt);
                            Poll::Ready(completed.ok().expect("actual root completion"))
                        }
                        Poll::Ready(Err(error)) => {
                            let failed = lock(&episode.state)
                                .cleanups
                                .protocol
                                .fail_root(ticket, error);
                            Poll::Ready(Err(failed.expect("exact failed root")))
                        }
                    },
                )
            }
            state => {
                *self = state;
                None
            }
        }
    }
}
fn initialize_callback(
    callback: &mut Callback,
    episode: &AsyncSetup,
) -> Result<RootSetup, CallbackError> {
    let item = lock(&episode.state)
        .cleanups
        .protocol
        .issue_root(episode.clone())
        .ok()
        .expect("one root invocation per episode");
    let ticket = item.ticket();
    let result = catch_unwind(AssertUnwindSafe(|| item.run(callback)));
    initialize_reply(episode, ticket, result)
}
fn initialize_reply(
    episode: &AsyncSetup,
    ticket: WorkTicket,
    result: std::thread::Result<WorkReceipt<RootReply>>,
) -> Result<RootSetup, CallbackError> {
    match result {
        Ok(reply) => match reply.dispatch() {
            RootDispatch::Ready(receipt) => {
                let completed = lock(&episode.state)
                    .cleanups
                    .protocol
                    .complete_root(receipt);
                completed.ok().expect("actual synchronous root result")?;
                Ok(RootSetup::Done)
            }
            RootDispatch::Pending(pending) => {
                Ok(RootSetup::Queued(ticket, Box::pin(pending.complete())))
            }
        },
        Err(panic) => {
            let error = CallbackError::panic(panic_message(panic));
            Err(lock(&episode.state)
                .cleanups
                .protocol
                .fail_root(ticket, error)
                .expect("issued factory failed"))
        }
    }
}
type CompletionFuture =
    Pin<Box<dyn Future<Output = Completion<RestoreTicket, CallbackResult>> + Send>>;
enum CleanupReply {
    Awaited(Completion<RestoreTicket, CallbackResult>),
    Failed(RestoreTicket, CallbackError),
}
enum RejectedCleanup {
    Awaited(
        Completion<RestoreTicket, CallbackResult>,
        Option<CleanupAction>,
    ),
    Failed(RestoreTicket, CallbackError, Option<CleanupAction>),
}
impl RejectedCleanup {
    fn discard(self) {
        match self {
            Self::Awaited(completion, retry) => drop((completion, retry)),
            Self::Failed(ticket, error, retry) => drop((ticket, error, retry)),
        }
    }
}
struct RunningCleanup {
    ticket: RestoreTicket,
    future: CompletionFuture,
    retry: Option<RetryCleanup>,
}
struct CleanupFailure {
    ticket: RestoreTicket,
    message: CallbackError,
    retry: Option<RetryCleanup>,
}
fn initialize_cleanup(
    ticket: RestoreTicket,
    cleanup: CleanupCallback,
) -> Result<RunningCleanup, CleanupFailure> {
    let (result, retry) = match cleanup {
        CleanupCallback::Once(cleanup) => (
            catch_unwind(AssertUnwindSafe(|| {
                invoke_future(ticket, (), |()| cleanup())
            })),
            None,
        ),
        CleanupCallback::Retryable(mut cleanup) => {
            let result = catch_unwind(AssertUnwindSafe(|| {
                invoke_future(ticket, (), |()| cleanup())
            }));
            (result, Some(cleanup))
        }
    };
    match result {
        Ok(future) => Ok(RunningCleanup {
            ticket,
            future: Box::pin(future.complete()),
            retry,
        }),
        Err(panic) => Err(CleanupFailure {
            ticket,
            retry,
            message: CallbackError::panic(panic_message(panic)),
        }),
    }
}
fn poll_cleanup_callback(
    attempt: &mut RunningCleanup,
    cx: &mut TaskContext<'_>,
) -> Poll<CleanupReply> {
    match normalize_poll(poll_catching_unwind(attempt.future.as_mut(), cx), |panic| {
        CallbackError::panic(panic_message(panic))
    }) {
        Poll::Pending => Poll::Pending,
        Poll::Ready(Ok(completion)) => Poll::Ready(CleanupReply::Awaited(completion)),
        Poll::Ready(Err(error)) => Poll::Ready(CleanupReply::Failed(attempt.ticket, error)),
    }
}

struct Mounted {
    next_config_update: Option<Option<ConfigUpdateCallback>>,
    service: Option<EffectHandle>,
    injection_config: BTreeMap<u64, serde_json::Value>,
    config_update: Option<ConfigUpdateCallback>,
    declared_dependencies: Vec<u64>,
    declared_injection_config: BTreeMap<u64, serde_json::Value>,
    name: String,
    context: Context,
    episode: Option<AsyncSetup>,
    root_setup: RootSetup,
    root_running: Option<RunningCleanup>,
    cleanup_failure: Option<CallbackError>,
    failed: Option<CallbackError>,
    restart: bool,
    // Children externally mounted while inactive become owner-bound on begin.
    owned: Vec<ChildIdentity>,
}
impl Mounted {
    fn pending_effects(&self) -> Vec<usize> {
        self.episode
            .as_ref()
            .map(|episode| {
                lock(&episode.state)
                    .cleanups
                    .protocol
                    .effects()
                    .iter()
                    .filter(|(_, group)| group.get().iterator.is_some())
                    .map(|(&id, _)| id)
                    .collect()
            })
            .unwrap_or_default()
    }
    fn running_effects(&self) -> bool {
        self.episode.as_ref().is_some_and(|episode| {
            lock(&episode.state)
                .cleanups
                .protocol
                .effects()
                .values()
                .any(|group| group.get().running.is_some())
        })
    }
    fn initialized_effects(&self) -> bool {
        self.episode.as_ref().is_none_or(|episode| {
            lock(&episode.state)
                .cleanups
                .protocol
                .effects()
                .values()
                .all(|group| group.get().iterator.is_none())
        })
    }
    fn idle_effects(&self) -> bool {
        self.episode.as_ref().is_none_or(|episode| {
            lock(&episode.state)
                .cleanups
                .protocol
                .effects()
                .values()
                .all(|group| group.get().iterator.is_none() && group.get().running.is_none())
        })
    }
    fn settled_effects(&self) -> bool {
        self.episode.as_ref().is_none_or(|episode| {
            lock(&episode.state)
                .cleanups
                .protocol
                .effects()
                .values()
                .all(|group| {
                    group.get().iterator.is_none() && !lock(&group.get().handle.status).cancelled
                })
        })
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeError {
    Kernel(String),
    UnknownPlugin(PluginId),
    Retired(PluginId),
    UnloadingOwner(PluginId),
    InactiveOwner(PluginId),
    IncompatibleUpdate(PluginId),
    DependencyConflict {
        key: u64,
        service: &'static str,
    },
    Setup {
        plugin: PluginId,
        error: CallbackError,
    },
    Cleanup {
        plugin: PluginId,
        error: CallbackError,
    },
    Stalled,
}
impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Kernel(message) => write!(f, "kernel rejected operation: {message}"),
            Self::UnknownPlugin(id) => write!(f, "unknown plugin {id}"),
            Self::Retired(id) => write!(f, "plugin {id} is retired"),
            Self::UnloadingOwner(id) => write!(f, "plugin {id} is unloading"),
            Self::InactiveOwner(id) => write!(f, "plugin {id} has no active episode"),
            Self::DependencyConflict { key, service } => write!(
                f,
                "conflicting availability inputs for service {service} (key {key})"
            ),
            Self::IncompatibleUpdate(id) => write!(
                f,
                "plugin {id} update changed service declarations or injection configuration"
            ),
            Self::Setup { plugin, error } => write!(f, "plugin {plugin} setup failed: {error}"),
            Self::Cleanup { plugin, error } => write!(f, "plugin {plugin} cleanup failed: {error}"),
            Self::Stalled => f.write_str("runtime cannot make progress"),
        }
    }
}
impl std::error::Error for RuntimeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Setup { error, .. } | Self::Cleanup { error, .. } => Some(error),
            _ => None,
        }
    }
}
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
    kernel: NativeDriver<Callback, Mounted, ServiceSlot>,
    cleanup_errors: Vec<RuntimeError>,
    maintenance_changes: usize,
    shutdown_failures: Option<BTreeMap<PluginId, CallbackError>>,
}
impl Default for Runtime {
    fn default() -> Self {
        Self::new()
    }
}
impl Runtime {
    pub fn new() -> Self {
        let kernel = NativeDriver::new().expect("lifecycle domain identity exhausted");
        Self {
            kernel,
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
            registered_plugins: self.kernel.len(),
            identity_slots: self.kernel.identity_slots(),
            declaration_records: self.kernel.declaration_records(),
            binding_records: self.kernel.binding_records(),
            live_bindings: self
                .kernel
                .ids()
                .iter()
                .map(|id| self.committed(*id).len())
                .sum(),
            published_values: self.kernel.value_count(),
        }
    }
    /// Inspect blocked initialization/restoration without polling user code or
    /// cloning service payloads. Snapshot order is stable by plugin identity.
    pub fn snapshot(&self) -> RuntimeSnapshot {
        let mut plugins = Vec::new();
        for id in self.kernel.ids() {
            let owner = self.kernel.host(id).unwrap();
            let registration = self.kernel.registration(id).unwrap();
            let phase = self.phase(id).expect("registered mounted plugin");
            let target = self.kernel.target(id);
            let committed = self.committed(id);
            let mut blockers = Vec::new();
            if let Some(message) = &owner.failed {
                blockers.push(Blocker::Failed(message.to_string()));
            }
            if phase == Phase::Inactive && !self.retired(id) {
                let missing: Vec<_> = registration
                    .dependencies()
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
            let groups = owner.pending_effects();
            if !groups.is_empty() {
                blockers.push(Blocker::EffectsPending(groups));
            }
            if phase == Phase::Unloading {
                let consumers: Vec<_> = self
                    .kernel
                    .ids()
                    .iter()
                    .copied()
                    .filter(|consumer| self.committed(*consumer).iter().any(|b| b.provider == id))
                    .collect();
                if !consumers.is_empty() {
                    blockers.push(Blocker::CommittedConsumers(consumers));
                }
            }
            if let Some(message) = &owner.cleanup_failure {
                blockers.push(Blocker::CleanupFailed(message.to_string()));
            }
            if self.cleanup_started(id) || owner.root_running.is_some() || owner.running_effects() {
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
                parent: registration.parent(),
                phase,
                retired: self.retired(id),
                restoring: self.cleanup_started(id),
                dependencies: registration.dependencies().to_vec(),
                provisions: registration.provisions().to_vec(),
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
        self.mount_inner(context, parent, plugin, true, None)
            .map(|(id, _)| id)
    }
    fn mount_inner(
        &mut self,
        context: &Context,
        parent: Option<PluginId>,
        plugin: Plugin,
        register_inverse: bool,
        child_slot: Option<&SharedChild>,
    ) -> Result<(PluginId, Option<ChildIdentity>), RuntimeError> {
        plugin.validate()?;
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
        let declared_dependencies = plugin.dependencies.clone();
        let declared_injection_config = plugin.injection_config.clone();
        let mut injection_config = parent
            .map(|parent| self.kernel.host(parent).unwrap().injection_config.clone())
            .unwrap_or_default();
        injection_config.extend(plugin.injection_config);
        let anchor = Port {
            key: fresh(&NEXT_KEY),
            realm: 0,
        };
        let definition =
            PluginDefinition::new(plugin.dependencies, plugin.provisions, plugin.setup);
        // Only the checked allocator can resolve a native shared Child slot.
        // Return rejected recipes out of its mutex before dropping captures.
        let host = Mounted {
            next_config_update: None,
            service: None,
            injection_config,
            config_update: plugin.config_update,
            declared_dependencies,
            declared_injection_config,
            name: plugin.name,
            context: context.clone(),
            episode: None,
            root_setup: RootSetup::Dormant,
            root_running: None,
            cleanup_failure: None,
            failed: None,
            restart: false,
            owned: Vec::new(),
        };
        let registered = if let Some(shared) = child_slot {
            if parent == Some(shared.parent_id()) {
                self.kernel
                    .register_shared_child(shared, &context.realms, anchor, definition, host)
            } else {
                Err((KernelError::InvalidState, definition, host))
            }
        } else {
            self.kernel
                .register_plugin(parent, &context.realms, anchor, definition, host)
        };
        let id = registered.map_err(|(error, _, _)| kernel_error(error))?;
        let child = self.kernel.registration(id).unwrap().child_identity();
        if register_inverse {
            if let Some(parent) = parent {
                let owner = self.kernel.host_mut(parent).unwrap();
                if let Some(episode) = &owner.episode {
                    lock(&episode.state).cleanups.push(
                        0,
                        CleanupAction::Native(
                            SharedChild::from_identity(child.expect("registered child")).0,
                        ),
                    );
                } else {
                    owner.owned.push(child.expect("registered child"));
                }
            }
        }
        Ok((id, child))
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
        self.kernel.host(id).map(|p| p.name.as_str())
    }
    pub fn context(&self, id: PluginId) -> Option<&Context> {
        self.kernel.host(id).map(|p| &p.context)
    }
    pub fn failure(&self, id: PluginId) -> Option<&str> {
        self.setup_error(id).map(CallbackError::message)
    }
    pub fn setup_error(&self, id: PluginId) -> Option<&CallbackError> {
        self.kernel.host(id)?.failed.as_ref()
    }
    pub fn cleanup_error(&self, id: PluginId) -> Option<&CallbackError> {
        self.kernel.host(id)?.cleanup_failure.as_ref()
    }
    pub fn committed(&self, id: PluginId) -> Vec<Binding> {
        self.kernel.committed(id)
    }
    /// The retained failure that requires explicit cleanup retry. Historical
    /// attempt errors remain available through take_cleanup_errors().
    pub fn cleanup_failure(&self, id: PluginId) -> Option<&str> {
        self.cleanup_error(id).map(CallbackError::message)
    }
    /// Admit a fresh whole-episode attempt only after the previous callbacks
    /// settle and its Failed receipt is recorded. No user callback runs here.
    pub fn retry_cleanup(&mut self, id: PluginId) -> Result<(), RuntimeError> {
        let owner = self
            .kernel
            .host(id)
            .ok_or(RuntimeError::UnknownPlugin(id))?;
        if owner.cleanup_failure.is_none()
            || !owner.root_setup.is_done()
            || owner.root_running.is_some()
            || !owner.idle_effects()
        {
            return Err(RuntimeError::Cleanup {
                plugin: id,
                error: "cleanup attempt is still running or has no retained failure".into(),
            });
        }
        let episode = owner
            .episode
            .as_ref()
            .ok_or(RuntimeError::InactiveOwner(id))?
            .clone();
        let mut state = lock(&episode.state);
        if !state.cleanups.protocol.can_retry_all() {
            return Err(RuntimeError::Cleanup {
                plugin: id,
                error: "retained cleanup cannot be retried".into(),
            });
        }
        self.kernel
            .retry_managed_execution(id, &mut state.cleanups.protocol)
            .map_err(kernel_error)?;
        self.kernel.host_mut(id).unwrap().cleanup_failure = None;
        let wake = state.driver.take();
        drop(state);
        if let Some(wake) = wake {
            wake.wake();
        }
        Ok(())
    }
    /// Identity of the current activation, for rejecting stale update plans.
    pub fn episode_generation(&self, id: PluginId) -> Option<u64> {
        self.kernel
            .host(id)?
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
        let slot = self.kernel.native_value(port)?;
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
        self.kernel
            .host(id)
            .unwrap()
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
                error: message,
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
                error: message,
            })
    }
    pub fn on_cleanup_retryable(
        &mut self,
        id: PluginId,
        cleanup: impl FnMut() -> CallbackResult + Send + 'static,
    ) -> Result<(), RuntimeError> {
        self.owner_context(id)?
            .on_cleanup_retryable(cleanup)
            .map_err(|message| RuntimeError::Setup {
                plugin: id,
                error: message,
            })
    }
    pub fn on_cleanup_retryable_async<F, Fut>(
        &mut self,
        id: PluginId,
        cleanup: F,
    ) -> Result<(), RuntimeError>
    where
        F: FnMut() -> Fut + Send + 'static,
        Fut: Future<Output = CallbackResult> + Send + 'static,
    {
        self.owner_context(id)?
            .on_cleanup_retryable_async(cleanup)
            .map_err(|message| RuntimeError::Setup {
                plugin: id,
                error: message,
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
                error: message,
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
                error: message,
            })?;
        Ok(())
    }
    /// Idempotent retirement. Children retire at their owned inverse, except a
    /// child relying on this owner's service must depart first to release it.
    pub fn dispose(&mut self, id: PluginId) -> Result<(), RuntimeError> {
        if !self.contains(id) {
            return Ok(());
        }
        if let Some(episode) = self.kernel.host(id).unwrap().episode.clone() {
            self.kernel
                .withdraw_managed_execution(id, &mut lock(&episode.state).cleanups.protocol, true)
                .map_err(kernel_error)?;
        } else {
            self.kernel.retire(id).map_err(kernel_error)?;
        }
        self.after_retirement(id)
    }
    fn after_retirement(&mut self, id: PluginId) -> Result<(), RuntimeError> {
        if let Some(service) = &self.kernel.host(id).unwrap().service {
            lock(&service.status).cancelled = true;
        }
        if let Some(episode) = &self.kernel.host(id).unwrap().episode {
            lock(&episode.state).withdraw();
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
                self.kernel
                    .ids()
                    .into_iter()
                    .filter_map(|id| {
                        self.kernel
                            .host(id)
                            .unwrap()
                            .failed
                            .clone()
                            .map(|message| (id, message))
                    })
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
            .map(|(plugin, message)| RuntimeError::Setup {
                plugin,
                error: message,
            })
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
        let restart = self.kernel.phase(id) != Some(Phase::Inactive);
        let plugin = self
            .kernel
            .host_mut(id)
            .ok_or(RuntimeError::UnknownPlugin(id))?;
        plugin.failed = None;
        plugin.restart = restart;
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
        if !self.contains(id) {
            return Err(RuntimeError::UnknownPlugin(id));
        }
        let previous = self
            .kernel
            .replace(id, sync_recipe(setup))
            .map_err(|(error, _)| kernel_error(error))?;
        drop(previous);
        self.restart(id)
    }
    pub fn update_async<F, Fut>(&mut self, id: PluginId, setup: F) -> Result<(), RuntimeError>
    where
        F: FnMut(AsyncSetup) -> Fut + Send + 'static,
        Fut: Future<Output = CallbackResult> + Send + 'static,
    {
        if self.kernel.retired(id) {
            return Err(RuntimeError::Retired(id));
        }
        if !self.contains(id) {
            return Err(RuntimeError::UnknownPlugin(id));
        }
        let previous = self
            .kernel
            .replace(id, async_recipe(setup))
            .map_err(|(error, _)| kernel_error(error))?;
        drop(previous);
        self.restart(id)
    }
    /// Replace a plugin recipe and restart with unchanged dependency/provision
    /// declarations and injection configuration. Validation precedes mutation.
    /// To change declarations, dispose and mount a new plugin instead.
    pub fn update_plugin(&mut self, id: PluginId, plugin: Plugin) -> Result<(), RuntimeError> {
        plugin.validate()?;
        if self.retired(id) {
            return Err(RuntimeError::Retired(id));
        }
        if !self.contains(id) {
            return Err(RuntimeError::UnknownPlugin(id));
        }
        if !self.config_recipe_compatible(id, &plugin) {
            return Err(RuntimeError::IncompatibleUpdate(id));
        }
        let previous = self
            .kernel
            .replace(id, plugin.setup)
            .map_err(|(error, _)| kernel_error(error))?;
        let mounted = self.kernel.host_mut(id).unwrap();
        mounted.name = plugin.name;
        drop(previous);
        mounted.next_config_update = Some(plugin.config_update);
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
        let Some(handler) = self.kernel.host_mut(id).unwrap().config_update.as_mut() else {
            return Ok(crate::config::ConfigUpdate::Restart);
        };
        catch_unwind(AssertUnwindSafe(|| handler(context, previous, next)))
            .unwrap_or_else(|panic| Err(CallbackError::panic(panic_message(panic))))
            .map_err(|message| RuntimeError::Setup {
                plugin: id,
                error: message,
            })
    }
    pub(crate) fn config_recipe_compatible(&self, id: PluginId, plugin: &Plugin) -> bool {
        if plugin.validate().is_err() {
            return false;
        }
        let Some(mounted) = self.kernel.host(id) else {
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
            && self.kernel.registration(id).unwrap().provisions() == provisions
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
                    error: "in-place update changed service declarations".into(),
                });
            }
        }
        let mut counts = BTreeMap::<PluginId, u64>::new();
        for (id, _) in &recipes {
            let count = counts.entry(*id).or_default();
            *count = count
                .checked_add(1)
                .ok_or_else(|| kernel_error(KernelError::Capacity))?;
        }
        for (id, count) in counts {
            if !self
                .kernel
                .registration(id)
                .unwrap()
                .can_replace_count(count)
            {
                return Err(kernel_error(KernelError::Capacity));
            }
        }
        let mut previous = Vec::new();
        for (id, plugin) in recipes {
            let setup = self
                .kernel
                .replace(id, plugin.setup)
                .ok()
                .expect("preflighted recipe revisions");
            let mounted = self.kernel.host_mut(id).unwrap();
            mounted.name = plugin.name;
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
            .kernel
            .host(id)
            .ok_or(RuntimeError::UnknownPlugin(id))?;
        let context = old.context.clone();
        let parent = self.kernel.registration(id).unwrap().parent();
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
        let plugin = &self.kernel.host(id).unwrap();
        bindings.iter().all(|binding| {
            // Anchors carry lifecycle identity, not user service values.
            if self
                .kernel
                .registration(binding.provider)
                .is_some_and(|provider| provider.anchor().key == binding.key)
            {
                return true;
            }
            self.kernel
                .native_value(Port {
                    key: binding.key,
                    realm: binding.realm,
                })
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
        self.kernel
            .coherent(id, self.kernel.host(id).unwrap().restart)
    }
    fn decision(&self, id: PluginId) -> Option<Decision> {
        let plugin = &self.kernel.host(id).unwrap();
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
                failed: plugin.failed.is_some() || plugin.cleanup_failure.is_some(),
                restart: plugin.restart,
            },
        )
    }
    fn leave(&mut self, id: PluginId) -> Result<(), RuntimeError> {
        if let Some(episode) = self.kernel.host(id).unwrap().episode.clone() {
            self.kernel
                .withdraw_managed_execution(id, &mut lock(&episode.state).cleanups.protocol, false)
                .map_err(kernel_error)?;
        } else {
            self.kernel.leave(id).map_err(kernel_error)?;
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
        while let Some(parent) = self
            .kernel
            .registration(child)
            .and_then(|registration| registration.parent())
        {
            if parent == owner {
                return true;
            }
            child = parent;
        }
        false
    }
    fn latch(&mut self, id: PluginId, message: CallbackError) {
        if let Some(failures) = &mut self.shutdown_failures {
            failures.entry(id).or_insert_with(|| message.clone());
        }
        if self.kernel.host(id).unwrap().failed.is_none() {
            self.kernel.host_mut(id).unwrap().failed = Some(message);
        }
    }
    fn start(&mut self, id: PluginId, cx: &mut TaskContext<'_>, protocol: EpisodeExecution) {
        let bindings = self.kernel.committed(id);
        let registration = self.kernel.registration(id).unwrap();
        let provisions = registration.provisions().to_vec();
        let anchor = registration.anchor();
        let plugin = self.kernel.host_mut(id).unwrap();
        if let Some(handler) = plugin.next_config_update.take() {
            plugin.config_update = handler;
        }
        let cleanups = Cleanups { protocol };
        let mut state = Episode {
            // Retain precisely the committed dependencies until restoration
            // finishes; unrelated services must not gain implicit Arc owners.
            values: EpisodeValues::default(),
            cleanups,
            driver: Some(cx.waker().clone()),
            static_only: false,
            dynamic_host: None,
            external_children: Vec::new(),
            service_updates: None,
            unsupported: None,
        };
        for child in plugin.owned.drain(..) {
            state.cleanups.push(
                0,
                CleanupAction::Native(SharedChild::from_identity(child).0),
            );
        }
        let episode = AsyncSetup {
            generation: fresh(&NEXT_EPISODE),
            owner: id,
            context: plugin.context.clone(),
            bindings,
            provisions,
            anchor,
            state: Arc::new(Mutex::new(state)),
            group: 0,
        };
        plugin.cleanup_failure = None;
        plugin.episode = Some(episode.clone());
        plugin.root_setup = RootSetup::Done;
        let invocation = self
            .kernel
            .admit_managed_root(
                id,
                &mut lock(&episode.state).cleanups.protocol,
                episode.clone(),
            )
            .ok()
            .expect("registered recipe and admitted episode");
        let ticket = invocation.ticket();
        let result = catch_unwind(AssertUnwindSafe(|| {
            self.kernel
                .call_root(id, invocation)
                .ok()
                .expect("unchanged registered recipe")
        }));
        match initialize_reply(&episode, ticket, result) {
            Ok(root) => self.kernel.host_mut(id).unwrap().root_setup = root,
            Err(message) => self.latch(id, message),
        }
    }
    // A rejected dispatch returns its actual iterator payload without allocation.
    #[allow(clippy::result_large_err)]
    fn drain_requests(&mut self, id: PluginId) -> Result<bool, RuntimeError> {
        let Some(episode) = self.kernel.host(id).unwrap().episode.clone() else {
            return Ok(false);
        };
        let (children, groups) = {
            let state = lock(&episode.state);
            (
                state.cleanups.protocol.child_count(),
                state.cleanups.protocol.group_count(),
            )
        };
        // Bound this dispatch to the actual queued prefix. Reentrant admission
        // remains visible to the next scheduler pass and prevents publication.
        for _ in 0..children {
            let item = lock(&episode.state)
                .cleanups
                .protocol
                .take_child()
                .expect("queued child");
            let receipt = item.run(|request| self.apply_child_request(id, request));
            let completed = lock(&episode.state)
                .cleanups
                .protocol
                .complete_request(receipt);
            assert!(completed.is_ok(), "actual child dispatch completion");
        }
        for _ in 0..groups {
            let item = lock(&episode.state)
                .cleanups
                .protocol
                .take_group()
                .expect("queued group");
            let receipt = item.run(|request| {
                lock(&episode.state)
                    .cleanups
                    .protocol
                    .activate_effect(request)
            });
            let completed = lock(&episode.state)
                .cleanups
                .protocol
                .complete_request(receipt);
            assert!(
                completed
                    .ok()
                    .expect("actual group dispatch completion")
                    .is_ok(),
                "fresh owned effect identity"
            );
        }
        Ok(children != 0 || groups != 0)
    }
    fn apply_child_request(&mut self, id: PluginId, request: ChildRequest) {
        let ChildDispatch::Native(request) = request else {
            self.latch(id, "ExternalChildInNativeRuntime".into());
            return;
        };
        let (request, child_slot) = request.into_parts();
        if request
            .service
            .as_ref()
            .is_some_and(|service| lock(&service.status).cancelled)
        {
            if let Some(service) = &request.service {
                finish_service(service);
            }
            return;
        }
        let result = self.mount_inner(
            &request.context,
            Some(id),
            request.plugin,
            false,
            Some(&child_slot),
        );
        match result {
            Ok((child, _)) => {
                self.kernel.host_mut(child).unwrap().service = request.service;
            }
            Err(error) => {
                let message = CallbackError::new(error);
                {
                    let mut error = lock(&request.error);
                    if child_slot.reject().result {
                        *error = Some(message.to_string());
                    }
                }
                if let Some(service) = &request.service {
                    lock(&service.status).errors.push(message);
                    finish_service(service);
                } else {
                    self.latch(id, message);
                }
            }
        }
    }
    fn record_cleanup(
        &mut self,
        id: PluginId,
        group: Option<&EffectHandle>,
        message: CallbackError,
    ) {
        if let Some(handle) = group {
            lock(&handle.status).errors.push(message.clone());
        }
        self.cleanup_errors.push(RuntimeError::Cleanup {
            plugin: id,
            error: message,
        });
    }
    fn finish_callback(
        &mut self,
        id: PluginId,
        group: usize,
        handle: Option<&EffectHandle>,
        ticket: RestoreTicket,
        result: CallbackResult,
        retry: Option<RetryCleanup>,
    ) {
        let episode = self
            .kernel
            .host(id)
            .unwrap()
            .episode
            .as_ref()
            .unwrap()
            .clone();
        let completed = lock(&episode.state).cleanups.complete_result(
            group,
            ticket,
            result,
            retry,
            CleanupPolicy::DrainConsumed,
        );
        let report = match completed {
            Ok(report) => report,
            Err(rejected) => {
                drop(rejected);
                panic!("exact issued restoration receipt");
            }
        };
        // User factories leave the bookkeeping lock before they are dropped.
        drop(report.discarded);
        if let Err(message) = report.result {
            if report.outcome == RestoreOutcome::Failed {
                self.kernel
                    .host_mut(id)
                    .unwrap()
                    .cleanup_failure
                    .get_or_insert_with(|| message.clone());
            }
            self.record_cleanup(id, handle, message);
        }
    }
    fn finish_reply(
        &mut self,
        id: PluginId,
        group: usize,
        handle: Option<&EffectHandle>,
        reply: CleanupReply,
        retry: Option<RetryCleanup>,
    ) {
        let episode = self
            .kernel
            .host(id)
            .unwrap()
            .episode
            .as_ref()
            .unwrap()
            .clone();
        let completed = lock(&episode.state).cleanups.complete_reply(
            group,
            reply,
            retry,
            CleanupPolicy::DrainConsumed,
        );
        // Both discarded and rejected user payloads leave the bookkeeping lock.
        let report = match completed {
            Ok(report) => report,
            Err(rejected) => {
                rejected.discard();
                panic!("exact issued restoration receipt");
            }
        };
        drop(report.discarded);
        if let Err(message) = report.result {
            if report.outcome == RestoreOutcome::Failed {
                self.kernel
                    .host_mut(id)
                    .unwrap()
                    .cleanup_failure
                    .get_or_insert_with(|| message.clone());
            }
            self.record_cleanup(id, handle, message);
        }
    }
    fn finish_value(
        &mut self,
        id: PluginId,
        handle: Option<&EffectHandle>,
        completion: ValueCleanupReport<CleanupCallback, ChildHandle>,
    ) {
        if let Err(error) = completion.report.result {
            let message = value_error(error);
            self.kernel
                .host_mut(id)
                .unwrap()
                .cleanup_failure
                .get_or_insert_with(|| message.clone());
            self.record_cleanup(id, handle, message);
        }
    }
    // Independent groups can progress, but a failed retryable inverse blocks
    // every earlier inverse in its own group until an explicit retry.
    fn poll_cleanup(
        &mut self,
        id: PluginId,
        group: usize,
        running: &mut Option<RunningCleanup>,
        handle: Option<&EffectHandle>,
        cx: &mut TaskContext<'_>,
    ) -> (bool, bool) {
        let episode = self
            .kernel
            .host(id)
            .unwrap()
            .episode
            .as_ref()
            .unwrap()
            .clone();
        let mut progress = false;
        if running.is_none() {
            let action = lock(&episode.state).cleanups.pop(group);
            if let Some(dispatch) = action {
                progress = true;
                let (ticket, action) = match dispatch {
                    CleanupDispatch::Value { completion, .. } => {
                        self.finish_value(id, handle, completion);
                        return (true, false);
                    }
                    CleanupDispatch::Host { ticket, action } => (ticket, action),
                };
                match action {
                    CleanupAction::Value(_) => {
                        unreachable!("value inverse runs inside the checked dispatcher")
                    }
                    CleanupAction::Native(child) => {
                        let retired = self
                            .kernel
                            .retire_shared_child(&child)
                            .map_err(|error| CallbackError::new(kernel_error(error)));
                        let result = match retired {
                            Ok(Some(identity)) if self.contains(identity.id()) => self
                                .after_retirement(identity.id())
                                .map_err(CallbackError::new),
                            Ok(_) => Ok(()),
                            Err(error) => Err(error),
                        };
                        self.finish_callback(id, group, handle, ticket, result, None);
                    }
                    CleanupAction::External(_) => self.finish_callback(
                        id,
                        group,
                        handle,
                        ticket,
                        Err("ExternalChildInNativeRuntime".into()),
                        None,
                    ),
                    CleanupAction::Callback(cleanup) => match initialize_cleanup(ticket, cleanup) {
                        Ok(future) => *running = Some(future),
                        Err(failure) => self.finish_reply(
                            id,
                            group,
                            handle,
                            CleanupReply::Failed(failure.ticket, failure.message),
                            failure.retry,
                        ),
                    },
                }
            }
        }
        if let Some(attempt) = running.as_mut() {
            match poll_cleanup_callback(attempt, cx) {
                Poll::Pending => return (progress, true),
                Poll::Ready(result) => {
                    let attempt = running.take().unwrap();
                    self.finish_reply(id, group, handle, result, attempt.retry);
                    progress = true;
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
        let episode = self
            .kernel
            .host(id)
            .unwrap()
            .episode
            .as_ref()
            .unwrap()
            .clone();
        let keys: Vec<_> = lock(&episode.state)
            .cleanups
            .protocol
            .effects()
            .keys()
            .copied()
            .collect();
        for key in keys {
            // Another provider may have departed earlier in this same driver
            // pass. Recheck immediately before a fresh iterator stage.
            let can_start = matches!(self.phase(id), Some(Phase::Active | Phase::Loading))
                && self.coherent(id)
                && self.services_available(id)
                && self.kernel.host(id).unwrap().failed.is_none()
                && self.kernel.host(id).unwrap().cleanup_failure.is_none();
            let mut group = lock(&episode.state)
                .cleanups
                .protocol
                .take_effect(key)
                .unwrap();
            let driver = cx.waker().clone();
            let (cancelled, previous) = {
                let mut status = lock(&group.get().handle.status);
                let previous = status.driver.replace(driver);
                if unloading || !can_start {
                    status.cancelled = true;
                }
                (status.cancelled, previous)
            };
            drop(previous);
            if cancelled {
                let mut state = lock(
                    &self
                        .kernel
                        .host(id)
                        .unwrap()
                        .episode
                        .as_ref()
                        .unwrap()
                        .state,
                );
                // Completed iterators also pass through abstract Leave before
                // their accumulator is restored. In-flight cancellation still
                // keeps the delayed abstract Reloading state until landing.
                state.cleanups.protocol.cancel(group.id());
            }
            if group.get().iterator.is_some() {
                let mut setup = self
                    .kernel
                    .host(id)
                    .unwrap()
                    .episode
                    .as_ref()
                    .unwrap()
                    .clone();
                setup.group = group.id();
                let target = if can_start {
                    self.kernel.target(id)
                } else {
                    None
                };
                let admitted = {
                    let mut state = lock(&setup.state);
                    state
                        .cleanups
                        .protocol
                        .admit_effect(&mut group, target.as_deref())
                };
                if !admitted {
                    group.get_mut().iterator = None;
                    progress = true;
                } else {
                    let called = group.call((&mut *cx, &setup), |mut payload, (cx, setup)| {
                        let result = catch_unwind(AssertUnwindSafe(|| {
                            payload.iterator.as_mut().unwrap().poll_next(cx, setup)
                        }));
                        let result = normalize_effect_poll(
                            result,
                            |inverse: Inverse| CleanupAction::Callback(inverse.0),
                            |panic| CallbackError::panic(panic_message(panic)),
                        );
                        (payload, result)
                    });
                    let (returned, reply) = match called {
                        Ok(called) => called,
                        Err(_) => panic!("one actual call per admitted poll"),
                    };
                    group = returned;
                    let landed = lock(&setup.state)
                        .cleanups
                        .protocol
                        .land_effect(&mut group, reply);
                    let report = match landed {
                        Ok(report) => report,
                        Err(rejected) => {
                            drop(rejected);
                            panic!("actual reply for this admitted effect poll");
                        }
                    };
                    if let Some(report) = report {
                        if let Some(message) = report.error {
                            if !(cancelled && message.is_cancelled()) {
                                lock(&group.get().handle.status)
                                    .errors
                                    .push(message.clone());
                                self.latch(id, message);
                            }
                        }
                        if !report.continue_iteration {
                            group.get_mut().iterator = None;
                        }
                        progress = true;
                    } else {
                        pending = true;
                    }
                }
            }
            if group.get().iterator.is_none() {
                let mut status = lock(&group.get().handle.status);
                if !status.initialized {
                    status.initialized = true;
                    let wakers = std::mem::take(&mut status.wakers);
                    drop(status);
                    wake_waiters(wakers);
                }
            }
            if cancelled
                && group.get().iterator.is_none()
                && ((can_start && !unloading) || cleanup_allowed)
            {
                let group_id = group.id();
                let payload = group.get_mut();
                let (did, waiting) = self.poll_cleanup(
                    id,
                    group_id,
                    &mut payload.running,
                    Some(&payload.handle),
                    cx,
                );
                progress |= did;
                pending |= waiting;
                let episode = self
                    .kernel
                    .host(id)
                    .unwrap()
                    .episode
                    .as_ref()
                    .unwrap()
                    .clone();
                if group.get().running.is_none() {
                    let retired = lock(&episode.state).cleanups.protocol.retire_effect(group);
                    match retired {
                        Ok(payload) => {
                            // Removal consumes the actual checkout under the same
                            // lock as registration. Drop user payloads after unlocking.
                            let mut status = lock(&payload.handle.status);
                            status.finished = true;
                            let wakers = std::mem::take(&mut status.wakers);
                            drop(status);
                            wake_waiters(wakers);
                            progress = true;
                            continue;
                        }
                        Err(retained) => group = retained,
                    }
                }
            }
            let returned = lock(&episode.state).cleanups.protocol.put_effect(group);
            assert!(
                returned.is_ok(),
                "return the checked-out effect to its live queue"
            );
        }
        (progress, pending)
    }
    pub(crate) fn settled_result(&self, id: PluginId) -> Option<Result<(), RuntimeError>> {
        let Some(owner) = self.kernel.host(id) else {
            return Some(Ok(()));
        };
        let ready = matches!(self.phase(id), Some(Phase::Inactive | Phase::Active))
            && !self.retired(id)
            && !owner.restart
            && !owner.root_setup.is_pending()
            && owner.settled_effects()
            && owner
                .episode
                .as_ref()
                .is_none_or(|episode| lock(&episode.state).cleanups.protocol.group_count() == 0)
            && !self
                .kernel
                .children(id)
                .iter()
                .any(|child| self.retired(*child));
        if ready {
            return Some(match &owner.failed {
                Some(message) => Err(RuntimeError::Setup {
                    plugin: id,
                    error: message.clone(),
                }),
                None => Ok(()),
            });
        }
        None
    }
    pub(crate) fn poll_settle(
        &mut self,
        cx: &mut TaskContext<'_>,
    ) -> Poll<Result<(), RuntimeError>> {
        for _ in 0..1024 {
            if self.maintenance_changes >= 256 {
                self.compact();
            }
            let mut progress = false;
            let mut pending = false;
            // Dynamic service disposal is a normal verified provider retirement.
            for id in self.kernel.ids() {
                if let Some(service) = self.kernel.host(id).unwrap().service.clone() {
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
                let Some(episode) = self.kernel.host(id).unwrap().episode.clone() else {
                    continue;
                };
                let driver = cx.waker().clone();
                let previous = lock(&episode.state).driver.replace(driver);
                drop(previous);
                let root_poll = self.kernel.host_mut(id).unwrap().root_setup.poll(
                    phase == Phase::Unloading,
                    &episode,
                    cx,
                );
                match root_poll {
                    Some(Poll::Pending) => pending = true,
                    Some(Poll::Ready(result)) => {
                        progress = true;
                        if let Err(message) = result {
                            if !(phase == Phase::Unloading && message.is_cancelled()) {
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
                    && self.kernel.host(id).unwrap().root_setup.is_done()
                    && !self.kernel.cleanup_started(id)
                {
                    // Do not restore any resource while any group has a setup
                    // poll outstanding: it may still rely on that resource.
                    let state = lock(&episode.state);
                    if state.cleanups.protocol.is_idle() && !state.cleanups.protocol.has_pending() {
                        if let Err(error) = self
                            .kernel
                            .settle_managed_execution(id, &state.cleanups.protocol)
                        {
                            return Poll::Ready(Err(kernel_error(error)));
                        }
                        match self.kernel.begin_cleanup(id) {
                            Ok(()) => progress = true,
                            Err(KernelError::Relied) => {}
                            Err(error) => return Poll::Ready(Err(kernel_error(error))),
                        }
                    }
                }
                let cleanup_allowed = unloading
                    && self.kernel.cleanup_started(id)
                    && self.kernel.pending_action(id).is_some();
                let (did, waiting) = self.poll_groups(
                    id,
                    unloading || self.kernel.host(id).unwrap().failed.is_some(),
                    cleanup_allowed,
                    cx,
                );
                progress |= did;
                pending |= waiting;
                match self.drain_requests(id) {
                    Ok(did) => progress |= did,
                    Err(error) => return Poll::Ready(Err(error)),
                }
                if unloading
                    && cleanup_allowed
                    && self.kernel.host(id).unwrap().root_setup.is_done()
                {
                    let mut running = self.kernel.host_mut(id).unwrap().root_running.take();
                    let (did, waiting) = self.poll_cleanup(id, 0, &mut running, None, cx);
                    self.kernel.host_mut(id).unwrap().root_running = running;
                    progress |= did;
                    pending |= waiting;
                    let mut state = lock(&episode.state);
                    let retained_failure = state.cleanups.protocol.has_failed();
                    let callbacks_idle = self.kernel.host(id).unwrap().root_running.is_none()
                        && state.cleanups.protocol.effects().values().all(|group| {
                            group.get().running.is_none() && group.get().iterator.is_none()
                        });
                    if retained_failure && callbacks_idle {
                        if self.kernel.pending_action(id).is_some() {
                            if let Err(error) = self
                                .kernel
                                .fail_managed_execution(id, &state.cleanups.protocol)
                            {
                                return Poll::Ready(Err(kernel_error(error)));
                            }
                            progress = true;
                        }
                    } else if self.kernel.host(id).unwrap().root_running.is_none()
                        && state.cleanups.protocol.effects().is_empty()
                        && state.cleanups.protocol.is_idle()
                        && state.cleanups.protocol.can_seal()
                    {
                        let episode_values = match self
                            .kernel
                            .release_managed_execution(id, &mut state.cleanups.protocol)
                        {
                            Ok((_, released)) => released,
                            Err(error) => return Poll::Ready(Err(kernel_error(error))),
                        };
                        self.maintenance_changes += 1;
                        // Services commonly retain their setup context. Empty the
                        // closed episode to break value -> context -> value cycles,
                        // but only after all consumer inverses have completed.
                        drop(state);
                        let plugin = self.kernel.host_mut(id).unwrap();
                        plugin.episode = None;
                        plugin.root_setup = RootSetup::Dormant;
                        plugin.restart = false;
                        drop(episode_values);
                        progress = true;
                    }
                } else if phase == Phase::Loading
                    && self.kernel.host(id).unwrap().root_setup.is_done()
                    && self.kernel.host(id).unwrap().initialized_effects()
                    && self.kernel.host(id).unwrap().failed.is_none()
                {
                    let mut state = lock(&episode.state);
                    // Serialize the Loading -> Active boundary with registration
                    // through escaped contexts. Requests admitted during Loading
                    // are initialized before the service becomes observable.
                    if state.cleanups.protocol.group_count() != 0
                        || state.cleanups.protocol.child_count() != 0
                    {
                        progress = true;
                        continue;
                    }
                    let target = self.kernel.target(id);
                    if !target
                        .as_ref()
                        .is_some_and(|target| state.can_finish(target))
                    {
                        // The protocol rejects publication while any admitted
                        // stage remains outstanding or its target has drifted.
                        drop(state);
                        if let Err(error) = self.leave(id) {
                            return Poll::Ready(Err(error));
                        }
                        progress = true;
                        continue;
                    }
                    let missing = state
                        .cleanups
                        .protocol
                        .native()
                        .expect("native execution")
                        .missing();
                    if let Some(port) = missing {
                        drop(state);
                        self.latch(
                            id,
                            format!("declared service {} has no value", port.key).into(),
                        );
                        progress = true;
                    } else {
                        let finished = self
                            .kernel
                            .finish_managed_execution(id, &mut state.cleanups.protocol);
                        drop(state);
                        match finished {
                            Ok(()) => {
                                if let Some(service) = &self.kernel.host(id).unwrap().service {
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
                }
            }
            for id in self.kernel.ids().into_iter().rev() {
                if self.retired(id)
                    && self.phase(id) == Some(Phase::Inactive)
                    && self.decision(id) == Some(Decision::Remove)
                {
                    let removed = match self.kernel.remove(id) {
                        Ok(removed) => removed,
                        Err(error) => return Poll::Ready(Err(kernel_error(error))),
                    };
                    self.maintenance_changes += 1;
                    let (registration, host) = removed.into_parts();
                    if let Some(service) = &host.service {
                        finish_service(service);
                    }
                    drop((registration, host));
                    progress = true;
                }
            }
            for id in self.kernel.ids() {
                if self.phase(id) != Some(Phase::Inactive)
                    || self.decision(id) != Some(Decision::Begin)
                {
                    continue;
                }
                let execution = match self
                    .kernel
                    .begin_managed_execution(id, fresh(&NEXT_CLEANUP))
                {
                    Ok(owners) => owners,
                    Err(KernelError::MissingDependency) => continue,
                    Err(error) => return Poll::Ready(Err(kernel_error(error))),
                };
                self.start(id, cx, execution);
                progress = true;
            }
            if progress {
                continue;
            }
            if let Some(id) = self
                .kernel
                .ids()
                .into_iter()
                .find(|id| self.kernel.host(*id).unwrap().cleanup_failure.is_some())
            {
                return Poll::Ready(Err(RuntimeError::Cleanup {
                    plugin: id,
                    error: self
                        .kernel
                        .host(id)
                        .unwrap()
                        .cleanup_failure
                        .clone()
                        .unwrap(),
                }));
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
            if let Some(id) = self
                .kernel
                .ids()
                .into_iter()
                .find(|id| self.kernel.host(*id).unwrap().failed.is_some())
            {
                return Poll::Ready(Err(RuntimeError::Setup {
                    plugin: id,
                    error: self.kernel.host(id).unwrap().failed.clone().unwrap(),
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
        if let Some(result) = self.runtime.settled_result(id) {
            return Poll::Ready(result);
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
            let execution = runtime
                .kernel
                .begin_managed_execution(owner, fresh(&NEXT_CLEANUP))
                .unwrap();
            runtime.start(
                owner,
                &mut TaskContext::from_waker(Waker::noop()),
                execution,
            );
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
