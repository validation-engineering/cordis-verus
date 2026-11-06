//! A static typed plugin episode driven by an external, authoritative graph.
//!
//! This module never constructs a Runtime or Driver. The embedding host must
//! validate owner/generation, committed bindings and publication leases before
//! calling `begin`, and retain those leases until cleanup really succeeds.
//! Dynamic publication and child plugins require the explicit external child
//! protocol; effect groups and configuration updates remain unsupported. Checked declared services and episode-bound payload
//! updates require the explicit `begin_with_service_updates` host contract. Existing `Plugin`, `Setup`, slots and inverse
//! journals are used directly; arbitrary callbacks remain unverified host code.
//!
//! Keep one [`StaticPlugin`] per logical fiber and retain every [`StaticStart`]
//! until its setup future lands. Cancellation is cooperative: `cancel` closes
//! business admission but does not complete a running future. The external host
//! owns scheduling and must finish setup before requesting cleanup. Dropping an
//! unfinished future leaves a sticky failure instead of claiming restoration.
//! Cleanup keeps the selected token until acknowledgement. Retryable factories
//! survive reported errors/panics and require explicit retry. Consumed FnOnce
//! failures and abandoned futures stay sticky; both policies retain values and
//! earlier inverses, and reject a replacement episode until cleanup succeeds.
//!
//! [`TypedSlot`] clones share the original `Arc<T>`, and are not revocable
//! capabilities. The host must never expose them as a substitute for checking
//! current episode/publication authority. Static service values become visible
//! in the external graph only after setup succeeds and that graph commits them.
pub use super::child::StaticChildControl;
use super::*;
mod progress;
use progress::StaticProgress;

thread_local! {
    static CHILD_JOIN_GUARD: std::cell::RefCell<Option<std::collections::BTreeSet<PluginId>>> = const { std::cell::RefCell::new(None) };
}

/// Poll one externally scheduled action with its current forbidden wait targets.
/// The host computes these IDs from the action's actual caller/committed leases,
/// ownership and setup dependencies in the authoritative graph. Recompute them
/// before every poll: children may be allocated after the future first yields.
/// This synchronous, panic-safe scope does not survive a Pending result and does
/// not itself prove that the host supplied the complete set of wait dependencies.
/// A forbidden ServiceHandle join rejects without claiming child restoration.
/// Nested scopes use their own action's targets and restore the caller's scope.
pub fn with_child_join_guard<R>(
    blocked: &std::collections::BTreeSet<PluginId>,
    callback: impl FnOnce() -> R,
) -> R {
    struct Restore(Option<std::collections::BTreeSet<PluginId>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            CHILD_JOIN_GUARD.with(|current| {
                current.replace(self.0.take());
            });
        }
    }
    let previous = CHILD_JOIN_GUARD.with(|current| current.replace(Some(blocked.clone())));
    let _restore = Restore(previous);
    callback()
}

pub(super) fn child_join_blocked(id: PluginId) -> bool {
    CHILD_JOIN_GUARD.with(|current| {
        current
            .borrow()
            .as_ref()
            .is_some_and(|blocked| blocked.contains(&id))
    })
}

pub type StaticFuture = Pin<Box<dyn Future<Output = CallbackResult> + Send + 'static>>;

/// A shared typed slot, not a serialization of its value or a lifecycle lease.
#[derive(Clone)]
pub struct TypedSlot(SharedSlot);
impl TypedSlot {
    pub fn from_arc<T: Any + Send + Sync>(value: Arc<T>) -> Self {
        Self::from_erased(value)
    }
    pub fn from_erased(value: Arc<dyn Any + Send + Sync>) -> Self {
        Self(ServiceSlot::from_value(value, None))
    }
    pub fn get<T: Any + Send + Sync>(&self) -> Option<Arc<T>> {
        self.0.get()
    }
    pub fn has_check(&self) -> bool {
        self.0.metadata().check.is_some()
    }
    /// Evaluates a pure predicate without retaining a bookkeeping lock. Panics reject.
    pub fn accepts(&self, context: &Context, config: &serde_json::Value) -> bool {
        self.0.accepts(context, config)
    }
    pub fn value(&self) -> Arc<dyn Any + Send + Sync> {
        self.0
            .read_value()
            .expect("a live typed slot retains its payload until final release")
    }
}
#[derive(Clone)]
pub struct StaticBinding {
    pub port: Port,
    pub provider: PluginId,
    pub slot: TypedSlot,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StaticDeclarations {
    pub name: String,
    pub dependencies: Vec<u64>,
    pub provisions: Vec<u64>,
    pub injection_config: BTreeMap<u64, serde_json::Value>,
}
/// A logical plugin definition. Its original FnMut callback persists across
/// episodes. Drop this definition only after the graph's Removed observation.
pub struct StaticPlugin {
    plugin: Plugin,
    declarations: StaticDeclarations,
    current: Option<StaticEpisode>,
    inherited_dependencies: Vec<Port>,
    inherited_context: Option<Vec<Port>>,
}
impl StaticPlugin {
    pub fn new(plugin: Plugin) -> Result<Self, String> {
        if !plugin.injection_config.is_empty() {
            return Err("UnsupportedStaticFeature: requires_with_config".into());
        }
        Self::new_inner(plugin)
    }
    /// Admit configured dependencies only after the external host has installed
    /// these exact ServiceKey/configuration pairs for pending availability.
    /// Explicit JSON null is a declaration, distinct from an inherited default.
    pub fn new_with_injection_config(
        plugin: Plugin,
        expected: BTreeMap<u64, serde_json::Value>,
    ) -> Result<Self, String> {
        if plugin.injection_config != expected {
            return Err("StaticInjectionConfigurationMismatch".into());
        }
        Self::new_inner(plugin)
    }
    fn new_inner(plugin: Plugin) -> Result<Self, String> {
        plugin.validate().map_err(|error| error.to_string())?;
        if plugin.config_update.is_some() {
            return Err("UnsupportedStaticFeature: config_update".into());
        }
        let declarations = StaticDeclarations {
            name: plugin.name.clone(),
            dependencies: plugin.dependencies.clone(),
            provisions: plugin.provisions.clone(),
            injection_config: plugin.injection_config.clone(),
        };
        Ok(Self {
            plugin,
            declarations,
            current: None,
            inherited_dependencies: Vec::new(),
            inherited_context: None,
        })
    }
    pub fn declarations(&self) -> &StaticDeclarations {
        &self.declarations
    }
    /// Bind a child to the parent's actual dependencies and to corresponding
    /// ports in the child's context. Ports and context must already be mapped
    /// to the same identity space that `begin` will use. This retains parent
    /// committed resources even when the child explicitly isolates a service.
    /// A child's own exact provision is excluded to avoid a dependency cycle.
    /// Configure once before the first episode; identity changes require a new
    /// logical child definition, never replacement of an active binding.
    pub fn inherit_dependencies(
        &mut self,
        context: &Context,
        parent_ports: Vec<Port>,
        mut inherited_config: BTreeMap<u64, serde_json::Value>,
    ) -> CallbackResult {
        if self.current.is_some() {
            return Err("StaticDefinitionAlreadyStarted".into());
        }
        if self.inherited_context.is_some() {
            return Err("StaticDependenciesAlreadyInherited".into());
        }
        let port = |key| context.resolve(key);
        let provisions = self
            .declarations
            .provisions
            .iter()
            .map(|key| port(*key))
            .collect::<Vec<_>>();
        let mut context_keys = self.declarations.dependencies.clone();
        context_keys.extend(self.declarations.provisions.iter().copied());
        context_keys.extend(parent_ports.iter().map(|port| port.key));
        context_keys.sort_unstable();
        context_keys.dedup();
        self.inherited_context = Some(context_keys.into_iter().map(port).collect());
        for parent in parent_ports {
            for dependency in [parent, port(parent.key)] {
                if !provisions.contains(&dependency)
                    && !self.inherited_dependencies.contains(&dependency)
                {
                    self.inherited_dependencies.push(dependency);
                }
            }
        }
        inherited_config.extend(self.plugin.injection_config.clone());
        self.declarations.injection_config = inherited_config;
        Ok(())
    }
    pub fn inherited_dependencies(&self) -> &[Port] {
        &self.inherited_dependencies
    }
    pub fn begin(
        &mut self,
        owner: PluginId,
        generation: u64,
        context: Context,
        imports: Vec<StaticBinding>,
    ) -> Result<StaticStart, String> {
        self.begin_inner(owner, generation, context, imports, None, None)
    }
    /// Opt into checked declared services and episode-bound `set`/`refresh`.
    /// The host must route notifications to its authoritative availability
    /// protocol. This never enables child publications, effects or new ports.
    pub fn begin_with_service_updates(
        &mut self,
        owner: PluginId,
        generation: u64,
        context: Context,
        imports: Vec<StaticBinding>,
        notify: Arc<dyn Fn() + Send + Sync>,
    ) -> Result<StaticStart, String> {
        self.begin_inner(owner, generation, context, imports, Some(notify), None)
    }
    /// Enable original `mount`/`publish` operations in the embedding graph.
    /// The host must publish `anchor` on this owner, resolve child dependencies
    /// there, and report child Removed only after actual cleanup and removal.
    /// It must drain requests after every callback/wake, including withdrawal.
    /// The notification callback schedules host work; it must not execute user
    /// callbacks while retaining a graph or episode bookkeeping lock.
    pub fn begin_with_dynamic_host(
        &mut self,
        owner: PluginId,
        generation: u64,
        context: Context,
        imports: Vec<StaticBinding>,
        anchor: Port,
        notify: Arc<dyn Fn() + Send + Sync>,
    ) -> Result<StaticStart, String> {
        if anchor.key == 0 || context.resolve(anchor.key) != anchor {
            return Err("InvalidStaticOwnerAnchor".into());
        }
        self.begin_inner(
            owner,
            generation,
            context,
            imports,
            Some(notify),
            Some(anchor),
        )
    }
    fn begin_inner(
        &mut self,
        owner: PluginId,
        generation: u64,
        context: Context,
        imports: Vec<StaticBinding>,
        service_updates: Option<Arc<dyn Fn() + Send + Sync>>,
        anchor: Option<Port>,
    ) -> Result<StaticStart, String> {
        if generation == 0 {
            return Err("StaticEpisodeRequiresGeneration".into());
        }
        if self
            .current
            .as_ref()
            .is_some_and(|episode| !episode.is_closed())
        {
            return Err("PreviousStaticEpisodeNotRestored".into());
        }
        let port = |key| context.resolve(key);
        if self.inherited_context.as_ref().is_some_and(|expected| {
            expected
                .iter()
                .any(|expected| port(expected.key) != *expected)
        }) {
            return Err("StaticInheritedContextChanged".into());
        }
        let execution = EpisodeExecution::new(Execution::new(fresh(&NEXT_CLEANUP)));
        let values = cordis_kernel::static_values::Values::from_definition(
            &execution,
            cordis_kernel::static_values::Definition {
                owner,
                generation,
                realms: context.realms.clone(),
                dependencies: self.declarations.dependencies.clone(),
                inherited: self.inherited_dependencies.clone(),
                provisions: self.declarations.provisions.clone(),
            },
            imports
                .into_iter()
                .map(|import| cordis_kernel::static_values::Import {
                    port: import.port,
                    provider: import.provider,
                    value: import.slot.0,
                })
                .collect(),
        )
        .map_err(|_| "InvalidStaticBindings".to_owned())?;
        let scope = execution
            .root_scope()
            .expect("static Begin has a root scope");
        let setup = AsyncSetup {
            state: SharedEpisode::external(
                Episode::for_external(
                    execution,
                    EpisodeValues(Some(values)),
                    service_updates,
                    anchor.is_some(),
                ),
                context,
                anchor.unwrap_or(Port { key: 0, realm: 0 }),
            ),
            scope,
        };
        let episode = StaticEpisode {
            setup,
            progress: Arc::new(StaticProgress::default()),
        };
        // Register ownership before invoking a synchronous callback: a partial
        // failure still returns an episode whose registered inverses can run.
        self.current = Some(episode.clone());
        let (root, initial) = match initialize_callback(&mut self.plugin.setup, &episode.setup) {
            Ok(root) => (root, None),
            Err(error) => (RootSetup::done(), Some(Err(error))),
        };
        let future = StaticSetupFuture {
            episode: episode.clone(),
            root,
            initial,
            finished: false,
        };
        Ok(StaticStart {
            episode,
            setup: Box::pin(future),
        })
    }
}
pub struct StaticStart {
    pub episode: StaticEpisode,
    pub setup: StaticFuture,
}
#[derive(Clone)]
pub struct StaticEpisode {
    setup: AsyncSetup,
    progress: Arc<StaticProgress>,
}
impl StaticEpisode {
    pub fn owner(&self) -> PluginId {
        self.setup.owner()
    }
    pub fn generation(&self) -> u64 {
        self.setup.state.generation()
    }
    pub fn is_closed(&self) -> bool {
        lock(&self.setup.state).phase() == EpisodePhase::Closed
    }
    pub fn cancel(&self) {
        let (wake, children) = {
            let mut state = lock(&self.setup.state);
            if state.phase() != EpisodePhase::Closed {
                state.withdraw();
            }
            (state.take_driver(), state.external_children.snapshot())
        };
        for child in children {
            child.request_retirement();
        }
        if let Some(wake) = wake {
            wake.wake();
        }
    }
    /// Take pending child definitions after a callback/poll. Cancelled queued
    /// children are rejected without allocation. An already drained request
    /// remains bound to this exact episode and reports retirement if cancelled.
    pub fn drain_child_requests(&self) -> Result<Vec<StaticChildRequest>, String> {
        let requests = {
            let mut state = lock(&self.setup.state);
            if !state.has_child_host() {
                return Ok(Vec::new());
            }
            state.external_children.prune_removed();
            let mut requests = Vec::with_capacity(state.execution.child_count());
            while let Some(request) = state.execution.take_child() {
                requests.push(request);
            }
            requests
        };
        let mut output: Vec<StaticChildRequest> = Vec::new();
        let mut failure: Option<String> = None;
        for item in requests {
            let receipt = item.run(|request| -> Result<(), String> {
                let ChildDispatch::External(request) = request else {
                    return Err("NativeChildInStaticHost".into());
                };
                let (context, plugin, control) = request.into_parts();
                if let Some(error) = &failure {
                    control.complete_mount(Err(error.clone()))?;
                    return Ok(());
                }
                if control.retirement_requested() {
                    control.complete_mount(Err(CANCELLED.into()))?;
                    return Ok(());
                }
                match StaticPlugin::new_inner(plugin) {
                    Ok(plugin) => output.push(StaticChildRequest {
                        context,
                        plugin,
                        control,
                    }),
                    Err(error) => {
                        control.complete_mount(Err(error.clone()))?;
                        lock(&self.setup.state).reject_child_batch(error.clone());
                        for accepted in output.drain(..) {
                            accepted.control.complete_mount(Err(error.clone()))?;
                        }
                        failure = Some(error);
                    }
                }
                Ok(())
            });
            let completed = lock(&self.setup.state).execution.complete_request(receipt);
            completed.ok().expect("actual child handoff result")?;
        }
        match failure {
            Some(error) => Err(error),
            None => Ok(output),
        }
    }
    /// A snapshot of this episode's actual child controls, including retained
    /// failures. The host observes these during normal scheduling and teardown.
    pub fn child_controls(&self) -> Vec<StaticChildControl> {
        let mut state = lock(&self.setup.state);
        state.external_children.prune_removed();
        state.external_children.snapshot()
    }
    pub fn provided(&self) -> Result<Vec<(Port, TypedSlot)>, String> {
        let state = lock(&self.setup.state);
        self.setup
            .check_live(&state)
            .map_err(|error| error.to_string())?;
        Ok(self
            .setup
            .state
            .services()
            .provisions()
            .iter()
            .filter_map(|port| {
                state
                    .values
                    .own(self.setup.owner(), *port)
                    .map(|slot| (*port, TypedSlot(slot.clone())))
            })
            .collect())
    }
    /// Begin one cleanup attempt. A reported failure remains sticky until an
    /// explicit retry; consumed FnOnce failures and abandoned futures cannot retry.
    pub fn cleanup(&self) -> Result<StaticFuture, String> {
        self.start_cleanup(false)
    }
    /// Retry only a retained retryable factory. The external authoritative host
    /// must first admit its own fresh cleanup action and keep dependency leases.
    pub fn retry_cleanup(&self) -> Result<StaticFuture, String> {
        self.start_cleanup(true)
    }
    pub fn can_retry_cleanup(&self) -> bool {
        let state = lock(&self.setup.state);
        self.progress.can_retry_cleanup(&state)
    }
    fn start_cleanup(&self, retry: bool) -> Result<StaticFuture, String> {
        let mut state = lock(&self.setup.state);
        let previous_error = self.progress.start_cleanup(&mut state, retry)?;
        let children = state.external_children.snapshot();
        drop(state);
        drop(previous_error);
        for child in children {
            child.request_retirement();
        }
        Ok(Box::pin(StaticCleanupFuture {
            episode: self.clone(),
            running: None,
            child: None,
            finished: false,
        }))
    }
}
struct StaticSetupFuture {
    episode: StaticEpisode,
    root: RootSetup,
    initial: Option<CallbackResult>,
    finished: bool,
}
impl Future for StaticSetupFuture {
    type Output = CallbackResult;
    fn poll(mut self: Pin<&mut Self>, cx: &mut TaskContext<'_>) -> Poll<Self::Output> {
        if self.finished {
            return Poll::Ready(Err("StaticSetupAlreadyCompleted".into()));
        }
        // A user-defined waker may reenter the episode from clone/Drop.
        let wake = cx.waker().clone();
        let (withdrawing, previous) = {
            let mut state = lock(&self.episode.setup.state);
            (
                state.phase() == EpisodePhase::Restoring,
                state.replace_driver(wake),
            )
        };
        drop(previous);
        let result = if let Some(result) = self.initial.take() {
            result
        } else {
            let setup = self.episode.setup.clone();
            match self.root.poll(withdrawing, &setup, cx) {
                Some(Poll::Pending) => return Poll::Pending,
                Some(Poll::Ready(result)) => result,
                None if withdrawing => Err(CANCELLED.into()),
                None => Ok(()),
            }
        };
        let (result, previous, discarded) = {
            let mut state = lock(&self.episode.setup.state);
            let mut result = result;
            // An opaque application cause can run arbitrary Drop code. Keep
            // the displaced result until both bookkeeping locks are released.
            let discarded = state
                .unsupported_error()
                .map(|error| std::mem::replace(&mut result, Err(error.into())));
            if result.is_ok() && state.phase() != EpisodePhase::Restoring {
                if let Some(port) = self
                    .episode
                    .setup
                    .state
                    .services()
                    .provisions()
                    .iter()
                    .find(|port| state.own(self.episode.setup.owner(), **port).is_none())
                {
                    result = Err(format!("declared service {} has no value", port.key).into());
                } else {
                    assert!(
                        state.execution.activate_external(),
                        "completed external setup"
                    );
                }
            }
            self.episode.progress.setup_landed();
            (result, state.take_driver(), discarded)
        };
        drop(discarded);
        drop(previous);
        self.finished = true;
        Poll::Ready(result)
    }
}
impl Drop for StaticSetupFuture {
    fn drop(&mut self) {
        if !self.finished {
            self.episode.cancel();
            lock(&self.episode.setup.state).execution.abandon_root();
            self.episode.progress.abandon_setup();
        }
    }
}
struct StaticCleanupFuture {
    episode: StaticEpisode,
    running: Option<RunningCleanup>,
    child: Option<(RestoreTicket, StaticChildControl)>,
    finished: bool,
}
impl StaticCleanupFuture {
    fn fail(&mut self, error: CallbackError) -> Poll<CallbackResult> {
        let previous = lock(&self.episode.setup.state).take_driver();
        drop(previous);
        let previous = self.episode.progress.cleanup_failed(error.clone());
        drop(previous);
        self.finished = true;
        Poll::Ready(Err(error))
    }
    fn complete_reply(&mut self, completion: CleanupCompletion) -> CallbackResult {
        let completed = completion.acknowledge(
            &mut lock(&self.episode.setup.state).execution,
            0,
            CleanupPolicy::RetainFailure,
        );
        let report = match completed {
            Ok(report) => report,
            Err(rejected) => {
                rejected.discard();
                panic!("exact issued restoration receipt");
            }
        };
        drop(report.discarded);
        report.result
    }
    fn complete_child_result(
        &mut self,
        ticket: RestoreTicket,
        result: CallbackResult,
    ) -> CallbackResult {
        let completed = lock(&self.episode.setup.state).execution.complete_result(
            0,
            ticket,
            result,
            None,
            CleanupPolicy::RetainFailure,
        );
        let report = match completed {
            Ok(report) => report,
            Err(rejected) => {
                drop(rejected);
                panic!("exact issued restoration receipt");
            }
        };
        drop(report.discarded);
        report.result
    }
}
impl Future for StaticCleanupFuture {
    type Output = CallbackResult;
    fn poll(mut self: Pin<&mut Self>, cx: &mut TaskContext<'_>) -> Poll<Self::Output> {
        if self.finished {
            return Poll::Ready(Err("StaticCleanupAlreadyCompleted".into()));
        }
        let wake = cx.waker().clone();
        let previous = lock(&self.episode.setup.state).replace_driver(wake);
        drop(previous);
        for _ in 0..64 {
            if let Some((ticket, child)) = self.child.as_ref() {
                let ticket = *ticket;
                match child.poll_retired(cx) {
                    Poll::Pending => return Poll::Pending,
                    Poll::Ready(result) => {
                        self.child = None;
                        if let Err(error) = self.complete_child_result(ticket, result) {
                            return self.fail(error);
                        }
                    }
                }
            }
            if self.running.is_none() {
                let (action, released) = {
                    let mut state = lock(&self.episode.setup.state);
                    let action = state
                        .execution
                        .dispatch(0)
                        .expect("live cleanup group and available attempt identity");
                    // The checked journal includes pending/failed receipts, so
                    // only successful sealing detaches host resources.
                    let released = if action.is_none() {
                        state.seal_external()
                    } else {
                        None
                    };
                    (action, released)
                };
                if let Some(released) = released {
                    let values = released.release_notifications();
                    self.episode.progress.cleanup_succeeded();
                    self.finished = true;
                    drop(values);
                    return Poll::Ready(Ok(()));
                }
                let Some(dispatch) = action else {
                    return self.fail("StaticCleanupUnsettled".into());
                };
                let dispatch = match dispatch {
                    PayloadDispatch::Payload(completion) => {
                        let result = completion.report.result;
                        drop(completion.restored);
                        drop(completion.report.discarded);
                        if let Err(error) = result {
                            return self.fail(payload_restore_error(error));
                        }
                        continue;
                    }
                    PayloadDispatch::Other(dispatch) => dispatch,
                };
                let (ticket, action) = match dispatch {
                    CleanupDispatch::Value { completion, .. } => {
                        if let Err(error) = completion.report.result {
                            return self.fail(value_error(error));
                        }
                        continue;
                    }
                    CleanupDispatch::Host { ticket, action } => (ticket, action),
                };
                match action {
                    CleanupAction::Value(_) => {
                        unreachable!("value inverse runs inside the checked dispatcher")
                    }
                    CleanupAction::Callback(cleanup) => {
                        match RunningCleanup::start(ticket, cleanup) {
                            Ok(future) => self.running = Some(future),
                            Err(failure) => {
                                let error = self.complete_reply(failure).unwrap_err();
                                return self.fail(error);
                            }
                        }
                    }
                    CleanupAction::Native(_) => {
                        self.complete_child_result(ticket, Err("NativeChildInStaticHost".into()))
                            .unwrap_err();
                        return self.fail("NativeChildInStaticHost".into());
                    }
                    CleanupAction::External(child) => {
                        child.request_retirement();
                        self.child = Some((ticket, child));
                        continue;
                    }
                }
            }
            match self.running.as_mut().unwrap().poll(cx) {
                Poll::Pending => return Poll::Pending,
                Poll::Ready(result) => {
                    let attempt = self.running.take().unwrap();
                    if let Err(error) = self.complete_reply(result) {
                        return self.fail(error);
                    }
                    // Retain the Future until completion and error handling unlock.
                    drop(attempt);
                }
            }
        }
        cx.waker().wake_by_ref();
        Poll::Pending
    }
}
impl Drop for StaticCleanupFuture {
    fn drop(&mut self) {
        if !self.finished {
            let previous = lock(&self.episode.setup.state).take_driver();
            drop(previous);
            let previous = self
                .episode
                .progress
                .cleanup_failed("StaticCleanupAbandoned: restoration is unconfirmed".into());
            drop(previous);
        }
    }
}

/// A child definition to install in the same authoritative graph as its owner.
/// `plugin` preserves the original callback and ServiceKey identities; its
/// declarations include the explicit anchor dependency of dynamic publications.
/// Keep its control until the host confirms the actual node was removed.
pub struct StaticChildRequest {
    pub context: Context,
    pub plugin: StaticPlugin,
    pub control: StaticChildControl,
}
impl StaticChildRequest {
    /// Resolve an original ServiceKey identity in this child's exact context.
    pub fn port(&self, key: u64) -> Port {
        self.context.resolve(key)
    }
}
