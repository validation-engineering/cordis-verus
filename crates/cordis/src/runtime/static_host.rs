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
//! Cleanup runs the existing FnOnce inverse journal in reverse order. A failed
//! inverse cannot be replayed, so that episode stays open with the same error
//! and remaining values/inverses; restarting it is rejected.
//!
//! [`TypedSlot`] clones share the original `Arc<T>`, and are not revocable
//! capabilities. The host must never expose them as a substitute for checking
//! current episode/publication authority. Static service values become visible
//! in the external graph only after setup succeeds and that graph commits them.
use super::*;

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
        Self(ServiceSlot::new(value, None))
    }
    pub fn get<T: Any + Send + Sync>(&self) -> Option<Arc<T>> {
        self.0.get()
    }
    pub fn has_check(&self) -> bool {
        self.0.check.is_some()
    }
    /// Evaluates a pure predicate without retaining a bookkeeping lock. Panics reject.
    pub fn accepts(&self, context: &Context, config: &serde_json::Value) -> bool {
        self.0.accepts(context, config)
    }
    pub fn value(&self) -> Arc<dyn Any + Send + Sync> {
        lock(&self.0.value).clone()
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
        let port = |key| Port {
            key,
            realm: context.realms.get(&key).copied().unwrap_or(0),
        };
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
        if anchor.key == 0 || context.realms.get(&anchor.key).copied().unwrap_or(0) != anchor.realm
        {
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
        let port = |key| Port {
            key,
            realm: context.realms.get(&key).copied().unwrap_or(0),
        };
        if self.inherited_context.as_ref().is_some_and(|expected| {
            expected
                .iter()
                .any(|expected| port(expected.key) != *expected)
        }) {
            return Err("StaticInheritedContextChanged".into());
        }
        let mut expected = self
            .declarations
            .dependencies
            .iter()
            .map(|key| port(*key))
            .collect::<Vec<_>>();
        for inherited in &self.inherited_dependencies {
            if !expected.contains(inherited) {
                expected.push(*inherited);
            }
        }
        if imports.len() != expected.len() {
            return Err("InvalidStaticBindings".into());
        }
        let mut seen = std::collections::BTreeSet::new();
        for import in &imports {
            if !expected.contains(&import.port)
                || !seen.insert((import.port.key, import.port.realm))
            {
                return Err("InvalidStaticBindings".into());
            }
        }
        let provisions = self
            .declarations
            .provisions
            .iter()
            .map(|key| port(*key))
            .collect();
        let bindings = imports
            .iter()
            .map(|import| Binding {
                key: import.port.key,
                realm: import.port.realm,
                provider: import.provider,
            })
            .collect();
        let values = imports
            .into_iter()
            .map(|import| {
                (
                    (import.provider, import.port.key, import.port.realm),
                    import.slot.0,
                )
            })
            .collect();
        let mut cleanups = BTreeMap::new();
        cleanups.insert(0, Cleanups::new());
        let setup = AsyncSetup {
            generation,
            owner,
            context,
            bindings,
            provisions,
            anchor: anchor.unwrap_or(Port { key: 0, realm: 0 }),
            state: Arc::new(Mutex::new(Episode {
                phase: EpisodePhase::Loading,
                values,
                cleanups,
                groups: Vec::new(),
                children: Vec::new(),
                next_group: 1,
                cancelled_groups: Default::default(),
                driver: None,
                static_only: true,
                dynamic_host: anchor.and(service_updates.clone()),
                external_children: Vec::new(),
                service_updates,
                unsupported: None,
            })),
            group: 0,
        };
        let episode = StaticEpisode {
            setup,
            progress: Arc::new(Mutex::new(StaticProgress::default())),
        };
        // Register ownership before invoking a synchronous callback: a partial
        // failure still returns an episode whose registered inverses can run.
        self.current = Some(episode.clone());
        let (root, initial) = match initialize_callback(&mut self.plugin.setup, &episode.setup) {
            Ok(root) => (root, None),
            Err(error) => (RootSetup::Done, Some(Err(error))),
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
#[derive(Default)]
struct StaticProgress {
    setup_landed: bool,
    abandoned: Option<String>,
    cleanup_running: bool,
    cleanup_error: Option<String>,
}
#[derive(Clone)]
pub struct StaticEpisode {
    setup: AsyncSetup,
    progress: Arc<Mutex<StaticProgress>>,
}
impl StaticEpisode {
    pub fn owner(&self) -> PluginId {
        self.setup.owner
    }
    pub fn generation(&self) -> u64 {
        self.setup.generation
    }
    pub fn is_closed(&self) -> bool {
        lock(&self.setup.state).phase == EpisodePhase::Closed
    }
    pub fn cancel(&self) {
        let (wake, children) = {
            let mut state = lock(&self.setup.state);
            if state.phase != EpisodePhase::Closed {
                state.phase = EpisodePhase::Restoring;
            }
            (state.driver.take(), state.external_children.clone())
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
            if state.dynamic_host.is_none() {
                return Ok(Vec::new());
            }
            state.external_children.retain(|child| !child.is_removed());
            std::mem::take(&mut state.children)
        };
        let mut output: Vec<StaticChildRequest> = Vec::new();
        let mut failure: Option<String> = None;
        for request in requests {
            let control = request.handle.external.expect("external child request");
            if let Some(error) = &failure {
                control.complete_mount(Err(error.clone()))?;
                continue;
            }
            if control.retirement_requested() {
                control.complete_mount(Err(CANCELLED.into()))?;
                continue;
            }
            match StaticPlugin::new_inner(request.plugin) {
                Ok(plugin) => output.push(StaticChildRequest {
                    context: request.context,
                    plugin,
                    control,
                }),
                Err(error) => {
                    control.complete_mount(Err(error.clone()))?;
                    lock(&self.setup.state).unsupported = Some(error.clone());
                    for accepted in output.drain(..) {
                        accepted.control.complete_mount(Err(error.clone()))?;
                    }
                    failure = Some(error);
                }
            }
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
        state.external_children.retain(|child| !child.is_removed());
        state.external_children.clone()
    }
    pub fn provided(&self) -> Result<Vec<(Port, TypedSlot)>, String> {
        let state = lock(&self.setup.state);
        AsyncSetup::check_live(&state)?;
        Ok(self
            .setup
            .provisions
            .iter()
            .filter_map(|port| {
                state
                    .values
                    .get(&(self.setup.owner, port.key, port.realm))
                    .map(|slot| (*port, TypedSlot(slot.clone())))
            })
            .collect())
    }
    /// A legacy FnOnce inverse cannot be replayed after failure. Such failure
    /// is sticky and retains the episode's values and unrun inverses; retries
    /// report the same error, never an empty successful cleanup.
    pub fn cleanup(&self) -> Result<StaticFuture, String> {
        let mut state = lock(&self.setup.state);
        let mut progress = lock(&self.progress);
        if state.phase == EpisodePhase::Closed {
            return Err("StaticEpisodeClosed".into());
        }
        if let Some(error) = progress
            .abandoned
            .as_ref()
            .or(progress.cleanup_error.as_ref())
        {
            return Err(error.clone());
        }
        if !progress.setup_landed {
            return Err("StaticSetupStillRunning".into());
        }
        if progress.cleanup_running {
            return Err("StaticCleanupStillRunning".into());
        }
        state.phase = EpisodePhase::Restoring;
        progress.cleanup_running = true;
        let children = state.external_children.clone();
        drop(progress);
        drop(state);
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
                state.phase == EpisodePhase::Restoring,
                state.driver.replace(wake),
            )
        };
        drop(previous);
        let result = if let Some(result) = self.initial.take() {
            result
        } else {
            match self.root.poll(withdrawing, cx) {
                Some(Poll::Pending) => return Poll::Pending,
                Some(Poll::Ready(result)) => result,
                None if withdrawing => Err(CANCELLED.into()),
                None => Ok(()),
            }
        };
        let (result, previous) = {
            let mut state = lock(&self.episode.setup.state);
            let mut result = result;
            if let Some(error) = &state.unsupported {
                result = Err(error.clone());
            }
            if result.is_ok() && state.phase != EpisodePhase::Restoring {
                if let Some(port) = self.episode.setup.provisions.iter().find(|port| {
                    !state
                        .values
                        .contains_key(&(self.episode.setup.owner, port.key, port.realm))
                }) {
                    result = Err(format!("declared service {} has no value", port.key));
                } else {
                    state.phase = EpisodePhase::Active;
                }
            }
            lock(&self.episode.progress).setup_landed = true;
            (result, state.driver.take())
        };
        drop(previous);
        self.finished = true;
        Poll::Ready(result)
    }
}
impl Drop for StaticSetupFuture {
    fn drop(&mut self) {
        if !self.finished {
            self.episode.cancel();
            lock(&self.episode.progress).abandoned =
                Some("StaticSetupAbandoned: restoration is unconfirmed".into());
        }
    }
}
struct StaticCleanupFuture {
    episode: StaticEpisode,
    running: Option<CleanupFuture>,
    child: Option<StaticChildControl>,
    finished: bool,
}
impl StaticCleanupFuture {
    fn fail(&mut self, error: String) -> Poll<CallbackResult> {
        let previous = lock(&self.episode.setup.state).driver.take();
        drop(previous);
        let mut progress = lock(&self.episode.progress);
        progress.cleanup_running = false;
        progress.cleanup_error = Some(error.clone());
        drop(progress);
        self.finished = true;
        Poll::Ready(Err(error))
    }
}
impl Future for StaticCleanupFuture {
    type Output = CallbackResult;
    fn poll(mut self: Pin<&mut Self>, cx: &mut TaskContext<'_>) -> Poll<Self::Output> {
        if self.finished {
            return Poll::Ready(Err("StaticCleanupAlreadyCompleted".into()));
        }
        let wake = cx.waker().clone();
        let previous = lock(&self.episode.setup.state).driver.replace(wake);
        drop(previous);
        for _ in 0..64 {
            if let Some(child) = self.child.as_ref() {
                match child.poll_retired(cx) {
                    Poll::Pending => return Poll::Pending,
                    Poll::Ready(Err(error)) => return self.fail(error),
                    Poll::Ready(Ok(())) => self.child = None,
                }
            }
            if self.running.is_none() {
                let (action, released, previous, notifications) = {
                    let mut state = lock(&self.episode.setup.state);
                    let action = state.cleanups.get_mut(&0).and_then(Cleanups::pop);
                    if action.is_none() {
                        // Seal under the same lock used by on_cleanup: a late
                        // inverse is either in this journal or rejected.
                        state.phase = EpisodePhase::Closed;
                        state.cleanups.clear();
                        (
                            None,
                            Some(std::mem::take(&mut state.values)),
                            state.driver.take(),
                            (
                                state.service_updates.take(),
                                state.dynamic_host.take(),
                                std::mem::take(&mut state.external_children),
                            ),
                        )
                    } else {
                        (action, None, None, (None, None, Vec::new()))
                    }
                };
                drop(previous);
                // A retained closed AsyncSetup must not retain host notification
                // resources. Their destructors may reenter the episode.
                drop(notifications);
                if let Some(released) = released {
                    lock(&self.episode.progress).cleanup_running = false;
                    self.finished = true;
                    drop(released); // User destructors never run under journal locks.
                    return Poll::Ready(Ok(()));
                }
                match action.unwrap() {
                    CleanupAction::Callback(cleanup) => match initialize_cleanup(cleanup) {
                        Ok(future) => self.running = Some(future),
                        Err(error) => return self.fail(error),
                    },
                    CleanupAction::Child(handle) => {
                        let Some(child) = handle.external else {
                            return self.fail("MissingStaticChildControl".into());
                        };
                        child.request_retirement();
                        self.child = Some(child);
                        continue;
                    }
                }
            }
            match poll_cleanup_callback(self.running.as_mut().unwrap(), cx) {
                Poll::Pending => return Poll::Pending,
                Poll::Ready(result) => {
                    self.running = None;
                    if let Err(error) = result {
                        return self.fail(error);
                    }
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
            let previous = lock(&self.episode.setup.state).driver.take();
            drop(previous);
            let mut progress = lock(&self.episode.progress);
            progress.cleanup_running = false;
            progress.cleanup_error =
                Some("StaticCleanupAbandoned: restoration is unconfirmed".into());
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
        Port {
            key,
            realm: self.context.realms.get(&key).copied().unwrap_or(0),
        }
    }
}
struct StaticChildProgress {
    owner: PluginId,
    generation: u64,
    identity: Arc<Mutex<Result<Option<PluginId>, String>>>,
    assigned: bool,
    retiring: bool,
    removed: bool,
    cleanup_error: Option<String>,
    service: Option<EffectHandle>,
    notify: Option<Arc<dyn Fn() + Send + Sync>>,
    cleanup_waiter: Option<Waker>,
}
/// Exact-episode acknowledgement for an externally allocated child. These are
/// host authority operations, not evidence that arbitrary callbacks are proved.
/// IDs must come from the embedding graph; `removed` requires its Removed
/// observation and must never be substituted with a retirement request.
#[derive(Clone)]
pub struct StaticChildControl(Arc<Mutex<StaticChildProgress>>);
impl StaticChildControl {
    pub(super) fn new(
        owner: PluginId,
        generation: u64,
        identity: Arc<Mutex<Result<Option<PluginId>, String>>>,
        service: Option<EffectHandle>,
        notify: Arc<dyn Fn() + Send + Sync>,
    ) -> Self {
        Self(Arc::new(Mutex::new(StaticChildProgress {
            owner,
            generation,
            identity,
            assigned: false,
            retiring: false,
            removed: false,
            cleanup_error: None,
            service,
            notify: Some(notify),
            cleanup_waiter: None,
        })))
    }
    pub fn owner(&self) -> PluginId {
        lock(&self.0).owner
    }
    pub fn generation(&self) -> u64 {
        lock(&self.0).generation
    }
    pub fn id(&self) -> Option<PluginId> {
        lock(&lock(&self.0).identity)
            .as_ref()
            .ok()
            .copied()
            .flatten()
    }
    pub fn retirement_requested(&self) -> bool {
        let state = lock(&self.0);
        state.retiring
            || state
                .service
                .as_ref()
                .is_some_and(|service| lock(&service.status).cancelled)
    }
    pub fn is_removed(&self) -> bool {
        lock(&self.0).removed
    }
    /// A rejected dynamic publication reports through its ServiceHandle; a
    /// rejected ordinary child request is a setup error of its owner.
    pub fn is_publication(&self) -> bool {
        lock(&self.0).service.is_some()
    }
    /// Resolve allocation exactly once. `Err` is only a pre-allocation rejection:
    /// once a graph node exists, acknowledge its ID and retire/remove it normally.
    /// An allocation that races cancellation
    /// still receives its real ID and must then be retired; it is not discarded.
    pub fn complete_mount(&self, result: Result<PluginId, String>) -> CallbackResult {
        let assigned_id = result.as_ref().ok().copied();
        let (wake, service, error, notify) = {
            let mut state = lock(&self.0);
            if state.assigned {
                return Err("StaticChildAlreadyAssigned".into());
            }
            state.assigned = true;
            let error = result.as_ref().err().cloned();
            if error.is_some() {
                state.removed = true;
            }
            *lock(&state.identity) = result.map(Some);
            let notify = if error.is_some() {
                state.notify.take()
            } else {
                None
            };
            (
                state.cleanup_waiter.take(),
                state.service.clone(),
                error,
                notify,
            )
        };
        drop(notify);
        if let Some(service) = service {
            if let Some(id) = assigned_id {
                let waiters = {
                    let mut status = lock(&service.status);
                    status.external_child_id = Some(id);
                    std::mem::take(&mut status.wakers)
                };
                // A join may already be pending inside the owner's setup. Wake
                // it now so the host can test the newly allocated wait edge.
                wake_waiters(waiters);
            }
            if let Some(error) = error {
                if error != CANCELLED {
                    lock(&service.status).errors.push(error);
                }
                finish_service(&service);
            }
        }
        if let Some(wake) = wake {
            wake.wake();
        }
        Ok(())
    }
    /// Mark a service child initialized only after native setup activation.
    pub fn mark_initialized(&self) -> CallbackResult {
        let service = {
            let state = lock(&self.0);
            if !state.assigned || state.removed || lock(&state.identity).is_err() {
                return Err("StaticChildNotMounted".into());
            }
            state.service.clone()
        };
        if let Some(service) = service {
            let waiters = {
                let mut status = lock(&service.status);
                status.initialized = true;
                std::mem::take(&mut status.wakers)
            };
            wake_waiters(waiters);
        }
        Ok(())
    }
    pub fn request_retirement(&self) {
        let (notify, service) = {
            let mut state = lock(&self.0);
            if state.removed || state.retiring {
                return;
            }
            state.retiring = true;
            (state.notify.clone(), state.service.clone())
        };
        if let Some(service) = service {
            service.cancel();
        }
        if let Some(notify) = notify {
            notify();
        }
    }
    /// Record setup/application failure for service status and eventual join.
    /// This alone does not say that child cleanup failed or removal occurred.
    pub fn record_error(&self, error: String) {
        let service = {
            let state = lock(&self.0);
            if state.removed {
                return;
            }
            state.service.clone()
        };
        if let Some(service) = service {
            let mut state = lock(&service.status);
            if !state.errors.contains(&error) {
                state.errors.push(error);
            }
        }
    }
    /// A failed child inverse blocks owner restoration and keeps the node's
    /// resources/lease alive. Legacy FnOnce cleanup failures remain sticky.
    /// A service join reports the failure while `finished()` remains false:
    /// failure is not an acknowledgement of restoration.
    pub fn cleanup_failed(&self, error: String) {
        let wake = {
            let mut state = lock(&self.0);
            if state.removed {
                return;
            }
            state.retiring = true;
            state.cleanup_error.get_or_insert_with(|| error.clone());
            state.cleanup_waiter.take()
        };
        self.record_error(error.clone());
        let service = lock(&self.0).service.clone();
        if let Some(service) = service {
            let waiters = {
                let mut status = lock(&service.status);
                status.cancelled = true;
                status.terminal_error.get_or_insert(error);
                std::mem::take(&mut status.wakers)
            };
            wake_waiters(waiters);
        }
        if let Some(wake) = wake {
            wake.wake();
        }
    }
    /// Acknowledge actual registry removal. A previously failed inverse cannot
    /// be turned into success by calling this method.
    pub fn removed(&self) -> CallbackResult {
        let (wake, notify, service) = {
            let mut state = lock(&self.0);
            if let Some(error) = &state.cleanup_error {
                return Err(error.clone());
            }
            if !state.assigned
                || lock(&state.identity)
                    .as_ref()
                    .ok()
                    .copied()
                    .flatten()
                    .is_none()
            {
                return Err("StaticChildNotMounted".into());
            }
            state.removed = true;
            (
                state.cleanup_waiter.take(),
                state.notify.take(),
                state.service.clone(),
            )
        };
        drop(notify);
        if let Some(service) = service {
            finish_service(&service);
        }
        if let Some(wake) = wake {
            wake.wake();
        }
        Ok(())
    }
    fn poll_retired(&self, cx: &mut TaskContext<'_>) -> Poll<CallbackResult> {
        let wake = cx.waker().clone();
        let (result, previous) = {
            let mut state = lock(&self.0);
            if let Some(error) = &state.cleanup_error {
                return Poll::Ready(Err(error.clone()));
            }
            if state.removed {
                return Poll::Ready(Ok(()));
            }
            (Poll::Pending, state.cleanup_waiter.replace(wake))
        };
        drop(previous);
        result
    }
}
