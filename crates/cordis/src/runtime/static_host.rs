//! A static typed plugin episode driven by an external, authoritative graph.
//!
//! This module never constructs a Runtime or Driver. The embedding host must
//! validate owner/generation, committed bindings and publication leases before
//! calling `begin`, and retain those leases until cleanup really succeeds.
//! Dynamic publication, children, effect groups, updates and service checks are
//! explicitly unsupported. Existing `Plugin`, `Setup`, slots and inverse
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
}
/// A logical plugin definition. Its original FnMut callback persists across
/// episodes. Drop this definition only after the graph's Removed observation.
pub struct StaticPlugin {
    plugin: Plugin,
    declarations: StaticDeclarations,
    current: Option<StaticEpisode>,
}
impl StaticPlugin {
    pub fn new(plugin: Plugin) -> Result<Self, String> {
        if plugin.config_update.is_some() {
            return Err("UnsupportedStaticFeature: config_update".into());
        }
        if !plugin.injection_config.is_empty() {
            return Err("UnsupportedStaticFeature: requires_with_config".into());
        }
        let declarations = StaticDeclarations {
            name: plugin.name.clone(),
            dependencies: plugin.dependencies.clone(),
            provisions: plugin.provisions.clone(),
        };
        Ok(Self {
            plugin,
            declarations,
            current: None,
        })
    }
    pub fn declarations(&self) -> &StaticDeclarations {
        &self.declarations
    }
    pub fn begin(
        &mut self,
        owner: PluginId,
        generation: u64,
        context: Context,
        imports: Vec<StaticBinding>,
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
        let expected = self
            .declarations
            .dependencies
            .iter()
            .map(|key| port(*key))
            .collect::<Vec<_>>();
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
            // Static mode rejects every operation that would use an anchor.
            anchor: Port { key: 0, realm: 0 },
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
        let wake = {
            let mut state = lock(&self.setup.state);
            if state.phase != EpisodePhase::Closed {
                state.phase = EpisodePhase::Restoring;
            }
            state.driver.take()
        };
        if let Some(wake) = wake {
            wake.wake();
        }
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
        Ok(Box::pin(StaticCleanupFuture {
            episode: self.clone(),
            running: None,
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
            if self.running.is_none() {
                let (action, released, previous) = {
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
                        )
                    } else {
                        (action, None, None)
                    }
                };
                drop(previous);
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
                    CleanupAction::Child(_) => {
                        return self.fail("UnsupportedStaticFeature: child inverse".into())
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
