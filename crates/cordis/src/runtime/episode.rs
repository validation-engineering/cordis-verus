//! Episode identity, host capabilities, notifications and checked closure.
//! The checked lock is the only production entry to its mutable state.
use super::*;

pub(super) struct Episode {
    pub(super) values: EpisodeValues,
    pub(super) execution: EpisodeExecution,
    driver: Option<Waker>,
    static_only: bool,
    dynamic_host: Option<Arc<dyn Fn() + Send + Sync>>,
    pub(super) external_children: ExternalChildren,
    service_updates: Option<Arc<dyn Fn() + Send + Sync>>,
    unsupported: Option<String>,
}
impl Episode {
    // Registration errors here violate the host's already-checked live scope.
    // The execution remains the only owner of the group and its real payload.
    pub(super) fn register_cleanup(&mut self, group: usize, cleanup: CleanupAction) {
        let accepted = self.execution.register(group, cleanup);
        assert!(
            accepted.is_ok(),
            "only live groups accept cleanup registration"
        );
    }
    pub(super) fn for_native(execution: EpisodeExecution, driver: Waker) -> Self {
        Self {
            // Native committed values live in the checked execution, not in a
            // second host map that could retain unrelated providers.
            values: EpisodeValues::default(),
            execution,
            driver: Some(driver),
            static_only: false,
            dynamic_host: None,
            external_children: ExternalChildren::default(),
            service_updates: None,
            unsupported: None,
        }
    }
    pub(super) fn for_external(
        execution: EpisodeExecution,
        values: EpisodeValues,
        service_updates: Option<Arc<dyn Fn() + Send + Sync>>,
        has_anchor: bool,
    ) -> Self {
        Self {
            values,
            execution,
            driver: None,
            static_only: true,
            dynamic_host: has_anchor.then(|| service_updates.clone()).flatten(),
            external_children: ExternalChildren::default(),
            service_updates,
            unsupported: None,
        }
    }
    pub(super) fn require_feature(&mut self, feature: Feature) -> CallbackResult {
        let allowed = !self.static_only
            || match feature {
                Feature::Mount | Feature::Publish => self.dynamic_host.is_some(),
                Feature::ProvideChecked | Feature::Set | Feature::Refresh => {
                    self.service_updates.is_some()
                }
                Feature::Effect => false,
            };
        if allowed {
            return Ok(());
        }
        let message = format!("UnsupportedStaticFeature: {}", feature.name());
        if self.unsupported.is_none() {
            self.unsupported = Some(message.clone());
        }
        Err(message.into())
    }
    pub(super) fn reject_child_batch(&mut self, error: String) {
        // Batch rejection takes precedence over an earlier unsupported call.
        self.unsupported = Some(error);
    }
    pub(super) fn unsupported_error(&self) -> Option<&str> {
        self.unsupported.as_deref()
    }
    pub(super) fn has_child_host(&self) -> bool {
        self.dynamic_host.is_some()
    }
    pub(super) fn child_host(&self) -> Option<Arc<dyn Fn() + Send + Sync>> {
        self.dynamic_host.clone()
    }
    pub(super) fn check_service_update(&self) -> CallbackResult {
        if self.service_updates.is_some()
            && !matches!(self.phase(), EpisodePhase::Loading | EpisodePhase::Active)
        {
            Err(CANCELLED.into())
        } else {
            Ok(())
        }
    }
    // Callers clone before acquiring the Episode guard and drop the displaced
    // waker after releasing it. Even a Waker's clone/Drop can run user code.
    pub(super) fn replace_driver(&mut self, driver: Waker) -> Option<Waker> {
        self.driver.replace(driver)
    }
    pub(super) fn take_driver(&mut self) -> Option<Waker> {
        self.driver.take()
    }
    pub(super) fn service_notification(&mut self) -> Notification {
        Notification::new(self.driver.take(), self.service_updates.clone())
    }
    pub(super) fn child_notification(&mut self) -> Notification {
        Notification::new(self.driver.take(), self.dynamic_host.clone())
    }
    pub(super) fn phase(&self) -> EpisodePhase {
        self.execution.phase()
    }
    pub(super) fn withdraw(&mut self) {
        self.execution.withdraw_work();
    }
    // Return all retired host resources; no user Drop runs under the guard.
    pub(super) fn seal_external(&mut self) -> Option<ClosedEpisode> {
        if !self.execution.seal_external() {
            return None;
        }
        Some(ClosedEpisode {
            values: std::mem::take(&mut self.values),
            driver: self.driver.take(),
            service_updates: self.service_updates.take(),
            dynamic_host: self.dynamic_host.take(),
            children: std::mem::take(&mut self.external_children),
        })
    }
    pub(super) fn can_finish(&self, target: &[Binding]) -> bool {
        self.execution.can_finish(target)
    }
    pub(super) fn own(&self, owner: PluginId, port: Port) -> Option<&SharedSlot> {
        match self.execution.native() {
            Some(values) if values.ticket().id == owner => values.own(port),
            Some(_) => None,
            None => self.values.own(owner, port),
        }
    }
    pub(super) fn provide(
        &mut self,
        owner: PluginId,
        provisions: &[Port],
        port: Port,
        value: SharedSlot,
    ) -> Result<(), (NativeValueError, SharedSlot)> {
        if self.execution.native().is_some() {
            self.execution.provide(port, value)
        } else {
            self.values.provide(owner, provisions, port, value)
        }
    }
}

// Only these public operations request optional host capabilities. A typed
// request keeps the policy and its existing diagnostic spelling together.
#[derive(Clone, Copy)]
pub(super) enum Feature {
    ProvideChecked,
    Set,
    Refresh,
    Publish,
    Mount,
    Effect,
}
impl Feature {
    fn name(self) -> &'static str {
        match self {
            Self::ProvideChecked => "provide_checked",
            Self::Set => "set",
            Self::Refresh => "refresh",
            Self::Publish => "publish",
            Self::Mount => "mount",
            Self::Effect => "effect",
        }
    }
}

// Shared by Episode and effect/service status. This transports an already
// selected notification, not permission to mutate either owner's state.
// There is no Drop hook: discarding it never invokes its callback.
pub(super) struct Notification {
    driver: Option<Waker>,
    notify: Option<Arc<dyn Fn() + Send + Sync>>,
}
impl Notification {
    pub(super) fn new(driver: Option<Waker>, notify: Option<Arc<dyn Fn() + Send + Sync>>) -> Self {
        Self { driver, notify }
    }
    pub(super) fn wake(self) {
        if let Some(notify) = self.notify {
            notify();
        }
        if let Some(driver) = self.driver {
            driver.wake();
        }
    }
}

pub(super) struct ClosedEpisode {
    values: EpisodeValues,
    driver: Option<Waker>,
    service_updates: Option<Arc<dyn Fn() + Send + Sync>>,
    dynamic_host: Option<Arc<dyn Fn() + Send + Sync>>,
    children: ExternalChildren,
}
impl ClosedEpisode {
    // Preserve the static host's release order: driver, notifications/children,
    // then completion bookkeeping, and only then values. Called after unlocking.
    pub(super) fn release_notifications(self) -> EpisodeValues {
        drop(self.driver);
        drop((self.service_updates, self.dynamic_host, self.children));
        self.values
    }
}

// Keep immutable context and mutable execution in one allocation. Cloning or
// scoping an AsyncSetup cannot pair a copied context with another Episode.
pub(super) struct SharedEpisode {
    association: cordis_kernel::host_context::Association,
    generation: u64,
    context: Context,
    services: SetupServices,
    anchor: Port,
    episode: Mutex<Episode>,
}
impl SharedEpisode {
    pub(super) fn native(episode: Episode, generation: u64) -> Arc<Self> {
        let (association, context) =
            cordis_kernel::host_context::Association::native(&episode.execution)
                .expect("native Begin carries its checked context");
        Arc::new(Self {
            association,
            generation,
            context: Context {
                realms: context.realm_context(),
            },
            anchor: context.anchor(),
            services: SetupServices::Native(context),
            episode: Mutex::new(episode),
        })
    }

    pub(super) fn external(episode: Episode, context: Context, anchor: Port) -> Arc<Self> {
        let services = episode
            .values
            .0
            .as_ref()
            .expect("static Begin carries its checked values")
            .context();
        let association = services.association();
        assert!(
            association.matches(&episode.execution),
            "static values belong to this execution"
        );
        Arc::new(Self {
            association,
            generation: services.generation(),
            context,
            services: SetupServices::External(services),
            anchor,
            episode: Mutex::new(episode),
        })
    }

    pub(super) fn generation(&self) -> u64 {
        self.generation
    }
    pub(super) fn context(&self) -> &Context {
        &self.context
    }
    pub(super) fn services(&self) -> &SetupServices {
        &self.services
    }
    pub(super) fn anchor(&self) -> Port {
        self.anchor
    }
}
pub(super) enum SetupServices {
    Native(Arc<NativeContext>),
    External(Arc<cordis_kernel::static_values::Context>),
}
impl SetupServices {
    pub(super) fn owner(&self) -> PluginId {
        match self {
            Self::Native(context) => context.owner(),
            Self::External(context) => context.owner(),
        }
    }
    pub(super) fn provisions(&self) -> &[Port] {
        match self {
            Self::Native(context) => context.provision_ports(),
            Self::External(context) => context.provision_ports(),
        }
    }
}
impl HostLock for SharedEpisode {
    type State = Episode;
    fn checked_lock(&self) -> MutexGuard<'_, Episode> {
        let state = self.episode.checked_lock();
        assert!(
            self.association.matches(&state.execution),
            "shared Episode execution identity changed"
        );
        state
    }
}

#[cfg(test)]
mod association_tests {
    use super::*;
    use crate::runtime::static_host::StaticPlugin;

    #[test]
    fn a_shared_episode_rejects_a_substituted_execution_before_access() {
        let captured = Arc::new(Mutex::new(None));
        let output = captured.clone();
        let mut plugin = StaticPlugin::new(Plugin::new("association", move |setup| {
            *lock(&output) = Some(setup.to_async());
            Ok(())
        }))
        .unwrap();
        let _start = plugin.begin(7, 1, Context::new(), vec![]).unwrap();
        let shared = lock(&captured).take().unwrap().state;
        let original = {
            let mut state = shared.episode.lock().unwrap();
            std::mem::replace(
                &mut state.execution,
                EpisodeExecution::new(Execution::new(fresh(&NEXT_CLEANUP))),
            )
        };
        let rejected =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| drop(lock(&shared))));
        assert!(rejected.is_err());
        shared
            .episode
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .execution = original;
        assert_eq!(lock(&shared).phase(), EpisodePhase::Loading);
    }
}

#[cfg(test)]
mod notification_tests {
    use super::*;
    use crate::runtime::static_host::StaticPlugin;
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

    struct ApplicationFailure {
        setup: AsyncSetup,
        unlocked: Arc<AtomicBool>,
        drops: Arc<AtomicUsize>,
    }
    impl fmt::Debug for ApplicationFailure {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("ApplicationFailure")
        }
    }
    impl fmt::Display for ApplicationFailure {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("application failed")
        }
    }
    impl std::error::Error for ApplicationFailure {}
    impl Drop for ApplicationFailure {
        fn drop(&mut self) {
            // Observe lock ownership without letting a regression hang the
            // process. Production code has no access to this raw mutex.
            self.unlocked.store(
                self.setup.state.episode.try_lock().is_ok(),
                Ordering::SeqCst,
            );
            self.drops.fetch_add(1, Ordering::SeqCst);
        }
    }
    #[test]
    fn setup_override_drops_application_error_outside_episode_lock() {
        let unlocked = Arc::new(AtomicBool::new(false));
        let drops = Arc::new(AtomicUsize::new(0));
        let observed = unlocked.clone();
        let released = drops.clone();
        let mut plugin = StaticPlugin::new(Plugin::new("unsupported-with-cause", move |setup| {
            // Unsupported operations remain sticky even if their error is
            // ignored and the plugin subsequently returns another error.
            let _ = setup.effect(Effect::new());
            Err(CallbackError::new(ApplicationFailure {
                setup: setup.to_async(),
                unlocked: observed.clone(),
                drops: released.clone(),
            }))
        }))
        .unwrap();
        let mut start = plugin.begin(1, 1, Context::new(), vec![]).unwrap();
        let mut cx = TaskContext::from_waker(Waker::noop());
        assert_eq!(
            start.setup.as_mut().poll(&mut cx),
            Poll::Ready(Err("UnsupportedStaticFeature: effect".into()))
        );
        assert_eq!(drops.load(Ordering::SeqCst), 1);
        assert!(unlocked.load(Ordering::SeqCst));
        let mut cleanup = start.episode.cleanup().unwrap();
        assert_eq!(cleanup.as_mut().poll(&mut cx), Poll::Ready(Ok(())));
        assert!(start.episode.is_closed());
    }
}
