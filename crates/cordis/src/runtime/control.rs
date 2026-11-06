//! Native polling ownership and its ordinary host/Driver boundary.
//! Only this module binds, lends or returns the actual checked PollControl.
//! Decisions are observations; the execution APIs recheck transition guards.
use super::*;

pub(super) struct Control(Option<PollControl<CallbackError>>);
impl Control {
    pub(super) fn unregistered() -> Self {
        Self(None)
    }
    pub(super) fn get(&self) -> &PollControl<CallbackError> {
        self.0.as_ref().expect("registered polling owner")
    }
    pub(super) fn record_setup_failure(&mut self, error: CallbackError) -> Option<CallbackError> {
        self.0
            .as_mut()
            .expect("registered polling owner")
            .record_setup_failure(error)
    }
    pub(super) fn record_cleanup_failure(&mut self, error: CallbackError) -> Option<CallbackError> {
        self.0
            .as_mut()
            .expect("registered polling owner")
            .record_cleanup_failure(error)
    }
}

impl Runtime {
    pub(super) fn bind_control(&mut self, id: PluginId) {
        let control = self
            .kernel
            .poll_control(id)
            .expect("new registered polling owner");
        let slot = &mut self.kernel.host_mut(id).unwrap().control;
        assert!(
            slot.0.is_none(),
            "polling ownership is bound once at registration"
        );
        slot.0 = Some(control);
    }
    // Call only checked, callback-free transitions while the slot is borrowed.
    // Restore it before interpreting either result or dropping returned errors.
    // This is not a recovery boundary for a panic inside the checked owner.
    fn with_control<T>(
        &mut self,
        id: PluginId,
        operation: impl FnOnce(
            &mut NativeDriver<RootBody, Mounted, ServiceSlot>,
            &mut PollControl<CallbackError>,
        ) -> T,
    ) -> T {
        let mut control = self
            .kernel
            .host_mut(id)
            .unwrap()
            .control
            .0
            .take()
            .expect("registered polling owner");
        assert_eq!(control.owner(), id, "polling owner belongs to this plugin");
        let result = operation(&mut self.kernel, &mut control);
        self.kernel.host_mut(id).unwrap().control.0 = Some(control);
        result
    }
    pub(super) fn begin_controlled(
        &mut self,
        id: PluginId,
    ) -> Result<RawEpisodeExecution, KernelError> {
        let domain = fresh(&NEXT_CLEANUP);
        let result = self.with_control(id, |kernel, control| {
            kernel.begin_controlled_execution(id, domain, control)
        });
        result.map(|(execution, discarded)| {
            drop(discarded);
            execution
        })
    }
    pub(super) fn release_controlled(
        &mut self,
        id: PluginId,
        execution: &mut EpisodeExecution,
    ) -> Result<
        (
            cordis_kernel::lifecycle_actions::CleanupOutcome,
            cordis_kernel::lifecycle_state::services::ReleasedNativeValues<ServiceSlot>,
        ),
        KernelError,
    > {
        self.with_control(id, |kernel, control| {
            kernel.release_recorded_controlled(id, execution, control)
        })
    }
    /// Admit a fresh whole-episode attempt only after the previous callbacks
    /// settle and its Failed receipt is recorded. No user callback runs here.
    pub fn retry_cleanup(&mut self, id: PluginId) -> Result<(), RuntimeError> {
        let owner = self
            .kernel
            .host(id)
            .ok_or(RuntimeError::UnknownPlugin(id))?;
        if owner.control().cleanup_failure().is_none()
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
        if !state.execution.can_retry_all() {
            return Err(RuntimeError::Cleanup {
                plugin: id,
                error: "retained cleanup cannot be retried".into(),
            });
        }
        let retried = self.with_control(id, |kernel, control| {
            kernel.retry_recorded_controlled(id, &mut state.execution, control)
        });
        let (_, discarded) = retried.map_err(kernel_error)?;
        let wake = state.take_driver();
        drop(state);
        drop(discarded);
        if let Some(wake) = wake {
            wake.wake();
        }
        Ok(())
    }
    pub fn restart(&mut self, id: PluginId) -> Result<(), RuntimeError> {
        if self.kernel.retired(id) {
            return Err(RuntimeError::Retired(id));
        }
        self.kernel
            .host(id)
            .ok_or(RuntimeError::UnknownPlugin(id))?;
        let restarted = self.with_control(id, |kernel, control| kernel.request_restart(control));
        drop(restarted.map_err(kernel_error)?);
        Ok(())
    }
    pub(super) fn coherent(&self, id: PluginId) -> bool {
        self.kernel.coherent(
            id,
            self.kernel.host(id).unwrap().control().restart_requested(),
        )
    }
    pub(super) fn decision(&self, id: PluginId) -> Option<Decision> {
        let plugin = &self.kernel.host(id).unwrap();
        self.kernel
            .observe_decision(id, plugin.control(), || self.services_available(id))
    }
    pub(super) fn latch(&mut self, id: PluginId, message: CallbackError) {
        if let Some(failures) = &mut self.shutdown_failures {
            failures.entry(id).or_insert_with(|| message.clone());
        }
        let discarded = self
            .kernel
            .host_mut(id)
            .unwrap()
            .control
            .record_setup_failure(message);
        drop(discarded);
    }
}
