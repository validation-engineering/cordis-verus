//! Historical observations and their Native source association.
//! Query success describes provenance; recovery conditions remain erased proof
//! evidence. These handles never replace live execution/cleanup capabilities.
use super::*;
use cordis_kernel::lifecycle_state::native::runtime::history;

impl<R, H, V> NativeDriver<R, H, V> {
    /// Check the actual retained Native allocation, independent of numeric IDs.
    /// Historical cuts remain associated after later mutations or new Episodes.
    pub fn owns_snapshot(&self, snapshot: &history::Snapshot<V>) -> bool {
        Arc::ptr_eq(
            self.state.poll_control_identity(),
            snapshot.native_identity(),
        )
    }
    /// Normalize observations since an authentic Native cut. None rejects a
    /// foreign owner; Some is not a runtime claim that cleanup or rollback succeeded.
    pub fn recovery_snapshot(
        &self,
        before: &history::Snapshot<V>,
    ) -> Option<history::recovery::Capture<V>> {
        if !self.owns_snapshot(before) {
            return None;
        }
        Some(self.state.recovery_snapshot_from(before))
    }
    pub fn control_source_snapshot(
        &self,
    ) -> Result<
        cordis_kernel::lifecycle_state::native::runtime::control_source::Capture<V>,
        cordis_kernel::lifecycle_state::native::runtime::control_source::Error,
    > {
        self.state.control_source_snapshot()
    }
    pub fn execution_snapshot(&self) -> cordis_kernel::reversible_value::joint::Snapshot {
        self.state.execution_snapshot()
    }
    /// Typed recipe/version evidence in the same history as actual native calls.
    pub fn recipe_snapshot(
        &self,
    ) -> cordis_kernel::lifecycle_state::native::runtime::recipes::Snapshot<R> {
        self.state.recipe_snapshot()
    }
    /// Exact native publication evidence, erased from release builds.
    pub fn publication_snapshot(
        &self,
    ) -> cordis_kernel::lifecycle_state::native::runtime::history::Snapshot<V> {
        self.state.publication_snapshot()
    }
    /// Checkpoint an episode returned by this driver's native Begin.
    pub fn episode_snapshot<C, G, I>(
        &self,
        id: usize,
        execution: &Execution<V, C, G, I>,
    ) -> Option<cordis_kernel::reversible_value::joint::Snapshot> {
        if !self.owns_execution(id, execution) {
            return None;
        }

        self.state
            .episode_snapshot(id, execution)
            .map(|snapshot| snapshot.into_joint())
    }
    /// Reject a foreign configuration before constructing a joint checkpoint.
    /// A configuration created directly in this driver's Journal is also valid.
    #[allow(clippy::type_complexity)]
    pub fn configuration_snapshot<S, C, K, U, P: Ord, T>(
        &self,
        configuration: &cordis_kernel::configuration_recorded::Recorded<S, C, K, U, P, T>,
    ) -> Option<
        cordis_kernel::lifecycle_state::native::runtime::configuration::Snapshot<
            S,
            C,
            K,
            U,
            P,
            T,
            V,
        >,
    > {
        if !self.owns_configuration(configuration) {
            return None;
        }
        Some(self.state.configuration_snapshot(configuration))
    }
}

impl<R, H, T, M> NativeDriver<R, H, cordis_kernel::reversible_value::slot::ServiceSlot<T, M>> {
    /// Certify actual managed publications in the shared execution domain.
    pub fn service_snapshot(&self) -> cordis_kernel::reversible_value::joint::Snapshot {
        self.state.service_snapshot().into_joint()
    }
    /// Certify the actual episode imports, owned services, work and cleanup.
    pub fn service_episode_snapshot<C, G, I>(
        &self,
        id: usize,
        execution: &Execution<cordis_kernel::reversible_value::slot::ServiceSlot<T, M>, C, G, I>,
    ) -> Option<cordis_kernel::reversible_value::joint::Snapshot> {
        if !self.owns_execution(id, execution) {
            return None;
        }

        self.state
            .service_episode_snapshot(id, execution)
            .map(|snapshot| snapshot.into_joint())
    }
    pub fn scoped_service_episode_snapshot<C, G, I, E>(
        &self,
        id: usize,
        execution: &Execution<cordis_kernel::reversible_value::slot::ServiceSlot<T, M>, C, G, I>,
        control: &cordis_kernel::poll_control::PollControl<E>,
        scope: &cordis_kernel::setup_context::SetupScope,
    ) -> Option<cordis_kernel::reversible_value::joint::Snapshot> {
        if !self.owns_setup_scope(id, execution, scope) {
            return None;
        }

        if !self.owns_poll_control(control) {
            return None;
        }
        self.state
            .scoped_service_episode_snapshot(id, execution, control, scope)
            .map(|snapshot| snapshot.into_joint())
    }
    pub fn controlled_service_episode_snapshot<C, G, I, E>(
        &self,
        id: usize,
        execution: &Execution<cordis_kernel::reversible_value::slot::ServiceSlot<T, M>, C, G, I>,
        control: &cordis_kernel::poll_control::PollControl<E>,
    ) -> Option<cordis_kernel::reversible_value::joint::Snapshot> {
        if !self.owns_execution(id, execution) {
            return None;
        }

        if !self.owns_poll_control(control) {
            return None;
        }
        self.state
            .controlled_service_episode_snapshot(id, execution, control)
            .map(|snapshot| snapshot.into_joint())
    }
}

impl<R, H, T: ?Sized, M>
    NativeDriver<
        R,
        H,
        cordis_kernel::reversible_value::slot::ServiceSlot<
            cordis_kernel::reversible_value::payload::SharedPayload<T>,
            M,
        >,
    >
{
    /// Certify actual managed publications in the shared execution domain.
    pub fn payload_service_snapshot(&self) -> cordis_kernel::reversible_value::joint::Snapshot {
        self.state.payload_service_snapshot().into_joint()
    }
    pub fn scoped_payload_service_episode_snapshot<C, G, I, E>(
        &self,
        id: usize,
        execution: &Execution<
            cordis_kernel::reversible_value::slot::ServiceSlot<
                cordis_kernel::reversible_value::payload::SharedPayload<T>,
                M,
            >,
            C,
            G,
            I,
        >,
        control: &cordis_kernel::poll_control::PollControl<E>,
        scope: &cordis_kernel::setup_context::SetupScope,
    ) -> Option<cordis_kernel::reversible_value::joint::Snapshot> {
        if !self.owns_setup_scope(id, execution, scope) {
            return None;
        }

        if !self.owns_poll_control(control) {
            return None;
        }
        self.state
            .scoped_payload_service_episode_snapshot(id, execution, control, scope)
            .map(|snapshot| snapshot.into_joint())
    }
}
