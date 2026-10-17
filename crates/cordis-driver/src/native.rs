//! Ordinary Rust access to the checked native registration/lifecycle owner.
//! Domain allocation and scheduler policy are shared with the external adapter.
use super::{allocate_domain, coherent, decision, host_ticket, Decision, HostStatus};
use crate::{ActionTicket, DriverError};
use cordis_kernel::execution::Execution;
use cordis_kernel::lifecycle_actions::CleanupOutcome;
use cordis_kernel::lifecycle_state::native::runtime::NativeRuntime;
use cordis_kernel::lifecycle_state::native::NativeEntry;
use cordis_kernel::lifecycle_state::registration::shared_child::SharedChild;
use cordis_kernel::lifecycle_state::registration::{
    ChildIdentity, PluginDefinition, RegisteredInvocation, RegisteredPlugin,
};
use cordis_kernel::lifecycle_state::services::ReleasedNativeValues;
use cordis_kernel::setup_work::WorkReceipt;
use cordis_kernel::{Error, Kernel, Port};
use std::collections::BTreeMap;
use std::ops::Deref;
use std::sync::Arc;

pub struct NativeDriver<R, H, V> {
    state: NativeRuntime<R, H, V>,
}
impl<R, H, V> Deref for NativeDriver<R, H, V> {
    type Target = Kernel;
    fn deref(&self) -> &Kernel {
        self.state.kernel()
    }
}
impl<R, H, V> NativeDriver<R, H, V> {
    pub fn new() -> Result<Self, DriverError> {
        Ok(Self {
            state: NativeRuntime::new(allocate_domain()?),
        })
    }
    pub fn execution_journal(&self) -> cordis_kernel::reversible_value::joint::Journal {
        self.state.execution_journal()
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
        self.state
            .episode_snapshot(id, execution)
            .map(|snapshot| snapshot.into_joint())
    }
    /// Create a configuration in this actual native execution domain.
    pub fn configuration<S, C, K, U, P: Ord, T>(
        &self,
        current: S,
    ) -> cordis_kernel::configuration_recorded::Recorded<S, C, K, U, P, T> {
        self.state.configuration(current)
    }
    /// Capture a configuration created by this driver. The embedding must
    /// preserve that association, just as it preserves episode ownership.
    #[allow(clippy::type_complexity)]
    pub fn configuration_snapshot<S, C, K, U, P: Ord, T>(
        &self,
        configuration: &cordis_kernel::configuration_recorded::Recorded<S, C, K, U, P, T>,
    ) -> cordis_kernel::lifecycle_state::native::runtime::configuration::Snapshot<S, C, K, U, P, T, V>
    {
        self.state.configuration_snapshot(configuration)
    }
    pub fn configuration_allocation(
        &self,
        id: usize,
    ) -> Option<cordis_kernel::configuration_runtime::Allocation> {
        self.state.configuration_allocation(id)
    }
    pub fn configuration_target(
        &self,
        id: usize,
    ) -> Option<cordis_kernel::configuration_runtime::Target> {
        self.state.configuration_target(id)
    }
    pub fn configuration_target_is_current(
        &self,
        target: cordis_kernel::configuration_runtime::Target,
    ) -> bool {
        self.state.configuration_target_is_current(target)
    }
    pub fn replace_configuration(
        &mut self,
        target: cordis_kernel::configuration_runtime::Target,
        payload: R,
    ) -> Result<R, (Error, R)> {
        self.state.replace_configuration(target, payload)
    }
    pub fn adopt_configurations<M, P>(
        &mut self,
        changes: Vec<cordis_kernel::configuration_runtime::adoption::Change<R, M>>,
        callback: impl Fn(&mut H, M) -> P,
    ) -> Result<
        Vec<cordis_kernel::configuration_runtime::adoption::Previous<R, P>>,
        cordis_kernel::configuration_runtime::adoption::Rejected<R, M>,
    > {
        self.state.adopt_configurations(changes, callback)
    }
    pub fn domain(&self) -> u64 {
        self.state.lifecycle().domain()
    }
    pub fn decision(&self, id: usize, status: HostStatus) -> Option<Decision> {
        decision(self.state.lifecycle(), id, status)
    }
    pub fn poll_control<E>(
        &self,
        id: usize,
    ) -> Option<cordis_kernel::poll_control::PollControl<E>> {
        self.state.poll_control(id)
    }
    pub fn decision_with_control<E>(
        &self,
        id: usize,
        control: &cordis_kernel::poll_control::PollControl<E>,
        available: bool,
    ) -> Option<Decision> {
        if control.owner() != id {
            return None;
        }
        let flags = control.poll_flags();
        self.decision(
            id,
            HostStatus {
                available,
                failed: flags.failed,
                restart: flags.restart,
            },
        )
    }
    pub fn request_restart<E>(
        &self,
        control: &mut cordis_kernel::poll_control::PollControl<E>,
    ) -> Result<Option<E>, Error> {
        self.state.request_restart(control)
    }
    #[allow(clippy::type_complexity)]
    pub fn begin_controlled_execution<C, G, I, E>(
        &mut self,
        id: usize,
        domain: u64,
        control: &mut cordis_kernel::poll_control::PollControl<E>,
    ) -> Result<(Execution<V, C, G, I>, Option<E>), Error> {
        self.state.begin_controlled_execution(id, domain, control)
    }
    pub fn retry_controlled_execution<C, G, I, E>(
        &mut self,
        id: usize,
        execution: &mut Execution<V, C, G, I>,
        control: &mut cordis_kernel::poll_control::PollControl<E>,
    ) -> Result<(cordis_kernel::action_ledger::ActionTicket, Option<E>), Error> {
        self.state
            .retry_controlled_execution(id, execution, control)
    }
    pub fn release_controlled_execution<C, G, I, E>(
        &mut self,
        id: usize,
        execution: &mut Execution<V, C, G, I>,
        control: &mut cordis_kernel::poll_control::PollControl<E>,
    ) -> Result<(CleanupOutcome, ReleasedNativeValues<V>), Error> {
        self.state
            .release_controlled_execution(id, execution, control)
    }
    pub fn coherent(&self, id: usize, restart: bool) -> bool {
        coherent(self.state.kernel(), id, restart)
    }
    pub fn host(&self, id: usize) -> Option<&H> {
        self.state.host(id)
    }
    pub fn host_mut(&mut self, id: usize) -> Option<&mut H> {
        self.state.host_mut(id)
    }
    pub fn registration(&self, id: usize) -> Option<&RegisteredPlugin<R>> {
        self.state.registration(id)
    }
    pub fn ids(&self) -> Vec<usize> {
        self.state.ids()
    }
    pub fn len(&self) -> usize {
        self.state.len()
    }
    pub fn is_empty(&self) -> bool {
        self.state.is_empty()
    }
    pub fn register_plugin(
        &mut self,
        parent: Option<usize>,
        realms: &BTreeMap<u64, u64>,
        anchor: Port,
        definition: PluginDefinition<R>,
        host: H,
    ) -> Result<usize, (Error, PluginDefinition<R>, H)> {
        self.state
            .register(parent, realms, anchor, definition, host)
    }
    pub fn register_shared_child(
        &mut self,
        child: &SharedChild,
        realms: &BTreeMap<u64, u64>,
        anchor: Port,
        definition: PluginDefinition<R>,
        host: H,
    ) -> Result<usize, (Error, PluginDefinition<R>, H)> {
        self.state
            .register_shared_child(child, realms, anchor, definition, host)
            .result
    }
    pub fn retire_shared_child(
        &mut self,
        child: &SharedChild,
    ) -> Result<Option<ChildIdentity>, Error> {
        self.state.retire_shared_child(child).result
    }
    pub fn remove(&mut self, id: usize) -> Result<NativeEntry<R, H>, Error> {
        self.state.remove(id)
    }
    pub fn replace(&mut self, id: usize, payload: R) -> Result<R, (Error, R)> {
        self.state.replace(id, payload)
    }
    pub fn call_root<A, O>(
        &mut self,
        id: usize,
        invocation: RegisteredInvocation<A>,
    ) -> Result<WorkReceipt<O>, RegisteredInvocation<A>>
    where
        R: FnMut(A) -> O,
    {
        self.state.call(id, invocation)
    }
    pub fn native_value(&self, port: Port) -> Option<&Arc<V>> {
        self.state.native_value(port)
    }
    pub fn value_count(&self) -> usize {
        self.state.value_count()
    }
    pub fn begin_cleanup(&mut self, id: usize) -> Result<(), Error> {
        self.state.begin_cleanup(id).map(|_| ())
    }
    pub fn pending_action(&self, id: usize) -> Option<ActionTicket> {
        self.state.lifecycle().pending(id).map(host_ticket)
    }
    pub fn retire(&mut self, id: usize) -> Result<(), Error> {
        self.state.retire(id)
    }
    pub fn leave(&mut self, id: usize) -> Result<(), Error> {
        self.state.leave(id)
    }
    pub fn compact_bindings(&mut self) -> usize {
        self.state.compact_bindings()
    }
    pub fn compact_declarations(&mut self) -> usize {
        self.state.compact_declarations()
    }
    pub fn withdraw_managed_execution<C, G, I>(
        &mut self,
        id: usize,
        execution: &mut Execution<V, C, G, I>,
        retiring: bool,
    ) -> Result<(), Error> {
        self.state
            .withdraw_managed_execution(id, execution, retiring)
    }
    pub fn begin_managed_execution<C, G, I>(
        &mut self,
        id: usize,
        domain: u64,
    ) -> Result<Execution<V, C, G, I>, Error> {
        self.state.begin_managed_execution(id, domain)
    }
    pub fn finish_managed_execution<C, G, I>(
        &mut self,
        id: usize,
        execution: &mut Execution<V, C, G, I>,
    ) -> Result<(), Error> {
        self.state.finish_managed_execution(id, execution)
    }
    pub fn release_managed_execution<C, G, I>(
        &mut self,
        id: usize,
        execution: &mut Execution<V, C, G, I>,
    ) -> Result<(CleanupOutcome, ReleasedNativeValues<V>), Error> {
        self.state.release_managed_execution(id, execution)
    }
    pub fn admit_managed_root<C, G, I, A>(
        &self,
        id: usize,
        execution: &mut Execution<V, C, G, I>,
        argument: A,
    ) -> Result<RegisteredInvocation<A>, A> {
        self.state.admit_managed_root(id, execution, argument)
    }
    pub fn settle_managed_execution<C, G, I>(
        &mut self,
        id: usize,
        execution: &Execution<V, C, G, I>,
    ) -> Result<(), Error> {
        self.state.settle_managed_execution(id, execution)
    }
    pub fn fail_managed_execution<C, G, I>(
        &mut self,
        id: usize,
        execution: &Execution<V, C, G, I>,
    ) -> Result<(), Error> {
        self.state.fail_managed_execution(id, execution)
    }
    pub fn retry_managed_execution<C, G, I>(
        &mut self,
        id: usize,
        execution: &mut Execution<V, C, G, I>,
    ) -> Result<ActionTicket, Error> {
        self.state
            .retry_managed_execution(id, execution)
            .map(host_ticket)
    }
}

impl<R, H, V, F> NativeDriver<cordis_kernel::reversible_value::function::Body<R, F>, H, V> {
    pub fn has_value_root(&self, id: usize) -> bool {
        self.state
            .registration(id)
            .is_some_and(|recipe| recipe.payload_ref().is_value())
    }
    pub fn has_managed_root(&self, id: usize) -> bool {
        self.state
            .registration(id)
            .is_some_and(|recipe| recipe.payload_ref().is_managed())
    }
    pub fn has_service_root(&self, id: usize) -> bool {
        self.state
            .registration(id)
            .is_some_and(|recipe| recipe.payload_ref().is_services())
    }
    pub fn call_opaque_root<A, O>(
        &mut self,
        id: usize,
        invocation: RegisteredInvocation<A>,
    ) -> Result<WorkReceipt<O>, RegisteredInvocation<A>>
    where
        R: FnMut(A) -> O,
    {
        self.state.call_opaque(id, invocation)
    }
}
impl<R, H, T, M, F>
    NativeDriver<
        cordis_kernel::reversible_value::function::Body<R, F>,
        H,
        cordis_kernel::reversible_value::slot::ServiceSlot<T, M>,
    >
{
    pub fn run_service_root<C, G, Cb, X>(
        &mut self,
        id: usize,
        execution: &mut Execution<
            cordis_kernel::reversible_value::slot::ServiceSlot<T, M>,
            C,
            G,
            cordis_kernel::lifecycle_state::registration::shared_child::ChildCleanup<Cb, X>,
        >,
    ) -> Result<
        cordis_kernel::reversible_value::service_function::RegisteredReport,
        cordis_kernel::reversible_value::service_function::AdmissionError,
    > {
        self.state.run_service_root(id, execution)
    }
    pub fn run_value_root<C, G, Cb, X>(
        &mut self,
        id: usize,
        execution: &mut Execution<
            cordis_kernel::reversible_value::slot::ServiceSlot<T, M>,
            C,
            G,
            cordis_kernel::lifecycle_state::registration::shared_child::ChildCleanup<Cb, X>,
        >,
    ) -> Result<
        cordis_kernel::reversible_value::function::RegisteredReport,
        cordis_kernel::reversible_value::function::AdmissionError,
    > {
        self.state.run_value_root(id, execution)
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
        self.state
            .scoped_payload_service_episode_snapshot(id, execution, control, scope)
            .map(|snapshot| snapshot.into_joint())
    }
}

impl<R, H, E: cordis_kernel::reversible_value::effect::ScalarEffect + Copy, T: ?Sized, M>
    NativeDriver<
        cordis_kernel::reversible_value::function::Body<
            R,
            cordis_kernel::reversible_value::managed::Function<E, T>,
        >,
        H,
        cordis_kernel::reversible_value::managed::Slot<T, M>,
    >
{
    pub fn run_managed_root<C, G, A, Retry, X>(
        &mut self,
        id: usize,
        execution: &mut cordis_kernel::reversible_value::managed::Owner<C, G, A, Retry, T, M, X>,
    ) -> Result<
        cordis_kernel::reversible_value::managed::root::RegisteredReport<E, T>,
        cordis_kernel::reversible_value::managed::root::AdmissionError,
    > {
        self.state.run_managed_root(id, execution)
    }
}
