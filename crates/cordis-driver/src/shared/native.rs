//! Ordinary Rust access to the checked native registration/lifecycle owner.
//! Domain allocation and scheduler policy are shared with the external adapter.
mod snapshots;
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
use cordis_kernel::reversible_value::managed::{
    interleaving::history::lifecycle::{
        native::{ReleaseOutcome, RootOutcome},
        RecordedExecution,
    },
    Owner, Slot,
};
use cordis_kernel::setup_work::WorkReceipt;
use cordis_kernel::{Error, Kernel, Port};
use std::collections::BTreeMap;
use std::ops::Deref;
use std::sync::Arc;

// The verified borrowed handles describe exactly the Journal used by commits.
// Arc identity comparison remains in this ordinary adapter, with no lock or clone.
fn same_journal(
    left: &cordis_kernel::reversible_value::joint::Journal,
    right: &cordis_kernel::reversible_value::joint::Journal,
) -> bool {
    Arc::ptr_eq(left.runtime_identity(), right.runtime_identity())
}

/// Ordinary Rust access to one native state owner. Executions/configurations
/// authenticate their actual Journal, and controlled/scoped calls also check
/// their retained Native/queue allocations before entering checked owners.
/// Invocation and configuration targets retain that same Native allocation.
/// Historical recovery keeps its own contracts; pointer comparison remains an
/// ordinary Rust/standard-library boundary.
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
    /// Opt in to a bounded transcript of actual native control transitions.
    /// Exhaustion disables source certification without failing lifecycle calls.
    pub fn new_recorded(limit: usize) -> Result<Self, DriverError> {
        Ok(Self {
            state: NativeRuntime::new_recorded(allocate_domain()?, limit),
        })
    }
    pub fn control_recording_status(
        &self,
    ) -> cordis_kernel::lifecycle_state::native::runtime::control_source::Status {
        self.state.control_recording_status()
    }

    pub fn execution_journal(&self) -> cordis_kernel::reversible_value::joint::Journal {
        self.state.execution_journal()
    }

    /// Journal provenance and the existing current-Episode selector are both
    /// required. Standalone work and equal numbers from another owner fail.
    pub fn owns_execution<C, G, I>(&self, id: usize, execution: &Execution<V, C, G, I>) -> bool {
        execution
            .execution_domain()
            .is_some_and(|journal| same_journal(self.state.execution_domain(), journal))
            && self.state.matches_execution(id, execution)
    }
    /// A scope retains the queue it was actually issued from, not its payload.
    pub fn owns_setup_scope<C, G, I>(
        &self,
        id: usize,
        execution: &Execution<V, C, G, I>,
        scope: &cordis_kernel::setup_context::SetupScope,
    ) -> bool {
        if !self.owns_execution(id, execution) || !scope.belongs(execution) {
            return false;
        }
        match (
            scope.binding_identity(),
            execution
                .get(scope.group())
                .and_then(|queue| queue.allocation_identity()),
        ) {
            (Some(scope), Some(queue)) => Arc::ptr_eq(scope, queue),
            _ => false,
        }
    }
    pub fn owns_configuration<S, C, K, U, P: Ord, T>(
        &self,
        configuration: &cordis_kernel::configuration_recorded::Recorded<S, C, K, U, P, T>,
    ) -> bool {
        same_journal(
            self.state.execution_domain(),
            configuration.execution_domain(),
        )
    }
    /// Authenticate provenance before dispatch; the kernel still checks current
    /// owner, episode, root readiness and recipe version.
    pub fn owns_invocation<A>(&self, invocation: &RegisteredInvocation<A>) -> bool {
        invocation
            .native_identity()
            .is_some_and(|identity| Arc::ptr_eq(self.state.poll_control_identity(), identity))
    }
    pub fn owns_configuration_target(
        &self,
        target: &cordis_kernel::configuration_runtime::Target,
    ) -> bool {
        Arc::ptr_eq(self.state.poll_control_identity(), target.native_identity())
    }

    /// Create a configuration in this actual native execution domain.
    pub fn configuration<S, C, K, U, P: Ord, T>(
        &self,
        current: S,
    ) -> cordis_kernel::configuration_recorded::Recorded<S, C, K, U, P, T> {
        self.state.configuration(current)
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
        target: &cordis_kernel::configuration_runtime::Target,
    ) -> bool {
        self.owns_configuration_target(target) && self.state.configuration_target_is_current(target)
    }
    pub fn replace_configuration(
        &mut self,
        target: &cordis_kernel::configuration_runtime::Target,
        payload: R,
    ) -> Result<R, (Error, R)> {
        if !self.owns_configuration_target(target) {
            return Err((Error::InvalidState, payload));
        }
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
        use cordis_kernel::configuration_runtime::adoption::{Cause, Failure, Rejected};
        // Reuse checked preflight instead of duplicating freshness, duplicate or
        // capacity policy. Merge provenance at the earliest input position;
        // a foreign target wins over other failures at that same position.
        let failure = self.state.preflight_configurations(&changes).err();
        let prefix = failure.map_or(changes.len(), |failure| failure.index + 1);
        if let Some(index) = changes[..prefix]
            .iter()
            .position(|change| !self.owns_configuration_target(&change.target))
        {
            return Err(Rejected {
                failure: Failure {
                    index,
                    cause: Cause::Target,
                },
                changes,
            });
        }
        if let Some(failure) = failure {
            return Err(Rejected { failure, changes });
        }
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
    /// Check the immutable allocation shared by this Native owner and its
    /// controls. Plugin/domain numbers and allocation counters are not compared.
    /// This establishes provenance, not current registration or episode liveness.
    pub fn owns_poll_control<E>(
        &self,
        control: &cordis_kernel::poll_control::PollControl<E>,
    ) -> bool {
        Arc::ptr_eq(
            self.state.poll_control_identity(),
            control.binding_identity(),
        )
    }
    /// Reject foreign controls before interpreting their polling flags.
    pub fn decision_with_control<E>(
        &self,
        id: usize,
        control: &cordis_kernel::poll_control::PollControl<E>,
        available: bool,
    ) -> Option<Decision> {
        if control.owner() != id || !self.owns_poll_control(control) {
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
    /// Observe availability only at the native executor's decision points.
    /// Foreign controls are rejected before the user callback is evaluated.
    /// The callback may inspect user values, so retiring/unloading nodes and
    /// incoherent active targets must not evaluate it. No observation is cached;
    /// callers still use the checked transition APIs after this decision.
    pub fn observe_decision<E>(
        &self,
        id: usize,
        control: &cordis_kernel::poll_control::PollControl<E>,
        available: impl FnOnce() -> bool,
    ) -> Option<Decision> {
        if control.owner() != id || !self.owns_poll_control(control) {
            return None;
        }
        let available = match self.state.kernel().phase(id) {
            Some(cordis_kernel::Phase::Loading | cordis_kernel::Phase::Active)
                if self.coherent(id, control.restart_requested()) =>
            {
                available()
            }
            Some(cordis_kernel::Phase::Inactive)
                if !self.state.kernel().retired(id) && control.failed().is_none() =>
            {
                available()
            }
            _ => false,
        };
        self.decision_with_control(id, control, available)
    }
    pub fn request_restart<E>(
        &self,
        control: &mut cordis_kernel::poll_control::PollControl<E>,
    ) -> Result<Option<E>, Error> {
        if !self.owns_poll_control(control) {
            return Err(Error::InvalidState);
        }
        self.state.request_restart(control)
    }
    #[allow(clippy::type_complexity)]
    pub fn begin_controlled_execution<C, G, I, E>(
        &mut self,
        id: usize,
        domain: u64,
        control: &mut cordis_kernel::poll_control::PollControl<E>,
    ) -> Result<(Execution<V, C, G, I>, Option<E>), Error> {
        if !self.owns_poll_control(control) {
            return Err(Error::InvalidState);
        }
        self.state.begin_controlled_execution(id, domain, control)
    }
    pub fn retry_controlled_execution<C, G, I, E>(
        &mut self,
        id: usize,
        execution: &mut Execution<V, C, G, I>,
        control: &mut cordis_kernel::poll_control::PollControl<E>,
    ) -> Result<(cordis_kernel::action_ledger::ActionTicket, Option<E>), Error> {
        if !self.owns_execution(id, execution) {
            return Err(Error::InvalidState);
        }

        if !self.owns_poll_control(control) {
            return Err(Error::InvalidState);
        }
        self.state
            .retry_controlled_execution(id, execution, control)
    }
    pub fn release_controlled_execution<C, G, I, E>(
        &mut self,
        id: usize,
        execution: &mut Execution<V, C, G, I>,
        control: &mut cordis_kernel::poll_control::PollControl<E>,
    ) -> Result<(CleanupOutcome, ReleasedNativeValues<V>), Error> {
        if !self.owns_execution(id, execution) {
            return Err(Error::InvalidState);
        }

        if !self.owns_poll_control(control) {
            return Err(Error::InvalidState);
        }
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
    /// The shared Child keeps its creating work or local registration Journal.
    /// Parent/episode freshness and terminal-state guards still belong to the kernel.
    pub fn owns_shared_child(&self, child: &SharedChild) -> bool {
        child
            .execution_domain()
            .is_some_and(|journal| same_journal(self.state.execution_domain(), journal))
    }
    pub fn registered_child(&self, id: usize) -> Option<SharedChild> {
        self.state
            .registered_child(id)
            .map(|(child, _snapshot)| child)
    }
    pub fn register_shared_child(
        &mut self,
        child: &SharedChild,
        realms: &BTreeMap<u64, u64>,
        anchor: Port,
        definition: PluginDefinition<R>,
        host: H,
    ) -> Result<usize, (Error, PluginDefinition<R>, H)> {
        if !self.owns_shared_child(child) {
            return Err((Error::InvalidState, definition, host));
        }
        self.state
            .register_shared_child(child, realms, anchor, definition, host)
            .result
    }
    pub fn retire_shared_child(
        &mut self,
        child: &SharedChild,
    ) -> Result<Option<ChildIdentity>, Error> {
        if !self.owns_shared_child(child) {
            return Err(Error::InvalidState);
        }
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
        if !self.owns_invocation(&invocation) {
            return Err(invocation);
        }
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
        if !self.owns_execution(id, execution) {
            return Err(Error::InvalidState);
        }

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
        if !self.owns_execution(id, execution) {
            return Err(Error::InvalidState);
        }

        self.state.finish_managed_execution(id, execution)
    }
    pub fn release_managed_execution<C, G, I>(
        &mut self,
        id: usize,
        execution: &mut Execution<V, C, G, I>,
    ) -> Result<(CleanupOutcome, ReleasedNativeValues<V>), Error> {
        if !self.owns_execution(id, execution) {
            return Err(Error::InvalidState);
        }

        self.state.release_managed_execution(id, execution)
    }
    pub fn admit_managed_root<C, G, I, A>(
        &self,
        id: usize,
        execution: &mut Execution<V, C, G, I>,
        argument: A,
    ) -> Result<RegisteredInvocation<A>, A> {
        if !self.owns_execution(id, execution) {
            return Err(argument);
        }

        self.state.admit_managed_root(id, execution, argument)
    }
    pub fn settle_managed_execution<C, G, I>(
        &mut self,
        id: usize,
        execution: &Execution<V, C, G, I>,
    ) -> Result<(), Error> {
        if !self.owns_execution(id, execution) {
            return Err(Error::InvalidState);
        }

        self.state.settle_managed_execution(id, execution)
    }
    pub fn fail_managed_execution<C, G, I>(
        &mut self,
        id: usize,
        execution: &Execution<V, C, G, I>,
    ) -> Result<(), Error> {
        if !self.owns_execution(id, execution) {
            return Err(Error::InvalidState);
        }

        self.state.fail_managed_execution(id, execution)
    }
    pub fn retry_managed_execution<C, G, I>(
        &mut self,
        id: usize,
        execution: &mut Execution<V, C, G, I>,
    ) -> Result<ActionTicket, Error> {
        if !self.owns_execution(id, execution) {
            return Err(Error::InvalidState);
        }

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
        if !self.owns_invocation(&invocation) {
            return Err(invocation);
        }
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
        if !self.owns_execution(id, execution) {
            return Err(
                cordis_kernel::reversible_value::service_function::AdmissionError::WrongOwner,
            );
        }

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
        if !self.owns_execution(id, execution) {
            return Err(cordis_kernel::reversible_value::function::AdmissionError::WrongOwner);
        }

        self.state.run_value_root(id, execution)
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
        if !self.owns_execution(id, execution) {
            return Err(cordis_kernel::reversible_value::managed::root::AdmissionError::WrongOwner);
        }

        self.state.run_managed_root(id, execution)
    }
}

impl<P, H, T: ?Sized, M> NativeDriver<P, H, Slot<T, M>> {
    pub fn finish_recorded_execution<C, G, A, R, X>(
        &mut self,
        id: usize,
        owner: &mut RecordedExecution<C, G, A, R, T, M, X>,
    ) -> Result<(), Error> {
        if !self.owns_execution(id, owner.execution()) {
            return Err(Error::InvalidState);
        }

        owner.finish(&mut self.state, id)
    }
    pub fn withdraw_recorded_execution<C, G, A, R, X>(
        &mut self,
        id: usize,
        owner: &mut RecordedExecution<C, G, A, R, T, M, X>,
        retiring: bool,
    ) -> Result<(), Error> {
        if !self.owns_execution(id, owner.execution()) {
            return Err(Error::InvalidState);
        }

        owner.withdraw(&mut self.state, id, retiring)
    }
    pub fn retry_recorded_controlled<C, G, A, R, X, E>(
        &mut self,
        id: usize,
        owner: &mut RecordedExecution<C, G, A, R, T, M, X>,
        control: &mut cordis_kernel::poll_control::PollControl<E>,
    ) -> Result<(cordis_kernel::action_ledger::ActionTicket, Option<E>), Error> {
        if !self.owns_execution(id, owner.execution()) {
            return Err(Error::InvalidState);
        }

        if !self.owns_poll_control(control) {
            return Err(Error::InvalidState);
        }
        owner.retry_controlled(&mut self.state, id, control)
    }
    pub fn release_recorded_controlled<C, G, A, R, X, E>(
        &mut self,
        id: usize,
        owner: &mut RecordedExecution<C, G, A, R, T, M, X>,
        control: &mut cordis_kernel::poll_control::PollControl<E>,
    ) -> Result<(CleanupOutcome, ReleasedNativeValues<Slot<T, M>>), Error> {
        self.release_recorded_controlled_observed(id, owner, control)
            .0
    }
    pub fn admit_recorded_root<C, G, A, R, X, B>(
        &self,
        id: usize,
        owner: &mut RecordedExecution<C, G, A, R, T, M, X>,
        argument: B,
    ) -> Result<RegisteredInvocation<B>, B> {
        if !self.owns_execution(id, owner.execution()) {
            return Err(argument);
        }

        owner.admit_root(&self.state, id, argument)
    }
}
impl<P, H, E: cordis_kernel::reversible_value::effect::ScalarEffect + Copy, T: ?Sized, M>
    NativeDriver<
        cordis_kernel::reversible_value::function::Body<
            P,
            cordis_kernel::reversible_value::managed::Function<E, T>,
        >,
        H,
        Slot<T, M>,
    >
{
    /// Attach the actual root-return prefix to the owner used for later cleanup.
    pub fn run_recorded_root<C, G, A, R, X>(
        &mut self,
        id: usize,
        owner: Owner<C, G, A, R, T, M, X>,
    ) -> RootOutcome<C, G, A, R, T, M, X, E> {
        if !self.owns_execution(id, &owner) {
            return (
                RecordedExecution::new(owner),
                Err(cordis_kernel::reversible_value::managed::root::AdmissionError::WrongOwner),
            );
        }

        self.state.run_recorded_root(id, owner)
    }
}
impl<P, H, F, T: ?Sized, M>
    NativeDriver<cordis_kernel::reversible_value::function::Body<P, F>, H, Slot<T, M>>
{
    pub fn run_recorded_value_root<C, G, A, R, X>(
        &mut self,
        id: usize,
        owner: &mut RecordedExecution<C, G, A, R, T, M, X>,
    ) -> Result<
        cordis_kernel::reversible_value::function::RegisteredReport,
        cordis_kernel::reversible_value::function::AdmissionError,
    > {
        if !self.owns_execution(id, owner.execution()) {
            return Err(cordis_kernel::reversible_value::function::AdmissionError::WrongOwner);
        }

        owner.run_value_root(&mut self.state, id)
    }
    pub fn run_recorded_service_root<C, G, A, R, X>(
        &mut self,
        id: usize,
        owner: &mut RecordedExecution<C, G, A, R, T, M, X>,
    ) -> Result<
        cordis_kernel::reversible_value::service_function::RegisteredReport,
        cordis_kernel::reversible_value::service_function::AdmissionError,
    > {
        if !self.owns_execution(id, owner.execution()) {
            return Err(
                cordis_kernel::reversible_value::service_function::AdmissionError::WrongOwner,
            );
        }

        owner.run_service_root(&mut self.state, id)
    }
}

impl<P, H, T: ?Sized, M> NativeDriver<P, H, Slot<T, M>> {
    /// Keep the authentic Unload and terminal queue evidence with the result.
    pub fn release_recorded_controlled_observed<C, G, A, R, X, E>(
        &mut self,
        id: usize,
        owner: &mut RecordedExecution<C, G, A, R, T, M, X>,
        control: &mut cordis_kernel::poll_control::PollControl<E>,
    ) -> ReleaseOutcome<A, R, T, M, X> {
        if !self.owns_execution(id, owner.execution()) {
            return cordis_kernel::lifecycle_state::native::runtime::rejected_release();
        }

        if !self.owns_poll_control(control) {
            return cordis_kernel::lifecycle_state::native::runtime::rejected_release();
        }
        owner.release_controlled(&mut self.state, id, control)
    }
}

#[cfg(test)]
mod control_tests;
#[cfg(test)]
mod provenance_tests;
#[cfg(test)]
mod test_support;

#[cfg(test)]
mod authority_tests;

#[cfg(test)]
mod child_tests;

#[cfg(test)]
mod snapshot_tests;
