//! Serialization adapter for the single verified Node protocol owner.
//! No mutable reference to its constituent owners escapes this module.
use crate::shared::{self, Decision, HostStatus};
use crate::{ActionTicket, DriverError};
use cordis_kernel::availability::admission::AdmissionError;
use cordis_kernel::lifecycle_state::cleanup::CleanupCommand;
use cordis_kernel::lifecycle_state::LifecycleState;
use cordis_kernel::node_runtime::NodeRuntime;
use cordis_kernel::publication::values::{PublicationStore, RejectedValue, ReleasedValue};
use cordis_kernel::publication::PublicationId;
use cordis_kernel::{Error, Kernel, Port};
use std::ops::Deref;

pub(crate) struct NodeDriver {
    pub core: NodeRuntime,
}
impl Deref for NodeDriver {
    type Target = Kernel;
    fn deref(&self) -> &Kernel {
        self.core.state().kernel()
    }
}
fn release_error(
    e: cordis_kernel::lifecycle_actions::resources::CleanupReleaseError,
) -> DriverError {
    use cordis_kernel::lifecycle_actions::resources::CleanupReleaseError;
    match e {
        CleanupReleaseError::Lifecycle(e) => e.into(),
        CleanupReleaseError::Publication(e) => e.into(),
    }
}
impl NodeDriver {
    pub fn new() -> Result<Self, DriverError> {
        Ok(Self {
            core: NodeRuntime::new(shared::allocate_domain()?),
        })
    }
    pub fn domain(&self) -> u64 {
        self.core.state().domain()
    }
    pub fn state(&self) -> &LifecycleState {
        self.core.state()
    }
    pub fn store(&self) -> &PublicationStore<u64> {
        self.core.store()
    }
    pub fn decision(&self, id: usize, status: HostStatus) -> Option<Decision> {
        shared::decision(self.state(), id, status)
    }
    pub fn mount(
        &mut self,
        parent: Option<usize>,
        dependencies: Vec<Port>,
        provisions: Vec<Port>,
        sealed: bool,
    ) -> Result<usize, DriverError> {
        self.core
            .mount(parent, dependencies, provisions, sealed)
            .map_err(Into::into)
    }
    pub fn ensure_action_capacity(&self, count: usize) -> Result<(), Error> {
        self.state()
            .check_capacity(u64::try_from(count).map_err(|_| Error::Capacity)?)
            .map_err(shared::ledger_error)
    }
    pub fn begin_checked(
        &mut self,
        id: usize,
    ) -> Result<cordis_kernel::action_ledger::ActionTicket, DriverError> {
        self.core.begin(id).map_err(|e| match e {
            AdmissionError::Unavailable => {
                DriverError::new("Unavailable", "setup dependencies are unavailable")
            }
            AdmissionError::Lifecycle(e) => e.into(),
            AdmissionError::Publication(e) => e.into(),
        })
    }
    // The wire view is derived from the authoritative pending ticket each time.
    pub fn pending_action(&self, id: usize) -> Option<ActionTicket> {
        self.state().pending(id).map(shared::host_ticket)
    }
    pub fn complete(
        &mut self,
        ticket: &ActionTicket,
        error: Option<String>,
    ) -> Result<(), DriverError> {
        self.core
            .complete(shared::kernel_ticket(ticket), error)
            .map(|_| ())
            .map_err(shared::cleanup_completion_error)
    }
    pub fn finish(&mut self, id: usize) -> Result<(), Error> {
        self.core.finish(id)
    }
    pub fn leave(&mut self, id: usize) -> Result<(), Error> {
        self.core
            .cleanup(CleanupCommand::Withdraw { id })
            .map(|_| ())
            .map_err(shared::cleanup_control_error)
    }
    pub fn retire(&mut self, id: usize) -> Result<(), Error> {
        self.core
            .cleanup(CleanupCommand::Retire { id })
            .map(|_| ())
            .map_err(shared::cleanup_control_error)
    }
    pub fn remove(&mut self, id: usize) -> Result<(), Error> {
        self.core
            .cleanup(CleanupCommand::Remove { id })
            .map(|_| ())
            .map_err(shared::cleanup_control_error)
    }
    pub fn begin_cleanup(&mut self, id: usize) -> Result<(), Error> {
        self.core
            .cleanup(CleanupCommand::Request {
                id,
                reservation: false,
            })
            .map(|_| ())
            .map_err(shared::cleanup_control_error)
    }
    pub fn begin_reservation_cleanup(&mut self, id: usize) -> Result<(), Error> {
        self.core
            .cleanup(CleanupCommand::Request {
                id,
                reservation: true,
            })
            .map(|_| ())
            .map_err(shared::cleanup_control_error)
    }
    pub fn retry_cleanup(&mut self, id: usize) -> Result<ActionTicket, Error> {
        self.core
            .cleanup(CleanupCommand::Retry { id })
            .map_err(shared::cleanup_control_error)
            .map(|t| shared::host_ticket(t.expect("cleanup retry issues a ticket")))
    }
    pub fn replace_value(
        &mut self,
        id: PublicationId,
        owner: usize,
        generation: u64,
        value: u64,
    ) -> Result<u64, RejectedValue<u64>> {
        self.core.replace(id, owner, generation, value)
    }
    pub fn finish_reservation_values(
        &mut self,
        id: usize,
    ) -> Result<Vec<ReleasedValue<u64>>, DriverError> {
        self.core
            .release_owned_reservation(id)
            .map_err(release_error)
    }
    pub fn finish_admission_values(
        &mut self,
        id: usize,
    ) -> Result<Vec<ReleasedValue<u64>>, DriverError> {
        self.core.release_owned(id).map_err(release_error)
    }
    pub fn compact_bindings(&mut self) -> usize {
        self.core.compact_bindings()
    }
    pub fn compact_declarations(&mut self) -> usize {
        self.core.compact_declarations()
    }
}
