//! Shared lifecycle arbitration for Rust and JavaScript executors.
//!
//! This layer owns the kernel and the verified setup/cleanup result protocol.
//! Executors supply availability and failure facts, retain their own values and
//! futures, and run callbacks only after the borrow of this driver has ended.
//! Ownership restoration order is an executor policy: retirement does not add
//! an implicit dependency between a parent and its children.
use crate::{ActionKind, ActionTicket, DriverError};
use cordis_kernel::action_ledger::{
    ActionError, ActionKind as KernelActionKind, ActionTicket as KernelActionTicket,
};
pub use cordis_kernel::lifecycle_actions::CleanupOutcome;
use cordis_kernel::lifecycle_state::cleanup::{CleanupCommand, CleanupError};
use cordis_kernel::lifecycle_state::LifecycleState;
use cordis_kernel::{Error, Kernel, Phase, Port};
use std::collections::BTreeMap;
use std::ops::Deref;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_DOMAIN: AtomicU64 = AtomicU64::new(1);

/// Observations that require access to executor-owned values or failure state.
#[derive(Clone, Copy, Debug)]
pub struct HostStatus {
    pub available: bool,
    pub failed: bool,
    pub restart: bool,
}

/// The next control transition; it never invokes executor code.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Decision {
    Withdraw,
    Begin,
    BeginCleanup,
    Remove,
}

/// One control graph and its verified action and cleanup-result protocol.
///
/// Dereferencing permits kernel observations, but intentionally provides no
/// mutable access that could bypass the cleanup-result protocol.
pub struct LifecycleDriver {
    state: LifecycleState,
    // Serialization views only; the verified protocol authorizes transitions.
    pending_views: BTreeMap<usize, ActionTicket>,
}
impl Deref for LifecycleDriver {
    type Target = Kernel;
    fn deref(&self) -> &Kernel {
        self.state.kernel()
    }
}
impl LifecycleDriver {
    pub fn new() -> Result<Self, DriverError> {
        let domain = NEXT_DOMAIN
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
            .map_err(|_| DriverError::new("Capacity", "domain identity exhausted"))?;
        Ok(Self {
            state: LifecycleState::new(domain),
            pending_views: BTreeMap::new(),
        })
    }
    pub fn domain(&self) -> u64 {
        self.state.domain()
    }
    /// Decide using current kernel facts. Hosts must recompute availability
    /// after callbacks; a prior decision is not a capability to mutate state.
    pub fn decision(&self, id: usize, status: HostStatus) -> Option<Decision> {
        match self.phase(id)? {
            Phase::Loading | Phase::Active
                if !self.coherent(id, status.restart) || !status.available || status.failed =>
            {
                Some(Decision::Withdraw)
            }
            Phase::Unloading if !self.cleanup_started(id) && !self.state.blocked(id) => {
                Some(Decision::BeginCleanup)
            }
            Phase::Inactive
                if self.retired(id) && self.children(id).is_empty() && !self.state.blocked(id) =>
            {
                Some(Decision::Remove)
            }
            Phase::Inactive
                if !self.retired(id)
                    && !status.failed
                    && status.available
                    && !self.state.blocked(id)
                    && self.target(id).is_some()
                    && !self.children(id).iter().any(|child| self.retired(*child)) =>
            {
                Some(Decision::Begin)
            }
            _ => None,
        }
    }
    pub fn coherent(&self, id: usize, restart: bool) -> bool {
        !self.retired(id)
            && !restart
            && self.target(id).is_some_and(|target| {
                cordis_kernel::episode::same_bindings(&target, &self.committed(id))
            })
            && (self.phase(id) != Some(Phase::Loading) || self.check_iteration(id).is_ok())
    }
    pub fn insert(
        &mut self,
        parent: Option<usize>,
        dependencies: Vec<Port>,
        provisions: Vec<Port>,
    ) -> Result<usize, Error> {
        self.state.insert(parent, dependencies, provisions)
    }
    pub fn declare_provision(&mut self, id: usize, port: Port) -> Result<(), Error> {
        self.state.declare_provision(id, port)
    }
    pub fn configure_pending_dependencies(
        &mut self,
        id: usize,
        dependencies: Vec<Port>,
    ) -> Result<(), Error> {
        self.state.configure_pending_dependencies(id, dependencies)
    }
    pub fn release_provision(&mut self, id: usize, port: Port) -> Result<(), Error> {
        self.state.release_provision(id, port)
    }
    /// Validate a complete action batch before making its first transition.
    pub fn ensure_action_capacity(&self, count: usize) -> Result<(), Error> {
        let count = u64::try_from(count).map_err(|_| Error::Capacity)?;
        self.state.check_capacity(count).map_err(ledger_error)
    }
    /// Admit setup and register its ownership before any executor sees it.
    pub fn begin(&mut self, id: usize) -> Result<(), Error> {
        let ticket = self.state.begin(id)?;
        self.pending_views.insert(id, host_ticket(ticket));
        Ok(())
    }
    pub fn pending_action(&self, id: usize) -> Option<&ActionTicket> {
        self.pending_views.get(&id)
    }
    /// Consume a setup result exactly once. Cleanup requires an explicit outcome;
    /// this setup-only entry point cannot authorize dependency release.
    /// Withdrawal never discards an outstanding setup ticket.
    pub fn complete_action(&mut self, ticket: &ActionTicket) -> Result<(), DriverError> {
        self.state
            .execute_cleanup(CleanupCommand::SettleSetup {
                ticket: kernel_ticket(ticket),
            })
            .map_err(cleanup_completion_error)?;
        self.pending_views.remove(&ticket.id);
        Ok(())
    }
    /// Record an exact cleanup attempt's outcome. Failed attempts retain a
    /// blocking receipt until explicit retry; only Succeeded or Drained can
    /// authorize finish_cleanup. The host remains responsible for that report.
    pub fn complete_cleanup(
        &mut self,
        ticket: &ActionTicket,
        outcome: CleanupOutcome,
    ) -> Result<(), DriverError> {
        self.state
            .execute_cleanup(CleanupCommand::Report {
                ticket: kernel_ticket(ticket),
                outcome,
            })
            .map_err(cleanup_completion_error)?;
        self.pending_views.remove(&ticket.id);
        Ok(())
    }
    /// Rust executors retain the action in this driver while polling their
    /// futures. Acknowledge it only when all admitted setup work has landed.
    pub fn settle_setup(&mut self, id: usize) -> Result<(), DriverError> {
        if let Some(ticket) = self.state.pending(id).map(host_ticket) {
            if ticket.kind != ActionKind::Setup {
                return Err(DriverError::new(
                    "InvalidState",
                    "setup is already restoring",
                ));
            }
            self.complete_action(&ticket)?;
        }
        Ok(())
    }
    pub fn finish(&mut self, id: usize) -> Result<(), Error> {
        self.state.finish(id)
    }
    pub fn leave(&mut self, id: usize) -> Result<(), Error> {
        self.state
            .execute_cleanup(CleanupCommand::Withdraw { id })
            .map(|_| ())
            .map_err(cleanup_control_error)
    }
    pub fn retire(&mut self, id: usize) -> Result<(), Error> {
        self.state
            .execute_cleanup(CleanupCommand::Retire { id })
            .map(|_| ())
            .map_err(cleanup_control_error)
    }
    pub fn begin_cleanup(&mut self, id: usize) -> Result<(), Error> {
        let ticket = self
            .state
            .execute_cleanup(CleanupCommand::Request {
                id,
                reservation: false,
            })
            .map_err(cleanup_control_error)?
            .expect("cleanup request issues a ticket");
        self.pending_views.insert(id, host_ticket(ticket));
        Ok(())
    }
    /// Restore host resources registered while a fiber was reserved, before
    /// its first kernel episode. This is a host extension, not a paper Step.
    pub fn begin_reservation_cleanup(&mut self, id: usize) -> Result<(), Error> {
        let ticket = self
            .state
            .execute_cleanup(CleanupCommand::Request {
                id,
                reservation: true,
            })
            .map_err(cleanup_control_error)?
            .expect("reservation cleanup issues a ticket");
        self.pending_views.insert(id, host_ticket(ticket));
        Ok(())
    }
    pub fn retry_cleanup(&mut self, id: usize) -> Result<ActionTicket, Error> {
        let ticket = host_ticket(
            self.state
                .execute_cleanup(CleanupCommand::Retry { id })
                .map_err(cleanup_control_error)?
                .expect("cleanup retry issues a ticket"),
        );
        self.pending_views.insert(id, ticket.clone());
        Ok(ticket)
    }
    pub fn finish_cleanup(&mut self, id: usize) -> Result<(), Error> {
        self.state
            .execute_cleanup(CleanupCommand::Release {
                id,
                reservation: false,
            })
            .map(|_| ())
            .map_err(cleanup_control_error)
    }
    /// Finish a reported cleanup only after its checked resource batch succeeds.
    pub fn finish_cleanup_resources(
        &mut self,
        registry: &mut cordis_kernel::publication::PublicationRegistry,
        id: usize,
        reservation: bool,
        leases: &[cordis_kernel::publication::LeaseId],
        publications: &[cordis_kernel::publication::PublicationId],
    ) -> Result<Vec<cordis_kernel::publication::ReleasedPublication>, DriverError> {
        use cordis_kernel::lifecycle_actions::resources::CleanupReleaseError;
        self.state
            .finish_cleanup_resources(registry, id, reservation, leases, publications)
            .map_err(|error| match error {
                CleanupReleaseError::Lifecycle(error) => error.into(),
                CleanupReleaseError::Publication(error) => error.into(),
            })
    }
    pub fn finish_reservation_cleanup(&mut self, id: usize) -> Result<(), Error> {
        self.state
            .execute_cleanup(CleanupCommand::Release {
                id,
                reservation: true,
            })
            .map(|_| ())
            .map_err(cleanup_control_error)
    }
    pub fn remove(&mut self, id: usize) -> Result<(), Error> {
        self.state
            .execute_cleanup(CleanupCommand::Remove { id })
            .map(|_| ())
            .map_err(cleanup_control_error)
    }
    pub fn compact_bindings(&mut self) -> usize {
        self.state.compact_bindings()
    }
    pub fn compact_declarations(&mut self) -> usize {
        self.state.compact_declarations()
    }
}

fn cleanup_control_error(error: CleanupError) -> Error {
    match error {
        CleanupError::Control(error) => error,
        CleanupError::Reply(error) => ledger_error(error),
    }
}
fn cleanup_completion_error(error: CleanupError) -> DriverError {
    match error {
        CleanupError::Control(error) => error.into(),
        CleanupError::Reply(error) => completion_error(error),
    }
}
fn ledger_error(error: ActionError) -> Error {
    match error {
        ActionError::Capacity => Error::Capacity,
        ActionError::Pending | ActionError::WrongDomain | ActionError::Stale => Error::InvalidState,
    }
}
fn completion_error(error: ActionError) -> DriverError {
    match error {
        ActionError::WrongDomain => {
            DriverError::new("WrongDomain", "action belongs to another driver")
        }
        ActionError::Stale => DriverError::new(
            "StaleAction",
            "action is unknown, already completed, or has the wrong kind",
        ),
        ActionError::Capacity | ActionError::Pending => {
            DriverError::new("InvalidState", "invalid action completion")
        }
    }
}
fn kernel_kind(kind: ActionKind) -> KernelActionKind {
    match kind {
        ActionKind::Setup => KernelActionKind::Setup,
        ActionKind::Cleanup => KernelActionKind::Cleanup,
    }
}
fn kernel_ticket(ticket: &ActionTicket) -> KernelActionTicket {
    KernelActionTicket {
        domain: ticket.domain,
        id: ticket.id,
        generation: ticket.generation,
        action: ticket.action,
        kind: kernel_kind(ticket.kind),
    }
}
fn host_ticket(ticket: KernelActionTicket) -> ActionTicket {
    ActionTicket {
        domain: ticket.domain,
        id: ticket.id,
        generation: ticket.generation,
        action: ticket.action,
        kind: match ticket.kind {
            KernelActionKind::Setup => ActionKind::Setup,
            KernelActionKind::Cleanup => ActionKind::Cleanup,
        },
    }
}
