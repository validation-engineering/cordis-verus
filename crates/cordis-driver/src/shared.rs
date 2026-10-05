//! Shared lifecycle arbitration for Rust and JavaScript executors.
//!
//! This layer owns the kernel and the outstanding setup/cleanup action ledger.
//! Executors supply availability and failure facts, retain their own values and
//! futures, and run callbacks only after the borrow of this driver has ended.
//! Ownership restoration order is an executor policy: retirement does not add
//! an implicit dependency between a parent and its children.
use crate::{ActionKind, ActionTicket, DriverError};
use cordis_kernel::action_ledger::{
    ActionError, ActionKind as KernelActionKind, ActionLedger, ActionTicket as KernelActionTicket,
};
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

/// One control graph and its exactly-once outstanding action ownership.
///
/// Dereferencing permits kernel observations, but intentionally provides no
/// mutable access that could bypass the action ledger.
pub struct LifecycleDriver {
    kernel: Kernel,
    actions: ActionLedger,
    // Serialization views only; the verified ledger authorizes transitions.
    pending_views: BTreeMap<usize, ActionTicket>,
}
impl Deref for LifecycleDriver {
    type Target = Kernel;
    fn deref(&self) -> &Kernel {
        &self.kernel
    }
}
impl LifecycleDriver {
    pub fn new() -> Result<Self, DriverError> {
        let domain = NEXT_DOMAIN
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |id| id.checked_add(1))
            .map_err(|_| DriverError::new("Capacity", "domain identity exhausted"))?;
        Ok(Self {
            kernel: Kernel::new(),
            actions: ActionLedger::new(domain),
            pending_views: BTreeMap::new(),
        })
    }
    pub fn domain(&self) -> u64 {
        self.actions.domain()
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
            Phase::Unloading if !self.cleanup_started(id) && self.actions.pending(id).is_none() => {
                Some(Decision::BeginCleanup)
            }
            Phase::Inactive
                if self.retired(id)
                    && self.children(id).is_empty()
                    && self.actions.pending(id).is_none() =>
            {
                Some(Decision::Remove)
            }
            Phase::Inactive
                if !self.retired(id)
                    && !status.failed
                    && status.available
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
            && self.target(id).as_ref() == Some(&self.committed(id))
            && (self.phase(id) != Some(Phase::Loading) || self.check_iteration(id).is_ok())
    }
    pub fn insert(
        &mut self,
        parent: Option<usize>,
        dependencies: Vec<Port>,
        provisions: Vec<Port>,
    ) -> Result<usize, Error> {
        self.kernel.insert(parent, dependencies, provisions)
    }
    pub fn declare_provision(&mut self, id: usize, port: Port) -> Result<(), Error> {
        self.kernel.declare_provision(id, port)
    }
    pub fn configure_pending_dependencies(
        &mut self,
        id: usize,
        dependencies: Vec<Port>,
    ) -> Result<(), Error> {
        self.kernel.configure_pending_dependencies(id, dependencies)
    }
    pub fn release_provision(&mut self, id: usize, port: Port) -> Result<(), Error> {
        self.kernel.release_provision(id, port)
    }
    /// Validate a complete action batch before making its first transition.
    pub fn ensure_action_capacity(&self, count: usize) -> Result<(), Error> {
        let count = u64::try_from(count).map_err(|_| Error::Capacity)?;
        self.actions.check_capacity(count).map_err(ledger_error)
    }
    fn reserve_action(&self, id: usize) -> Result<(), Error> {
        self.actions.can_issue(id).map_err(ledger_error)
    }
    fn issue(&mut self, id: usize, kind: ActionKind) {
        let generation = self
            .episode_generation(id)
            .expect("registered action owner");
        let ticket = self
            .actions
            .issue(id, generation, kernel_kind(kind))
            .expect("action ownership and capacity checked before kernel admission");
        self.pending_views.insert(id, host_ticket(ticket));
    }
    /// Admit setup and register its ownership before any executor sees it.
    pub fn begin(&mut self, id: usize) -> Result<(), Error> {
        self.reserve_action(id)?;
        self.kernel.begin(id)?;
        self.issue(id, ActionKind::Setup);
        Ok(())
    }
    pub fn pending_action(&self, id: usize) -> Option<&ActionTicket> {
        self.pending_views.get(&id)
    }
    /// Consume a result exactly once. Withdrawal never discards an outstanding
    /// setup ticket: its eventual inverse still belongs to the original episode.
    pub fn complete_action(&mut self, ticket: &ActionTicket) -> Result<(), DriverError> {
        self.actions
            .complete(kernel_ticket(ticket))
            .map_err(|error| match error {
                ActionError::WrongDomain => {
                    DriverError::new("WrongDomain", "action belongs to another driver")
                }
                ActionError::Stale => {
                    DriverError::new("StaleAction", "action is unknown or already completed")
                }
                ActionError::Capacity | ActionError::Pending => {
                    DriverError::new("InvalidState", "invalid action completion")
                }
            })?;
        self.pending_views.remove(&ticket.id);
        Ok(())
    }
    /// Rust executors retain the action in this driver while polling their
    /// futures. Acknowledge it only when all admitted setup work has landed.
    pub fn settle_setup(&mut self, id: usize) -> Result<(), DriverError> {
        if let Some(ticket) = self.actions.pending(id).map(host_ticket) {
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
        if self.actions.pending(id).is_some() {
            return Err(Error::InvalidState);
        }
        self.kernel.finish(id)
    }
    pub fn leave(&mut self, id: usize) -> Result<(), Error> {
        self.kernel.leave(id)
    }
    pub fn retire(&mut self, id: usize) -> Result<(), Error> {
        self.kernel.retire(id)
    }
    pub fn begin_cleanup(&mut self, id: usize) -> Result<(), Error> {
        // An outstanding action may still be using the committed dependencies.
        if self.actions.pending(id).is_some() {
            return Err(Error::Relied);
        }
        self.reserve_action(id)?;
        self.kernel.begin_cleanup(id)?;
        self.issue(id, ActionKind::Cleanup);
        Ok(())
    }
    /// Restore host resources registered while a fiber was reserved, before
    /// its first kernel episode. This is a host extension, not a paper Step:
    /// the kernel remains Inactive while the verified ledger owns the action.
    pub fn begin_reservation_cleanup(&mut self, id: usize) -> Result<(), Error> {
        if !self.kernel.contains(id) {
            return Err(Error::Unknown);
        }
        if !self.kernel.retired(id)
            || self.kernel.phase(id) != Some(Phase::Inactive)
            || self.kernel.episode_generation(id) != Some(0)
        {
            return Err(Error::InvalidState);
        }
        self.reserve_action(id)?;
        self.issue(id, ActionKind::Cleanup);
        Ok(())
    }
    pub fn retry_cleanup(&mut self, id: usize) -> Result<ActionTicket, Error> {
        if !self.cleanup_started(id) || self.phase(id) != Some(Phase::Unloading) {
            return Err(Error::InvalidState);
        }
        self.reserve_action(id)?;
        self.issue(id, ActionKind::Cleanup);
        Ok(self.pending_views[&id].clone())
    }
    pub fn finish_cleanup(&mut self, id: usize) -> Result<(), Error> {
        if self.actions.pending(id).is_some() {
            return Err(Error::InvalidState);
        }
        self.kernel.finish_cleanup(id)
    }
    pub fn remove(&mut self, id: usize) -> Result<(), Error> {
        if self.actions.pending(id).is_some() {
            return Err(Error::InvalidState);
        }
        self.kernel.remove(id)
    }
    pub fn compact_bindings(&mut self) -> usize {
        self.kernel.compact_bindings()
    }
    pub fn compact_declarations(&mut self) -> usize {
        self.kernel.compact_declarations()
    }
}

fn ledger_error(error: ActionError) -> Error {
    match error {
        ActionError::Capacity => Error::Capacity,
        ActionError::Pending | ActionError::WrongDomain | ActionError::Stale => Error::InvalidState,
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
