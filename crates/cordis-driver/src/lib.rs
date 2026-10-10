//! Value-independent lifecycle driving for native hosts.
//!
//! Commands never execute callbacks. An executor receives owned actions after
//! the mutable driver borrow ends and submits one completion for each ticket.
//! This host adapter is ordinary Rust; kernel proofs do not prove its callbacks
//! or JSON translation. Dynamic publication admission is filtered here until
//! publication visibility has a full paper-model refinement.

mod availability;
mod protocol;
use availability::{Availability, Candidate};
pub use availability::{CheckAction, CheckTicket};
pub mod shared;
use cordis_kernel::publication::{LeaseId, PublicationError, PublicationId, PublicationRegistry};
use cordis_kernel::{Error as KernelError, Phase, Port};
pub use protocol::{ActionKind, ActionTicket, Command, HostAction, Profile, ServicePort};
use serde_json::{json, Value};
use shared::{CleanupOutcome, Decision, HostStatus, LifecycleDriver};
use std::collections::BTreeMap;
use std::fmt;

/// A rejected command leaves pending executor ownership intact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DriverError {
    pub code: &'static str,
    pub message: String,
}
impl DriverError {
    fn new(code: &'static str, message: impl Into<String>) -> Self {
        Self {
            code,
            message: message.into(),
        }
    }
}
impl fmt::Display for DriverError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.code, self.message)
    }
}
impl std::error::Error for DriverError {}
impl From<KernelError> for DriverError {
    fn from(value: KernelError) -> Self {
        Self::new("Kernel", format!("{value:?}"))
    }
}
impl From<PublicationError> for DriverError {
    fn from(value: PublicationError) -> Self {
        Self::new("Publication", format!("{value:?}"))
    }
}

#[derive(Clone, Copy)]
struct ResourceBinding {
    port: Port,
    publication: PublicationId,
    lease: LeaseId,
}
struct Node {
    parent: Option<usize>,
    provisions: Vec<Port>,
    dependencies: Vec<ServicePort>,
    sealed: bool,
    prepared: bool,
    prepared_cleanup: bool,
    publications: Vec<PublicationId>,
    restoring_publications: Vec<PublicationId>,
    resources: Vec<ResourceBinding>,
    pending: Option<ActionTicket>,
    failed: Option<String>,
    cleanup_failed: bool,
    restart: bool,
}

/// One authoritative lifecycle domain. Values are opaque host-owned handles.
pub struct Driver {
    profile: Profile,
    configured: bool,
    domain: u64,
    kernel: LifecycleDriver,
    publications: PublicationRegistry,
    nodes: BTreeMap<usize, Node>,
    values: BTreeMap<usize, u64>,
    next_slot: usize,
    released: Vec<u64>,
    checked: BTreeMap<usize, u64>,
    availability: Availability,
    declarations: BTreeMap<(u64, u64), usize>,
    maintenance_changes: usize,
}
impl Driver {
    /// Allocate a process-unique domain identity, failing rather than wrapping.
    pub fn new() -> Result<Self, DriverError> {
        let kernel = LifecycleDriver::new()?;
        let domain = kernel.domain();
        Ok(Self {
            profile: Profile::Cordis,
            configured: false,
            domain,
            kernel,
            publications: PublicationRegistry::for_domain(domain),
            nodes: BTreeMap::new(),
            values: BTreeMap::new(),
            next_slot: 0,
            released: Vec::new(),
            checked: BTreeMap::new(),
            availability: Availability::default(),
            declarations: BTreeMap::new(),
            maintenance_changes: 0,
        })
    }

    // Use the verified stable filters also used by the ordinary Rust Runtime.
    // They retain live commitments even while another inverse is pending or
    // failed. Identity/publication records are deliberately not reused. Released
    // lease records are reclaimed immediately without reusing their identities.
    fn maintain_history(&mut self) {
        self.maintenance_changes += 1;
        if self.maintenance_changes >= 256 {
            self.kernel.compact_bindings();
            self.kernel.compact_declarations();
            self.maintenance_changes = 0;
        }
    }

    /// The domain carried by all completion tickets.
    pub fn domain(&self) -> u64 {
        self.domain
    }

    /// Insert declarations without executing setup. Parent ownership is not an
    /// implicit dependency; child setup is separately gated by its own ports.
    pub fn mount(
        &mut self,
        parent: Option<usize>,
        dependencies: Vec<ServicePort>,
        provisions: Vec<ServicePort>,
    ) -> Result<usize, DriverError> {
        if let Some(parent) = parent {
            if !self.kernel.contains(parent)
                || self.kernel.retired(parent)
                || self.kernel.phase(parent) == Some(Phase::Unloading)
            {
                return Err(DriverError::new(
                    "ParentClosed",
                    "parent cannot admit a child",
                ));
            }
        }
        let provisions: Vec<Port> = provisions.into_iter().map(Into::into).collect();
        let id = self.kernel.insert(
            parent,
            dependencies.iter().copied().map(Into::into).collect(),
            provisions.clone(),
        )?;
        // A default profile is frozen by the first successful allocation,
        // even after every node is later removed from this domain.
        self.configured = true;
        self.nodes.insert(
            id,
            Node {
                parent,
                provisions,
                dependencies,
                sealed: true,
                prepared: false,
                prepared_cleanup: false,
                publications: Vec::new(),
                restoring_publications: Vec::new(),
                resources: Vec::new(),
                pending: None,
                failed: None,
                cleanup_failed: false,
                restart: false,
            },
        );
        Ok(id)
    }

    /// Request recursive ownership retirement. Pending actions remain owned and
    /// must still complete before their episode can restore resources.
    pub fn retire(&mut self, id: usize) -> Result<(), DriverError> {
        self.kernel.retire(id)?;
        let mut pending = self.kernel.children(id);
        while let Some(child) = pending.pop() {
            self.kernel.retire(child)?;
            pending.extend(self.kernel.children(child));
        }
        Ok(())
    }

    pub fn restart(&mut self, id: usize) -> Result<(), DriverError> {
        if self.kernel.retired(id) {
            return Err(DriverError::new(
                "Retired",
                "cannot restart a retired plugin",
            ));
        }
        let node = self.nodes.get_mut(&id).ok_or(KernelError::Unknown)?;
        node.failed = None;
        node.restart = self.kernel.phase(id) != Some(Phase::Inactive);
        Ok(())
    }

    /// Latch a failure of the current host episode and close its admission.
    /// This is for episode-owned work (such as a rejected child request), not a
    /// fabricated action completion. An outstanding setup ticket remains owned
    /// by its executor and must actually land before cleanup can begin. Normal
    /// committed-consumer and cleanup-failure guards still govern restoration.
    pub fn fail_episode(
        &mut self,
        id: usize,
        generation: u64,
        error: String,
    ) -> Result<(), DriverError> {
        self.validate(id, generation)?;
        if !matches!(self.kernel.phase(id), Some(Phase::Loading | Phase::Active)) {
            return Err(DriverError::new(
                "AdmissionClosed",
                "no active episode to fail",
            ));
        }
        self.nodes.get_mut(&id).unwrap().failed.get_or_insert(error);
        self.withdraw(id)
    }

    /// Admit host effects for a reserved fiber before its first activation.
    /// Retirement drains this journal through a generation-zero cleanup ticket.
    pub fn prepare(&mut self, id: usize) -> Result<u64, DriverError> {
        if !self.kernel.contains(id) {
            return Err(KernelError::Unknown.into());
        }
        if self.kernel.retired(id)
            || self.kernel.phase(id) != Some(Phase::Inactive)
            || self.kernel.episode_generation(id) != Some(0)
        {
            return Err(DriverError::new(
                "AdmissionClosed",
                "reservation cannot acquire new resources",
            ));
        }
        self.nodes.get_mut(&id).unwrap().prepared = true;
        Ok(0)
    }

    /// Validate admission for new resource work, including escaped async calls.
    pub fn validate(&self, id: usize, generation: u64) -> Result<(), DriverError> {
        if self.kernel.episode_generation(id) != Some(generation) {
            return Err(DriverError::new(
                "StaleEpisode",
                "plugin generation is not current",
            ));
        }
        if generation == 0
            && !self.kernel.retired(id)
            && self.kernel.phase(id) == Some(Phase::Inactive)
            && self.nodes.get(&id).is_some_and(|node| node.prepared)
        {
            return Ok(());
        }
        if self.kernel.retired(id)
            || !matches!(self.kernel.phase(id), Some(Phase::Loading | Phase::Active))
        {
            return Err(DriverError::new(
                "AdmissionClosed",
                "episode cannot acquire new resources",
            ));
        }
        Ok(())
    }

    /// Publish an opaque value while retaining the logical provider identity.
    pub fn publish(
        &mut self,
        id: usize,
        generation: u64,
        port: ServicePort,
        value: u64,
    ) -> Result<usize, DriverError> {
        self.validate(id, generation)?;
        let next_slot = self
            .next_slot
            .checked_add(1)
            .ok_or_else(|| DriverError::new("Capacity", "value slot identity exhausted"))?;
        let port: Port = port.into();
        if self.publications.resolve(port).is_some() {
            return Err(PublicationError::Conflict.into());
        }
        match self.kernel.declare_provision(id, port) {
            Ok(()) => {
                if !self.nodes[&id].provisions.contains(&port) {
                    self.declarations.insert((port.key, port.realm), id);
                }
            }
            Err(KernelError::Conflict)
                if self.declarations.contains_key(&(port.key, port.realm)) => {}
            Err(error) => return Err(error.into()),
        }
        let publication = self
            .publications
            .publish(id, generation, port, self.next_slot)?;
        self.values.insert(self.next_slot, value);
        self.next_slot = next_slot;
        self.nodes
            .get_mut(&id)
            .unwrap()
            .publications
            .push(publication);
        Ok(publication.0)
    }

    fn owned_publication(
        &self,
        id: usize,
        generation: u64,
        publication: usize,
    ) -> Result<cordis_kernel::publication::Publication, DriverError> {
        let entry = self
            .publications
            .entry(PublicationId(publication))
            .ok_or(PublicationError::Unknown)?;
        if entry.owner != id
            || entry.generation != generation
            || self.kernel.episode_generation(id) != Some(generation)
        {
            return Err(DriverError::new(
                "StalePublication",
                "publication does not belong to this episode",
            ));
        }
        Ok(entry)
    }

    /// Replace one slot without changing publication identity or notifying peers.
    pub fn set(
        &mut self,
        id: usize,
        generation: u64,
        publication: usize,
        value: u64,
    ) -> Result<(), DriverError> {
        self.validate(id, generation)?;
        let entry = self.owned_publication(id, generation, publication)?;
        if !entry.visible {
            return Err(PublicationError::Revoked.into());
        }
        if let Some(revision) = self.checked.get_mut(&publication) {
            *revision = revision
                .checked_add(1)
                .ok_or_else(|| DriverError::new("Capacity", "value revision exhausted"))?;
        }
        if let Some(previous) = self.values.insert(entry.slot, value) {
            if previous != value {
                self.released.push(previous);
            }
        }
        Ok(())
    }

    /// Withdrawal allows existing committed consumers to keep the old slot.
    /// Cleanup may idempotently revoke an already withdrawn publication.
    pub fn revoke(
        &mut self,
        id: usize,
        generation: u64,
        publication: usize,
    ) -> Result<(), DriverError> {
        self.owned_publication(id, generation, publication)?;
        self.publications.revoke(PublicationId(publication))?;
        self.nodes
            .get_mut(&id)
            .unwrap()
            .restoring_publications
            .retain(|id| id.0 != publication);
        Ok(())
    }

    /// Read a committed binding during setup, use, and cleanup. An unowned root
    /// lookup uses current visibility and confers no lifecycle consumer lease.
    pub fn resolve(
        &self,
        port: ServicePort,
        consumer: Option<usize>,
        generation: Option<u64>,
    ) -> Result<Option<Value>, DriverError> {
        let port: Port = port.into();
        let publication = if let Some(consumer) = consumer {
            let node = self.nodes.get(&consumer).ok_or(KernelError::Unknown)?;
            if let Some(generation) = generation {
                if self.kernel.episode_generation(consumer) != Some(generation) {
                    return Err(DriverError::new(
                        "StaleEpisode",
                        "lookup belongs to an earlier episode",
                    ));
                }
            }
            if let Some(binding) = node.resources.iter().find(|binding| binding.port == port) {
                self.publications.leased_slot(binding.lease)?;
                Some(binding.publication)
            } else {
                self.publications
                    .resolve(port)
                    .filter(|publication| {
                        self.publications
                            .entry(*publication)
                            .is_some_and(|entry| entry.owner == consumer)
                    })
                    .or_else(|| {
                        node.restoring_publications
                            .iter()
                            .rev()
                            .copied()
                            .find(|publication| {
                                self.publications
                                    .entry(*publication)
                                    .is_some_and(|entry| entry.port == port && entry.retained)
                            })
                    })
            }
        } else {
            self.publications.resolve(port).filter(|publication| {
                self.publications.entry(*publication).is_some_and(|entry| {
                    self.kernel.phase(entry.owner) == Some(Phase::Active)
                        && !self.kernel.retired(entry.owner)
                })
            })
        };
        let Some(publication) = publication else {
            return Ok(None);
        };
        let entry = self
            .publications
            .entry(publication)
            .ok_or(PublicationError::Unknown)?;
        let value = self.values.get(&entry.slot).ok_or_else(|| {
            DriverError::new("MissingValue", "retained publication has no host value")
        })?;
        Ok(Some(
            json!({"publication":publication.0.to_string(),"value":value.to_string(),"owner":entry.owner.to_string()}),
        ))
    }

    fn reconcile_publications(&mut self) -> Result<(), DriverError> {
        let declarations: Vec<_> = self
            .declarations
            .iter()
            .map(|(&port, &owner)| (port, owner))
            .collect();
        for ((key, realm), owner) in declarations {
            let port = Port { key, realm };
            let visible = self
                .publications
                .resolve(port)
                .and_then(|id| self.publications.entry(id));
            if visible.is_some_and(|p| p.owner == owner) {
                continue;
            }
            match self.kernel.release_provision(owner, port) {
                Ok(()) => {
                    self.declarations.remove(&(key, realm));
                }
                Err(KernelError::Relied) => continue,
                Err(error) => return Err(error.into()),
            }
            if let Some(next) = visible {
                if !self.kernel.retired(next.owner)
                    && (matches!(
                        self.kernel.phase(next.owner),
                        Some(Phase::Loading | Phase::Active)
                    ) || (self.kernel.phase(next.owner) == Some(Phase::Inactive)
                        && self.kernel.episode_generation(next.owner) == Some(0)
                        && self.nodes[&next.owner].prepared))
                {
                    self.kernel.declare_provision(next.owner, port)?;
                    self.declarations.insert((key, realm), next.owner);
                }
            }
        }
        Ok(())
    }
    fn reclaim(
        &mut self,
        id: usize,
        generation: u64,
        publication: usize,
    ) -> Result<bool, DriverError> {
        let entry = self.owned_publication(id, generation, publication)?;
        if !entry.retained {
            return Ok(true);
        }
        let slot = match self.publications.reclaim(PublicationId(publication)) {
            Ok(slot) => slot,
            Err(PublicationError::Relied) => return Ok(false),
            Err(error) => return Err(error.into()),
        };
        let node = self.nodes.get_mut(&id).unwrap();
        node.publications.retain(|p| p.0 != publication);
        node.restoring_publications.retain(|p| p.0 != publication);
        self.checked.remove(&publication);
        if let Some(value) = self.values.remove(&slot) {
            self.released.push(value);
        }
        self.reconcile_publications()?;
        Ok(true)
    }

    fn check_candidate(&self, consumer: usize, port: ServicePort) -> Option<Candidate> {
        let node = self.nodes.get(&consumer)?;
        if self.kernel.retired(consumer) || !node.dependencies.contains(&port) {
            return None;
        }
        let publication = self.publications.resolve(port.into())?;
        let entry = self.publications.entry(publication)?;
        if self.kernel.phase(entry.owner) != Some(Phase::Active) || self.kernel.retired(entry.owner)
        {
            return None;
        }
        Some(Candidate {
            consumer,
            port,
            publication: publication.0,
            value: *self.values.get(&entry.slot)?,
            value_revision: *self.checked.get(&publication.0)?,
        })
    }
    pub fn check_actions(&mut self) -> Result<Vec<CheckAction>, DriverError> {
        let mut candidates = Vec::new();
        for (&id, node) in &self.nodes {
            for port in &node.dependencies {
                if let Some(candidate) = self.check_candidate(id, *port) {
                    candidates.push(candidate);
                }
            }
        }
        self.availability.request(self.domain, candidates)
    }

    fn host_status(&self, id: usize) -> HostStatus {
        HostStatus {
            available: self.nodes[&id].sealed && self.ready(id),
            failed: self.nodes[&id].failed.is_some(),
            restart: self.nodes[&id].restart,
        }
    }

    fn ready(&self, id: usize) -> bool {
        self.kernel.target(id).is_some_and(|bindings| {
            bindings.iter().all(|binding| {
                self.publications
                    .resolve(Port {
                        key: binding.key,
                        realm: binding.realm,
                    })
                    .is_some_and(|publication| {
                        // No callback or mutation can interleave these observations.
                        // Keep the resolved identity instead of rescanning visibility.
                        self.publications.entry(publication).is_some_and(|entry| {
                            entry.owner == binding.provider
                                && !self.kernel.retired(entry.owner)
                                && (!self.checked.contains_key(&publication.0)
                                    || self.availability.available(
                                        id,
                                        entry.port.into(),
                                        publication.0,
                                    ))
                        })
                    })
            })
        })
    }

    fn next_ticket(&mut self, id: usize, kind: ActionKind) -> Result<ActionTicket, DriverError> {
        let ticket = self.kernel.pending_action(id).cloned().ok_or_else(|| {
            DriverError::new("MissingAction", "shared driver did not register an action")
        })?;
        if ticket.kind != kind {
            return Err(DriverError::new(
                "WrongAction",
                "shared action kind differs",
            ));
        }
        self.nodes.get_mut(&id).unwrap().pending = Some(ticket.clone());
        Ok(ticket)
    }

    fn withdraw_publications(&mut self, id: usize) -> Result<(), DriverError> {
        self.nodes.get_mut(&id).unwrap().restoring_publications = self.nodes[&id]
            .publications
            .iter()
            .copied()
            .filter(|publication| {
                self.publications
                    .entry(*publication)
                    .is_some_and(|entry| entry.visible)
            })
            .collect();
        for publication in &self.nodes[&id].publications {
            self.publications.revoke(*publication)?;
        }
        Ok(())
    }

    fn withdraw(&mut self, id: usize) -> Result<(), DriverError> {
        self.kernel.leave(id)?;
        self.withdraw_publications(id)?;
        // Nested setup instances are episode resources, so restart withdraws
        // their ownership too; ownership itself never invents a service edge.
        for child in self.kernel.children(id) {
            self.retire(child)?;
        }
        Ok(())
    }

    /// Bounded pump. Actions are returned only after all kernel mutations end.
    /// The executor must not discard actions because cancellation arrived later.
    pub fn drive(&mut self) -> Result<Vec<HostAction>, DriverError> {
        // At most one callback action per present node can be emitted without
        // an intervening completion. Reserve the entire batch before mutation.
        self.kernel.ensure_action_capacity(self.nodes.len())?;
        let mut actions = Vec::new();
        self.reconcile_publications()?;
        for _ in 0..256 {
            let mut progress = false;
            // Reach withdrawal closure before permitting any provider inverse.
            loop {
                let mut withdrew = false;
                for id in self.kernel.ids() {
                    // Availability resolves the complete dependency interface.
                    // Consult it only in phases that can take this transition;
                    // the shared decision still authorizes every eligible node.
                    if matches!(self.kernel.phase(id), Some(Phase::Loading | Phase::Active))
                        && self.kernel.decision(id, self.host_status(id))
                            == Some(Decision::Withdraw)
                    {
                        self.withdraw(id)?;
                        withdrew = true;
                        progress = true;
                    }
                }
                if !withdrew {
                    break;
                }
            }
            for id in self.kernel.ids() {
                let node = &self.nodes[&id];
                if self.kernel.phase(id) == Some(Phase::Unloading)
                    && self.kernel.decision(id, self.host_status(id))
                        == Some(Decision::BeginCleanup)
                    && node.pending.is_none()
                    && !node.cleanup_failed
                {
                    match self.kernel.begin_cleanup(id) {
                        Ok(()) => {
                            let ticket = self.next_ticket(id, ActionKind::Cleanup)?;
                            actions.push(HostAction::Cleanup { id, ticket });
                            progress = true;
                        }
                        Err(KernelError::Relied) => {}
                        Err(error) => return Err(error.into()),
                    }
                }
            }
            // A never-activated fiber may still own synchronous observer
            // effects. Its ledger action must land before registry removal.
            for id in self.kernel.ids() {
                let node = &self.nodes[&id];
                if node.prepared
                    && self.kernel.retired(id)
                    && self.kernel.phase(id) == Some(Phase::Inactive)
                    && node.pending.is_none()
                    && !node.cleanup_failed
                {
                    self.kernel.begin_reservation_cleanup(id)?;
                    self.withdraw_publications(id)?;
                    self.nodes.get_mut(&id).unwrap().prepared_cleanup = true;
                    let ticket = self.next_ticket(id, ActionKind::Cleanup)?;
                    actions.push(HostAction::Cleanup { id, ticket });
                    progress = true;
                }
            }
            for id in self.kernel.ids().into_iter().rev() {
                if self.kernel.phase(id) == Some(Phase::Inactive)
                    && !self.nodes[&id].prepared
                    && !self.nodes[&id].prepared_cleanup
                    && self.kernel.decision(id, self.host_status(id)) == Some(Decision::Remove)
                {
                    self.kernel.remove(id)?;
                    self.nodes.remove(&id);
                    self.declarations.retain(|_, owner| *owner != id);
                    self.availability.remove_consumer(id);
                    self.maintain_history();
                    actions.push(HostAction::Removed { id });
                    progress = true;
                }
            }
            for id in self.kernel.ids() {
                if self.kernel.phase(id) != Some(Phase::Inactive)
                    || self.kernel.decision(id, self.host_status(id)) != Some(Decision::Begin)
                {
                    continue;
                }
                // Initial observer publications are adopted without changing
                // their identities. Preflight before acquiring any resources or
                // registering Setup, so a rejected adoption is mutation-free.
                let prepared_publications = if self.nodes[&id].prepared {
                    self.nodes[&id].publications.clone()
                } else {
                    Vec::new()
                };
                for publication in &prepared_publications {
                    self.publications.can_adopt(*publication, id, 1)?;
                }
                let bindings = self
                    .kernel
                    .target(id)
                    .ok_or(KernelError::MissingDependency)?;
                let generation = self
                    .kernel
                    .episode_generation(id)
                    .unwrap()
                    .checked_add(1)
                    .ok_or(KernelError::Capacity)?;
                let mut resources = Vec::new();
                for binding in bindings {
                    let port = Port {
                        key: binding.key,
                        realm: binding.realm,
                    };
                    let publication = self
                        .publications
                        .resolve(port)
                        .ok_or(PublicationError::Unknown)?;
                    match self.publications.acquire_for(publication, id, generation) {
                        Ok(lease) => resources.push(ResourceBinding {
                            port,
                            publication,
                            lease,
                        }),
                        Err(error) => {
                            for resource in resources {
                                self.publications.release(resource.lease)?;
                            }
                            return Err(error.into());
                        }
                    }
                }
                if let Err(error) = self.kernel.begin(id) {
                    for resource in resources {
                        self.publications.release(resource.lease)?;
                    }
                    return Err(error.into());
                }
                // No callbacks or lease acquisitions for this inactive owner
                // can interleave with the preflight and first Begin above.
                for publication in prepared_publications {
                    self.publications.adopt(publication, id, 1)?;
                }
                let node = self.nodes.get_mut(&id).unwrap();
                node.resources = resources;
                node.prepared = false;
                let ticket = self.next_ticket(id, ActionKind::Setup)?;
                actions.push(HostAction::Setup { id, ticket });
                progress = true;
            }
            if !progress {
                break;
            }
        }
        Ok(actions)
    }

    /// Accept an outstanding result at most once. Cancellation never invalidates
    /// a legitimately outstanding setup result; its inverse still needs cleanup.
    pub fn complete(
        &mut self,
        ticket: ActionTicket,
        success: bool,
        error: Option<String>,
    ) -> Result<(), DriverError> {
        if ticket.domain != self.domain {
            return Err(DriverError::new(
                "WrongDomain",
                "action belongs to another driver",
            ));
        }
        let node = self
            .nodes
            .get(&ticket.id)
            .ok_or_else(|| DriverError::new("StaleAction", "action owner no longer exists"))?;
        if node.pending.as_ref() != Some(&ticket) {
            return Err(DriverError::new(
                "StaleAction",
                "action is unknown or already completed",
            ));
        }
        let id = ticket.id;
        match ticket.kind {
            ActionKind::Setup => self.kernel.complete_action(&ticket)?,
            ActionKind::Cleanup => self.kernel.complete_cleanup(
                &ticket,
                if success {
                    CleanupOutcome::Succeeded
                } else {
                    CleanupOutcome::Failed
                },
            )?,
        }
        self.nodes.get_mut(&id).unwrap().pending = None;
        match ticket.kind {
            ActionKind::Setup => {
                if !success {
                    self.nodes.get_mut(&id).unwrap().failed =
                        Some(error.unwrap_or_else(|| "setup failed".to_owned()));
                }
                if self.kernel.phase(id) == Some(Phase::Loading) {
                    let missing = self.nodes[&id]
                        .provisions
                        .iter()
                        .any(|port| self.publications.resolve(*port).is_none());
                    if missing && success {
                        self.nodes.get_mut(&id).unwrap().failed =
                            Some("declared service was not published".to_owned());
                    }
                    if self.nodes[&id].failed.is_none()
                        && !self.nodes[&id].restart
                        && self.ready(id)
                    {
                        match self.kernel.finish(id) {
                            Ok(()) => {}
                            Err(KernelError::Changed | KernelError::Retired) => {
                                self.withdraw(id)?
                            }
                            Err(error) => return Err(error.into()),
                        }
                    } else {
                        self.withdraw(id)?;
                    }
                }
            }
            ActionKind::Cleanup => {
                if !success {
                    let node = self.nodes.get_mut(&id).unwrap();
                    node.cleanup_failed = true;
                    node.failed = Some(error.unwrap_or_else(|| "cleanup failed".to_owned()));
                    return Ok(());
                }
                let prepared_cleanup = self.nodes[&id].prepared_cleanup;
                let leases: Vec<_> = self.nodes[&id]
                    .resources
                    .iter()
                    .map(|resource| resource.lease)
                    .collect();
                let released = self.kernel.finish_cleanup_resources(
                    &mut self.publications,
                    id,
                    prepared_cleanup,
                    &leases,
                    &self.nodes[&id].publications,
                )?;
                let node = self.nodes.get_mut(&id).unwrap();
                if prepared_cleanup {
                    node.failed = None;
                }
                node.prepared = false;
                node.prepared_cleanup = false;
                node.resources.clear();
                node.publications.clear();
                for resource in released {
                    self.checked.remove(&resource.publication.0);
                    if let Some(value) = self.values.remove(&resource.slot) {
                        self.released.push(value);
                    }
                }
                node.restoring_publications.clear();
                node.restart = false;
                node.cleanup_failed = false;
                self.reconcile_publications()?;
                self.maintain_history();
            }
        }
        Ok(())
    }

    /// Retry an inverse after a reported failure. The previous action ticket
    /// remains consumed; the executor receives a fresh ticket for this attempt.
    pub fn retry_cleanup(&mut self, id: usize) -> Result<HostAction, DriverError> {
        let node = self.nodes.get(&id).ok_or(KernelError::Unknown)?;
        if !node.cleanup_failed
            || node.pending.is_some()
            || !(self.kernel.cleanup_started(id) || node.prepared_cleanup)
        {
            return Err(DriverError::new(
                "InvalidState",
                "no failed cleanup to retry",
            ));
        }
        self.kernel.retry_cleanup(id)?;
        let ticket = self.next_ticket(id, ActionKind::Cleanup)?;
        self.nodes.get_mut(&id).unwrap().cleanup_failed = false;
        Ok(HostAction::Cleanup { id, ticket })
    }

    fn phase_name(&self, id: usize) -> &'static str {
        let node = &self.nodes[&id];
        match self.kernel.phase(id).unwrap() {
            _ if node.prepared_cleanup => "Unloading",
            Phase::Inactive if node.failed.is_some() => "Failed",
            Phase::Inactive => "Pending",
            Phase::Loading => "Loading",
            Phase::Active => "Active",
            Phase::Unloading => "Unloading",
        }
    }

    fn identity_snapshot(&self, id: usize) -> Value {
        json!({
            "id": id.to_string(),
            "generation": self.kernel.episode_generation(id).map(|v| v.to_string()),
        })
    }

    fn binding_snapshot(
        &self,
        id: usize,
        binding: cordis_kernel::Binding,
        committed: bool,
    ) -> Value {
        let port = Port {
            key: binding.key,
            realm: binding.realm,
        };
        let publication = if committed {
            self.nodes[&id]
                .resources
                .iter()
                .find(|resource| resource.port == port)
                .map(|resource| resource.publication)
        } else {
            self.publications.resolve(port).filter(|publication| {
                self.publications
                    .entry(*publication)
                    .is_some_and(|entry| entry.owner == binding.provider)
            })
        };
        // The old episode retains its own publication even when the current
        // resolver selects a different identity for the same port.
        let generation = if committed {
            publication.and_then(|publication| {
                self.publications
                    .entry(publication)
                    .map(|entry| entry.generation)
            })
        } else {
            self.kernel.episode_generation(binding.provider)
        };
        json!({
            "key": binding.key.to_string(), "realm": binding.realm.to_string(),
            "provider": binding.provider.to_string(),
            "generation": generation.map(|value| value.to_string()),
            "publication": publication.map(|value| value.0.to_string()),
        })
    }

    fn dependency_blocker(&self, id: usize, port: ServicePort) -> Option<Value> {
        let provider = self.kernel.resolve(port.into());
        let publication = self.publications.resolve(port.into());
        let entry = publication.and_then(|publication| self.publications.entry(publication));
        let mut blocker = if let Some(provider) = provider {
            match entry {
                None => json!({"code": "PublicationMissing", "provider": provider.to_string()}),
                Some(entry) if entry.owner != provider || self.kernel.retired(entry.owner) => {
                    json!({"code": "ProviderUnavailable", "providers": [{
                        "id": entry.owner.to_string(),
                        "generation": entry.generation.to_string(),
                        "state": self.phase_name(entry.owner),
                        "retired": self.kernel.retired(entry.owner),
                    }]})
                }
                Some(entry) => {
                    let publication = publication.unwrap();
                    if !self.checked.contains_key(&publication.0)
                        || self.availability.available(id, port, publication.0)
                    {
                        return None;
                    }
                    let candidate = self.check_candidate(id, port)?;
                    let mut blocker = self.availability.blocker(candidate);
                    blocker["provider"] = json!(entry.owner.to_string());
                    blocker["publication"] = json!(publication.0.to_string());
                    blocker
                }
            }
        } else {
            // Include declared providers as well as dynamic publications. A
            // visible publication in another realm is never a matching service.
            let mut providers = Vec::new();
            let mut realms = std::collections::BTreeSet::new();
            for (&provider, node) in &self.nodes {
                let ports =
                    node.provisions
                        .iter()
                        .copied()
                        .chain(node.publications.iter().filter_map(|publication| {
                            self.publications
                                .entry(*publication)
                                .filter(|entry| entry.retained)
                                .map(|entry| entry.port)
                        }));
                let mut matches = false;
                for candidate in ports.filter(|candidate| candidate.key == port.key) {
                    if candidate.realm == port.realm {
                        matches = true;
                    } else {
                        realms.insert(candidate.realm);
                    }
                }
                if matches {
                    providers.push(json!({
                        "id": provider.to_string(),
                        "generation": self.kernel.episode_generation(provider).map(|v| v.to_string()),
                        "state": self.phase_name(provider), "retired": self.kernel.retired(provider),
                    }));
                }
            }
            if !providers.is_empty() {
                json!({"code": "ProviderUnavailable", "providers": providers})
            } else if !realms.is_empty() {
                json!({"code": "RealmMismatch", "observedRealms": realms.iter().map(|realm| realm.to_string()).collect::<Vec<_>>()})
            } else {
                json!({"code": "MissingProvider"})
            }
        };
        blocker["port"] = json!(port);
        Some(blocker)
    }

    fn plugin_state(&self, id: usize) -> Value {
        let node = &self.nodes[&id];
        json!({
            "id": id.to_string(),
            "generation": self.kernel.episode_generation(id).unwrap().to_string(),
            "parent": node.parent.map(|id| id.to_string()),
            "state": self.phase_name(id), "retired": self.kernel.retired(id),
            "error": node.failed, "cleanupFailed": node.cleanup_failed,
            "pendingAction": node.pending,
        })
    }

    /// Read only the lifecycle fields needed by executor coordination. Unlike
    /// `snapshot`, this does not resolve targets, scan dependency histories, or
    /// construct diagnostics/storage. It carries no new admission authority.
    pub fn snapshot_state(&self) -> Value {
        let plugins: Vec<_> = self.nodes.keys().map(|&id| self.plugin_state(id)).collect();
        json!({"abi": 1, "profile": self.profile, "domain": self.domain.to_string(), "plugins": plugins})
    }

    /// Diagnostic observations, not an independent lifecycle state machine.
    /// `leaseRecords` counts stored live leases; `leaseAllocations` is the
    /// monotonic allocation count, including leases already released.
    pub fn snapshot(&self) -> Value {
        let mut consumers: BTreeMap<usize, Vec<Value>> = BTreeMap::new();
        for &id in self.nodes.keys() {
            let mut providers = std::collections::BTreeSet::new();
            for binding in self.kernel.committed(id) {
                if providers.insert(binding.provider) {
                    consumers
                        .entry(binding.provider)
                        .or_default()
                        .push(self.identity_snapshot(id));
                }
            }
        }
        let plugins: Vec<_> = self
            .nodes
            .iter()
            .map(|(&id, node)| {
                let phase = self.kernel.phase(id).unwrap();
                let committed = self.kernel.committed(id);
                let target = self.kernel.target(id);
                let mut blockers = Vec::new();
                if node.cleanup_failed {
                    blockers.push(
                        json!({"code": "CleanupFailed", "error": node.failed, "retryable": true}),
                    );
                } else if phase != Phase::Unloading && !node.prepared_cleanup {
                    if let Some(error) = &node.failed {
                        blockers.push(json!({"code": "Failed", "error": error}));
                    }
                }
                if !self.kernel.retired(id) && phase != Phase::Unloading {
                    if !node.sealed {
                        blockers.push(json!({"code": "Unsealed"}));
                    }
                    for port in &node.dependencies {
                        if let Some(blocker) = self.dependency_blocker(id, *port) {
                            blockers.push(blocker);
                        }
                    }
                }
                if matches!(phase, Phase::Loading | Phase::Active)
                    && !target.as_ref().is_some_and(|target| {
                        cordis_kernel::episode::same_bindings(target, &committed)
                    })
                {
                    blockers.push(json!({"code": "TargetChanged"}));
                }
                if let Some(ticket) = &node.pending {
                    blockers.push(json!({"code": "PendingAction", "ticket": ticket}));
                }
                if phase == Phase::Unloading {
                    if let Some(consumers) = consumers.get(&id) {
                        blockers
                            .push(json!({"code": "CommittedConsumers", "consumers": consumers}));
                    }
                }
                // Ownership only delays removal or the next episode. It is not a
                // service edge and does not delay this parent's cleanup action.
                if phase == Phase::Inactive {
                    let children: Vec<_> = self
                        .kernel
                        .children(id)
                        .into_iter()
                        .filter(|child| self.kernel.retired(*child))
                        .map(|child| self.identity_snapshot(child))
                        .collect();
                    if !children.is_empty() {
                        blockers.push(json!({"code": "RetiringChildren", "children": children}));
                    }
                }
                let mut plugin = self.plugin_state(id);
                plugin["dependencies"] = json!(node.dependencies);
                plugin["committed"] = json!(committed
                    .into_iter()
                    .map(|binding| self.binding_snapshot(id, binding, true))
                    .collect::<Vec<_>>());
                plugin["target"] = json!(target.map(|bindings| bindings
                    .into_iter()
                    .map(|binding| self.binding_snapshot(id, binding, false))
                    .collect::<Vec<_>>()));
                plugin["blockers"] = json!(blockers);
                plugin
            })
            .collect();
        let storage = json!({
            "registeredPlugins": self.nodes.len(),
            "identitySlots": self.kernel.identity_slots(),
            "declarationRecords": self.kernel.declaration_records(),
            "bindingRecords": self.kernel.binding_records(),
            "liveBindings": self.nodes.keys().map(|id| self.kernel.committed(*id).len()).sum::<usize>(),
            "publicationRecords": self.publications.publication_records(),
            "leaseRecords": self.publications.lease_record_count(),
            "leaseAllocations": self.publications.lease_allocation_count(),
            "liveLeases": self.nodes.values().map(|node| node.resources.len()).sum::<usize>(),
            "publishedValues": self.values.len(),
            "pendingActions": self.nodes.values().filter(|node| node.pending.is_some()).count(),
        });
        json!({"abi":1,"diagnosticsSchema":"cordis.driver/v1","profile":self.profile,"domain":self.domain.to_string(),"plugins":plugins,"checkErrors":self.availability.diagnostics(),"storage":storage})
    }

    /// Whether a fiber is in an episode's still-committed dependency closure.
    /// Host cleanup continuations use this read-only query to carry restoration
    /// authority through service calls. Ownership alone creates no such edge.
    pub fn committed_reaches(
        &self,
        from: usize,
        generation: u64,
        target: usize,
    ) -> Result<bool, DriverError> {
        if self.kernel.episode_generation(from) != Some(generation) {
            return Err(DriverError::new(
                "StaleEpisode",
                "dependency lookup belongs to an earlier episode",
            ));
        }
        let mut pending = vec![from];
        let mut visited = std::collections::BTreeSet::new();
        while let Some(id) = pending.pop() {
            if !visited.insert(id) {
                continue;
            }
            if id == target {
                return Ok(true);
            }
            pending.extend(
                self.kernel
                    .committed(id)
                    .into_iter()
                    .map(|binding| binding.provider),
            );
        }
        Ok(false)
    }

    /// Parse and execute the JSON ABI. Successful replies include no callbacks
    /// and no executor payloads, only opaque host value identities.
    pub fn command(&mut self, input: &str) -> Result<String, DriverError> {
        let command: Command = serde_json::from_str(input)
            .map_err(|error| DriverError::new("InvalidCommand", error.to_string()))?;
        self.execute(command).and_then(|value| {
            serde_json::to_string(&value)
                .map_err(|error| DriverError::new("Serialization", error.to_string()))
        })
    }

    /// Alias used by native bindings that expose an explicitly JSON ABI.
    pub fn command_json(&mut self, input: &str) -> Result<String, DriverError> {
        self.command(input)
    }

    pub fn execute(&mut self, command: Command) -> Result<Value, DriverError> {
        match command {
            Command::CommittedReaches {
                from,
                generation,
                target,
            } => Ok(json!({"reachable": self.committed_reaches(from,generation,target)?})),
            Command::Configure { profile } => {
                if self.configured || !self.kernel.ids().is_empty() {
                    return Err(DriverError::new(
                        "ProfileFrozen",
                        "profile must be selected once before mounting",
                    ));
                }
                self.profile = profile;
                self.configured = true;
                Ok(json!({"profile":profile}))
            }
            Command::Mount {
                sealed,
                parent,
                dependencies,
                provisions,
            } => {
                let id = self.mount(parent, dependencies, provisions)?;
                self.nodes.get_mut(&id).unwrap().sealed = sealed;
                Ok(json!({"id":id.to_string()}))
            }
            Command::Prepare { id } => Ok(json!({"generation":self.prepare(id)?.to_string()})),
            Command::Seal { id, dependencies } => {
                let node = self.nodes.get(&id).ok_or(KernelError::Unknown)?;
                if node.sealed {
                    return Err(DriverError::new(
                        "AlreadySealed",
                        "plugin declaration was already sealed",
                    ));
                }
                if !self.kernel.retired(id) {
                    self.kernel.configure_pending_dependencies(
                        id,
                        dependencies.iter().copied().map(Into::into).collect(),
                    )?;
                    let node = self.nodes.get_mut(&id).unwrap();
                    node.dependencies = dependencies;
                    node.sealed = true;
                }
                Ok(json!({}))
            }
            Command::Reclaim {
                id,
                generation,
                publication,
            } => Ok(json!({"drained":self.reclaim(id,generation,publication)?})),
            Command::Drive => {
                let actions = self.drive()?;
                Ok(
                    json!({"actions":actions,"released":std::mem::take(&mut self.released).into_iter().filter(|value| !self.values.values().any(|retained|retained == value)).map(|value|value.to_string()).collect::<Vec<_>>()}),
                )
            }
            Command::Complete {
                ticket,
                success,
                error,
            } => {
                self.complete(ticket, success, error)?;
                Ok(json!({}))
            }
            Command::Retire { id } => {
                self.retire(id)?;
                Ok(json!({}))
            }
            Command::Restart { id } => {
                self.restart(id)?;
                Ok(json!({}))
            }
            Command::RetryCleanup { id } => Ok(json!({"actions":[self.retry_cleanup(id)?]})),
            Command::Validate { id, generation } => {
                self.validate(id, generation)?;
                Ok(json!({"valid":true}))
            }
            Command::Publish {
                check,
                id,
                generation,
                key,
                realm,
                value,
            } => {
                let publication =
                    self.publish(id, generation, ServicePort { key, realm }, value)?;
                if check {
                    self.checked.insert(publication, 0);
                }
                Ok(json!({"publication":publication.to_string()}))
            }
            Command::Set {
                id,
                generation,
                publication,
                value,
            } => {
                self.set(id, generation, publication, value)?;
                Ok(json!({}))
            }
            Command::Revoke {
                id,
                generation,
                publication,
            } => {
                self.revoke(id, generation, publication)?;
                Ok(json!({}))
            }
            Command::Resolve {
                key,
                realm,
                consumer,
                generation,
            } => Ok(self
                .resolve(ServicePort { key, realm }, consumer, generation)?
                .unwrap_or(Value::Null)),
            Command::Checks => Ok(json!({"checks":self.check_actions()?})),
            Command::Notify { ports } => {
                self.availability.notify(&ports)?;
                if self.profile == Profile::Harness {
                    for node in self.nodes.values_mut() {
                        if !node.cleanup_failed
                            && node.dependencies.iter().any(|port| ports.contains(port))
                        {
                            node.failed = None;
                        }
                    }
                }
                Ok(json!({"checks":self.check_actions()?}))
            }
            Command::ValidateCheck { ticket } => {
                let candidate = self.check_candidate(ticket.consumer, ticket.port);
                Ok(
                    json!({"current":ticket.domain == self.domain && self.availability.current(&ticket,candidate)}),
                )
            }
            Command::CompleteCheck {
                ticket,
                available,
                error,
            } => {
                if ticket.domain != self.domain {
                    return Err(DriverError::new(
                        "WrongDomain",
                        "check belongs to another driver",
                    ));
                }
                let candidate = self.check_candidate(ticket.consumer, ticket.port);
                Ok(
                    json!({"accepted":self.availability.complete(ticket,candidate,available,error)?}),
                )
            }
            Command::Snapshot => Ok(self.snapshot()),
            Command::SnapshotState => Ok(self.snapshot_state()),
        }
    }
}
