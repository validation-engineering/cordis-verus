//! Value-independent lifecycle driving for native hosts.
//!
//! Commands never execute callbacks. An executor receives owned actions after
//! the mutable driver borrow ends and submits one completion for each ticket.
//! This host adapter is ordinary Rust; kernel proofs do not prove its callbacks
//! or JSON translation. Actual service admission, dynamic declaration ownership
//! and provider reconciliation execute in the checked NodeRuntime. JavaScript
//! object contents still need their own paper-model interpretation.

mod availability;
mod node;
mod objects;
pub use objects::{HostBridge, HostCall, HostSelection, ObjectKey};
mod protocol;
use availability::{Availability, Candidate};
pub use availability::{CheckAction, CheckTicket};
pub mod shared;
use cordis_kernel::availability::admission::ResourceBinding;
use cordis_kernel::invocation_ledger::ScopeError;
use cordis_kernel::node_runtime::episode::{Command as EpisodeCommand, Episode, EpisodeError};
pub use cordis_kernel::node_runtime::paths::Path as InvocationPath;
use cordis_kernel::publication::{PublicationError, PublicationId};
pub use cordis_kernel::request_ledger;
use cordis_kernel::{Error as KernelError, Phase, Port};
use node::NodeDriver;
pub use protocol::{
    ActionKind, ActionTicket, Command, HostAction, Profile, RequestTicket, ScopeHandle, ServicePort,
};
use serde_json::{json, Value};
use shared::{Decision, HostStatus};
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
impl From<ScopeError> for DriverError {
    fn from(value: ScopeError) -> Self {
        Self::new(
            match value {
                ScopeError::StaleEpisode => "StaleEpisode",
                ScopeError::Completed => "StaleAuthority",
                ScopeError::Capacity => "Capacity",
                ScopeError::WrongDomain | ScopeError::Unknown => "InvalidAuthority",
            },
            format!("invocation scope: {value:?}"),
        )
    }
}
impl From<PublicationError> for DriverError {
    fn from(value: PublicationError) -> Self {
        Self::new("Publication", format!("{value:?}"))
    }
}

impl From<EpisodeError> for DriverError {
    fn from(error: EpisodeError) -> Self {
        match error {
            EpisodeError::Unknown => KernelError::Unknown.into(),
            EpisodeError::Retired => Self::new("Retired", "cannot restart a retired plugin"),
            EpisodeError::Stale => Self::new("StaleEpisode", "plugin generation is not current"),
            EpisodeError::Closed => {
                Self::new("AdmissionClosed", "episode cannot acquire new resources")
            }
        }
    }
}
impl From<cordis_kernel::node_runtime::policy::PolicyError> for DriverError {
    fn from(error: cordis_kernel::node_runtime::policy::PolicyError) -> Self {
        use cordis_kernel::node_runtime::policy::PolicyError;
        match error {
            PolicyError::ProfileFrozen => Self::new(
                "ProfileFrozen",
                "profile must be selected once before mounting",
            ),
            PolicyError::ParentClosed => Self::new("ParentClosed", "parent cannot admit a child"),
            PolicyError::AlreadySealed => {
                Self::new("AlreadySealed", "plugin declaration was already sealed")
            }
            PolicyError::Kernel(error) => error.into(),
            PolicyError::Episode(error) => error.into(),
        }
    }
}

/// One authoritative lifecycle domain. Values are opaque host-owned handles.
pub struct Driver {
    domain: u64,
    kernel: NodeDriver,
    availability: Availability,
    maintenance_changes: usize,
}
impl Driver {
    /// Allocate a process-unique domain identity, failing rather than wrapping.
    pub fn new() -> Result<Self, DriverError> {
        let kernel = NodeDriver::new()?;
        let domain = kernel.domain();
        Ok(Self {
            domain,
            kernel,
            availability: Availability::new(),
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
        self.mount_sealed(parent, dependencies, provisions, true)
    }

    fn mount_sealed(
        &mut self,
        parent: Option<usize>,
        dependencies: Vec<ServicePort>,
        provisions: Vec<ServicePort>,
        sealed: bool,
    ) -> Result<usize, DriverError> {
        self.kernel.mount(
            parent,
            dependencies.into_iter().map(Into::into).collect(),
            provisions.into_iter().map(Into::into).collect(),
            sealed,
        )
    }

    fn profile(&self) -> Profile {
        self.kernel.core.profile().into()
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

    fn episode(&self, id: usize) -> &Episode {
        self.kernel
            .core
            .episode(id)
            .expect("registered node has an episode state")
    }
    fn resources(&self, id: usize) -> &[ResourceBinding] {
        self.kernel
            .core
            .admission(id)
            .map_or(&[], |admission| admission.resources())
    }
    fn episode_command(&mut self, command: EpisodeCommand) -> Result<(), DriverError> {
        self.kernel
            .core
            .episode_command(command)
            .map_err(Into::into)
    }
    pub fn restart(&mut self, id: usize) -> Result<(), DriverError> {
        self.episode_command(EpisodeCommand::Restart { id })
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
        self.episode_command(EpisodeCommand::Fail {
            id,
            generation,
            error,
        })?;
        self.withdraw(id)
    }

    /// Admit host effects for a reserved fiber before its first activation.
    /// Retirement drains this journal through a generation-zero cleanup ticket.
    pub fn prepare(&mut self, id: usize) -> Result<u64, DriverError> {
        self.episode_command(EpisodeCommand::Prepare { id })?;
        Ok(0)
    }

    /// Validate admission for new resource work, including escaped async calls.
    pub fn validate(&self, id: usize, generation: u64) -> Result<(), DriverError> {
        self.kernel
            .core
            .validate(id, generation)
            .map_err(|error| match error {
                EpisodeError::Stale => {
                    DriverError::new("StaleEpisode", "plugin generation is not current")
                }
                _ => DriverError::new("AdmissionClosed", "episode cannot acquire new resources"),
            })
    }

    /// Publish an opaque value while retaining the logical provider identity.
    pub fn publish(
        &mut self,
        id: usize,
        generation: u64,
        port: ServicePort,
        value: u64,
    ) -> Result<usize, DriverError> {
        use cordis_kernel::node_runtime::interfaces::PublishError;
        self.kernel
            .core
            .publish_service(id, generation, port.into(), value)
            .map(|publication| publication.0)
            .map_err(|error| match error {
                PublishError::Access(EpisodeError::Stale) => {
                    DriverError::new("StaleEpisode", "plugin generation is not current")
                }
                PublishError::Access(_) => {
                    DriverError::new("AdmissionClosed", "episode cannot acquire new resources")
                }
                PublishError::Declaration(error) => error.into(),
                PublishError::Publication(error) => error.into(),
            })
    }

    fn owned_publication(
        &self,
        id: usize,
        generation: u64,
        publication: usize,
    ) -> Result<cordis_kernel::publication::Publication, DriverError> {
        let entry = self
            .kernel
            .store()
            .registry()
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
        self.kernel
            .replace_value(PublicationId(publication), id, generation, value)
            .map_err(|rejected| DriverError::from(rejected.error))?;
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
        self.kernel.core.revoke(PublicationId(publication))?;
        Ok(())
    }

    /// Read a committed binding during setup, use, and cleanup. An unowned root
    /// lookup uses current visibility and confers no lifecycle consumer lease.
    pub fn resolve(
        &mut self,
        port: ServicePort,
        consumer: Option<usize>,
        generation: Option<u64>,
    ) -> Result<Option<Value>, DriverError> {
        use cordis_kernel::node_runtime::reads::ReadError;
        let out = self
            .kernel
            .core
            .resolve(port.into(), consumer, generation)
            .map_err(|error| match error {
                ReadError::Unknown => DriverError::from(KernelError::Unknown),
                ReadError::Stale => {
                    DriverError::new("StaleEpisode", "lookup belongs to an earlier episode")
                }
            })?;
        Ok(out.map(|read| {
            json!({
                "publication":read.publication.0.to_string(),
                "value":read.value.to_string(),
                "owner":read.owner.to_string(),
            })
        }))
    }

    fn reconcile_publications(&mut self) -> Result<(), DriverError> {
        self.kernel
            .core
            .reconcile_declarations()
            .map_err(Into::into)
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
        match self.kernel.core.reclaim(PublicationId(publication)) {
            Ok(_) => {}
            Err(PublicationError::Relied) => return Ok(false),
            Err(error) => return Err(error.into()),
        };
        self.kernel.core.set_checked(publication, false);
        self.reconcile_publications()?;
        Ok(true)
    }

    fn check_candidate(&self, consumer: usize, port: ServicePort) -> Option<Candidate> {
        let node = self.kernel.core.interfaces().get(&consumer)?;
        if self.kernel.retired(consumer) || !node.dependencies.contains(&port.into()) {
            return None;
        }
        let publication = self.kernel.store().registry().resolve(port.into())?;
        let entry = self.kernel.store().registry().entry(publication)?;
        if self.kernel.phase(entry.owner) != Some(Phase::Active) || self.kernel.retired(entry.owner)
        {
            return None;
        }
        if !self.kernel.core.checked().contains(&publication.0) {
            return None;
        }
        Some(Candidate {
            consumer,
            port,
            publication: publication.0,
        })
    }
    pub fn check_actions(&mut self) -> Result<Vec<CheckAction>, DriverError> {
        let mut candidates = Vec::new();
        for (&id, node) in self.kernel.core.interfaces() {
            for port in &node.dependencies {
                if let Some(candidate) = self.check_candidate(id, (*port).into()) {
                    candidates.push(candidate);
                }
            }
        }
        self.availability.request(&mut self.kernel.core, candidates)
    }

    fn host_status(&self, id: usize) -> HostStatus {
        HostStatus {
            available: self.episode(id).sealed && self.ready(id),
            failed: self.episode(id).failed.is_some(),
            restart: self.episode(id).restart,
        }
    }

    fn ready(&self, id: usize) -> bool {
        self.kernel.core.ready(id)
    }

    fn next_ticket(&mut self, id: usize, kind: ActionKind) -> Result<ActionTicket, DriverError> {
        let ticket = self.kernel.pending_action(id).ok_or_else(|| {
            DriverError::new("MissingAction", "shared driver did not register an action")
        })?;
        if ticket.kind != kind {
            return Err(DriverError::new(
                "WrongAction",
                "shared action kind differs",
            ));
        }
        Ok(ticket)
    }

    fn withdraw_publications(&mut self, id: usize) -> Result<(), DriverError> {
        self.kernel.core.withdraw_publications(id)?;
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
        self.kernel
            .ensure_action_capacity(self.kernel.core.interfaces().len())?;
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
                let episode = self.episode(id);
                if self.kernel.phase(id) == Some(Phase::Unloading)
                    && self.kernel.decision(id, self.host_status(id))
                        == Some(Decision::BeginCleanup)
                    && self.kernel.pending_action(id).is_none()
                    && !episode.cleanup_failed
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
                let episode = self.episode(id);
                if episode.prepared
                    && self.kernel.retired(id)
                    && self.kernel.phase(id) == Some(Phase::Inactive)
                    && self.kernel.pending_action(id).is_none()
                    && !episode.cleanup_failed
                {
                    self.kernel.begin_reservation_cleanup(id)?;
                    self.withdraw_publications(id)?;
                    let ticket = self.next_ticket(id, ActionKind::Cleanup)?;
                    actions.push(HostAction::Cleanup { id, ticket });
                    progress = true;
                }
            }
            for id in self.kernel.ids().into_iter().rev() {
                if self.kernel.phase(id) == Some(Phase::Inactive)
                    && !self.episode(id).prepared
                    && !self.episode(id).prepared_cleanup
                    && self.kernel.decision(id, self.host_status(id)) == Some(Decision::Remove)
                {
                    self.kernel.remove(id)?;
                    self.availability.remove_consumer(&mut self.kernel.core, id);
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
                let prepared_publications = if self.episode(id).prepared {
                    self.kernel.core.publications(id)
                } else {
                    Vec::new()
                };
                for publication in &prepared_publications {
                    self.kernel
                        .store()
                        .registry()
                        .can_adopt(*publication, id, 1)?;
                }
                self.kernel.begin_checked(id)?;
                // No callbacks or lease acquisitions for this inactive owner
                // can interleave with the preflight and first Begin above.
                for publication in prepared_publications {
                    self.kernel.core.adopt(publication, id, 1)?;
                }
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
        if self.kernel.pending_action(ticket.id).as_ref() != Some(&ticket) {
            return Err(DriverError::new(
                "StaleAction",
                "action is unknown or already completed",
            ));
        }
        let id = ticket.id;
        let failure = if !success {
            Some(error.unwrap_or_else(|| match ticket.kind {
                ActionKind::Setup => "setup failed".to_owned(),
                ActionKind::Cleanup => "cleanup failed".to_owned(),
            }))
        } else if ticket.kind == ActionKind::Setup
            && self.kernel.phase(id) == Some(Phase::Loading)
            && self.kernel.core.interfaces()[&id]
                .provisions
                .iter()
                .any(|port| self.kernel.store().registry().resolve(*port).is_none())
        {
            Some("declared service was not published".to_owned())
        } else {
            None
        };
        self.kernel.complete(&ticket, failure)?;
        match ticket.kind {
            ActionKind::Setup => {
                if self.kernel.phase(id) == Some(Phase::Loading) {
                    if self.episode(id).failed.is_none()
                        && !self.episode(id).restart
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
                    return Ok(());
                }
                let prepared_cleanup = self.episode(id).prepared_cleanup;
                let released = if prepared_cleanup {
                    self.kernel.finish_reservation_values(id)?
                } else {
                    self.kernel.finish_admission_values(id)?
                };
                for resource in released {
                    self.kernel.core.set_checked(resource.publication.0, false);
                }
                self.reconcile_publications()?;
                self.maintain_history();
            }
        }
        Ok(())
    }

    /// Retry an inverse after a reported failure. The previous action ticket
    /// remains consumed; the executor receives a fresh ticket for this attempt.
    pub fn retry_cleanup(&mut self, id: usize) -> Result<HostAction, DriverError> {
        if !self.kernel.core.interfaces().contains_key(&id) {
            return Err(KernelError::Unknown.into());
        }
        if !self.episode(id).cleanup_failed
            || self.kernel.pending_action(id).is_some()
            || !(self.kernel.cleanup_started(id) || self.episode(id).prepared_cleanup)
        {
            return Err(DriverError::new(
                "InvalidState",
                "no failed cleanup to retry",
            ));
        }
        self.kernel.retry_cleanup(id)?;
        let ticket = self.next_ticket(id, ActionKind::Cleanup)?;
        Ok(HostAction::Cleanup { id, ticket })
    }

    fn phase_name(&self, id: usize) -> &'static str {
        let episode = self.episode(id);
        match self.kernel.phase(id).unwrap() {
            _ if episode.prepared_cleanup => "Unloading",
            Phase::Inactive if episode.failed.is_some() => "Failed",
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
            self.resources(id)
                .iter()
                .find(|resource| resource.port == port)
                .map(|resource| resource.publication)
        } else {
            self.kernel
                .store()
                .registry()
                .resolve(port)
                .filter(|publication| {
                    self.kernel
                        .store()
                        .registry()
                        .entry(*publication)
                        .is_some_and(|entry| entry.owner == binding.provider)
                })
        };
        // The old episode retains its own publication even when the current
        // resolver selects a different identity for the same port.
        let generation = if committed {
            publication.and_then(|publication| {
                self.kernel
                    .store()
                    .registry()
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
        let publication = self.kernel.store().registry().resolve(port.into());
        let entry =
            publication.and_then(|publication| self.kernel.store().registry().entry(publication));
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
                    if !self.kernel.core.checked().contains(&publication.0)
                        || self
                            .availability
                            .available(&self.kernel.core, id, port, publication.0)
                    {
                        return None;
                    }
                    let candidate = self.check_candidate(id, port)?;
                    let mut blocker = self.availability.blocker(candidate, &self.kernel.core);
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
            for (&provider, node) in self.kernel.core.interfaces() {
                let publications = self.kernel.core.publications(provider);
                let ports = node
                    .provisions
                    .iter()
                    .copied()
                    .chain(publications.iter().filter_map(|publication| {
                        self.kernel
                            .store()
                            .registry()
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
        let node = &self.kernel.core.interfaces()[&id];
        json!({
            "id": id.to_string(),
            "generation": self.kernel.episode_generation(id).unwrap().to_string(),
            "parent": node.parent.map(|id| id.to_string()),
            "state": self.phase_name(id), "retired": self.kernel.retired(id),
            "error": self.episode(id).failed, "cleanupFailed": self.episode(id).cleanup_failed,
            "pendingAction": self.kernel.pending_action(id),
        })
    }

    /// Read only the lifecycle fields needed by executor coordination. Unlike
    /// `snapshot`, this does not resolve targets, scan dependency histories, or
    /// construct diagnostics/storage. It carries no new admission authority.
    pub fn snapshot_state(&self) -> Value {
        let _execution = self.execution_snapshot();
        let plugins: Vec<_> = self
            .kernel
            .core
            .interfaces()
            .keys()
            .map(|&id| self.plugin_state(id))
            .collect();
        json!({"abi": 1, "profile": self.profile(), "domain": self.domain.to_string(), "plugins": plugins})
    }

    /// The checked protocol trajectory is erased from the executable. It is
    /// captured from this actual owner, independently of JSON diagnostics.
    pub fn execution_snapshot(&self) -> cordis_kernel::node_runtime::Snapshot {
        self.kernel.core.snapshot()
    }

    /// Diagnostic observations, not an independent lifecycle state machine.
    /// `leaseRecords` counts stored live leases; `leaseAllocations` is the
    /// monotonic allocation count, including leases already released.
    pub fn snapshot(&self) -> Value {
        let _execution = self.execution_snapshot();
        let mut consumers: BTreeMap<usize, Vec<Value>> = BTreeMap::new();
        for &id in self.kernel.core.interfaces().keys() {
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
        let plugins: Vec<_> = self.kernel.core.interfaces()
            .iter()
            .map(|(&id, node)| {
                let phase = self.kernel.phase(id).unwrap();
                let committed = self.kernel.committed(id);
                let target = self.kernel.target(id);
                let mut blockers = Vec::new();
                if self.episode(id).cleanup_failed {
                    blockers.push(
                        json!({"code": "CleanupFailed", "error": self.episode(id).failed, "retryable": true}),
                    );
                } else if phase != Phase::Unloading && !self.episode(id).prepared_cleanup {
                    if let Some(error) = &self.episode(id).failed {
                        blockers.push(json!({"code": "Failed", "error": error}));
                    }
                }
                if !self.kernel.retired(id) && phase != Phase::Unloading {
                    if !self.episode(id).sealed {
                        blockers.push(json!({"code": "Unsealed"}));
                    }
                    for port in &node.dependencies {
                        if let Some(blocker) = self.dependency_blocker(id, (*port).into()) {
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
                if let Some(ticket) = self.kernel.pending_action(id) {
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
                plugin["dependencies"] = json!(node.dependencies.iter().copied().map(ServicePort::from).collect::<Vec<_>>());
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
            "registeredPlugins": self.kernel.core.interfaces().len(),
            "identitySlots": self.kernel.identity_slots(),
            "declarationRecords": self.kernel.declaration_records(),
            "bindingRecords": self.kernel.binding_records(),
            "liveBindings": self.kernel.core.interfaces().keys().map(|id| self.kernel.committed(*id).len()).sum::<usize>(),
            "publicationRecords": self.kernel.store().registry().publication_records(),
            "leaseRecords": self.kernel.store().registry().lease_record_count(),
            "leaseAllocations": self.kernel.store().registry().lease_allocation_count(),
            "liveLeases": self.kernel.core.interfaces().keys().map(|&id| self.resources(id).len()).sum::<usize>(),
            "publishedValues": self.kernel.store().retained_count(),
            "invocationScopes": self.kernel.core.invocation_count(),
            "pendingActions": self.kernel.core.interfaces().keys().filter(|&&id| self.kernel.pending_action(id).is_some()).count(),
        });
        json!({"abi":1,"diagnosticsSchema":"cordis.driver/v1","profile":self.profile(),"domain":self.domain.to_string(),"plugins":plugins,"checkErrors":self.availability.diagnostics(&self.kernel.core),"storage":storage})
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
        self.kernel
            .committed_reaches(from, generation, target)
            .ok_or_else(|| {
                DriverError::new(
                    "StaleEpisode",
                    "dependency lookup belongs to an earlier episode",
                )
            })
    }

    /// Low-level read-only admission with an explicit host ownership fact.
    /// Managed JS uses CheckScopeWait; reverse callbacks use check_request_wait.
    pub fn check_wait(
        &self,
        from: usize,
        generation: u64,
        target: usize,
        holding: bool,
    ) -> Result<Option<usize>, DriverError> {
        use cordis_kernel::wait_guard::WaitDecision;
        match self.kernel.check_wait(from, generation, target, holding) {
            WaitDecision::Allowed => Ok(None),
            WaitDecision::Blocked { retained } => Ok(Some(retained)),
            WaitDecision::StaleEpisode => Err(DriverError::new(
                "StaleEpisode",
                "wait admission belongs to an earlier episode",
            )),
        }
    }

    /// Admit a wait using the transport's recorded request, never a host boolean.
    pub fn check_request_wait(
        &self,
        ledger: &request_ledger::RequestLedger,
        ticket: RequestTicket,
        target: usize,
    ) -> Result<Option<usize>, DriverError> {
        use cordis_kernel::wait_guard::WaitDecision;
        use request_ledger::RequestError;
        let decision = ledger
            .check_wait(&self.kernel, self.domain, ticket.into(), target)
            .map_err(|error| {
                DriverError::new(
                    if error == RequestError::Stale {
                        "StaleAuthority"
                    } else {
                        "InvalidAuthority"
                    },
                    "wait requires an outstanding request in this domain",
                )
            })?;
        match decision {
            WaitDecision::Allowed => Ok(None),
            WaitDecision::Blocked { retained } => Ok(Some(retained)),
            WaitDecision::StaleEpisode => Err(DriverError::new(
                "StaleEpisode",
                "wait belongs to an earlier episode",
            )),
        }
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

    /// Capture the selected callback ancestry once in the checked Node owner.
    pub fn begin_invocation(
        &mut self,
        id: usize,
        generation: u64,
        parent: Option<&InvocationPath>,
    ) -> Result<InvocationPath, DriverError> {
        self.kernel
            .core
            .begin_invocation(id, generation, parent)
            .map_err(Into::into)
    }
    pub fn finish_invocation(&mut self, path: &InvocationPath) -> Result<(), DriverError> {
        self.kernel.core.finish_invocation(path).map_err(Into::into)
    }
    pub fn invocation_live(&mut self, path: &InvocationPath) -> Result<bool, DriverError> {
        self.kernel.core.invocation_live(path).map_err(Into::into)
    }
    pub fn invocation_own_live(&mut self, path: &InvocationPath) -> Result<bool, DriverError> {
        self.kernel
            .core
            .invocation_own_live(path)
            .map_err(Into::into)
    }
    pub fn check_invocation_wait(
        &mut self,
        path: &InvocationPath,
        target: usize,
    ) -> Result<Value, DriverError> {
        Ok(
            match self.kernel.core.check_invocation_wait(path, target)? {
                None => json!({"blocked":false}),
                Some(block) => json!({"blocked":true,"scope":ScopeHandle::from(block.scope),
                "owner":block.id.to_string(),"generation":block.generation.to_string(),
                "retained":block.retained.to_string()}),
            },
        )
    }

    pub fn execute(&mut self, command: Command) -> Result<Value, DriverError> {
        match command {
            Command::BeginScope { id, generation } => {
                let scope: ScopeHandle = self.kernel.core.begin_scope(id, generation)?.into();
                Ok(json!({"scope":scope}))
            }
            Command::FinishScope { scope } => {
                self.kernel.core.finish_scope(scope.into())?;
                Ok(json!({}))
            }
            Command::ScopesLive { scopes } => {
                let scopes: Vec<_> = scopes.into_iter().map(Into::into).collect();
                Ok(json!({"live":self.kernel.core.scopes_live(&scopes)?}))
            }
            Command::CheckScopeWait { scopes, target } => {
                let scopes: Vec<_> = scopes.into_iter().map(Into::into).collect();
                let block = self.kernel.core.check_scope_wait(&scopes, target)?;
                Ok(match block {
                    None => json!({"blocked":false}),
                    Some(block) => json!({"blocked":true,"scope":ScopeHandle::from(block.scope),
                        "owner":block.id.to_string(),"generation":block.generation.to_string(),
                        "retained":block.retained.to_string()}),
                })
            }
            Command::CheckWait {
                from,
                generation,
                target,
                holding,
            } => {
                let retained = self.check_wait(from, generation, target, holding)?;
                Ok(
                    json!({"blocked":retained.is_some(), "retained":retained.map(|id| id.to_string())}),
                )
            }
            Command::CommittedReaches {
                from,
                generation,
                target,
            } => Ok(json!({"reachable": self.committed_reaches(from,generation,target)?})),
            Command::Configure { profile } => {
                self.kernel.core.configure_profile(profile.into())?;
                Ok(json!({"profile":profile}))
            }
            Command::Mount {
                sealed,
                parent,
                dependencies,
                provisions,
            } => {
                let id = self.mount_sealed(parent, dependencies, provisions, sealed)?;
                Ok(json!({"id":id.to_string()}))
            }
            Command::Prepare { id } => Ok(json!({"generation":self.prepare(id)?.to_string()})),
            Command::Seal { id, dependencies } => {
                self.kernel
                    .core
                    .seal_declarations(id, dependencies.into_iter().map(Into::into).collect())?;
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
                    json!({"actions":actions,"released":self.kernel.core.drain_released().into_iter().map(|value|value.to_string()).collect::<Vec<_>>()}),
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
                    self.kernel.core.set_checked(publication, true);
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
                self.availability.notify(&mut self.kernel.core, &ports)?;
                Ok(json!({"checks":self.check_actions()?}))
            }
            Command::ValidateCheck { ticket } => Ok(
                json!({"current":ticket.domain == self.domain && self.availability.current(&ticket, &self.kernel.core)}),
            ),
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
                Ok(
                    json!({"accepted":self.availability.complete(ticket, &mut self.kernel.core, available, error)?}),
                )
            }
            Command::Snapshot => Ok(self.snapshot()),
            Command::SnapshotState => Ok(self.snapshot_state()),
        }
    }
}
