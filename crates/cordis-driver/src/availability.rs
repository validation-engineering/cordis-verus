//! Synchronous check callbacks use explicit snapshots, never execute under a
//! driver borrow, and cannot commit a result after publication/value/notification
//! changes. A new explicit notification is required after an invalidated check.
use crate::{DriverError, ServicePort};
use cordis_kernel::{node_runtime::NodeRuntime, publication::PublicationId};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct CheckTicket {
    #[serde(with = "crate::protocol::decimal")]
    pub domain: u64,
    #[serde(with = "crate::protocol::decimal")]
    pub consumer: usize,
    pub port: ServicePort,
    #[serde(with = "crate::protocol::decimal")]
    pub publication: usize,
    #[serde(with = "crate::protocol::decimal")]
    pub value_revision: u64,
    #[serde(with = "crate::protocol::decimal")]
    pub notification: u64,
    #[serde(with = "crate::protocol::decimal")]
    pub action: u64,
}
#[derive(Clone, Debug, Serialize)]
pub struct CheckAction {
    #[serde(with = "crate::protocol::decimal")]
    pub consumer: usize,
    pub port: ServicePort,
    #[serde(with = "crate::protocol::decimal")]
    pub publication: usize,
    #[serde(with = "crate::protocol::decimal")]
    pub value: u64,
    pub ticket: CheckTicket,
}
#[derive(Clone, Copy)]
pub(crate) struct Candidate {
    pub consumer: usize,
    pub port: ServicePort,
    pub publication: usize,
}
/// Only diagnostic text lives outside the checked ledger. It never authorizes
/// lifecycle progress or changes a ticket's acceptance.
pub(crate) struct Availability {
    errors: BTreeMap<(usize, u64, u64), String>,
}
impl From<&CheckTicket> for cordis_kernel::availability::CheckTicket {
    fn from(t: &CheckTicket) -> Self {
        Self {
            domain: t.domain,
            consumer: t.consumer,
            port: t.port.into(),
            publication: PublicationId(t.publication),
            value_revision: t.value_revision,
            notification: t.notification,
            action: t.action,
        }
    }
}
impl From<cordis_kernel::availability::CheckTicket> for CheckTicket {
    fn from(t: cordis_kernel::availability::CheckTicket) -> Self {
        Self {
            domain: t.domain,
            consumer: t.consumer,
            port: t.port.into(),
            publication: t.publication.0,
            value_revision: t.value_revision,
            notification: t.notification,
            action: t.action,
        }
    }
}
fn protocol_error(error: cordis_kernel::availability::CheckError) -> DriverError {
    match error {
        cordis_kernel::availability::CheckError::Capacity => {
            DriverError::new("Capacity", "check identity exhausted")
        }
        cordis_kernel::availability::CheckError::Stale => {
            DriverError::new("StaleCheck", "check is unknown or already completed")
        }
    }
}
impl Availability {
    pub fn new() -> Self {
        Self {
            errors: BTreeMap::new(),
        }
    }
    fn key(consumer: usize, port: ServicePort) -> (usize, u64, u64) {
        (consumer, port.key, port.realm)
    }
    pub fn notify(
        &mut self,
        core: &mut NodeRuntime,
        ports: &[ServicePort],
    ) -> Result<(), DriverError> {
        let ports: Vec<_> = ports.iter().copied().map(Into::into).collect();
        core.notify(&ports).map_err(protocol_error)
    }
    pub fn request(
        &mut self,
        core: &mut NodeRuntime,
        candidates: Vec<Candidate>,
    ) -> Result<Vec<CheckAction>, DriverError> {
        core.checks()
            .check_capacity(candidates.len() as u64)
            .map_err(protocol_error)?;
        let mut actions = Vec::new();
        for candidate in candidates {
            if let Some(action) = core
                .request_check(candidate.consumer, candidate.port.into())
                .map_err(protocol_error)?
            {
                let ticket: CheckTicket = action.ticket.into();
                actions.push(CheckAction {
                    consumer: ticket.consumer,
                    port: ticket.port,
                    publication: ticket.publication,
                    value: action.value,
                    ticket,
                });
            }
        }
        Ok(actions)
    }
    pub fn available(
        &self,
        core: &NodeRuntime,
        consumer: usize,
        port: ServicePort,
        publication: usize,
    ) -> bool {
        core.checks()
            .available(consumer, port.into(), PublicationId(publication))
    }
    pub fn current(&self, ticket: &CheckTicket, core: &NodeRuntime) -> bool {
        core.current_check(ticket.into())
    }
    pub fn complete(
        &mut self,
        ticket: CheckTicket,
        core: &mut NodeRuntime,
        available: bool,
        error: Option<String>,
    ) -> Result<bool, DriverError> {
        let current = core
            .complete_check((&ticket).into(), available)
            .map_err(protocol_error)?;
        if core
            .checks()
            .record(ticket.consumer, ticket.port.into())
            .is_some_and(|r| {
                r.publication.0 == ticket.publication && r.notification == ticket.notification
            })
        {
            let key = Self::key(ticket.consumer, ticket.port);
            if let Some(error) = error.or_else(|| {
                (!current).then(|| "check snapshot invalidated; notify to reevaluate".into())
            }) {
                self.errors.insert(key, error);
            } else {
                self.errors.remove(&key);
            }
        }
        Ok(current)
    }
    /// Explain cached state without issuing or accepting a callback.
    pub fn blocker(&self, candidate: Candidate, core: &NodeRuntime) -> serde_json::Value {
        use serde_json::json;
        let Some(record) = core
            .checks()
            .record(candidate.consumer, candidate.port.into())
        else {
            return json!({"code":"CheckNotEvaluated"});
        };
        if record.publication.0 != candidate.publication || record.dirty {
            return json!({"code":"CheckNotEvaluated"});
        }
        if let Some(action) = core.checks().pending().values().find(|a| {
            let t = a.ticket;
            t.consumer == candidate.consumer
                && t.port == candidate.port.into()
                && t.publication.0 == candidate.publication
                && t.notification == record.notification
        }) {
            let ticket: CheckTicket = action.ticket.into();
            return json!({"code":if self.current(&ticket,core) {"CheckPending"} else {"CheckInvalidated"},"ticket":ticket});
        }
        let error = self
            .errors
            .get(&Self::key(candidate.consumer, candidate.port));
        if record.last_current == Some(false) {
            return json!({"code":"CheckInvalidated","error":error});
        }
        if record.last_current.is_none() {
            return json!({"code":"CheckNotEvaluated"});
        }
        match error {
            Some(error) => json!({"code":"CheckError","error":error}),
            None => json!({"code":"CheckRejected"}),
        }
    }
    pub fn remove_consumer(&mut self, core: &mut NodeRuntime, consumer: usize) {
        core.forget_checks(consumer);
        self.errors.retain(|(id, _, _), _| *id != consumer);
    }
    pub fn diagnostics(&self, core: &NodeRuntime) -> Vec<serde_json::Value> {
        core.checks().records().keys().filter_map(|key|self.errors.get(key).map(|error|
            serde_json::json!({"consumer":key.0.to_string(),"key":key.1.to_string(),"realm":key.2.to_string(),"error":error}))).collect()
    }
}
