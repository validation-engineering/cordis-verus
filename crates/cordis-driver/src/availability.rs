//! Synchronous check callbacks use explicit snapshots, never execute under a
//! driver borrow, and cannot commit a result after publication/value/notification
//! changes. A new explicit notification is required after an invalidated check.
use crate::{DriverError, ServicePort};
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
    pub value: u64,
    pub value_revision: u64,
}
struct Record {
    publication: usize,
    notification: u64,
    dirty: bool,
    available: bool,
    error: Option<String>,
    // Diagnostic observation only; never used to admit a lifecycle transition.
    last_current: Option<bool>,
}
#[derive(Default)]
pub(crate) struct Availability {
    records: BTreeMap<(usize, u64, u64), Record>,
    pending: BTreeMap<u64, CheckTicket>,
    next_action: u64,
    notification: u64,
}
impl Availability {
    fn key(consumer: usize, port: ServicePort) -> (usize, u64, u64) {
        (consumer, port.key, port.realm)
    }
    pub fn notify(&mut self, ports: &[ServicePort]) -> Result<(), DriverError> {
        let next = self
            .notification
            .checked_add(1)
            .ok_or_else(|| DriverError::new("Capacity", "check notification identity exhausted"))?;
        self.notification = next;
        for ((_, key, realm), record) in &mut self.records {
            if ports.iter().any(|p| p.key == *key && p.realm == *realm) {
                record.notification = next;
                record.dirty = true;
            }
        }
        Ok(())
    }
    pub fn request(
        &mut self,
        domain: u64,
        candidates: Vec<Candidate>,
    ) -> Result<Vec<CheckAction>, DriverError> {
        self.next_action
            .checked_add(candidates.len() as u64)
            .ok_or_else(|| DriverError::new("Capacity", "check action identity exhausted"))?;
        let mut actions = Vec::new();
        for candidate in candidates {
            let key = Self::key(candidate.consumer, candidate.port);
            let record = self.records.entry(key).or_insert(Record {
                publication: candidate.publication,
                notification: self.notification,
                dirty: true,
                available: false,
                error: None,
                last_current: None,
            });
            if record.publication != candidate.publication {
                record.publication = candidate.publication;
                record.dirty = true;
                record.available = false;
                record.last_current = None;
            }
            if !record.dirty {
                continue;
            }
            record.dirty = false;
            let ticket = CheckTicket {
                domain,
                consumer: candidate.consumer,
                port: candidate.port,
                publication: candidate.publication,
                value_revision: candidate.value_revision,
                notification: record.notification,
                action: self.next_action,
            };
            self.next_action += 1;
            self.pending.insert(ticket.action, ticket.clone());
            actions.push(CheckAction {
                consumer: candidate.consumer,
                port: candidate.port,
                publication: candidate.publication,
                value: candidate.value,
                ticket,
            });
        }
        Ok(actions)
    }
    pub fn available(&self, consumer: usize, port: ServicePort, publication: usize) -> bool {
        self.records
            .get(&Self::key(consumer, port))
            .is_some_and(|r| r.publication == publication && r.available)
    }
    pub fn current(&self, ticket: &CheckTicket, candidate: Option<Candidate>) -> bool {
        self.pending.get(&ticket.action) == Some(ticket)
            && candidate.is_some_and(|c| {
                c.publication == ticket.publication && c.value_revision == ticket.value_revision
            })
            && self
                .records
                .get(&Self::key(ticket.consumer, ticket.port))
                .is_some_and(|r| {
                    r.publication == ticket.publication
                        && r.notification == ticket.notification
                        && !r.dirty
                })
    }
    pub fn complete(
        &mut self,
        ticket: CheckTicket,
        candidate: Option<Candidate>,
        available: bool,
        error: Option<String>,
    ) -> Result<bool, DriverError> {
        if self.pending.get(&ticket.action) != Some(&ticket) {
            return Err(DriverError::new(
                "StaleCheck",
                "check is unknown or already completed",
            ));
        }
        let current = self.current(&ticket, candidate);
        self.pending.remove(&ticket.action);
        if let Some(record) = self
            .records
            .get_mut(&Self::key(ticket.consumer, ticket.port))
        {
            // Never let an old callback overwrite a newer notification's result.
            if record.publication == ticket.publication
                && record.notification == ticket.notification
            {
                record.last_current = Some(current);
                record.available = current && available;
                record.error = error.or_else(|| {
                    (!current).then(|| "check snapshot invalidated; notify to reevaluate".into())
                });
            }
        }
        Ok(current)
    }
    /// Explain a currently unavailable check from the cached protocol state.
    /// This never requests a callback or accepts/invalidates a ticket.
    pub fn blocker(&self, candidate: Candidate) -> serde_json::Value {
        use serde_json::json;
        let Some(record) = self
            .records
            .get(&Self::key(candidate.consumer, candidate.port))
        else {
            return json!({"code": "CheckNotEvaluated"});
        };
        if record.publication != candidate.publication || record.dirty {
            return json!({"code": "CheckNotEvaluated"});
        }
        if let Some(ticket) = self.pending.values().find(|ticket| {
            ticket.consumer == candidate.consumer
                && ticket.port == candidate.port
                && ticket.publication == candidate.publication
                && ticket.notification == record.notification
        }) {
            return json!({
                "code": if self.current(ticket, Some(candidate)) { "CheckPending" } else { "CheckInvalidated" },
                "ticket": ticket,
            });
        }
        if record.last_current == Some(false) {
            return json!({"code": "CheckInvalidated", "error": record.error});
        }
        if record.last_current.is_none() {
            return json!({"code": "CheckNotEvaluated"});
        }
        match &record.error {
            Some(error) => json!({"code": "CheckError", "error": error}),
            None => json!({"code": "CheckRejected"}),
        }
    }

    pub fn remove_consumer(&mut self, consumer: usize) {
        self.records.retain(|(id, _, _), _| *id != consumer);
        // Outstanding callbacks still acknowledge their ticket exactly once.
    }
    pub fn diagnostics(&self) -> Vec<serde_json::Value> {
        self.records.iter().filter_map(|((id, key, realm), r)| r.error.as_ref().map(|error|
            serde_json::json!({"consumer":id.to_string(),"key":key.to_string(),"realm":realm.to_string(),"error":error}))).collect()
    }
}
