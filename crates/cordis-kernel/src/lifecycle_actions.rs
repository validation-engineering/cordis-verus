//! Verified admission, reply, retry, and finish gates for host cleanup actions.
//!
//! The host reports callback outcomes. `Succeeded` is that report, not a proof
//! about callback effects. `Drained` records exhaustion of an ordinary Rust
//! `FnOnce` cleanup sequence, including entries whose calls failed; it does not
//! assert that every callback succeeded. Both may authorize lifecycle release.
//! `Failed` retains the obligation and permits a fresh, explicitly requested retry.
use crate::action_ledger::{ActionError, ActionKind, ActionLedger, ActionTicket};
use crate::{Error, Kernel, Phase};
use vstd::prelude::*;

verus! {

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum CleanupOutcome { Failed, Succeeded, Drained }

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
struct CleanupRecord {
    ticket: ActionTicket,
    // None is allocated at admission, before a host reply can arrive.
    outcome: Option<CleanupOutcome>,
}

pub struct LifecycleActions {
    ledger: ActionLedger,
    cleanups: Vec<CleanupRecord>,
}

impl LifecycleActions {
    pub closed spec fn domain_id(&self) -> u64 { self.ledger.domain_id() }
    pub closed spec fn next_id(&self) -> u64 { self.ledger.next_id() }
    pub closed spec fn outstanding(&self, id: usize) -> bool { self.ledger.outstanding(id) }
    pub closed spec fn recorded(&self, ticket: ActionTicket) -> bool { self.ledger.recorded(ticket) }
    pub closed spec fn has_cleanup(&self, id: usize) -> bool {
        exists|i:int| 0 <= i < self.cleanups.len() && self.cleanups[i].ticket.id == id
    }
    pub closed spec fn reported(&self, ticket: ActionTicket, outcome: CleanupOutcome) -> bool {
        exists|i:int| 0 <= i < self.cleanups.len()
            && self.cleanups[i] == (CleanupRecord { ticket, outcome: Some(outcome) })
    }
    pub closed spec fn eligible(&self, id: usize, generation: u64) -> bool {
        exists|i:int| 0 <= i < self.cleanups.len() && self.cleanups[i].ticket.id == id
            && self.cleanups[i].ticket.generation == generation
            && self.cleanups[i].outcome.is_some()
            && self.cleanups[i].outcome.unwrap() != CleanupOutcome::Failed
    }
    pub closed spec fn failed(&self, id: usize, generation: u64) -> bool {
        exists|i:int| 0 <= i < self.cleanups.len() && self.cleanups[i].ticket.id == id
            && self.cleanups[i].ticket.generation == generation
            && self.cleanups[i].outcome == Some(CleanupOutcome::Failed)
    }
    pub closed spec fn blocked_spec(&self, id: usize) -> bool {
        self.outstanding(id) || self.has_cleanup(id)
    }
    pub closed spec fn same_cleanup_records(&self, prior: &Self) -> bool {
        self.cleanups@ == prior.cleanups@
    }
    pub closed spec fn capacity_enabled(&self, count: u64) -> bool {
        self.next_id() as int + count <= u64::MAX
            && self.ledger.records().len() + count <= usize::MAX
            && self.cleanups.len() + count <= usize::MAX
    }
    pub closed spec fn cleanup_reply_enabled(&self, ticket: ActionTicket) -> bool {
        ticket.kind == ActionKind::Cleanup && self.recorded(ticket)
            && exists|i:int| 0 <= i < self.cleanups.len()
                && self.cleanups[i] == (CleanupRecord { ticket, outcome: None })
    }
    pub closed spec fn same(&self, prior: &Self) -> bool {
        self.ledger.unchanged(&prior.ledger) && self.cleanups@ == prior.cleanups@
    }
    pub closed spec fn wf(&self) -> bool {
        &&& self.ledger.wf()
        &&& forall|i:int| 0 <= i < self.cleanups.len() ==> {
            let r = #[trigger] self.cleanups[i];
            &&& r.ticket.kind == ActionKind::Cleanup
            &&& r.ticket.domain == self.domain_id()
            &&& 0 < r.ticket.action < self.next_id()
            &&& if r.outcome.is_none() { self.recorded(r.ticket) }
                else { !self.outstanding(r.ticket.id) }
        }
        &&& forall|i:int, j:int| 0 <= i < j < self.cleanups.len()
            ==> self.cleanups[i].ticket.id != self.cleanups[j].ticket.id
    }
    /// A free owner slot and both bounded storage/counter preflights. Cleanup
    /// receipt space is reserved by inserting its Pending record at admission.
    pub closed spec fn admission_enabled(&self, id: usize) -> bool {
        !self.blocked_spec(id) && self.next_id() < u64::MAX
            && self.ledger.records().len() < usize::MAX && self.cleanups.len() < usize::MAX
    }
    pub closed spec fn reservation(kernel: &Kernel, id: usize) -> bool {
        kernel.phase_of(id) == Some(Phase::Inactive) && kernel.is_retired(id)
            && kernel.generation_of(id) == Some(0)
    }
    pub closed spec fn finish_enabled(&self, kernel: &Kernel, id: usize) -> bool {
        kernel.is_restoring(id) && kernel.generation_of(id).is_some()
            && self.eligible(id, kernel.generation_of(id).unwrap())
    }
    pub closed spec fn reservation_finish_enabled(&self, kernel: &Kernel, id: usize) -> bool {
        Self::reservation(kernel, id) && self.eligible(id, 0)
    }
    pub closed spec fn retry_enabled(&self, kernel: &Kernel, id: usize) -> bool {
        kernel.generation_of(id).is_some()
            && self.failed(id, kernel.generation_of(id).unwrap())
            && (kernel.is_restoring(id) || Self::reservation(kernel, id))
            && self.next_id() < u64::MAX && self.ledger.records().len() < usize::MAX
    }

    pub fn new(domain: u64) -> (out: Self)
        ensures out.wf(), out.domain_id() == domain, out.next_id() == 1,
            forall|id:usize| !out.blocked_spec(id),
    {
        Self { ledger: ActionLedger::new(domain), cleanups: Vec::new() }
    }

    pub fn domain(&self) -> (out: u64)
        ensures out == self.domain_id(),
    { self.ledger.domain() }

    /// Batch preflight is not a reservation; each actual admission checks again.
    pub fn check_capacity(&self, count: u64) -> (out: Result<(), ActionError>)
        ensures out.is_ok() == self.capacity_enabled(count),
    {
        self.ledger.check_capacity(count)?;
        if count as u128 > (usize::MAX - self.ledger.len()) as u128
            || count as u128 > (usize::MAX - self.cleanups.len()) as u128 {
            return Err(ActionError::Capacity);
        }
        Ok(())
    }

    pub fn pending(&self, id: usize) -> (out: Option<ActionTicket>)
        ensures out.is_some() ==> self.recorded(out.unwrap()) && out.unwrap().id == id,
            out.is_none() == !self.outstanding(id),
    { self.ledger.pending(id) }

    fn cleanup_index(&self, id: usize) -> (out: Option<usize>)
        ensures out.is_some() ==> out.unwrap() < self.cleanups.len()
                && self.cleanups[out.unwrap() as int].ticket.id == id,
            out.is_none() == !self.has_cleanup(id),
    {
        let mut i = 0;
        while i < self.cleanups.len()
            invariant i <= self.cleanups.len(),
                forall|j:int| 0 <= j < i ==> self.cleanups[j].ticket.id != id,
            decreases self.cleanups.len() - i,
        {
            if self.cleanups[i].ticket.id == id { return Some(i); }
            i += 1;
        }
        None
    }

    pub fn blocked(&self, id: usize) -> (out: bool)
        ensures out == self.blocked_spec(id),
    { self.pending(id).is_some() || self.cleanup_index(id).is_some() }

    fn preflight(&self, id: usize) -> (out: Result<(), Error>)
        ensures out.is_ok() == self.admission_enabled(id),
    {
        if self.blocked(id) { return Err(Error::Relied); }
        if self.ledger.can_issue(id).is_err() || self.cleanups.len() == usize::MAX {
            return Err(Error::Capacity);
        }
        Ok(())
    }

    /// This helper runs only after preflight. Its ticket allocation cannot return
    /// an error after the kernel has admitted the corresponding lifecycle step.
    fn issue(&mut self, id: usize, generation: u64, kind: ActionKind) -> (ticket: ActionTicket)
        requires old(self).wf(), old(self).admission_enabled(id),
        ensures final(self).wf(), final(self).domain_id() == old(self).domain_id(),
            ticket == (ActionTicket { domain: old(self).domain_id(), id, generation,
                action: old(self).next_id(), kind }), final(self).recorded(ticket),
            final(self).next_id() == old(self).next_id() + 1,
            final(self).outstanding(id),
            kind == ActionKind::Cleanup ==> final(self).has_cleanup(id)
                && final(self).cleanup_reply_enabled(ticket),
    {
        let ghost prior = *self;
        let ticket = self.ledger.issue(id, generation, kind).unwrap();
        proof {
            assert forall|i:int| 0 <= i < self.cleanups.len() implies {
                let r = #[trigger] self.cleanups[i];
                &&& r.ticket.kind == ActionKind::Cleanup
                &&& r.ticket.domain == self.domain_id()
                &&& 0 < r.ticket.action < self.next_id()
                &&& if r.outcome.is_none() { self.recorded(r.ticket) }
                    else { !self.outstanding(r.ticket.id) }
            } by {
                assert(prior.cleanups[i].ticket.id != ticket.id);
                if self.cleanups[i].outcome.is_none() {
                    assert(prior.ledger.records().contains(self.cleanups[i].ticket));
                    let j = choose|j:int| 0 <= j < prior.ledger.records().len()
                        && prior.ledger.records()[j] == self.cleanups[i].ticket;
                    assert(self.ledger.records()[j] == self.cleanups[i].ticket);
                    assert(self.ledger.records().contains(self.cleanups[i].ticket));
                }
            }
        }
        if kind == ActionKind::Cleanup {
            self.cleanups.push(CleanupRecord { ticket, outcome: None });
            assert(self.cleanups[prior.cleanups.len() as int].ticket.id == id);
        }
        ticket
    }

    pub fn begin(&mut self, kernel: &mut Kernel, id: usize) -> (out: Result<ActionTicket, Error>)
        requires old(self).wf(), old(kernel).wf(),
        ensures final(self).wf(), final(kernel).wf(),
            out.is_ok() == (old(self).admission_enabled(id) && old(kernel).begin_enabled(id)),
            out.is_err() ==> final(self).same(old(self)) && final(kernel).unchanged(old(kernel)),
            out.is_ok() ==> out.unwrap().kind == ActionKind::Setup
                && out.unwrap().id == id && out.unwrap().domain == old(self).domain_id()
                && final(self).recorded(out.unwrap())
                && final(kernel).generation_of(id) == Some(out.unwrap().generation),
    {
        proof {
            reveal(Kernel::unchanged);
            reveal(Kernel::same_bindings);
            reveal(Kernel::registered);
            reveal(Kernel::phase_of);
            reveal(Kernel::is_retired);
            reveal(Kernel::is_restoring);
            reveal(Kernel::generation_of);
        }
        self.preflight(id)?;
        kernel.begin(id)?;
        let generation = kernel.episode_generation(id).unwrap();
        Ok(self.issue(id, generation, ActionKind::Setup))
    }

    pub fn begin_cleanup(&mut self, kernel: &mut Kernel, id: usize) -> (out: Result<ActionTicket, Error>)
        requires old(self).wf(), old(kernel).wf(),
        ensures final(self).wf(), final(kernel).wf(),
            out.is_ok() == (old(self).admission_enabled(id) && old(kernel).cleanup_enabled(id)),
            final(kernel).same_bindings(old(kernel)),
            final(kernel).paper() == old(kernel).paper(),
            out.is_ok() ==> final(kernel).restoration_guarded(id),
            out.is_err() ==> final(self).same(old(self)) && final(kernel).unchanged(old(kernel)),
            out.is_ok() ==> out.unwrap().kind == ActionKind::Cleanup && out.unwrap().id == id
                && final(self).recorded(out.unwrap()) && final(self).has_cleanup(id)
                && final(self).cleanup_reply_enabled(out.unwrap())
                && final(kernel).is_restoring(id)
                && final(kernel).generation_of(id) == Some(out.unwrap().generation),
    {
        proof {
            reveal(Kernel::unchanged);
            reveal(Kernel::same_bindings);
            reveal(Kernel::registered);
            reveal(Kernel::phase_of);
            reveal(Kernel::is_retired);
            reveal(Kernel::is_restoring);
            reveal(Kernel::generation_of);
        }
        self.preflight(id)?;
        kernel.begin_cleanup(id)?;
        proof { reveal(Kernel::is_restoring); reveal(Kernel::generation_of); }
        let generation = kernel.episode_generation(id).unwrap();
        Ok(self.issue(id, generation, ActionKind::Cleanup))
    }

    pub fn begin_reservation_cleanup(&mut self, kernel: &Kernel, id: usize) -> (out: Result<ActionTicket, Error>)
        requires old(self).wf(), kernel.wf(),
        ensures final(self).wf(),
            out.is_ok() == (old(self).admission_enabled(id) && Self::reservation(kernel, id)),
            out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> out.unwrap().kind == ActionKind::Cleanup && out.unwrap().id == id
                && out.unwrap().generation == 0 && final(self).recorded(out.unwrap())
                && final(self).has_cleanup(id) && final(self).cleanup_reply_enabled(out.unwrap()),
    {
        proof {
            reveal(Kernel::unchanged);
            reveal(Kernel::same_bindings);
            reveal(Kernel::registered);
            reveal(Kernel::phase_of);
            reveal(Kernel::is_retired);
            reveal(Kernel::is_restoring);
            reveal(Kernel::generation_of);
        }
        if !kernel.contains(id) { return Err(Error::Unknown); }
        if kernel.phase(id) != Some(Phase::Inactive) || !kernel.retired(id)
            || kernel.episode_generation(id) != Some(0) { return Err(Error::InvalidState); }
        self.preflight(id)?;
        Ok(self.issue(id, 0, ActionKind::Cleanup))
    }

    pub fn complete_setup(&mut self, ticket: ActionTicket) -> (out: Result<(), ActionError>)
        requires old(self).wf(),
        ensures final(self).wf(),
            out.is_ok() == (ticket.kind == ActionKind::Setup && old(self).recorded(ticket)),
            out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> !final(self).outstanding(ticket.id),
            final(self).same_cleanup_records(old(self)),
    {
        if ticket.kind != ActionKind::Setup { return Err(ActionError::Stale); }
        let ghost prior = *self;
        self.ledger.complete(ticket)?;
        proof {
            assert forall|i:int| 0 <= i < self.cleanups.len() && self.cleanups[i].ticket.id == ticket.id
                implies self.cleanups[i].outcome.is_some() by {
                if self.cleanups[i].outcome.is_none() {
                    prior.ledger.recorded_owner_unique(self.cleanups[i].ticket, ticket);
                }
            }
            self.completion_frame(&prior, ticket);
        }
        Ok(())
    }

    /// The exact pending tuple is consumed once. A failed reply is retained and
    /// cannot authorize either finish method. Duplicate/stale replies do nothing.
    pub fn complete_cleanup(&mut self, ticket: ActionTicket, outcome: CleanupOutcome) -> (out: Result<(), ActionError>)
        requires old(self).wf(),
        ensures final(self).wf(),
            out.is_ok() == old(self).cleanup_reply_enabled(ticket),
            out.is_ok() ==> old(self).recorded(ticket) && ticket.kind == ActionKind::Cleanup
                && final(self).reported(ticket, outcome) && !final(self).outstanding(ticket.id),
            out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> final(self).eligible(ticket.id, ticket.generation) == (outcome != CleanupOutcome::Failed),
            out.is_ok() && outcome == CleanupOutcome::Failed
                ==> !final(self).eligible(ticket.id, ticket.generation),
    {
        if ticket.kind != ActionKind::Cleanup { return Err(ActionError::Stale); }
        let i = match self.cleanup_index(ticket.id) { Some(i) => i, None => return Err(ActionError::Stale) };
        if self.cleanups[i].ticket != ticket || self.cleanups[i].outcome.is_some() {
            return Err(ActionError::Stale);
        }
        let ghost prior = *self;
        self.ledger.complete(ticket)?;
        self.cleanups.set(i, CleanupRecord { ticket, outcome: Some(outcome) });
        proof {
            self.completion_frame(&prior, ticket);
            assert(self.cleanups[i as int] == (CleanupRecord { ticket, outcome: Some(outcome) }));
            assert(self.reported(ticket, outcome));
        }
        Ok(())
    }

    // Nonmatching records keep their pending/settled ledger relationship when
    // one exact ticket is consumed. The matching record, if any, was updated.
    proof fn completion_frame(&self, prior: &Self, ticket: ActionTicket)
        requires prior.wf(), self.ledger.wf(), prior.recorded(ticket),
            self.ledger.domain_id() == prior.ledger.domain_id(),
            self.ledger.next_id() == prior.ledger.next_id(),
            forall|id:usize| self.outstanding(id) == (id != ticket.id && prior.outstanding(id)),
            forall|other:ActionTicket| other != ticket ==> self.recorded(other) == prior.recorded(other),
            self.cleanups.len() == prior.cleanups.len(),
            forall|i:int| 0 <= i < self.cleanups.len() ==> self.cleanups[i].ticket == prior.cleanups[i].ticket
                && (self.cleanups[i].ticket.id != ticket.id ==> self.cleanups[i] == prior.cleanups[i])
                && (self.cleanups[i].ticket.id == ticket.id ==> self.cleanups[i].outcome.is_some()),
        ensures self.wf(),
    {
        assert forall|i:int| 0 <= i < self.cleanups.len() implies {
            let r = #[trigger] self.cleanups[i];
            &&& r.ticket.kind == ActionKind::Cleanup
            &&& r.ticket.domain == self.domain_id()
            &&& 0 < r.ticket.action < self.next_id()
            &&& if r.outcome.is_none() { self.recorded(r.ticket) }
                else { !self.outstanding(r.ticket.id) }
        } by { }
    }

    /// Reissue only a failed result of the current episode. A retired reservation
    /// has generation zero and never entered Loading, but uses the same protocol.
    pub fn retry_cleanup(&mut self, kernel: &Kernel, id: usize) -> (out: Result<ActionTicket, Error>)
        requires old(self).wf(), kernel.wf(),
        ensures final(self).wf(),
            out.is_ok() == old(self).retry_enabled(kernel, id),
            out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> final(self).recorded(out.unwrap()) && out.unwrap().id == id
                && out.unwrap().kind == ActionKind::Cleanup
                && kernel.generation_of(id) == Some(out.unwrap().generation)
                && out.unwrap().action == old(self).next_id()
                && old(self).failed(id, out.unwrap().generation)
                && !final(self).eligible(id, out.unwrap().generation)
                && final(self).cleanup_reply_enabled(out.unwrap())
                && final(self).next_id() == old(self).next_id() + 1,
    {
        proof {
            reveal(Kernel::unchanged);
            reveal(Kernel::same_bindings);
            reveal(Kernel::registered);
            reveal(Kernel::phase_of);
            reveal(Kernel::is_retired);
            reveal(Kernel::is_restoring);
            reveal(Kernel::generation_of);
        }
        let i = match self.cleanup_index(id) { Some(i) => i, None => return Err(Error::InvalidState) };
        let previous = self.cleanups[i];
        if previous.outcome != Some(CleanupOutcome::Failed) { return Err(Error::InvalidState); }
        if kernel.episode_generation(id) != Some(previous.ticket.generation) { return Err(Error::InvalidState); }
        if !kernel.cleanup_started(id)
            && !(kernel.phase(id) == Some(Phase::Inactive) && kernel.retired(id)
                && previous.ticket.generation == 0) { return Err(Error::InvalidState); }
        if self.ledger.can_issue(id).is_err() { return Err(Error::Capacity); }
        let ghost prior = *self;
        let ticket = self.ledger.issue(id, previous.ticket.generation, ActionKind::Cleanup).unwrap();
        self.cleanups.set(i, CleanupRecord { ticket, outcome: None });
        proof {
            assert forall|j:int| 0 <= j < self.cleanups.len() implies {
                let r = #[trigger] self.cleanups[j];
                &&& r.ticket.kind == ActionKind::Cleanup
                &&& r.ticket.domain == self.domain_id()
                &&& 0 < r.ticket.action < self.next_id()
                &&& if r.outcome.is_none() { self.recorded(r.ticket) }
                    else { !self.outstanding(r.ticket.id) }
            } by {
                if j != i {
                    assert(prior.cleanups[j].ticket.id != id);
                    if self.cleanups[j].outcome.is_none() {
                        assert(prior.ledger.records().contains(self.cleanups[j].ticket));
                        let k = choose|k:int| 0 <= k < prior.ledger.records().len()
                            && prior.ledger.records()[k] == self.cleanups[j].ticket;
                        assert(self.ledger.records()[k] == self.cleanups[j].ticket);
                        assert(self.ledger.records().contains(self.cleanups[j].ticket));
                    }
                }
            }
            assert(self.cleanups[i as int] == (CleanupRecord { ticket, outcome: None }));
            assert(self.cleanup_reply_enabled(ticket));
        }
        Ok(ticket)
    }

    fn remove_cleanup(&mut self, i: usize)
        requires old(self).wf(), i < old(self).cleanups.len(),
            old(self).cleanups[i as int].outcome.is_some(),
        ensures final(self).wf(), final(self).ledger.unchanged(&old(self).ledger),
            !final(self).has_cleanup(old(self).cleanups[i as int].ticket.id),
    {
        let ghost prior = *self;
        self.cleanups.remove(i);
        proof {
            assert forall|a:int| 0 <= a < self.cleanups.len() implies {
                let r = #[trigger] self.cleanups[a];
                &&& r.ticket.kind == ActionKind::Cleanup
                &&& r.ticket.domain == self.domain_id()
                &&& 0 < r.ticket.action < self.next_id()
                &&& if r.outcome.is_none() { self.recorded(r.ticket) }
                    else { !self.outstanding(r.ticket.id) }
            } by {
                let b = if a < i { a } else { a + 1 };
                assert(self.cleanups[a] == prior.cleanups[b]);
            }
            assert forall|a:int,b:int| 0 <= a < b < self.cleanups.len()
                implies self.cleanups[a].ticket.id != self.cleanups[b].ticket.id by {
                let pa = if a < i { a } else { a + 1 };
                let pb = if b < i { b } else { b + 1 };
                assert(self.cleanups[a] == prior.cleanups[pa]);
                assert(self.cleanups[b] == prior.cleanups[pb]);
            }
            assert forall|a:int| 0 <= a < self.cleanups.len()
                implies self.cleanups[a].ticket.id != prior.cleanups[i as int].ticket.id by {
                let b = if a < i { a } else { a + 1 };
                assert(self.cleanups[a] == prior.cleanups[b]);
            }
        }
    }

    /// The receipt gate and the actual commitment release occur in this same
    /// verified function. Failure cannot change any kernel state or commitments.
    pub fn finish_cleanup(&mut self, kernel: &mut Kernel, id: usize) -> (out: Result<(), Error>)
        requires old(self).wf(), old(kernel).wf(),
        ensures final(self).wf(), final(kernel).wf(),
            out.is_ok() == old(self).finish_enabled(old(kernel), id),
            out.is_err() ==> final(self).same(old(self)) && final(kernel).unchanged(old(kernel))
                && final(kernel).same_bindings(old(kernel)),
            out.is_ok() ==> final(kernel).phase_of(id) == Some(Phase::Inactive)
                && final(kernel).no_committed(id) && !final(self).blocked_spec(id)
                && crate::refinement::step(old(kernel).paper(), final(kernel).paper(), id, crate::refinement::Rule::Unload),
    {
        proof {
            reveal(Kernel::unchanged);
            reveal(Kernel::same_bindings);
            reveal(Kernel::registered);
            reveal(Kernel::phase_of);
            reveal(Kernel::is_retired);
            reveal(Kernel::is_restoring);
            reveal(Kernel::generation_of);
        }
        let i = match self.cleanup_index(id) { Some(i) => i, None => return Err(Error::InvalidState) };
        let receipt = self.cleanups[i];
        if receipt.outcome.is_none() || receipt.outcome == Some(CleanupOutcome::Failed) {
            return Err(Error::InvalidState);
        }
        if kernel.episode_generation(id) != Some(receipt.ticket.generation) || !kernel.cleanup_started(id) {
            return Err(Error::InvalidState);
        }
        kernel.finish_cleanup(id)?;
        self.remove_cleanup(i);
        Ok(())
    }

    pub fn finish_reservation_cleanup(&mut self, kernel: &Kernel, id: usize) -> (out: Result<(), Error>)
        requires old(self).wf(), kernel.wf(),
        ensures final(self).wf(),
            out.is_ok() == old(self).reservation_finish_enabled(kernel, id),
            out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> !final(self).blocked_spec(id),
    {
        proof {
            reveal(Kernel::unchanged);
            reveal(Kernel::same_bindings);
            reveal(Kernel::registered);
            reveal(Kernel::phase_of);
            reveal(Kernel::is_retired);
            reveal(Kernel::is_restoring);
            reveal(Kernel::generation_of);
        }
        let i = match self.cleanup_index(id) { Some(i) => i, None => return Err(Error::InvalidState) };
        let receipt = self.cleanups[i];
        if receipt.outcome.is_none() || receipt.outcome == Some(CleanupOutcome::Failed)
            || receipt.ticket.generation != 0 { return Err(Error::InvalidState); }
        if kernel.phase(id) != Some(Phase::Inactive) || !kernel.retired(id)
            || kernel.episode_generation(id) != Some(0) { return Err(Error::InvalidState); }
        self.remove_cleanup(i);
        Ok(())
    }
}

}
