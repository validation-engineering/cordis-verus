//! Exactly-once completion tokens shared by lifecycle executors.
//!
//! Cancellation does not consume a token. An admitted setup or cleanup stays
//! outstanding until its result lands; callbacks and their effects remain host
//! responsibilities. Completed entries are removed, while the monotonic action
//! counter prevents stale tokens from aliasing later work.
use vstd::prelude::*;

verus! {

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum ActionKind { Setup, Cleanup }

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub struct ActionTicket {
    pub domain: u64,
    pub id: usize,
    pub generation: u64,
    pub action: u64,
    pub kind: ActionKind,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum ActionError { Capacity, Pending, WrongDomain, Stale }

pub struct ActionLedger {
    domain: u64,
    next: u64,
    entries: Vec<ActionTicket>,
}

impl ActionLedger {
    pub closed spec fn domain_id(&self) -> u64 { self.domain }
    pub closed spec fn next_id(&self) -> u64 { self.next }
    pub closed spec fn records(&self) -> Seq<ActionTicket> { self.entries@ }
    pub open spec fn recorded(&self, ticket: ActionTicket) -> bool { self.records().contains(ticket) }
    pub open spec fn outstanding(&self, id: usize) -> bool {
        exists|i: int| 0 <= i < self.records().len() && self.records()[i].id == id
    }
    pub open spec fn unchanged(&self, prior: &Self) -> bool {
        self.domain_id() == prior.domain_id() && self.next_id() == prior.next_id() && self.records() == prior.records()
    }
    pub closed spec fn wf(&self) -> bool {
        &&& self.next > 0
        &&& forall|i: int| 0 <= i < self.entries.len() ==> self.entries[i].domain == self.domain
            && 0 < self.entries[i].action < self.next
        &&& forall|i: int, j: int| 0 <= i < j < self.entries.len()
            ==> self.entries[i].id != self.entries[j].id && self.entries[i].action != self.entries[j].action
    }

    /// Exact pending tickets for the same owner are identical. This exposes the
    /// needed uniqueness fact without unfolding storage invariants in clients.
    pub proof fn recorded_owner_unique(&self, a: ActionTicket, b: ActionTicket)
        requires self.wf(), self.recorded(a), self.recorded(b), a.id == b.id,
        ensures a == b,
    {
        let i = choose|i:int| 0 <= i < self.entries.len() && self.entries[i] == a;
        let j = choose|j:int| 0 <= j < self.entries.len() && self.entries[j] == b;
        if i < j { assert(a.id != b.id); }
        if j < i { assert(a.id != b.id); }
    }

    pub proof fn recorded_bounds(&self,ticket:ActionTicket)
        requires self.wf(),self.recorded(ticket),
        ensures ticket.domain==self.domain_id(),0<ticket.action<self.next_id(),
    {
        let i=choose|i:int| 0<=i<self.entries.len() && self.entries[i]==ticket;
    }

    pub fn new(domain: u64) -> (ledger: Self)
        ensures ledger.wf(), ledger.domain_id() == domain, ledger.next_id() == 1,
            ledger.records().len() == 0,
    { Self { domain, next: 1, entries: Vec::new() } }

    pub fn domain(&self) -> (domain: u64)
        ensures domain == self.domain_id(),
    { self.domain }

    pub fn len(&self) -> (count: usize)
        ensures count == self.records().len(),
    { self.entries.len() }

    pub fn is_empty(&self) -> (empty: bool)
        ensures empty == (self.records().len() == 0),
    { self.entries.len() == 0 }

    /// Preflight a batch without reserving or consuming identities.
    pub fn check_capacity(&self, count: u64) -> (out: Result<(), ActionError>)
        ensures out.is_ok() == (self.next_id() as int + count <= u64::MAX),
    {
        if count > u64::MAX - self.next { Err(ActionError::Capacity) } else { Ok(()) }
    }

    pub fn pending(&self, id: usize) -> (out: Option<ActionTicket>)
        ensures out.is_some() ==> self.recorded(out.unwrap()) && out.unwrap().id == id,
            out.is_none() == !self.outstanding(id),
    {
        let mut i = 0;
        while i < self.entries.len()
            invariant i <= self.entries.len(),
                forall|j: int| 0 <= j < i ==> self.entries[j].id != id,
            decreases self.entries.len() - i,
        {
            if self.entries[i].id == id { return Some(self.entries[i]); }
            i += 1;
        }
        None
    }

    pub fn can_issue(&self, id: usize) -> (out: Result<(), ActionError>)
        ensures out.is_ok() == (!self.outstanding(id) && self.next_id() < u64::MAX && self.records().len() < usize::MAX),
    {
        if self.pending(id).is_some() { return Err(ActionError::Pending); }
        if self.next == u64::MAX || self.entries.len() == usize::MAX { return Err(ActionError::Capacity); }
        Ok(())
    }

    /// The host supplies episode metadata only after kernel admission succeeds.
    pub fn issue(&mut self, id: usize, generation: u64, kind: ActionKind) -> (out: Result<ActionTicket, ActionError>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).domain_id() == old(self).domain_id(),
            out.is_ok() == (!old(self).outstanding(id) && old(self).next_id() < u64::MAX && old(self).records().len() < usize::MAX),
            out.is_err() ==> final(self).unchanged(old(self)),
            out.is_ok() ==> (forall|n:usize| final(self).outstanding(n) == (n == id || old(self).outstanding(n))),
            out.is_ok() ==> 0 < out.unwrap().action,
            out.is_ok() ==> out.unwrap() == (ActionTicket { domain: old(self).domain_id(), id, generation,
                    action: old(self).next_id(), kind })
                && final(self).records() == old(self).records().push(out.unwrap())
                && final(self).next_id() == old(self).next_id() + 1,
    {
        self.can_issue(id)?;
        let ticket = ActionTicket { domain: self.domain, id, generation, action: self.next, kind };
        self.next += 1;
        let ghost before = self.entries@;
        self.entries.push(ticket);
        proof {
            assert forall|n:usize| self.outstanding(n) == (n == id || old(self).outstanding(n)) by {
                if n == id { assert(self.entries[before.len() as int].id == n); }
                if old(self).outstanding(n) {
                    let j = choose|j:int| 0 <= j < before.len() && before[j].id == n;
                    assert(self.entries[j].id == n);
                }
                if self.outstanding(n) {
                    let j = choose|j:int| 0 <= j < self.entries.len() && self.entries[j].id == n;
                    if j < before.len() { assert(before[j].id == n); }
                    else { assert(n == id); }
                }
            }
        }
        Ok(ticket)
    }

    /// Consume only the exact domain/owner/episode/action/kind tuple. No API
    /// removes an action merely because its episode has been cancelled.
    pub fn complete(&mut self, ticket: ActionTicket) -> (out: Result<(), ActionError>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).domain_id() == old(self).domain_id(),
            final(self).next_id() == old(self).next_id(),
            out.is_ok() == old(self).recorded(ticket),
            out.is_ok() ==> (forall|n:usize| final(self).outstanding(n) == (n != ticket.id && old(self).outstanding(n))),
            out.is_err() ==> final(self).unchanged(old(self)),
            out.is_ok() ==> old(self).recorded(ticket) && !final(self).outstanding(ticket.id)
                && final(self).records().len() + 1 == old(self).records().len(),
            out.is_ok() ==> (forall|other: ActionTicket| other != ticket
                ==> final(self).recorded(other) == old(self).recorded(other)),
    {
        if ticket.domain != self.domain { return Err(ActionError::WrongDomain); }
        let mut i = 0;
        while i < self.entries.len()
            invariant i <= self.entries.len(), self.wf(), self == old(self),
                forall|j: int| 0 <= j < i ==> self.entries[j].id != ticket.id,
            decreases self.entries.len() - i,
        {
            let pending = self.entries[i];
            if pending.id == ticket.id {
                if pending != ticket { return Err(ActionError::Stale); }
                let ghost before = self.entries@;
                self.entries.remove(i);
                proof {
                    assert forall|a: int| 0 <= a < self.entries.len() implies self.entries[a].domain == self.domain
                        && 0 < self.entries[a].action < self.next by {
                        let b = if a < i { a } else { a + 1 };
                        assert(self.entries[a] == before[b]);
                    }
                    assert forall|a: int, b: int| 0 <= a < b < self.entries.len()
                        implies self.entries[a].id != self.entries[b].id && self.entries[a].action != self.entries[b].action by {
                        let old_a = if a < i { a } else { a + 1 };
                        let old_b = if b < i { b } else { b + 1 };
                        assert(self.entries[a] == before[old_a]);
                        assert(self.entries[b] == before[old_b]);
                        assert(old_a < old_b);
                    }
                    assert forall|a: int| 0 <= a < self.entries.len() implies self.entries[a].id != ticket.id by {
                        let b = if a < i { a } else { a + 1 };
                        assert(self.entries[a] == before[b]);
                    }
                    assert forall|other: ActionTicket| other != ticket
                        implies self.entries@.contains(other) == before.contains(other) by {
                        if before.contains(other) {
                            let a = choose|a: int| 0 <= a < before.len() && before[a] == other;
                            let b = if a < i { a } else { a - 1 };
                            assert(a != i);
                            assert(self.entries[b] == other);
                        }
                        if self.entries@.contains(other) {
                            let a = choose|a: int| 0 <= a < self.entries.len() && self.entries[a] == other;
                            let b = if a < i { a } else { a + 1 };
                            assert(before[b] == other);
                        }
                    }
                    assert forall|n:usize| self.outstanding(n) == (n != ticket.id && old(self).outstanding(n)) by {
                        if self.outstanding(n) {
                            let a = choose|a:int| 0 <= a < self.entries.len() && self.entries[a].id == n;
                            let b = if a < i { a } else { a + 1 };
                            assert(before[b].id == n);
                        }
                        if n != ticket.id && old(self).outstanding(n) {
                            let a = choose|a:int| 0 <= a < before.len() && before[a].id == n;
                            assert(a != i);
                            let b = if a < i { a } else { a - 1 };
                            assert(self.entries[b].id == n);
                        }
                    }
                }
                return Ok(());
            }
            i += 1;
        }
        Err(ActionError::Stale)
    }
}

}
