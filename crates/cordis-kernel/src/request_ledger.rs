//! Outstanding reverse requests, shared by the native transport and wait guard.
//!
//! Cancellation and dropping a future do not consume a request. Only an exact
//! receipt does; accepting a receipt says nothing about successful JS cleanup.
use crate::{wait_guard::WaitDecision, Kernel};
use vstd::prelude::*;

verus! {

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub struct RequestTicket {
    pub domain: u64,
    pub id: usize,
    pub generation: u64,
    pub session: u64,
    pub job: u64,
    pub request: u64,
    pub restoring: bool,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum RequestError { Capacity, WrongDomain, Stale, Mismatch }

pub struct RequestLedger {
    domain: u64,
    next: u64,
    entries: Vec<RequestTicket>,
}

impl RequestLedger {
    pub closed spec fn domain_id(&self) -> u64 { self.domain }
    pub closed spec fn next_id(&self) -> u64 { self.next }
    pub closed spec fn records(&self) -> Seq<RequestTicket> { self.entries@ }
    pub open spec fn recorded(&self, ticket: RequestTicket) -> bool { self.records().contains(ticket) }
    pub open spec fn outstanding(&self, session: u64, job: u64) -> bool {
        exists|i: int| 0 <= i < self.records().len()
            && self.records()[i].session == session && self.records()[i].job == job
    }
    pub open spec fn unchanged(&self, prior: &Self) -> bool {
        self.domain_id() == prior.domain_id() && self.next_id() == prior.next_id()
            && self.records() == prior.records()
    }
    pub closed spec fn wf(&self) -> bool {
        &&& self.next > 0
        &&& forall|i: int| 0 <= i < self.entries.len() ==> self.entries[i].domain == self.domain
            && 0 < self.entries[i].request < self.next
        &&& forall|i: int, j: int| 0 <= i < j < self.entries.len()
            ==> self.entries[i].request != self.entries[j].request
    }

    pub proof fn record_facts(&self)
        requires self.wf(),
        ensures self.next_id() > 0,
            forall|ticket:RequestTicket| self.recorded(ticket) ==> ticket.domain == self.domain_id()
                && 0 < ticket.request < self.next_id(),
    {
        assert forall|ticket:RequestTicket| self.recorded(ticket) implies ticket.domain == self.domain_id()
            && 0 < ticket.request < self.next_id() by {
            let i = choose|i:int| 0 <= i < self.entries.len() && self.entries[i] == ticket;
        }
    }

    pub fn new(domain: u64) -> (ledger: Self)
        ensures ledger.wf(), ledger.domain_id() == domain, ledger.next_id() == 1,
            ledger.records().len() == 0,
    { Self { domain, next: 1, entries: Vec::new() } }

    pub fn pending_count(&self) -> (out: usize)
        ensures out == self.records().len(),
    { self.entries.len() }

    pub fn domain(&self) -> (domain: u64)
        ensures domain == self.domain_id(),
    { self.domain }

    /// Monotonic allocation remembers completed identities without tombstones.
    pub fn issued(&self, request: u64) -> (out: bool)
        ensures out == (0 < request < self.next_id()),
    { 0 < request && request < self.next }

    pub fn pending(&self, request: u64) -> (out: Option<RequestTicket>)
        ensures out.is_some() ==> self.recorded(out.unwrap()) && out.unwrap().request == request,
            out.is_none() == !(exists|i:int| 0 <= i < self.records().len() && self.records()[i].request == request),
    {
        let mut i = 0;
        while i < self.entries.len()
            invariant i <= self.entries.len(),
                forall|j:int| 0 <= j < i ==> self.entries[j].request != request,
            decreases self.entries.len() - i,
        {
            if self.entries[i].request == request {
                proof { assert(self.records()[i as int].request == request); }
                return Some(self.entries[i]);
            }
            i += 1;
        }
        None
    }

    pub proof fn recorded_request_unique(&self, a: RequestTicket, b: RequestTicket)
        requires self.wf(), self.recorded(a), self.recorded(b), a.request == b.request,
        ensures a == b,
    {
        let i = choose|i:int| 0 <= i < self.entries.len() && self.entries[i] == a;
        let j = choose|j:int| 0 <= j < self.entries.len() && self.entries[j] == b;
        if i < j { assert(a.request != b.request); }
        if j < i { assert(a.request != b.request); }
    }

    pub fn validate(&self, ticket: RequestTicket) -> (out: Result<(), RequestError>)
        requires self.wf(),
        ensures out.is_ok() == self.recorded(ticket),
    {
        if ticket.domain != self.domain { return Err(RequestError::WrongDomain); }
        match self.pending(ticket.request) {
            None => Err(RequestError::Stale),
            Some(pending) => {
                if pending != ticket {
                    proof { if self.recorded(ticket) { self.recorded_request_unique(pending, ticket); } }
                    Err(RequestError::Mismatch)
                } else { Ok(()) }
            },
        }
    }

    /// Exact admission records; multiple requests for one job may coexist.
    /// The host captures episode and job metadata when constructing its context.
    pub fn issue(&mut self, id: usize, generation: u64, session: u64, job: u64, restoring: bool)
        -> (out: Result<RequestTicket, RequestError>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).domain_id() == old(self).domain_id(),
            out.is_ok() == (old(self).next_id() < u64::MAX && old(self).records().len() < usize::MAX),
            out.is_err() ==> final(self).unchanged(old(self)),
            out.is_ok() ==> out.unwrap() == (RequestTicket {domain: old(self).domain_id(), id, generation,
                session, job, request: old(self).next_id(), restoring})
                && final(self).records() == old(self).records().push(out.unwrap())
                && final(self).next_id() == old(self).next_id() + 1,
            out.is_ok() ==> !old(self).recorded(out.unwrap()) && final(self).recorded(out.unwrap()),
    {
        if self.next == u64::MAX || self.entries.len() == usize::MAX { return Err(RequestError::Capacity); }
        let ticket = RequestTicket {domain: self.domain, id, generation, session, job, request: self.next, restoring};
        proof {
            assert(!self.recorded(ticket)) by {
                if self.recorded(ticket) {
                    let i = choose|i:int| 0 <= i < self.entries.len() && self.entries[i] == ticket;
                    assert(self.entries[i].request < self.next);
                }
            }
        }
        self.next += 1;
        self.entries.push(ticket);
        proof { assert(self.entries[(self.entries.len() - 1) as int] == ticket); }
        Ok(ticket)
    }

    /// The job cannot drain while even one admitted request lacks a receipt.
    pub fn job_drained(&self, session: u64, job: u64) -> (out: bool)
        ensures out == !self.outstanding(session, job),
    {
        let mut i = 0;
        while i < self.entries.len()
            invariant i <= self.entries.len(),
                forall|j:int| 0 <= j < i ==> !(self.entries[j].session == session && self.entries[j].job == job),
            decreases self.entries.len() - i,
        {
            if self.entries[i].session == session && self.entries[i].job == job {
                proof { assert(self.records()[i as int].session == session && self.records()[i as int].job == job); }
                return false;
            }
            i += 1;
        }
        true
    }

    /// Consume one exact receipt; duplicates, altered tuples and foreign-domain
    /// replies leave every record intact. Failure replies also settle requests.
    pub fn complete(&mut self, ticket: RequestTicket) -> (out: Result<(), RequestError>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).domain_id() == old(self).domain_id(),
            final(self).next_id() == old(self).next_id(),
            out.is_ok() == old(self).recorded(ticket),
            out.is_err() ==> final(self).unchanged(old(self)),
            out.is_ok() ==> !final(self).recorded(ticket)
                && final(self).records().len() + 1 == old(self).records().len(),
            out.is_ok() ==> (forall|other: RequestTicket| final(self).recorded(other)
                == (other != ticket && old(self).recorded(other))),
    {
        self.validate(ticket)?;
        let mut i = 0;
        while i < self.entries.len()
            invariant i <= self.entries.len(), self.wf(), self == old(self), self.recorded(ticket),
                forall|j:int| 0 <= j < i ==> self.entries[j].request != ticket.request,
            decreases self.entries.len() - i,
        {
            let pending = self.entries[i];
            if pending.request == ticket.request {
                proof { self.recorded_request_unique(pending, ticket); }
                let ghost before = self.entries@;
                self.entries.remove(i);
                proof {
                    assert forall|a:int| 0 <= a < self.entries.len() implies self.entries[a].domain == self.domain
                        && 0 < self.entries[a].request < self.next by {
                        let b = if a < i { a } else { a + 1 };
                        assert(self.entries[a] == before[b]);
                    }
                    assert forall|a:int,b:int| 0 <= a < b < self.entries.len()
                        implies self.entries[a].request != self.entries[b].request by {
                        let old_a = if a < i { a } else { a + 1 };
                        let old_b = if b < i { b } else { b + 1 };
                        assert(self.entries[a] == before[old_a]);
                        assert(self.entries[b] == before[old_b]);
                        assert(old_a < old_b);
                    }
                    assert forall|other:RequestTicket| self.recorded(other) == (other != ticket && old(self).recorded(other)) by {
                        if before.contains(other) && other != ticket {
                            let a = choose|a:int| 0 <= a < before.len() && before[a] == other;
                            let b = if a < i { a } else { a - 1 };
                            assert(a != i);
                            assert(self.entries[b] == other);
                        }
                        if self.entries@.contains(other) {
                            let a = choose|a:int| 0 <= a < self.entries.len() && self.entries[a] == other;
                            let b = if a < i { a } else { a + 1 };
                            assert(before[b] == other);
                            assert(b != i);
                            if b < i { assert(before[b].request != before[i as int].request); }
                            if b > i { assert(before[i as int].request != before[b].request); }
                        }
                    }
                }
                return Ok(());
            }
            i += 1;
        }
        proof { assert(false); }
        Err(RequestError::Stale)
    }

    /// Compose the actual request record with the actual kernel wait policy.
    /// No caller-supplied `holding` flag can turn a pending request into a no-op.
    pub fn check_wait(&self, kernel: &Kernel, domain: u64, ticket: RequestTicket, target: usize)
        -> (out: Result<WaitDecision, RequestError>)
        requires self.wf(), kernel.wf(),
        ensures out.is_ok() == (domain == self.domain_id() && self.recorded(ticket)),
            out.is_ok() ==> ((out.unwrap() == WaitDecision::StaleEpisode)
                == (kernel.generation_of(ticket.id) != Some(ticket.generation))),
            out.is_ok() ==> ((out.unwrap() == WaitDecision::Allowed)
                == (kernel.generation_of(ticket.id) == Some(ticket.generation) && !kernel.wait_conflict(ticket.id, target))),
            out.is_ok() ==> match out.unwrap() {
                WaitDecision::Blocked {retained} => kernel.generation_of(ticket.id) == Some(ticket.generation)
                    && kernel.committed_reachable(ticket.id, retained) && kernel.owned_by(retained, target),
                _ => true,
            },
    {
        if domain != self.domain { return Err(RequestError::WrongDomain); }
        self.validate(ticket)?;
        Ok(kernel.check_wait(ticket.id, ticket.generation, target, true))
    }
}

} // verus!
