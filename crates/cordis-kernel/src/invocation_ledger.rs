//! Live JS callback ownership, using the same verified receipt store as requests.
//!
//! Only live records occupy storage. Completed handles remain valid inactive
//! origins, while their never-reused identities cannot finish a newer callback.
//! This ledger checks supplied scopes; the production Node path owner captures
//! them once, preserving its selected parent. ALS selection remains in the host.
use crate::{
    request_ledger::{RequestLedger, RequestTicket},
    wait_guard::WaitDecision,
    Kernel,
};
use vstd::prelude::*;

verus! {

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub struct ScopeHandle { pub domain: u64, pub scope: u64 }

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum ScopeError { Capacity, WrongDomain, Unknown, Completed, StaleEpisode }

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub struct ScopeBlock {
    pub scope: ScopeHandle,
    pub id: usize,
    pub generation: u64,
    pub retained: usize,
}

pub struct InvocationLedger { requests: RequestLedger }

impl InvocationLedger {
    pub closed spec fn wf(&self) -> bool { self.requests.wf() }
    pub closed spec fn domain_id(&self) -> u64 { self.requests.domain_id() }
    pub closed spec fn next_id(&self) -> u64 { self.requests.next_id() }
    pub closed spec fn records(&self) -> Seq<RequestTicket> { self.requests.records() }
    pub closed spec fn unchanged(&self, prior: &Self) -> bool { self.requests.unchanged(&prior.requests) }
    pub proof fn allocation_facts(&self)
        requires self.wf(),ensures self.next_id()>0,
    {self.requests.record_facts();}
    pub proof fn unchanged_reflexive(&self) ensures self.unchanged(self), {reveal(RequestLedger::unchanged);}
    pub proof fn unchanged_observations(&self,prior:&Self)
        requires self.unchanged(prior),
        ensures self.domain_id()==prior.domain_id(),self.next_id()==prior.next_id(),self.records()==prior.records(),
    {reveal(RequestLedger::unchanged);}
    pub open spec fn known(&self, handle: ScopeHandle) -> bool {
        handle.domain == self.domain_id() && 0 < handle.scope < self.next_id()
    }
    pub open spec fn owns(&self, handle: ScopeHandle, record: RequestTicket) -> bool {
        self.known(handle) && record.domain == handle.domain && record.request == handle.scope
            && self.records().contains(record)
    }
    pub open spec fn live(&self, handle: ScopeHandle) -> bool {
        exists|record:RequestTicket| self.owns(handle, record)
    }
    pub open spec fn safe(&self, kernel: &Kernel, handle: ScopeHandle, target: usize) -> bool {
        self.known(handle) && forall|record:RequestTicket| self.owns(handle, record)
            ==> kernel.generation_of(record.id) == Some(record.generation) && !kernel.wait_conflict(record.id, target)
    }
    pub open spec fn blocked(&self, kernel: &Kernel, block: ScopeBlock, target: usize) -> bool {
        exists|record:RequestTicket| self.owns(block.scope, record) && record.id == block.id
            && record.generation == block.generation
            && kernel.generation_of(record.id) == Some(record.generation)
            && kernel.committed_reachable(record.id, block.retained) && kernel.owned_by(block.retained, target)
    }

    pub fn new(domain: u64) -> (out: Self)
        ensures out.wf(), out.domain_id() == domain, out.records().len() == 0, out.next_id() == 1,
    { Self { requests: RequestLedger::new(domain) } }

    pub fn live_count(&self) -> (out: usize)
        ensures out == self.records().len(),
    { self.requests.pending_count() }

    pub fn begin(&mut self, kernel: &Kernel, id: usize, generation: u64) -> (out: Result<ScopeHandle, ScopeError>)
        requires old(self).wf(), kernel.wf(),
        ensures final(self).wf(), final(self).domain_id() == old(self).domain_id(),
            out.is_err() ==> final(self).unchanged(old(self)),
            out.is_ok() == (kernel.generation_of(id) == Some(generation)
                && old(self).next_id() < u64::MAX && old(self).records().len() < usize::MAX),
            out.is_ok() ==> out.unwrap() == (ScopeHandle {domain: old(self).domain_id(), scope: old(self).next_id()})
                && !old(self).known(out.unwrap()) && final(self).live(out.unwrap())
                && final(self).next_id() == old(self).next_id() + 1
                && final(self).records() == old(self).records().push(RequestTicket {
                    domain: old(self).domain_id(), id, generation, session: 0, job: 0,
                    request: old(self).next_id(), restoring: false}),
    {
        proof { self.requests.record_facts(); }
        if kernel.episode_generation(id) != Some(generation) { return Err(ScopeError::StaleEpisode); }
        match self.requests.issue(id, generation, 0, 0, false) {
            Ok(ticket) => {
                let handle = ScopeHandle {domain: ticket.domain, scope: ticket.request};
                proof { self.requests.record_facts(); assert(self.owns(handle, ticket)); }
                Ok(handle)
            },
            Err(_) => Err(ScopeError::Capacity),
        }
    }

    fn lookup(&self, handle: ScopeHandle) -> (out: Result<Option<RequestTicket>, ScopeError>)
        requires self.wf(),
        ensures out.is_ok() == self.known(handle),
            out.is_ok() ==> out.unwrap().is_some() == self.live(handle),
            out.is_ok() && out.unwrap().is_some() ==> self.owns(handle, out.unwrap().unwrap())
                && (forall|record:RequestTicket| self.owns(handle, record) ==> record == out.unwrap().unwrap()),
    {
        proof { self.requests.record_facts(); }
        if handle.domain != self.requests.domain() { return Err(ScopeError::WrongDomain); }
        if !self.requests.issued(handle.scope) { return Err(ScopeError::Unknown); }
        let pending = self.requests.pending(handle.scope);
        proof {
            if let Some(ticket) = pending {
                assert(self.owns(handle, ticket));
                assert forall|record:RequestTicket| self.owns(handle, record) implies record == ticket by {
                    self.requests.recorded_request_unique(record, ticket);
                }
            } else if self.live(handle) {
                let record = choose|record:RequestTicket| self.owns(handle, record);
                let i = choose|i:int| 0 <= i < self.records().len() && self.records()[i] == record;
                assert(self.requests.records()[i].request == handle.scope);
            }
        }
        Ok(pending)
    }

    /// A callback result consumes only its own scope. Abort is not completion.
    pub fn finish(&mut self, handle: ScopeHandle) -> (out: Result<(), ScopeError>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).domain_id() == old(self).domain_id(),
            final(self).next_id() == old(self).next_id(),
            out.is_ok() == old(self).live(handle),
            out.is_err() ==> final(self).unchanged(old(self)),
            out.is_ok() ==> !final(self).live(handle)
                && final(self).records().len() + 1 == old(self).records().len(),
            out.is_ok() ==> (forall|record:RequestTicket| final(self).records().contains(record)
                == (old(self).records().contains(record) && record.request != handle.scope)),
    {
        let pending = self.lookup(handle)?;
        let ticket = match pending { Some(ticket) => ticket, None => return Err(ScopeError::Completed) };
        proof {
            assert forall|other:RequestTicket| self.records().contains(other) && other.request == handle.scope
                implies other == ticket by { self.requests.recorded_request_unique(other, ticket); }
        }
        match self.requests.complete(ticket) {
            Ok(()) => {
                proof {
                    assert forall|record:RequestTicket| self.records().contains(record)
                        == (old(self).records().contains(record) && record.request != handle.scope) by {
                        assert(self.requests.recorded(record) == (record != ticket && old(self).requests.recorded(record)));
                        if old(self).records().contains(record) && record.request == handle.scope {
                            old(self).requests.recorded_request_unique(record, ticket);
                        }
                    }
                }
                Ok(())
            },
            Err(_) => { proof { assert(false); } Err(ScopeError::Completed) },
        }
    }

    /// All identities are checked, including those after the first live scope.
    pub fn any_live(&self, handles: &[ScopeHandle]) -> (out: Result<bool, ScopeError>)
        requires self.wf(),
        ensures out.is_ok() == (forall|i:int| 0 <= i < handles.len() ==> self.known(handles[i])),
            out.is_ok() ==> out.unwrap() == (exists|i:int| 0 <= i < handles.len() && self.live(handles[i])),
    {
        let mut found = false;
        let mut i = 0;
        while i < handles.len()
            invariant self.wf(), i <= handles.len(),
                forall|j:int| 0 <= j < i ==> self.known(handles[j]),
                found == (exists|j:int| 0 <= j < i && self.live(handles[j])),
            decreases handles.len() - i,
        {
            let pending = self.lookup(handles[i])?;
            if pending.is_some() { found = true; }
            i += 1;
        }
        Ok(found)
    }

    fn check_one(&self, kernel: &Kernel, handle: ScopeHandle, target: usize)
        -> (out: Result<Option<ScopeBlock>, ScopeError>)
        requires self.wf(), kernel.wf(),
        ensures (out == Ok(None)) == self.safe(kernel, handle, target),
            out.is_ok() && out.unwrap().is_some() ==> out.unwrap().unwrap().scope == handle
                && self.blocked(kernel, out.unwrap().unwrap(), target),
    {
        let pending = self.lookup(handle)?;
        let ticket = match pending { Some(ticket) => ticket, None => return Ok(None) };
        match kernel.check_wait(ticket.id, ticket.generation, target, true) {
            WaitDecision::Allowed => Ok(None),
            WaitDecision::StaleEpisode => Err(ScopeError::StaleEpisode),
            WaitDecision::Blocked {retained} => {
                let block = ScopeBlock {scope: handle, id: ticket.id, generation: ticket.generation, retained};
                proof { self.requests.record_facts(); assert(self.owns(handle, ticket)); }
                Ok(Some(block))
            },
        }
    }

    /// A completed nested scope cannot conceal a supplied live ancestor. The
    /// host supplies the ancestry, but neither owner metadata nor a holding bit.
    pub fn check_wait(&self, kernel: &Kernel, handles: &[ScopeHandle], target: usize)
        -> (out: Result<Option<ScopeBlock>, ScopeError>)
        requires self.wf(), kernel.wf(),
        ensures (out == Ok(None)) == (forall|i:int| 0 <= i < handles.len() ==> self.safe(kernel, handles[i], target)),
            out.is_ok() && out.unwrap().is_some() ==> handles@.contains(out.unwrap().unwrap().scope)
                && self.blocked(kernel, out.unwrap().unwrap(), target),
    {
        let mut i = 0;
        while i < handles.len()
            invariant self.wf(), kernel.wf(), i <= handles.len(),
                forall|j:int| 0 <= j < i ==> self.safe(kernel, handles[j], target),
            decreases handles.len() - i,
        {
            let block = self.check_one(kernel, handles[i], target)?;
            if block.is_some() {
                proof { assert(handles@.contains(handles[i as int])); }
                return Ok(block);
            }
            i += 1;
        }
        Ok(None)
    }
}

} // verus!
