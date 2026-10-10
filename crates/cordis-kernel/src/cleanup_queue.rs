//! Executable ownership of the payloads named by CleanupJournal's tokens.
//! Opaque payloads move out once per attempt and return to the selected slot
//! only after an accepted failure. No callback is invoked by this container.
use crate::cleanup_journal::{CleanupJournal, RestoreError, RestoreOutcome, RestoreTicket};
use crate::Binding;
use vstd::prelude::*;

verus! {
pub struct CleanupQueue<T> {
    journal:CleanupJournal,
    payloads:Vec<Option<T>>,
    in_flight:bool,
}
impl<T> CleanupQueue<T> {
    pub closed spec fn protocol(&self)->CleanupJournal {self.journal}
    pub closed spec fn slots(&self)->Seq<Option<T>> {self.payloads@}
    pub closed spec fn issued(&self)->bool {self.in_flight}
    pub closed spec fn wf(&self)->bool {
        &&& self.journal.wf()
        &&& self.journal.waiting().no_duplicates()
        &&& forall|i:int| 0<=i<self.journal.waiting().len() ==>
            #[trigger] self.journal.waiting()[i]<self.slots().len()
            && self.slots()[self.journal.waiting()[i] as int].is_some()
        &&& self.journal.selected().is_some() ==> {
            let token=self.journal.selected().unwrap().token;
            &&& token<self.slots().len()
            &&& !self.journal.waiting().contains(token)
            &&& !self.in_flight && !self.journal.failed_spec() ==> self.slots()[token as int].is_some()
        }
        &&& self.in_flight ==> self.journal.selected().is_some() && !self.journal.failed_spec()
            && self.slots()[self.journal.selected().unwrap().token as int].is_none()
        &&& forall|i:int| 0<=i<self.slots().len() && #[trigger] self.slots()[i].is_some() ==>
            i<=usize::MAX && (self.journal.waiting().contains(i as usize)
            || (self.journal.selected().is_some() && self.journal.selected().unwrap().token==i && !self.in_flight))
    }
    pub closed spec fn same(&self,prior:&Self)->bool {
        self.journal.same(&prior.journal) && self.slots()==prior.slots() && self.in_flight==prior.in_flight
    }
    pub closed spec fn retry_enabled(&self)->bool {
        self.journal.failed_spec() && self.journal.next_attempt()<u64::MAX
            && self.slots()[self.journal.selected().unwrap().token as int].is_some()
    }
    pub closed spec fn completion_enabled(&self,ticket:RestoreTicket,outcome:RestoreOutcome,retained:Option<T>)->bool {
        self.in_flight && self.journal.selected()==Some(ticket) && !self.journal.failed_spec()
            && (outcome==RestoreOutcome::Failed || retained.is_none())
    }
    pub fn scope(domain:u64)->(out:Self)
        ensures out.wf(),out.slots()==Seq::<Option<T>>::empty(),!out.issued(),
            out.protocol().domain_id()==domain,out.protocol().selected().is_none(),out.protocol().waiting().len()==0,
    {Self {journal:CleanupJournal::scope(domain),payloads:Vec::new(),in_flight:false}}
    pub fn iterator(domain:u64,committed:Vec<Binding>)->(out:Self)
        ensures out.wf(),out.slots()==Seq::<Option<T>>::empty(),!out.issued(),
            out.protocol().domain_id()==domain,out.protocol().selected().is_none(),out.protocol().waiting().len()==0,
            out.protocol().stage().committed_view()==committed@,
    {Self {journal:CleanupJournal::iterator(domain,committed),payloads:Vec::new(),in_flight:false}}

    /// Allocate the token and store its real payload in one exclusive operation.
    pub fn register(&mut self,payload:T)->(token:usize)
        requires old(self).wf(),
        ensures final(self).wf(),token==old(self).slots().len(),
            final(self).slots()==old(self).slots().push(Some(payload)),
            final(self).protocol().waiting()==old(self).protocol().waiting().push(token),
            final(self).protocol().selected()==old(self).protocol().selected(),
            final(self).protocol().failed_spec()==old(self).protocol().failed_spec(),
            final(self).issued()==old(self).issued(),
    {
        let ghost prior=*self;
        let token=self.payloads.len();
        self.payloads.push(Some(payload));
        self.journal.register(token);
        proof {
            assert forall|i:int| 0<=i<self.slots().len() && #[trigger] self.slots()[i].is_some() implies
                i<=usize::MAX && (self.journal.waiting().contains(i as usize)
                || (self.journal.selected().is_some() && self.journal.selected().unwrap().token==i && !self.in_flight)) by {
                if i<prior.slots().len() {
                    assert(prior.slots()[i].is_some());
                    if prior.journal.waiting().contains(i as usize) {
                        let j=choose|j:int| 0<=j<prior.journal.waiting().len() && prior.journal.waiting()[j]==i as usize;
                        assert(self.journal.waiting()[j]==i as usize);
                    }
                } else {
                    assert(i==token);
                    assert(self.journal.waiting()[prior.journal.waiting().len() as int]==i as usize);
                }
            }
        }
        token
    }
    /// Rejected landings return the exact input payload without changing state.
    pub fn land(&mut self,payload:T)->(out:Result<usize,T>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_ok()==old(self).protocol().stage().pending(),
            out.is_err() ==> out.unwrap_err()==payload && final(self).same(old(self)),
            out.is_ok() ==> out->Ok_0==old(self).slots().len()
                && final(self).slots()==old(self).slots().push(Some(payload))
                && final(self).protocol().waiting()==old(self).protocol().waiting().push(out->Ok_0),
            final(self).protocol().selected()==old(self).protocol().selected(),final(self).issued()==old(self).issued(),
    {
        if !self.journal.is_pending() {return Err(payload);}
        let ghost prior=*self;
        let token=self.payloads.len();
        self.payloads.push(Some(payload));
        let _accepted=self.journal.land(token);
        assert(_accepted);
        proof {
            assert forall|i:int| 0<=i<self.slots().len() && #[trigger] self.slots()[i].is_some() implies
                i<=usize::MAX && (self.journal.waiting().contains(i as usize)
                || (self.journal.selected().is_some() && self.journal.selected().unwrap().token==i && !self.in_flight)) by {
                if i<prior.slots().len() {
                    assert(prior.slots()[i].is_some());
                    if prior.journal.waiting().contains(i as usize) {
                        let j=choose|j:int| 0<=j<prior.journal.waiting().len() && prior.journal.waiting()[j]==i as usize;
                        assert(self.journal.waiting()[j]==i as usize);
                    }
                } else {
                    assert(i==token);
                    assert(self.journal.waiting()[prior.journal.waiting().len() as int]==i as usize);
                }
            }
        }
        Ok(token)
    }

    /// A payload already handed to an executor cannot be handed out again.
    /// New work follows LIFO; an admitted retry uses its same retained slot.
    pub fn pop(&mut self)->(out:Result<Option<(RestoreTicket,T)>,RestoreError>)
        requires old(self).wf(),
        ensures final(self).wf(),
            out.is_err() || out.unwrap().is_none() ==> final(self).same(old(self)),
            out.is_ok() && out.unwrap().is_some() ==> {
                let (ticket,payload)=out.unwrap().unwrap();
                &&& !old(self).issued() && !old(self).protocol().failed_spec()
                &&& ticket.token<old(self).slots().len()
                &&& old(self).slots()[ticket.token as int]==Some(payload)
                &&& final(self).slots()==old(self).slots().update(ticket.token as int,None)
                &&& final(self).issued() && final(self).protocol().selected()==Some(ticket)
                &&& if old(self).protocol().selected().is_some() {
                    ticket==old(self).protocol().selected().unwrap()
                        && final(self).protocol().waiting()==old(self).protocol().waiting()
                } else {
                    old(self).protocol().waiting().len()>0 && ticket.token==old(self).protocol().waiting().last()
                        && final(self).protocol().waiting()==old(self).protocol().waiting().drop_last()
                }
            },
    {
        let ghost prior=*self;
        if self.in_flight || self.journal.has_failed() {return Ok(None);}
        let ticket=match self.journal.current() {
            Some(ticket)=>ticket,
            None=>match self.journal.begin_restore() {
                Err(error)=>return Err(error),Ok(None)=>return Ok(None),Ok(Some(ticket))=>ticket,
            },
        };
        proof {
            assert(ticket.token<self.slots().len());
            assert(self.slots()[ticket.token as int].is_some());
            assert(!self.journal.waiting().contains(ticket.token));
        }
        let payload=self.payloads[ticket.token].take().unwrap();
        self.in_flight=true;
        proof {
            assert forall|i:int| 0<=i<self.slots().len() && #[trigger] self.slots()[i].is_some() implies
                i<=usize::MAX && (self.journal.waiting().contains(i as usize)
                || (self.journal.selected().is_some() && self.journal.selected().unwrap().token==i && !self.in_flight)) by {
                assert(i!=ticket.token);
                assert(prior.slots()[i].is_some());
                assert(prior.journal.waiting().contains(i as usize));
                let j=choose|j:int| 0<=j<prior.journal.waiting().len() && prior.journal.waiting()[j]==i as usize;
                if prior.journal.selected().is_none() {
                    assert(j<prior.journal.waiting().len()-1);
                }
                assert(self.journal.waiting()[j]==i as usize);
            }
        }
        Ok(Some((ticket,payload)))
    }

    /// A rejection preserves all queued work and returns the supplied payload.
    /// Only a Failed acknowledgement may place retry work in the selected slot.
    pub fn complete(&mut self,ticket:RestoreTicket,outcome:RestoreOutcome,retained:Option<T>)
        ->(out:Result<(),Option<T>>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_ok()==old(self).completion_enabled(ticket,outcome,retained),
            out.is_err() ==> out.unwrap_err()==retained && final(self).same(old(self)),
            out.is_ok() ==> !final(self).issued()
                && final(self).slots()==old(self).slots().update(ticket.token as int,retained)
                && final(self).protocol().waiting()==old(self).protocol().waiting()
                && final(self).protocol().failed_spec()==(outcome==RestoreOutcome::Failed)
                && final(self).protocol().selected()==if outcome==RestoreOutcome::Failed {Some(ticket)} else {None},
    {
        if !self.in_flight || self.journal.current()!=Some(ticket)
            || (outcome!=RestoreOutcome::Failed && retained.is_some()) {return Err(retained);}
        let _accepted=self.journal.complete(ticket,outcome);
        assert(_accepted);
        self.payloads[ticket.token]=retained;
        self.in_flight=false;
        Ok(())
    }
    pub fn can_retry(&self)->(out:bool)
        requires self.wf(),ensures out==self.retry_enabled(),
    {
        if !self.journal.can_retry() {return false;}
        self.payloads[self.journal.receipt().unwrap().token].is_some()
    }
    /// A consumed nonretryable failure cannot be converted into an empty retry.
    pub fn retry(&mut self)->(out:Result<RestoreTicket,RestoreError>)
        requires old(self).wf(),
        ensures final(self).wf(),out.is_ok()==old(self).retry_enabled(),
            final(self).slots()==old(self).slots(),final(self).issued()==old(self).issued(),
            final(self).protocol().waiting()==old(self).protocol().waiting(),
            out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> final(self).protocol().selected()==Some(out.unwrap()) && !final(self).protocol().failed_spec()
                && out.unwrap().token==old(self).protocol().selected().unwrap().token
                && out.unwrap().attempt>old(self).protocol().selected().unwrap().attempt,
    {
        if !self.can_retry() {return Err(RestoreError::InvalidState);}
        assert(!self.in_flight);
        let out=self.journal.retry();
        proof {
            assert(out.is_ok());
            assert(self.journal.selected().is_some());
            assert(self.journal.selected().unwrap().token<self.slots().len());
            assert(!self.journal.waiting().contains(self.journal.selected().unwrap().token));
            assert(self.slots()[self.journal.selected().unwrap().token as int].is_some());
        }
        out
    }
    pub fn admit(&mut self,target:Option<&[Binding]>)->(out:bool)
        requires old(self).wf(),ensures final(self).wf(),final(self).slots()==old(self).slots(),
            final(self).issued()==old(self).issued(),
    {self.journal.admit(target)}
    pub fn end(&mut self)->(out:bool)
        requires old(self).wf(),ensures final(self).wf(),final(self).slots()==old(self).slots(),
            final(self).issued()==old(self).issued(),
    {self.journal.end()}
    pub fn cancel(&mut self)
        requires old(self).wf(),ensures final(self).wf(),final(self).slots()==old(self).slots(),
            final(self).issued()==old(self).issued(),
    {self.journal.cancel();}
    pub fn is_pending(&self)->(out:bool)
        ensures out==self.protocol().stage().pending(),
    {self.journal.is_pending()}
    pub fn has_failed(&self)->(out:bool)
        ensures out==self.protocol().failed_spec(),
    {self.journal.has_failed()}
    pub fn can_finish(&self,target:&[Binding])->(out:bool)
        requires self.wf(),ensures out ==> self.protocol().selected().is_none() && !self.issued(),
    {self.journal.can_finish(target)}
    pub fn is_empty(&self)->(out:bool)
        requires self.wf(),
        ensures out==(self.protocol().waiting().len()==0 && self.protocol().selected().is_none()),
            out ==> !self.issued() && forall|i:int| 0<=i<self.slots().len() ==> #[trigger] self.slots()[i].is_none(),
    {self.journal.is_empty()}
}
}
