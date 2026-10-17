//! Executable ownership of the payloads named by CleanupJournal's tokens.
//! Opaque payloads move out once per attempt and return to the selected slot
//! only after an accepted failure. No callback is invoked by this container.
use crate::cleanup_journal::{CleanupJournal, RestoreError, RestoreOutcome, RestoreTicket};
#[cfg(verus_keep_ghost)]
use crate::episode::{accumulator_step, AccumulatorRule};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::joint::episode::cleanup_step;
use crate::reversible_value::joint::episode::{CleanupChange, CleanupState};
use crate::reversible_value::joint::{self, Journal, Member};
use crate::Binding;
use vstd::prelude::*;

verus! {
/// The token is runtime data; the witness of its actual registration is erased.
pub(crate) struct Insertion {pub(crate) token:usize,#[allow(dead_code)] pub(crate) trace:Tracked<Option<joint::Receipt>>}
impl Insertion {
    pub(crate) open spec fn recorded(&self,link:Option<(Journal,nat)>,state:CleanupState,cause:Option<joint::Receipt>,settled:Option<nat>)->bool {
        self.trace@.is_some()==link.is_some() && (self.trace@.is_some() ==> {
            let receipt=self.trace@.unwrap();
            &&& receipt.wf() && receipt.journal()==link.unwrap().0
            &&& receipt.event()==(joint::Step {key:link.unwrap().1,change:if cause.is_some() && cause.unwrap().journal()==receipt.journal() && cause.unwrap().forward()
                    {joint::Change::RegisterInverse {write:cause.unwrap().at()}} else {joint::Change::Cleanup {event:CleanupChange::Register}},
                after:joint::Record::Cleanup {state},pending:false,settled})
            &&& state.occupied.len()==self.token+1 && state.occupied[self.token as int]
            &&& state.waiting.last()==self.token
            &&& settled.is_some() ==> joint::pending_at(receipt.events(),receipt.at()).contains_key(settled.unwrap())
                && !receipt.events().last().pending.contains_key(settled.unwrap())
            &&& cause.is_some() && cause.unwrap().journal()==receipt.journal() ==> receipt.follows(&cause.unwrap())
        })
    }
}
pub struct CleanupQueue<T> {
    journal:CleanupJournal,
    payloads:Vec<Option<T>>,
    in_flight:bool,
    joint:Option<Member>,
}
impl<T> CleanupQueue<T> {
    pub closed spec fn protocol(&self)->CleanupJournal {self.journal}
    pub closed spec fn slots(&self)->Seq<Option<T>> {self.payloads@}
    pub closed spec fn trace(&self)->Seq<joint::Frame> {match self.joint {Some(member)=>member.events(),None=>Seq::empty()}}
    pub(crate) proof fn latest_receipt(tracked &self)->(tracked out:Option<joint::Receipt>)
        requires self.wf(),
        ensures out.is_some()==self.link().is_some(),out.is_some() ==> out.unwrap().wf()
            && out.unwrap().journal()==self.link().unwrap().0 && out.unwrap().event().key==self.link().unwrap().1
            && out.unwrap().events()==self.trace() && out.unwrap().event().after==(joint::Record::Cleanup {state:self.observation()}),
    {match &self.joint {Some(member)=>Some(member.receipt()),None=>None}}
    /// Export the real issued ticket, including the journal's identity and
    /// attempt bound, without exposing the queue's representation to clients.
    pub(crate) proof fn issue_receipt(tracked &self,ticket:RestoreTicket)->(tracked out:Option<joint::Receipt>)
        requires self.wf(),self.issued(),self.protocol().selected()==Some(ticket),
            self.link().is_some() ==> self.trace().last().event.change==(joint::Change::Cleanup {event:CleanupChange::Pop {ticket}}),
        ensures crate::reversible_value::restoration::issued(out,self.link(),ticket),
            out.is_some() ==> out.unwrap().events()==self.trace(),
    {self.latest_receipt()}
    pub(crate) proof fn issued_slot(&self,ticket:RestoreTicket)
        requires self.wf(),self.issued(),self.protocol().selected()==Some(ticket),
        ensures ticket.token<self.slots().len(),self.slots()[ticket.token as int].is_none(),
    { }
    pub closed spec fn issued(&self)->bool {self.in_flight}
    pub closed spec fn local_wf(&self)->bool {
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
    pub closed spec fn link(&self)->Option<(Journal,nat)> {
        match self.joint {Some(member)=>Some((member.journal(),member.key())),None=>None}
    }
    pub open spec fn observation(&self)->CleanupState {
        let p=self.protocol();let stage=p.stage();
        CleanupState {domain:p.domain_id(),next:p.next_attempt(),selected:p.selected(),failed:p.failed_spec(),
            committed:stage.committed_view(),waiting:p.waiting(),pending:stage.pending(),settled:stage.settled(),cancelled:stage.cancellation(),
            occupied:self.slots().map(|i:int,slot:Option<T>|slot.is_some()),issued:self.issued()}
    }
    pub closed spec fn traces(&self,state:CleanupState)->bool {
        match self.joint {None=>true,Some(member)=>member.wf() && member.record()==(joint::Record::Cleanup {state})}
    }
    pub closed spec fn wf(&self)->bool {self.local_wf() && self.traces(self.observation())}
    fn commit(&mut self,Ghost(before):Ghost<CleanupState>,Ghost(event):Ghost<CleanupChange>)
        requires old(self).local_wf(),old(self).traces(before),cleanup_step(before,old(self).observation(),event),
        ensures final(self).wf(),final(self).protocol()==old(self).protocol(),final(self).slots()==old(self).slots(),
            final(self).issued()==old(self).issued(),final(self).link()==old(self).link(),
            final(self).link().is_some() ==> old(self).trace().len()<final(self).trace().len()
                && final(self).trace().take(old(self).trace().len() as int)==old(self).trace()
                && final(self).trace().last().event.change==(joint::Change::Cleanup {event}),
    {
        let ghost after=self.observation();
        if let Some(member)=&mut self.joint {
            proof {reveal(joint::changes);}
            member.update(Ghost(joint::Record::Cleanup {state:after}),Ghost(joint::Change::Cleanup {event}));
        }
    }
    fn commit_following(&mut self,Ghost(before):Ghost<CleanupState>,Ghost(event):Ghost<CleanupChange>,Tracked(cause):Tracked<Option<joint::Receipt>>)
        requires cause.is_some() ==> cause.unwrap().wf(),old(self).local_wf(),old(self).traces(before),cleanup_step(before,old(self).observation(),event),
        ensures final(self).wf(),final(self).protocol()==old(self).protocol(),final(self).slots()==old(self).slots(),
            final(self).issued()==old(self).issued(),final(self).link()==old(self).link(),
            final(self).link().is_some() ==> old(self).trace().len()<final(self).trace().len()
                && final(self).trace().take(old(self).trace().len() as int)==old(self).trace()
                && final(self).trace().last().event.change==(joint::Change::Cleanup {event}),
            cause.is_some() && final(self).link().is_some() && cause.unwrap().journal()==final(self).link().unwrap().0 ==>
                cause.unwrap().events().len()<final(self).trace().len() && final(self).trace().take(cause.unwrap().events().len() as int)==cause.unwrap().events(),
    {
        let ghost after=self.observation();
        if let Some(member)=&mut self.joint {
            proof {reveal(joint::changes);}
            let _pending=member.update_following(Ghost(joint::Record::Cleanup {state:after}),Ghost(joint::Change::Cleanup {event}),Tracked(cause),Ghost(false),Tracked(None));
        }
    }
    pub(crate) fn attach_execution(&mut self,journal:&Journal)
        requires old(self).wf(),old(self).link().is_none(),
        ensures final(self).wf(),final(self).protocol()==old(self).protocol(),final(self).slots()==old(self).slots(),
            final(self).issued()==old(self).issued(),final(self).link().is_some(),final(self).link().unwrap().0==*journal,
    {self.joint=Some(journal.allocate(Ghost(joint::Record::Cleanup {state:self.observation()})));}
    pub(crate) fn certify(&self,view:&joint::ReadView)
        requires self.wf(),view.wf(),self.link().is_some(),view.journal_spec()==self.link().unwrap().0,
        ensures view.state().contains_key(self.link().unwrap().1),
            view.state()[self.link().unwrap().1]==(joint::Record::Cleanup {state:self.observation()}),
    {self.joint.as_ref().unwrap().certify(view);}
    pub(crate) fn certify_write(&self,view:&joint::WriteView)
        requires self.wf(),view.wf(),self.link().is_some(),view.journal_spec()==self.link().unwrap().0,
        ensures view.state().contains_key(self.link().unwrap().1),
            view.state()[self.link().unwrap().1]==(joint::Record::Cleanup {state:self.observation()}),
    {self.joint.as_ref().unwrap().certify_write(view);}
    // The explicit Some branch supplies this actual member's invariant.
    #[allow(clippy::manual_map)]
    pub fn observe_execution(&self)->(out:Option<joint::Snapshot>)
        requires self.wf(),
        ensures out.is_some()==self.link().is_some(),out.is_some() ==> out.unwrap().certified()
            && out.unwrap().journal_spec()==self.link().unwrap().0
            && out.unwrap().last().contains_key(self.link().unwrap().1)
            && out.unwrap().last()[self.link().unwrap().1]==(joint::Record::Cleanup {state:self.observation()}),
    {match &self.joint {Some(member)=>Some(member.observe()),None=>None}}
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
    pub(crate) proof fn completion_condition(&self,ticket:RestoreTicket,outcome:RestoreOutcome,retained:Option<T>)
        ensures self.completion_enabled(ticket,outcome,retained)==(self.issued() && self.protocol().selected()==Some(ticket)
            && !self.protocol().failed_spec() && (outcome==RestoreOutcome::Failed || retained.is_none())),
    { }
    pub fn scope(domain:u64)->(out:Self)
        ensures out.link().is_none(),out.wf(),out.slots()==Seq::<Option<T>>::empty(),!out.issued(),
            out.protocol().domain_id()==domain,out.protocol().selected().is_none(),out.protocol().waiting().len()==0,
            !out.protocol().stage().pending(),
    {Self {journal:CleanupJournal::scope(domain),payloads:Vec::new(),in_flight:false,joint:None}}
    pub fn iterator(domain:u64,committed:Vec<Binding>)->(out:Self)
        ensures out.link().is_none(),out.wf(),out.slots()==Seq::<Option<T>>::empty(),!out.issued(),
            out.protocol().domain_id()==domain,out.protocol().selected().is_none(),out.protocol().waiting().len()==0,
            !out.protocol().stage().pending(),
            out.protocol().stage().committed_view()==committed@,
    {Self {journal:CleanupJournal::iterator(domain,committed),payloads:Vec::new(),in_flight:false,joint:None}}

    /// Allocate the token and store its real payload in one exclusive operation.
    pub fn register(&mut self,payload:T)->(token:usize)
        requires old(self).wf(),
        ensures final(self).link()==old(self).link(),final(self).wf(),final(self).protocol().domain_id()==old(self).protocol().domain_id(),token==old(self).slots().len(),
            final(self).slots()==old(self).slots().push(Some(payload)),
            final(self).protocol().waiting()==old(self).protocol().waiting().push(token),
            final(self).protocol().selected()==old(self).protocol().selected(),
            final(self).protocol().failed_spec()==old(self).protocol().failed_spec(),
            final(self).issued()==old(self).issued(),
    {self.register_following(payload,Tracked(None),Tracked(None)).token}
    /// Allocate the token and store its real payload in one exclusive operation.
    pub(crate) fn register_following(&mut self,payload:T,Tracked(cause):Tracked<Option<joint::Receipt>>,Tracked(pending):Tracked<Option<joint::Pending>>)->(out:Insertion)
        requires old(self).wf(),cause.is_some() ==> cause.unwrap().wf(),
            joint::registration_pending(pending,cause,old(self).link()),
        ensures final(self).protocol().stage().cancellation()==old(self).protocol().stage().cancellation(),
            final(self).link()==old(self).link(),final(self).wf(),final(self).protocol().domain_id()==old(self).protocol().domain_id(),out.token==old(self).slots().len(),
            final(self).slots()==old(self).slots().push(Some(payload)),
            final(self).protocol().waiting()==old(self).protocol().waiting().push(out.token),
            final(self).protocol().selected()==old(self).protocol().selected(),
            final(self).protocol().failed_spec()==old(self).protocol().failed_spec(),
            final(self).issued()==old(self).issued(),
            out.recorded(final(self).link(),final(self).observation(),cause,joint::pending_index(pending)),
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
        proof {assert(self.observation().occupied =~= prior.observation().occupied.push(true));}
        let ghost after=self.observation();
        let tracked trace;
        match &mut self.joint {
            None=>{proof {trace=None;}},
            Some(member)=>{
                proof {reveal(joint::changes);}
                let ghost change=if cause.is_some() && cause.unwrap().journal()==member.journal() && cause.unwrap().forward()
                    {joint::Change::RegisterInverse {write:cause.unwrap().at()}} else {joint::Change::Cleanup {event:CleanupChange::Register}};
                let _pending=member.update_following(Ghost(joint::Record::Cleanup {state:after}),Ghost(change),Tracked(cause),Ghost(false),Tracked(pending));
                proof {
                    trace=Some(member.receipt());
                    let r=trace.unwrap();
                    r.transition();
                }
            },
        }
        Insertion {token,trace:Tracked(trace)}
    }
    /// Rejected landings return the exact input payload without changing state.
    pub fn land(&mut self,payload:T)->(out:Result<usize,T>)
        requires old(self).wf(),
        ensures final(self).link()==old(self).link(),final(self).wf(),final(self).protocol().domain_id()==old(self).protocol().domain_id(),out.is_ok()==old(self).protocol().stage().pending(),
            out.is_err() ==> out.unwrap_err()==payload && final(self).same(old(self)),
            out.is_ok() ==> out->Ok_0==old(self).slots().len()
                && final(self).slots()==old(self).slots().push(Some(payload))
                && final(self).protocol().waiting()==old(self).protocol().waiting().push(out->Ok_0)
                && !final(self).protocol().stage().pending()
                && final(self).protocol().stage().settled()==old(self).protocol().stage().cancellation()
                && accumulator_step(old(self).protocol().stage().abstract_view(),final(self).protocol().stage().abstract_view(),
                    if old(self).protocol().stage().cancellation() {AccumulatorRule::Divert(Some(out->Ok_0))} else {AccumulatorRule::Iter(out->Ok_0)}),
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
        proof {assert(self.observation().occupied =~= prior.observation().occupied.push(true));}
        self.commit(Ghost(prior.observation()),Ghost(CleanupChange::Land));
        Ok(token)
    }

    /// A payload already handed to an executor cannot be handed out again.
    /// New work follows LIFO; an admitted retry uses its same retained slot.
    pub fn pop(&mut self)->(out:Result<Option<(RestoreTicket,T)>,RestoreError>)
        requires old(self).wf(),
        ensures final(self).link()==old(self).link(),final(self).wf(),final(self).protocol().domain_id()==old(self).protocol().domain_id(),
            out.is_err() || out.unwrap().is_none() ==> final(self).same(old(self)) && final(self).trace()==old(self).trace(),
            out.is_ok() && out.unwrap().is_some() ==> {
                let (ticket,payload)=out.unwrap().unwrap();
                &&& final(self).link().is_some() ==> final(self).trace().last().event.change==(joint::Change::Cleanup {event:CleanupChange::Pop {ticket}})
                    && old(self).trace().len()<final(self).trace().len() && final(self).trace().take(old(self).trace().len() as int)==old(self).trace()
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
        proof {assert(self.observation().occupied =~= prior.observation().occupied.update(ticket.token as int,false));}
        self.commit(Ghost(prior.observation()),Ghost(CleanupChange::Pop {ticket}));
        Ok(Some((ticket,payload)))
    }

    /// A rejection preserves all queued work and returns the supplied payload.
    /// Only a Failed acknowledgement may place retry work in the selected slot.
    pub fn complete(&mut self,ticket:RestoreTicket,outcome:RestoreOutcome,retained:Option<T>)
        ->(out:Result<(),Option<T>>)
        requires old(self).wf(),
        ensures final(self).link()==old(self).link(),final(self).wf(),final(self).protocol().domain_id()==old(self).protocol().domain_id(),out.is_ok()==old(self).completion_enabled(ticket,outcome,retained),
            out.is_err() ==> out.unwrap_err()==retained && final(self).same(old(self)),
            out.is_ok() ==> !final(self).issued()
                && final(self).slots()==old(self).slots().update(ticket.token as int,retained)
                && final(self).protocol().waiting()==old(self).protocol().waiting()
                && final(self).protocol().failed_spec()==(outcome==RestoreOutcome::Failed)
                && final(self).protocol().selected()==if outcome==RestoreOutcome::Failed {Some(ticket)} else {None},
    {self.complete_following(ticket,outcome,retained,Tracked(None))}
    pub(crate) fn complete_following(&mut self,ticket:RestoreTicket,outcome:RestoreOutcome,retained:Option<T>,Tracked(cause):Tracked<Option<joint::Receipt>>)
        ->(out:Result<(),Option<T>>)
        requires old(self).wf(),cause.is_some() ==> cause.unwrap().wf(),
        ensures final(self).link()==old(self).link(),final(self).wf(),final(self).protocol().domain_id()==old(self).protocol().domain_id(),out.is_ok()==old(self).completion_enabled(ticket,outcome,retained),
            out.is_err() ==> out.unwrap_err()==retained && final(self).same(old(self)),
            out.is_ok() ==> final(self).slots()==old(self).slots().update(ticket.token as int,retained),
            out.is_ok() ==> !final(self).issued()
                && final(self).protocol().waiting()==old(self).protocol().waiting()
                && final(self).protocol().failed_spec()==(outcome==RestoreOutcome::Failed)
                && final(self).protocol().selected()==if outcome==RestoreOutcome::Failed {Some(ticket)} else {None},
            out.is_ok() && final(self).link().is_some() ==>
                final(self).trace().last().event.change==(joint::Change::Cleanup {event:CleanupChange::Complete {ticket,outcome,retained:retained.is_some()}})
                && old(self).trace().len()<final(self).trace().len() && final(self).trace().take(old(self).trace().len() as int)==old(self).trace(),
            out.is_ok() && cause.is_some() && final(self).link().is_some() && cause.unwrap().journal()==final(self).link().unwrap().0 ==>
                cause.unwrap().events().len()<final(self).trace().len() && final(self).trace().take(cause.unwrap().events().len() as int)==cause.unwrap().events(),
    {
        if !self.in_flight || self.journal.current()!=Some(ticket)
            || (outcome!=RestoreOutcome::Failed && retained.is_some()) {return Err(retained);}
        let ghost before=self.observation();let ghost keep=retained.is_some();
        let _accepted=self.journal.complete(ticket,outcome);
        assert(_accepted);
        self.payloads[ticket.token]=retained;
        self.in_flight=false;
        proof {assert(self.observation().occupied =~= before.occupied.update(ticket.token as int,keep));}
        self.commit_following(Ghost(before),Ghost(CleanupChange::Complete {ticket,outcome,retained:keep}),Tracked(cause));
        Ok(())
    }
    pub fn is_issued(&self)->(out:bool) ensures out==self.issued(), {self.in_flight}
    pub fn can_retry(&self)->(out:bool)
        requires self.wf(),ensures out==self.retry_enabled(),
    {
        if !self.journal.can_retry() {return false;}
        self.payloads[self.journal.receipt().unwrap().token].is_some()
    }
    /// A consumed nonretryable failure cannot be converted into an empty retry.
    pub fn retry(&mut self)->(out:Result<RestoreTicket,RestoreError>)
        requires old(self).wf(),
        ensures final(self).link()==old(self).link(),final(self).wf(),final(self).protocol().domain_id()==old(self).protocol().domain_id(),out.is_ok()==old(self).retry_enabled(),
            final(self).slots()==old(self).slots(),final(self).issued()==old(self).issued(),
            final(self).protocol().waiting()==old(self).protocol().waiting(),
            out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> final(self).protocol().selected()==Some(out.unwrap()) && !final(self).protocol().failed_spec()
                && out.unwrap().token==old(self).protocol().selected().unwrap().token
                && out.unwrap().attempt>old(self).protocol().selected().unwrap().attempt,
    {
        if !self.can_retry() {return Err(RestoreError::InvalidState);}
        assert(!self.in_flight);
        let ghost before=self.observation();
        let out=self.journal.retry();
        proof {
            assert(out.is_ok());
            assert(self.journal.selected().is_some());
            assert(self.journal.selected().unwrap().token<self.slots().len());
            assert(!self.journal.waiting().contains(self.journal.selected().unwrap().token));
            assert(self.slots()[self.journal.selected().unwrap().token as int].is_some());
        }
        self.commit(Ghost(before),Ghost(CleanupChange::Retry {ticket:out->Ok_0}));
        out
    }
    pub fn admit(&mut self,target:Option<&[Binding]>)->(out:bool)
        requires old(self).wf(),ensures final(self).link()==old(self).link(),final(self).wf(),final(self).protocol().domain_id()==old(self).protocol().domain_id(),final(self).slots()==old(self).slots(),
            final(self).issued()==old(self).issued(),
            out==final(self).protocol().stage().pending(),
            out==(old(self).protocol().stage().pending() || (!old(self).protocol().stage().settled() && !old(self).protocol().stage().cancellation() && target.is_some() && crate::episode::binding_set(target.unwrap()@)==crate::episode::binding_set(old(self).protocol().stage().committed_view()))),
    {
        let ghost before=self.observation();
        let ghost matches=target.is_some() && crate::episode::binding_set(target.unwrap()@)==crate::episode::binding_set(before.committed);
        let out=self.journal.admit(target);
        self.commit(Ghost(before),Ghost(CleanupChange::Admit {matches}));out
    }
    pub fn end(&mut self)->(out:bool)
        requires old(self).wf(),ensures final(self).link()==old(self).link(),final(self).wf(),final(self).protocol().domain_id()==old(self).protocol().domain_id(),final(self).slots()==old(self).slots(),
            final(self).issued()==old(self).issued(),out==old(self).protocol().stage().pending(),
            out ==> !final(self).protocol().stage().pending() && final(self).protocol().stage().settled()
                && accumulator_step(old(self).protocol().stage().abstract_view(),final(self).protocol().stage().abstract_view(),
                    if old(self).protocol().stage().cancellation() {AccumulatorRule::Divert(None)} else {AccumulatorRule::Finish}),
    {let ghost before=self.observation();let out=self.journal.end();self.commit(Ghost(before),Ghost(CleanupChange::End));out}
    pub fn cancel(&mut self)
        requires old(self).wf(),ensures final(self).link()==old(self).link(),final(self).wf(),final(self).protocol().domain_id()==old(self).protocol().domain_id(),final(self).slots()==old(self).slots(),
            final(self).issued()==old(self).issued(),
            final(self).protocol().stage().cancellation(),final(self).protocol().stage().pending()==old(self).protocol().stage().pending(),
    {let ghost before=self.observation();self.journal.cancel();self.commit(Ghost(before),Ghost(CleanupChange::Cancel));}
    pub fn domain(&self)->(out:u64)
        ensures out==self.protocol().domain_id(),
    {self.journal.domain()}
    pub fn is_settled(&self)->(out:bool)
        ensures out==self.protocol().stage().settled(),
    {self.journal.is_settled()}
    pub fn is_cancelled(&self)->(out:bool) ensures out==self.protocol().stage().cancellation(),
    {self.journal.is_cancelled()}
    pub fn is_pending(&self)->(out:bool)
        ensures out==self.protocol().stage().pending(),
    {self.journal.is_pending()}
    pub fn has_failed(&self)->(out:bool)
        ensures out==self.protocol().failed_spec(),
    {self.journal.has_failed()}
    pub fn can_finish(&self,target:&[Binding])->(out:bool)
        requires self.wf(),ensures out ==> self.protocol().selected().is_none() && !self.issued(),
    {self.journal.can_finish(target)}
    pub proof fn empty_payloads(&self)
        requires self.wf(),self.protocol().waiting().len()==0,self.protocol().selected().is_none(),
        ensures !self.issued(),forall|i:int| 0<=i<self.slots().len() ==> #[trigger] self.slots()[i].is_none(),
    { }
    pub(crate) proof fn drained_observation(&self)
        requires self.wf(),self.protocol().waiting().len()==0,self.protocol().selected().is_none(),
            !self.protocol().stage().pending(),self.protocol().stage().settled(),
        ensures joint::groups::ready(self.observation()),
    {
        self.empty_payloads();
        assert forall|i:int| 0<=i<self.observation().occupied.len() implies !#[trigger] self.observation().occupied[i] by {
            assert(self.slots()[i].is_none());
        }
    }
    pub fn is_empty(&self)->(out:bool)
        requires self.wf(),
        ensures out==(self.protocol().waiting().len()==0 && self.protocol().selected().is_none()),
            out ==> !self.issued() && forall|i:int| 0<=i<self.slots().len() ==> #[trigger] self.slots()[i].is_none(),
    {self.journal.is_empty()}
}
}

#[path = "cleanup_completion.rs"]
pub mod completion;

#[path = "stage_landing.rs"]
pub mod landing;
