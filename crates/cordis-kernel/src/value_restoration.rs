//! Actual queue issue, guarded restoration and acknowledgement receipts.
//! Same-domain causality is established under the existing journal lock.
#[cfg(verus_keep_ghost)]
use super::joint::episode::interval;
use super::{joint, Inverse};
#[cfg(verus_keep_ghost)]
use super::{Event, ValueState};
use crate::cleanup_journal::RestoreTicket;
#[cfg(verus_keep_ghost)]
use crate::{cleanup_journal::RestoreOutcome, Port};
use vstd::prelude::*;

verus! {
pub open spec fn attempted(receipt:&joint::Receipt,inverse:Inverse,success:bool)->bool {
    &&& receipt.wf() && receipt.journal()==inverse.target().journal_spec()
    &&& receipt.event().key==inverse.target().object().key && receipt.event().change is Value
    &&& receipt.event().change->Value_event.valid()
    &&& if success {receipt.event().change==(joint::Change::Value {event:Event::Restore {inverse:inverse.state(),before:inverse.state().after,after:inverse.state().before}})}
        else {receipt.event().change==(joint::Change::Value {event:Event::Blocked {inverse:inverse.state(),before:receipt.event().change->Value_event.before()}})}
}
pub open spec fn issued(receipt:Option<joint::Receipt>,queue:Option<(joint::Journal,nat)>,ticket:RestoreTicket)->bool {
    receipt.is_some()==queue.is_some() && (receipt.is_some() ==> {
        let r=receipt.unwrap();
        &&& r.wf() && r.journal()==queue.unwrap().0 && r.event().key==queue.unwrap().1
        &&& r.event().change==(joint::Change::Cleanup {event:joint::episode::CleanupChange::Pop {ticket}})
        &&& r.event().after is Cleanup && interval::outstanding(r.event().after->Cleanup_state,ticket)
    })
}
#[allow(dead_code)]
pub tracked struct Evidence {
    pub(crate) issue:Option<joint::Receipt>,pub(crate) attempt:joint::Receipt,pub(crate) acknowledgement:Option<joint::Receipt>,
    pub(crate) ghost queue:Option<(joint::Journal,nat)>,pub(crate) ghost ticket:RestoreTicket,
    pub(crate) ghost inverse:Inverse,pub(crate) ghost success:bool,
}
impl Evidence {
    pub(crate) proof fn representation(&self)
        ensures self.issue()==self.issue,self.attempt()==self.attempt,self.acknowledgement()==self.acknowledgement,
            self.queue()==self.queue,self.ticket()==self.ticket,self.inverse()==self.inverse,self.succeeded()==self.success,
    {}
    pub closed spec fn issue(&self)->Option<joint::Receipt> {self.issue}
    pub closed spec fn attempt(&self)->joint::Receipt {self.attempt}
    pub closed spec fn acknowledgement(&self)->Option<joint::Receipt> {self.acknowledgement}
    pub closed spec fn queue(&self)->Option<(joint::Journal,nat)> {self.queue}
    pub closed spec fn ticket(&self)->RestoreTicket {self.ticket}
    pub closed spec fn inverse(&self)->Inverse {self.inverse}
    pub closed spec fn succeeded(&self)->bool {self.success}
    pub open spec fn same_domain(&self)->bool {self.queue().is_some() && self.queue().unwrap().0==self.attempt().journal()}
    pub open spec fn protocol(&self)->bool {
        &&& issued(self.issue(),self.queue(),self.ticket())
        &&& attempted(&self.attempt(),self.inverse(),self.succeeded())
        &&& self.acknowledgement().is_some()==self.queue().is_some()
        &&& self.acknowledgement().is_some() ==> {
            let r=self.acknowledgement().unwrap();let outcome=if self.succeeded() {RestoreOutcome::Succeeded} else {RestoreOutcome::Failed};
            &&& r.wf() && r.journal()==self.queue().unwrap().0 && r.event().key==self.queue().unwrap().1
            &&& r.event().change==(joint::Change::Cleanup {event:joint::episode::CleanupChange::Complete {ticket:self.ticket(),outcome,retained:!self.succeeded()}})
            &&& r.event().after is Cleanup && !r.event().after->Cleanup_state.issued
            &&& r.event().after->Cleanup_state.failed==!self.succeeded()
            &&& r.event().after->Cleanup_state.occupied[self.ticket().token as int]==!self.succeeded()
            &&& r.event().after->Cleanup_state.selected==if self.succeeded() {None} else {Some(self.ticket())}
            &&& r.follows(&self.issue().unwrap())
        }
        &&& self.same_domain() ==> self.attempt().follows(&self.issue().unwrap())
            && self.acknowledgement().unwrap().follows(&self.attempt())
    }
    pub open spec fn certified(&self)->bool {
        self.protocol() && (self.queue().is_some() ==> interval::holds(self.acknowledgement().unwrap().events(),
            self.issue().unwrap().at()+1,self.acknowledgement().unwrap().at(),self.queue().unwrap().1,self.ticket()))
    }
    /// Called by the real typed dispatcher before returning its completion.
    /// The interval endpoints are its own authoritative queue receipts.
    pub(crate) proof fn establish_interval(&self)
        requires self.protocol(),ensures self.certified(),
    {
        if self.queue().is_some() {
            let issue=self.issue().unwrap();let ack=self.acknowledgement().unwrap();
            let frames=ack.events();let key=self.queue().unwrap().1;
            let start=issue.at()+1;let end=ack.at();
            assert(frames[issue.at() as int]==issue.events()[issue.at() as int]);
            assert(joint::step(joint::state_at(frames,issue.at()),frames[issue.at() as int].state,issue.event()));
            assert(joint::step(joint::state_at(frames,end),frames[end as int].state,ack.event()));
            reveal(joint::changes);
            interval::between(frames,start,end,key,self.ticket());
        }
    }
    /// Includes the restore/block commit for same-domain objects. The actual
    /// payload is fixed by records/corresponds, including failure retention.
    pub proof fn custody_interval(&self)
        requires self.certified(),self.queue().is_some(),
        ensures interval::holds(self.acknowledgement().unwrap().events(),self.issue().unwrap().at()+1,
            self.acknowledgement().unwrap().at(),self.queue().unwrap().1,self.ticket()),
            self.same_domain() ==> interval::outstanding(interval::at(self.acknowledgement().unwrap().events(),
                self.attempt().at()+1,self.queue().unwrap().1),self.ticket()),
    {
        if self.same_domain() {
            assert(interval::present(self.acknowledgement().unwrap().events(),self.attempt().at()+1,self.queue().unwrap().1));
        }
    }
    pub open spec fn records(&self,inverse:Inverse,ticket:RestoreTicket,queue:Option<(joint::Journal,nat)>)->bool {
        self.certified() && self.inverse()==inverse && self.ticket()==ticket && self.queue()==queue
    }
    /// One authentic trace includes issue, the actual guarded write or block,
    /// acknowledgement and any intervening commits. It is not one atomic step.
    pub proof fn microsteps(&self)->(frames:Seq<joint::Frame>)
        requires self.certified(),self.same_domain(),
        ensures frames==self.acknowledgement().unwrap().events(),joint::valid(frames),
            self.issue().unwrap().at()<self.attempt().at()<self.acknowledgement().unwrap().at(),
            frames[self.issue().unwrap().at() as int].event==self.issue().unwrap().event(),
            frames[self.attempt().at() as int].event==self.attempt().event(),
            frames.last().event==self.acknowledgement().unwrap().event(),
    {
        let frames=self.acknowledgement().unwrap().events();
        assert(frames[self.attempt().at() as int]==self.attempt().events()[self.attempt().at() as int]);
        assert(frames.take(self.issue().unwrap().events().len() as int) =~= self.issue().unwrap().events());
        frames
    }
    proof fn completion_boundary(&self)
        requires self.certified(),self.queue().is_some(),
        ensures interval::present(self.acknowledgement().unwrap().events(),self.acknowledgement().unwrap().events().len(),self.queue().unwrap().1),
            !interval::active(interval::at(self.acknowledgement().unwrap().events(),self.acknowledgement().unwrap().events().len(),self.queue().unwrap().1),self.ticket()),
            self.ticket().attempt<interval::at(self.acknowledgement().unwrap().events(),self.acknowledgement().unwrap().events().len(),self.queue().unwrap().1).next,
    {
        let ack=self.acknowledgement().unwrap();let frames=ack.events();let key=self.queue().unwrap().1;
        assert(interval::present(frames,ack.at(),key));
        interval::after_completion(frames,ack.at(),key,self.ticket());
    }
    /// Any later authentic snapshot keeps this completed attempt inactive,
    /// including after a retry of the same slot. Delayed/duplicate replies
    /// cannot become a second accepted completion of this ticket.
    pub proof fn completed_attempt_stays_closed(&self,later:&joint::Snapshot)
        requires self.certified(),self.queue().is_some(),later.certified(),
            later.journal_spec()==self.queue().unwrap().0,
            self.acknowledgement().unwrap().events().len()<=later.events().len(),
            later.events().take(self.acknowledgement().unwrap().events().len() as int)==self.acknowledgement().unwrap().events(),
        ensures interval::retired(later.events(),self.acknowledgement().unwrap().events().len(),self.queue().unwrap().1,self.ticket()),
    {
        self.completion_boundary();
        later.valid_history();
        interval::closed_extension(self.acknowledgement().unwrap().events(),later.events(),self.queue().unwrap().1,self.ticket());
    }
    /// The actual restoration uses the strict inverse; a blocked attempt
    /// preserves the interpreted scalar service table.
    pub proof fn paper_attempt(&self,key:Port,table:Map<Port,ValueState>)
        requires self.certified(),table.contains_key(key),table[key]==self.attempt().event().change->Value_event.before(),
        ensures super::interpreted_step(self.attempt().event().change->Value_event,key,table,
            table.insert(key,self.attempt().event().change->Value_event.after())),
            !self.succeeded() ==> self.attempt().event().change->Value_event.before()==self.attempt().event().change->Value_event.after(),
    {super::interpret_event(self.attempt().event().change->Value_event,key,table);}
}
}
