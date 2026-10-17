//! One actual typed cleanup request, observed attempt and acknowledgement.
//! Reads have a state cut, not an invented write event. Cross-domain histories
//! remain separate while the actual queue retains the same inverse payload.
use super::Attempt;
#[cfg(verus_keep_ghost)]
use super::Inverse;
use crate::cleanup_journal::RestoreTicket;
use crate::reversible_value::joint;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::restoration::issued;
#[cfg(verus_keep_ghost)]
use crate::{cleanup_journal::RestoreOutcome, reversible_value::joint::episode::interval};
use vstd::prelude::*;

verus! {
#[allow(dead_code)]
pub tracked struct Evidence<T:?Sized> {
    pub(crate) issue:Option<joint::Receipt>,pub(crate) attempt:Attempt<T>,
    pub(crate) acknowledgement:Option<joint::Receipt>,pub(crate) ghost queue:Option<(joint::Journal,nat)>,
    pub(crate) ghost ticket:RestoreTicket,
}
impl<T:?Sized> Evidence<T> {
    pub(crate) proof fn representation(&self)
        ensures self.issue()==self.issue,self.attempt()==self.attempt,self.acknowledgement()==self.acknowledgement,
            self.queue()==self.queue,self.ticket()==self.ticket,
    { }
    pub closed spec fn issue(&self)->Option<joint::Receipt> {self.issue}
    pub closed spec fn attempt(&self)->Attempt<T> {self.attempt}
    pub closed spec fn acknowledgement(&self)->Option<joint::Receipt> {self.acknowledgement}
    pub closed spec fn queue(&self)->Option<(joint::Journal,nat)> {self.queue}
    pub closed spec fn ticket(&self)->RestoreTicket {self.ticket}
    pub open spec fn inverse(&self)->Inverse<T> {self.attempt().inverse()}
    pub open spec fn succeeded(&self)->bool {self.attempt().result().is_ok()}
    pub open spec fn same_domain(&self)->bool {self.queue().is_some() && self.queue().unwrap().0==self.attempt().read().checkpoint().journal()}
    pub open spec fn protocol(&self)->bool {
        &&& issued(self.issue(),self.queue(),self.ticket())
        &&& self.attempt().wf() && self.attempt().follows_cause(self.issue())
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
        &&& self.same_domain() ==> self.acknowledgement().unwrap().follows(&self.attempt().endpoint())
    }
    #[verifier::opaque]
    pub open spec fn certified(&self)->bool {
        self.protocol() && (self.queue().is_some() ==> interval::holds(self.acknowledgement().unwrap().events(),
            self.issue().unwrap().at()+1,self.acknowledgement().unwrap().at(),self.queue().unwrap().1,self.ticket()))
    }
    pub open spec fn records(&self,inverse:Inverse<T>,ticket:RestoreTicket,queue:Option<(joint::Journal,nat)>)->bool {
        self.certified() && self.inverse()==inverse && self.ticket()==ticket && self.queue()==queue
    }
    pub(crate) proof fn establish_interval(&self)
        requires self.protocol(),ensures self.certified(),
    {
        reveal(Evidence::certified);
        if self.queue().is_some() {
            interval::issued_interval(&self.issue().unwrap(),&self.acknowledgement().unwrap(),self.queue().unwrap().1,self.ticket());
        }
    }
    /// The real read may observe the state immediately after issue, without
    /// appending any event. The ticket stays outstanding throughout that read,
    /// through a successful write if present, and until acknowledgement.
    pub proof fn custody_interval(&self)
        requires self.certified(),self.queue().is_some(),
        ensures interval::holds(self.acknowledgement().unwrap().events(),self.issue().unwrap().at()+1,
                self.acknowledgement().unwrap().at(),self.queue().unwrap().1,self.ticket()),
            self.same_domain() ==> {
                let frames=self.acknowledgement().unwrap().events();let key=self.queue().unwrap().1;
                let read=self.attempt().read().checkpoint();let end=self.attempt().endpoint();
                &&& self.issue().unwrap().events().len()<=read.events().len()<=end.events().len()<=self.acknowledgement().unwrap().at()
                &&& interval::outstanding(interval::at(frames,read.events().len(),key),self.ticket())
                &&& interval::outstanding(interval::at(frames,end.events().len(),key),self.ticket())
                &&& interval::at(frames,read.events().len(),key).committed==interval::at(frames,self.issue().unwrap().events().len(),key).committed
            },
    {
        reveal(Evidence::certified);self.attempt().boundaries();
        if self.same_domain() {
            interval::checkpoint_interval(&self.issue().unwrap(),&self.attempt().read().checkpoint(),
                &self.attempt().endpoint(),&self.acknowledgement().unwrap(),self.queue().unwrap().1,self.ticket());
        }
    }
    /// The full classified sequence retains all interleavings. A read cut is
    /// a prefix length; only an actual successful write has a mutation index.
    pub proof fn microsteps(&self)->(frames:Seq<joint::Frame>)
        requires self.certified(),self.same_domain(),
        ensures frames==self.acknowledgement().unwrap().events(),joint::classification::history(frames),
            self.issue().unwrap().at()<self.attempt().read().checkpoint().events().len()<=self.acknowledgement().unwrap().at(),
            frames.take(self.attempt().read().checkpoint().events().len() as int)==self.attempt().read().checkpoint().events(),
            self.attempt().write().is_some() ==> self.issue().unwrap().at()<self.attempt().write().unwrap().at()<self.acknowledgement().unwrap().at()
                && frames[self.attempt().write().unwrap().at() as int].event==self.attempt().write().unwrap().event()
                && self.attempt().write().unwrap().event().change==joint::Change::PayloadRestore,
            self.attempt().write().is_none() ==> self.attempt().endpoint().same(&self.attempt().read().checkpoint()),
            frames[self.issue().unwrap().at() as int].event==self.issue().unwrap().event(),frames.last().event==self.acknowledgement().unwrap().event(),
    {
        reveal(Evidence::certified);
        let ack=self.acknowledgement().unwrap();let read=self.attempt().read().checkpoint();let end=self.attempt().endpoint();
        self.attempt().facts();ack.classify();self.attempt().classified();self.custody_interval();
        if self.attempt().write().is_some() {ack.after_cover(&end,&read);} else {assert(end.same(&read));}
        ack.included(&self.issue().unwrap());
        if self.attempt().write().is_some() {ack.included(&self.attempt().write().unwrap());}
        ack.events()
    }
    pub proof fn completed_attempt_stays_closed(&self,later:&joint::Snapshot)
        requires self.certified(),self.queue().is_some(),later.certified(),later.journal_spec()==self.queue().unwrap().0,
            self.acknowledgement().unwrap().events().len()<=later.events().len(),
            later.events().take(self.acknowledgement().unwrap().events().len() as int)==self.acknowledgement().unwrap().events(),
        ensures interval::retired(later.events(),self.acknowledgement().unwrap().events().len(),self.queue().unwrap().1,self.ticket()),
    {
        reveal(Evidence::certified);
        let ack=self.acknowledgement().unwrap();let frames=ack.events();let key=self.queue().unwrap().1;
        assert(interval::present(frames,ack.at(),key));interval::after_completion(frames,ack.at(),key,self.ticket());
        later.valid_history();interval::closed_extension(frames,later.events(),key,self.ticket());
    }
}
}
