//! A managed inverse is related to its actual forward event and actual queue
//! insertion. The intermediate interval is explicit; this is not atomicity.
use super::{joint, Applied};
#[cfg(verus_keep_ghost)]
use super::{Event, Inverse, ValueState};
use crate::execution::Execution;
use crate::lifecycle_state::registration::shared_child::ChildCleanup;
#[cfg(verus_keep_ghost)]
use crate::Port;
use vstd::prelude::*;

verus! {
/// Persistent witnesses indexed by the actual instruction and its write or
/// inverse registration. This map, including foreign-domain witnesses, erases.
pub type ReceiptMap=Map<(int,bool),joint::Receipt>;
pub open spec fn witnesses(receipts:ReceiptMap)->bool {
    forall|k:(int,bool)| receipts.contains_key(k) ==> #[trigger] receipts[k].wf()
}
pub open spec fn recorded_in(receipts:ReceiptMap,index:int,evidence:Evidence)->bool {
    receipts.contains_key((index,false)) && receipts[(index,false)].same(&evidence.write())
        && (evidence.insertion().is_some() ==> receipts.contains_key((index,true))
            && receipts[(index,true)].same(&evidence.insertion().unwrap()))
}
pub open spec fn before_return(receipts:ReceiptMap,end:joint::Receipt)->bool {
    forall|k:(int,bool)| receipts.contains_key(k) && #[trigger] receipts[k].journal()==end.journal() ==> end.follows(&receipts[k])
}
pub proof fn registered_before_return(receipts:ReceiptMap,index:int,evidence:Evidence,end:joint::Receipt)
    requires recorded_in(receipts,index,evidence),before_return(receipts,end),
    ensures evidence.write().journal()==end.journal() ==> end.follows(&evidence.write()),
        evidence.insertion().is_some() && evidence.insertion().unwrap().journal()==end.journal() ==> end.follows(&evidence.insertion().unwrap()),
{}

#[allow(dead_code)]
pub tracked struct Evidence {
    write:joint::Receipt,insertion:Option<joint::Receipt>,
    ghost queue:Option<(joint::Journal,nat)>,ghost token:usize,ghost domain:u64,
}
impl Evidence {
    pub closed spec fn write(&self)->joint::Receipt {self.write}
    pub(crate) proof fn retain(tracked &self,tracked receipts:&mut ReceiptMap,index:int)
        requires self.certified(),witnesses(*old(receipts)),
        ensures witnesses(*final(receipts)),recorded_in(*final(receipts),index,*self),
            *final(receipts)==if self.insertion().is_some() {
                old(receipts).insert((index,false),final(receipts)[(index,false)]).insert((index,true),final(receipts)[(index,true)])
            } else {old(receipts).insert((index,false),final(receipts)[(index,false)])},
            forall|k:(int,bool)| k.0!=index ==> final(receipts).contains_key(k)==old(receipts).contains_key(k)
                && (old(receipts).contains_key(k) ==> #[trigger] final(receipts)[k]==old(receipts)[k]),
    {
        receipts.tracked_insert((index,false),self.write.duplicate());
        match &self.insertion {Some(receipt)=>receipts.tracked_insert((index,true),receipt.duplicate()),None=>{}}
    }
    /// Same-domain completion includes inverse registration. Foreign queues
    /// retain their own boundary; their event cannot order the value Journal.
    pub open spec fn completion(&self)->joint::Receipt {if self.same_domain() {self.insertion().unwrap()} else {self.write()}}
    pub proof fn completion_valid(&self)
        requires self.certified(),
        ensures self.completion().wf(),self.completion().covers(&self.write()),
    {if !self.same_domain() {assert(self.write().events().take(self.write().events().len() as int) =~= self.write().events());}}
    pub(crate) proof fn completion_receipt(tracked &self)->(tracked out:joint::Receipt)
        requires self.certified(),
        ensures out.wf(),out.same(&self.completion()),out.covers(&self.write()),
    {
        self.completion_valid();
        if self.same_domain() {match &self.insertion {Some(receipt)=>receipt.duplicate(),None=>self.write.duplicate()}} else {self.write.duplicate()}
    }
    pub closed spec fn insertion(&self)->Option<joint::Receipt> {self.insertion}
    pub closed spec fn queue(&self)->Option<(joint::Journal,nat)> {self.queue}
    pub closed spec fn token(&self)->usize {self.token}
    pub closed spec fn domain(&self)->u64 {self.domain}
    pub open spec fn same_domain(&self)->bool {self.queue().is_some() && self.queue().unwrap().0==self.write().journal()}
    pub open spec fn certified(&self)->bool {
        &&& self.write().wf()
        &&& self.write().event().change is Value
        &&& (self.write().event().change->Value_event is Forward || self.write().event().change->Value_event is Computed)
        &&& self.insertion().is_some()==self.queue().is_some()
        &&& self.insertion().is_some() ==> {
            let r=self.insertion().unwrap();
            &&& r.wf() && r.journal()==self.queue().unwrap().0 && r.event().key==self.queue().unwrap().1
            &&& r.event().change==if self.same_domain() {joint::Change::RegisterInverse {write:self.write().at()}}
                else {joint::Change::Cleanup {event:joint::episode::CleanupChange::Register}}
            &&& r.event().after is Cleanup
            &&& r.event().after->Cleanup_state.domain==self.domain()
            &&& r.event().after->Cleanup_state.occupied.len()==self.token()+1
            &&& r.event().after->Cleanup_state.occupied[self.token() as int]
            &&& r.event().after->Cleanup_state.waiting.last()==self.token()
            &&& self.same_domain() ==> r.follows(&self.write())
                && r.event().settled==Some(self.write().at())
                && joint::pending_at(r.events(),r.at()).contains_key(self.write().at())
                && !r.events().last().pending.contains_key(self.write().at())
        }
    }
    pub open spec fn records(&self,inverse:Inverse,queue:Option<(joint::Journal,nat)>,domain:u64,token:usize)->bool {
        self.certified() && inverse.recorded() && self.write().same(&inverse.origin())
            && self.queue()==queue && self.domain()==domain && self.token()==token
    }
    /// Before this actual queue insertion, every intermediate journal state
    /// retains the obligation backed by the executor's linear capability.
    /// The insertion consumes it in the same commit as the queue entry.
    pub proof fn pending_interval(&self)
        requires self.certified(),self.same_domain(),
        ensures self.write().event().pending,
            forall|n:nat| self.write().at()<n<=self.insertion().unwrap().at() ==>
                #[trigger] joint::pending_at(self.insertion().unwrap().events(),n).contains_pair(self.write().at(),self.write().event().key),
            !self.insertion().unwrap().events().last().pending.contains_key(self.write().at()),
    {
        let frames=self.microsteps();
        joint::pending_since(frames,self.write().at(),self.insertion().unwrap().at());
    }
    /// The actual registered inverse stays registered through a later return.
    /// This concerns this write's debt, not other concurrent writers' debts or
    /// the eventual execution/success of the retained inverse.
    pub proof fn settled_through(&self,end:&joint::Receipt)
        requires self.certified(),self.same_domain(),end.wf(),end.covers(&self.insertion().unwrap()),
        ensures !joint::pending_at(end.events(),end.events().len()).contains_key(self.write().at()),
            forall|n:nat| self.insertion().unwrap().events().len()<=n<=end.events().len() ==>
                !#[trigger] joint::pending_at(end.events(),n).contains_key(self.write().at()),
            forall|i:nat| i<end.events().len() && (#[trigger] end.events()[i as int]).event.settled==Some(self.write().at())
                ==> i==self.insertion().unwrap().at(),
    {
        let inserted=self.insertion().unwrap();end.included(&inserted);
        assert(joint::pending_at(end.events(),inserted.events().len())==inserted.events().last().pending);
        joint::pending_absent_later(end.events(),self.write().at(),inserted.events().len(),end.events().len());
        assert forall|i:nat| i<end.events().len() && (#[trigger] end.events()[i as int]).event.settled==Some(self.write().at())
            implies i==inserted.at() by {joint::unique_settlement(end.events(),i,inserted.at(),self.write().at());}
    }
    /// Real interleavings remain in the interval. No consecutive-index premise
    /// or caller-provided "coherent" table is used to manufacture this pair.
    pub proof fn microsteps(&self)->(frames:Seq<joint::Frame>)
        requires self.certified(),self.same_domain(),
        ensures joint::valid(frames),self.write().at()<self.insertion().unwrap().at(),
            frames==self.insertion().unwrap().events(),
            frames[self.write().at() as int].event==self.write().event(),
            frames.last().event==self.insertion().unwrap().event(),
            frames.last().event.key==self.queue().unwrap().1,
            frames.last().event.change==(joint::Change::RegisterInverse {write:self.write().at()}),
    {
        let frames=self.insertion().unwrap().events();
        assert(frames[self.write().at() as int]==self.write().events()[self.write().at() as int]);
        frames
    }
}
impl Evidence {
    /// The forward end of the recorded pair uses the dependent grammar's
    /// actual operation and strict returned inverse. The registration end is
    /// an explicit implementation rule, not silently an atomic paper step.
    pub proof fn paper_write(&self,inverse:Inverse,key:Port,table:Map<Port,ValueState>)
        requires self.records(inverse,self.queue(),self.domain(),self.token()),
            table.contains_key(key),table[key]==inverse.state().before,
        ensures super::interpreted_step(self.write().event().change->Value_event,key,table,table.insert(key,inverse.state().after)),
            forall|current:ValueState| #[trigger] inverse.state().undo(current)==
                if current==self.write().event().change->Value_event.after() {Some(self.write().event().change->Value_event.before())} else {None},
    {super::interpret_event(self.write().event().change->Value_event,key,table);}
}
pub(crate) struct Registered {pub(crate) token:usize,pub(crate) evidence:Tracked<Evidence>}
impl<V,C,G,Cb,X> Execution<V,C,G,ChildCleanup<Cb,X>> {
    /// Private typed bridge: the witness comes from this very payload. An
    /// arbitrary Ghost index cannot stand in for the actual forward operation.
    pub(crate) fn register_inverse(&mut self,id:usize,applied:Applied)->(out:Registered)
        requires old(self).wf(),old(self).cleanup_state().live(id),applied.inverse.recorded(),
            applied.pending_for(joint::local(old(self).cleanup_state().queues()[id].link(),applied.inverse.target().journal_spec())),
        ensures final(self).wf(),final(self).execution_journal()==old(self).execution_journal(),final(self).value_attempts()==old(self).value_attempts(),
            final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),
            final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(),
            final(self).effect_state()==old(self).effect_state(),final(self).checked_out()==old(self).checked_out(),final(self).initialized()==old(self).initialized(),
            final(self).cleanup_state().frame(&old(self).cleanup_state(),id),
            final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids(),
            final(self).cleanup_state().drained_failure()==old(self).cleanup_state().drained_failure(),
            final(self).cleanup_state().acquisition_open(id)==old(self).cleanup_state().acquisition_open(id),
            final(self).cleanup_state().live(id),final(self).cleanup_state().queues()[id].link()==old(self).cleanup_state().queues()[id].link(),out.token==old(self).cleanup_state().queues()[id].slots().len(),
            final(self).cleanup_state().queues()[id].slots()==old(self).cleanup_state().queues()[id].slots().push(Some(ChildCleanup::<Cb,X>::Value(applied.inverse))),
            final(self).cleanup_state().queues()[id].protocol().waiting()==old(self).cleanup_state().queues()[id].protocol().waiting().push(out.token),
            out.evidence@.records(applied.inverse,final(self).cleanup_state().queues()[id].link(),final(self).cleanup_state().queues()[id].protocol().domain_id(),out.token),
            final(self).status_links()==old(self).status_links(),
    {
        proof {self.representation();}
        let tracked write=applied.inverse.origin.borrow().duplicate();
        let tracked cause=Some(write.duplicate());
        let inserted=self.groups.register_following(id,ChildCleanup::Value(applied.inverse),Tracked(cause),applied.pending);
        proof {self.representation();}
        assert(inserted.is_ok());
        let inserted=match inserted {Ok(value)=>value,Err(_)=>{assert(false);panic!("live cleanup group");}};
        let tracked evidence=Evidence {write,insertion:inserted.trace.get(),
            queue:self.cleanup_state().queues()[id].link(),domain:self.cleanup_state().queues()[id].protocol().domain_id(),token:inserted.token};
        Registered {token:inserted.token,evidence:Tracked(evidence)}
    }
}
}
