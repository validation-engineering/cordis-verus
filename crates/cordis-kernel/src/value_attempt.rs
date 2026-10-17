//! Erased owner-local receipts for real scalar calls, including rejected calls.
//! The producer appends while holding the value lock. Returning an error must
//! identify that rejection; discarding a successful inverse cannot invent one.
use super::joint;
#[cfg(verus_keep_ghost)]
use super::{
    effect::{Code, EffectError},
    Event, Inverse, Operation, ReversibleValue, ValueError, ValueState,
};
use vstd::prelude::*;

verus! {
pub open spec fn value_rejection(event:Event,op:Operation,error:ValueError)->bool {
    &&& event is Rejected && event->Rejected_operation==op && event.valid()
    &&& error==if event.before().depth==u64::MAX {ValueError::Capacity} else {ValueError::Overflow}
}
pub open spec fn effect_rejection(event:Event,code:Code,expected:ValueState,error:EffectError)->bool {
    match error {
        EffectError::Interference=>event==(Event::StaleComputation {expected,before:event.before()}) && event.valid(),
        EffectError::Capacity=>event==(Event::ComputationRejected {code,before:expected}) && expected.depth==u64::MAX,
        EffectError::Rejected=>event==(Event::ComputationRejected {code,before:expected}) && expected.depth<u64::MAX && code(expected.value).is_none(),
        EffectError::Closed=>false,
    }
}
#[allow(dead_code)] // All receipts are erased, with no runtime history allocation.
pub tracked struct Ledger {ghost events:Seq<joint::Receipt>,last:Option<joint::Receipt>}
impl Ledger {
    pub closed spec fn events(&self)->Seq<joint::Receipt> {self.events}
    pub closed spec fn last(&self)->Option<joint::Receipt> {self.last}
    pub open spec fn wf(&self)->bool {
        (self.last().is_some()==(self.events().len()>0))
            && (self.last().is_some() ==> self.last().unwrap().wf() && self.last().unwrap().same(&self.events().last()))
            && forall|i:int| 0<=i<self.events().len() ==> (#[trigger] self.events()[i]).wf()
                && self.events()[i].event().change is Value
                && self.events()[i].event().change->Value_event.valid()
    }
    pub open spec fn appended(&self,prior:&Self,target:&ReversibleValue)->bool {
        self.wf() && self.events().len()==prior.events().len()+1
            && self.events().take(prior.events().len() as int)==prior.events()
            && self.events().last().journal()==target.journal_spec()
            && self.events().last().event().key==target.object().key
    }
    pub open spec fn event(&self)->Event {self.events().last().event().change->Value_event}
    pub open spec fn records(&self,inverse:Inverse)->bool {
        self.events().len()>0 && self.events().last().same(&inverse.origin())
    }
    /// A rejected attempt stutters the whole joint observation at its actual
    /// commit, including outstanding inverse obligations. Other callers may
    /// still interleave before or after that commit.
    pub proof fn rejection_step(&self)
        requires self.wf(),self.events().len()>0,
            self.event() is Rejected || self.event() is ComputationRejected || self.event() is StaleComputation,
        ensures {
            let receipt=self.events().last();let frames=receipt.events();
            &&& joint::state_at(frames,receipt.at())==frames.last().state
            &&& joint::pending_at(frames,receipt.at())==frames.last().pending
            &&& !receipt.event().pending && receipt.event().settled.is_none()
        },
    {
        let receipt=self.events().last();let frames=receipt.events();
        receipt.transition();
        assert(joint::step(joint::state_at(frames,receipt.at()),frames.last().state,receipt.event()));
        reveal(joint::changes);
        assert(joint::state_at(frames,receipt.at()) =~= frames.last().state);
    }
    pub(crate) proof fn latest(tracked &self)->(tracked out:joint::Receipt)
        requires self.wf(),self.events().len()>0,
        ensures out.wf(),out.same(&self.events().last()),
    {match &self.last {Some(receipt)=>receipt.duplicate(),None=>{assert(false);proof_from_false()}}}
    pub(crate) proof fn new()->(tracked out:Self)
        ensures out.wf(),out.events()==Seq::<joint::Receipt>::empty(),
    {Self {events:Seq::empty(),last:None}}
    pub(super) proof fn record(tracked &mut self,tracked receipt:&joint::Receipt)
        requires old(self).wf(),receipt.wf(),receipt.event().change is Value,
            receipt.event().change->Value_event.valid(),
        ensures final(self).wf(),final(self).events()==old(self).events().push(*receipt),
            final(self).events().take(old(self).events().len() as int)==old(self).events(),
    {
        let prior=self.events;self.events=self.events.push(*receipt);self.last=Some(receipt.duplicate());
        assert(self.events.take(prior.len() as int) =~= prior);
    }
}
}
