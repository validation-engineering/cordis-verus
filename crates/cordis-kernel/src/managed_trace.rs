//! The complete stored function, actual mixed queue suffix and strict inverse.
#[cfg(verus_keep_ghost)]
use super::Function;
#[cfg(verus_keep_ghost)]
use super::{
    retained,
    semantics::{self as s, Value},
    tokens, Action, Call, Owner, ResultStep, Slot,
};
use super::{Report, Step};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::effect::ScalarEffect;
#[cfg(verus_keep_ghost)]
use crate::{
    cleanup_groups::payload as cleanup,
    dependent_grammar as d,
    lifecycle_state::{registration::shared_child::ChildCleanup, services::NativeEpisode},
    reversible_value::service_composition::Address,
    Port,
};
use vstd::prelude::*;

verus! {
pub open spec fn forward<T:?Sized>(steps:Seq<Step<T>>)->bool {forall|i:int,j:int|#![trigger steps[i],steps[j]] 0<=i<j<steps.len() ==> steps[i].pc<steps[j].pc}
proof fn transitive<T:?Sized>(steps:Seq<Step<T>>,i:int,j:int)
    requires 0<=i<j<steps.len(),forall|k:int|0<k<steps.len() ==> (#[trigger] steps[k-1]).pc<steps[k].pc,
    ensures steps[i].pc<steps[j].pc,
    decreases j-i,
{assert(steps[j-1].pc<steps[j].pc);if j>i+1 {transitive(steps,i,j-1);}}
impl<T:?Sized> Report<T> {
    pub open spec fn resolution(&self)->spec_fn(usize)->Address {
        |pc:usize|if exists|i:int|0<=i<self.steps.len() && (#[trigger] self.steps@[i]).pc==pc {
            self.steps@[choose|i:int|0<=i<self.steps.len() && (#[trigger] self.steps@[i]).pc==pc].address()
        } else {arbitrary()}
    }
    pub open spec fn heads(&self)->spec_fn(usize)->u64 {
        |pc:usize|if exists|i:int|0<=i<self.steps.len() && (#[trigger] self.steps@[i]).pc==pc {
            self.steps@[choose|i:int|0<=i<self.steps.len() && (#[trigger] self.steps@[i]).pc==pc].head()
        } else {0}
    }
    proof fn positions<E:ScalarEffect,M>(&self,body:&Function<E,T>,ports:Seq<Port>,episode:NativeEpisode<Slot<T,M>>)
        requires body.valid(),self.certified(body.code(),ports,episode),
        ensures forward(self.steps@),
    {
        assert forall|i:int|0<i<self.steps.len() implies (#[trigger] self.steps@[i-1]).pc<self.steps@[i].pc by {
            assert(self.steps@.take(i).last()==self.steps@[i-1]);
        }
        assert forall|i:int,j:int|#![trigger self.steps@[i],self.steps@[j]] 0<=i<j<self.steps.len() implies self.steps@[i].pc<self.steps@[j].pc by {transitive(self.steps@,i,j);}
    }
    proof fn position(&self,i:int)
        requires forward(self.steps@),0<=i<self.steps.len(),
        ensures (self.resolution())(self.steps@[i].pc)==self.steps@[i].address(),(self.heads())(self.steps@[i].pc)==self.steps@[i].head(),
    {
        let pc=self.steps@[i].pc;
        assert(exists|j:int|0<=j<self.steps.len() && (#[trigger] self.steps@[j]).pc==pc);
        let j=choose|j:int|0<=j<self.steps.len() && (#[trigger] self.steps@[j]).pc==pc;
        if j<i {assert(self.steps@[j].pc<self.steps@[i].pc);}else if i<j {assert(self.steps@[i].pc<self.steps@[j].pc);}
        assert(i==j);
    }
    #[verifier::opaque]
    pub open spec fn interpreted<E:ScalarEffect>(&self,code:Seq<Call<E,T>>)->bool {
        &&& d::member(s::library::<Address,T>(),s::program(code,self.resolution(),self.heads()),s::keys(code,self.resolution()),ISet::empty(),0)
        &&& forall|i:int,heap:Map<Address,Value<T>>|#![trigger self.steps@[i],d::run(s::library::<Address,T>(),s::node(code,self.resolution(),self.heads(),self.steps@[i].pc),heap)]
            0<=i<self.steps.len() && heap.contains_key(self.steps@[i].address()) && heap[self.steps@[i].address()]==self.steps@[i].before() ==> {
                let step=self.steps@[i];let run=d::run(s::library::<Address,T>(),s::node(code,self.resolution(),self.heads(),step.pc),heap);
                &&& run.is_some() && run.unwrap().state==heap.insert(step.address(),step.after()) && run.unwrap().next==step.next
                &&& forall|recovery:Map<Address,Value<T>>| #[trigger] (run.unwrap().undo)(recovery)==s::undo_step(step,recovery)
            }
    }
    /// Membership covers every input and both branches. The actual trace fixes
    /// only the resolution/fresh-stamp parameters and executed continuations.
    pub proof fn interpret<E:ScalarEffect,M>(&self,body:&Function<E,T>,ports:Seq<Port>,episode:NativeEpisode<Slot<T,M>>)
        requires body.valid(),self.certified(body.code(),ports,episode),
        ensures self.interpreted(body.code()),
    {
        self.positions(body,ports,episode);body.member(self.resolution(),self.heads(),0);reveal(Report::interpreted);
        assert forall|i:int,heap:Map<Address,Value<T>>|#![trigger self.steps@[i],d::run(s::library::<Address,T>(),s::node(body.code(),self.resolution(),self.heads(),self.steps@[i].pc),heap)]
            0<=i<self.steps.len() && heap.contains_key(self.steps@[i].address()) && heap[self.steps@[i].address()]==self.steps@[i].before() implies {
                let step=self.steps@[i];let run=d::run(s::library::<Address,T>(),s::node(body.code(),self.resolution(),self.heads(),step.pc),heap);
                &&& run.is_some() && run.unwrap().state==heap.insert(step.address(),step.after()) && run.unwrap().next==step.next
                &&& forall|recovery:Map<Address,Value<T>>| #[trigger] (run.unwrap().undo)(recovery)==s::undo_step(step,recovery)
            } by {
                self.position(i);self.steps@[i].interpretation(body.code()[self.steps@[i].pc as int],ports[self.steps@[i].pc as int],episode);
            }
    }
}
pub open spec fn undo_action<A,R,T:?Sized,M,X>(action:Action<A,R,T,M,X>,heap:Map<Address,Value<T>>)->Option<Map<Address,Value<T>>> {
    match action {
        ChildCleanup::Value(inverse)=>{
            let address=Address {journal:inverse.target().journal_spec(),key:inverse.target().object().key};
            if heap.contains_key(address) && heap[address]==Value::Scalar(inverse.state().after) {Some(heap.insert(address,Value::Scalar(inverse.state().before)))} else {None}
        },
        ChildCleanup::Callback(cleanup::Cleanup::Payload {inverse,..})=>{
            let address=Address {journal:inverse.owner().journal_spec(),key:inverse.owner().key()};
            if heap.contains_key(address) && heap[address]==Value::Payload(inverse.after().state()) {Some(heap.insert(address,Value::Payload(inverse.before().state())))} else {None}
        },_=>None,
    }
}
pub open spec fn queued_undo<A,R,T:?Sized,M,X>(slots:Seq<Option<Action<A,R,T,M,X>>>,heap:Map<Address,Value<T>>)->Option<Map<Address,Value<T>>>
    decreases slots.len(),
{
    if slots.len()==0 {Some(heap)} else if slots.last().is_none() {None} else {
        match undo_action(slots.last().unwrap(),heap) {Some(previous)=>queued_undo(slots.drop_last(),previous),None=>None}
    }
}
impl<T:?Sized> Step<T> {
    proof fn retained_inverse<E:ScalarEffect,A,R,M,X>(&self,slot:Option<Action<A,R,T,M,X>>,call:Call<E,T>,port:Port,episode:NativeEpisode<Slot<T,M>>)
        requires self.corresponds(call,port,episode),self.in_slot(slot),
        ensures forall|heap:Map<Address,Value<T>>| #[trigger] undo_action(slot.unwrap(),heap)==s::undo_step(*self,heap),
    {
        reveal(Step::corresponds);
        if let ResultStep::Payload(a)=self.result {a.inverse().provenance();}
    }
}
proof fn same_stack<A,R,T:?Sized,M,X>(steps:Seq<Step<T>>,slots:Seq<Option<Action<A,R,T,M,X>>>,heap:Map<Address,Value<T>>)
    requires slots.len()==steps.len(),forall|i:int|0<=i<steps.len() ==> (#[trigger] steps[i]).in_slot(slots[i])
        && forall|recovery:Map<Address,Value<T>>| #[trigger] undo_action(slots[i].unwrap(),recovery)==s::undo_step(steps[i],recovery),
    ensures queued_undo(slots,heap)==s::undo(steps,heap),
    decreases steps.len(),
{
    if steps.len()>0 {
        assert(steps.last().in_slot(slots.last()));
        assert(undo_action(slots.last().unwrap(),heap)==s::undo_step(steps.last(),heap));
        if let Some(previous)=s::undo_step(steps.last(),heap) {same_stack(steps.drop_last(),slots.drop_last(),previous);}
    }
}
impl<T:?Sized> Report<T> {
    pub open spec fn queue_semantics<C,G,A,R,M,X>(&self,owner:Owner<C,G,A,R,T,M,X>,id:usize,offset:nat)->bool {
        let slots=owner.cleanup_state().queues()[id].slots();let suffix=slots.subrange(offset as int,slots.len() as int);
        forall|heap:Map<Address,Value<T>>| #[trigger] queued_undo(suffix,heap)==s::undo(self.steps@,heap)
    }
    proof fn prefix_facts<E:ScalarEffect,M>(&self,code:Seq<Call<E,T>>,ports:Seq<Port>,episode:NativeEpisode<Slot<T,M>>)
        requires self.certified(code,ports,episode),
        ensures super::prefix(code,ports,self.steps@,episode),
    {}
    pub proof fn interpret_queue<E:ScalarEffect,C,G,A,R,M,X>(&self,code:Seq<Call<E,T>>,ports:Seq<Port>,episode:NativeEpisode<Slot<T,M>>,owner:Owner<C,G,A,R,T,M,X>,id:usize,offset:nat)
        requires self.certified(code,ports,episode),retained(self.steps@,owner,id,offset),
        ensures self.queue_semantics(owner,id,offset),
    {
        hide(Report::certified);self.prefix_facts(code,ports,episode);
        let slots=owner.cleanup_state().queues()[id].slots();let suffix=slots.subrange(offset as int,slots.len() as int);
        assert forall|i:int|0<=i<self.steps.len() implies (#[trigger] self.steps@[i]).in_slot(suffix[i])
            && forall|recovery:Map<Address,Value<T>>| #[trigger] undo_action(suffix[i].unwrap(),recovery)==s::undo_step(self.steps@[i],recovery) by {
            let step=self.steps@[i];step.retained_inverse(suffix[i],code[step.pc as int],ports[step.pc as int],episode);
        }
        assert forall|heap:Map<Address,Value<T>>| #[trigger] queued_undo(suffix,heap)==s::undo(self.steps@,heap) by {same_stack(self.steps@,suffix,heap);}
    }
    pub proof fn recoverable<C,G,A,R,M,X>(&self,owner:Owner<C,G,A,R,T,M,X>,id:usize,offset:nat,heap:Map<Address,Value<T>>)
        requires self.queue_semantics(owner,id,offset),s::replay(self.steps@,heap).is_some(),
        ensures queued_undo(owner.cleanup_state().queues()[id].slots().subrange(offset as int,owner.cleanup_state().queues()[id].slots().len() as int),s::replay(self.steps@,heap).unwrap())==Some(heap),
    {s::roundtrip(self.steps@,heap);}
    /// The checked dispatcher selects the last real token, regardless of
    /// whether its inverse belongs to a scalar or typed payload allocation.
    pub proof fn next_inverse<C,G,A,R,M,X>(&self,owner:Owner<C,G,A,R,T,M,X>,id:usize,offset:nat,prior:Seq<usize>,dispatch:cleanup::Dispatch<A,R,std::sync::Arc<Slot<T,M>>,T,X>)
        requires retained(self.steps@,owner,id,offset),self.steps.len()>0,
            owner.cleanup_state().queues()[id].protocol().waiting()==prior+tokens(self.steps@),
            owner.cleanup_state().queues()[id].protocol().selected().is_none(),
            dispatch.selected_from(None,owner.cleanup_state().queues()[id].protocol().waiting()),dispatch.from_slot(owner.cleanup_state().queues()[id].slots()),
        ensures dispatch.ticket().token==self.steps@.last().token(),
            self.steps@.last().result is Payload ==> dispatch is Payload,
            self.steps@.last().result is Scalar ==> dispatch is Other && dispatch->Other_0 is Value,
    {
        let waiting=owner.cleanup_state().queues()[id].protocol().waiting();assert(waiting.last()==tokens(self.steps@).last());
        assert(self.steps@.last().in_slot(owner.cleanup_state().queues()[id].slots()[self.steps@.last().token() as int]));
    }
}
impl<T:?Sized> super::Failure<T> {
    /// A rejected computed instruction preserves the complete recorded state.
    /// Capacity/rejection are undefined primitive results; interference is an
    /// explicit stale-input refusal, never a fabricated successful operation.
    pub proof fn rejection<E:ScalarEffect,M>(&self,call:Call<E,T>,port:Port,episode:NativeEpisode<Slot<T,M>>)
        requires self.explained(call,port,episode),self.error is Scalar,
        ensures self.receipt@.is_some(),{
            let r=self.receipt@.unwrap();let event=r.event().change->Value_event;
            &&& crate::reversible_value::joint::state_at(r.events(),r.at())==r.events().last().state
            &&& crate::reversible_value::joint::pending_at(r.events(),r.at())==r.events().last().pending
            &&& self.error->Scalar_0!=crate::reversible_value::effect::EffectError::Interference ==>
                s::operation(s::code(call.effect,0))(Value::Scalar(event.before())).is_none()
        },
    {
        reveal(super::Failure::explained);
        let r=self.receipt@.unwrap();r.transition();reveal(crate::reversible_value::joint::changes);
        assert(crate::reversible_value::joint::state_at(r.events(),r.at()) =~= r.events().last().state);
    }
}

}
