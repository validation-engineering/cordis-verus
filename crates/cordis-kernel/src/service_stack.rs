//! Strict accumulated inverse of the actual retained multi-service prefix.
//! The proof is over qualified allocations, so aliases share one stack cell and
//! foreign Journals remain distinct. Interference is not hidden by restoration.
use super::services::Report;
#[cfg(verus_keep_ghost)]
use super::{
    service_composition::{address, Address},
    services::{self, Step},
    slot::ServiceSlot,
    Inverse, ValueState,
};
#[cfg(verus_keep_ghost)]
use crate::{execution::Execution, lifecycle_state::registration::shared_child::ChildCleanup};
use vstd::prelude::*;

verus! {
pub open spec fn redo(step:Step,heap:Map<Address,ValueState>)->Option<Map<Address,ValueState>> {
    let event=step.write.admission.registration().write().event().change->Value_event;let key=address(step.write);
    if heap.contains_key(key) && heap[key]==event.before() {Some(heap.insert(key,event.after()))} else {None}
}
pub open spec fn undo_step(step:Step,heap:Map<Address,ValueState>)->Option<Map<Address,ValueState>> {
    let event=step.write.admission.registration().write().event().change->Value_event;let key=address(step.write);
    if heap.contains_key(key) && heap[key]==event.after() {Some(heap.insert(key,event.before()))} else {None}
}
pub open spec fn replay(steps:Seq<Step>,heap:Map<Address,ValueState>)->Option<Map<Address,ValueState>>
    decreases steps.len(),
{
    if steps.len()==0 {Some(heap)} else {match replay(steps.drop_last(),heap) {Some(previous)=>redo(steps.last(),previous),None=>None}}
}
pub open spec fn undo(steps:Seq<Step>,heap:Map<Address,ValueState>)->Option<Map<Address,ValueState>>
    decreases steps.len(),
{
    if steps.len()==0 {Some(heap)} else {match undo_step(steps.last(),heap) {Some(previous)=>undo(steps.drop_last(),previous),None=>None}}
}
/// When the actual before/after observations compose from this input, the
/// reverse stack recovers it. This does not assume that inverse calls succeed.
/// A conflicting external write can make replay or the real undo reject.
pub proof fn roundtrip(steps:Seq<Step>,heap:Map<Address,ValueState>)
    requires replay(steps,heap).is_some(),
    ensures undo(steps,replay(steps,heap).unwrap())==Some(heap),
    decreases steps.len(),
{
    if steps.len()>0 {
        let previous=replay(steps.drop_last(),heap).unwrap();let step=steps.last();let key=address(step.write);
        let event=step.write.admission.registration().write().event().change->Value_event;
        assert(previous.insert(key,event.after()).insert(key,event.before()) =~= previous);
        roundtrip(steps.drop_last(),heap);
    }
}
pub open spec fn inverse_address(inverse:Inverse)->Address {
    Address {journal:inverse.target().journal_spec(),key:inverse.target().object().key}
}
pub open spec fn inverse_step(inverse:Inverse,heap:Map<Address,ValueState>)->Option<Map<Address,ValueState>> {
    let key=inverse_address(inverse);
    if !heap.contains_key(key) {None} else {match inverse.state().undo(heap[key]) {Some(value)=>Some(heap.insert(key,value)),None=>None}}
}
pub open spec fn queued_undo(inverses:Seq<Inverse>,heap:Map<Address,ValueState>)->Option<Map<Address,ValueState>>
    decreases inverses.len(),
{
    if inverses.len()==0 {Some(heap)} else {match inverse_step(inverses.last(),heap) {Some(previous)=>queued_undo(inverses.drop_last(),previous),None=>None}}
}
pub open spec fn agrees(steps:Seq<Step>,inverses:Seq<Inverse>)->bool {
    steps.len()==inverses.len() && forall|i:int| 0<=i<steps.len() ==> {
        let step=#[trigger] steps[i];let inverse=inverses[i];let event=step.write.admission.registration().write().event().change->Value_event;
        &&& inverse_address(inverse)==address(step.write)
        &&& inverse.state().before==event.before() && inverse.state().after==event.after()
    }
}
proof fn same_stack(steps:Seq<Step>,inverses:Seq<Inverse>,heap:Map<Address,ValueState>)
    requires agrees(steps,inverses),
    ensures queued_undo(inverses,heap)==undo(steps,heap),
    decreases steps.len(),
{
    if steps.len()>0 {
        assert(inverse_step(inverses.last(),heap)==undo_step(steps.last(),heap));
        assert(agrees(steps.drop_last(),inverses.drop_last()));
        if let Some(previous)=undo_step(steps.last(),heap) {same_stack(steps.drop_last(),inverses.drop_last(),previous);}
    }
}
pub open spec fn actual_queue<T,M,C,G,Cb,X>(execution:Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>>,id:usize,offset:nat)->Seq<Inverse> {
    let slots=execution.cleanup_state().queues()[id].slots();
    slots.subrange(offset as int,slots.len() as int).map(|_:int,slot:Option<ChildCleanup<Cb,X>>|slot.unwrap()->Value_0)
}
impl Report {
    pub open spec fn queue_semantics<T,M,C,G,Cb,X>(&self,execution:Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>>,id:usize,offset:nat)->bool {
        forall|heap:Map<Address,ValueState>| #[trigger] queued_undo(actual_queue(execution,id,offset),heap)==undo(self.steps@,heap)
    }
    /// Use the exact retained queue suffix, including the failed body's prefix.
    /// A caller cannot substitute a second list of expected inverses.
    pub proof fn interpret_queue<T,M,C,G,Cb,X>(&self,execution:Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>>,id:usize,offset:nat)
        requires services::retained(self.steps@,execution,id,offset),
        ensures self.queue_semantics(execution,id,offset),
    {
        let inverses=actual_queue(execution,id,offset);
        assert forall|i:int| 0<=i<self.steps.len() implies {
            let step=#[trigger] self.steps@[i];let inverse=inverses[i];let event=step.write.admission.registration().write().event().change->Value_event;
            &&& inverse_address(inverse)==address(step.write)
            &&& inverse.state().before==event.before() && inverse.state().after==event.after()
        } by {
            assert(self.steps@[i].write.recorded(execution,id));
            assert(inverses[i]==execution.cleanup_state().queues()[id].slots()[offset+i].unwrap()->Value_0);
        }
        assert forall|heap:Map<Address,ValueState>| #[trigger] queued_undo(inverses,heap)==undo(self.steps@,heap)
            by {same_stack(self.steps@,inverses,heap);}
    }
    /// Combine the real waiting suffix with dispatch's exported LIFO policy.
    /// An already selected retry keeps its own ticket and is handled separately.
    pub proof fn next_queued_inverse<T,M,C,G,Cb,X>(&self,execution:Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>>,id:usize,offset:nat,prior:Seq<usize>,dispatch:crate::cleanup_queue::completion::CleanupDispatch<Cb,X>)
        requires services::retained(self.steps@,execution,id,offset),self.steps.len()>0,
            execution.cleanup_state().queues()[id].protocol().waiting()==prior+services::tokens(self.steps@),
            execution.cleanup_state().queues()[id].protocol().selected().is_none(),
            dispatch.selected_from(execution.cleanup_state().queues()[id].protocol().selected(),execution.cleanup_state().queues()[id].protocol().waiting()),
            dispatch.from_slot(execution.cleanup_state().queues()[id].slots()),
        ensures dispatch is Value,dispatch.ticket().token==self.steps@.last().write.admission.token,
            dispatch->Value_completion.corresponds(actual_queue(execution,id,offset).last()),
    {
        let waiting=execution.cleanup_state().queues()[id].protocol().waiting();
        let last=self.steps@.last();
        assert(waiting.last()==services::tokens(self.steps@).last());
        assert(last.write.recorded(execution,id));
        assert(actual_queue(execution,id,offset).last()==execution.cleanup_state().queues()[id].slots()[last.write.admission.token as int].unwrap()->Value_0);
    }
    pub proof fn recoverable<T,M,C,G,Cb,X>(&self,execution:Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>>,id:usize,offset:nat,heap:Map<Address,ValueState>)
        requires services::retained(self.steps@,execution,id,offset),replay(self.steps@,heap).is_some(),
        ensures queued_undo(actual_queue(execution,id,offset),replay(self.steps@,heap).unwrap())==Some(heap),
    {self.interpret_queue(execution,id,offset);roundtrip(self.steps@,heap);}
}
}
