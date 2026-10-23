//! Finite composition of real mixed-dispatch observations and retained slots.
//! Queue snapshots and read values are source conditions, not a premise that
//! any inverse succeeds. This is not a scheduler or whole-Unload theorem.
use super::root::RegisteredReport;
#[cfg(verus_keep_ghost)]
use super::{semantics::Value, trace, Action, Owner};
use crate::{cleanup_groups::payload as cleanup, reversible_value::effect::ScalarEffect};
#[cfg(verus_keep_ghost)]
use crate::{
    cleanup_groups::payload::recovery as r, cleanup_queue::CleanupQueue,
    reversible_value::service_composition::Address,
};
use vstd::prelude::*;

verus! {
pub type Turn<A,R,T,M,X> = cleanup::Dispatch<A,R,std::sync::Arc<super::Slot<T,M>>,T,X>;
pub open spec fn slots_at<A,R,T:?Sized,M,X>(turns:Seq<Turn<A,R,T,M,X>>,initial:Seq<Option<Action<A,R,T,M,X>>>,n:nat)->Seq<Option<Action<A,R,T,M,X>>> {
    if n==0 {initial} else {turns[n-1].after_queue().slots()}
}
/// The value trajectory is constructed from actual cleanup outputs. It is a
/// per-allocation interpretation; interleaving unrelated commits is allowed.
pub open spec fn values_at<A,R,T:?Sized,M,X>(turns:Seq<Turn<A,R,T,M,X>>,initial:Map<Address,Value<T>>,n:nat)->Map<Address,Value<T>>
    decreases n,
{
    if n==0 {initial} else {
        let turn=turns[n-1];let action=turn.before_queue().slots()[turn.ticket().token as int].unwrap();
        turn.apply_observation(action,values_at(turns,initial,(n-1) as nat))
    }
}
pub open spec fn linked<A,R,T:?Sized,M,X>(turns:Seq<Turn<A,R,T,M,X>>,queue:CleanupQueue<Action<A,R,T,M,X>>,initial:Map<Address,Value<T>>,offset:nat)->bool {
    queue.link().is_some() && offset<=queue.slots().len() && forall|i:int|0<=i<turns.len() ==> {
        let turn=#[trigger] turns[i];let dispatch=turn;let token=dispatch.ticket().token;
        &&& dispatch.authentic() && dispatch.managed()
        &&& turn.before_queue().link()==queue.link() && turn.after_queue().link()==queue.link()
        &&& turn.before_queue().protocol().domain_id()==queue.protocol().domain_id() && dispatch.ticket().domain==queue.protocol().domain_id()
        &&& turn.before_queue().slots()==slots_at(turns,queue.slots(),i as nat)
        &&& queue.trace().len()<=turn.before_queue().trace().len()
            && turn.before_queue().trace().take(queue.trace().len() as int)==queue.trace()
        &&& i>0 ==> turns[i-1].after_queue().trace().len()<=turn.before_queue().trace().len()
            && turn.before_queue().trace().take(turns[i-1].after_queue().trace().len() as int)==turns[i-1].after_queue().trace()
        &&& offset<=token && r::top(turn.before_queue().slots(),token)
        &&& dispatch.observes(turn.before_queue().slots()[token as int].unwrap(),values_at(turns,initial,i as nat))
        // Reusing a completion is not another attempt. An admitted retry has a
        // strictly newer identity even though its slot and inverse are equal.
        &&& i>0 ==> turns[i-1].ticket().attempt<dispatch.ticket().attempt
    }
}
proof fn queue_defined<A,R,T:?Sized,M,X>(slots:Seq<Option<Action<A,R,T,M,X>>>,heap:Map<Address,Value<T>>)
    requires trace::queued_undo(slots,heap).is_some(),
    ensures r::pending(slots,heap)==trace::queued_undo(slots,heap),
    decreases slots.len(),
{
    if slots.len()>0 {
        assert(r::undo(slots.last().unwrap(),heap)==trace::undo_action(slots.last().unwrap(),heap));
        queue_defined(slots.drop_last(),heap.insert(r::address(slots.last().unwrap()),r::original(slots.last().unwrap())));
    }
}
pub open spec fn suffix<A,R,T:?Sized,M,X>(slots:Seq<Option<Action<A,R,T,M,X>>>,offset:nat,heap:Map<Address,Value<T>>)->Option<Map<Address,Value<T>>> {
    r::pending(slots.subrange(offset as int,slots.len() as int),heap)
}
proof fn prefix<A,R,T:?Sized,M,X>(turns:Seq<Turn<A,R,T,M,X>>,queue:CleanupQueue<Action<A,R,T,M,X>>,initial:Map<Address,Value<T>>,offset:nat,n:nat)
    requires linked(turns,queue,initial,offset),n<=turns.len(),
    ensures slots_at(turns,queue.slots(),n).len()==queue.slots().len(),
        suffix(slots_at(turns,queue.slots(),n),offset,values_at(turns,initial,n))==suffix(queue.slots(),offset,initial),
    decreases n,
{
    if n>0 {
        prefix(turns,queue,initial,offset,(n-1) as nat);
        let turn=turns[n-1];let heap=values_at(turns,initial,(n-1) as nat);
        turn.progress_suffix(turn.before_queue().slots(),turn.after_queue().slots(),heap,offset);
    }
}
proof fn empty<A,R,T:?Sized,M,X>(slots:Seq<Option<Action<A,R,T,M,X>>>,heap:Map<Address,Value<T>>)
    requires forall|i:int|0<=i<slots.len() ==> (#[trigger] slots[i]).is_none(),
    ensures r::pending(slots,heap)==Some(heap),
    decreases slots.len(),
{if slots.len()>0 {empty(slots.drop_last(),heap);}}

impl<E:ScalarEffect,T:?Sized> RegisteredReport<E,T> {
    /// The starting inverse obligation is derived from this invocation's real
    /// Begin and return. Each finite cleanup turn is the checked production
    /// dispatcher with its own observed read and actual before/after slots.
    pub proof fn cleanup_progress<C,G,A,R,M,X>(&self,owner:Owner<C,G,A,R,T,M,X>,id:usize,offset:nat,turns:Seq<Turn<A,R,T,M,X>>)
        requires owner.wf(),owner.cleanup_state().live(id),self.endpoint_source(),self.retained_recovery(owner,id,offset),
            linked(turns,owner.cleanup_state().queues()[id],self.return_values(),offset),
        ensures suffix(slots_at(turns,owner.cleanup_state().queues()[id].slots(),turns.len()),offset,
            values_at(turns,self.return_values(),turns.len()))==Some(self.begin_values()),
    {
        let queue=owner.cleanup_state().queues()[id];self.recover_begin(owner,id,offset);
        queue_defined(queue.slots().subrange(offset as int,queue.slots().len() as int),self.return_values());
        prefix(turns,queue,self.return_values(),offset,turns.len());
    }
    /// When actual cleanup reads continue the proven return trajectory, each
    /// real restoration succeeds. This excludes conflicting failed reads from
    /// linked; retaining/retrying those attempts has its separate contract.
    pub proof fn cleanup_attempts_succeed<C,G,A,R,M,X>(&self,owner:Owner<C,G,A,R,T,M,X>,id:usize,offset:nat,turns:Seq<Turn<A,R,T,M,X>>)
        requires owner.wf(),owner.cleanup_state().live(id),self.endpoint_source(),self.retained_recovery(owner,id,offset),
            linked(turns,owner.cleanup_state().queues()[id],self.return_values(),offset),
        ensures forall|i:int|0<=i<turns.len() ==> (#[trigger] turns[i]).succeeded(),
    {
        let queue=owner.cleanup_state().queues()[id];self.recover_begin(owner,id,offset);
        queue_defined(queue.slots().subrange(offset as int,queue.slots().len() as int),self.return_values());
        assert forall|i:int|0<=i<turns.len() implies (#[trigger] turns[i]).succeeded() by {
            prefix(turns,queue,self.return_values(),offset,i as nat);
            let turn=turns[i];
            turn.progress_suffix(turn.before_queue().slots(),turn.after_queue().slots(),values_at(turns,self.return_values(),i as nat),offset);
        }
    }
    /// A finite, fully consumed suffix recovers Begin values. Whether the host
    /// eventually obtains such a suffix is an explicitly separate obligation.
    pub proof fn cleanup_recovers_begin<C,G,A,R,M,X>(&self,owner:Owner<C,G,A,R,T,M,X>,id:usize,offset:nat,turns:Seq<Turn<A,R,T,M,X>>)
        requires owner.wf(),owner.cleanup_state().live(id),self.endpoint_source(),self.retained_recovery(owner,id,offset),
            linked(turns,owner.cleanup_state().queues()[id],self.return_values(),offset),
            forall|i:int|offset<=i<slots_at(turns,owner.cleanup_state().queues()[id].slots(),turns.len()).len() ==>
                (#[trigger] slots_at(turns,owner.cleanup_state().queues()[id].slots(),turns.len())[i]).is_none(),
        ensures values_at(turns,self.return_values(),turns.len())==self.begin_values(),
    {
        self.cleanup_progress(owner,id,offset,turns);
        let slots=slots_at(turns,owner.cleanup_state().queues()[id].slots(),turns.len());
        empty(slots.subrange(offset as int,slots.len() as int),values_at(turns,self.return_values(),turns.len()));
    }
}
}
