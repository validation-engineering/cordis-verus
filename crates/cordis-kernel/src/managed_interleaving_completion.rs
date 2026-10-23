//! Completion is checked from actual later successful restore events; callers
//! need not assert that the constructed inverse word is empty.
#[cfg(verus_keep_ghost)]
use super::{contains, linked, obligations, outstanding, prefix, slot_of, values, Event};
use crate::reversible_value::{effect::ScalarEffect, managed::root::RegisteredReport};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{
    joint,
    managed::{semantics::Value, Owner},
    service_composition::Address,
};
use vstd::prelude::*;

verus! {
pub open spec fn restores<A,R,T:?Sized,M,X>(event:Event<A,R,T,M,X>,inverse:obligations::Inverse<T>)->bool {
    !event.forward() && event.succeeded() && event.inverse()==inverse
}
pub open spec fn later<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,inverse:obligations::Inverse<T>,cut:nat)->bool {
    exists|i:int|cut<=i<events.len() && #[trigger] restores(events[i],inverse)
}
pub open spec fn foreign_settled<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,keys:Set<Address>)->bool {
    forall|i:int|0<=i<events.len() && (#[trigger] events[i]).forward() && keys.contains(events[i].inverse().address) ==>
        later(events,events[i].inverse(),(i+1) as nat)
}
/// This is a property of a finite emitted history, not a prediction that a
/// scheduler or an interfering plugin will eventually perform restoration.
pub open spec fn settled<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,initial:Seq<Option<obligations::Inverse<T>>>,keys:Set<Address>)->bool {
    (forall|i:int|0<=i<initial.len() && (#[trigger] initial[i]).is_some() ==> later(events,initial[i].unwrap(),0))
        && foreign_settled(events,keys)
}
proof fn pending_has_later<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,start:joint::Receipt,heap:Map<Address,Value<T>>,initial:Seq<Option<obligations::Inverse<T>>>,n:nat)
    requires linked(events,start,heap,initial),obligations::valid(initial),obligations::recover(initial,heap).is_some(),
        settled(events,initial,heap.dom()),n<=events.len(),
    ensures forall|i:int|0<=i<outstanding(events,initial,heap.dom(),n).len() && (#[trigger] outstanding(events,initial,heap.dom(),n)[i]).is_some() ==>
        later(events,outstanding(events,initial,heap.dom(),n)[i].unwrap(),n),
    decreases n,
{
    if n>0 {
        pending_has_later(events,start,heap,initial,(n-1) as nat);
        prefix(events,start,heap,initial,(n-1) as nat);prefix(events,start,heap,initial,n);
        let event=events[n-1];event.facts();let inv=event.inverse();let keys=heap.dom();
        let before=outstanding(events,initial,keys,(n-1) as nat);let after=outstanding(events,initial,keys,n);
        let previous=values(events,heap,(n-1) as nat);let current=values(events,heap,n);
        if keys.contains(inv.address) && !event.forward() && event.succeeded() {
            assert(contains(before,inv));let selected=slot_of(before,inv);
            assert(before[selected]==Some(inv));assert(inv.undo(previous).is_some());
            obligations::consume(before,previous,selected);
        }
        assert forall|i:int|0<=i<after.len() && (#[trigger] after[i]).is_some() implies later(events,after[i].unwrap(),n) by {
            let inverse=after[i].unwrap();
            obligations::depth_bound(after,current,i);
            assert(keys.contains(inverse.address));
            if keys.contains(inv.address) && event.forward() && i==before.len() {
                assert(later(events,inverse,n));
            } else {
                assert(i<before.len() && before[i]==after[i]);
                assert(later(events,inverse,(n-1) as nat));
                let j=choose|j:int|n-1<=j<events.len() && #[trigger] restores(events[j],inverse);
                if j==n-1 {assert(!event.forward() && event.succeeded() && inv==inverse);assert(after[i]!=Some(inv));}
                assert(n<=j<events.len());
            }
        }
    }
}
pub proof fn drained<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,start:joint::Receipt,heap:Map<Address,Value<T>>,initial:Seq<Option<obligations::Inverse<T>>>)
    requires linked(events,start,heap,initial),obligations::valid(initial),obligations::recover(initial,heap).is_some(),
        settled(events,initial,heap.dom()),
    ensures forall|i:int|0<=i<outstanding(events,initial,heap.dom(),events.len()).len() ==>
        (#[trigger] outstanding(events,initial,heap.dom(),events.len())[i]).is_none(),
{
    pending_has_later(events,start,heap,initial,events.len());
}
impl<E:ScalarEffect,T:?Sized> RegisteredReport<E,T> {
    pub proof fn settled_recovers_begin<C,G,A,R,M,X>(&self,owner:Owner<C,G,A,R,T,M,X>,id:usize,offset:nat,events:Seq<Event<A,R,T,M,X>>)
        requires owner.wf(),owner.cleanup_state().live(id),self.endpoint_source(),self.retained_recovery(owner,id,offset),
            self.result->Ok_0.recovery_history(),super::super::retained(self.result->Ok_0.steps@,owner,id,offset),
            linked(events,self.completion(),self.return_values(),self.obligations(owner,id,offset)),
            settled(events,self.obligations(owner,id,offset),self.return_values().dom()),
        ensures values(events,self.return_values(),events.len())==self.begin_values(),
    {
        self.initial(owner,id,offset);
        drained(events,self.completion(),self.return_values(),self.obligations(owner,id,offset));
        self.interleaved_recovers_begin(owner,id,offset,events);
    }
}
}
