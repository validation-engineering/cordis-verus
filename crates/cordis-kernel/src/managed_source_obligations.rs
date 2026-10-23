//! Derive outstanding-inverse membership from actual source origins and
//! absence of duplicate successful observations. No inverse result is assumed.
#[cfg(verus_keep_ghost)]
use super::super::{contains, obligations::Inverse, outstanding, slot_of, Event};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::service_composition::Address;
use vstd::prelude::*;

verus! {
pub open spec fn created<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,initial:Seq<Option<Inverse<T>>>,inverse:Inverse<T>,n:nat)->bool {
    contains(initial,inverse) || exists|i:int|0<=i<n && (#[trigger] events[i]).forward() && events[i].inverse()==inverse
}
pub open spec fn unconsumed<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,inverse:Inverse<T>,n:nat)->bool {
    forall|i:int|0<=i<n ==> !(#[trigger] events[i]).forward() && events[i].succeeded() ==> events[i].inverse()!=inverse
}
/// Every successful restore names a retained or observed creating write, and
/// is observed only once. These are guards on source identities, not on undo.
pub open spec fn admitted<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,initial:Seq<Option<Inverse<T>>>,keys:Set<Address>)->bool {
    forall|i:int|0<=i<events.len() && keys.contains((#[trigger] events[i]).inverse().address) && !events[i].forward() && events[i].succeeded() ==>
        created(events,initial,events[i].inverse(),i as nat) && unconsumed(events,events[i].inverse(),i as nat)
}
proof fn preserve<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,initial:Seq<Option<Inverse<T>>>,keys:Set<Address>,n:nat)
    requires n<=events.len(),admitted(events,initial,keys),
    ensures forall|inverse:Inverse<T>|keys.contains(inverse.address) && created(events,initial,inverse,n) && unconsumed(events,inverse,n) ==>
            #[trigger] contains(outstanding(events,initial,keys,n),inverse),
        forall|i:int|0<=i<n && keys.contains((#[trigger] events[i]).inverse().address) && !events[i].forward() && events[i].succeeded() ==>
            contains(outstanding(events,initial,keys,i as nat),events[i].inverse()),
    decreases n,
{
    if n>0 {
        let m=(n-1) as nat;preserve(events,initial,keys,m);let event=events[m as int];let prior=outstanding(events,initial,keys,m);
        if keys.contains(event.inverse().address) && !event.forward() && event.succeeded() {
            assert(created(events,initial,event.inverse(),m));assert(unconsumed(events,event.inverse(),m));
            assert(contains(prior,event.inverse()));
        }
        assert forall|inverse:Inverse<T>|keys.contains(inverse.address) && created(events,initial,inverse,n) && unconsumed(events,inverse,n) implies
            #[trigger] contains(outstanding(events,initial,keys,n),inverse) by {
            if keys.contains(event.inverse().address) && event.forward() && event.inverse()==inverse {
                assert(outstanding(events,initial,keys,n)[prior.len() as int]==Some(inverse));
            } else {
                assert(created(events,initial,inverse,m)) by {
                    if !contains(initial,inverse) {
                        let i=choose|i:int|0<=i<n && (#[trigger] events[i]).forward() && events[i].inverse()==inverse;
                        assert(i<m);
                    }
                }
                assert(unconsumed(events,inverse,m));assert(contains(prior,inverse));let i=slot_of(prior,inverse);
                assert(0<=i<prior.len() && prior[i]==Some(inverse));
                if keys.contains(event.inverse().address) && !event.forward() && event.succeeded() {
                    let removed=slot_of(prior,event.inverse());
                    assert(0<=removed<prior.len() && prior[removed]==Some(event.inverse()));
                    assert(event.inverse()!=inverse);assert(i!=removed);
                }
                assert(outstanding(events,initial,keys,n)[i]==Some(inverse));
            }
        }
        assert forall|i:int|0<=i<n && keys.contains((#[trigger] events[i]).inverse().address) && !events[i].forward() && events[i].succeeded() implies
            contains(outstanding(events,initial,keys,i as nat),events[i].inverse()) by {if i==m {assert(contains(prior,event.inverse()));}}
    }
}
pub proof fn available<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,initial:Seq<Option<Inverse<T>>>,keys:Set<Address>)
    requires admitted(events,initial,keys),
    ensures forall|i:int|0<=i<events.len() && keys.contains((#[trigger] events[i]).inverse().address) && !events[i].forward() && events[i].succeeded() ==>
        contains(outstanding(events,initial,keys,i as nat),events[i].inverse()),
{preserve(events,initial,keys,events.len());}
}
