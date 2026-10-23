//! Complete source coverage is a census of actual changing Journal frames.
//! It derives every read gap and the terminal tail; neither is caller input.
#[cfg(verus_keep_ghost)]
use super::super::{endpoint, Event};
#[cfg(verus_keep_ghost)]
use super::link;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{joint, managed::recovery, service_composition::Address};
use vstd::prelude::*;

verus! {
/// Ignore real no-op rejections, but never erase a change merely because the
/// visible user value is equal. Typed revisions and scalar depth are retained.
pub open spec fn changes_at(frames:Seq<joint::Frame>,at:int,key:nat)->bool {
    0<=at<frames.len() && frames[at].event.key==key
        && !joint::state_at(frames,at as nat).contains_pair(key,frames[at].event.after)
}
pub open spec fn names<A,R,T:?Sized,M,X>(event:Event<A,R,T,M,X>,journal:joint::Journal,key:nat,at:int)->bool {
    event.source() && event.inverse().address==(Address {journal,key})
        && (event.forward() || event.succeeded()) && event.read_cut()<=at
        && event.checkpoint().journal()==journal && event.checkpoint().at()==at
}
/// The census is over the real shared Journal, not just the supplied events.
/// An omitted conflicting operation therefore leaves a concrete uncovered index.
pub open spec fn complete<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,start:joint::Receipt,end:joint::Receipt,keys:Set<Address>)->bool {
    &&& start.wf() && end.wf() && end.covers(&start)
    &&& forall|key:Address|keys.contains(key) ==> key.journal==end.journal()
    &&& forall|i:int|0<=i<events.len() ==> end.covers(&(#[trigger] events[i]).checkpoint())
    &&& forall|key:Address,at:int|keys.contains(key) && start.events().len()<=at<end.events().len()
        && #[trigger] changes_at(end.events(),at,key.key) ==>
            exists|i:int|0<=i<events.len() && #[trigger] names(events[i],end.journal(),key.key,at)
}
/// A missing source is an actual changed frame, including its allocation and
/// full record. This witness can drive proof clients and omission controls.
pub proof fn missing<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,start:joint::Receipt,end:joint::Receipt,keys:Set<Address>)->(out:(Address,int))
    requires start.wf(),end.wf(),end.covers(&start),
        forall|key:Address|keys.contains(key) ==> key.journal==end.journal(),
        forall|i:int|0<=i<events.len() ==> end.covers(&(#[trigger] events[i]).checkpoint()),
        !complete(events,start,end,keys),
    ensures keys.contains(out.0),start.events().len()<=out.1<end.events().len(),changes_at(end.events(),out.1,out.0.key),
        forall|i:int|0<=i<events.len() ==> !#[trigger] names(events[i],end.journal(),out.0.key,out.1),
{
    choose|key:Address,at:int|keys.contains(key) && start.events().len()<=at<end.events().len()
        && changes_at(end.events(),at,key.key)
        && !(exists|i:int|0<=i<events.len() && #[trigger] names(events[i],end.journal(),key.key,at))
}
proof fn latest_covers<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,key:Address,n:nat)
    requires n<=events.len(),
    ensures endpoint::latest(events,key,n).is_some() ==> endpoint::latest(events,key,n).unwrap()<n
        && events[endpoint::latest(events,key,n).unwrap() as int].inverse().address==key,
        forall|j:int|0<=j<n && (#[trigger] events[j]).inverse().address==key ==>
            endpoint::latest(events,key,n).is_some() && j<=endpoint::latest(events,key,n).unwrap(),
    decreases n,
{
    if n>0 {latest_covers(events,key,(n-1) as nat);}
}
/// One proof handles both the interval before a read and the final suffix.
proof fn quiet_interval<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,start:joint::Receipt,end:joint::Receipt,keys:Set<Address>,key:Address,n:nat,until:nat)
    requires link::ordered(events,start),complete(events,start,end,keys),keys.contains(key),n<=events.len(),
        start.events().len()<=until<=end.events().len(),
        n<events.len() ==> until==events[n as int].read_cut(),
        n==events.len() ==> until==end.events().len(),
    ensures recovery::quiet(end.events(),match endpoint::latest(events,key,n) {Some(j)=>events[j as int].checkpoint().events().len(),None=>start.events().len()},until,key.key),
{
    hide(joint::valid);hide(joint::step);
    latest_covers(events,key,n);
    if n<events.len() {events[n as int].facts();}
    let earlier=endpoint::latest(events,key,n);
    let from=match earlier {Some(j)=>events[j as int].checkpoint().events().len(),None=>start.events().len()};
    if let Some(j)=earlier {assert(from<=until);}
    assert forall|at:int|from<=at<until implies {
        let e=#[trigger] end.events()[at].event;
        e.key!=key.key || joint::state_at(end.events(),at as nat).contains_pair(key.key,e.after)
    } by {
        if changes_at(end.events(),at,key.key) {
            assert(start.events().len()<=from);
            let j=choose|j:int|0<=j<events.len() && #[trigger] names(events[j],end.journal(),key.key,at);
            let event=events[j];
            if j>=n {
                assert(n<events.len());
                if j==n {assert(until==event.read_cut());}
                else {assert(events[n as int].checkpoint().events().len()<=event.read_cut());}
                assert(until<=at);
            } else {
                assert(earlier.is_some());let last=earlier.unwrap();
                assert(j<=last);
                if j<last {assert(event.checkpoint().events().len()<=events[last as int].read_cut());}
                assert(at<from);
            }
            assert(false);
        }
    }
}
pub proof fn gaps_from_census<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,start:joint::Receipt,end:joint::Receipt,keys:Set<Address>)
    requires link::ordered(events,start),complete(events,start,end,keys),
    ensures link::gaps(events,start,keys),
{
    hide(joint::valid);hide(joint::step);
    assert forall|i:int|0<=i<events.len() && keys.contains((#[trigger] events[i]).inverse().address) implies {
        let event=events[i];let earlier=endpoint::latest(events,event.inverse().address,i as nat);
        recovery::quiet(event.checkpoint().events(),match earlier {Some(j)=>events[j as int].checkpoint().events().len(),None=>start.events().len()},event.read_cut(),event.inverse().address.key)
    } by {
        let event=events[i];event.facts();
        quiet_interval(events,start,end,keys,event.inverse().address,i as nat,event.read_cut());
        let from=match endpoint::latest(events,event.inverse().address,i as nat) {Some(j)=>events[j as int].checkpoint().events().len(),None=>start.events().len()};
        assert forall|at:int|from<=at<event.read_cut() implies {
            let e=#[trigger] event.checkpoint().events()[at].event;
            e.key!=event.inverse().address.key || joint::state_at(event.checkpoint().events(),at as nat).contains_pair(event.inverse().address.key,e.after)
        } by {
            assert(end.events()[at]==event.checkpoint().events()[at]);
            assert(joint::state_at(end.events(),at as nat)==joint::state_at(event.checkpoint().events(),at as nat));
        }
    }
}
pub proof fn tails_from_census<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,start:joint::Receipt,end:joint::Receipt,keys:Set<Address>)
    requires link::ordered(events,start),complete(events,start,end,keys),
    ensures forall|key:Address|keys.contains(key) ==> recovery::quiet(end.events(),
        match endpoint::latest(events,key,events.len()) {Some(j)=>events[j as int].checkpoint().events().len(),None=>start.events().len()},end.events().len(),key.key),
{
    assert forall|key:Address|keys.contains(key) implies recovery::quiet(end.events(),
        match endpoint::latest(events,key,events.len()) {Some(j)=>events[j as int].checkpoint().events().len(),None=>start.events().len()},end.events().len(),key.key) by {
        quiet_interval(events,start,end,keys,key,events.len(),end.events().len());
    }
}
/// Unrelated native/queue/registration activity and rejected value calls may
/// advance the Journal. Only new actual changes need additional producers.
pub proof fn extend<A,R,T:?Sized,M,X>(events:Seq<Event<A,R,T,M,X>>,suffix:Seq<Event<A,R,T,M,X>>,start:joint::Receipt,middle:joint::Receipt,end:joint::Receipt,keys:Set<Address>)
    requires complete(events,start,middle,keys),end.wf(),end.covers(&middle),
        forall|i:int|0<=i<suffix.len() ==> end.covers(&(#[trigger] suffix[i]).checkpoint()),
        forall|key:Address,at:int|keys.contains(key) && middle.events().len()<=at<end.events().len()
            && #[trigger] changes_at(end.events(),at,key.key) ==>
                exists|i:int|0<=i<suffix.len() && #[trigger] names(suffix[i],end.journal(),key.key,at),
    ensures complete(events+suffix,start,end,keys),
{
    end.cover_through(&middle,&start);
    assert forall|i:int|0<=i<(events+suffix).len() implies end.covers(&(#[trigger] (events+suffix)[i]).checkpoint()) by {
        if i<events.len() {end.cover_through(&middle,&events[i].checkpoint());}
    }
    assert forall|key:Address,at:int|keys.contains(key) && start.events().len()<=at<end.events().len()
        && #[trigger] changes_at(end.events(),at,key.key) implies
            exists|i:int|0<=i<(events+suffix).len() && #[trigger] names((events+suffix)[i],end.journal(),key.key,at) by {
        if at<middle.events().len() {
            assert(changes_at(middle.events(),at,key.key));
            let i=choose|i:int|0<=i<events.len() && #[trigger] names(events[i],middle.journal(),key.key,at);
            assert((events+suffix)[i]==events[i]);
        } else {
            let i=choose|i:int|0<=i<suffix.len() && #[trigger] names(suffix[i],end.journal(),key.key,at);
            assert((events+suffix)[events.len()+i]==suffix[i]);
        }
    }
}
}
