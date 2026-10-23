//! Exact intermediate inverse-registration obligations from the real Journal.
//! Only a managed forward creates an entry; its actual registration consumes
//! it exactly once. Callback completion is not registration or value recovery.
#[cfg(verus_keep_ghost)]
use super::{pending_at, pending_step, Frame};
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub open spec fn settles(frames:Seq<Frame>,write:nat,at:nat)->bool {
    at<frames.len() && frames[at as int].event.settled==Some(write)
}
pub open spec fn no_settlement(frames:Seq<Frame>,write:nat,start:nat,end:nat)->bool {
    forall|at:nat|start<=at<end ==> !#[trigger] settles(frames,write,at)
}
pub open spec fn outstanding(frames:Seq<Frame>,write:nat,end:nat)->bool {
    write<end && frames[write as int].event.pending && no_settlement(frames,write,write+1,end)
}
pub proof fn retained(frames:Seq<Frame>,write:nat,start:nat,end:nat)
    requires super::valid(frames),start<=end<=frames.len(),pending_at(frames,start).contains_key(write),
        no_settlement(frames,write,start,end),
    ensures pending_at(frames,end).contains_pair(write,pending_at(frames,start)[write]),
    decreases end-start,
{
    if start<end {
        retained(frames,write,start,(end-1) as nat);
        assert(super::step(super::state_at(frames,(end-1) as nat),frames[end-1].state,frames[end-1].event));
        assert(!settles(frames,write,(end-1) as nat));
        assert(pending_step(pending_at(frames,(end-1) as nat),frames[end-1].pending,frames[end-1].event,(end-1) as nat));
        assert(write<start) by {super::pending_since(frames,write,start);}
    }
}
pub proof fn settlement_source(frames:Seq<Frame>,write:nat,at:nat)
    requires super::valid(frames),settles(frames,write,at),
    ensures write<at,frames[write as int].event.pending,super::forward(frames[write as int].event),
        frames[at as int].event.change==(super::Change::RegisterInverse {write}),
        pending_at(frames,at).contains_pair(write,frames[write as int].event.key),
        !pending_at(frames,at+1).contains_key(write),
        forall|n:nat|at<n<=frames.len() ==> !#[trigger] pending_at(frames,n).contains_key(write),
{
    assert(super::step(super::state_at(frames,at),frames[at as int].state,frames[at as int].event));
    assert(pending_step(pending_at(frames,at),frames[at as int].pending,frames[at as int].event,at));
    super::pending_since(frames,write,at);
    super::pending_absent_later(frames,write,at+1,frames.len());
}
pub proof fn unique_settlement(frames:Seq<Frame>,write:nat,a:nat,b:nat)
    requires super::valid(frames),settles(frames,write,a),settles(frames,write,b),
    ensures a==b,
{
    super::unique_settlement(frames,a,b,write);
}
pub proof fn exact(frames:Seq<Frame>,write:nat,end:nat)
    requires super::valid(frames),end<=frames.len(),
    ensures pending_at(frames,end).contains_key(write)==outstanding(frames,write,end),
        pending_at(frames,end).contains_key(write) ==> pending_at(frames,end)[write]==frames[write as int].event.key,
{
    if pending_at(frames,end).contains_key(write) {
        super::pending_since(frames,write,end);
        assert forall|at:nat|write+1<=at<end implies !#[trigger] settles(frames,write,at) by {
            if settles(frames,write,at) {settlement_source(frames,write,at);}
        }
    }
    if outstanding(frames,write,end) {
        assert(super::step(super::state_at(frames,write),frames[write as int].state,frames[write as int].event));
        assert(pending_step(pending_at(frames,write),frames[write as int].pending,frames[write as int].event,write));
        retained(frames,write,write+1,end);
    }
}
pub open spec fn kept(frames:Seq<Frame>,start:nat,end:nat,write:nat)->bool {
    pending_at(frames,start).contains_key(write) && no_settlement(frames,write,start,end)
}
pub open spec fn introduced(frames:Seq<Frame>,start:nat,end:nat,write:nat)->bool {
    start<=write && outstanding(frames,write,end)
}
pub open spec fn reconstructed(frames:Seq<Frame>,start:nat,end:nat)->Map<nat,nat> {
    Map::new(frames.map(|i:int,_:Frame|i as nat).to_set().filter(|write:nat|kept(frames,start,end,write) || introduced(frames,start,end,write)),
        |write:nat|frames[write as int].event.key)
}
pub proof fn normalize(frames:Seq<Frame>,start:nat,end:nat)
    requires super::valid(frames),start<=end<=frames.len(),
    ensures pending_at(frames,end)==reconstructed(frames,start,end),
{
    assert forall|write:nat|pending_at(frames,end).contains_key(write) implies
        reconstructed(frames,start,end).contains_pair(write,pending_at(frames,end)[write]) by {
        exact(frames,write,end);
        assert(frames.map(|i:int,_:Frame|i as nat)[write as int]==write);
        assert(frames.map(|i:int,_:Frame|i as nat).to_set().contains(write));
        if write<start {super::pending_since(frames,write,end);assert(pending_at(frames,start).contains_pair(write,frames[write as int].event.key));}
    }
    assert forall|write:nat|reconstructed(frames,start,end).contains_key(write) implies
        pending_at(frames,end).contains_pair(write,reconstructed(frames,start,end)[write]) by {
        if kept(frames,start,end,write) {retained(frames,write,start,end);super::pending_since(frames,write,start);}
        else {exact(frames,write,end);}
    }
    assert(pending_at(frames,end) =~= reconstructed(frames,start,end));
}
pub open spec fn project(values:Map<nat,nat>,scope:Set<nat>)->Map<nat,nat> {
    Map::new(values.dom().filter(|write:nat|scope.contains(values[write])),|write:nat|values[write])
}
pub proof fn complete_scope(frames:Seq<Frame>,n:nat)
    requires super::valid(frames),n<=frames.len(),
    ensures project(pending_at(frames,n),frames.map(|_:int,frame:Frame|frame.event.key).to_set())==pending_at(frames,n),
{
    hide(super::valid);hide(super::step);
    let objects=frames.map(|_:int,frame:Frame|frame.event.key).to_set();
    assert forall|write:nat|pending_at(frames,n).contains_key(write) implies objects.contains(pending_at(frames,n)[write]) by {
        super::pending_since(frames,write,n);
        assert(pending_at(frames,n).contains_pair(write,frames[write as int].event.key));
        assert(frames.map(|_:int,frame:Frame|frame.event.key)[write as int]==pending_at(frames,n)[write]);
        assert(objects.contains(pending_at(frames,n)[write]));
    }
    assert(project(pending_at(frames,n),objects) =~= pending_at(frames,n));
}
pub open spec fn balanced(frames:Seq<Frame>,start:nat,end:nat,scope:Set<nat>)->bool {
    (forall|write:nat|pending_at(frames,start).contains_key(write) && scope.contains(pending_at(frames,start)[write]) ==>
        #[trigger] no_settlement(frames,write,start,end))
    && (forall|write:nat|start<=write<end && scope.contains(frames[write as int].event.key) ==> !#[trigger] outstanding(frames,write,end))
}
pub proof fn closed_from_registrations(frames:Seq<Frame>,start:nat,end:nat,scope:Set<nat>)
    requires super::valid(frames),start<=end<=frames.len(),
        forall|write:nat|pending_at(frames,start).contains_key(write) && scope.contains(pending_at(frames,start)[write]) ==>
            #[trigger] no_settlement(frames,write,start,end),
        forall|write:nat|start<=write<end && scope.contains(frames[write as int].event.key) && frames[write as int].event.pending ==>
            exists|at:nat|write<at<end && #[trigger] settles(frames,write,at),
    ensures balanced(frames,start,end,scope),
{
    assert forall|write:nat|start<=write<end && scope.contains(frames[write as int].event.key) implies !#[trigger] outstanding(frames,write,end) by {
        if outstanding(frames,write,end) {
            let at=choose|at:nat|write<at<end && settles(frames,write,at);
            settlement_source(frames,write,at);
            assert(!settles(frames,write,at));
        }
    }
}
pub ghost enum Issue {SettledInitial {write:nat,at:nat},Outstanding {write:nat}}
pub open spec fn diagnosed(frames:Seq<Frame>,start:nat,end:nat,scope:Set<nat>,issue:Issue)->bool {
    match issue {
        Issue::SettledInitial {write,at}=>pending_at(frames,start).contains_key(write) && scope.contains(pending_at(frames,start)[write])
            && start<=at<end && settles(frames,write,at),
        Issue::Outstanding {write}=>start<=write<end && scope.contains(frames[write as int].event.key) && outstanding(frames,write,end),
    }
}
pub proof fn check(frames:Seq<Frame>,start:nat,end:nat,scope:Set<nat>)->(issue:Option<Issue>)
    requires super::valid(frames),start<=end<=frames.len(),
    ensures issue.is_none()==balanced(frames,start,end,scope),
        issue.is_none() ==> project(pending_at(frames,end),scope)==project(pending_at(frames,start),scope),
        issue.is_some() ==> diagnosed(frames,start,end,scope,issue.unwrap()),
{
    if exists|write:nat,at:nat|pending_at(frames,start).contains_key(write) && scope.contains(pending_at(frames,start)[write])
        && start<=at<end && settles(frames,write,at) {
        let (write,at)=choose|write:nat,at:nat|pending_at(frames,start).contains_key(write) && scope.contains(pending_at(frames,start)[write])
            && start<=at<end && settles(frames,write,at);
        assert(!no_settlement(frames,write,start,end));
        assert(!balanced(frames,start,end,scope));
        Some(Issue::SettledInitial {write,at})
    } else if exists|write:nat|start<=write<end && scope.contains(frames[write as int].event.key) && outstanding(frames,write,end) {
        let write=choose|write:nat|start<=write<end && scope.contains(frames[write as int].event.key) && outstanding(frames,write,end);
        assert(!balanced(frames,start,end,scope));
        Some(Issue::Outstanding {write})
    } else {
        normalize(frames,start,end);
        assert(balanced(frames,start,end,scope));
        assert forall|write:nat|project(pending_at(frames,start),scope).contains_key(write) implies
            project(pending_at(frames,end),scope).contains_pair(write,pending_at(frames,start)[write]) by {retained(frames,write,start,end);}
        assert forall|write:nat|project(pending_at(frames,end),scope).contains_key(write) implies
            project(pending_at(frames,start),scope).contains_pair(write,pending_at(frames,end)[write]) by {
            exact(frames,write,end);
            assert(write<start);super::pending_since(frames,write,end);
            assert(pending_at(frames,start).contains_pair(write,frames[write as int].event.key));
        }
        assert(project(pending_at(frames,end),scope) =~= project(pending_at(frames,start),scope));
        None
    }
}
}
