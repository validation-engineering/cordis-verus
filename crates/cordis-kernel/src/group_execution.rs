//! Live cleanup membership, separate from retained queue history. Removal and
//! sealing are guarded by the actual queue records under the same journal lock.
#[cfg(verus_keep_ghost)]
use super::{Change, Record};
use crate::action_ledger::ActionTicket;
use vstd::prelude::*;

verus! {
pub struct State {
    pub origin:Option<ActionTicket>,pub queues:Map<usize,(nat,u64)>,
    pub next:usize,pub last_domain:u64,pub sealed:bool,pub consumed_failure:bool,
}
pub enum Event {Add {id:usize,key:nat,domain:u64},Remove {id:usize},Seal,ConsumedFailure}
pub open spec fn step(a:State,b:State,event:Event)->bool {
    match event {
        Event::Add {id,key,domain}=>!a.sealed && id==a.next && a.next<usize::MAX
            && !a.queues.contains_key(id) && domain>a.last_domain
            && b==(State {queues:a.queues.insert(id,(key,domain)),next:(a.next+1) as usize,last_domain:domain,..a}),
        Event::Remove {id}=>a.queues.contains_key(id) && id<a.next && b==(State {queues:a.queues.remove(id),..a}),
        Event::Seal=>b==(State {queues:Map::empty(),sealed:true,..a}),
        Event::ConsumedFailure=>b==(State {consumed_failure:true,..a}),
    }
}
pub open spec fn present(state:Map<nat,Record>,entry:(nat,u64))->bool {
    state.contains_key(entry.0) && state[entry.0] is Cleanup && state[entry.0]->Cleanup_state.domain==entry.1
}
pub open spec fn ready(q:super::episode::CleanupState)->bool {
    q.waiting.len()==0 && q.selected.is_none() && !q.pending && q.settled && !q.issued
        && forall|i:int| 0<=i<q.occupied.len() ==> !#[trigger] q.occupied[i]
}
pub open spec fn drained(state:Map<nat,Record>,entry:(nat,u64))->bool {
    present(state,entry) && ready(state[entry.0]->Cleanup_state)
}
#[verifier::opaque]
pub open spec fn guard(state:Map<nat,Record>,before:Record,change:Change)->bool {
    match change {
        Change::Groups {event}=>before is Groups && match event {
            Event::Add {key,domain,..}=>present(state,(key,domain)),
            Event::Remove {id}=>before->Groups_state.queues.contains_key(id)
                && drained(state,before->Groups_state.queues[id]),
            Event::Seal=>forall|id:usize| #[trigger] before->Groups_state.queues.contains_key(id)
                ==> drained(state,before->Groups_state.queues[id]),
            Event::ConsumedFailure=>true,
        },
        _=>true,
    }
}
/// A removed group cannot be reintroduced by a later Add: IDs are allocated
/// above the high-water mark. Sealing keeps the live membership empty.
pub proof fn preserves_retirement(a:State,b:State,event:Event,id:usize)
    requires step(a,b,event),id<a.next,!a.queues.contains_key(id),
    ensures a.next<=b.next,!b.queues.contains_key(id),a.sealed ==> b.sealed,
{}
pub open spec fn recorded(frames:Seq<super::Frame>,n:nat,key:nat)->bool {
    super::state_at(frames,n).contains_key(key) && super::state_at(frames,n)[key] is Groups
}
pub open spec fn at(frames:Seq<super::Frame>,n:nat,key:nat)->State {super::state_at(frames,n)[key]->Groups_state}
proof fn edge(frames:Seq<super::Frame>,n:nat,key:nat,id:usize)
    requires super::valid(frames),n<frames.len(),recorded(frames,n,key),
        id<at(frames,n,key).next,!at(frames,n,key).queues.contains_key(id),
    ensures recorded(frames,n+1,key),id<at(frames,n+1,key).next,!at(frames,n+1,key).queues.contains_key(id),
{
    let event=frames[n as int].event;
    assert(super::step(super::state_at(frames,n),frames[n as int].state,event));
    if event.key==key {
        reveal(super::changes);
        assert(event.change is Groups);
        preserves_retirement(at(frames,n,key),at(frames,n+1,key),event.change->Groups_event,id);
    }
}
/// A live membership record persists, but an ID removed below its next counter
/// remains absent in every later state, including interleaved object/queue work.
pub proof fn absent_later(frames:Seq<super::Frame>,start:nat,end:nat,key:nat,id:usize)
    requires super::valid(frames),start<=end<=frames.len(),recorded(frames,start,key),
        id<at(frames,start,key).next,!at(frames,start,key).queues.contains_key(id),
    ensures recorded(frames,end,key),id<at(frames,end,key).next,!at(frames,end,key).queues.contains_key(id),
    decreases end-start,
{
    if start<end {absent_later(frames,start,(end-1) as nat,key,id);edge(frames,(end-1) as nat,key,id);}
}
proof fn removal_guard(frames:Seq<super::Frame>,index:nat,key:nat,id:usize)
    requires super::valid(frames),index<frames.len(),frames[index as int].event.key==key,
        frames[index as int].event.change==(Change::Groups {event:Event::Remove {id}}),
    ensures recorded(frames,index,key),at(frames,index,key).queues.contains_key(id),id<at(frames,index+1,key).next,
        drained(super::state_at(frames,index),at(frames,index,key).queues[id]),recorded(frames,index+1,key),
        at(frames,index+1,key).queues==at(frames,index,key).queues.remove(id),
{
    assert(super::step(super::state_at(frames,index),frames[index as int].state,frames[index as int].event));
    reveal(super::changes);reveal(guard);
}
/// Audit an actual removal commit, not a caller-supplied drain certificate.
pub proof fn checked_removal(snapshot:&super::Snapshot,index:nat,key:nat,id:usize)
    requires snapshot.certified(),index<snapshot.events().len(),
        snapshot.events()[index as int].event.key==key,
        snapshot.events()[index as int].event.change==(Change::Groups {event:Event::Remove {id}}),
    ensures recorded(snapshot.events(),index,key),at(snapshot.events(),index,key).queues.contains_key(id),
        drained(super::state_at(snapshot.events(),index),at(snapshot.events(),index,key).queues[id]),
        recorded(snapshot.events(),index+1,key),
        at(snapshot.events(),index+1,key).queues==at(snapshot.events(),index,key).queues.remove(id),
        forall|n:nat| index<n<=snapshot.events().len() ==> #[trigger] recorded(snapshot.events(),n,key)
            && !at(snapshot.events(),n,key).queues.contains_key(id),
{
    snapshot.valid_history();let frames=snapshot.events();removal_guard(frames,index,key,id);
    assert forall|n:nat| index<n<=frames.len() implies #[trigger] recorded(frames,n,key)
        && !at(frames,n,key).queues.contains_key(id) by {
        absent_later(frames,index+1,n,key,id);
    }
}
proof fn sealed_later(frames:Seq<super::Frame>,start:nat,end:nat,key:nat)
    requires super::valid(frames),start<=end<=frames.len(),recorded(frames,start,key),
        at(frames,start,key).sealed,at(frames,start,key).queues.is_empty(),
    ensures recorded(frames,end,key),at(frames,end,key).sealed,at(frames,end,key).queues.is_empty(),
    decreases end-start,
{
    if start<end {
        let n=(end-1) as nat;sealed_later(frames,start,n,key);
        let event=frames[n as int].event;
        assert(super::step(super::state_at(frames,n),frames[n as int].state,event));
        if event.key==key {reveal(super::changes);}
    }
}
proof fn seal_guard(frames:Seq<super::Frame>,index:nat,key:nat)
    requires super::valid(frames),index<frames.len(),frames[index as int].event.key==key,
        frames[index as int].event.change==(Change::Groups {event:Event::Seal}),
    ensures recorded(frames,index,key),
        forall|id:usize| #[trigger] at(frames,index,key).queues.contains_key(id)
            ==> drained(super::state_at(frames,index),at(frames,index,key).queues[id]),
        recorded(frames,index+1,key),at(frames,index+1,key).sealed,at(frames,index+1,key).queues.is_empty(),
{
    assert(super::step(super::state_at(frames,index),frames[index as int].state,frames[index as int].event));
    reveal(super::changes);reveal(guard);
}
/// Seal consumes the complete live manifest. Every listed queue is checked
/// against the same joint state; the historical queue records remain retained.
pub proof fn checked_seal(snapshot:&super::Snapshot,index:nat,key:nat)
    requires snapshot.certified(),index<snapshot.events().len(),
        snapshot.events()[index as int].event.key==key,
        snapshot.events()[index as int].event.change==(Change::Groups {event:Event::Seal}),
    ensures recorded(snapshot.events(),index,key),
        forall|id:usize| #[trigger] at(snapshot.events(),index,key).queues.contains_key(id)
            ==> drained(super::state_at(snapshot.events(),index),at(snapshot.events(),index,key).queues[id]),
        recorded(snapshot.events(),index+1,key),at(snapshot.events(),index+1,key).sealed,
        at(snapshot.events(),index+1,key).queues.is_empty(),
        forall|n:nat| index<n<=snapshot.events().len() ==> #[trigger] recorded(snapshot.events(),n,key)
            && at(snapshot.events(),n,key).sealed && at(snapshot.events(),n,key).queues.is_empty(),
{
    snapshot.valid_history();let frames=snapshot.events();seal_guard(frames,index,key);
    assert forall|n:nat| index<n<=frames.len() implies #[trigger] recorded(frames,n,key)
        && at(frames,n,key).sealed && at(frames,n,key).queues.is_empty() by {
        sealed_later(frames,index+1,n,key);
    }
}
}
