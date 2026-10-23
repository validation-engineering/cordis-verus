//! A queue that disappears from its actual membership record was checked
//! drained at a real removal or seal. This includes groups retired before Unload.
#[cfg(verus_keep_ghost)]
use super::{at, drained, recorded};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::joint::{self, Change, Frame};
use vstd::prelude::*;

verus! {
proof fn edge(frames:Seq<Frame>,n:nat,key:nat,id:usize,entry:(nat,u64))
    requires joint::valid(frames),n<frames.len(),recorded(frames,n,key),at(frames,n,key).queues.contains_pair(id,entry),
    ensures recorded(frames,n+1,key),
        at(frames,n+1,key).queues.contains_key(id) ==> at(frames,n+1,key).queues[id]==entry,
        !at(frames,n+1,key).queues.contains_key(id) ==> drained(joint::state_at(frames,n),entry)
            && frames[n as int].event.key==key
            && (frames[n as int].event.change==(Change::Groups {event:super::Event::Remove {id}})
                || frames[n as int].event.change==(Change::Groups {event:super::Event::Seal})),
{
    let event=frames[n as int].event;
    assert(joint::step(joint::state_at(frames,n),frames[n as int].state,event));
    if event.key==key {reveal(joint::changes);reveal(super::guard);}
}
/// The cut is found in the source history. No earlier drain certificate or
/// premise about successful cleanup is supplied by the caller.
pub proof fn drained_before_exit(frames:Seq<Frame>,start:nat,end:nat,key:nat,id:usize,entry:(nat,u64))->(cut:nat)
    requires joint::valid(frames),start<=end<=frames.len(),recorded(frames,start,key),at(frames,start,key).queues.contains_pair(id,entry),
        recorded(frames,end,key),!at(frames,end,key).queues.contains_key(id),
    ensures start<=cut<end,drained(joint::state_at(frames,cut),entry),recorded(frames,cut,key),
        at(frames,cut,key).queues.contains_pair(id,entry),
        frames[cut as int].event.key==key
            && (frames[cut as int].event.change==(Change::Groups {event:super::Event::Remove {id}})
                || frames[cut as int].event.change==(Change::Groups {event:super::Event::Seal})),
    decreases end-start,
{
    hide(joint::valid);hide(joint::step);assert(start<end);
    edge(frames,start,key,id,entry);
    if at(frames,start+1,key).queues.contains_key(id) {drained_before_exit(frames,start+1,end,key,id,entry)} else {start}
}
}
