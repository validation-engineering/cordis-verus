//! Linear allocation ownership remembers the last actual commit, even when
//! two writes install equal records. No holder can silently skip a same-key
//! write while retaining this capability. All data in this module is erased.
#[cfg(verus_keep_ghost)]
use super::{state_at, step, Frame, Step};
use vstd::prelude::*;

verus! {
pub open spec fn quiet(frames:Seq<Frame>,from:nat,to:nat,key:nat)->bool {
    from<=to<=frames.len() && forall|i:int|from<=i<to ==> (#[trigger] frames[i]).event.key!=key
}
pub open spec fn latest(frames:Seq<Frame>,key:nat,at:nat)->bool {
    at<frames.len() && frames[at as int].event.key==key && quiet(frames,at+1,frames.len(),key)
}
#[verifier::opaque]
pub open spec fn frontier(heads:Map<nat,nat>,frames:Seq<Frame>)->bool {
    heads.dom()==state_at(frames,frames.len()).dom()
        && forall|key:nat|heads.contains_key(key) ==> #[trigger] latest(frames,key,heads[key])
}
#[verifier::opaque]
pub open spec fn ready(heads:Map<nat,nat>,frames:Seq<Frame>,event:Step)->bool {
    heads.dom()==state_at(frames,frames.len()).dom().insert(event.key)
        && heads.contains_pair(event.key,frames.len())
        && forall|key:nat|heads.contains_key(key) && key!=event.key ==> #[trigger] latest(frames,key,heads[key])
}
pub proof fn at(heads:Map<nat,nat>,frames:Seq<Frame>,key:nat)
    requires frontier(heads,frames),heads.contains_key(key),
    ensures latest(frames,key,heads[key]),
{reveal(frontier);}
pub proof fn empty()
    ensures frontier(Map::empty(),Seq::empty()),
{reveal(frontier);}
pub proof fn prepare(heads:Map<nat,nat>,frames:Seq<Frame>,event:Step)
    requires frontier(heads,frames),
    ensures ready(heads.insert(event.key,frames.len()),frames,event),
{reveal(frontier);reveal(ready);}
pub proof fn append(heads:Map<nat,nat>,frames:Seq<Frame>,frame:Frame)
    requires ready(heads,frames,frame.event),step(state_at(frames,frames.len()),frame.state,frame.event),
    ensures frontier(heads,frames.push(frame)),
{
    reveal(frontier);reveal(ready);
    let next=frames.push(frame);
    assert forall|key:nat|heads.contains_key(key) implies #[trigger] latest(next,key,heads[key]) by {
        if key!=frame.event.key {
            assert(latest(frames,key,heads[key]));
            assert forall|i:int|heads[key]+1<=i<next.len() implies (#[trigger] next[i]).event.key!=key by {
                if i<frames.len() {assert(frames[i].event.key!=key);}
            }
        }
    }
}
/// Complete source lists grow only at the actual owner's commits. The
/// borrowed linear frontier rules out unobserved same-allocation writes.
pub open spec fn complete(positions:Seq<nat>,frames:Seq<Frame>,key:nat)->bool {
    &&& forall|i:int|0<=i<positions.len() ==> positions[i]<frames.len() && frames[positions[i] as int].event.key==key
    &&& forall|i:int|0<=i<frames.len() && (#[trigger] frames[i]).event.key==key ==> positions.contains(i as nat)
    &&& forall|i:int,j:int|0<=i<j<positions.len() ==> #[trigger] positions[i]<#[trigger] positions[j]
}
pub proof fn extend(positions:Seq<nat>,before:Seq<Frame>,after:Seq<Frame>,key:nat)
    requires complete(positions,before,key),before.len()<=after.len(),after.take(before.len() as int)==before,quiet(after,before.len(),after.len(),key),
    ensures complete(positions,after,key),
{
    assert forall|i:int|0<=i<after.len() && (#[trigger] after[i]).event.key==key implies positions.contains(i as nat) by {
        assert(i<before.len());assert(before[i]==after[i]);
    }
}
pub proof fn commit(positions:Seq<nat>,before:Seq<Frame>,after:Seq<Frame>,key:nat)
    requires complete(positions,before,key),before.len()<after.len(),after.take(before.len() as int)==before,
        quiet(after,before.len(),(after.len()-1) as nat,key),after.last().event.key==key,
    ensures complete(positions.push((after.len()-1) as nat),after,key),
{
    let next=positions.push((after.len()-1) as nat);
    assert forall|i:int|0<=i<after.len() && (#[trigger] after[i]).event.key==key implies next.contains(i as nat) by {
        if i<before.len() {assert(before[i]==after[i]);assert(positions.contains(i as nat));let j=choose|j:int|0<=j<positions.len() && positions[j]==i;assert(next[j]==i);}
        else {assert(i==after.len()-1);assert(next[positions.len() as int]==i);}
    }
    assert forall|i:int,j:int|0<=i<j<next.len() implies #[trigger] next[i]<#[trigger] next[j] by {
        if j==positions.len() {assert(positions[i]<before.len());}
    }
}
pub proof fn allocation(frames:Seq<Frame>,key:nat)
    requires super::valid(frames),frames.len()>0,frames.last().event.key==key,frames.last().event.change==super::Change::Allocate,
    ensures complete(seq![(frames.len()-1) as nat],frames,key),
{
    let at=(frames.len()-1) as nat;
    assert(step(state_at(frames,at),frames[at as int].state,frames[at as int].event));
    assert forall|i:int|0<=i<frames.len() && (#[trigger] frames[i]).event.key==key implies seq![at].contains(i as nat) by {
        if i<at {
            assert(step(state_at(frames,i as nat),frames[i].state,frames[i].event));
            super::key_persists(frames,(i+1) as nat,at,key);assert(false);
        } else {assert(i==at);assert(seq![at][0]==i);}
    }
}

}
