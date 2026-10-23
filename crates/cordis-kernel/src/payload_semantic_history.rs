//! Typed semantic heads classified by the actual indexed Journal mutation.
//! A restored head is backed by a real Restore, despite increasing revisions.
#[cfg(verus_keep_ghost)]
use super::State;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::joint::{Change, Frame};
use vstd::prelude::*;

verus! {
pub open spec fn change<T:?Sized>(before:State<T>,after:State<T>,revision:nat,kind:Change)->bool {
    match kind {
        Change::PayloadApply=>after.head==revision && after.depth as int==before.depth as int+1,
        Change::PayloadReplace=>after.head==revision && after.depth==0,
        Change::PayloadRestore=>after.head<before.head && after.depth as int+1==before.depth as int,
        _=>false,
    }
}
pub open spec fn entry<T:?Sized>(states:Seq<State<T>>,positions:Seq<nat>,frames:Seq<Frame>,i:int)->bool {
    let state=states[i];
    &&& positions[i]<frames.len() && state.head<=i && states[state.head as int]==state
    &&& if i==0 {state.head==0 && state.depth==0 && frames[positions[i] as int].event.change==Change::Allocate}
        else {change(states[i-1],state,i as nat,frames[positions[i] as int].event.change)
            && (frames[positions[i] as int].event.change==Change::PayloadRestore ==>
                states[i-1].head>0 && state==states[states[i-1].head as int-1])}
}
#[verifier::opaque]
pub open spec fn valid<T:?Sized>(states:Seq<State<T>>,positions:Seq<nat>,frames:Seq<Frame>)->bool {
    states.len()==positions.len() && forall|i:int|0<=i<states.len() ==> #[trigger] entry(states,positions,frames,i)
}
pub proof fn initial<T:?Sized>(state:State<T>,frames:Seq<Frame>)
    requires frames.len()>0,frames.last().event.change==Change::Allocate,state.head==0,state.depth==0,
    ensures valid(seq![state],seq![(frames.len()-1) as nat],frames),
{reveal(valid);}
pub proof fn append<T:?Sized>(states:Seq<State<T>>,positions:Seq<nat>,before:Seq<Frame>,after:Seq<Frame>,state:State<T>)
    requires valid(states,positions,before),states.len()>0,before.len()<after.len(),after.take(before.len() as int)==before,
        state.head<=states.len(),state.head<states.len() ==> states[state.head as int]==state,
        change(states.last(),state,states.len(),after.last().event.change),
        after.last().event.change==Change::PayloadRestore ==> states.last().head>0 && state==states[states.last().head as int-1],
    ensures valid(states.push(state),positions.push((after.len()-1) as nat),after),
{
    hide(change);reveal(valid);
    let next=states.push(state);let indexes=positions.push((after.len()-1) as nat);
    assert forall|i:int|0<=i<next.len() implies #[trigger] entry(next,indexes,after,i) by {
        if i<states.len() {
            assert(entry(states,positions,before,i));
            assert(after[indexes[i] as int]==before[positions[i] as int]);
            assert(next[states[i].head as int]==states[states[i].head as int]);
            if i>0 && before[positions[i] as int].event.change==Change::PayloadRestore {assert(entry(states,positions,before,i-1));assert(next[states[i-1].head as int-1]==states[states[i-1].head as int-1]);}
        } else {assert(next[i-1]==states.last());assert(entry(states,positions,before,states.len() as int-1));if after.last().event.change==Change::PayloadRestore {assert(next[states.last().head as int-1]==states[states.last().head as int-1]);}}
    }
}
/// Only an actual Restore can land on an older semantic head. A repeated
/// value or depth is insufficient, and the monotone revision is not rewound.
pub proof fn restored<T:?Sized>(states:Seq<State<T>>,positions:Seq<nat>,frames:Seq<Frame>,revision:int)
    requires valid(states,positions,frames),0<=revision<states.len(),states[revision].head<revision,
    ensures frames[positions[revision] as int].event.change==Change::PayloadRestore,
{reveal(valid);assert(entry(states,positions,frames,revision));assert(revision>0);assert(change(states[revision-1],states[revision],revision as nat,frames[positions[revision] as int].event.change));}
/// The live inverse stack is reconstructed from the immutable creation
/// states. Restore must follow its actual predecessor, never an older sibling.
pub open spec fn stack<T:?Sized>(states:Seq<State<T>>,head:nat)->Seq<nat>
    decreases head,
{
    if head==0 || head>=states.len() || states[head as int].depth==0 || states[head as int-1].head>=head {Seq::empty()}
    else {stack(states,states[head as int-1].head as nat).push(head)}
}
pub proof fn stack_bounds<T:?Sized>(states:Seq<State<T>>,head:nat)
    ensures forall|i:int|0<=i<stack(states,head).len() ==> (#[trigger] stack(states,head)[i])<=head,
        forall|i:int,j:int|0<=i<j<stack(states,head).len() ==> #[trigger] stack(states,head)[i]<#[trigger] stack(states,head)[j],
    decreases head,
{
    if head>0 && head<states.len() && states[head as int].depth>0 && states[head as int-1].head<head {
        let parent=states[head as int-1].head as nat;stack_bounds(states,parent);
        let prefix=stack(states,parent);let all=stack(states,head);
        assert forall|i:int,j:int|0<=i<j<all.len() implies #[trigger] all[i]<#[trigger] all[j] by {
            if j==prefix.len() {assert(prefix[i]<=parent);}
        }
    }
}
pub proof fn transition<T:?Sized>(states:Seq<State<T>>,positions:Seq<nat>,frames:Seq<Frame>,i:int)
    requires valid(states,positions,frames),0<i<states.len(),
    ensures {
        let before=stack(states,states[i-1].head as nat);let after=stack(states,states[i].head as nat);
        match frames[positions[i] as int].event.change {
            Change::PayloadApply=>after==before.push(i as nat),
            Change::PayloadReplace=>after==Seq::<nat>::empty(),
            Change::PayloadRestore=>before.len()>0 && before.last()==states[i-1].head && after==before.drop_last(),
            _=>false,
        }
    },
{
    reveal(valid);assert(entry(states,positions,frames,i));assert(entry(states,positions,frames,i-1));
    let old_head=states[i-1].head as int;let head=states[i].head as int;
    if frames[positions[i] as int].event.change==Change::PayloadRestore {
        assert(old_head>0);assert(states[old_head]==states[i-1]);assert(entry(states,positions,frames,old_head));
        assert(entry(states,positions,frames,old_head-1));
        let parent=states[old_head-1].head as nat;
        assert(parent<old_head);assert(states[i]==states[old_head-1]);
        assert(stack(states,old_head as nat)==stack(states,parent).push(old_head as nat));
        assert(stack(states,old_head as nat).drop_last() =~= stack(states,parent));
    }
}
pub proof fn restore_origin<T:?Sized>(states:Seq<State<T>>,positions:Seq<nat>,frames:Seq<Frame>,i:int)
    requires valid(states,positions,frames),0<i<states.len(),frames[positions[i] as int].event.change==Change::PayloadRestore,
    ensures 0<states[i-1].head<i,
        frames[positions[states[i-1].head as int] as int].event.change==Change::PayloadApply,
        states[i]==states[states[i-1].head as int-1],
        states[i-1]==states[states[i-1].head as int],
{
    reveal(valid);assert(entry(states,positions,frames,i));assert(entry(states,positions,frames,i-1));
    let head=states[i-1].head as int;assert(entry(states,positions,frames,head));
    assert(states[head].depth>0);
}
pub proof fn absent_later<T:?Sized>(states:Seq<State<T>>,positions:Seq<nat>,frames:Seq<Frame>,from:int,to:int,head:nat)
    requires valid(states,positions,frames),0<=from<=to<states.len(),head<=from,
        !stack(states,states[from].head as nat).contains(head),
    ensures !stack(states,states[to].head as nat).contains(head),
    decreases to-from,
{
    if from<to {
        absent_later(states,positions,frames,from,to-1,head);transition(states,positions,frames,to);
        let before=stack(states,states[to-1].head as nat);let after=stack(states,states[to].head as nat);
        if after.contains(head) {
            let j=choose|j:int|0<=j<after.len() && after[j]==head;
            if frames[positions[to] as int].event.change==Change::PayloadApply {assert(j<before.len());assert(before[j]==head);}
            else if frames[positions[to] as int].event.change==Change::PayloadRestore {assert(before[j]==head);}
            assert(false);
        }
    }
}
/// A successful restore removes the actual creating head permanently. Fresh
/// writes use new revisions and cannot revive it, even with identical Arc data.
proof fn distinct_restore<T:?Sized>(states:Seq<State<T>>,positions:Seq<nat>,frames:Seq<Frame>,first:int,second:int)
    requires valid(states,positions,frames),0<first<second<states.len(),
        frames[positions[first] as int].event.change==Change::PayloadRestore,
        frames[positions[second] as int].event.change==Change::PayloadRestore,
        states[first-1].head==states[second-1].head,
    ensures false,
{
    {
        restore_origin(states,positions,frames,first);transition(states,positions,frames,first);transition(states,positions,frames,second);
        let head=states[first-1].head as nat;let before=stack(states,head);stack_bounds(states,head);
        assert(!stack(states,states[first].head as nat).contains(head)) by {
            let after=stack(states,states[first].head as nat);
            if after.contains(head) {let i=choose|i:int|0<=i<after.len() && after[i]==head;assert(before[i]<before.last());}
        }
        absent_later(states,positions,frames,first,second-1,head);
        assert(stack(states,states[second-1].head as nat).last()==head);
        assert(false);
    }
}

pub proof fn unique_restore<T:?Sized>(states:Seq<State<T>>,positions:Seq<nat>,frames:Seq<Frame>,first:int,second:int)
    requires valid(states,positions,frames),0<first<states.len(),0<second<states.len(),
        frames[positions[first] as int].event.change==Change::PayloadRestore,
        frames[positions[second] as int].event.change==Change::PayloadRestore,
        states[first-1].head==states[second-1].head,
    ensures first==second,
{
    if first<second {distinct_restore(states,positions,frames,first,second);}
    if second<first {distinct_restore(states,positions,frames,second,first);}
}

}
