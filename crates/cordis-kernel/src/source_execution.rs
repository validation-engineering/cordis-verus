//! Source checkpoints ordered with the actual accepted configuration owner.
//! The guard is checked in the same held Journal epoch as the source event.
use vstd::prelude::*;
verus! {
pub struct State {pub configuration:nat,pub index:nat,pub loaded:bool}
#[derive(Copy,Clone,PartialEq,Eq,Structural)]
pub enum Kind {Clear,Load,Save {domain:u64}}
pub struct Event {pub kind:Kind,pub accepted:super::configuration::State}
#[verifier::opaque]
pub open spec fn step(a:State,b:State,event:Event)->bool {
    b.configuration==a.configuration && b.index==a.index+1
        && b.loaded==match event.kind {Kind::Clear=>false,Kind::Load=>true,Kind::Save {..}=>a.loaded}
}
pub open spec fn guard(state:Map<nat,super::Record>,before:State,event:Event)->bool {
    !event.accepted.pending
        && state.contains_pair(before.configuration,super::Record::Configuration {state:event.accepted})
}
pub open spec fn recorded(frames:Seq<super::Frame>,n:nat,key:nat)->bool {
    super::state_at(frames,n).contains_key(key) && super::state_at(frames,n)[key] is Sources
}
pub open spec fn at(frames:Seq<super::Frame>,n:nat,key:nat)->State {super::state_at(frames,n)[key]->Sources_state}
pub proof fn edge(frames:Seq<super::Frame>,n:nat,key:nat)
    requires super::valid(frames),n<frames.len(),recorded(frames,n,key),
    ensures recorded(frames,n+1,key),
        frames[n as int].event.key==key ==> frames[n as int].event.change is Sources
            && step(at(frames,n,key),at(frames,n+1,key),frames[n as int].event.change->Sources_event)
            && at(frames,n+1,key).index==at(frames,n,key).index+1
            && guard(super::state_at(frames,n),at(frames,n,key),frames[n as int].event.change->Sources_event),
        frames[n as int].event.key!=key ==> at(frames,n+1,key)==at(frames,n,key),
{
    assert(super::step(super::state_at(frames,n),frames[n as int].state,frames[n as int].event));
    reveal(super::changes);reveal(step);
}
pub proof fn monotone(frames:Seq<super::Frame>,start:nat,end:nat,key:nat)
    requires super::valid(frames),start<=end<=frames.len(),recorded(frames,start,key),
    ensures recorded(frames,end,key),at(frames,start,key).index<=at(frames,end,key).index,
    decreases end-start,
{if start<end {monotone(frames,start,(end-1) as nat,key);edge(frames,(end-1) as nat,key);}}
/// Bound an actual source mutation by the final observed index. This trace
/// lemma is independent of typed configuration/source payloads.
pub proof fn modification_index(frames:Seq<super::Frame>,start:nat,n:nat,key:nat,latest:nat)
    requires super::valid(frames),start<frames.len(),n<frames.len(),
        frames[start as int].event.key==key,frames[start as int].event.change==super::Change::Allocate,
        frames[start as int].event.after is Sources,frames[start as int].event.after->Sources_state.index==0,
        frames[n as int].event.key==key,recorded(frames,frames.len(),key),at(frames,frames.len(),key).index==latest,
    ensures frames[n as int].event.after is Sources,frames[n as int].event.after->Sources_state.index<=latest,
{
    if n<start {
        assert(super::step(super::state_at(frames,n),frames[n as int].state,frames[n as int].event));
        assert(super::state_at(frames,n+1).contains_key(key));
        super::key_persists(frames,n+1,start,key);
        assert(super::step(super::state_at(frames,start),frames[start as int].state,frames[start as int].event));
        assert(false);
    }
    if n>start {
        assert(super::step(super::state_at(frames,start),frames[start as int].state,frames[start as int].event));
        assert(recorded(frames,start+1,key));
        monotone(frames,start+1,n,key);edge(frames,n,key);monotone(frames,n+1,frames.len(),key);
    }
}
pub proof fn unique_index(frames:Seq<super::Frame>,a:nat,b:nat,key:nat)
    requires super::valid(frames),a<frames.len(),b<frames.len(),
        frames[a as int].event.key==key,frames[b as int].event.key==key,
        frames[a as int].event.after is Sources,frames[b as int].event.after is Sources,
        frames[a as int].event.after->Sources_state.index==frames[b as int].event.after->Sources_state.index,
    ensures a==b,
{
    assert(super::step(super::state_at(frames,a),frames[a as int].state,frames[a as int].event));
    assert(super::step(super::state_at(frames,b),frames[b as int].state,frames[b as int].event));
    if a<b {monotone(frames,a+1,b,key);edge(frames,b,key);}
    if b<a {monotone(frames,b+1,a,key);edge(frames,a,key);}
}
}
