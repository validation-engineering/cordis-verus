//! Publication ownership in the common execution domain. Generic Arc values
//! remain in NativeRuntime's exact typed history; its indexed projection joins
//! that history to these same commits without inventing payload semantics.
use crate::action_ledger::ActionTicket;
use crate::lifecycle_state::native::runtime::owner::EpisodeOwner;
use crate::refinement as r;
use crate::Binding;
use vstd::prelude::*;

verus! {
pub struct Publication {
    pub origin:ActionTicket,pub work_domain:u64,pub realms:Map<u64,u64>,pub anchor:crate::Port,pub ports:Set<(u64,u64)>,
    pub bindings:Seq<Binding>,pub imports:Set<(usize,u64,u64)>,pub sources:Map<usize,ActionTicket>,
}
pub struct State {
    pub revision:nat,pub control:r::State,pub owners:Map<usize,EpisodeOwner>,pub publications:Map<usize,Publication>,
}
/// Control, owner admission/removal and publication membership commit together.
/// Restart/Retire preserve the actual publication and its captured providers.
#[verifier::opaque]
pub open spec fn step(a:State,b:State,actor:usize,rule:r::Rule)->bool {
    &&& b.revision==a.revision+1
    &&& r::step(a.control,b.control,actor,rule)
    &&& match rule {
        r::Rule::Begin=>!a.owners.contains_key(actor) && b.owners.contains_key(actor)
            && b.owners==a.owners.insert(actor,b.owners[actor]),
        r::Rule::Unload=>b.owners==a.owners.remove(actor),
        _=>b.owners==a.owners,
    }
    &&& match rule {
        r::Rule::Finish=>!a.publications.contains_key(actor) && b.publications.contains_key(actor)
            && b.publications==a.publications.insert(actor,b.publications[actor]),
        r::Rule::Unload=>b.publications==a.publications.remove(actor),
        _=>b.publications==a.publications,
    }
}
pub open spec fn recorded(frames:Seq<super::Frame>,n:nat,key:nat)->bool {
    super::state_at(frames,n).contains_key(key) && super::state_at(frames,n)[key] is Native
}
pub open spec fn at(frames:Seq<super::Frame>,n:nat,key:nat)->State {super::state_at(frames,n)[key]->Native_state}
/// An unrelated value, slot, work or cleanup event cannot change ownership.
pub proof fn edge(frames:Seq<super::Frame>,n:nat,key:nat)
    requires super::valid(frames),n<frames.len(),recorded(frames,n,key),
    ensures recorded(frames,n+1,key),
        frames[n as int].event.key==key ==> frames[n as int].event.change is Native
            && step(at(frames,n,key),at(frames,n+1,key),frames[n as int].event.change->Native_actor,frames[n as int].event.change->Native_rule)
            && at(frames,n+1,key).revision==at(frames,n,key).revision+1,
        frames[n as int].event.key!=key ==> at(frames,n+1,key)==at(frames,n,key),
{
    assert(super::step(super::state_at(frames,n),frames[n as int].state,frames[n as int].event));
    reveal(super::changes);reveal(step);
}
proof fn step_retains(a:State,b:State,actor:usize,rule:r::Rule,id:usize)
    requires step(a,b,actor,rule),a.owners.contains_key(id),a.publications.contains_key(id),
        actor!=id || rule!=r::Rule::Unload,
    ensures b.owners.contains_pair(id,a.owners[id]),b.publications.contains_pair(id,a.publications[id]),
{reveal(step);}
/// During arbitrary interleavings, ownership and published slots survive until
/// that provider's successful Unload. Failure/retry events cannot remove them.
pub proof fn retained(frames:Seq<super::Frame>,start:nat,end:nat,key:nat,id:usize)
    requires super::valid(frames),start<=end<=frames.len(),recorded(frames,start,key),
        at(frames,start,key).owners.contains_key(id),at(frames,start,key).publications.contains_key(id),
        forall|i:int| start<=i<end ==> #[trigger] frames[i].event.key!=key
            || frames[i].event.change!=(super::Change::Native {actor:id,rule:r::Rule::Unload}),
    ensures recorded(frames,end,key),at(frames,end,key).owners.contains_pair(id,at(frames,start,key).owners[id]),
        at(frames,end,key).publications.contains_pair(id,at(frames,start,key).publications[id]),
    decreases end-start,
{
    if start<end {
        retained(frames,start,(end-1) as nat,key,id);edge(frames,(end-1) as nat,key);
        assert(frames[end-1].event.key!=key || frames[end-1].event.change!=(super::Change::Native {actor:id,rule:r::Rule::Unload}));
        if frames[end-1].event.key==key {
            step_retains(at(frames,(end-1) as nat,key),at(frames,end,key),
                frames[end-1].event.change->Native_actor,frames[end-1].event.change->Native_rule,id);
        }
    }
}
/// Native revisions cannot skip backwards, even among other owners' commits.
pub proof fn monotone(frames:Seq<super::Frame>,start:nat,end:nat,key:nat)
    requires super::valid(frames),start<=end<=frames.len(),recorded(frames,start,key),
    ensures recorded(frames,end,key),at(frames,start,key).revision<=at(frames,end,key).revision,
    decreases end-start,
{
    if start<end {monotone(frames,start,(end-1) as nat,key);edge(frames,(end-1) as nat,key);}
}
/// A native revision identifies one real commit, even across interleavings.
pub proof fn unique_revision(frames:Seq<super::Frame>,a:nat,b:nat,key:nat)
    requires super::valid(frames),a<frames.len(),b<frames.len(),
        frames[a as int].event.key==key,frames[b as int].event.key==key,
        frames[a as int].event.after is Native,frames[b as int].event.after is Native,
        frames[a as int].event.after->Native_state.revision==frames[b as int].event.after->Native_state.revision,
    ensures a==b,
{
    assert(super::step(super::state_at(frames,a),frames[a as int].state,frames[a as int].event));
    assert(super::step(super::state_at(frames,b),frames[b as int].state,frames[b as int].event));
    if a<b {monotone(frames,a+1,b,key);edge(frames,b,key);}
    if b<a {monotone(frames,b+1,a,key);edge(frames,a,key);}
}
/// Equal endpoint revisions exclude an omitted native mutation, including a
/// stuttering control rule. All intervening operations belong to other owners.
pub proof fn unchanged_interval(frames:Seq<super::Frame>,start:nat,end:nat,key:nat)
    requires super::valid(frames),start<=end<=frames.len(),recorded(frames,start,key),recorded(frames,end,key),
        at(frames,start,key).revision==at(frames,end,key).revision,
    ensures at(frames,start,key)==at(frames,end,key),
        forall|i:int| start<=i<end ==> #[trigger] frames[i].event.key!=key,
{
    assert forall|i:int| start<=i<end implies #[trigger] frames[i].event.key!=key by {
        monotone(frames,start,i as nat,key);edge(frames,i as nat,key);monotone(frames,(i+1) as nat,end,key);
    }
    unchanged_framing(frames,start,end,key);
}
proof fn unchanged_framing(frames:Seq<super::Frame>,start:nat,end:nat,key:nat)
    requires super::valid(frames),start<=end<=frames.len(),recorded(frames,start,key),
        forall|i:int| start<=i<end ==> #[trigger] frames[i].event.key!=key,
    ensures recorded(frames,end,key),at(frames,start,key)==at(frames,end,key),
    decreases end-start,
{if start<end {unchanged_framing(frames,start,(end-1) as nat,key);edge(frames,(end-1) as nat,key);}}
}
