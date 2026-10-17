//! Recipe versions in the same execution domain as native lifecycle and values.
//! Bodies retain their exact typed history in the native owner; this projection
//! records identity, interfaces and revisions without inventing callback meaning.
use crate::action_ledger::ActionTicket;
use crate::setup_work::WorkTicket;
use crate::Port;
use vstd::prelude::*;
verus! {
pub struct Shape {
    pub domain:u64,pub id:usize,pub parent:Option<usize>,pub anchor:Port,pub realms:Map<u64,u64>,
    pub dependencies:Seq<Port>,pub provisions:Seq<Port>,pub version:u64,
}
impl Shape {
    pub open spec fn same_identity(&self,other:Self)->bool {
        self.domain==other.domain && self.id==other.id && self.parent==other.parent && self.anchor==other.anchor
            && self.realms==other.realms && self.dependencies==other.dependencies && self.provisions==other.provisions
    }
}
pub struct State {pub native:nat,pub revision:nat,pub entries:Map<usize,Shape>}
#[allow(inconsistent_fields)]
pub enum Event {Insert {id:usize},Remove {id:usize},Replace {id:usize},Call {id:usize,version:u64,origin:ActionTicket,work:WorkTicket}}
impl Event {
    pub open spec fn actor(&self)->usize {match self {Self::Insert {id}|Self::Remove {id}|Self::Replace {id}|Self::Call {id,..}=>*id}}
}
#[verifier::opaque]
pub open spec fn step(a:State,b:State,event:Event)->bool {
    let id=event.actor();
    &&& b.native==a.native && b.revision==a.revision+1
    &&& match event {
        Event::Insert {..}=>!a.entries.contains_key(id) && b.entries.contains_key(id)
            && b.entries==a.entries.insert(id,b.entries[id]) && b.entries[id].version==0,
        Event::Remove {..}=>a.entries.contains_key(id) && b.entries==a.entries.remove(id),
        Event::Replace {..}=>a.entries.contains_key(id) && b.entries.contains_key(id)
            && b.entries==a.entries.insert(id,b.entries[id]) && b.entries[id].same_identity(a.entries[id])
            && a.entries[id].version<u64::MAX && b.entries[id].version==a.entries[id].version+1,
        Event::Call {version,..}=>a.entries.contains_key(id) && a.entries[id].version==version && b.entries==a.entries,
    }
}
pub open spec fn native_guard(state:super::native::State,event:Event)->bool {
    let id=event.actor();
    match event {
        Event::Remove {..}=>!state.control.fibers.dom().contains(id),
        Event::Call {origin,work,..}=>state.control.fibers.dom().contains(id) && state.owners.contains_key(id)
            && state.owners[id].origin==origin && state.owners[id].work_domain==work.domain_id()
            && state.control.fibers[id].phase==crate::Phase::Loading && !state.control.fibers[id].retired,
        _=>state.control.fibers.dom().contains(id),
    }
}
pub open spec fn guard(state:Map<nat,super::Record>,before:State,event:Event)->bool {
    state.contains_key(before.native) && state[before.native] is Native
        && native_guard(state[before.native]->Native_state,event)
}
pub open spec fn recorded(frames:Seq<super::Frame>,n:nat,key:nat)->bool {
    super::state_at(frames,n).contains_key(key) && super::state_at(frames,n)[key] is Recipes
}
pub open spec fn at(frames:Seq<super::Frame>,n:nat,key:nat)->State {super::state_at(frames,n)[key]->Recipes_state}
pub proof fn edge(frames:Seq<super::Frame>,n:nat,key:nat)
    requires super::valid(frames),n<frames.len(),recorded(frames,n,key),
    ensures recorded(frames,n+1,key),
        frames[n as int].event.key==key ==> frames[n as int].event.change is Recipes
            && step(at(frames,n,key),at(frames,n+1,key),frames[n as int].event.change->Recipes_event)
            && at(frames,n+1,key).revision==at(frames,n,key).revision+1
            && guard(super::state_at(frames,n),at(frames,n,key),frames[n as int].event.change->Recipes_event),
        frames[n as int].event.key!=key ==> at(frames,n+1,key)==at(frames,n,key),
{
    assert(super::step(super::state_at(frames,n),frames[n as int].state,frames[n as int].event));
    reveal(super::changes);reveal(step);
}
pub proof fn monotone(frames:Seq<super::Frame>,start:nat,end:nat,key:nat)
    requires super::valid(frames),start<=end<=frames.len(),recorded(frames,start,key),
    ensures recorded(frames,end,key),at(frames,start,key).revision<=at(frames,end,key).revision,
    decreases end-start,
{if start<end {monotone(frames,start,(end-1) as nat,key);edge(frames,(end-1) as nat,key);}}
pub proof fn unique_revision(frames:Seq<super::Frame>,a:nat,b:nat,key:nat)
    requires super::valid(frames),a<frames.len(),b<frames.len(),
        frames[a as int].event.key==key,frames[b as int].event.key==key,
        frames[a as int].event.after is Recipes,frames[b as int].event.after is Recipes,
        frames[a as int].event.after->Recipes_state.revision==frames[b as int].event.after->Recipes_state.revision,
    ensures a==b,
{
    assert(super::step(super::state_at(frames,a),frames[a as int].state,frames[a as int].event));
    assert(super::step(super::state_at(frames,b),frames[b as int].state,frames[b as int].event));
    if a<b {monotone(frames,a+1,b,key);edge(frames,b,key);}
    if b<a {monotone(frames,b+1,a,key);edge(frames,a,key);}
}
}
