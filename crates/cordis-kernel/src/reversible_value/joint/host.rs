//! Observable host progress in the same trajectory as native work and values.
//! An external service report is distinct from checked effect retirement.
#[cfg(verus_keep_ghost)]
use super::{Change, Record};
use crate::action_ledger::ActionTicket;
use vstd::prelude::*;

verus! {
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct EpisodeIdentity {pub origin:Option<ActionTicket>,pub work_domain:u64}
impl EpisodeIdentity {
    pub open spec fn owns<V,C,G,I>(&self,execution:&crate::execution::Execution<V,C,G,I>)->bool {
        self.origin==execution.origin() && self.work_domain==execution.work_state().domain_id()
    }
    pub fn matches<V,C,G,I>(&self,execution:&crate::execution::Execution<V,C,G,I>)->(out:bool)
        ensures out==self.owns(execution),
    {self.origin==execution.lifecycle_ticket() && self.work_domain==execution.work().domain()}
}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum Kind {Service,Effect {group:usize,domain:u64}}
pub struct State {
    pub owner:Option<nat>,pub episode:Option<EpisodeIdentity>,pub kind:Kind,pub cancelled:bool,pub initialized:bool,
    pub finished:bool,pub errors:nat,pub terminal:bool,pub child:Option<usize>,
}
pub enum Event {Cancel,Error,Terminal,Child,ServiceInitialized,ServiceFinished,EffectInitialized,EffectFinished}
#[verifier::opaque]
pub open spec fn step(a:State,b:State,event:Event)->bool {
    match event {
        Event::Cancel=>b==(State {cancelled:true,..a}),
        Event::Error=>b==(State {errors:a.errors+1,..a}),
        Event::Terminal=>a.kind==Kind::Service && b==(State {terminal:true,cancelled:true,..a}),
        Event::Child=>a.kind==Kind::Service && a.child.is_none() && b.child.is_some() && b==(State {child:b.child,..a}),
        Event::ServiceInitialized=>a.kind==Kind::Service && b==(State {initialized:true,..a}),
        Event::ServiceFinished=>a.kind==Kind::Service && !a.terminal && b==(State {finished:true,..a}),
        Event::EffectInitialized=>a.kind is Effect && b==(State {initialized:true,..a}),
        Event::EffectFinished=>a.kind is Effect && b==(State {initialized:true,finished:true,..a}),
    }
}
pub open spec fn bound(state:Map<nat,Record>,s:State)->bool {
    s.owner.is_some() && s.episode.is_some() && state.contains_key(s.owner.unwrap()) && state[s.owner.unwrap()] is Groups
        && state[s.owner.unwrap()]->Groups_state.origin==s.episode.unwrap().origin
}
#[verifier::opaque]
pub open spec fn guard(state:Map<nat,Record>,s:State,event:Event)->bool {
    match event {
        Event::EffectInitialized=>bound(state,s) && s.kind is Effect && {
            let gs=state[s.owner.unwrap()]->Groups_state;let id=s.kind->Effect_group;
            gs.queues.contains_key(id) && gs.queues[id].1==s.kind->Effect_domain
                && super::groups::present(state,gs.queues[id])
                && state[gs.queues[id].0]->Cleanup_state.settled && !state[gs.queues[id].0]->Cleanup_state.pending
        },
        Event::EffectFinished=>bound(state,s) && s.kind is Effect && {
            let gs=state[s.owner.unwrap()]->Groups_state;let id=s.kind->Effect_group;
            id<gs.next && !gs.queues.contains_key(id)
        },
        _=>true,
    }
}
proof fn completion_guard(frames:Seq<super::Frame>,index:nat,key:nat)
    requires super::valid(frames),index<frames.len(),frames[index as int].event.key==key,
        frames[index as int].event.change==(Change::Host {event:Event::EffectFinished}),
    ensures frames[index as int].event.after is Host,
        frames[index as int].event.after->Host_state.finished,
        frames[index as int].event.after->Host_state.kind is Effect,
        super::groups::recorded(frames,index,frames[index as int].event.after->Host_state.owner.unwrap()),
        frames[index as int].event.after->Host_state.kind->Effect_group
            <super::groups::at(frames,index,frames[index as int].event.after->Host_state.owner.unwrap()).next,
        !super::groups::at(frames,index,frames[index as int].event.after->Host_state.owner.unwrap()).queues
            .contains_key(frames[index as int].event.after->Host_state.kind->Effect_group),
{
    let before=super::state_at(frames,index);let event=frames[index as int].event;
    assert(super::step(before,frames[index as int].state,event));
    assert(before[key] is Host && event.after is Host
        && step(before[key]->Host_state,event.after->Host_state,Event::EffectFinished)) by {reveal(super::changes);}
    assert(guard(before,before[key]->Host_state,Event::EffectFinished));
    reveal(step);reveal(guard);
}
/// A completion commit cannot be used as evidence of success for a live group.
/// The group's absence also persists across all subsequent native/value steps.
pub proof fn checked_completion(snapshot:&super::Snapshot,index:nat,key:nat)
    requires snapshot.certified(),index<snapshot.events().len(),snapshot.events()[index as int].event.key==key,
        snapshot.events()[index as int].event.change==(Change::Host {event:Event::EffectFinished}),
    ensures snapshot.events()[index as int].event.after is Host,
        snapshot.events()[index as int].event.after->Host_state.finished,
        snapshot.events()[index as int].event.after->Host_state.kind is Effect,
        forall|n:nat| #![trigger super::groups::recorded(snapshot.events(),n,snapshot.events()[index as int].event.after->Host_state.owner.unwrap())] index<=n<=snapshot.events().len() ==> {
            let s=snapshot.events()[index as int].event.after->Host_state;
            super::groups::recorded(snapshot.events(),n,s.owner.unwrap())
                && !super::groups::at(snapshot.events(),n,s.owner.unwrap()).queues.contains_key(s.kind->Effect_group)
        },
{
    snapshot.valid_history();let frames=snapshot.events();completion_guard(frames,index,key);
    let s=frames[index as int].event.after->Host_state;
    assert forall|n:nat| index<=n<=frames.len() implies
        #[trigger] super::groups::recorded(frames,n,s.owner.unwrap())
            && !super::groups::at(frames,n,s.owner.unwrap()).queues.contains_key(s.kind->Effect_group) by {
        super::groups::absent_later(frames,index,n,s.owner.unwrap(),s.kind->Effect_group);
    }
}

/// Actual construction starts without progress, errors or a Child report.
pub open spec fn initial(state:State)->State {
    State {owner:state.owner,episode:state.episode,kind:state.kind,cancelled:false,
        initialized:false,finished:false,errors:0,terminal:false,child:None}
}
pub open spec fn origin(frames:Seq<super::Frame>,key:nat,birth:nat,state:State)->bool {
    birth<frames.len() && frames[birth as int].event.key==key
        && frames[birth as int].event.change==Change::Allocate
        && frames[birth as int].event.after==(Record::Host {state:initial(state)})
}
/// Classify each real interleaving: another member preserves this complete
/// record; this member executes one of the declared guarded Host transitions.
pub open spec fn classified(frames:Seq<super::Frame>,index:nat,key:nat)->bool {
    let event=frames[index as int].event;
    recorded(frames,index+1,key) && if event.key==key {
        event.change is Host && step(at(frames,index,key),at(frames,index+1,key),event.change->Host_event)
            && guard(super::state_at(frames,index),at(frames,index,key),event.change->Host_event)
    } else {at(frames,index+1,key)==at(frames,index,key)}
}
/// The immutable owner/kind and monotone progress of one actual host record.
/// Error count is a projection; the typed payload owner proves vector retention.
pub open spec fn progress(before:State,after:State)->bool {
    after.owner==before.owner && after.episode==before.episode && after.kind==before.kind
        && (before.cancelled ==> after.cancelled) && (before.initialized ==> after.initialized)
        && (before.finished ==> after.finished) && before.errors<=after.errors
        && (before.terminal ==> after.terminal) && (before.child.is_some() ==> after.child==before.child)
}
pub proof fn progress_step(before:State,after:State,event:Event)
    requires step(before,after,event),ensures progress(before,after),
{reveal(step);}
pub proof fn progress_transitive(first:State,middle:State,last:State)
    requires progress(first,middle),progress(middle,last),ensures progress(first,last),
{}
pub open spec fn recorded(frames:Seq<super::Frame>,at:nat,key:nat)->bool {
    super::state_at(frames,at).contains_key(key) && super::state_at(frames,at)[key] is Host
}
pub open spec fn at(frames:Seq<super::Frame>,index:nat,key:nat)->State {super::state_at(frames,index)[key]->Host_state}
pub open spec fn segment(frames:Seq<super::Frame>,start:nat,end:nat,key:nat)->bool {
    recorded(frames,end,key) && progress(at(frames,start,key),at(frames,end,key))
}
proof fn progress_edge(frames:Seq<super::Frame>,index:nat,key:nat)
    requires super::valid(frames),index<frames.len(),recorded(frames,index,key),
    ensures segment(frames,index,index+1,key),classified(frames,index,key),
{
    let event=frames[index as int].event;
    assert(super::step(super::state_at(frames,index),frames[index as int].state,event));
    if event.key==key {
        reveal(super::changes);
        assert(event.change is Host);
        progress_step(at(frames,index,key),at(frames,index+1,key),event.change->Host_event);
    }
}
/// Includes arbitrary intervening writes to values, queues, lifecycle,
/// configuration and other handles. No adjacent-event or scheduler premise.
pub proof fn progress_between(frames:Seq<super::Frame>,start:nat,end:nat,key:nat)
    requires super::valid(frames),start<=end<=frames.len(),recorded(frames,start,key),
    ensures segment(frames,start,end,key),decreases end-start,
{
    if start<end {
        let previous=(end-1) as nat;
        progress_between(frames,start,previous,key);progress_edge(frames,previous,key);
        progress_transitive(at(frames,start,key),at(frames,previous,key),at(frames,end,key));
    }
}
pub open spec fn history(frames:Seq<super::Frame>,key:nat)->bool {
    &&& forall|start:nat,end:nat| start<=end<=frames.len() && recorded(frames,start,key)
        ==> #[trigger] segment(frames,start,end,key)
    &&& forall|index:nat| index<frames.len() && recorded(frames,index,key)
        ==> #[trigger] classified(frames,index,key)
}
pub proof fn history_progress(frames:Seq<super::Frame>,key:nat)
    requires super::valid(frames),ensures history(frames,key),
{
    assert forall|start:nat,end:nat| start<=end<=frames.len() && recorded(frames,start,key)
        implies #[trigger] segment(frames,start,end,key) by {progress_between(frames,start,end,key);}
    assert forall|index:nat| index<frames.len() && recorded(frames,index,key)
        implies #[trigger] classified(frames,index,key) by {progress_edge(frames,index,key);}
}
}
