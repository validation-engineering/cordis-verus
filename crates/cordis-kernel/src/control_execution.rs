//! Actual polling failures and restart intent, joined to native lifecycle.
use crate::action_ledger::ActionTicket;
use vstd::prelude::*;
verus! {
pub struct State {
    pub native:nat,pub owner:usize,pub episode:Option<ActionTicket>,pub work_domain:u64,
    pub groups:Option<nat>,pub failed:bool,pub cleanup_failure:bool,pub restart:bool,
}
pub enum Event {SetupFailure,CleanupFailure,Restart {running:bool},Begin {episode:ActionTicket,work_domain:u64,groups:nat},Retry {ticket:ActionTicket},Release}
#[verifier::opaque]
pub open spec fn step(a:State,b:State,event:Event)->bool {
    match event {
        Event::SetupFailure=>b==(State {failed:true,..a}),
        Event::CleanupFailure=>b==(State {cleanup_failure:true,..a}),
        Event::Restart {running}=>b==(State {failed:false,restart:running,..a}),
        Event::Begin {episode,work_domain,groups}=>a.episode.is_none() && !a.failed && !a.cleanup_failure && episode.id==a.owner
            && b==(State {episode:Some(episode),work_domain,groups:Some(groups),cleanup_failure:false,..a}),
        Event::Retry {ticket}=>a.episode.is_some() && a.cleanup_failure && ticket.id==a.owner
            && b==(State {cleanup_failure:false,..a}),
        Event::Release=>a.episode.is_some() && b==(State {episode:None,groups:None,restart:false,..a}),
    }
}
#[verifier::opaque]
pub open spec fn guard(records:Map<nat,super::Record>,s:State,event:Event)->bool {
    match event {
        Event::Restart {running}=>records.contains_key(s.native) && records[s.native] is Native && {
            let n=records[s.native]->Native_state;
            crate::refinement::registered(n.control,s.owner) && !n.control.fibers[s.owner].retired
                && running==(n.control.fibers[s.owner].phase!=crate::Phase::Inactive)
        },
        Event::Begin {episode,work_domain,groups}=>records.contains_key(s.native) && records[s.native] is Native && {
            let n=records[s.native]->Native_state;
            n.owners.contains_key(s.owner) && n.owners[s.owner].origin==episode && n.owners[s.owner].work_domain==work_domain
                && records.contains_key(groups) && records[groups] is Groups && records[groups]->Groups_state.origin==Some(episode)
        },
        Event::Release=>records.contains_key(s.native) && records[s.native] is Native
            && !records[s.native]->Native_state.owners.contains_key(s.owner),
        _=>true,
    }
}
/// Neither failure reporting nor a restart request claims that cleanup ran.
pub proof fn failure_retains_episode(a:State,b:State,event:Event)
    requires step(a,b,event),event==Event::SetupFailure || event==Event::CleanupFailure || event is Restart,
    ensures b.episode==a.episode,b.groups==a.groups,b.work_domain==a.work_domain,
        event is Restart ==> b.cleanup_failure==a.cleanup_failure,
{reveal(step);}
/// A Begin observation names both the real native owner and the actual cleanup
/// membership in that same trajectory, rather than a reconstructed host label.
pub proof fn begin_binds_actual_members(snapshot:&super::Snapshot,index:nat)
    requires snapshot.certified(),index<snapshot.events().len(),
        snapshot.events()[index as int].event.change is Control,
        snapshot.events()[index as int].event.change->Control_event is Begin,
    ensures {
        let frame=snapshot.events()[index as int];let state=frame.event.after->Control_state;
        let before=super::state_at(snapshot.events(),index);
        frame.event.after is Control && state.episode.is_some() && state.groups.is_some()
            && before.contains_key(state.native) && before[state.native] is Native
            && before[state.native]->Native_state.owners.contains_key(state.owner)
            && before[state.native]->Native_state.owners[state.owner].origin==state.episode.unwrap()
            && before[state.native]->Native_state.owners[state.owner].work_domain==state.work_domain
            && before.contains_key(state.groups.unwrap()) && before[state.groups.unwrap()] is Groups
            && before[state.groups.unwrap()]->Groups_state.origin==state.episode
    },
{
    snapshot.valid_history();let frame=snapshot.events()[index as int];
    assert(super::step(super::state_at(snapshot.events(),index),frame.state,frame.event));
    reveal(super::changes);reveal(step);reveal(guard);
}

}
