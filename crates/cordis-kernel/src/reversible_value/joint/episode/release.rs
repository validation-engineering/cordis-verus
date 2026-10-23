//! Draining a previously occupied slot requires an actual non-failed Complete.
//! Drained callbacks remain distinct from successful managed restoration.
#[cfg(verus_keep_ghost)]
use super::{cleanup_step, interval, CleanupChange, CleanupState};
#[cfg(verus_keep_ghost)]
use crate::{cleanup_journal::RestoreOutcome, reversible_value::joint};
use vstd::prelude::*;

verus! {
/// Pop moves an inverse out of the Vec but leaves the selected ticket live.
/// A failed retained or consumed attempt also remains selected until resolved.
pub open spec fn pending(state:CleanupState,token:usize)->bool {
    token<state.occupied.len() && (state.occupied[token as int]
        || state.selected.is_some() && state.selected.unwrap().token==token)
}
pub open spec fn completes(event:joint::Step,key:nat,token:usize)->bool {
    event.key==key && match event.change {
        joint::Change::Cleanup {event:CleanupChange::Complete {ticket,outcome,retained}}=>ticket.token==token && outcome!=RestoreOutcome::Failed && !retained,
        _=>false,
    }
}
proof fn step(a:CleanupState,b:CleanupState,event:CleanupChange,token:usize)
    requires cleanup_step(a,b,event),pending(a,token),!pending(b,token),
    ensures match event {CleanupChange::Complete {ticket,outcome,retained}=>ticket.token==token && outcome!=RestoreOutcome::Failed && !retained,_=>false},
{
    match event {
        CleanupChange::Register=>{},CleanupChange::Land=>{},CleanupChange::Pop {..}=>{},
        CleanupChange::Complete {..}=>{},CleanupChange::Retry {..}=>{},
        CleanupChange::Admit {..}=>{},CleanupChange::End=>{},CleanupChange::Cancel=>{},
    }
}
proof fn edge(frames:Seq<joint::Frame>,n:nat,key:nat,token:usize)
    requires joint::valid(frames),n<frames.len(),interval::present(frames,n,key),pending(interval::at(frames,n,key),token),
    ensures interval::present(frames,n+1,key),interval::at(frames,n,key).occupied.len()<=interval::at(frames,n+1,key).occupied.len(),!pending(interval::at(frames,n+1,key),token) ==> completes(frames[n as int].event,key,token)
            && frames[n as int].event.after is Cleanup && token<frames[n as int].event.after->Cleanup_state.occupied.len(),
{
    let event=frames[n as int].event;
    assert(joint::step(joint::state_at(frames,n),frames[n as int].state,event));
    if event.key==key {
        reveal(joint::changes);
        if !pending(interval::at(frames,n+1,key),token) {
            if event.change is Cleanup {step(interval::at(frames,n,key),interval::at(frames,n+1,key),event.change->Cleanup_event,token);}
            else {step(interval::at(frames,n,key),interval::at(frames,n+1,key),CleanupChange::Register,token);}
        }
    }
}
pub proof fn completed_before_drain(frames:Seq<joint::Frame>,start:nat,end:nat,key:nat,token:usize)->(cut:nat)
    requires joint::valid(frames),start<=end<=frames.len(),interval::present(frames,start,key),pending(interval::at(frames,start,key),token),
        interval::present(frames,end,key),!pending(interval::at(frames,end,key),token),
    ensures start<=cut<end,completes(frames[cut as int].event,key,token),
        interval::present(frames,cut,key),pending(interval::at(frames,cut,key),token),
        interval::present(frames,cut+1,key),!pending(interval::at(frames,cut+1,key),token),
        frames[cut as int].event.after is Cleanup,token<frames[cut as int].event.after->Cleanup_state.occupied.len(),
    decreases end-start,
{
    hide(joint::valid);hide(joint::step);assert(start<end);
    edge(frames,start,key,token);
    if pending(interval::at(frames,start+1,key),token) {completed_before_drain(frames,start+1,end,key,token)} else {start}
}
proof fn spent_step(a:CleanupState,b:CleanupState,event:CleanupChange,token:usize)
    requires cleanup_step(a,b,event),token<a.occupied.len(),!pending(a,token),
    ensures token<b.occupied.len(),!pending(b,token),
{match event {CleanupChange::Pop {..}=>{},CleanupChange::Complete {..}=>{},CleanupChange::Retry {..}=>{},_=>{}}}
proof fn spent_edge(frames:Seq<joint::Frame>,n:nat,key:nat,token:usize)
    requires joint::valid(frames),n<frames.len(),interval::present(frames,n,key),token<interval::at(frames,n,key).occupied.len(),!pending(interval::at(frames,n,key),token),
    ensures interval::present(frames,n+1,key),token<interval::at(frames,n+1,key).occupied.len(),!pending(interval::at(frames,n+1,key),token),
        !completes(frames[n as int].event,key,token),
{
    let event=frames[n as int].event;
    assert(joint::step(joint::state_at(frames,n),frames[n as int].state,event));
    if event.key==key {
        reveal(joint::changes);
        if event.change is Cleanup {spent_step(interval::at(frames,n,key),interval::at(frames,n+1,key),event.change->Cleanup_event,token);}
        else {spent_step(interval::at(frames,n,key),interval::at(frames,n+1,key),CleanupChange::Register,token);}
    }
}
pub proof fn spent_between(frames:Seq<joint::Frame>,start:nat,end:nat,key:nat,token:usize)
    requires joint::valid(frames),start<=end<=frames.len(),interval::present(frames,start,key),token<interval::at(frames,start,key).occupied.len(),!pending(interval::at(frames,start,key),token),
    ensures interval::present(frames,end,key),token<interval::at(frames,end,key).occupied.len(),!pending(interval::at(frames,end,key),token),
    decreases end-start,
{if start<end {spent_edge(frames,start,key,token);spent_between(frames,start+1,end,key,token);}}
pub proof fn consuming_cut(frames:Seq<joint::Frame>,at:nat,key:nat,token:usize)
    requires joint::valid(frames),at<frames.len(),completes(frames[at as int].event,key,token),
        frames[at as int].event.after is Cleanup,token<frames[at as int].event.after->Cleanup_state.occupied.len(),
    ensures interval::present(frames,at,key),interval::present(frames,at+1,key),
        pending(interval::at(frames,at,key),token),token<interval::at(frames,at+1,key).occupied.len(),!pending(interval::at(frames,at+1,key),token),
{
    hide(joint::valid);hide(joint::step);
    crate::reversible_value::managed::recovery::frame_update(frames,at);
    reveal(joint::step);reveal(joint::changes);
}
/// A completed slot is never reused, even when later registration grows the
/// queue or another attempt fails and retries. This is token uniqueness, not
/// just the existing uniqueness of one attempt ticket.
pub proof fn unique_consumption(frames:Seq<joint::Frame>,a:nat,b:nat,key:nat,token:usize)
    requires joint::valid(frames),a<frames.len(),b<frames.len(),
        completes(frames[a as int].event,key,token),completes(frames[b as int].event,key,token),
        frames[a as int].event.after is Cleanup,token<frames[a as int].event.after->Cleanup_state.occupied.len(),
        frames[b as int].event.after is Cleanup,token<frames[b as int].event.after->Cleanup_state.occupied.len(),
    ensures a==b,
{
    consuming_cut(frames,a,key,token);consuming_cut(frames,b,key,token);
    if a<b {spent_between(frames,a+1,b,key,token);}
    if b<a {spent_between(frames,b+1,a,key,token);}
}

proof fn bound_edge(frames:Seq<joint::Frame>,n:nat,key:nat,token:usize)
    requires joint::valid(frames),n<frames.len(),interval::present(frames,n,key),token<interval::at(frames,n,key).occupied.len(),
    ensures interval::present(frames,n+1,key),token<interval::at(frames,n+1,key).occupied.len(),
{
    hide(joint::valid);hide(joint::step);
    crate::reversible_value::managed::recovery::frame_update(frames,n);
    reveal(joint::step);
    if frames[n as int].event.key==key {reveal(joint::changes);}
}
/// Registration appends slots; no transition shrinks or reuses an existing token.
pub proof fn bound_between(frames:Seq<joint::Frame>,start:nat,end:nat,key:nat,token:usize)
    requires joint::valid(frames),start<=end<=frames.len(),interval::present(frames,start,key),token<interval::at(frames,start,key).occupied.len(),
    ensures interval::present(frames,end,key),token<interval::at(frames,end,key).occupied.len(),
    decreases end-start,
{
    hide(joint::valid);hide(joint::step);
    if start<end {bound_edge(frames,start,key,token);bound_between(frames,start+1,end,key,token);}
}

}
