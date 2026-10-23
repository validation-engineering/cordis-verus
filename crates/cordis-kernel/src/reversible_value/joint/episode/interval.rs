//! An issued ticket cannot disappear and later become live again. These
//! lemmas use the actual queue transitions in the authenticated joint history.
#[cfg(verus_keep_ghost)]
use super::{cleanup_step, CleanupChange, CleanupState};
#[cfg(verus_keep_ghost)]
use crate::{cleanup_journal::RestoreTicket, reversible_value::joint};
use vstd::prelude::*;

verus! {
pub open spec fn active(state:CleanupState,ticket:RestoreTicket)->bool {
    state.selected==Some(ticket) && !state.failed
}
pub open spec fn outstanding(state:CleanupState,ticket:RestoreTicket)->bool {
    active(state,ticket) && state.issued && state.domain==ticket.domain && ticket.attempt<state.next
        && ticket.token<state.occupied.len() && !state.occupied[ticket.token as int]
}
pub open spec fn present(frames:Seq<joint::Frame>,n:nat,key:nat)->bool {
    joint::state_at(frames,n).contains_key(key) && joint::state_at(frames,n)[key] is Cleanup
}
pub open spec fn at(frames:Seq<joint::Frame>,n:nat,key:nat)->CleanupState {
    joint::state_at(frames,n)[key]->Cleanup_state
}
/// A queue keeps its admission-time committed providers across every real
/// cleanup/value interleaving, including failure and retry. Retired records
/// remain historical evidence; their presence does not imply live membership.
proof fn committed_step(before:Map<nat,joint::Record>,after:Map<nat,joint::Record>,event:joint::Step,key:nat)
    requires joint::step(before,after,event),before.contains_key(key),before[key] is Cleanup,
    ensures after.contains_key(key),after[key] is Cleanup,
        after[key]->Cleanup_state.committed==before[key]->Cleanup_state.committed,
{
    if event.key==key {reveal(joint::changes);}
}
pub proof fn committed_between(frames:Seq<joint::Frame>,start:nat,end:nat,key:nat)
    requires joint::valid(frames),start<=end<=frames.len(),present(frames,start,key),
    ensures present(frames,end,key),at(frames,end,key).committed==at(frames,start,key).committed,
    decreases end-start,
{
    if start<end {
        committed_between(frames,start,(end-1) as nat,key);
        let n=(end-1) as nat;
        assert(joint::step(joint::state_at(frames,n),frames[n as int].state,frames[n as int].event));
        committed_step(joint::state_at(frames,n),frames[n as int].state,frames[n as int].event,key);
    }
}
pub open spec fn closes(event:joint::Step,key:nat)->bool {
    event.key==key && event.change is Cleanup && event.change->Cleanup_event is Complete
}
pub open spec fn moves(event:joint::Step,key:nat)->bool {
    event.key==key && event.change is Cleanup && (event.change->Cleanup_event is Pop
        || event.change->Cleanup_event is Retry || event.change->Cleanup_event is Complete)
}
pub open spec fn completes(event:joint::Step,key:nat,ticket:RestoreTicket)->bool {
    closes(event,key) && event.change->Cleanup_event->Complete_ticket==ticket
}
pub open spec fn holds(frames:Seq<joint::Frame>,start:nat,end:nat,key:nat,ticket:RestoreTicket)->bool {
    &&& start<=end<=frames.len()
    &&& forall|n:nat| start<=n<=end ==> #[trigger] present(frames,n,key) && outstanding(at(frames,n,key),ticket)
    &&& forall|i:int| start<=i<end ==> !moves(#[trigger] frames[i].event,key)
}

/// Once an attempt number has been passed, neither Pop nor Retry can recreate
/// that ticket. Complete makes it inactive; other steps preserve that identity.
pub proof fn one_step(a:CleanupState,b:CleanupState,change:CleanupChange,ticket:RestoreTicket)
    requires cleanup_step(a,b,change),
    ensures b.domain==a.domain,a.next<=b.next,
        ticket.attempt<a.next && active(b,ticket) ==> active(a,ticket),
        outstanding(a,ticket) && active(b,ticket) ==> outstanding(b,ticket) && !(change is Pop) && !(change is Retry) && !(change is Complete),
{
    match change {
        CleanupChange::Pop {ticket:issued}=>{},
        CleanupChange::Retry {ticket:retried}=>{},
        CleanupChange::Complete {..}=>{},
        _=>{},
    }
}

proof fn edge(frames:Seq<joint::Frame>,i:nat,key:nat,ticket:RestoreTicket)
    requires joint::valid(frames),i<frames.len(),present(frames,i,key),
    ensures present(frames,i+1,key),at(frames,i+1,key).domain==at(frames,i,key).domain,
        at(frames,i,key).next<=at(frames,i+1,key).next,
        ticket.attempt<at(frames,i,key).next && active(at(frames,i+1,key),ticket) ==> active(at(frames,i,key),ticket),
        outstanding(at(frames,i,key),ticket) && active(at(frames,i+1,key),ticket) ==>
            outstanding(at(frames,i+1,key),ticket) && !moves(frames[i as int].event,key),
{
    let event=frames[i as int].event;
    assert(joint::step(joint::state_at(frames,i),frames[i as int].state,event));
    if event.key==key {
        reveal(joint::changes);
        match event.change {
            joint::Change::Cleanup {event:change}=>one_step(at(frames,i,key),at(frames,i+1,key),change,ticket),
            joint::Change::RegisterInverse {..}=>one_step(at(frames,i,key),at(frames,i+1,key),CleanupChange::Register,ticket),
            _=>{assert(false);},
        }
    }
}

proof fn reachable(frames:Seq<joint::Frame>,start:nat,end:nat,key:nat,ticket:RestoreTicket)
    requires joint::valid(frames),start<=end<=frames.len(),present(frames,start,key),
    ensures present(frames,end,key),at(frames,end,key).domain==at(frames,start,key).domain,
        at(frames,start,key).next<=at(frames,end,key).next,
    decreases end-start,
{
    if start<end {
        reachable(frames,start,(end-1) as nat,key,ticket);
        edge(frames,(end-1) as nat,key,ticket);
    }
}

/// An endpoint that is still active excludes any earlier completion of this
/// already issued ticket. This does not assume quiescence between the receipts.
proof fn active_backward(frames:Seq<joint::Frame>,start:nat,end:nat,key:nat,ticket:RestoreTicket)
    requires joint::valid(frames),start<=end<=frames.len(),present(frames,start,key),
        ticket.attempt<at(frames,start,key).next,present(frames,end,key),active(at(frames,end,key),ticket),
    ensures active(at(frames,start,key),ticket),
    decreases end-start,
{
    if start<end {
        reachable(frames,start,(end-1) as nat,key,ticket);
        edge(frames,(end-1) as nat,key,ticket);
        active_backward(frames,start,(end-1) as nat,key,ticket);
    }
}

proof fn issued_forward(frames:Seq<joint::Frame>,start:nat,n:nat,end:nat,key:nat,ticket:RestoreTicket)
    requires joint::valid(frames),start<=n<=end<=frames.len(),present(frames,start,key),
        outstanding(at(frames,start,key),ticket),present(frames,end,key),active(at(frames,end,key),ticket),
    ensures present(frames,n,key),outstanding(at(frames,n,key),ticket),
    decreases n-start,
{
    reachable(frames,start,n,key,ticket);
    active_backward(frames,n,end,key,ticket);
    if start<n {
        issued_forward(frames,start,(n-1) as nat,end,key,ticket);
        edge(frames,(n-1) as nat,key,ticket);
    }
}

/// Every intervening state retains the selected attempt and its vacant slot.
/// The first completion may occur only at the exclusive end of this interval.
pub proof fn between(frames:Seq<joint::Frame>,start:nat,end:nat,key:nat,ticket:RestoreTicket)
    requires joint::valid(frames),start<=end<=frames.len(),present(frames,start,key),
        outstanding(at(frames,start,key),ticket),present(frames,end,key),active(at(frames,end,key),ticket),
    ensures holds(frames,start,end,key,ticket),
{
    assert forall|n:nat| start<=n<=end implies #[trigger] present(frames,n,key) && outstanding(at(frames,n,key),ticket) by {
        issued_forward(frames,start,n,end,key,ticket);
    }
    assert forall|i:int| start<=i<end implies !moves(#[trigger] frames[i].event,key) by {
        assert(present(frames,i as nat,key));
        assert(present(frames,(i+1) as nat,key));
        edge(frames,i as nat,key,ticket);
    }
}
/// Derive an uninterrupted issued interval from authentic queue endpoints.
/// This lemma depends only on queue events, not on a payload's value semantics.
pub proof fn issued_interval(issue:&joint::Receipt,ack:&joint::Receipt,key:nat,ticket:RestoreTicket)
    requires issue.wf(),ack.wf(),ack.follows(issue),issue.event().key==key,ack.event().key==key,
        issue.event().after is Cleanup,outstanding(issue.event().after->Cleanup_state,ticket),
        ack.event().change is Cleanup,ack.event().change->Cleanup_event is Complete,
        ack.event().change->Cleanup_event->Complete_ticket==ticket,
    ensures holds(ack.events(),issue.at()+1,ack.at(),key,ticket),
{
    let frames=ack.events();let end=ack.at();
    assert(frames[issue.at() as int]==issue.events()[issue.at() as int]);
    assert(joint::step(joint::state_at(frames,issue.at()),frames[issue.at() as int].state,issue.event()));
    assert(joint::step(joint::state_at(frames,end),frames[end as int].state,ack.event()));
    reveal(joint::changes);
    between(frames,issue.at()+1,end,key,ticket);
}
/// Query two real read cuts inside an already established issue interval.
/// Receipt prefix lengths also cover a read that appended no mutation.
pub proof fn checkpoint_interval(issue:&joint::Receipt,read:&joint::Receipt,end:&joint::Receipt,ack:&joint::Receipt,key:nat,ticket:RestoreTicket)
    requires issue.wf(),ack.wf(),read.covers(issue),end.covers(read),ack.follows(end),
        holds(ack.events(),issue.at()+1,ack.at(),key,ticket),
    ensures issue.events().len()<=read.events().len()<=end.events().len()<=ack.at(),
        outstanding(at(ack.events(),read.events().len(),key),ticket),
        outstanding(at(ack.events(),end.events().len(),key),ticket),
        at(ack.events(),read.events().len(),key).committed==at(ack.events(),issue.events().len(),key).committed,
{
    let frames=ack.events();let start=issue.events().len();let cut=read.events().len();
    assert(present(frames,start,key));assert(present(frames,cut,key));assert(present(frames,end.events().len(),key));
    committed_between(frames,start,cut,key);
}
/// The actual Complete transition retires this ticket even when its slot is
/// retained for retry. The counter has already passed this attempt number.
pub proof fn after_completion(frames:Seq<joint::Frame>,end:nat,key:nat,ticket:RestoreTicket)
    requires joint::valid(frames),end<frames.len(),present(frames,end,key),outstanding(at(frames,end,key),ticket),
        completes(frames[end as int].event,key,ticket),
    ensures present(frames,end+1,key),!active(at(frames,end+1,key),ticket),ticket.attempt<at(frames,end+1,key).next,
{
    edge(frames,end,key,ticket);
    assert(joint::step(joint::state_at(frames,end),frames[end as int].state,frames[end as int].event));
    reveal(joint::changes);
}

/// A completed attempt remains inactive throughout any authentic extension.
/// Retry may reopen the same token only with a different attempt identity.
pub proof fn never_reactivated(frames:Seq<joint::Frame>,start:nat,end:nat,key:nat,ticket:RestoreTicket)
    requires joint::valid(frames),start<=end<=frames.len(),present(frames,start,key),
        ticket.attempt<at(frames,start,key).next,!active(at(frames,start,key),ticket),
    ensures forall|n:nat| start<=n<=end ==> #[trigger] present(frames,n,key)
            && !active(at(frames,n,key),ticket) && ticket.attempt<at(frames,n,key).next,
        forall|i:int| start<=i<end ==> !completes(#[trigger] frames[i].event,key,ticket),
{
    assert forall|n:nat| start<=n<=end implies #[trigger] present(frames,n,key)
        && !active(at(frames,n,key),ticket) && ticket.attempt<at(frames,n,key).next by {
        reachable(frames,start,n,key,ticket);
        if active(at(frames,n,key),ticket) {active_backward(frames,start,n,key,ticket);}
    }
    assert forall|i:int| start<=i<end implies !completes(#[trigger] frames[i].event,key,ticket) by {
        assert(present(frames,i as nat,key));
        let event=frames[i].event;
        assert(joint::step(joint::state_at(frames,i as nat),frames[i].state,event));
        reveal(joint::changes);
    }
}
/// Keep the universal extension theorem opaque until a client needs a
/// particular state, avoiding automatic expansion of several shared histories.
#[verifier::opaque]
pub open spec fn retired(frames:Seq<joint::Frame>,start:nat,key:nat,ticket:RestoreTicket)->bool {
    &&& start<=frames.len()
    &&& forall|n:nat| start<=n<=frames.len() ==> #[trigger] present(frames,n,key) && !active(at(frames,n,key),ticket)
    &&& forall|i:int| start<=i<frames.len() ==> !completes(#[trigger] frames[i].event,key,ticket)
}
pub proof fn retired_at(frames:Seq<joint::Frame>,start:nat,key:nat,ticket:RestoreTicket,n:nat)
    requires retired(frames,start,key,ticket),start<=n<=frames.len(),
    ensures present(frames,n,key),!active(at(frames,n,key),ticket),
        n<frames.len() ==> !completes(frames[n as int].event,key,ticket),
{reveal(retired);}

/// Transfer a completed boundary into a later history using exact prefix
/// equality. Authentication of the histories is supplied by the caller.
pub proof fn closed_extension(prefix:Seq<joint::Frame>,later:Seq<joint::Frame>,key:nat,ticket:RestoreTicket)
    requires joint::valid(later),0<prefix.len()<=later.len(),later.take(prefix.len() as int)==prefix,
        present(prefix,prefix.len(),key),ticket.attempt<at(prefix,prefix.len(),key).next,
        !active(at(prefix,prefix.len(),key),ticket),
    ensures retired(later,prefix.len(),key,ticket),
{
    assert(later[prefix.len()-1]==prefix[prefix.len()-1]);
    never_reactivated(later,prefix.len(),later.len(),key,ticket);
    reveal(retired);
}
}
