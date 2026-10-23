//! Host acknowledgements can retain only host actions. They cannot replace a
//! managed inverse, or turn an ordinary callback result into a managed restore.
use super::RecordedExecution;
use crate::async_completion::Completion;
#[cfg(verus_keep_ghost)]
use crate::cleanup_groups::payload::recovery::managed;
use crate::cleanup_groups::payload::Cleanup;
use crate::cleanup_journal::RestoreTicket;
use crate::cleanup_queue::completion::{CleanupPolicy, CleanupReport};
use crate::lifecycle_state::registration::shared_child::{ChildCleanup, SharedChild};
use crate::reversible_value::managed::Action;
use vstd::prelude::*;

verus! {
pub enum HostAction<A,R,X> {Once(A),Retryable(R),Native(SharedChild),External(X)}
impl<A,R,X> HostAction<A,R,X> {
    pub open spec fn action<T:?Sized,M>(&self)->Action<A,R,T,M,X> {
        match self {Self::Once(a)=>ChildCleanup::Callback(Cleanup::Once(*a)),Self::Retryable(r)=>ChildCleanup::Callback(Cleanup::Retryable(*r)),Self::Native(n)=>ChildCleanup::Native(*n),Self::External(x)=>ChildCleanup::External(*x)}
    }
    pub fn into_action<T:?Sized,M>(self)->(out:Action<A,R,T,M,X>)
        ensures out==self.action(),!managed(out),
    {
        match self {Self::Once(a)=>ChildCleanup::Callback(Cleanup::Once(a)),Self::Retryable(r)=>ChildCleanup::Callback(Cleanup::Retryable(r)),Self::Native(n)=>ChildCleanup::Native(n),Self::External(x)=>ChildCleanup::External(x)}
    }
}
pub type FutureCompletionResult<E,A,R,T,M,X> = Result<CleanupReport<E,Action<A,R,T,M,X>>,(Completion<RestoreTicket,Result<(),E>>,Option<Action<A,R,T,M,X>>)>;
pub type CompletionResult<E,A,R,T,M,X> = Result<CleanupReport<E,Action<A,R,T,M,X>>,(RestoreTicket,Result<(),E>,Option<Action<A,R,T,M,X>>)>;
impl<C,G,A,R,T:?Sized,M,X> RecordedExecution<C,G,A,R,T,M,X> {
    // Explicit branches preserve the erased receipt and owner relations.
    #[allow(clippy::manual_map)]
    pub fn complete_result<E>(&mut self,id:usize,ticket:RestoreTicket,result:Result<(),E>,retry:Option<HostAction<A,R,X>>,policy:CleanupPolicy)->(out:CompletionResult<E,A,R,T,M,X>)
        requires old(self).wf(),
        ensures old(self).conserved() && (retry.is_none() || old(self).histories().contains_key(id)
                && ticket.token<old(self).histories()[id].initial().len()
                && old(self).histories()[id].initial()[ticket.token as int]==Some(retry.unwrap().action::<T,M>())) ==> final(self).conserved(),
            old(self).histories().contains_key(id) && ticket.token<old(self).histories()[id].initial().len()
                && old(self).histories()[id].initial()[ticket.token as int].is_some()
                && managed(old(self).histories()[id].initial()[ticket.token as int].unwrap()) ==> out.is_err(),
            out.is_err() ==> out->Err_0.1==result,
            final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).wf(),final(self).baseline()==old(self).baseline(),final(self).origins()==old(self).origins(),final(self).terminal()==old(self).terminal(),
            final(self).histories().dom()==old(self).histories().dom(),
            forall|key:usize|#[trigger] old(self).histories().contains_key(key) ==> final(self).histories()[key].initial()==old(self).histories()[key].initial()
                && final(self).histories()[key].events()==old(self).histories()[key].events(),
            out.is_ok() ==> out->Ok_0.result==result && old(self).core().cleanup_state().live(id)
                && old(self).core().cleanup_state().queues()[id].issued()
                && old(self).core().cleanup_state().queues()[id].protocol().selected()==Some(ticket)
                && (old(self).histories()[id].initial()[ticket.token as int].is_none() || !managed(old(self).histories()[id].initial()[ticket.token as int].unwrap())),
    {
        proof {reveal(RecordedExecution::source_order_extends);self.facts();}
        let ghost before=*self;let ghost kept=retry;
        let retry=match retry {Some(action)=>Some(action.into_action::<T,M>()),None=>None};
        proof {assert(retry==if kept.is_some() {Some(kept.unwrap().action::<T,M>())} else {None});}
        let out=self.core.complete_result(id,ticket,result,retry,policy);
        proof {
            if before.core().cleanup_state().live(id) {
                let tracked mut history=self.histories.borrow_mut().tracked_remove(id);
                let queue=self.core.cleanup_state().queues()[id];
                assert(before.entry(id));
                assert forall|token:int|0<=token<history.initial().len() && (#[trigger] history.initial()[token]).is_some() && managed(history.initial()[token].unwrap()) implies
                    queue.slots()[token]==history.current()[token] by {
                    if out.is_ok() {assert(token!=ticket.token as int);}
                }
                history.frame(queue);self.histories.borrow_mut().tracked_insert(id,history);
            }
            reveal(RecordedExecution::wf);
            if before.conserved() && (kept.is_none() || before.histories().contains_key(id)
                && ticket.token<before.histories()[id].initial().len()
                && before.histories()[id].initial()[ticket.token as int]==Some(kept.unwrap().action::<T,M>())) {
                assert forall|group:usize,i:int|self.histories().contains_key(group)
                    && 0<=i<self.histories()[group].current().len() && (#[trigger] self.histories()[group].current()[i]).is_some() implies
                        i<self.histories()[group].initial().len() && self.histories()[group].current()[i]==self.histories()[group].initial()[i] by {
                    if group==id && before.core().cleanup_state().live(id) {
                        assert(self.histories()[group].current()==self.core().cleanup_state().queues()[group].slots());
                        assert(before.histories()[group].current()==before.core().cleanup_state().queues()[group].slots());
                        assert(self.histories()[group].current().len()==before.histories()[group].current().len());
                    } else {assert(self.histories()[group]==before.histories()[group]);}
                    if out.is_ok() && group==id && i==ticket.token as int {
                        assert(result.is_err());assert(kept.is_some());
                        assert(before.histories()[id].initial()[i]==Some(kept.unwrap().action::<T,M>()));
                        assert(self.histories()[id].current()[i]==Some(kept.unwrap().action::<T,M>()));
                    } else {assert(before.histories()[group].current()[i].is_some());}
                }
            }
        }
        out
    }
    /// The actual awaited result remains paired with its captured ticket.
    /// This does not assert eventual Future completion or external I/O truth.
    pub fn complete_future<E>(&mut self,id:usize,completion:Completion<RestoreTicket,Result<(),E>>,retry:Option<HostAction<A,R,X>>,policy:CleanupPolicy)->(out:FutureCompletionResult<E,A,R,T,M,X>)
        requires old(self).wf(),
        ensures final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).wf(),final(self).baseline()==old(self).baseline(),final(self).origins()==old(self).origins(),final(self).terminal()==old(self).terminal(),
            final(self).histories().dom()==old(self).histories().dom(),
            forall|key:usize|#[trigger] old(self).histories().contains_key(key) ==> final(self).histories()[key].initial()==old(self).histories()[key].initial()
                && final(self).histories()[key].events()==old(self).histories()[key].events(),
            out.is_err() ==> out->Err_0.0==completion,
            out.is_ok() ==> out->Ok_0.result==completion.result() && old(self).core().cleanup_state().live(id)
                && old(self).core().cleanup_state().queues()[id].issued()
                && old(self).core().cleanup_state().queues()[id].protocol().selected()==Some(completion.argument())
                && (old(self).histories()[id].initial()[completion.argument().token as int].is_none() || !managed(old(self).histories()[id].initial()[completion.argument().token as int].unwrap())),
    {
        proof {reveal(RecordedExecution::source_order_extends);self.facts();}
        let ghost before=*self;let ghost ticket=completion.argument();
        let retry=retry.map(|retry:HostAction<A,R,X>|retry.into_action::<T,M>());
        let out=self.core.complete_future(id,completion,retry,policy);
        proof {
            if before.core().cleanup_state().live(id) {
                let tracked mut history=self.histories.borrow_mut().tracked_remove(id);
                let queue=self.core.cleanup_state().queues()[id];
                assert(before.entry(id));
                assert forall|token:int|0<=token<history.initial().len() && (#[trigger] history.initial()[token]).is_some() && managed(history.initial()[token].unwrap()) implies
                    queue.slots()[token]==history.current()[token] by {
                    if out.is_ok() {assert(token!=ticket.token as int);}
                }
                history.frame(queue);self.histories.borrow_mut().tracked_insert(id,history);
            }
            reveal(RecordedExecution::wf);
        }
        out
    }
}
}
