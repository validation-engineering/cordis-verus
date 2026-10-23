//! Child request admission and its inverse stay in one recorded owner.
//! The shared native slot is constructed by the existing production admission.
pub mod completion;
use super::RecordedExecution;
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::registration::shared_child::ChildCleanup;
use crate::lifecycle_state::registration::shared_child::{ChildDispatch, SharedChild};
use crate::reversible_value::managed::Action;
use vstd::prelude::*;

verus! {
pub type ChildAdmission<C,A,R,T,M,X> = Result<usize,(C,Action<A,R,T,M,X>)>;
broadcast use vstd::seq_lib::group_seq_properties;
impl<C,G,A,R,T:?Sized,M,X> RecordedExecution<C,G,A,R,T,M,X> {
    /// Source relation to the real retained inverse, including the creating
    /// episode. Numeric child/plugin IDs alone cannot satisfy this relation.
    pub open spec fn owned_child_retirement(&self,id:usize,token:int,retirement:&crate::lifecycle_state::native::runtime::child_recovery::Retirement)->bool {
        &&& self.wf() && self.histories().contains_key(id)
        &&& 0<=token<self.histories()[id].initial().len() && self.histories()[id].initial()[token].is_some()
        &&& self.histories()[id].initial()[token].unwrap() is Native
        &&& {
            let child=self.histories()[id].initial()[token].unwrap()->Native_0;
            &&& retirement.belongs_to(&child) && self.baseline().origin().is_some()
            &&& retirement.domain()==self.baseline().origin().unwrap().domain
            &&& retirement.parent()==self.baseline().origin().unwrap().id
            &&& retirement.parent_episode()==Some(self.baseline().origin().unwrap().generation)
            &&& self.baseline().execution_journal()==Some(retirement.checkpoint().journal())
        }
    }
    /// Complete the assigned Child's endpoint using its own actual release.
    /// This does not consume a host ticket or prove descendant execution deletion.
    pub proof fn native_child_released(&self,id:usize,token:int,retirement:&crate::lifecycle_state::native::runtime::child_recovery::Retirement,end:&crate::lifecycle_state::native::runtime::episode::Unload)
        requires self.owned_child_retirement(id,token,retirement),retirement.matches_unload(end),
        ensures end.owner().origin.id==retirement.child(),
            end.after().control.fibers[retirement.child()].phase==crate::Phase::Inactive,
            !end.after().owners.contains_key(retirement.child()),!end.after().publications.contains_key(retirement.child()),
            !crate::refinement::relied(end.before().control,retirement.child()),
            end.cleanup_source(),
    {retirement.unload_releases_assigned_episode(end);}
    /// Pending cancellation/rejection has no assigned Child to unload. The
    /// persistent decision prevents a later dispatcher from allocating it.
    pub proof fn native_child_unassigned(tracked &self,id:usize,token:int,tracked retirement:&crate::lifecycle_state::native::runtime::child_recovery::Retirement,tracked later:&crate::lifecycle_state::registration::shared_child::ChildSnapshot)
        requires self.owned_child_retirement(id,token,retirement),!retirement.assigned(),
            later.wf(),later.source()==retirement.source(),
        ensures !(later.state() is Assigned),
    {retirement.unassigned_stays_unassigned(later);}
    /// An explicit external child/inverse pair has an external semantic law;
    /// the owner proves atomic admission and retains any managed inverse.
    pub fn enqueue_owned_child(&mut self,id:usize,payload:C,inverse:Action<A,R,T,M,X>)
        ->(out:ChildAdmission<C,A,R,T,M,X>)
        requires old(self).wf(),
        ensures final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).wf(),final(self).baseline()==old(self).baseline(),final(self).origins()==old(self).origins(),final(self).terminal()==old(self).terminal(),
            final(self).histories().dom()==old(self).histories().dom(),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==(payload,inverse),
            out.is_ok() ==> old(self).core().work_state().accepts() && old(self).core().cleanup_state().acquisition_open(id)
                && final(self).core().work_state().child_requests().last().value()==payload
                && out->Ok_0==old(self).histories()[id].initial().len()
                && final(self).histories()[id].initial()==old(self).histories()[id].initial().push(Some(inverse)),
            forall|group:usize|#[trigger] old(self).histories().contains_key(group) ==> final(self).histories()[group].events()==old(self).histories()[group].events(),
            forall|group:usize|group!=id && #[trigger] old(self).histories().contains_key(group) ==> final(self).histories()[group]==old(self).histories()[group],
    {
        proof {reveal(RecordedExecution::source_order_extends);self.facts();}let ghost before=*self;
        let out=self.core.enqueue_owned_child(id,payload,inverse);
        proof {if out.is_ok() {
            let tracked mut history=self.histories.borrow_mut().tracked_remove(id);let ghost prior=history;
            assert(before.entry(id));assert(history.matches(before.core().cleanup_state().queues()[id]));
            let queue=self.core.cleanup_state().queues()[id];
            assert(queue.slots()==history.current().push(Some(inverse)));
            assert(queue.slots().take(history.current().len() as int) =~= history.current());
            history.extend(queue);history.prefix_transitive(prior,self.origins()[id].slots());
            self.histories.borrow_mut().tracked_insert(id,history);
        }reveal(RecordedExecution::wf);}out
    }
}
impl<N,Y,G,A,R,T:?Sized,M,X> RecordedExecution<ChildDispatch<N,Y>,G,A,R,T,M,X> {
    /// The returned handle, actual queued request and inverse share the same
    /// allocation. Successful admission extends rather than resets its log.
    pub fn enqueue_native_child(&mut self,id:usize,payload:N)->(out:Result<(SharedChild,usize),N>)
        requires old(self).wf(),
        ensures old(self).conserved() ==> final(self).conserved(),final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).wf(),final(self).baseline()==old(self).baseline(),final(self).origins()==old(self).origins(),final(self).terminal()==old(self).terminal(),
            final(self).histories().dom()==old(self).histories().dom(),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==payload,
            out.is_ok() ==> {
                let child=out->Ok_0.0;let token=out->Ok_0.1;
                &&& child.wf() && old(self).core().origin().is_some()
                &&& child.domain_id()==old(self).core().origin().unwrap().domain && child.owner()==old(self).core().origin().unwrap().id
                &&& child.episode()==Some(old(self).core().origin().unwrap().generation)
                &&& final(self).core().work_state().child_requests().last().value() is Native
                &&& final(self).core().work_state().child_requests().last().value()->Native_0.payload()==payload
                &&& final(self).core().work_state().child_requests().last().value()->Native_0.child()==child
                &&& token==old(self).histories()[id].initial().len()
                &&& final(self).histories()[id].initial()==old(self).histories()[id].initial().push(Some(ChildCleanup::Native(child)))
            },
            forall|group:usize|#[trigger] old(self).histories().contains_key(group) ==> final(self).histories()[group].events()==old(self).histories()[group].events(),
            forall|group:usize|group!=id && #[trigger] old(self).histories().contains_key(group) ==> final(self).histories()[group]==old(self).histories()[group],
    {
        proof {reveal(RecordedExecution::source_order_extends);self.facts();}let ghost before=*self;
        let out=self.core.enqueue_native_child(id,payload);
        proof {if let Ok((ref child,_))=out {
            let tracked mut history=self.histories.borrow_mut().tracked_remove(id);let ghost prior=history;
            assert(before.entry(id));assert(history.matches(before.core().cleanup_state().queues()[id]));
            let queue=self.core.cleanup_state().queues()[id];
            assert(queue.slots()==history.current().push(Some(ChildCleanup::Native(*child))));
            assert(queue.slots().take(history.current().len() as int) =~= history.current());
            history.extend(queue);history.prefix_transitive(prior,self.origins()[id].slots());
            self.histories.borrow_mut().tracked_insert(id,history);
        }reveal(RecordedExecution::wf);
            if before.conserved() {
                assert forall|group:usize,i:int|self.histories().contains_key(group)
                    && 0<=i<self.histories()[group].current().len() && (#[trigger] self.histories()[group].current()[i]).is_some() implies
                        i<self.histories()[group].initial().len() && self.histories()[group].current()[i]==self.histories()[group].initial()[i] by {
                    if group==id && out.is_ok() {
                        if i<before.histories()[id].current().len() {assert(before.histories()[id].current()[i].is_some());}
                    }
                }
            }
        }out
    }
}
}
