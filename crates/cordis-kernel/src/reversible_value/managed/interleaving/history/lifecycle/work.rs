//! Real work requests and effect runners keep the recorded cleanup owner.
//! Poll landing appends only the inverse returned by the admitted callback.
#[cfg(verus_keep_ghost)]
use super::History;
use super::RecordedExecution;
use crate::cleanup_queue::landing::StageReport;
use crate::effect_work::{EffectReply, EffectRequest, EffectRun};
use crate::reversible_value::managed::Action;
use crate::setup_context::SetupScope;
use crate::setup_work::{WorkItem, WorkReceipt};
use crate::Binding;
use vstd::prelude::*;

verus! {
pub type LandingResult<A,R,T,M,X,E> = Result<Option<StageReport<E>>,EffectReply<Action<A,R,T,M,X>,E>>;
broadcast use vstd::seq_lib::group_seq_properties;
impl<C,G,A,R,T:?Sized,M,X> RecordedExecution<C,G,A,R,T,M,X> {
    /// Any retained current action is exactly its original acquisition. This
    /// strengthens ordinary host histories, whose callback replies may replace
    /// a retry payload, and is maintained by the sealed component interface.
    pub open spec fn conserved(&self)->bool {
        forall|id:usize,i:int|self.histories().contains_key(id)
            && 0<=i<self.histories()[id].current().len() && (#[trigger] self.histories()[id].current()[i]).is_some() ==>
                i<self.histories()[id].initial().len() && self.histories()[id].current()[i]==self.histories()[id].initial()[i]
    }
    /// All originally acquired actions keep their exact token and order across
    /// cleanup attempts, retries and successful group/owner release.
    pub open spec fn same_inverse_word(&self,prior:&Self)->bool {
        self.baseline()==prior.baseline() && self.histories().dom()==prior.histories().dom()
            && forall|id:usize|#[trigger] prior.histories().contains_key(id) ==>
                self.histories()[id].initial()==prior.histories()[id].initial()
    }
    /// Work-only transitions may change pending requests, but cannot replace
    /// any history, original function boundary or retired queue observation.
    pub open spec fn same_history(&self,prior:&Self)->bool {
        self.recovery_boundary()==prior.recovery_boundary() && self.baseline()==prior.baseline() && self.origins()==prior.origins()
            && self.histories()==prior.histories() && self.terminal()==prior.terminal()
    }
    pub fn take_group(&mut self)->(out:Option<WorkItem<EffectRequest<G>>>)
        requires old(self).wf(),
        ensures final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).wf(),final(self).same_history(old(self)),
            final(self).core().cleanup_state()==old(self).core().cleanup_state(),
            out.is_some() ==> out.unwrap()==old(self).core().work_state().group_requests().first()
                && !old(self).core().work_state().outstanding().contains_key(out.unwrap().origin().id())
                && final(self).core().work_state().outstanding()==old(self).core().work_state().outstanding().insert(out.unwrap().origin().id(),crate::setup_work::WorkKind::Group),
            out.is_none() ==> final(self).core().work_state()==old(self).core().work_state(),
    {
        proof {reveal(RecordedExecution::source_order_extends);self.facts();}let out=self.core.take_group();
        proof {reveal(RecordedExecution::wf);}out
    }
    pub fn take_child(&mut self)->(out:Option<WorkItem<C>>)
        requires old(self).wf(),
        ensures final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).wf(),final(self).same_history(old(self)),
            final(self).core().cleanup_state()==old(self).core().cleanup_state(),
            out.is_some() ==> out.unwrap()==old(self).core().work_state().child_requests().first()
                && !old(self).core().work_state().outstanding().contains_key(out.unwrap().origin().id())
                && final(self).core().work_state().outstanding()==old(self).core().work_state().outstanding().insert(out.unwrap().origin().id(),crate::setup_work::WorkKind::Child),
            out.is_none() ==> final(self).core().work_state()==old(self).core().work_state(),
    {
        proof {reveal(RecordedExecution::source_order_extends);self.facts();}let out=self.core.take_child();
        proof {reveal(RecordedExecution::wf);}out
    }
    /// The receipt originates in WorkItem::run or the real awaited PendingWork.
    /// Completing it removes only its own outstanding work identity.
    pub fn complete_request<V>(&mut self,receipt:WorkReceipt<V>)->(out:Result<V,WorkReceipt<V>>)
        requires old(self).wf(),
        ensures final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).wf(),final(self).same_history(old(self)),
            final(self).core().cleanup_state()==old(self).core().cleanup_state(),
            out.is_ok()==(receipt.origin().domain()==old(self).core().work_state().domain_id()
                && old(self).core().work_state().outstanding().contains_key(receipt.origin().id())
                && old(self).core().work_state().outstanding()[receipt.origin().id()]==receipt.origin().kind()),
            out.is_ok() ==> out->Ok_0==receipt.value()
                && final(self).core().work_state().outstanding()==old(self).core().work_state().outstanding().remove(receipt.origin().id()),
            out.is_err() ==> out->Err_0==receipt && final(self).core().work_state()==old(self).core().work_state(),
    {
        proof {reveal(RecordedExecution::source_order_extends);self.facts();}let out=self.core.complete_request(receipt);
        proof {reveal(RecordedExecution::wf);}out
    }
    pub fn activate_effect(&mut self,request:EffectRequest<G>)->(out:Result<(),EffectRequest<G>>)
        requires old(self).wf(),
        ensures final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).wf(),final(self).same_history(old(self)),
            final(self).core().cleanup_state()==old(self).core().cleanup_state(),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==request,
            out.is_ok() ==> final(self).core().effect_state().contains_key(request.identity().group_id())
                && final(self).core().effect_state()[request.identity().group_id()].identity()==request.identity()
                && final(self).core().effect_state()[request.identity().group_id()].payload()==request.payload(),
    {
        proof {reveal(RecordedExecution::source_order_extends);self.facts();}let out=self.core.activate_effect(request);
        proof {reveal(RecordedExecution::wf);}out
    }
    pub fn take_effect(&mut self,id:usize)->(out:Option<EffectRun<G>>)
        requires old(self).wf(),
        ensures final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).wf(),final(self).same_history(old(self)),
            final(self).core().cleanup_state()==old(self).core().cleanup_state(),
            out.is_some()==old(self).core().effect_state().contains_key(id),
            out.is_some() ==> out.unwrap()==old(self).core().effect_state()[id] && out.unwrap().wf(),
            final(self).core().effect_state()==old(self).core().effect_state().remove(id),
            final(self).core().checked_out()==if out.is_some() {old(self).core().checked_out().insert(id,())} else {old(self).core().checked_out()},
    {
        proof {reveal(RecordedExecution::source_order_extends);self.facts();}let out=self.core.take_effect(id);
        proof {reveal(RecordedExecution::wf);}out
    }
    pub fn put_effect(&mut self,run:EffectRun<G>)->(out:Result<(),EffectRun<G>>)
        requires old(self).wf(),run.wf(),
        ensures final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).wf(),final(self).same_history(old(self)),
            final(self).core().cleanup_state()==old(self).core().cleanup_state(),
            out.is_ok()==(old(self).core().checked_out().contains_key(run.identity().group_id())
                && !old(self).core().effect_state().contains_key(run.identity().group_id())
                && run.identity().matches(&old(self).core().cleanup_state())),
            out.is_ok() ==> final(self).core().effect_state()==old(self).core().effect_state().insert(run.identity().group_id(),run)
                && final(self).core().checked_out()==old(self).core().checked_out().remove(run.identity().group_id()),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==run,
    {
        proof {reveal(RecordedExecution::source_order_extends);self.facts();}let out=self.core.put_effect(run);
        proof {reveal(RecordedExecution::wf);}out
    }
    /// Begin-captured bindings, not a later target supplied by the adapter.
    pub fn enqueue_native_effect(&mut self,source:usize,domain:u64,payload:G)->(out:Result<usize,G>)
        requires old(self).wf(),
        ensures final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).wf(),final(self).baseline()==old(self).baseline(),final(self).terminal()==old(self).terminal(),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==payload,
            out.is_ok() ==> !old(self).histories().contains_key(out->Ok_0)
                && old(self).core().capture().is_some()
                && final(self).core().cleanup_state().queues()[out->Ok_0].protocol().stage().committed_view()==old(self).core().capture().unwrap().bindings
                && out->Ok_0==old(self).core().cleanup_state().next_id()
                && final(self).origins()==old(self).origins().insert(out->Ok_0,final(self).core().cleanup_state().queues()[out->Ok_0])
                && final(self).histories().dom()==old(self).histories().dom().insert(out->Ok_0)
                && final(self).histories()[out->Ok_0].initial().len()==0 && final(self).histories()[out->Ok_0].events().len()==0,
            forall|id:usize|#[trigger] old(self).histories().contains_key(id) ==> final(self).histories()[id]==old(self).histories()[id],
    {
        proof {reveal(RecordedExecution::source_order_extends);self.facts();}let out=self.core.enqueue_native_effect(source,domain,payload);
        proof {if let Ok(id)=out {
            let queue=self.core.cleanup_state().queues()[id];self.origins=Ghost(self.origins@.insert(id,queue));
            let tracked history=History::new(queue);self.histories.borrow_mut().tracked_insert(id,history);
        }reveal(RecordedExecution::wf);}out
    }
    pub fn admit_effect(&mut self,run:&mut EffectRun<G>,target:Option<&[Binding]>)->(out:bool)
        requires old(self).wf(),old(run).wf(),
        ensures final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).wf(),final(self).same_history(old(self)),final(run).wf(),final(run).identity()==old(run).identity(),
            out==(old(run).current().is_none() && old(run).next()<u64::MAX
                && old(run).identity().matches(&old(self).core().cleanup_state())
                && old(self).core().cleanup_state().poll_enabled(old(run).identity().group_id(),target)),
            out ==> final(run).current()==Some(old(run).next()) && !final(run).called()
                && final(self).core().cleanup_state().queues()[old(run).identity().group_id()].protocol().stage().pending(),
            !out ==> *final(run)==*old(run),
    {
        proof {reveal(RecordedExecution::source_order_extends);self.facts();}let out=self.core.admit_effect(run,target);
        proof {reveal(RecordedExecution::wf);}out
    }
    pub fn admit_scoped_effect(&mut self,run:&mut EffectRun<G>,target:Option<&[Binding]>)->(out:Option<SetupScope>)
        requires old(self).wf(),old(run).wf(),
        ensures final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).wf(),final(self).same_history(old(self)),final(run).wf(),final(run).identity()==old(run).identity(),
            out.is_some()==(old(run).current().is_none() && old(run).next()<u64::MAX
                && old(run).identity().matches(&old(self).core().cleanup_state())
                && old(self).core().cleanup_state().poll_enabled(old(run).identity().group_id(),target)),
            out.is_some() ==> out.unwrap().matches(&final(self).core()) && out.unwrap().matches_effect(final(run).identity())
                && final(run).current()==Some(old(run).next()) && !final(run).called(),
            out.is_none() ==> *final(run)==*old(run),
    {
        proof {reveal(RecordedExecution::source_order_extends);self.facts();}let out=self.core.admit_scoped_effect(run,target);
        proof {reveal(RecordedExecution::wf);}out
    }
    pub fn cancel(&mut self,id:usize)
        requires old(self).wf(),
        ensures final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).wf(),final(self).same_history(old(self)),
            old(self).core().cleanup_state().live(id) ==> final(self).core().cleanup_state().queues()[id].protocol().stage().cancellation()
                && final(self).core().cleanup_state().queues()[id].protocol().stage().pending()==old(self).core().cleanup_state().queues()[id].protocol().stage().pending(),
    {
        proof {reveal(RecordedExecution::source_order_extends);self.facts();}self.core.cancel(id);proof {reveal(RecordedExecution::wf);}
    }
    /// Even after cancellation, a returned inverse extends the same obligation
    /// prefix. Pending/error replies do not fabricate an inverse or a receipt.
    pub fn land_effect<E>(&mut self,run:&mut EffectRun<G>,reply:EffectReply<Action<A,R,T,M,X>,E>)
        ->(out:LandingResult<A,R,T,M,X,E>)
        requires old(self).wf(),old(run).wf(),
        ensures final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).wf(),final(run).wf(),final(run).identity()==old(run).identity(),
            final(self).baseline()==old(self).baseline(),final(self).origins()==old(self).origins(),final(self).terminal()==old(self).terminal(),
            final(self).histories().dom()==old(self).histories().dom(),
            out.is_err() ==> out->Err_0==reply && *final(self)==*old(self) && *final(run)==*old(run),
            out.is_ok() ==> old(run).called() && old(run).current()==Some(reply.serial()) && reply.identity()==old(run).identity()
                && old(run).identity().matches(&old(self).core().cleanup_state())
                && final(run).current().is_none() && !final(run).called(),
            out.is_ok() ==> {
                let id=old(run).identity().group_id();
                &&& final(self).histories()[id].starts_with(old(self).histories()[id].initial())
                &&& final(self).histories()[id].initial()==if reply.result() is Ready && reply.result()->Ready_0.is_ok() && reply.result()->Ready_0->Ok_0.is_some()
                    {old(self).histories()[id].initial().push(reply.result()->Ready_0->Ok_0)} else {old(self).histories()[id].initial()}
                &&& out->Ok_0.is_some() ==> out->Ok_0.unwrap().token==if reply.result() is Ready && reply.result()->Ready_0.is_ok() && reply.result()->Ready_0->Ok_0.is_some()
                    {Some(old(self).histories()[id].initial().len() as usize)} else {None}
            },
            forall|id:usize|#[trigger] old(self).histories().contains_key(id) ==> final(self).histories()[id].events()==old(self).histories()[id].events(),
            forall|id:usize|#[trigger] old(self).histories().contains_key(id) && id!=old(run).identity().group_id() ==> final(self).histories()[id]==old(self).histories()[id],
    {
        proof {reveal(RecordedExecution::source_order_extends);self.facts();}let ghost before=*self;let ghost id=run.identity().group_id();
        let out=self.core.land_effect(run,reply);
        proof {if out.is_ok() {
            let tracked mut history=self.histories.borrow_mut().tracked_remove(id);let ghost prior=history;
            assert(before.entry(id));assert(history.matches(before.core().cleanup_state().queues()[id]));
            let queue=self.core.cleanup_state().queues()[id];
            assert(queue.slots().take(history.current().len() as int) =~= history.current());
            history.extend(queue);history.prefix_transitive(prior,self.origins()[id].slots());
            self.histories.borrow_mut().tracked_insert(id,history);
        }reveal(RecordedExecution::wf);}out
    }
    /// The actual drain-guarded removal supplies the terminal queue; checked-out
    /// or pending runners cannot be retired by inventing a completed history.
    pub fn retire_effect(&mut self,run:EffectRun<G>)->(out:Result<G,EffectRun<G>>)
        requires old(self).wf(),run.wf(),
        ensures final(self).source_order_extends(old(self)),final(self).value_sources()==old(self).value_sources(),final(self).recovery_boundary()==old(self).recovery_boundary(),final(self).wf(),final(self).baseline()==old(self).baseline(),final(self).origins()==old(self).origins(),
            final(self).histories()==old(self).histories(),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==run,
            out.is_ok() ==> out->Ok_0==run.payload()
                && final(self).terminal()==old(self).terminal().insert(run.identity().group_id(),old(self).core().cleanup_state().queues()[run.identity().group_id()])
                && !final(self).core().cleanup_state().live(run.identity().group_id()),
    {
        proof {reveal(RecordedExecution::source_order_extends);self.facts();}let ghost id=run.identity().group_id();let ghost queue=self.core.cleanup_state().queues()[id];
        let out=self.core.retire_effect(run);
        proof {if out.is_ok() {self.terminal=Ghost(self.terminal@.insert(id,queue));}reveal(RecordedExecution::wf);}out
    }
}
}
