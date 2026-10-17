//! Native setup metadata is issued by the actual Begin owner, rather than
//! reconstructed by the adapter. Group admission uses its committed bindings.
use crate::action_ledger::ActionTicket;
#[cfg(verus_keep_ghost)]
use crate::effect_work::EffectIdentity;
use crate::effect_work::EffectRun;
use crate::execution::Execution;
use crate::lifecycle_state::services::NativeContext;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::joint;
use crate::Binding;
use std::sync::Arc;
use vstd::prelude::*;

verus! {
/// Issued from a real work owner and live cleanup queue. It carries no payload
/// reference. Numeric identities are scoped to the host's execution domain;
/// this is not an authenticity claim about arbitrary colliding host instances.
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct SetupScope {origin:Option<ActionTicket>,work_domain:u64,group:usize,queue_domain:u64}
impl SetupScope {
    pub closed spec fn origin(&self)->Option<ActionTicket> {self.origin}
    pub closed spec fn work_domain(&self)->u64 {self.work_domain}
    pub closed spec fn group_id(&self)->usize {self.group}
    pub closed spec fn queue_domain(&self)->u64 {self.queue_domain}
    pub fn group(&self)->(out:usize) ensures out==self.group_id(), {self.group}
    pub open spec fn matches_effect(&self,identity:EffectIdentity)->bool {
        self.origin()==identity.origin() && self.group_id()==identity.group_id() && self.queue_domain()==identity.domain_id()
    }
    pub(crate) fn accepts_effect(&self,origin:Option<ActionTicket>,group:usize,domain:u64)->(out:bool)
        ensures out==(self.origin()==origin && self.group_id()==group && self.queue_domain()==domain),
    {self.origin==origin && self.group==group && self.queue_domain==domain}
    pub open spec fn matches<V,C,G,I>(&self,execution:&Execution<V,C,G,I>)->bool {
        self.origin()==execution.origin() && self.work_domain()==execution.work_state().domain_id()
            && execution.cleanup_state().live(self.group_id())
            && execution.cleanup_state().domain_ids()[self.group_id()]==self.queue_domain()
    }
    pub fn belongs<V,C,G,I>(&self,execution:&Execution<V,C,G,I>)->(out:bool)
        requires execution.wf(),ensures out==self.matches(execution),
    {
        proof {execution.representation();}
        self.origin==execution.lifecycle_ticket() && self.work_domain==execution.work.domain()
            && match execution.groups.get(self.group) {Some(queue)=>queue.domain()==self.queue_domain,None=>false}
    }
    pub open spec fn observed_in<V,C,G,I>(&self,execution:&Execution<V,C,G,I>,snapshot:&joint::Snapshot)->bool {
        self.matches(execution) && execution.observed(snapshot)
            && snapshot.last()[execution.work_state().link().unwrap().1]->Work_state.origin==self.origin()
            && snapshot.last()[execution.work_state().link().unwrap().1]->Work_state.domain==self.work_domain()
            && snapshot.last()[execution.cleanup_state().link().unwrap().1]->Groups_state.queues.contains_key(self.group_id())
            && snapshot.last()[execution.cleanup_state().link().unwrap().1]->Groups_state.queues[self.group_id()].1==self.queue_domain()
            && snapshot.last()[execution.cleanup_state().queues()[self.group_id()].link().unwrap().1] is Cleanup
    }
    /// The callback scope selects the queue actually present in the same read
    /// epoch as its work owner, not merely a retained historical queue record.
    pub proof fn observed<V,C,G,I>(&self,execution:&Execution<V,C,G,I>,snapshot:&joint::Snapshot)
        requires execution.wf(),self.matches(execution),execution.observed(snapshot),
        ensures self.observed_in(execution,snapshot),
            snapshot.last()[execution.work_state().link().unwrap().1]->Work_state.origin==self.origin(),
            snapshot.last()[execution.work_state().link().unwrap().1]->Work_state.domain==self.work_domain(),
            snapshot.last()[execution.cleanup_state().link().unwrap().1]->Groups_state.queues.contains_key(self.group_id()),
            snapshot.last()[execution.cleanup_state().link().unwrap().1]->Groups_state.queues[self.group_id()].1==self.queue_domain(),
            snapshot.last()[execution.cleanup_state().queues()[self.group_id()].link().unwrap().1] is Cleanup,
    {}
}
impl<V,C,G,I> Execution<V,C,G,I> {
    // Keep the Some-branch verification precondition explicit.
    #[allow(clippy::manual_map)]
    pub fn native_context(&self)->(out:Option<Arc<NativeContext>>)
        requires self.wf(),
        ensures out.is_some()==self.capture().is_some(),
            out.is_some() ==> out.unwrap().describes(self.capture().unwrap())
                && Some(out.unwrap().origin())==self.origin()
                && out.unwrap().domain_id()==self.work_state().domain_id(),
    {match self.native() {Some(values)=>Some(values.setup_context()),None=>None}}

    fn scope_for_group(&self,group:usize)->(out:Option<SetupScope>)
        requires self.wf(),
        ensures out.is_some()==self.cleanup_state().live(group),
            out.is_some() ==> out.unwrap().matches(self) && out.unwrap().group_id()==group,
    {
        proof {self.representation();}
        let queue=self.groups.get(group)?;
        Some(SetupScope {origin:self.lifecycle_ticket(),work_domain:self.work.domain(),group,queue_domain:queue.domain()})
    }
    pub fn root_scope(&self)->(out:Option<SetupScope>)
        requires self.wf(),
        ensures out.is_some()==self.cleanup_state().live(0),
            out.is_some() ==> out.unwrap().matches(self) && out.unwrap().group_id()==0,
    {self.scope_for_group(0)}

    /// Admit the real iterator and issue its callback scope in one operation.
    /// Rejection cannot produce a scope or alter the iterator. A changed target
    /// may still cancel/settle its queue through the ordinary checked protocol.
    pub fn admit_scoped_effect(&mut self,run:&mut EffectRun<G>,target:Option<&[Binding]>)->(out:Option<SetupScope>)
        requires old(self).wf(),old(run).wf(),
        ensures final(self).wf(),final(run).wf(),final(self).execution_journal()==old(self).execution_journal(),
            final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),
            final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),
            final(self).phase_spec()==old(self).phase_spec(),final(run).identity()==old(run).identity(),
            out.is_some()==(old(run).current().is_none() && old(run).next()<u64::MAX
                && old(run).identity().matches(&old(self).cleanup_state())
                && old(self).cleanup_state().poll_enabled(old(run).identity().group_id(),target)),
            out.is_none() ==> *final(run)==*old(run),
            out.is_some() ==> out.unwrap().matches(final(self))
                && out.unwrap().group_id()==final(run).identity().group_id()
                && out.unwrap().queue_domain()==final(run).identity().domain_id()
                && final(run).current()==Some(old(run).next()) && !final(run).called()
                && final(self).cleanup_state().queues()[out.unwrap().group_id()].protocol().stage().pending(),
            final(self).status_links()==old(self).status_links(),
    {
        if !self.admit_effect(run,target) {return None;}
        self.scope_for_group(run.id())
    }

    /// A context describes this immutable Begin capture, and its work/cleanup
    /// identities are present in the same certified observation as the values.
    pub open spec fn context_observed(&self,snapshot:&joint::Snapshot)->bool {
        self.capture().is_some() && self.observed(snapshot)
            && snapshot.last()[self.work_state().link().unwrap().1]->Work_state.origin==Some(self.capture().unwrap().origin)
            && snapshot.last()[self.work_state().link().unwrap().1]->Work_state.domain==self.capture().unwrap().work_domain
            && snapshot.last()[self.cleanup_state().link().unwrap().1]->Groups_state.origin==Some(self.capture().unwrap().origin)
    }
    pub proof fn context_correspondence(&self,snapshot:&joint::Snapshot)
        requires self.wf(),self.capture().is_some(),self.observed(snapshot),
        ensures self.context_observed(snapshot),
    {self.capture_correspondence();}

    pub proof fn effect_context_correspondence(&self,id:usize,snapshot:&joint::Snapshot)
        requires self.wf(),self.context_observed(snapshot),self.cleanup_state().live(id),
            self.cleanup_state().queues()[id].protocol().stage().committed_view()==self.capture().unwrap().bindings,
        ensures {
            let queue=self.cleanup_state().queues()[id];
            &&& queue.link().is_some()
            &&& joint::episode::interval::present(snapshot.events(),snapshot.events().len(),queue.link().unwrap().1)
            &&& joint::episode::interval::at(snapshot.events(),snapshot.events().len(),queue.link().unwrap().1).committed==self.capture().unwrap().bindings
        },
    {}

    /// Native callers cannot substitute the current target or another owner's
    /// bindings. Rejection returns the untouched payload and execution.
    pub fn enqueue_native_effect(&mut self,source:usize,domain:u64,payload:G)->(out:Result<usize,G>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).execution_journal()==old(self).execution_journal(),
            final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),
            final(self).origin()==old(self).origin(),final(self).value_state()==old(self).value_state(),
            final(self).phase_spec()==old(self).phase_spec(),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==payload,
            out.is_ok() ==> old(self).capture().is_some()
                && out->Ok_0==old(self).cleanup_state().next_id()
                && final(self).cleanup_state().queues().contains_key(out->Ok_0)
                && final(self).cleanup_state().queues().remove(out->Ok_0)==old(self).cleanup_state().queues()
                && final(self).cleanup_state().queues()[out->Ok_0].protocol().stage().committed_view()==old(self).capture().unwrap().bindings
                && final(self).work_state().group_requests().last().value().payload()==payload
                && final(self).work_state().group_requests().last().value().identity().matches(&final(self).cleanup_state()),
            final(self).status_links()==old(self).status_links(),
    {
        let context=match self.native_context() {Some(context)=>context,None=>return Err(payload)};
        let committed=context.committed_vec();
        match self.enqueue_effect(source,domain,committed,payload) {Ok(id)=>Ok(id),Err((_,payload))=>Err(payload)}
    }
}
}
