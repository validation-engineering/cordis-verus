//! Atomic production episode operations on the existing native host.
use super::NativeHost;
use crate::action_ledger::ActionTicket;
use crate::execution::Execution;
#[cfg(verus_keep_ghost)]
use crate::execution::ExecutionPhase;
use crate::lifecycle_actions::CleanupOutcome;
use crate::lifecycle_state::registration::RegisteredInvocation;
use crate::lifecycle_state::services::{NativeServices, ReleasedNativeValues};
#[cfg(verus_keep_ghost)]
use crate::refinement::{self, Rule};
use crate::Error;
#[cfg(verus_keep_ghost)]
use crate::Kernel;
#[cfg(verus_keep_ghost)]
use crate::Port;
use std::collections::BTreeMap;
use vstd::prelude::*;

verus! {
impl<R,H> NativeHost<R,H> {
    pub fn begin_managed_execution<V,C,G,I>(&mut self,id:usize,store:&NativeServices<V>,domain:u64)
        ->(out:Result<Execution<V,C,G,I>,Error>)
        requires old(self).wf(),store.wf(),
        ensures out.is_ok() ==> out->Ok_0.work_state().link().is_none() && out->Ok_0.cleanup_state().execution_journal().is_none() && out->Ok_0.cleanup_state().queues().dom()==set![0usize],final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(), (forall|n:usize| n!=id ==> final(self).state().control().generation_of(n)==old(self).state().control().generation_of(n)), final(self).wf(),final(self).entries()==old(self).entries(),
            out.is_err() ==> final(self).state().same(&old(self).state()),
            out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.value_attempts().events().len()==0 && out->Ok_0.phase_spec()==ExecutionPhase::Loading
                && final(self).state().execution_matches(id,&out->Ok_0.work_state(),&out->Ok_0.cleanup_state())
                && out->Ok_0.value_state().is_some() && out->Ok_0.value_state().unwrap().owned()==Map::empty()
                && out->Ok_0.value_state().unwrap().capture().control==final(self).state().control()
                && out->Ok_0.value_state().unwrap().capture().sources==crate::lifecycle_state::services::capture::sources(store.entries())
                && out->Ok_0.value_state().unwrap().capture().work_domain==domain
                && out->Ok_0.value_state().unwrap().provisions()==old(self).entries()[id].recipe().provisions_spec()
                && out->Ok_0.capture().unwrap().realms==old(self).entries()[id].recipe().realms()
                && out->Ok_0.capture().unwrap().anchor==old(self).entries()[id].recipe().anchor_port()
                && (forall|b:crate::Binding| out->Ok_0.value_state().unwrap().bindings().contains(b)==final(self).state().control().binding_recorded(id,b))
                && (forall|key:(usize,u64,u64)| #[trigger] out->Ok_0.value_state().unwrap().imports().contains_key(key)==(
                    out->Ok_0.value_state().unwrap().bindings().contains(crate::Binding {provider:key.0,key:key.1,realm:key.2})
                    && store.available(&final(self).state(),key.0,Port {key:key.1,realm:key.2})))
                && (forall|key:(usize,u64,u64)| #[trigger] out->Ok_0.value_state().unwrap().imports().contains_key(key) ==>
                    out->Ok_0.value_state().unwrap().imports()[key]==store.entries()[key.0].values()[(key.1,key.2)])
                && refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),id,Rule::Begin),
    {
        let (work,groups,values)=self.begin_native_execution(id,store,domain)?;
        let out=Execution {work,groups,values:Some(values),initialized:false,effects:BTreeMap::new(),checked_out:BTreeMap::new(),statuses:BTreeMap::new(),attempts:Tracked(crate::reversible_value::attempt::Ledger::new())};
        proof {out.representation();}
        Ok(out)
    }
    /// The actual publication and local Active observation become visible in
    /// the same exclusive call; there is no second adapter phase assignment.
    pub fn finish_managed_execution<V,C,G,I>(&mut self,id:usize,store:&mut NativeServices<V>,execution:&mut Execution<V,C,G,I>)
        ->(out:Result<(),Error>)
        requires old(self).wf(),old(store).wf(),old(execution).wf(),
        ensures final(store).domain_id()==old(store).domain_id(), final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(), final(self).state().control().generations_preserved(&old(self).state().control()), final(self).wf(),final(self).entries()==old(self).entries(),final(store).wf(),final(execution).wf(),final(execution).execution_journal()==old(execution).execution_journal(),final(execution).value_attempts()==old(execution).value_attempts(),final(execution).capture()==old(execution).capture(),
            final(execution).work_state()==old(execution).work_state(),final(execution).cleanup_state()==old(execution).cleanup_state(),
            final(execution).value_state()==old(execution).value_state(),
            out.is_err() ==> *final(execution)==*old(execution) && *final(store)==*old(store)
                && final(self).state().control().unchanged(&old(self).state().control()),
            out.is_ok() ==> old(self).state().execution_matches(id,&old(execution).work_state(),&old(execution).cleanup_state())
                && final(store).entries().dom()==old(store).entries().dom().insert(id)
                && final(store).entries()[id].capture()==old(execution).value_state().unwrap().capture()
                && final(store).entries()[id].origin()==final(execution).value_state().unwrap().origin()
                && (forall|n:usize| n!=id && #[trigger] old(store).entries().contains_key(n) ==> final(store).entries()[n]==old(store).entries()[n])
                && final(execution).phase_spec()==ExecutionPhase::Active
                && final(store).entries()[id].values()==final(execution).value_state().unwrap().owned()
                && final(execution).value_state().unwrap().complete()
                && refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),id,Rule::Finish),
            final(execution).status_links()==old(execution).status_links(),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        proof {execution.representation();}
        proof {reveal(Kernel::unchanged);}
        if execution.values.is_none() || !execution.checked_out.is_empty() || !execution.work.accepting_now() || execution.work.closed_now() {return Err(Error::InvalidState);}
        self.finish_native_execution(id,store,execution.values.as_ref().unwrap(),&execution.work,&execution.groups)?;
        execution.initialized=true;
        proof {execution.representation();}
        Ok(())
    }
    pub fn release_managed_execution<V,C,G,I>(&mut self,id:usize,store:&mut NativeServices<V>,execution:&mut Execution<V,C,G,I>)
        ->(out:Result<(CleanupOutcome,ReleasedNativeValues<V>),Error>)
        requires old(self).wf(),old(store).wf(),old(execution).wf(),
        ensures final(store).domain_id()==old(store).domain_id(), final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(), final(self).state().control().generations_preserved(&old(self).state().control()), final(self).wf(),final(self).entries()==old(self).entries(),final(store).wf(),final(execution).wf(),final(execution).execution_journal()==old(execution).execution_journal(),final(execution).value_attempts()==old(execution).value_attempts(),final(execution).capture()==old(execution).capture(),
            final(execution).origin()==old(execution).origin(),
            final(execution).value_state().is_some() ==> final(execution).value_state().unwrap().capture()==old(execution).value_state().unwrap().capture(),
            out.is_err() ==> final(self).state().same(&old(self).state()) && *final(store)==*old(store) && *final(execution)==*old(execution),
            out.is_ok() ==> final(execution).phase_spec()==ExecutionPhase::Closed
                && old(execution).work_state().idle() && old(execution).cleanup_state().all_drained()
                && out->Ok_0.1.owned()==old(execution).value_state().unwrap().owned()
                && out->Ok_0.1.imports()==old(execution).value_state().unwrap().imports()
                && out->Ok_0.1.imports()==old(execution).value_state().unwrap().capture().imports
                && final(store).entries()==old(store).entries().remove(id)
                && refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),id,Rule::Unload),
            final(execution).status_links()==old(execution).status_links(),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        proof {execution.representation();}
        if execution.values.is_none() || !execution.effects.is_empty() || !execution.checked_out.is_empty() || !execution.statuses.is_empty() {
            proof {reveal(crate::lifecycle_state::LifecycleState::same);reveal(Kernel::unchanged);self.state().protocol().same_reflexive();}
            return Err(Error::InvalidState);
        }
        let out=self.release_native_execution(id,store,execution.values.as_mut().unwrap(),&mut execution.work,&mut execution.groups);
        proof {execution.representation();}
        out
    }
    /// Withdrawal closes acquisition in the same checked call as the actual
    /// Retire or explicit Restart control transition. In-flight inverses stay owned.
    pub fn withdraw_managed_execution<V,C,G,I>(&mut self,id:usize,execution:&mut Execution<V,C,G,I>,retiring:bool)
        ->(out:Result<(),Error>)
        requires old(self).wf(),old(execution).wf(),
        ensures final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(), final(self).state().control().generations_preserved(&old(self).state().control()), final(self).wf(),final(self).entries()==old(self).entries(),final(execution).wf(),final(execution).execution_journal()==old(execution).execution_journal(),final(execution).value_attempts()==old(execution).value_attempts(),final(execution).capture()==old(execution).capture(),
            final(execution).origin()==old(execution).origin(),
            final(execution).cleanup_state()==old(execution).cleanup_state(),final(execution).value_state()==old(execution).value_state(),
            out.is_err() ==> final(self).state().same(&old(self).state()) && *final(execution)==*old(execution),
            out.is_ok() ==> final(execution).phase_spec()==ExecutionPhase::Restoring
                && !final(execution).work_state().accepts()
                && old(self).state().execution_matches(id,&old(execution).work_state(),&old(execution).cleanup_state())
                && refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),id,
                    if retiring {Rule::Retire} else {Rule::Restart}),
            final(execution).status_links()==old(execution).status_links(),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        proof {execution.representation();}
        if execution.work.closed_now() || !self.lifecycle.matches_execution(id,&execution.work,&execution.groups) {
            proof {reveal(crate::lifecycle_state::LifecycleState::same);reveal(Kernel::unchanged);self.state().protocol().same_reflexive();}
            return Err(Error::InvalidState);
        }
        if retiring {self.retire(id)?;} else {self.leave(id)?;}
        execution.withdraw();Ok(())
    }
    pub fn admit_managed_root<V,C,G,I,A>(&self,id:usize,execution:&mut Execution<V,C,G,I>,argument:A)
        ->(out:Result<RegisteredInvocation<A>,A>)
        requires self.wf(),old(execution).wf(),
        ensures final(execution).wf(),final(execution).execution_journal()==old(execution).execution_journal(),final(execution).value_attempts()==old(execution).value_attempts(),final(execution).capture()==old(execution).capture(),final(execution).value_state()==old(execution).value_state(),
            final(execution).cleanup_state()==old(execution).cleanup_state(),final(execution).origin()==old(execution).origin(),
            final(execution).work_state().domain_id()==old(execution).work_state().domain_id(),
            final(execution).value_state().is_some() ==> final(execution).value_state().unwrap().capture()==old(execution).value_state().unwrap().capture(),
            out.is_err() ==> out->Err_0==argument && *final(execution)==*old(execution),
            out.is_ok() ==> out->Ok_0.work().value()==argument && out->Ok_0.owner()==id
                && out->Ok_0.lifecycle()==old(execution).origin().unwrap()
                && out->Ok_0.work().origin().domain_id()==old(execution).work_state().domain_id()
                && self.state().root_invocation_enabled(out->Ok_0.lifecycle())
                && out->Ok_0.version()==self.entries()[id].recipe().version()
                && final(execution).work_state().root_status()==crate::setup_work::RootStatus::Queued
                && out->Ok_0.work().origin().request_id()==0 && out->Ok_0.work().origin().request_kind()==crate::setup_work::WorkKind::Root,
            final(execution).status_links()==old(execution).status_links(),
    {
        proof {execution.representation();} let out=self.admit_root(id,&mut execution.work,argument);proof {execution.representation();} out}
    pub fn settle_managed_execution<V,C,G,I>(&mut self,id:usize,execution:&Execution<V,C,G,I>)->(out:Result<(),Error>)
        requires old(self).wf(),execution.wf(),
        ensures final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(), final(self).state().control().generations_preserved(&old(self).state().control()), final(self).wf(),final(self).entries()==old(self).entries(),final(self).state().control().unchanged(&old(self).state().control()),
            out.is_ok() ==> execution.work_state().idle() && !execution.cleanup_state().any_pending(),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        proof {execution.representation();}self.settle_execution(id,&execution.work,&execution.groups)}
    pub fn fail_managed_execution<V,C,G,I>(&mut self,id:usize,execution:&Execution<V,C,G,I>)->(out:Result<(),Error>)
        requires old(self).wf(),execution.wf(),
        ensures final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(), final(self).state().control().generations_preserved(&old(self).state().control()), final(self).wf(),final(self).entries()==old(self).entries(),final(self).state().control().unchanged(&old(self).state().control()),
            out.is_ok() ==> execution.cleanup_state().any_failed() && execution.work_state().idle()
                && !execution.cleanup_state().any_pending() && !execution.cleanup_state().any_issued(),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        proof {execution.representation();}self.fail_execution(id,&execution.work,&execution.groups)}
    pub fn retry_managed_execution<V,C,G,I>(&mut self,id:usize,execution:&mut Execution<V,C,G,I>)->(out:Result<ActionTicket,Error>)
        requires old(self).wf(),old(execution).wf(),
        ensures out.is_ok() ==> out->Ok_0.id==id && out->Ok_0.generation==old(execution).origin().unwrap().generation
                && out->Ok_0.action==old(self).state().protocol().next_id(),
            final(self).state().control().unchanged(&old(self).state().control()), final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(), final(self).state().control().generations_preserved(&old(self).state().control()), final(self).wf(),final(self).entries()==old(self).entries(),final(execution).wf(),final(execution).execution_journal()==old(execution).execution_journal(),final(execution).value_attempts()==old(execution).value_attempts(),final(execution).capture()==old(execution).capture(),
            final(execution).work_state()==old(execution).work_state(),final(execution).value_state()==old(execution).value_state(),
            final(execution).phase_spec()==old(execution).phase_spec(),
            out.is_err() ==> final(self).state().same(&old(self).state()) && *final(execution)==*old(execution),
            out.is_ok() ==> !final(execution).cleanup_state().any_failed()
                && final(self).state().protocol().cleanup_reply_enabled(out->Ok_0),
            final(execution).status_links()==old(execution).status_links(),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        proof {execution.representation();} let out=self.retry_execution(id,&execution.work,&mut execution.groups);proof {execution.representation();} out}
}
}
