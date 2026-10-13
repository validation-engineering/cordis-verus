//! Compose actual admitted work and all cleanup groups with lifecycle actions.
//! A work owner is bound at Begin, not by a later caller-supplied identity.
//! Successful release derives its outcome from the owned groups, seals work,
//! consumes the current cleanup action and performs the real Unload step.
use super::LifecycleState;
use crate::action_ledger::{ActionKind, ActionTicket};
use crate::cleanup_groups::CleanupGroups;
use crate::lifecycle_actions::CleanupOutcome;
use crate::setup_work::SetupWork;
use crate::Error;
#[cfg(verus_keep_ghost)]
use crate::{Kernel, Phase};
use vstd::prelude::*;

verus! {
impl LifecycleState {
    pub open spec fn execution_matches<C,G,T>(&self,id:usize,work:&SetupWork<C,G>,groups:&CleanupGroups<T>)->bool {
        work.origin().is_some() && work.origin()==groups.origin() && work.origin().unwrap().domain==self.protocol().domain_id()
            && work.origin().unwrap().id==id
            && self.control().generation_of(id)==Some(work.origin().unwrap().generation)
            && work.owns(groups)
    }
    pub fn matches_execution<C,G,T>(&self,id:usize,work:&SetupWork<C,G>,groups:&CleanupGroups<T>)->(out:bool)
        requires self.wf(),work.wf(),groups.wf(),
        ensures out==self.execution_matches(id,work,groups),
    {
        let ticket=match work.lifecycle_ticket() {Some(ticket)=>ticket,None=>return false};
        groups.lifecycle_ticket()==Some(ticket) && ticket.domain==self.domain() && ticket.id==id
            && self.kernel.episode_generation(id)==Some(ticket.generation) && work.matches(groups)
    }

    /// Create the real work/cleanup owners as part of the successful Begin.
    /// The unbound static adapter constructor cannot manufacture this origin.
    #[allow(clippy::type_complexity)]
    pub fn begin_execution<C,G,T>(&mut self,id:usize,cleanup_domain:u64)
        ->(out:Result<(SetupWork<C,G>,CleanupGroups<T>),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
            out.is_ok()==(old(self).protocol().admission_enabled(id) && old(self).control().begin_enabled(id)),
            out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> out->Ok_0.0.wf() && out->Ok_0.1.wf()
                && final(self).execution_matches(id,&out->Ok_0.0,&out->Ok_0.1)
                && final(self).protocol().recorded(out->Ok_0.0.origin().unwrap())
                && !out->Ok_0.0.idle() && !out->Ok_0.1.drained_failure()
                && out->Ok_0.1.queues().dom()==set![0usize]
                && crate::refinement::step(old(self).control().paper(),final(self).control().paper(),id,crate::refinement::Rule::Begin),
    {
        let ticket=self.begin(id)?;
        Ok((SetupWork::for_lifecycle(ticket,cleanup_domain),CleanupGroups::for_lifecycle(ticket,cleanup_domain)))
    }

    /// Admitted root, dispatched requests and every pending stage must land
    /// before its setup action can be acknowledged, including on withdrawal.
    pub fn settle_execution<C,G,T>(&mut self,id:usize,work:&SetupWork<C,G>,groups:&CleanupGroups<T>)->(out:Result<(),Error>)
        requires old(self).wf(),work.wf(),groups.wf(),
        ensures final(self).wf(),final(self).control().unchanged(&old(self).control()),
            out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> old(self).execution_matches(id,work,groups) && work.idle() && !groups.any_pending()
                && !final(self).protocol().outstanding(id),
    {
        proof {reveal(Kernel::unchanged);self.actions.same_reflexive();}
        if !self.matches_execution(id,work,groups) || !work.is_idle() || groups.has_pending() {
            return Err(Error::InvalidState);
        }
        if let Some(ticket)=self.pending(id) {
            if Some(ticket)!=work.lifecycle_ticket() {return Err(Error::InvalidState);}
            let result=self.complete_setup(ticket);
            if result.is_err() {return Err(Error::InvalidState);}
        }
        proof {reveal(Kernel::unchanged);}
        Ok(())
    }

    /// The Active transition uses the real current target and the bound work.
    /// A failed Finish can still settle its completed setup action; it cannot
    /// change the kernel or make services Active.
    pub fn finish_execution<C,G,T>(&mut self,id:usize,work:&SetupWork<C,G>,groups:&CleanupGroups<T>)->(out:Result<(),Error>)
        requires old(self).wf(),work.wf(),groups.wf(),
        ensures final(self).wf(),
            out.is_err() ==> final(self).control().unchanged(&old(self).control()),
            out.is_ok() ==> old(self).execution_matches(id,work,groups) && work.idle() && !work.failed()
                && !groups.any_pending() && !groups.any_failed()
                && final(self).control().phase_of(id)==Some(Phase::Active)
                && crate::refinement::step(old(self).control().paper(),final(self).control().paper(),id,crate::refinement::Rule::Finish),
    {
        proof {reveal(Kernel::unchanged);self.actions.same_reflexive();}
        if !self.matches_execution(id,work,groups) {return Err(Error::InvalidState);}
        let target=match self.kernel.target(id) {Some(target)=>target,None=>return Err(Error::Changed)};
        if !work.can_finish(groups,&target) {return Err(Error::InvalidState);}
        let ghost prior=self.control();
        self.settle_execution(id,work,groups)?;
        proof {self.kernel.unchanged_observations(&prior);}
        self.finish(id)
    }

    /// Report a real retained failure, never a caller-selected success.
    pub fn fail_execution<C,G,T>(&mut self,id:usize,work:&SetupWork<C,G>,groups:&CleanupGroups<T>)->(out:Result<(),Error>)
        requires old(self).wf(),work.wf(),groups.wf(),
        ensures final(self).wf(),final(self).control().unchanged(&old(self).control()),
            out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> old(self).execution_matches(id,work,groups) && groups.any_failed()
                && work.idle() && !groups.any_pending() && !groups.any_issued()
                && !final(self).protocol().eligible(id,work.origin().unwrap().generation),
    {
        proof {reveal(Kernel::unchanged);self.actions.same_reflexive();}
        if !self.matches_execution(id,work,groups) || !work.is_idle() || groups.has_pending()
            || groups.has_issued() || !groups.has_failed() {return Err(Error::InvalidState);}
        let ticket=match self.pending(id) {Some(ticket)=>ticket,None=>return Err(Error::InvalidState)};
        if ticket.generation!=work.lifecycle_ticket().unwrap().generation {return Err(Error::InvalidState);}
        match self.complete_cleanup(ticket,CleanupOutcome::Failed) {
            Ok(())=>Ok(()),Err(_)=>Err(Error::InvalidState),
        }
    }

    /// Whole-episode retry and all retained inverse retries advance together.
    /// A preflight failure cannot consume a lifecycle action or another group.
    pub fn retry_execution<C,G,T>(&mut self,id:usize,work:&SetupWork<C,G>,groups:&mut CleanupGroups<T>)->(out:Result<ActionTicket,Error>)
        requires old(self).wf(),work.wf(),old(groups).wf(),
        ensures final(self).wf(),final(groups).wf(),final(self).control().unchanged(&old(self).control()),
            out.is_err() ==> final(self).same(old(self)) && *final(groups)==*old(groups),
            out.is_ok() ==> old(self).execution_matches(id,work,old(groups)) && old(groups).retries_ready()
                && !final(groups).any_failed() && final(self).protocol().cleanup_reply_enabled(out->Ok_0)
                && out->Ok_0.id==id && out->Ok_0.generation==work.origin().unwrap().generation
                && out->Ok_0.action==old(self).protocol().next_id(),
            final(groups).drained_failure()==old(groups).drained_failure(),
    {
        proof {reveal(Kernel::unchanged);self.actions.same_reflexive();}
        if !self.matches_execution(id,work,groups) || !work.is_idle() || groups.has_pending()
            || groups.has_issued() || !groups.can_retry_all() {return Err(Error::InvalidState);}
        let ticket=self.retry_cleanup(id)?;
        let _retried=groups.retry_all();assert(_retried);
        Ok(ticket)
    }

    /// No outcome or manifest is supplied by the host. Checking the bound
    /// episode precedes every mutation; wrong generations, pending work and
    /// retained failures leave lifecycle, work and all queues unchanged.
    pub fn release_execution<C,G,T>(&mut self,id:usize,work:&mut SetupWork<C,G>,groups:&mut CleanupGroups<T>)
        ->(out:Result<CleanupOutcome,Error>)
        requires old(self).wf(),old(work).wf(),old(groups).wf(),
        ensures final(self).wf(),final(work).wf(),final(groups).wf(),
            out.is_err() ==> final(self).same(old(self)) && *final(work)==*old(work) && *final(groups)==*old(groups),
            out.is_ok() ==> old(self).execution_matches(id,old(work),old(groups)) && old(work).idle() && old(groups).all_drained()
                && old(self).control().is_restoring(id)
                && out->Ok_0==if old(groups).drained_failure() {CleanupOutcome::Drained} else {CleanupOutcome::Succeeded}
                && final(work).is_closed() && final(groups).closed()
                && final(self).control().no_committed(id) && final(self).control().phase_of(id)==Some(Phase::Inactive)
                && !final(self).protocol().blocked_spec(id)
                && crate::refinement::step(old(self).control().paper(),final(self).control().paper(),id,crate::refinement::Rule::Unload),
    {
        proof {reveal(Kernel::unchanged);self.actions.same_reflexive();}
        if !self.matches_execution(id,work,groups) || !work.is_idle() || !groups.can_seal()
            || !self.kernel.cleanup_started(id) {return Err(Error::InvalidState);}
        let ticket=match self.pending(id) {Some(ticket)=>ticket,None=>return Err(Error::InvalidState)};
        if ticket.kind!=ActionKind::Cleanup || ticket.generation!=work.lifecycle_ticket().unwrap().generation {
            return Err(Error::InvalidState);
        }
        let outcome=if groups.has_consumed_failure() {CleanupOutcome::Drained} else {CleanupOutcome::Succeeded};
        let ghost prior=self.control();
        if self.complete_cleanup(ticket,outcome).is_err() {return Err(Error::InvalidState);}
        let _sealed=work.seal(groups);assert(_sealed);
        proof {
            reveal(Kernel::unchanged);reveal(Kernel::is_restoring);reveal(Kernel::generation_of);
            self.kernel.unchanged_observations(&prior);
        }
        let _finished=self.finish_cleanup(id);assert(_finished.is_ok());
        Ok(outcome)
    }
}
}
