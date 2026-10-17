//! Own the Kernel and action protocol as one verified, non-interchangeable state.
//! Hosts can inspect the Kernel but cannot replace it or borrow it mutably.
//! Callback execution, global domain allocation and value handles stay outside.
use crate::action_ledger::{ActionError, ActionTicket};
use crate::lifecycle_actions::resources::CleanupReleaseError;
use crate::lifecycle_actions::{CleanupOutcome, LifecycleActions};
#[cfg(verus_keep_ghost)]
use crate::publication::LeaseOwner;
use crate::publication::{LeaseId, PublicationId, PublicationRegistry, ReleasedPublication};
#[cfg(verus_keep_ghost)]
use crate::Binding;
use crate::{Error, Kernel, Phase, Port};
use vstd::prelude::*;
#[path = "control_history.rs"]
pub mod history;
use history::History;
#[cfg(verus_keep_ghost)]
use history::Label;

verus! {
#[allow(dead_code)] // Control history is erased from executable Cargo builds.
pub struct LifecycleState { kernel:Kernel, actions:LifecycleActions,history:Ghost<History> }

impl LifecycleState {
    pub closed spec fn control_history(&self)->History {self.history@}
    pub closed spec fn wf(&self)->bool {self.kernel.wf() && self.actions.wf() && self.control_history_valid()}
    pub closed spec fn control(&self)->Kernel {self.kernel}
    pub closed spec fn protocol(&self)->LifecycleActions {self.actions}
    pub closed spec fn same(&self,prior:&Self)->bool {
        self.kernel.unchanged(&prior.kernel) && self.actions.same(&prior.actions)
    }
    pub proof fn same_components(&self,prior:&Self)
        requires self.same(prior),
        ensures self.control().unchanged(&prior.control()),self.protocol().same(&prior.protocol()),
    {}
    pub proof fn same_reflexive(&self)
        ensures self.same(self),self.control().unchanged(&self.control()),self.protocol().same(&self.protocol()),
    {reveal(Kernel::unchanged);self.actions.same_reflexive();}
    pub open spec fn bindings_except(&self,prior:&Self,released:Option<usize>)->bool {
        forall|id:usize,b:Binding| released!=Some(id) ==>
            self.control().binding_recorded(id,b)==prior.control().binding_recorded(id,b)
    }
    pub proof fn same_observations(&self,prior:&Self)
        requires self.same(prior),
        ensures self.bindings_except(prior,None),self.protocol().history_preserved(&prior.protocol()),
            self.protocol().no_new_release(&prior.protocol()),
    {reveal(Kernel::unchanged);reveal(Kernel::binding_recorded);self.actions.same_observations(&prior.actions);}


    pub fn new(domain:u64)->(out:Self)
        ensures out.wf(),out.protocol().domain_id()==domain,out.control().paper().fibers.dom().is_empty(),
            out.protocol().next_id()==1,forall|id:usize|!out.protocol().blocked_spec(id),
    {let kernel=Kernel::new();let ghost states=seq![kernel.paper()];
        Self {kernel,actions:LifecycleActions::new(domain),history:Ghost(History {states,labels:Seq::empty()})}}

    pub fn kernel(&self)->(out:&Kernel)
        requires self.wf(),
        ensures *out==self.control(),out.wf(),
    {&self.kernel}

    pub fn domain(&self)->(out:u64)
        ensures out==self.protocol().domain_id(),
    {self.actions.domain()}

    pub fn blocked(&self,id:usize)->(out:bool)
        ensures out==self.protocol().blocked_spec(id),
    {self.actions.blocked(id)}

    pub fn pending(&self,id:usize)->(out:Option<ActionTicket>)
        ensures out.is_some() ==> self.protocol().recorded(out.unwrap()) && out.unwrap().id==id,
            out.is_none()==!self.protocol().outstanding(id),
    {self.actions.pending(id)}

    pub fn check_capacity(&self,count:u64)->(out:Result<(),ActionError>)
        ensures out.is_ok()==self.protocol().capacity_enabled(count),
    {self.actions.check_capacity(count)}

    /// Managed service admission includes the explicit generation-zero
    /// reservation extension. Hosts may impose additional preparation policy.
    pub open spec fn service_open(&self,id:usize,generation:u64)->bool {
        self.control().registered(id) && self.control().generation_of(id)==Some(generation)
            && !self.control().is_retired(id)
            && (self.control().phase_of(id)==Some(Phase::Loading)
                || self.control().phase_of(id)==Some(Phase::Active)
                || (generation==0 && self.control().phase_of(id)==Some(Phase::Inactive)))
    }
    pub fn check_service_access(&self,id:usize,generation:u64)->(out:Result<(),Error>)
        requires self.wf(),ensures out.is_ok()==self.service_open(id,generation),
    {
        if !self.kernel.contains(id) {return Err(Error::Unknown);}
        if self.kernel.episode_generation(id)!=Some(generation) {return Err(Error::InvalidState);}
        if self.kernel.retired(id) {return Err(Error::Retired);}
        match self.kernel.phase(id) {
            Some(Phase::Loading)|Some(Phase::Active)=>Ok(()),
            Some(Phase::Inactive) if generation==0=>Ok(()),
            _=>Err(Error::InvalidState),
        }
    }

    pub fn insert(&mut self,parent:Option<usize>,dependencies:Vec<Port>,provisions:Vec<Port>)->(out:Result<usize,Error>)
        requires old(self).wf(),
        ensures final(self).control().generations_preserved(&old(self).control()), final(self).wf(),final(self).control_history().extends(old(self).control_history()),final(self).protocol().same(&old(self).protocol()),
            out.is_ok()==old(self).control().insert_enabled(parent,dependencies@,provisions@),
            out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> out->Ok_0==old(self).control().next_id()
                && crate::refinement::step(old(self).control().paper(),final(self).control().paper(),out->Ok_0,crate::refinement::Rule::Insert)
                && final(self).control().paper().fibers[out->Ok_0].parent==parent
                && (forall|p:Port| final(self).control().paper().fibers[out->Ok_0].dependencies.contains(p)==dependencies@.contains(p))
                && (forall|p:Port| final(self).control().paper().fibers[out->Ok_0].provisions.contains(p)==provisions@.contains(p)),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let ghost prior=self.control();
        proof {self.actions.same_reflexive();}
        let out=self.kernel.insert(parent,dependencies,provisions);
        proof {
            let label=if out.is_ok() {Label::Paper {actor:out->Ok_0,rule:crate::refinement::Rule::Insert}} else {Label::Internal};
            reveal(Kernel::unchanged);reveal(Kernel::commitments_frame);if self.kernel.unchanged(&prior) {self.kernel.unchanged_observations(&prior);}
            self.record_control(prior.paper(),label);
        }
        out
    }

    pub fn declare_provision(&mut self,id:usize,port:Port)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).control_history().labels.last()==if out.is_ok() {Label::Declare {actor:id,port}} else {Label::Internal},final(self).wf(),final(self).control_history().extends(old(self).control_history()),final(self).protocol().same(&old(self).protocol()),
            final(self).control().same_control(&old(self).control()),final(self).control().same_bindings(&old(self).control()),
            out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> final(self).control().declares_provision(id,port),
    {
        let ghost prior=self.control();
        proof {self.actions.same_reflexive();}
        let out=self.kernel.declare_provision(id,port);
        proof {
            let label=if out.is_ok() {Label::Declare {actor:id,port}} else {Label::Internal};
            reveal(Kernel::unchanged);reveal(Kernel::commitments_frame);if out.is_ok() {self.kernel.interface_history(&prior,label);} else {self.kernel.unchanged_observations(&prior);}
            self.record_control(prior.paper(),label);
        }
        out
    }

    pub fn configure_pending_dependencies(&mut self,id:usize,dependencies:Vec<Port>)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).control_history().labels.last()==if out.is_ok() {Label::Dependencies {actor:id,ports:dependencies@.to_set().to_iset()}} else {Label::Internal},final(self).wf(),final(self).control_history().extends(old(self).control_history()),final(self).protocol().same(&old(self).protocol()),
            final(self).control().same_control(&old(self).control()),final(self).control().same_bindings(&old(self).control()),
            out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> old(self).control().registered(id) && final(self).control().pending_dependencies_configured(&old(self).control(),id,dependencies@),
    {
        let ghost prior=self.control();let ghost ports=dependencies@;
        proof {self.actions.same_reflexive();}
        let out=self.kernel.configure_pending_dependencies(id,dependencies);
        proof {
            let label=if out.is_ok() {Label::Dependencies {actor:id,ports:ports.to_set().to_iset()}} else {Label::Internal};
            reveal(Kernel::unchanged);reveal(Kernel::commitments_frame);if out.is_ok() {self.kernel.dependencies_history(&prior,id,ports);} else {self.kernel.unchanged_observations(&prior);}
            self.record_control(prior.paper(),label);
        }
        out
    }

    pub fn release_provision(&mut self,id:usize,port:Port)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).control_history().labels.last()==if out.is_ok() {Label::Release {actor:id,port}} else {Label::Internal},final(self).wf(),final(self).control_history().extends(old(self).control_history()),final(self).protocol().same(&old(self).protocol()),
            final(self).control().same_control(&old(self).control()),final(self).control().same_bindings(&old(self).control()),
            out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> final(self).control().provision_released_from(&old(self).control(),id,port) && !final(self).control().declares_provision(id,port) && final(self).control().other_interfaces_preserved(&old(self).control(),id,port),
    {
        let ghost prior=self.control();
        proof {self.actions.same_reflexive();}
        let out=self.kernel.release_provision(id,port);
        proof {
            let label=if out.is_ok() {Label::Release {actor:id,port}} else {Label::Internal};
            reveal(Kernel::unchanged);reveal(Kernel::commitments_frame);if out.is_ok() {self.kernel.interface_history(&prior,label);} else {self.kernel.unchanged_observations(&prior);}
            self.record_control(prior.paper(),label);
        }
        out
    }

    pub fn begin(&mut self,id:usize)->(out:Result<ActionTicket,Error>)
        requires old(self).wf(),
        ensures (forall|n:usize| n!=id ==> final(self).control().generation_of(n)==old(self).control().generation_of(n)), final(self).wf(),final(self).control_history().extends(old(self).control_history()),
            out.is_ok()==(old(self).protocol().admission_enabled(id) && old(self).control().begin_enabled(id)),
            out.is_err() ==> final(self).same(old(self)),
            final(self).protocol().history_preserved(&old(self).protocol()),
            final(self).protocol().no_new_release(&old(self).protocol()),
            out.is_ok() ==> out.unwrap().kind==crate::action_ledger::ActionKind::Setup
                && out.unwrap().id==id && out.unwrap().domain==old(self).protocol().domain_id()
                && final(self).protocol().recorded(out.unwrap())
                && final(self).control().generation_of(id)==Some(out.unwrap().generation)
                && old(self).control().generation_of(id).is_some()
                && out.unwrap().generation as nat==old(self).control().generation_of(id).unwrap() as nat+1
                && final(self).control().committed_from(&old(self).control(),id)
                && crate::refinement::step(old(self).control().paper(),final(self).control().paper(),id,crate::refinement::Rule::Begin),
    {
        let ghost prior=self.control();
        proof {self.actions.same_reflexive();}
        let out=self.actions.begin(&mut self.kernel,id);
        proof {
            let label=if out.is_ok() {Label::Paper {actor:id,rule:crate::refinement::Rule::Begin}} else {Label::Internal};
            reveal(Kernel::unchanged);reveal(Kernel::commitments_frame);if self.kernel.unchanged(&prior) {self.kernel.unchanged_observations(&prior);}
            self.record_control(prior.paper(),label);
        }
        out
    }

    pub fn complete_setup(&mut self,ticket:ActionTicket)->(out:Result<(),ActionError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).control_history().extends(old(self).control_history()),
            out.is_ok()==(ticket.kind==crate::action_ledger::ActionKind::Setup && old(self).protocol().recorded(ticket)),
            out.is_err() ==> final(self).same(old(self)),
            final(self).control().unchanged(&old(self).control()),
            final(self).protocol().history_preserved(&old(self).protocol()),
            final(self).protocol().no_new_release(&old(self).protocol()),
            out.is_ok() ==> !final(self).protocol().recorded(ticket) && !final(self).protocol().outstanding(ticket.id),
    {
        let ghost prior=self.control();
        proof {self.actions.same_reflexive();}
        let out=self.actions.complete_setup(ticket);
        proof {
            let label=Label::Internal;
            reveal(Kernel::unchanged);reveal(Kernel::commitments_frame);if self.kernel.unchanged(&prior) {self.kernel.unchanged_observations(&prior);}
            self.record_control(prior.paper(),label);
        }
        out
    }

    pub fn complete_cleanup(&mut self,ticket:ActionTicket,outcome:CleanupOutcome)->(out:Result<(),ActionError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).control_history().extends(old(self).control_history()),
            out.is_ok()==old(self).protocol().cleanup_reply_enabled(ticket),
            out.is_err() ==> final(self).same(old(self)),
            final(self).control().unchanged(&old(self).control()),
            final(self).protocol().history_preserved(&old(self).protocol()),
            out.is_ok() ==> ticket.kind==crate::action_ledger::ActionKind::Cleanup && old(self).protocol().recorded(ticket)
                && final(self).protocol().reported(ticket,outcome) && !final(self).protocol().outstanding(ticket.id) && !final(self).protocol().recorded(ticket)
                && final(self).protocol().eligible(ticket.id,ticket.generation)==(outcome!=CleanupOutcome::Failed),
            forall|id:usize,g:u64| final(self).protocol().eligible(id,g) ==> old(self).protocol().eligible(id,g)
                || (out.is_ok() && id==ticket.id && g==ticket.generation && outcome!=CleanupOutcome::Failed),
    {
        let ghost prior=self.control();
        proof {self.actions.same_reflexive();}
        let out=self.actions.complete_cleanup(ticket,outcome);
        proof {
            let label=Label::Internal;
            reveal(Kernel::unchanged);reveal(Kernel::commitments_frame);if self.kernel.unchanged(&prior) {self.kernel.unchanged_observations(&prior);}
            self.record_control(prior.paper(),label);
        }
        out
    }

    pub fn begin_cleanup(&mut self,id:usize)->(out:Result<ActionTicket,Error>)
        requires old(self).wf(),
        ensures final(self).control().generations_preserved(&old(self).control()), final(self).wf(),final(self).control_history().extends(old(self).control_history()),
            out.is_ok()==(old(self).protocol().admission_enabled(id) && old(self).control().cleanup_enabled(id)),
            out.is_err() ==> final(self).same(old(self)),
            final(self).control().same_bindings(&old(self).control()),
            final(self).control().paper()==old(self).control().paper(),
            final(self).protocol().history_preserved(&old(self).protocol()),
            final(self).protocol().no_new_release(&old(self).protocol()),
            out.is_ok() ==> out.unwrap().kind==crate::action_ledger::ActionKind::Cleanup && out.unwrap().id==id
                && out.unwrap().domain==old(self).protocol().domain_id() && out.unwrap().action==old(self).protocol().next_id()
                && final(self).protocol().cleanup_reply_enabled(out.unwrap())
                && final(self).control().generation_of(id)==Some(out.unwrap().generation)
                && final(self).control().restoration_guarded(id),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let ghost prior=self.control();
        proof {self.actions.same_reflexive();}
        let out=self.actions.begin_cleanup(&mut self.kernel,id);
        proof {
            let label=Label::Internal;
            reveal(Kernel::unchanged);reveal(Kernel::commitments_frame);if self.kernel.unchanged(&prior) {self.kernel.unchanged_observations(&prior);}
            self.record_control(prior.paper(),label);
        }
        out
    }

    pub fn begin_reservation_cleanup(&mut self,id:usize)->(out:Result<ActionTicket,Error>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).control_history().extends(old(self).control_history()),
            out.is_ok()==(old(self).protocol().admission_enabled(id) && LifecycleActions::reservation(&old(self).control(),id)),
            out.is_err() ==> final(self).same(old(self)),
            final(self).control().unchanged(&old(self).control()),
            final(self).protocol().history_preserved(&old(self).protocol()),
            final(self).protocol().no_new_release(&old(self).protocol()),
            out.is_ok() ==> out.unwrap().kind==crate::action_ledger::ActionKind::Cleanup && out.unwrap().id==id
                && out.unwrap().domain==old(self).protocol().domain_id() && out.unwrap().action==old(self).protocol().next_id()
                && out.unwrap().generation==0 && final(self).protocol().cleanup_reply_enabled(out.unwrap()),
    {
        let ghost prior=self.control();
        proof {self.actions.same_reflexive();}
        let out=self.actions.begin_reservation_cleanup(&self.kernel,id);
        proof {
            let label=Label::Internal;
            reveal(Kernel::unchanged);reveal(Kernel::commitments_frame);if self.kernel.unchanged(&prior) {self.kernel.unchanged_observations(&prior);}
            self.record_control(prior.paper(),label);
        }
        out
    }

    pub fn retry_cleanup(&mut self,id:usize)->(out:Result<ActionTicket,Error>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).control_history().extends(old(self).control_history()),
            out.is_ok()==old(self).protocol().retry_enabled(&old(self).control(),id),
            out.is_err() ==> final(self).same(old(self)),
            final(self).control().unchanged(&old(self).control()),
            final(self).protocol().history_preserved(&old(self).protocol()),
            final(self).protocol().no_new_release(&old(self).protocol()),
            out.is_ok() ==> out.unwrap().kind==crate::action_ledger::ActionKind::Cleanup && out.unwrap().id==id
                && out.unwrap().domain==old(self).protocol().domain_id() && out.unwrap().action==old(self).protocol().next_id()
                && final(self).control().generation_of(id)==Some(out.unwrap().generation)
                && old(self).protocol().failed(id,out.unwrap().generation)
                && !final(self).protocol().eligible(id,out.unwrap().generation)
                && final(self).protocol().cleanup_reply_enabled(out.unwrap()),
    {
        let ghost prior=self.control();
        proof {self.actions.same_reflexive();}
        let out=self.actions.retry_cleanup(&self.kernel,id);
        proof {
            let label=Label::Internal;
            reveal(Kernel::unchanged);reveal(Kernel::commitments_frame);if self.kernel.unchanged(&prior) {self.kernel.unchanged_observations(&prior);}
            self.record_control(prior.paper(),label);
        }
        out
    }

    pub fn finish_cleanup(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).control().generations_preserved(&old(self).control()), final(self).wf(),final(self).control_history().extends(old(self).control_history()),
            out.is_ok()==old(self).protocol().finish_enabled(&old(self).control(),id),
            out.is_err() ==> final(self).same(old(self)),
            final(self).protocol().history_preserved(&old(self).protocol()),
            final(self).protocol().no_new_release(&old(self).protocol()),
            final(self).bindings_except(old(self),Some(id)),
            out.is_ok() ==> final(self).control().no_committed(id) && final(self).control().phase_of(id)==Some(Phase::Inactive)
                && !final(self).protocol().blocked_spec(id)
                && crate::refinement::step(old(self).control().paper(),final(self).control().paper(),id,crate::refinement::Rule::Unload),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let ghost prior=self.control();
        proof {self.actions.same_reflexive();}
        let out=self.actions.finish_cleanup(&mut self.kernel,id);
        proof {
            let label=if out.is_ok() {Label::Paper {actor:id,rule:crate::refinement::Rule::Unload}} else {Label::Internal};
            reveal(Kernel::unchanged);reveal(Kernel::commitments_frame);if self.kernel.unchanged(&prior) {self.kernel.unchanged_observations(&prior);}
            self.record_control(prior.paper(),label);
        }
        out
    }

    pub fn finish_reservation_cleanup(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).control_history().extends(old(self).control_history()),
            out.is_ok()==old(self).protocol().reservation_finish_enabled(&old(self).control(),id),
            out.is_err() ==> final(self).same(old(self)),
            final(self).control().unchanged(&old(self).control()),
            final(self).protocol().history_preserved(&old(self).protocol()),
            final(self).protocol().no_new_release(&old(self).protocol()),
            out.is_ok() ==> !final(self).protocol().blocked_spec(id),
    {
        let ghost prior=self.control();
        proof {self.actions.same_reflexive();}
        let out=self.actions.finish_reservation_cleanup(&self.kernel,id);
        proof {
            let label=Label::Internal;
            reveal(Kernel::unchanged);reveal(Kernel::commitments_frame);if self.kernel.unchanged(&prior) {self.kernel.unchanged_observations(&prior);}
            self.record_control(prior.paper(),label);
        }
        out
    }

    pub fn finish(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).control().generations_preserved(&old(self).control()), final(self).wf(),final(self).control_history().extends(old(self).control_history()),final(self).protocol().same(&old(self).protocol()),
            out.is_ok()==(!old(self).protocol().blocked_spec(id) && old(self).control().iteration_enabled(id)),
            out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> final(self).control().phase_of(id)==Some(Phase::Active)
                && crate::refinement::step(old(self).control().paper(),final(self).control().paper(),id,crate::refinement::Rule::Finish),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let ghost prior=self.control();
        proof {self.actions.same_reflexive();}
        let out=if self.actions.blocked(id) {Err(Error::InvalidState)} else {self.kernel.finish(id)};
        proof {
            let label=if out.is_ok() {Label::Paper {actor:id,rule:crate::refinement::Rule::Finish}} else {Label::Internal};
            reveal(Kernel::unchanged);reveal(Kernel::commitments_frame);if self.kernel.unchanged(&prior) {self.kernel.unchanged_observations(&prior);}
            self.record_control(prior.paper(),label);
        }
        out
    }

    pub fn remove(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).control().generations_preserved(&old(self).control()), final(self).wf(),final(self).control_history().extends(old(self).control_history()),
            out.is_err() ==> final(self).same(old(self)),
            final(self).control().same_bindings(&old(self).control()),
            final(self).protocol().same(&old(self).protocol()),
            out.is_ok() ==> !old(self).protocol().blocked_spec(id) && !final(self).control().registered(id)
                && crate::refinement::step(old(self).control().paper(),final(self).control().paper(),id,crate::refinement::Rule::Remove),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let ghost prior=self.control();
        proof {self.actions.same_reflexive();}
        let out=if self.actions.blocked(id) {Err(Error::InvalidState)} else {self.kernel.remove(id)};
        proof {
            let label=if out.is_ok() {Label::Paper {actor:id,rule:crate::refinement::Rule::Remove}} else {Label::Internal};
            reveal(Kernel::unchanged);reveal(Kernel::commitments_frame);if self.kernel.unchanged(&prior) {self.kernel.unchanged_observations(&prior);}
            self.record_control(prior.paper(),label);
        }
        out
    }

    pub fn leave(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).control().generations_preserved(&old(self).control()), final(self).wf(),final(self).control_history().extends(old(self).control_history()),
            out.is_err() ==> final(self).same(old(self)),
            final(self).control().same_bindings(&old(self).control()),
            final(self).protocol().same(&old(self).protocol()),
            out.is_ok() ==> crate::refinement::step(old(self).control().paper(),final(self).control().paper(),id,crate::refinement::Rule::Restart),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let ghost prior=self.control();
        proof {self.actions.same_reflexive();}
        let out=self.kernel.leave(id);
        proof {
            let label=if out.is_ok() {history::withdrawal(prior.paper(),id)} else {Label::Internal};
            reveal(Kernel::unchanged);reveal(Kernel::commitments_frame);if self.kernel.unchanged(&prior) {self.kernel.unchanged_observations(&prior);}
            if out.is_ok() {history::withdrawal_classified(prior.paper(),self.control().paper(),id);}
            self.record_control(prior.paper(),label);
        }
        out
    }

    pub fn retire(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).control().generations_preserved(&old(self).control()), final(self).wf(),final(self).control_history().extends(old(self).control_history()),
            out.is_err() ==> final(self).same(old(self)),
            final(self).control().same_bindings(&old(self).control()),
            final(self).protocol().same(&old(self).protocol()),
            out.is_ok() ==> crate::refinement::step(old(self).control().paper(),final(self).control().paper(),id,crate::refinement::Rule::Retire),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let ghost prior=self.control();
        proof {self.actions.same_reflexive();}
        let out=self.kernel.retire(id);
        proof {
            let label=if out.is_ok() {Label::Paper {actor:id,rule:crate::refinement::Rule::Retire}} else {Label::Internal};
            reveal(Kernel::unchanged);reveal(Kernel::commitments_frame);if self.kernel.unchanged(&prior) {self.kernel.unchanged_observations(&prior);}
            self.record_control(prior.paper(),label);
        }
        out
    }

    pub fn compact_bindings(&mut self)->(out:usize)
        requires old(self).wf(),
        ensures final(self).control().generations_preserved(&old(self).control()), final(self).wf(),final(self).control_history().extends(old(self).control_history()),final(self).protocol().same(&old(self).protocol()),
            final(self).control().paper()==old(self).control().paper(),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let ghost prior=self.control();
        proof {self.actions.same_reflexive();}
        let out=self.kernel.compact_bindings();
        proof {
            let label=Label::Internal;
            reveal(Kernel::unchanged);reveal(Kernel::commitments_frame);if self.kernel.unchanged(&prior) {self.kernel.unchanged_observations(&prior);}
            self.record_control(prior.paper(),label);
        }
        out
    }

    pub fn compact_declarations(&mut self)->(out:usize)
        requires old(self).wf(),
        ensures final(self).control().generations_preserved(&old(self).control()), final(self).wf(),final(self).control_history().extends(old(self).control_history()),final(self).protocol().same(&old(self).protocol()),
            final(self).control().paper()==old(self).control().paper(),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let ghost prior=self.control();
        proof {self.actions.same_reflexive();}
        let out=self.kernel.compact_declarations();
        proof {
            let label=Label::Internal;
            reveal(Kernel::unchanged);reveal(Kernel::commitments_frame);if self.kernel.unchanged(&prior) {self.kernel.unchanged_observations(&prior);}
            self.record_control(prior.paper(),label);
        }
        out
    }

    /// The host cannot pass a different Kernel to the cleanup receipt protocol.
    pub fn finish_cleanup_resources(&mut self,registry:&mut PublicationRegistry,id:usize,
        reservation:bool,leases:&[LeaseId],publications:&[PublicationId])
        ->(out:Result<Vec<ReleasedPublication>,CleanupReleaseError>)
        requires old(self).wf(),old(registry).wf(),
        ensures final(self).wf(),final(self).control_history().extends(old(self).control_history()),final(registry).wf(),final(registry).domain_id()==old(registry).domain_id(),
            out.is_ok()==(old(registry).domain_id()==Some(old(self).protocol().domain_id())
                && old(self).protocol().resource_finish_enabled(&old(self).control(),id,reservation)
                && old(registry).cleanup_batch_enabled(LeaseOwner {owner:id,generation:old(self).control().generation_of(id).unwrap()},leases@,publications@)),
            out.is_err() ==> final(self).control().unchanged(&old(self).control())
                && final(self).protocol().same(&old(self).protocol()) && final(registry).unchanged(old(registry)),
            out.is_ok() ==> old(self).protocol().resource_finish_enabled(&old(self).control(),id,reservation)
                && final(registry).cleanup_batch_released(old(registry),leases@,publications@,out.unwrap()@)
                && final(registry).episode_resources_cleared(LeaseOwner {owner:id,generation:old(self).control().generation_of(id).unwrap()})
                && old(registry).domain_id()==Some(old(self).protocol().domain_id())
                && !final(self).protocol().blocked_spec(id),
            out.is_ok() && !reservation ==> final(self).control().no_committed(id)
                && crate::refinement::step(old(self).control().paper(),final(self).control().paper(),id,crate::refinement::Rule::Unload),
            reservation ==> final(self).control().unchanged(&old(self).control()),
            final(self).cleanup_step(old(self),cleanup::CleanupCommand::Release {id,reservation},cleanup::resource_reply(out)),
    {
        let ghost prior=*self;
        proof {}
        let out=self.actions.finish_cleanup_resources(&mut self.kernel,registry,id,reservation,leases,publications);
        proof {
            reveal(Kernel::commitments_frame);reveal(Kernel::unchanged);reveal(Kernel::binding_recorded);
            if out.is_err() {self.same_observations(&prior);}
            if out.is_err() || reservation {self.kernel.unchanged_observations(&prior.control());}
            self.record_control(prior.control().paper(),if out.is_ok() && !reservation {
                Label::Paper {actor:id,rule:crate::refinement::Rule::Unload}
            } else {Label::Internal});
        }
        out
    }
}
}

#[path = "cleanup_protocol.rs"]
pub mod cleanup;

#[path = "execution_lifecycle.rs"]
pub mod execution;

#[path = "plugin_registration.rs"]
pub mod registration;

#[path = "native_values.rs"]
pub mod services;

#[path = "native_host.rs"]
pub mod native;
