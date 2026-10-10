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
use crate::{Binding, Phase};
use crate::{Error, Kernel, Port};
use vstd::prelude::*;

verus! {
pub struct LifecycleState { kernel:Kernel, actions:LifecycleActions }

impl LifecycleState {
    pub closed spec fn wf(&self)->bool {self.kernel.wf() && self.actions.wf()}
    pub closed spec fn control(&self)->Kernel {self.kernel}
    pub closed spec fn protocol(&self)->LifecycleActions {self.actions}
    pub closed spec fn same(&self,prior:&Self)->bool {
        self.kernel.unchanged(&prior.kernel) && self.actions.same(&prior.actions)
    }
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
        ensures out.wf(),out.protocol().domain_id()==domain,
    {Self {kernel:Kernel::new(),actions:LifecycleActions::new(domain)}}

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

    pub fn insert(&mut self,parent:Option<usize>,dependencies:Vec<Port>,provisions:Vec<Port>)->(out:Result<usize,Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
    {self.kernel.insert(parent,dependencies,provisions)}

    pub fn declare_provision(&mut self,id:usize,port:Port)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
    {self.kernel.declare_provision(id,port)}

    pub fn configure_pending_dependencies(&mut self,id:usize,dependencies:Vec<Port>)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
    {self.kernel.configure_pending_dependencies(id,dependencies)}

    pub fn release_provision(&mut self,id:usize,port:Port)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
    {self.kernel.release_provision(id,port)}

    pub fn begin(&mut self,id:usize)->(out:Result<ActionTicket,Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
            out.is_ok()==(old(self).protocol().admission_enabled(id) && old(self).control().begin_enabled(id)),
            out.is_err() ==> final(self).same(old(self)),
            final(self).protocol().history_preserved(&old(self).protocol()),
            final(self).protocol().no_new_release(&old(self).protocol()),
            out.is_ok() ==> out.unwrap().kind==crate::action_ledger::ActionKind::Setup
                && out.unwrap().id==id && out.unwrap().domain==old(self).protocol().domain_id()
                && final(self).protocol().recorded(out.unwrap())
                && final(self).control().generation_of(id)==Some(out.unwrap().generation),
    {self.actions.begin(&mut self.kernel,id)}

    pub fn complete_setup(&mut self,ticket:ActionTicket)->(out:Result<(),ActionError>)
        requires old(self).wf(),
        ensures final(self).wf(),
            out.is_ok()==(ticket.kind==crate::action_ledger::ActionKind::Setup && old(self).protocol().recorded(ticket)),
            out.is_err() ==> final(self).same(old(self)),
            final(self).control().unchanged(&old(self).control()),
            final(self).protocol().history_preserved(&old(self).protocol()),
            final(self).protocol().no_new_release(&old(self).protocol()),
            out.is_ok() ==> !final(self).protocol().recorded(ticket),
    {self.actions.complete_setup(ticket)}

    pub fn complete_cleanup(&mut self,ticket:ActionTicket,outcome:CleanupOutcome)->(out:Result<(),ActionError>)
        requires old(self).wf(),
        ensures final(self).wf(),
            out.is_ok()==old(self).protocol().cleanup_reply_enabled(ticket),
            out.is_err() ==> final(self).same(old(self)),
            final(self).control().unchanged(&old(self).control()),
            final(self).protocol().history_preserved(&old(self).protocol()),
            out.is_ok() ==> ticket.kind==crate::action_ledger::ActionKind::Cleanup && old(self).protocol().recorded(ticket)
                && final(self).protocol().reported(ticket,outcome) && !final(self).protocol().outstanding(ticket.id) && !final(self).protocol().recorded(ticket)
                && final(self).protocol().eligible(ticket.id,ticket.generation)==(outcome!=CleanupOutcome::Failed),
            forall|id:usize,g:u64| final(self).protocol().eligible(id,g) ==> old(self).protocol().eligible(id,g)
                || (out.is_ok() && id==ticket.id && g==ticket.generation && outcome!=CleanupOutcome::Failed),
    {self.actions.complete_cleanup(ticket,outcome)}

    pub fn begin_cleanup(&mut self,id:usize)->(out:Result<ActionTicket,Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
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
    {self.actions.begin_cleanup(&mut self.kernel,id)}

    pub fn begin_reservation_cleanup(&mut self,id:usize)->(out:Result<ActionTicket,Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
            out.is_ok()==(old(self).protocol().admission_enabled(id) && LifecycleActions::reservation(&old(self).control(),id)),
            out.is_err() ==> final(self).same(old(self)),
            final(self).control().unchanged(&old(self).control()),
            final(self).protocol().history_preserved(&old(self).protocol()),
            final(self).protocol().no_new_release(&old(self).protocol()),
            out.is_ok() ==> out.unwrap().kind==crate::action_ledger::ActionKind::Cleanup && out.unwrap().id==id
                && out.unwrap().domain==old(self).protocol().domain_id() && out.unwrap().action==old(self).protocol().next_id()
                && out.unwrap().generation==0 && final(self).protocol().cleanup_reply_enabled(out.unwrap()),
    {self.actions.begin_reservation_cleanup(&self.kernel,id)}

    pub fn retry_cleanup(&mut self,id:usize)->(out:Result<ActionTicket,Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
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
    {self.actions.retry_cleanup(&self.kernel,id)}

    pub fn finish_cleanup(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
            out.is_ok()==old(self).protocol().finish_enabled(&old(self).control(),id),
            out.is_err() ==> final(self).same(old(self)),
            final(self).protocol().history_preserved(&old(self).protocol()),
            final(self).protocol().no_new_release(&old(self).protocol()),
            final(self).bindings_except(old(self),Some(id)),
            out.is_ok() ==> final(self).control().no_committed(id) && final(self).control().phase_of(id)==Some(Phase::Inactive)
                && !final(self).protocol().blocked_spec(id)
                && crate::refinement::step(old(self).control().paper(),final(self).control().paper(),id,crate::refinement::Rule::Unload),
    {reveal(Kernel::commitments_frame);self.actions.finish_cleanup(&mut self.kernel,id)}

    pub fn finish_reservation_cleanup(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
            out.is_ok()==old(self).protocol().reservation_finish_enabled(&old(self).control(),id),
            out.is_err() ==> final(self).same(old(self)),
            final(self).control().unchanged(&old(self).control()),
            final(self).protocol().history_preserved(&old(self).protocol()),
            final(self).protocol().no_new_release(&old(self).protocol()),
            out.is_ok() ==> !final(self).protocol().blocked_spec(id),
    {self.actions.finish_reservation_cleanup(&self.kernel,id)}

    pub fn finish(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
    {if self.actions.blocked(id) {return Err(Error::InvalidState);} self.kernel.finish(id)}

    pub fn remove(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
            out.is_err() ==> final(self).same(old(self)),
            final(self).control().same_bindings(&old(self).control()),
            final(self).protocol().same(&old(self).protocol()),
            out.is_ok() ==> !old(self).protocol().blocked_spec(id) && !final(self).control().registered(id),
    {reveal(Kernel::unchanged);proof {self.actions.same_reflexive();} if self.actions.blocked(id) {return Err(Error::InvalidState);} self.kernel.remove(id)}

    pub fn leave(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
            out.is_err() ==> final(self).same(old(self)),
            final(self).control().same_bindings(&old(self).control()),
            final(self).protocol().same(&old(self).protocol()),
    {proof {self.actions.same_reflexive();} self.kernel.leave(id)}

    pub fn retire(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
            out.is_err() ==> final(self).same(old(self)),
            final(self).control().same_bindings(&old(self).control()),
            final(self).protocol().same(&old(self).protocol()),
    {proof {self.actions.same_reflexive();} self.kernel.retire(id)}

    pub fn compact_bindings(&mut self)->(out:usize)
        requires old(self).wf(),
        ensures final(self).wf(),
    {self.kernel.compact_bindings()}

    pub fn compact_declarations(&mut self)->(out:usize)
        requires old(self).wf(),
        ensures final(self).wf(),
    {self.kernel.compact_declarations()}

    /// The host cannot pass a different Kernel to the cleanup receipt protocol.
    pub fn finish_cleanup_resources(&mut self,registry:&mut PublicationRegistry,id:usize,
        reservation:bool,leases:&[LeaseId],publications:&[PublicationId])
        ->(out:Result<Vec<ReleasedPublication>,CleanupReleaseError>)
        requires old(self).wf(),old(registry).wf(),
        ensures final(self).wf(),final(registry).wf(),
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
        let out=self.actions.finish_cleanup_resources(&mut self.kernel,registry,id,reservation,leases,publications);
        proof {
            reveal(Kernel::commitments_frame);reveal(Kernel::unchanged);reveal(Kernel::binding_recorded);
            if out.is_err() {self.same_observations(&prior);}
        }
        out
    }
}
}

#[path = "cleanup_protocol.rs"]
pub mod cleanup;
