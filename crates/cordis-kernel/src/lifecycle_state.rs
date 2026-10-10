//! Own the Kernel and action protocol as one verified, non-interchangeable state.
//! Hosts can inspect the Kernel but cannot replace it or borrow it mutably.
//! Callback execution, global domain allocation and value handles stay outside.
use crate::action_ledger::{ActionError, ActionTicket};
use crate::lifecycle_actions::resources::CleanupReleaseError;
use crate::lifecycle_actions::{CleanupOutcome, LifecycleActions};
#[cfg(verus_keep_ghost)]
use crate::publication::LeaseOwner;
use crate::publication::{LeaseId, PublicationId, PublicationRegistry, ReleasedPublication};
use crate::{Error, Kernel, Port};
use vstd::prelude::*;

verus! {
pub struct LifecycleState { kernel:Kernel, actions:LifecycleActions }

impl LifecycleState {
    pub closed spec fn wf(&self)->bool {self.kernel.wf() && self.actions.wf()}
    pub closed spec fn control(&self)->Kernel {self.kernel}
    pub closed spec fn protocol(&self)->LifecycleActions {self.actions}

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
    {self.actions.begin(&mut self.kernel,id)}

    pub fn complete_setup(&mut self,ticket:ActionTicket)->(out:Result<(),ActionError>)
        requires old(self).wf(),
        ensures final(self).wf(),
    {self.actions.complete_setup(ticket)}

    pub fn complete_cleanup(&mut self,ticket:ActionTicket,outcome:CleanupOutcome)->(out:Result<(),ActionError>)
        requires old(self).wf(),
        ensures final(self).wf(),
    {self.actions.complete_cleanup(ticket,outcome)}

    pub fn begin_cleanup(&mut self,id:usize)->(out:Result<ActionTicket,Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
    {self.actions.begin_cleanup(&mut self.kernel,id)}

    pub fn begin_reservation_cleanup(&mut self,id:usize)->(out:Result<ActionTicket,Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
    {self.actions.begin_reservation_cleanup(&self.kernel,id)}

    pub fn retry_cleanup(&mut self,id:usize)->(out:Result<ActionTicket,Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
    {self.actions.retry_cleanup(&self.kernel,id)}

    pub fn finish_cleanup(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
    {self.actions.finish_cleanup(&mut self.kernel,id)}

    pub fn finish_reservation_cleanup(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
    {self.actions.finish_reservation_cleanup(&self.kernel,id)}

    pub fn finish(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
    {if self.actions.blocked(id) {return Err(Error::InvalidState);} self.kernel.finish(id)}

    pub fn remove(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
    {if self.actions.blocked(id) {return Err(Error::InvalidState);} self.kernel.remove(id)}

    pub fn leave(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
    {self.kernel.leave(id)}

    pub fn retire(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),
    {self.kernel.retire(id)}

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
    {self.actions.finish_cleanup_resources(&mut self.kernel,registry,id,reservation,leases,publications)}
}
}
