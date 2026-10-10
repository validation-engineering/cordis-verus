//! Compose the real cleanup receipt gate, publication batch and L-Unload.
//! Callback reports remain host input. This function proves release authority
//! and mutation order for a checked resource manifest, not arbitrary effects.
use super::{CleanupOutcome, LifecycleActions};
use crate::publication::{
    LeaseId, LeaseOwner, PublicationError, PublicationId, PublicationRegistry, ReleasedPublication,
};
use crate::{Error, Kernel, Phase};
use vstd::prelude::*;

verus! {
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum CleanupReleaseError { Lifecycle(Error), Publication(PublicationError) }

impl LifecycleActions {
    pub closed spec fn resource_finish_enabled(&self,kernel:&Kernel,id:usize,reservation:bool)->bool {
        if reservation {self.reservation_finish_enabled(kernel,id)} else {self.finish_enabled(kernel,id)}
    }

    /// Read-only guard: Failed, absent, stale and still-Pending reports never
    /// authorize a resource mutation. Drained retains its explicit host policy.
    pub fn check_resource_finish(&self,kernel:&Kernel,id:usize,reservation:bool)->(out:Result<u64,Error>)
        requires self.wf(),kernel.wf(),
        ensures out.is_ok()==self.resource_finish_enabled(kernel,id,reservation),
            out.is_ok() ==> kernel.generation_of(id)==Some(out.unwrap()),
    {
        proof {
            reveal(LifecycleActions::wf);reveal(LifecycleActions::finish_enabled);
            reveal(LifecycleActions::reservation_finish_enabled);reveal(LifecycleActions::reservation);
            reveal(LifecycleActions::eligible);reveal(LifecycleActions::has_cleanup);
        }
        let generation=match kernel.episode_generation(id) {Some(g)=>g,None=>return Err(Error::InvalidState)};
        let i=match self.cleanup_index(id) {Some(i)=>i,None=>return Err(Error::InvalidState)};
        let record=self.cleanups[i];
        if record.ticket.generation!=generation || record.outcome.is_none()
            || record.outcome==Some(CleanupOutcome::Failed) {return Err(Error::InvalidState);}
        if reservation {
            if kernel.phase(id)!=Some(Phase::Inactive) || !kernel.retired(id) || generation!=0 {
                return Err(Error::InvalidState);
            }
        } else if !kernel.cleanup_started(id) {return Err(Error::InvalidState);}
        Ok(generation)
    }

    /// The actual resource batch must succeed before committed bindings are
    /// released. Rejected batches retain the receipt and entire prior state.
    pub fn finish_cleanup_resources(&mut self,kernel:&mut Kernel,registry:&mut PublicationRegistry,
        id:usize,reservation:bool,leases:&[LeaseId],publications:&[PublicationId])
        ->(out:Result<Vec<ReleasedPublication>,CleanupReleaseError>)
        requires old(self).wf(),old(kernel).wf(),old(registry).wf(),
        ensures final(self).wf(),final(kernel).wf(),final(registry).wf(),
            out.is_ok()==(old(registry).domain_id()==Some(old(self).domain_id()) && old(self).resource_finish_enabled(old(kernel),id,reservation)
                && old(registry).cleanup_batch_enabled(LeaseOwner {owner:id,generation:old(kernel).generation_of(id).unwrap()},leases@,publications@)),
            out.is_err() ==> final(self).same(old(self)) && final(kernel).unchanged(old(kernel))
                && final(registry).unchanged(old(registry)),
            out.is_ok() ==> final(registry).cleanup_batch_released(old(registry),leases@,publications@,out.unwrap()@)
                && final(registry).episode_resources_cleared(LeaseOwner {owner:id,generation:old(kernel).generation_of(id).unwrap()})
                && !final(self).blocked_spec(id),
            out.is_ok() && !reservation ==> final(kernel).no_committed(id)
                && final(kernel).phase_of(id)==Some(Phase::Inactive)
                && crate::refinement::step(old(kernel).paper(),final(kernel).paper(),id,crate::refinement::Rule::Unload),
            reservation ==> final(kernel).unchanged(old(kernel)),
    {
        reveal(LifecycleActions::same);reveal(Kernel::unchanged);proof {registry.unchanged_reflexive();}
        if registry.domain()!=Some(self.domain()) {
            return Err(CleanupReleaseError::Publication(PublicationError::InvalidState));
        }
        let generation=match self.check_resource_finish(kernel,id,reservation) {
            Ok(g)=>g,Err(e)=>return Err(CleanupReleaseError::Lifecycle(e)),
        };
        let released=match registry.cleanup_batch(LeaseOwner {owner:id,generation},leases,publications) {
            Ok(released)=>released,Err(e)=>return Err(CleanupReleaseError::Publication(e)),
        };
        if reservation {self.finish_reservation_cleanup(kernel,id).unwrap();}
        else {self.finish_cleanup(kernel,id).unwrap();}
        Ok(released)
    }
}
}
