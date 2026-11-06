//! Compose the real cleanup receipt gate, publication batch and L-Unload.
//! Callback reports remain host input. This function proves release authority
//! and mutation order for a checked resource manifest, not arbitrary effects.
use super::LifecycleActions;
use crate::publication::{
    LeaseId, LeaseOwner, PublicationError, PublicationId, PublicationRegistry, ReleasedPublication,
};
#[cfg(verus_keep_ghost)]
use crate::Phase;
use crate::{Error, Kernel};
use vstd::prelude::*;

verus! {
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum CleanupReleaseError { Lifecycle(Error), Publication(PublicationError) }

impl LifecycleActions {
    /// The actual resource batch must succeed before committed bindings are
    /// released. Rejected batches retain the receipt and entire prior state.
    pub fn finish_cleanup_resources(&mut self,kernel:&mut Kernel,registry:&mut PublicationRegistry,
        id:usize,reservation:bool,leases:&[LeaseId],publications:&[PublicationId])
        ->(out:Result<Vec<ReleasedPublication>,CleanupReleaseError>)
        requires old(self).wf(),old(kernel).wf(),old(registry).wf(),
        ensures final(self).wf(),final(kernel).wf(),final(registry).wf(),final(registry).domain_id()==old(registry).domain_id(),
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
            final(self).history_preserved(old(self)),final(self).no_new_release(old(self)),
            final(kernel).commitments_frame(old(kernel),id),
    {
        reveal(Kernel::commitments_frame);reveal(LifecycleActions::same);reveal(Kernel::unchanged);proof {registry.unchanged_reflexive();registry.unchanged_observations(registry);}
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
