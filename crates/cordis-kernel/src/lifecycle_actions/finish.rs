//! One cleanup receipt gate for lifecycle and publication release.
//! The index is private and consumed in the same call. Resource preflight only
//! reports a generation; it grants no transferable release authority.
#[cfg(verus_keep_ghost)]
use super::ActionKind;
use super::{CleanupOutcome, LifecycleActions};
use crate::{Error, Kernel, Phase};
use vstd::prelude::*;

verus! {
impl LifecycleActions {
    pub open spec fn resource_finish_enabled(&self,kernel:&Kernel,id:usize,reservation:bool)->bool {
        if reservation {self.reservation_finish_enabled(kernel,id)} else {self.finish_enabled(kernel,id)}
    }

    /// Select the actual successful/drained record for the current generation
    /// and release mode. Pending/failed, absent and mismatched records all fail.
    fn finish_index(&self,kernel:&Kernel,id:usize,reservation:bool)->(out:Result<usize,Error>)
        requires self.wf(),kernel.wf(),
        ensures out.is_ok() == self.resource_finish_enabled(kernel, id, reservation),
            out.is_ok() ==> out.unwrap()<self.cleanups.len()
                && self.cleanups[out.unwrap() as int].ticket.id==id
                && self.cleanups[out.unwrap() as int].outcome.is_some()
                && self.cleanups[out.unwrap() as int].outcome!=Some(CleanupOutcome::Failed)
                && kernel.generation_of(id)==Some(self.cleanups[out.unwrap() as int].ticket.generation),
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
        Ok(i)
    }

    /// Read-only guard: Failed, absent, stale and still-Pending reports never
    /// authorize a resource mutation. Drained retains its explicit host policy.
    pub fn check_resource_finish(&self,kernel:&Kernel,id:usize,reservation:bool)->(out:Result<u64,Error>)
        requires self.wf(),kernel.wf(),
        ensures out.is_ok()==self.resource_finish_enabled(kernel,id,reservation),
            out.is_ok() ==> kernel.generation_of(id)==Some(out.unwrap()),
    {
        let i=self.finish_index(kernel,id,reservation)?;
        Ok(self.cleanups[i].ticket.generation)
    }

    fn remove_cleanup(&mut self, i: usize)
        requires old(self).wf(), i < old(self).cleanups.len(),
            old(self).cleanups[i as int].outcome.is_some(),
        ensures final(self).wf(), final(self).ledger.unchanged(&old(self).ledger),
            !final(self).has_cleanup(old(self).cleanups[i as int].ticket.id),
            final(self).history_preserved(old(self)),final(self).no_new_release(old(self)),
    {
        let ghost prior = *self;
        self.cleanups.remove(i);
        proof {
            assert forall|a:int| 0 <= a < self.cleanups.len() implies {
                let r = #[trigger] self.cleanups[a];
                &&& r.ticket.kind == ActionKind::Cleanup
                &&& r.ticket.domain == self.domain_id()
                &&& 0 < r.ticket.action < self.next_id()
                &&& if r.outcome.is_none() { self.recorded(r.ticket) }
                    else { !self.outstanding(r.ticket.id) }
            } by {
                let b = if a < i { a } else { a + 1 };
                assert(self.cleanups[a] == prior.cleanups[b]);
            }
            assert forall|a:int,b:int| 0 <= a < b < self.cleanups.len()
                implies self.cleanups[a].ticket.id != self.cleanups[b].ticket.id by {
                let pa = if a < i { a } else { a + 1 };
                let pb = if b < i { b } else { b + 1 };
                assert(self.cleanups[a] == prior.cleanups[pa]);
                assert(self.cleanups[b] == prior.cleanups[pb]);
            }
            assert forall|a:int| 0 <= a < self.cleanups.len()
                implies self.cleanups[a].ticket.id != prior.cleanups[i as int].ticket.id by {
                let b = if a < i { a } else { a + 1 };
                assert(self.cleanups[a] == prior.cleanups[b]);
            }
        }
    }

    /// The receipt gate and the actual commitment release occur in this same
    /// verified function. Failure cannot change any kernel state or commitments.
    pub fn finish_cleanup(&mut self, kernel: &mut Kernel, id: usize) -> (out: Result<(), Error>)
        requires old(self).wf(), old(kernel).wf(),
        ensures final(kernel).generations_preserved(old(kernel)), final(self).wf(), final(kernel).wf(),
            out.is_ok() == old(self).finish_enabled(old(kernel), id),
            out.is_err() ==> final(self).same(old(self)) && final(kernel).unchanged(old(kernel))
                && final(kernel).same_bindings(old(kernel)),
            out.is_ok() ==> final(kernel).phase_of(id) == Some(Phase::Inactive)
                && final(kernel).no_committed(id) && !final(self).blocked_spec(id)
                && crate::refinement::step(old(kernel).paper(), final(kernel).paper(), id, crate::refinement::Rule::Unload),
            final(self).history_preserved(old(self)),final(self).no_new_release(old(self)),
            final(kernel).commitments_frame(old(kernel),id),
    {
        proof {reveal(Kernel::generations_preserved);reveal(Kernel::unchanged);}

        proof {
            reveal(Kernel::unchanged);
            reveal(Kernel::same_bindings);
            reveal(Kernel::registered);
            reveal(Kernel::phase_of);
            reveal(Kernel::is_retired);
            reveal(Kernel::is_restoring);
            reveal(Kernel::generation_of);
        }
        let i = self.finish_index(kernel, id, false)?;
        kernel.finish_cleanup(id)?;
        self.remove_cleanup(i);
        Ok(())
    }

    pub fn finish_reservation_cleanup(&mut self, kernel: &Kernel, id: usize) -> (out: Result<(), Error>)
        requires old(self).wf(), kernel.wf(),
        ensures final(self).wf(),
            out.is_ok() == old(self).reservation_finish_enabled(kernel, id),
            out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> !final(self).blocked_spec(id),
            final(self).history_preserved(old(self)),final(self).no_new_release(old(self)),
    {
        proof {
            reveal(Kernel::unchanged);
            reveal(Kernel::same_bindings);
            reveal(Kernel::registered);
            reveal(Kernel::phase_of);
            reveal(Kernel::is_retired);
            reveal(Kernel::is_restoring);
            reveal(Kernel::generation_of);
        }
        let i = self.finish_index(kernel, id, true)?;
        self.remove_cleanup(i);
        Ok(())
    }
}
}
