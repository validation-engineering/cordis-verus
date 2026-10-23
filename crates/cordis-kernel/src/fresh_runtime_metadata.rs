//! Finite-machine side conditions of the synchronous source interpreter.
//! Counters and restoring flags are real Kernel fields, not paper assumptions.
use super::FreshDriver;
use crate::Kernel;
use vstd::prelude::*;
verus! {
impl Kernel {
    pub(crate) proof fn metadata_after_begin(&self,prior:&Self,actor:usize)
        requires actor<prior.nodes.len(),self.nodes.len()==prior.nodes.len(),
            forall|i:int|0<=i<self.nodes.len() && i!=actor ==> self.nodes[i]==prior.nodes[i],
            self.nodes[actor as int].generation as nat==prior.nodes[actor as int].generation as nat+1,
            !self.nodes[actor as int].restoring,
        ensures self.synchronous_metadata(prior,true),
    { }
    pub proof fn metadata_progress(&self,prior:&Self,steps:nat,advance:bool)
        requires prior.metadata_bound(steps),self.synchronous_metadata(prior,advance),
        ensures self.metadata_bound(steps+(if advance {1nat}else{0nat})),
    {
        assert forall|i:int|0<=i<self.nodes.len() implies self.nodes[i].generation<=steps+(if advance {1nat}else{0nat}) by {
            if i<prior.nodes.len() {assert(prior.nodes[i].generation<=steps);}
        }
    }
}
impl FreshDriver {
    pub proof fn metadata_progress(&self,prior:&Self,steps:nat)
        requires prior.metadata_bound(steps),self.metadata_step(prior),
        ensures self.metadata_bound(steps+1),
    {self.inner.kernel.metadata_progress(&prior.inner.kernel,steps,true);}
    pub proof fn metadata_admission(&self,actor:usize,steps:nat)
        requires self.wf(),self.metadata_bound(steps),steps<u64::MAX,crate::refinement::registered(self.control(),actor),
        ensures self.generation_available(actor),self.cleanup_idle(actor),
    {
        self.inner.kernel.paper_observations(actor);
        assert(self.inner.kernel.nodes[actor as int].generation<=steps);
    }
}
}
