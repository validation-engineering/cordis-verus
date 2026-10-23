//! Recover Child endpoints from the native runtime's collected sources and
//! the original inverses retained by the creating recorded execution.
#[path = "managed_child_cut.rs"]
pub mod cut;
use super::RecordedExecution;
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::native::runtime::child_history::{completion::Resolution, Ledger};
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::registration::shared_child::SharedChild;
use vstd::prelude::*;

verus! {
impl<C,G,A,R,T:?Sized,M,X> RecordedExecution<C,G,A,R,T,M,X> {
    /// This uses the original action even after dispatch, retry, group removal
    /// or parent Unload. A host reply cannot replace this original shared slot.
    pub open spec fn native_child_source(&self,id:usize,token:int)->Option<SharedChild> {
        if self.histories().contains_key(id) && 0<=token<self.histories()[id].initial().len()
            && self.histories()[id].initial()[token].is_some()
            && self.histories()[id].initial()[token].unwrap() is Native {
            Some(self.histories()[id].initial()[token].unwrap()->Native_0)
        } else {None}
    }
    pub open spec fn native_child_completion(&self,ledger:&Ledger,id:usize,token:int,resolution:Resolution)->bool {
        &&& self.native_child_source(id,token).is_some()
        &&& ledger.records(&self.native_child_source(id,token).unwrap(),resolution)
        &&& self.owned_child_retirement(id,token,&ledger.retirements()[resolution.retirement])
        &&& resolution.birth.is_some() ==> {
            let birth=ledger.births()[resolution.birth.unwrap()];
            &&& birth.parent().origin==self.baseline().origin().unwrap()
            &&& birth.parent().work_domain==self.baseline().work_state().domain_id()
        }
    }
    /// Completeness is checked against every retained native inverse, including
    /// dynamically added groups and tokens. Incomplete Child work stays open.
    pub open spec fn native_children_resolved(&self,ledger:&Ledger)->bool {
        self.wf() && ledger.wf() && forall|id:usize,token:int| (#[trigger] self.native_child_source(id,token)).is_some() ==>
            exists|resolution:Resolution|self.native_child_completion(ledger,id,token,resolution)
    }
    pub proof fn native_child_endpoint(&self,ledger:&Ledger,id:usize,token:int)->(resolution:Resolution)
        requires self.native_children_resolved(ledger),self.native_child_source(id,token).is_some(),
        ensures self.native_child_completion(ledger,id,token,resolution),
            resolution.birth.is_none() ==> !ledger.retirements()[resolution.retirement].assigned(),
            resolution.birth.is_some() ==> {
                let b=ledger.births()[resolution.birth.unwrap()];let retirement=ledger.retirements()[resolution.retirement];
                &&& b.id()==retirement.child() && b.parent().origin==self.baseline().origin().unwrap()
                &&& b.parent().work_domain==self.baseline().work_state().domain_id()
                &&& if resolution.unload.is_none() {retirement.quiescent()} else {
                    let end=ledger.unloads()[resolution.unload.unwrap()];
                    &&& end.owner().origin.id==b.id()
                    &&& end.after().control.fibers[b.id()].phase==crate::Phase::Inactive
                    &&& end.after().control.fibers[b.id()].retired
                    &&& !end.after().owners.contains_key(b.id()) && !end.after().publications.contains_key(b.id())
                    &&& !crate::refinement::relied(end.before().control,b.id()) && end.cleanup_source()
                }
            },
    {
        let resolution=choose|resolution:Resolution|self.native_child_completion(ledger,id,token,resolution);
        ledger.resolution_facts(&self.native_child_source(id,token).unwrap(),resolution);resolution
    }
    /// Other native activity appends sources; it cannot erase already collected
    /// endpoints. This preserves historical evidence, not a current-state claim.
    pub proof fn retain_native_child_endpoints(&self,earlier:&Ledger,later:&Ledger)
        requires self.native_children_resolved(earlier),later.wf(),later.extends(earlier),
        ensures self.native_children_resolved(later),
    {
        assert forall|id:usize,token:int| (#[trigger] self.native_child_source(id,token)).is_some() implies
            exists|resolution:Resolution|self.native_child_completion(later,id,token,resolution) by {
            let resolution=choose|resolution:Resolution|self.native_child_completion(earlier,id,token,resolution);
            later.retained_resolution(earlier,&self.native_child_source(id,token).unwrap(),resolution);
            assert(later.retirements()[resolution.retirement]==earlier.retirements()[resolution.retirement]);
            if let Some(b)=resolution.birth {assert(later.births()[b]==earlier.births()[b]);}
            assert(self.native_child_completion(later,id,token,resolution));
        }
    }
}
}
