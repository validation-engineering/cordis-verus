//! Closure queries over sources collected by actual native operations. These
//! describe observed endpoints; they do not schedule a Child or assert liveness.
use super::Ledger;
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::registration::shared_child::{ChildSnapshot, SharedChild};
use vstd::prelude::*;

verus! {
pub ghost struct Resolution {pub birth:Option<int>,pub retirement:int,pub unload:Option<int>}
impl Ledger {
    pub open spec fn has_birth(&self,child:&SharedChild)->bool {
        exists|i:int|0<=i<self.births().len() && (#[trigger] self.births()[i]).belongs_to(child)
    }
    pub open spec fn records(&self,child:&SharedChild,resolution:Resolution)->bool {
        &&& self.wf() && child.wf()
        &&& 0<=resolution.retirement<self.retirements().len()
        &&& self.retirements()[resolution.retirement].belongs_to(child)
        &&& match resolution.birth {
            None=>!self.retirements()[resolution.retirement].assigned() && resolution.unload.is_none(),
            Some(b)=>0<=b<self.births().len() && self.births()[b].belongs_to(child)
                && self.births()[b].matches_retirement(&self.retirements()[resolution.retirement])
                && match resolution.unload {
                    None=>self.retirements()[resolution.retirement].outstanding().is_none(),
                    Some(u)=>0<=u<self.unloads().len() && self.retirements()[resolution.retirement].matches_unload(&self.unloads()[u]),
                },
        }
    }
    #[verifier::opaque]
    pub open spec fn resolved(&self,child:&SharedChild)->bool {
        exists|resolution:Resolution|self.records(child,resolution)
    }
    pub proof fn retained_resolution(&self,earlier:&Self,child:&SharedChild,resolution:Resolution)
        requires self.wf(),self.extends(earlier),earlier.records(child,resolution),
        ensures self.records(child,resolution),
    {reveal(Ledger::wf);
        assert(self.retirements()[resolution.retirement]==earlier.retirements()[resolution.retirement]);
        if let Some(b)=resolution.birth {assert(self.births()[b]==earlier.births()[b]);}
        if let Some(u)=resolution.unload {assert(self.unloads()[u]==earlier.unloads()[u]);}
    }
    pub proof fn cancelled_record(tracked &self,child:&SharedChild,r:int,tracked later:&ChildSnapshot)
        requires self.wf(),0<=r<self.retirements().len(),self.retirements()[r].belongs_to(child),!self.retirements()[r].assigned(),
            later.wf(),later.source()==child.source(),
        ensures self.resolved(child),!(later.state() is Assigned),
    {reveal(Ledger::wf);
        self.retirement_witness(r).unassigned_stays_unassigned(later);
        reveal(Ledger::resolved);let resolution=Resolution {birth:None,retirement:r,unload:None};assert(self.records(child,resolution));
    }
    /// Used by the real retirement entry after its actual observation is stored.
    pub(crate) proof fn settle_retirement(tracked &self,child:&SharedChild,r:int)
        requires self.wf(),child.wf(),0<=r<self.retirements().len(),self.retirements()[r].belongs_to(child),
            !self.retirements()[r].assigned() || self.retirements()[r].outstanding().is_none() && self.has_birth(child),
            forall|b:int|0<=b<self.births().len() ==> self.retirements()[r].checkpoint().covers(&(#[trigger] self.births()[b]).checkpoint()),
        ensures self.resolved(child),
    {reveal(Ledger::wf);
        let birth=if !self.retirements()[r].assigned() {None} else {
            let b=choose|b:int|0<=b<self.births().len() && self.births()[b].belongs_to(child);
            self.births()[b].facts();
            self.birth_witness(b).retirement_agrees(self.retirement_witness(r));Some(b)
        };
        reveal(Ledger::resolved);let resolution=Resolution {birth,retirement:r,unload:None};assert(self.records(child,resolution));
    }
    pub proof fn settle_release(tracked &self,child:&SharedChild,b:int,r:int,u:int)
        requires self.wf(),child.wf(),0<=b<self.births().len(),0<=r<self.retirements().len(),0<=u<self.unloads().len(),
            self.births()[b].belongs_to(child),self.retirements()[r].belongs_to(child),
            self.retirements()[r].checkpoint().covers(&self.births()[b].checkpoint()),
            self.retirements()[r].matches_unload(&self.unloads()[u]),
        ensures self.resolved(child),self.records(child,Resolution {birth:Some(b),retirement:r,unload:Some(u)}),
    {reveal(Ledger::wf);
        self.births()[b].facts();
            self.birth_witness(b).retirement_agrees(self.retirement_witness(r));
        reveal(Ledger::resolved);let resolution=Resolution {birth:Some(b),retirement:r,unload:Some(u)};assert(self.records(child,resolution));
    }
    /// Compose the source facts exported by real retirement and release calls.
    /// Keeping this lemma separate avoids unfolding the whole runtime invariant.
    pub(crate) proof fn finish_release(tracked &self,child:&SharedChild,r:int,u:int,
        retirement:&super::super::child_recovery::Retirement,end:&super::super::episode::Unload)
        requires self.wf(),child.wf(),self.has_birth(child),0<=r<self.retirements().len(),0<=u<self.unloads().len(),
            self.retirements()[r].same_source(retirement),self.unloads()[u].same_source(end),retirement.belongs_to(child),retirement.matches_unload(end),
            forall|b:int|0<=b<self.births().len() ==> retirement.checkpoint().covers(&(#[trigger] self.births()[b]).checkpoint()),
        ensures self.resolved(child),
    {reveal(Ledger::wf);
        let b=choose|b:int|0<=b<self.births().len() && self.births()[b].belongs_to(child);
        self.settle_release(child,b,r,u);
    }
    /// The concrete conclusions use the retained actual cut for each case.
    /// Inactive/absent at retirement is distinct from a recorded Unload.
    pub proof fn resolution_facts(&self,child:&SharedChild,resolution:Resolution)
        requires self.records(child,resolution),
        ensures resolution.birth.is_none() ==> !self.retirements()[resolution.retirement].assigned(),
            resolution.birth.is_some() ==> {
                let b=self.births()[resolution.birth.unwrap()];let r=self.retirements()[resolution.retirement];
                &&& b.id()==r.child() && b.parent().origin.id==child.owner() && b.parent().origin.domain==child.domain_id()
                &&& Some(b.parent().origin.generation)==child.episode()
                &&& if resolution.unload.is_none() {r.quiescent()} else {
                    let end=self.unloads()[resolution.unload.unwrap()];
                    &&& end.owner().origin.id==b.id()
                    &&& end.after().control.fibers[b.id()].phase==crate::Phase::Inactive
                    &&& end.after().control.fibers[b.id()].retired
                    &&& !end.after().owners.contains_key(b.id()) && !end.after().publications.contains_key(b.id())
                    &&& !crate::refinement::relied(end.before().control,b.id()) && end.cleanup_source()
                }
            },
    {reveal(Ledger::wf);
        if let Some(b)=resolution.birth {
            self.births()[b].facts();
            match resolution.unload {
                Some(u)=>self.retirements()[resolution.retirement].unload_releases_assigned_episode(&self.unloads()[u]),
                None=>self.retirements()[resolution.retirement].no_episode_is_quiescent(),
            }
        }
    }
}
}
