//! Bind an in-place configuration update to the actual native registration,
//! activation and recipe version. Capture/check read the real lifecycle owner;
//! the guarded replacement cannot reuse a target after recipe replacement.
use crate::lifecycle_state::native::runtime::NativeRuntime;
use crate::reversible_value::joint;
use crate::{Error, Phase};
use vstd::prelude::*;
#[path = "configuration_adoption.rs"]
pub mod adoption;
verus! {
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct Target {domain:u64,id:usize,generation:u64,revision:u64}
impl Target {
    pub closed spec fn domain_id(&self)->u64 {self.domain}
    pub closed spec fn owner(&self)->usize {self.id}
    pub closed spec fn epoch(&self)->u64 {self.generation}
    pub closed spec fn version(&self)->u64 {self.revision}
    pub fn id(&self)->(out:usize) ensures out==self.owner(), {self.id}
    pub fn generation(&self)->(out:u64) ensures out==self.epoch(), {self.generation}
    pub fn revision(&self)->(out:u64) ensures out==self.version(), {self.revision}
}
/// Captured from a real native registration, including its parent in a
/// certified execution snapshot. The record is evidence of that observation;
/// it does not claim that the registration remains live forever.
#[allow(dead_code)]
pub struct Allocation {domain:u64,id:usize,parent:Option<usize>,evidence:Ghost<joint::Snapshot>,key:Ghost<nat>}
impl Allocation {
    pub closed spec fn domain_id(&self)->u64 {self.domain}
    pub closed spec fn owner(&self)->usize {self.id}
    pub closed spec fn parent_id(&self)->Option<usize> {self.parent}
    pub closed spec fn snapshot(&self)->joint::Snapshot {self.evidence@}
    pub closed spec fn native_key(&self)->nat {self.key@}
    pub open spec fn wf(&self)->bool {
        self.snapshot().certified() && self.snapshot().last().contains_key(self.native_key())
            && self.snapshot().last()[self.native_key()] is Native
            && self.snapshot().last()[self.native_key()]->Native_state.control.fibers.dom().contains(self.owner())
            && self.snapshot().last()[self.native_key()]->Native_state.control.fibers[self.owner()].parent==self.parent_id()
            && !self.snapshot().last()[self.native_key()]->Native_state.control.fibers[self.owner()].retired
    }
    pub fn id(&self)->(out:usize) ensures out==self.owner(), {self.id}
    pub fn domain(&self)->(out:u64) ensures out==self.domain_id(), {self.domain}
    pub fn parent(&self)->(out:Option<usize>) ensures out==self.parent_id(), {self.parent}
}
impl Clone for Allocation {
    fn clone(&self)->(out:Self) ensures out==*self,
    {Self {domain:self.domain,id:self.id,parent:self.parent,evidence:Ghost(self.evidence@),key:Ghost(self.key@)}}
}
impl<R,H,V> NativeRuntime<R,H,V> {
    pub fn configuration_allocation(&self,id:usize)->(out:Option<Allocation>)
        requires self.wf(),
        ensures out.is_some()==(self.registry().entries().contains_key(id) && !self.state().control().is_retired(id)),
            out.is_some() ==> out.unwrap().wf() && out.unwrap().owner()==id
                && out.unwrap().domain_id()==self.state().protocol().domain_id()
                && out.unwrap().parent_id()==self.registry().entries()[id].recipe().parent_id()
                && out.unwrap().native_key()==self.joint_key()
                && out.unwrap().snapshot().domain()==self.journal_spec().source(),
    {
        let recipe=self.registration(id)?;
        if self.kernel().retired(id) {return None;}
        let parent=recipe.parent();let domain=self.lifecycle().domain();
        let _evidence=self.execution_snapshot();
        proof {assert(self.registry().recipe_matches(id));reveal(crate::Kernel::paper);reveal(crate::Kernel::is_retired);}
        Some(Allocation {domain,id,parent,evidence:Ghost(_evidence),key:Ghost(self.joint_key())})
    }
    pub open spec fn configuration_enabled(&self,id:usize)->bool {
        self.registry().entries().contains_key(id) && self.state().control().phase_of(id)==Some(Phase::Active)
            && !self.state().control().is_retired(id) && self.state().control().generation_of(id).is_some()
    }
    pub open spec fn configuration_matches(&self,target:Target)->bool {
        self.configuration_enabled(target.owner()) && target.domain_id()==self.state().protocol().domain_id()
            && self.state().control().generation_of(target.owner())==Some(target.epoch())
            && self.registry().entries()[target.owner()].recipe().version()==target.version()
    }
    pub fn configuration_target(&self,id:usize)->(out:Option<Target>)
        requires self.wf(),
        ensures out.is_some()==self.configuration_enabled(id),
            out.is_some() ==> out.unwrap().owner()==id && self.configuration_matches(out.unwrap()),
    {
        if self.kernel().phase(id)!=Some(Phase::Active) || self.kernel().retired(id) {return None;}
        let generation=self.kernel().episode_generation(id)?;
        let recipe=self.registration(id)?;
        Some(Target {domain:self.lifecycle().domain(),id,generation,revision:recipe.revision()})
    }
    pub fn configuration_target_is_current(&self,target:Target)->(out:bool)
        requires self.wf(),ensures out==self.configuration_matches(target),
    {self.configuration_target(target.id)==Some(target)}
    pub fn replace_configuration(&mut self,target:Target,payload:R)->(out:Result<R,(Error,R)>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            final(self).state()==old(self).state(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            !old(self).configuration_matches(target) ==> *final(self)==*old(self) && out==Err((Error::InvalidState,payload)),
            out.is_ok()==(old(self).configuration_matches(target) && old(self).registry().entries()[target.owner()].recipe().version()<u64::MAX),
            final(self).registry().entries().dom()==old(self).registry().entries().dom(),
            forall|n:usize| #[trigger] old(self).registry().entries().contains_key(n) ==>
                final(self).registry().entries()[n].bookkeeping()==old(self).registry().entries()[n].bookkeeping()
                && (n!=target.owner() ==> final(self).registry().entries()[n]==old(self).registry().entries()[n]),
            out.is_err() ==> final(self).registry().entries()==old(self).registry().entries(),
            out.is_ok() ==> final(self).registry().entries()[target.owner()].recipe().same_identity(&old(self).registry().entries()[target.owner()].recipe()),
            out.is_ok() ==> old(self).configuration_matches(target) && !final(self).configuration_matches(target)
                && final(self).registry().entries()[target.owner()].recipe().version()==target.version()+1
                && final(self).registry().entries()[target.owner()].recipe().payload()==payload
                && out->Ok_0==old(self).registry().entries()[target.owner()].recipe().payload(),
            out.is_err() ==> out->Err_0.1==payload,
    {
        if !self.configuration_target_is_current(target) {return Err((Error::InvalidState,payload));}
        self.replace(target.id,payload)
    }
}
}
