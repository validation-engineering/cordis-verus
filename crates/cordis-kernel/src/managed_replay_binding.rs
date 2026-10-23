//! Certified dynamic scalar selections. A real slot replacement returns its
//! actual version/object; a prepared call validates that retained selection
//! before committing any scalar write. Old calls and inverses keep their object.
use super::super::{Effect, Owner, Step};
use super::{
    bank::Bank,
    batch::Provider,
    inputs::Seed,
    scalar::{PrepareError, PreparedStep},
    selection, Source,
};
use crate::reversible_value::{
    effect::{EffectError, ScalarEffect},
    native_effect, slot,
};
use std::sync::Arc;
use vstd::prelude::*;

verus! {
#[allow(inconsistent_fields)]
pub enum Error {Missing,NotScalar,Capacity,SourceObject,ChangedVersion,Selection(selection::Error),Prepare(PrepareError)}
pub struct Selection {slot:usize,target:usize,capture:slot::Capture}
impl Selection {
    pub closed spec fn slot_index(&self)->usize {self.slot}
    pub closed spec fn target_index(&self)->usize {self.target}
    pub closed spec fn capture(&self)->slot::Capture {self.capture}
    pub open spec fn wf<T:?Sized>(&self,bank:&Bank<T>)->bool {
        self.slot_index()<bank.len_spec() && self.target_index()<bank.len_spec()
            && self.capture().wf() && bank.service(self.slot_index() as int).managed()==Some(self.capture().slot())
            && bank.target(self.target_index() as int) is Scalar
            && *self.capture().value_spec()==bank.target(self.target_index() as int)->Scalar_0
    }
    pub fn slot_number(&self)->(out:usize) ensures out==self.slot_index(), {self.slot}
    pub fn revision(&self)->(out:u64) ensures out==self.capture().revision_spec(), {self.capture.revision()}
    /// Publish another existing Bank allocation through this actual service
    /// slot. The receipt is constructed by the real swap, never supplied by a caller.
    pub fn replace<T:?Sized>(bank:&Bank<T>,slot:usize,target:usize)->(out:Result<Self,Error>)
        requires bank.wf(),
        ensures out.is_ok() ==> out->Ok_0.wf(bank) && out->Ok_0.slot_index()==slot && out->Ok_0.target_index()==target,
    {
        let value=match bank.seed(target) {Some(Seed::Scalar(v))=>v,_=>return Err(Error::NotScalar)};
        let service=match bank.slot(slot) {Some(s)=>s,None=>return Err(Error::Missing)};
        let handle=match service.reversible() {Some(s)=>s,None=>return Err(Error::NotScalar)};
        let replaced=match handle.replace(Arc::new(value.clone())) {Ok(r)=>r,Err(_)=>return Err(Error::Capacity)};
        let (_,current)=replaced.observations();
        Ok(Self {slot,target,capture:current.duplicate()})
    }
    /// Use a fresh slot without changing it; a nonzero revision requires an
    /// authentic replacement Selection rather than an inferred current value.
    pub fn initial<T:?Sized>(bank:&Bank<T>,entry:usize)->(out:Result<Self,Error>)
        requires bank.wf(),
        ensures out.is_ok() ==> out->Ok_0.wf(bank) && out->Ok_0.slot_index()==entry && out->Ok_0.target_index()==entry,
    {
        let service=match bank.slot(entry) {Some(s)=>s,None=>return Err(Error::Missing)};
        let handle=match service.reversible() {Some(s)=>s,None=>return Err(Error::NotScalar)};
        let capture=handle.capture();
        if capture.revision()!=0 {return Err(Error::ChangedVersion);}
        proof {capture.initial_selection();bank.seed_facts(entry as int);service.payload_partition();}
        Ok(Self {slot:entry,target:entry,capture})
    }
    pub fn check<E,T:?Sized>(&self,_bank:&Bank<T>,providers:&[Provider<E,T>],capture:&native_effect::Capture<crate::reversible_value::payload::SharedPayload<T>,()>)->(out:Result<(),Error>)
        requires _bank.wf(),self.wf(_bank),capture.wf(),!capture.episode().provisions().contains(capture.binding().port_spec()),
            selection::providers_match(_bank,providers@,capture.episode().capture().sources),
        ensures out.is_ok() ==> *capture.binding().capture_spec().value_spec()==_bank.target(self.target_index() as int)->Scalar_0,
    {
        proof {capture.provenance();}
        let binding=capture.binding_ref();let port=binding.port();
        let p=match selection::find_provider(providers,port,self.slot) {Some(p)=>p,None=>return Err(Error::Selection(selection::Error::MissingProvider {step:self.slot}))};
        let expected=providers[p].id;let observed=binding.provider();
        if expected!=observed {return Err(Error::Selection(selection::Error::Provider {step:self.slot,expected,observed}));}
        proof {
            let episode=capture.episode();assert(episode.wf());assert(episode.capture().wf());
            assert(episode.capture().sources[expected].values.contains_pair((port.key,port.realm),_bank.service(self.slot as int)));
            assert(episode.imports()[(expected,port.key,port.realm)]==_bank.service(self.slot as int));
            assert(binding.capture_spec().slot()==self.capture.slot());
        }
        if !self.capture.same_revision(binding.capture()) {return Err(Error::ChangedVersion);}
        Ok(())
    }
}
#[allow(dead_code)]
pub struct Prepared<E,T:?Sized> {step:PreparedStep<E,T,()>,mapping:Ghost<Map<crate::reversible_value::service_composition::Address,crate::reversible_value::service_composition::Address>>}
impl<E:ScalarEffect,T:?Sized> Prepared<E,T> {
    pub closed spec fn step(&self)->PreparedStep<E,T,()> {self.step}
    pub closed spec fn mapping(&self)->Map<crate::reversible_value::service_composition::Address,crate::reversible_value::service_composition::Address> {self.mapping@}
    pub closed spec fn wf(&self)->bool {
        self.step().wf() && self.mapping().contains_pair(self.step().source().address(),crate::reversible_value::service_composition::Address {
            journal:self.step().computation().prepared().target().journal_spec(),key:self.step().computation().prepared().target().object().key})
    }
    /// The original landing rechecks scalar input under its write lock and
    /// registers the actual inverse. Slot changes after preparation do not retarget it.
    pub fn land<C,G,A,R,X>(self,owner:&mut Owner<C,G,A,R,T,(),X>,id:usize)->(out:Result<Step<T>,EffectError>)
        requires self.wf(),old(owner).wf(),
        ensures final(owner).wf(),out.is_ok() || out==Err(EffectError::Closed) || out==Err(EffectError::Interference),
            out.is_err() ==> final(owner).same_runtime(old(owner)),
            out.is_ok() ==> self.mapping().contains_pair(self.step().source().address(),out->Ok_0.address())
                && out->Ok_0.before()==self.step().source().before() && out->Ok_0.after()==self.step().source().after()
                && out->Ok_0.next==self.step().source().next
                && out->Ok_0.in_slot(final(owner).cleanup_state().queues()[id].slots()[out->Ok_0.token() as int]),
    {self.step.land(owner,id)}
}
impl<E:ScalarEffect+Copy,T:?Sized> Source<E,T> {
    /// Only data-only instructions enter this replay path. No user callback can
    /// run before the allocation selection check or while committing the write.
    #[allow(clippy::too_many_arguments)] // Source, owner and certified allocation selection are distinct.
    pub fn prepare_mapped_scalar<C,G,A,R,X>(&self,position:usize,owner:&Owner<C,G,A,R,T,(),X>,id:usize,bank:&Bank<T>,providers:&[Provider<E,T>],selected:&Selection)
        ->(out:Result<Prepared<E,T>,Error>)
        requires self.wf(),owner.wf(),bank.wf(),selected.wf(bank),owner.value_state().is_some(),owner.value_state().unwrap().provisions().len()==0,
            selection::providers_match(bank,providers@,owner.value_state().unwrap().capture().sources),
            forall|i:int|0<=i<self.input_spec().len() ==> (#[trigger] self.input_spec()[i]).identity_spec().namespace()==bank.namespace(),
        ensures out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.mapping()==bank.mapping()
            && out->Ok_0.step().source()==self.original().result->Ok_0.steps@[position as int],
    {
        reveal(Source::input_spec);
        if position>=self.inputs.len() {return Err(Error::Missing);}
        proof {assert(self.input_spec()[position as int]==self.inputs@[position as int]);
            assert(self.inputs@[position as int].identity_spec().namespace()==bank.namespace());}
        let input=&self.inputs[position];let pc=input.pc();
        if !matches!(&self.function.code[pc].effect,Effect::Kernel(_)) {return Err(Error::NotScalar);}
        let index=match bank.find(input) {Some(i)=>i,None=>return Err(Error::SourceObject)};
        if index!=selected.target_index_exec() {return Err(Error::SourceObject);}
        let step=match self.prepare_scalar(position,owner,id) {Ok(s)=>s,Err(e)=>return Err(Error::Prepare(e))};
        selected.check(bank,providers,step.capture_ref())?;
        proof {bank.mapping_entry(index as int);}
        Ok(Prepared {step,mapping:Ghost(bank.mapping())})
    }
}
impl Selection {pub(crate) fn target_index_exec(&self)->(out:usize) ensures out==self.target_index(), {self.target}}
}

#[cfg(not(verus_keep_ghost))]
impl std::fmt::Debug for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Missing => f.write_str("Missing"),
            Self::NotScalar => f.write_str("NotScalar"),
            Self::Capacity => f.write_str("Capacity"),
            Self::SourceObject => f.write_str("SourceObject"),
            Self::ChangedVersion => f.write_str("ChangedVersion"),
            Self::Selection(error) => f.debug_tuple("Selection").field(error).finish(),
            Self::Prepare(error) => f.debug_tuple("Prepare").field(error).finish(),
        }
    }
}
