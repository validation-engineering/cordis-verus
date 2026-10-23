//! Complete declaration-slot identity transport, including unvisited services.
//! A slot is not its selected cell: distinct slots stay distinct even when they
//! select the same object, and all aliases of one source slot reuse one target.
#[cfg(verus_keep_ghost)]
use super::objects::service_address;
use super::{
    objects::{Error, Projection},
    Value,
};
use crate::reversible_value::service_composition::Address;
use crate::reversible_value::{
    joint,
    managed::replay::{
        bank::Bank,
        environment::{Environment, Selected},
        services::Preload,
        slots::Slots,
    },
    slot,
};
use std::sync::Arc;
use vstd::prelude::*;

verus! {
#[allow(dead_code)]
struct Entry {
    source:Arc<joint::identity::AllocationIdentity>,target:Arc<joint::identity::AllocationIdentity>,
    template:Preload<Value>,cell:Ghost<Address>,
    source_selection:slot::Capture,target_selection:slot::Capture,versions:Ghost<Map<u64,u64>>,
}
impl Entry {
    spec fn selections(&self,projection:&Projection)->bool {
        self.source_selection.wf() && self.target_selection.wf()
            && self.source.address()==(Address {journal:self.source_selection.slot().journal_spec(),key:self.source_selection.slot().key()})
            && self.template.service.managed()==Some(self.target_selection.slot())
            && (self.template.route.is_none() ==> {
                &&& projection.mapping().contains_pair(selected(&self.source_selection),selected(&self.target_selection))
                &&& crate::reversible_value::managed::replay::typed::injective(self.versions@)
                &&& crate::reversible_value::managed::replay::typed_correspondence::epochs::ordered(self.versions@)
                &&& crate::reversible_value::managed::replay::typed::bounded(self.versions@,self.source_selection.revision_spec(),self.target_selection.revision_spec())
                &&& self.versions@.contains_pair(self.source_selection.revision_spec(),self.target_selection.revision_spec())
            })
    }
}
pub open spec fn selected(c:&slot::Capture)->Address {Address {journal:c.value_spec().journal_spec(),key:c.value_spec().object().key}}
pub open spec fn slot_address(c:&slot::Capture)->Address {Address {journal:c.slot().journal_spec(),key:c.slot().key()}}
pub open spec fn compatible(a:&slot::Capture,b:&slot::Capture)->bool {
    slot_address(a)!=slot_address(b) || (a.revision_spec()==b.revision_spec() && selected(a)==selected(b))
}

pub(crate) struct Catalog {entries:Vec<Entry>}
impl Catalog {
    pub(crate) closed spec fn wf(&self,bank:&Bank<Value>,slots:&Slots<Value>,projection:&Projection)->bool {
        (forall|i:int|0<=i<self.entries.len() ==> {
            let e=#[trigger] self.entries@[i];
            &&& e.source.wf() && e.target.wf() && e.source.number_spec().is_some() && e.target.number_spec().is_some()
            &&& e.source.namespace()==bank.namespace() && e.target.namespace()==bank.journal().identity_namespace()
            &&& e.selections(projection)
            &&& e.template.wf(bank,slots) && e.template.service.managed().is_some()
            &&& e.target.address()==(Address {journal:e.template.service.managed().unwrap().journal_spec(),key:e.template.service.managed().unwrap().key()})
            &&& projection.mapping().contains_pair(e.cell@,service_address(e.template.service))
        }) && forall|i:int,j:int|0<=i<j<self.entries.len() ==>
            self.entries@[i].source.address()!=self.entries@[j].source.address() && self.entries@[i].target.address()!=self.entries@[j].target.address()
    }
    pub(crate) fn new()->(out:Self)
        ensures forall|bank:&Bank<Value>,slots:&Slots<Value>,p:&Projection|out.wf(bank,slots,p),
    {Self {entries:Vec::new()}}
    #[allow(unused_variables)] // Runtime arguments anchor erased allocation contracts.
    #[allow(clippy::too_many_arguments)] // Both physical catalogs and the source capture are explicit.
    pub(crate) fn select(&mut self,bank:&Bank<Value>,slots:&Slots<Value>,projection:&Projection,selection:&Selected<Value>,candidate:Preload<Value>,Ghost(cell):Ghost<Address>)
        ->(out:Result<(Preload<Value>,Ghost<Address>),Error>)
        requires old(self).wf(bank,slots,projection),bank.wf(),slots.wf(bank),projection.wf(bank),selection.wf(),selection.namespace(bank.namespace()),
            candidate.wf(bank,slots),projection.mapping().contains_pair(cell,service_address(candidate.service)),
            candidate.service.managed().is_some() ==> candidate.service.managed().unwrap().journal_spec()==bank.journal(),
            candidate.route.is_none() ==> cell==selection.address(),
        ensures final(self).wf(bank,slots,projection),
            out.is_ok() ==> out->Ok_0.0.wf(bank,slots) && out->Ok_0.0.port==candidate.port
                && projection.mapping().contains_pair(out->Ok_0.1@,service_address(out->Ok_0.0.service)),
    {
        let capture=match selection {Selected::Scalar(c)=>c,_=>return Ok((candidate,Ghost(cell)))};
        let source=capture.slot_ref().identity();if source.number().is_none() {return Err(Error::Unnamed);}
        let mut i=0;
        while i<self.entries.len()
            invariant self.wf(bank,slots,projection),*self==*old(self),source.wf(),source.number_spec().is_some(),source.namespace()==bank.namespace(),i<=self.entries.len(),
                forall|j:int|0<=j<i ==> self.entries@[j].source.address()!=source.address(),
            decreases self.entries.len()-i,
        {
            if self.entries[i].source.same(&source)==Some(true) {
                let template=self.entries[i].template.relabel(candidate.port,candidate.origin());
                return Ok((template,Ghost(self.entries@[i as int].cell@)));
            }i+=1;
        }
        let slot=match candidate.service.reversible() {Some(s)=>s,None=>return Err(Error::Kind)};
        let target=slot.identity();if target.number().is_none() {return Err(Error::Unnamed);}
        let mut j=0;
        while j<self.entries.len()
            invariant self.wf(bank,slots,projection),*self==*old(self),source.wf(),source.number_spec().is_some(),source.namespace()==bank.namespace(),
                target.wf(),target.number_spec().is_some(),target.namespace()==bank.journal().identity_namespace(),j<=self.entries.len(),
                forall|k:int|0<=k<self.entries.len() ==> self.entries@[k].source.address()!=source.address(),
                forall|k:int|0<=k<j ==> self.entries@[k].target.address()!=target.address(),
            decreases self.entries.len()-j,
        {if self.entries[j].target.same(&target)!=Some(false) {return Err(Error::Alias);}j+=1;}
        let target_selection=slot.capture();
        if candidate.route.is_none() && target_selection.revision()!=0 {return Err(Error::History);}
        if candidate.route.is_none() {proof {target_selection.initial_selection();assert(cell==selection.address());}}
        let versions=Ghost(Map::empty().insert(capture.revision_spec(),target_selection.revision_spec()));
        let template=candidate.duplicate();let ghost prior=self.entries@;
        self.entries.push(Entry {source,target,template,cell:Ghost(cell),source_selection:capture.duplicate(),target_selection,versions});
        proof {
            assert forall|a:int,b:int|0<=a<b<self.entries.len() implies self.entries@[a].source.address()!=self.entries@[b].source.address()
                && self.entries@[a].target.address()!=self.entries@[b].target.address() by {
                if b<prior.len() {assert(self.entries@[a]==prior[a]);assert(self.entries@[b]==prior[b]);}
                else {assert(b==prior.len());assert(self.entries@[a]==prior[a]);}
            }
        }
        Ok((candidate,Ghost(cell)))
    }
}
}

verus! {
impl Catalog {
    pub(crate) closed spec fn synchronized(&self,source:&slot::Capture)->bool {
        exists|i:int|0<=i<self.entries.len() && (#[trigger] self.entries@[i]).source.address()==(Address {journal:source.slot().journal_spec(),key:source.slot().key()})
            && (self.entries@[i].template.route.is_some() || (self.entries@[i].source_selection.revision_spec()==source.revision_spec() && selected(&self.entries@[i].source_selection)==selected(source)))
    }
    /// Synchronize declarations not visited by any retained instruction. Used
    /// slots remain owned by the operand catalog; both paths use real CAS.
    #[verifier::rlimit(16)]
    pub(crate) fn synchronize(&mut self,bank:&Bank<Value>,projection:&Projection,source:&slot::Capture,Ghost(slots):Ghost<Slots<Value>>)->(out:Result<(),Error>)
        requires bank.wf(),projection.wf(bank),old(self).wf(bank,&slots,projection),source.wf(),source.slot().journal_spec().identity_namespace()==bank.namespace(),selected(source).journal.identity_namespace()==bank.namespace(),
        ensures final(self).wf(bank,&slots,projection),out.is_ok() ==> final(self).synchronized(source),
            forall|other:&slot::Capture|compatible(source,other) && #[trigger] old(self).synchronized(other) ==> final(self).synchronized(other),
    {
        let identity=source.slot_ref().identity();let mut i=0;
        while i<self.entries.len()
            invariant self.wf(bank,&slots,projection),*self==*old(self),bank.wf(),projection.wf(bank),source.wf(),selected(source).journal.identity_namespace()==bank.namespace(),identity.wf(),identity.namespace()==bank.namespace(),identity.address()==(Address {journal:source.slot().journal_spec(),key:source.slot().key()}),i<=self.entries.len(),
            decreases self.entries.len()-i,
        {
            if self.entries[i].source.same(&identity)!=Some(true) {i+=1;continue;}
            let entry=&self.entries[i];
            proof {projection.facts(bank);assert(entry.selections(projection));assert(entry.source.address()==identity.address());}
            if entry.template.route.is_some() {proof {assert(self.entries@[i as int].source.address()==identity.address());}return Ok(());}
            let target=entry.template.service.reversible().unwrap();
            if source.same_revision_at(&entry.source_selection) {
                let current=target.capture();
                if !current.same_revision(&entry.target_selection) {return Err(Error::History);}
                proof {assert(self.entries@[i as int].source_selection.revision_spec()==source.revision_spec());}
                return Ok(());
            }
            if source.revision()<entry.source_selection.revision() {return Err(Error::History);}
            let object=source.value().identity();
            let value=match projection.scalar_target(bank,&object) {Some(v)=>v,None=>return Err(Error::Reference)};
            let change=match target.replace_captured(&entry.target_selection,value) {Ok(c)=>c,Err(_)=>return Err(Error::History)};
            let (_,current)=change.observations();
            proof {
                crate::reversible_value::managed::replay::typed::extend(entry.versions@,entry.source_selection.revision_spec(),entry.target_selection.revision_spec(),source.revision_spec(),current.revision_spec());
                crate::reversible_value::managed::replay::typed_correspondence::epochs::ordered_extend(entry.versions@,entry.source_selection.revision_spec(),entry.target_selection.revision_spec(),source.revision_spec(),current.revision_spec());
            }
            let updated=Entry {source:entry.source.clone(),target:entry.target.clone(),template:entry.template.duplicate(),cell:entry.cell,
                source_selection:source.duplicate(),target_selection:current.duplicate(),versions:Ghost(entry.versions@.insert(source.revision_spec(),current.revision_spec()))};
            let ghost before=self.entries@;
            self.entries.set(i,updated);
            proof {
                assert(updated.selections(projection));assert(self.entries@[i as int].source_selection.revision_spec()==source.revision_spec());
                assert forall|other:&slot::Capture|compatible(source,other) && #[trigger] old(self).synchronized(other) implies self.synchronized(other) by {
                    let j=choose|j:int|0<=j<before.len() && (#[trigger] before[j]).source.address()==slot_address(other)
                        && (before[j].template.route.is_some() || (before[j].source_selection.revision_spec()==other.revision_spec() && selected(&before[j].source_selection)==selected(other)));
                    if j==i {assert(slot_address(source)==slot_address(other));} else {assert(self.entries@[j]==before[j]);}
                    assert(self.entries@[j].source.address()==slot_address(other));
                }
                assert forall|j:int|0<=j<self.entries.len() implies (#[trigger] self.entries@[j]).selections(projection) by {if j!=i {assert(self.entries@[j]==before[j]);}}
                assert forall|a:int,b:int|0<=a<b<self.entries.len() implies self.entries@[a].source.address()!=self.entries@[b].source.address() && self.entries@[a].target.address()!=self.entries@[b].target.address() by {assert(self.entries@[a].source==before[a].source && self.entries@[b].source==before[b].source);}
            }
            return Ok(());
        }Err(Error::Reference)
    }
    pub(crate) open spec fn environment_synchronized(&self,environment:&Environment<Value>)->bool {
        forall|i:int|0<=i<environment.entries().len() && environment.entries()[i].result.is_ok()
            && environment.entries()[i].result->Ok_0.selected is Scalar ==>
                self.synchronized(&(#[trigger] environment.entries()[i]).result->Ok_0.selected->Scalar_0)
    }
    pub(crate) fn synchronize_environment(&mut self,bank:&Bank<Value>,projection:&Projection,environment:&Environment<Value>,Ghost(slots):Ghost<Slots<Value>>)->(out:Result<(),Error>)
        requires bank.wf(),projection.wf(bank),old(self).wf(bank,&slots,projection),environment.wf(),environment.namespace(bank.namespace()),
        ensures final(self).wf(bank,&slots,projection),out.is_ok() ==> final(self).environment_synchronized(environment),
    {
        let entries=environment.observations();let mut i=0;
        while i<entries.len()
            invariant bank.wf(),projection.wf(bank),self.wf(bank,&slots,projection),environment.wf(),environment.namespace(bank.namespace()),entries@==environment.entries(),i<=entries.len(),
                forall|a:int,b:int|0<=a<i && 0<=b<a && entries@[a].result.is_ok() && entries@[b].result.is_ok()
                    && entries@[a].result->Ok_0.selected is Scalar && entries@[b].result->Ok_0.selected is Scalar ==>
                    compatible(&(#[trigger] entries@[a]).result->Ok_0.selected->Scalar_0,&(#[trigger] entries@[b]).result->Ok_0.selected->Scalar_0),
            decreases entries.len()-i,
        {
            if let Ok(binding)=&entries[i].result {if let Selected::Scalar(a)=&binding.selected {
                let ai=a.slot_ref().identity();let mut j=0;
                while j<i
                    invariant self.wf(bank,&slots,projection),environment.wf(),environment.namespace(bank.namespace()),entries@==environment.entries(),i<entries.len(),j<=i,a.wf(),ai.wf(),ai.namespace()==bank.namespace(),ai.address()==slot_address(a),
                        forall|b:int|0<=b<j && entries@[b].result.is_ok() && entries@[b].result->Ok_0.selected is Scalar ==>
                            compatible(a,&(#[trigger] entries@[b]).result->Ok_0.selected->Scalar_0),
                        forall|x:int,y:int|0<=x<i && 0<=y<x && entries@[x].result.is_ok() && entries@[y].result.is_ok()
                            && entries@[x].result->Ok_0.selected is Scalar && entries@[y].result->Ok_0.selected is Scalar ==>
                            compatible(&(#[trigger] entries@[x]).result->Ok_0.selected->Scalar_0,&(#[trigger] entries@[y]).result->Ok_0.selected->Scalar_0),
                    decreases i-j,
                {
                    if let Ok(binding)=&entries[j].result {if let Selected::Scalar(b)=&binding.selected {
                        let bi=b.slot_ref().identity();
                        match ai.same(&bi) {
                            Some(true)=>if !a.same_revision_at(b) {return Err(Error::History);},
                            Some(false)=>{},None=>return Err(Error::Unnamed),
                        }
                        assert(compatible(a,b));
                    }}j+=1;
                }
            }}i+=1;
        }
        let mut i=0;
        while i<entries.len()
            invariant bank.wf(),projection.wf(bank),self.wf(bank,&slots,projection),environment.wf(),environment.namespace(bank.namespace()),entries@==environment.entries(),i<=entries.len(),
                forall|a:int,b:int|0<=a<entries.len() && 0<=b<a && entries@[a].result.is_ok() && entries@[b].result.is_ok()
                    && entries@[a].result->Ok_0.selected is Scalar && entries@[b].result->Ok_0.selected is Scalar ==>
                    compatible(&(#[trigger] entries@[a]).result->Ok_0.selected->Scalar_0,&(#[trigger] entries@[b]).result->Ok_0.selected->Scalar_0),
                forall|j:int|0<=j<i && entries@[j].result.is_ok() && entries@[j].result->Ok_0.selected is Scalar ==>
                    self.synchronized(&(#[trigger] entries@[j]).result->Ok_0.selected->Scalar_0),
            decreases entries.len()-i,
        {
            if let Ok(binding)=&entries[i].result {if let Selected::Scalar(capture)=&binding.selected {
                let ghost prior=*self;
                self.synchronize(bank,projection,capture,Ghost(slots))?;
                assert forall|j:int|0<=j<i && entries@[j].result.is_ok() && entries@[j].result->Ok_0.selected is Scalar implies
                    self.synchronized(&(#[trigger] entries@[j]).result->Ok_0.selected->Scalar_0) by {
                    let other=&entries@[j].result->Ok_0.selected->Scalar_0;
                    assert(compatible(capture,other));assert(prior.synchronized(other));
                }
            }}i+=1;
        }Ok(())
    }
}
}
