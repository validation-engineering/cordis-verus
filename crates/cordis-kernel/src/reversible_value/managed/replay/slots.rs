//! Persistent mapping of actual source slot allocations, separate from cells.
//! Multiple source slots may select the same cell; one source slot shared by
//! several services is represented by one actual target slot and one history.
use super::super::Slot;
use super::{
    bank::Bank,
    inputs::{Input, Seed},
};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::service_composition::Address;
use crate::reversible_value::{joint, slot};
use std::sync::Arc;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
impl<T:?Sized> Default for Slots<T> {
    fn default()->Self {Self::new()}
}

#[derive(Debug)]
pub enum Error {NotScalar,Unnamed,Allocation,StaleSource,ChangedSource,Target(slot::SelectionError),ChangedTarget}
#[allow(dead_code)] // The version injection is erased; retained captures are real.
struct Entry<T:?Sized> {
    source:Arc<joint::identity::AllocationIdentity>,target:Arc<joint::identity::AllocationIdentity>,
    source_selection:slot::Capture,target_selection:slot::Capture,service:Arc<Slot<T,()>>,
    initial:usize,selected:usize,versions:Ghost<Map<u64,u64>>,
}
impl<T:?Sized> Entry<T> {
    spec fn wf(&self,bank:&Bank<T>)->bool {
        self.source.wf() && self.source.number_spec().is_some() && self.source.namespace()==bank.namespace()
            && self.target.wf() && self.target.number_spec().is_some() && self.target.namespace()==bank.journal().identity_namespace()
            && self.source_selection.wf() && self.target_selection.wf()
            && self.source.address()==(Address {journal:self.source_selection.slot().journal_spec(),key:self.source_selection.slot().key()})
            && self.target.address()==(Address {journal:self.target_selection.slot().journal_spec(),key:self.target_selection.slot().key()})
            && self.target_selection.slot().journal_spec()==bank.journal()
            && self.service.managed()==Some(self.target_selection.slot())
            && self.initial<bank.len_spec() && bank.target(self.initial as int) is Scalar
            && *self.target_selection.slot().initial()==bank.target(self.initial as int)->Scalar_0
            && self.selected<bank.len_spec() && bank.target(self.selected as int) is Scalar
            && *self.target_selection.value_spec()==bank.target(self.selected as int)->Scalar_0
            && bank.address(self.selected as int)==(Address {journal:self.source_selection.value_spec().journal_spec(),key:self.source_selection.value_spec().object().key})
            && super::typed::injective(self.versions@) && super::typed_correspondence::epochs::ordered(self.versions@)
            && super::typed::bounded(self.versions@,self.source_selection.revision_spec(),self.target_selection.revision_spec())
            && self.versions@.contains_pair(self.source_selection.revision_spec(),self.target_selection.revision_spec())
    }
}
pub struct Slots<T:?Sized> {entries:Vec<Entry<T>>}
impl<T:?Sized> Slots<T> {
    pub closed spec fn wf(&self,bank:&Bank<T>)->bool {
        (forall|i:int|0<=i<self.entries.len() ==> (#[trigger] self.entries@[i]).wf(bank))
            && forall|i:int,j:int|0<=i<j<self.entries.len() ==> self.source(i)!=self.source(j) && self.target(i)!=self.target(j)
    }
    pub closed spec fn len_spec(&self)->nat {self.entries@.len()}
    pub closed spec fn source(&self,i:int)->Address {self.entries@[i].source.address()}
    pub closed spec fn target(&self,i:int)->Address {self.entries@[i].target.address()}
    pub closed spec fn service(&self,i:int)->Arc<Slot<T,()>> {self.entries@[i].service}
    pub closed spec fn initial(&self,i:int)->usize {self.entries@[i].initial}
    pub closed spec fn selected(&self,i:int)->usize {self.entries@[i].selected}
    pub closed spec fn capture(&self,i:int)->slot::Capture {self.entries@[i].target_selection}
    pub closed spec fn source_capture(&self,i:int)->slot::Capture {self.entries@[i].source_selection}
    pub closed spec fn versions(&self,i:int)->Map<u64,u64> {self.entries@[i].versions@}
    pub open spec fn frame(&self,prior:&Self)->bool {
        self.len_spec()==prior.len_spec() && forall|i:int|0<=i<self.len_spec() ==> self.source(i)==prior.source(i)
            && self.target(i)==prior.target(i) && self.service(i)==prior.service(i) && self.initial(i)==prior.initial(i)
    }
    pub fn new()->(out:Self) ensures forall|bank:&Bank<T>|out.wf(bank),out.len_spec()==0, {Self {entries:Vec::new()}}
    pub proof fn entry_facts(&self,bank:&Bank<T>,i:int)
        requires bank.wf(),self.wf(bank),0<=i<self.len_spec(),
        ensures self.initial(i)<bank.len_spec(),super::bank::seed_slot(bank.target(self.initial(i) as int),*self.service(i)),
            self.capture(i).wf(),self.service(i).managed()==Some(self.capture(i).slot()),self.capture(i).slot().journal_spec()==bank.journal(),
            self.selected(i)<bank.len_spec(),bank.target(self.selected(i) as int) is Scalar,*self.capture(i).value_spec()==bank.target(self.selected(i) as int)->Scalar_0,
    {bank.target_facts(self.initial(i) as int);}
    pub proof fn extend_bank(&self,prior:&Bank<T>,bank:&Bank<T>)
        requires self.wf(prior),bank.extends(prior),ensures self.wf(bank),
    {
        assert forall|i:int|0<=i<self.entries.len() implies (#[trigger] self.entries@[i]).wf(bank) by {
            let e=self.entries@[i];assert(e.wf(prior));assert(bank.target(e.initial as int)==prior.target(e.initial as int));assert(bank.target(e.selected as int)==prior.target(e.selected as int));
        }
    }
    pub fn len(&self)->(out:usize) ensures out==self.len_spec(), {self.entries.len()}
    pub fn is_empty(&self)->(out:bool) ensures out==(self.len_spec()==0), {self.entries.is_empty()}
    pub fn published(&self,i:usize)->(out:Option<Arc<Slot<T,()>>>)
        ensures out.is_some()==(i<self.len_spec()),out.is_some() ==> out.unwrap()==self.service(i as int),
    {if i<self.entries.len() {Some(self.entries[i].service.clone())} else {None}}
    pub fn selected_entry(&self,i:usize)->(out:Option<usize>)
        ensures out.is_some()==(i<self.len_spec()),out.is_some() ==> out.unwrap()==self.selected(i as int),
    {if i<self.entries.len() {Some(self.entries[i].selected)} else {None}}
    pub fn retained(&self,i:usize)->(out:Option<&slot::Capture>)
        ensures out.is_some()==(i<self.len_spec()),out.is_some() ==> *out.unwrap()==self.capture(i as int),
    {if i<self.entries.len() {Some(&self.entries[i].target_selection)} else {None}}
    pub fn original_entry(&self,i:usize)->(out:Option<usize>)
        ensures out.is_some()==(i<self.len_spec()),out.is_some() ==> out.unwrap()==self.initial(i as int),
    {if i<self.entries.len() {Some(self.entries[i].initial)} else {None}}
    #[allow(unused_variables)] // Bank anchors the erased source namespace.
    pub fn find_selection(&self,bank:&Bank<T>,capture:&slot::Capture)->(out:Option<usize>)
        requires self.wf(bank),capture.wf(),capture.slot().journal_spec().identity_namespace()==bank.namespace(),
        ensures out.is_some() ==> out.unwrap()<self.len_spec() && self.source(out.unwrap() as int)==(Address {journal:capture.slot().journal_spec(),key:capture.slot().key()}),
    {
        let identity=capture.slot_ref().identity();let mut i=0;
        while i<self.entries.len()
            invariant self.wf(bank),capture.wf(),identity.wf(),identity.namespace()==bank.namespace(),identity.address()==(Address {journal:capture.slot().journal_spec(),key:capture.slot().key()}),i<=self.entries.len(),
            decreases self.entries.len()-i,
        {if self.entries[i].source.same(&identity)==Some(true) {return Some(i);}i+=1;}None
    }
    /// Allocate from the first real use of this source slot. Reusing a cell
    /// never merges independently allocated source slots.
    #[verifier::rlimit(16)]
    pub fn bind(&mut self,bank:&Bank<T>,input:&Input<T>,index:usize)->(out:Result<usize,Error>)
        requires bank.wf(),old(self).wf(bank),input.wf(),input.namespace(bank.namespace()),index<bank.len_spec(),bank.address(index as int)==input.source().address(),
        ensures final(self).wf(bank),final(self).len_spec()>=old(self).len_spec(),
            forall|i:int|0<=i<old(self).len_spec() ==> final(self).source(i)==old(self).source(i) && final(self).target(i)==old(self).target(i) && final(self).service(i)==old(self).service(i) && final(self).initial(i)==old(self).initial(i),
            out.is_ok() ==> out->Ok_0<final(self).len_spec() && input.source().result is Scalar
                && final(self).source(out->Ok_0 as int)==(Address {journal:input.source().result->Scalar_write.binding.capture_spec().slot().journal_spec(),key:input.source().result->Scalar_write.binding.capture_spec().slot().key()}),
    {
        hide(joint::valid);hide(joint::step);
        let source=match input.selected_slot() {Some(c)=>c,None=>return Err(Error::NotScalar)};
        let identity=source.slot_ref().identity();if identity.number().is_none() {return Err(Error::Unnamed);}
        let mut i=0;
        while i<self.entries.len()
            invariant bank.wf(),self.wf(bank),*self==*old(self),input.wf(),input.namespace(bank.namespace()),source.wf(),input.source().result is Scalar,source.slot()==input.source().result->Scalar_write.binding.capture_spec().slot(),identity.wf(),identity.number_spec().is_some(),
                identity.namespace()==bank.namespace(),identity.address()==(Address {journal:source.slot().journal_spec(),key:source.slot().key()}),i<=self.entries.len(),
                forall|j:int|0<=j<i ==> self.source(j)!=identity.address(),
            decreases self.entries.len()-i,
        {if self.entries[i].source.same(&identity)==Some(true) {return Ok(i);}i+=1;}
        let value=match bank.seed(index).unwrap() {Seed::Scalar(v)=>v,_=>return Err(Error::NotScalar)};
        let service=Arc::new(Slot::new_reversible(Arc::new(value.clone()),()));let handle=service.reversible().unwrap();
        let capture=handle.capture();if capture.revision()!=0 {return Err(Error::ChangedTarget);}
        proof {capture.initial_selection();bank.target_facts(index as int);}
        let target=handle.identity();if target.number().is_none() {return Err(Error::Unnamed);}
        let ghost prior=*self;
        let mut j=0;
        while j<self.entries.len()
            invariant bank.wf(),self.wf(bank),*self==prior,*self==*old(self),i==self.entries.len(),
                forall|k:int|0<=k<self.entries.len() ==> self.source(k)!=identity.address(),
                target.wf(),target.number_spec().is_some(),target.namespace()==bank.journal().identity_namespace(),j<=self.entries.len(),
                forall|k:int|0<=k<j ==> self.target(k)!=target.address(),
            decreases self.entries.len()-j,
        {if self.entries[j].target.same(&target)!=Some(false) {return Err(Error::Allocation);}j+=1;}
        let ghost previous=self.entries@;
        self.entries.push(Entry {source:identity,target,source_selection:source.duplicate(),target_selection:capture,service,initial:index,selected:index,
            versions:Ghost(Map::empty().insert(source.revision_spec(),0))});
        proof {
            assert(self.entries@[i as int].wf(bank));
            assert forall|a:int,b:int|0<=a<b<self.entries.len() implies self.source(a)!=self.source(b) && self.target(a)!=self.target(b) by {
                assert(self.source(a)==prior.source(a));assert(self.target(a)==prior.target(a));
                if b<i {assert(self.source(b)==prior.source(b));assert(self.target(b)==prior.target(b));assert(prior.source(a)!=prior.source(b));assert(prior.target(a)!=prior.target(b));}
                else {assert(b==i);assert(self.source(b)==identity.address());assert(self.target(b)==target.address());assert(prior.source(a)!=identity.address());assert(prior.target(a)!=target.address());}
            }
        }Ok(i)
    }
    /// Advance once per new source version, atomically refusing a target that
    /// changed since our retained capture. Repeated reads preserve one mapping.
    #[verifier::rlimit(16)]
    pub fn advance(&mut self,bank:&Bank<T>,entry:usize,input:&Input<T>,index:usize)->(out:Result<(),Error>)
        requires bank.wf(),old(self).wf(bank),input.wf(),input.namespace(bank.namespace()),
            index<bank.len_spec(),bank.address(index as int)==input.source().address(),
        ensures final(self).wf(bank),final(self).frame(old(self)),
            out.is_ok() ==> entry<final(self).len_spec() && final(self).selected(entry as int)==index
                && input.source().result is Scalar
                && final(self).source(entry as int)==(Address {journal:input.source().result->Scalar_write.binding.capture_spec().slot().journal_spec(),key:input.source().result->Scalar_write.binding.capture_spec().slot().key()})
                && final(self).versions(entry as int).contains_pair(input.source().result->Scalar_write.binding.capture_spec().revision_spec(),final(self).capture(entry as int).revision_spec()),
    {
        hide(joint::valid);hide(joint::step);
        if entry>=self.entries.len() {return Err(Error::Allocation);}
        let source=match input.selected_slot() {Some(c)=>c,None=>return Err(Error::NotScalar)};let identity=source.slot_ref().identity();
        let prior=&self.entries[entry];
        if prior.source.same(&identity)!=Some(true) {return Err(Error::Allocation);}
        if source.same_revision_at(&prior.source_selection) {
            if index!=prior.selected {return Err(Error::ChangedSource);}return Ok(());
        }
        if source.revision()<prior.source_selection.revision() {return Err(Error::StaleSource);}
        let value=match bank.seed(index).unwrap() {Seed::Scalar(v)=>v,_=>return Err(Error::NotScalar)};
        let slot=prior.service.reversible().unwrap();
        let replacement=match slot.replace_captured(&prior.target_selection,Arc::new(value.clone())) {Ok(r)=>r,Err(e)=>return Err(Error::Target(e))};
        let (_,current)=replacement.observations();
        let ghost old_entry=*prior;
        proof {super::typed::extend(prior.versions@,prior.source_selection.revision_spec(),prior.target_selection.revision_spec(),source.revision_spec(),current.revision_spec());super::typed_correspondence::epochs::ordered_extend(prior.versions@,prior.source_selection.revision_spec(),prior.target_selection.revision_spec(),source.revision_spec(),current.revision_spec());}
        let updated=Entry {source:prior.source.clone(),target:prior.target.clone(),source_selection:source.duplicate(),target_selection:current.duplicate(),service:prior.service.clone(),initial:prior.initial,selected:index,
            versions:Ghost(prior.versions@.insert(source.revision_spec(),current.revision_spec()))};
        proof {assert(updated.wf(bank));}
        let ghost prior_entries=self.entries@;
        self.entries.set(entry,updated);
        proof {
            assert forall|i:int|0<=i<self.entries.len() implies (#[trigger] self.entries@[i]).wf(bank) by {
                if i==entry {} else {assert(self.entries@[i]==prior_entries[i]);}
            }
            assert forall|i:int|0<=i<self.len_spec() implies self.source(i)==old(self).source(i) && self.target(i)==old(self).target(i)
                && self.service(i)==old(self).service(i) && self.initial(i)==old(self).initial(i) by {
                if i==entry {} else {assert(self.entries@[i]==prior_entries[i]);}
            }
            assert(self.frame(old(self)));
            assert forall|i:int,j:int|0<=i<j<self.entries.len() implies self.source(i)!=self.source(j) && self.target(i)!=self.target(j) by {
                assert(old(self).source(i)!=old(self).source(j));assert(old(self).target(i)!=old(self).target(j));
            }
        }Ok(())
    }
    pub proof fn aliases(&self,bank:&Bank<T>,a:int,b:int)
        requires self.wf(bank),0<=a<self.len_spec(),0<=b<self.len_spec(),
        ensures (self.source(a)==self.source(b))==(self.target(a)==self.target(b)),
    {if a<b {} else if b<a {}}
}
}

verus! {
pub open spec fn provider<E,T:?Sized>(bank:&Bank<T>,slots:&Slots<T>,p:super::batch::Provider<E,T>,sources:Map<usize,crate::lifecycle_state::services::capture::Source<Slot<T,()>>>)->bool {
    p.index<bank.len_spec() && sources.contains_key(p.id)
        && sources[p.id].values.contains_pair((p.port.key,p.port.realm),p.service)
        && match p.slot {
            Some(i)=>i<slots.len_spec() && p.service==slots.service(i as int) && p.index==slots.initial(i as int),
            None=>p.service==bank.service(p.index as int),
        }
}
pub open spec fn published<E,T:?Sized>(bank:&Bank<T>,slots:&Slots<T>,providers:Seq<super::batch::Provider<E,T>>,sources:Map<usize,crate::lifecycle_state::services::capture::Source<Slot<T,()>>>)->bool {
    forall|i:int|0<=i<providers.len() ==> provider(bank,slots,#[trigger] providers[i],sources)
}
pub proof fn preserve<E,T:?Sized>(bank:&Bank<T>,slots:&Slots<T>,providers:Seq<super::batch::Provider<E,T>>,
    before:Map<usize,crate::lifecycle_state::services::NativePublication<Slot<T,()>>>,after:Map<usize,crate::lifecycle_state::services::NativePublication<Slot<T,()>>>)
    requires published(bank,slots,providers,crate::lifecycle_state::services::capture::sources(before)),before.submap_of(after),
    ensures published(bank,slots,providers,crate::lifecycle_state::services::capture::sources(after)),
{
    assert forall|i:int|0<=i<providers.len() implies provider(bank,slots,#[trigger] providers[i],crate::lifecycle_state::services::capture::sources(after)) by {
        let p=providers[i];
        assert(provider(bank,slots,p,crate::lifecycle_state::services::capture::sources(before)));
        assert(before.dom().contains(p.id));
        assert(after.dom().contains(p.id) && before[p.id]==after[p.id]) by {reveal(Map::submap_of);}
    }
}
pub proof fn remove_unrelated<E,T:?Sized>(bank:&Bank<T>,slots:&Slots<T>,providers:Seq<super::batch::Provider<E,T>>,
    before:Map<usize,crate::lifecycle_state::services::NativePublication<Slot<T,()>>>,after:Map<usize,crate::lifecycle_state::services::NativePublication<Slot<T,()>>>,id:usize)
    requires published(bank,slots,providers,crate::lifecycle_state::services::capture::sources(before)),after==before || after==before.remove(id),
        forall|i:int|0<=i<providers.len() ==> (#[trigger] providers[i]).id!=id,
    ensures published(bank,slots,providers,crate::lifecycle_state::services::capture::sources(after)),
{
    assert forall|i:int|0<=i<providers.len() implies provider(bank,slots,#[trigger] providers[i],crate::lifecycle_state::services::capture::sources(after)) by {
        let p=providers[i];assert(p.id!=id);assert(provider(bank,slots,p,crate::lifecycle_state::services::capture::sources(before)));assert(before.dom().contains(p.id));assert(before[p.id]==after[p.id]);
    }
}
pub proof fn extend_published<E,T:?Sized>(bank:&Bank<T>,slots:&Slots<T>,prior:&Slots<T>,providers:Seq<super::batch::Provider<E,T>>,sources:Map<usize,crate::lifecycle_state::services::capture::Source<Slot<T,()>>>)
    requires slots.len_spec()>=prior.len_spec(),
        forall|i:int|0<=i<prior.len_spec() ==> slots.service(i)==prior.service(i) && slots.initial(i)==prior.initial(i),
        published(bank,prior,providers,sources),
    ensures published(bank,slots,providers,sources),
{
    assert forall|i:int|0<=i<providers.len() implies provider(bank,slots,#[trigger] providers[i],sources) by {
        let p=providers[i];assert(provider(bank,prior,p,sources));if p.slot.is_some() {let n=p.slot.unwrap() as int;assert(slots.service(n)==prior.service(n));assert(slots.initial(n)==prior.initial(n));}
    }
}
pub proof fn frame_published<E,T:?Sized>(bank:&Bank<T>,slots:&Slots<T>,prior:&Slots<T>,providers:Seq<super::batch::Provider<E,T>>,sources:Map<usize,crate::lifecycle_state::services::capture::Source<Slot<T,()>>>)
    requires slots.frame(prior),published(bank,prior,providers,sources),ensures published(bank,slots,providers,sources),
{}
}

pub(crate) mod storage;
