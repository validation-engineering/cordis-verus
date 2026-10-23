//! One target allocation per captured source allocation. Later operands reuse
//! the actual object; outstanding inverse depth is produced by earlier calls.
use super::super::Slot;
use super::inputs::{Input, Operand, Seed, SeedError};
use crate::reversible_value::joint::{self, identity::AllocationIdentity};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::service_composition::Address;
use std::sync::Arc;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum Error {Unnamed,Seed(SeedError),KindMismatch}
#[allow(dead_code)]
struct Entry<T:?Sized> {source:Arc<AllocationIdentity>,seed:Seed<T>,slot:Arc<Slot<T,()>>,first:Input<T>}
#[allow(dead_code)] // Namespace evidence erases.
pub struct Bank<T:?Sized> {journal:joint::Journal,entries:Vec<Entry<T>>,namespace:Ghost<vstd::resource::Loc>,frontier:Tracked<Option<joint::Receipt>>}
impl<T:?Sized> Bank<T> {
    pub closed spec fn namespace(&self)->vstd::resource::Loc {self.namespace@}
    pub closed spec fn journal(&self)->joint::Journal {self.journal}
    pub closed spec fn len_spec(&self)->nat {self.entries@.len()}
    pub closed spec fn address(&self,i:int)->crate::reversible_value::service_composition::Address {self.entries@[i].source.address()}
    pub closed spec fn target(&self,i:int)->Seed<T> {self.entries@[i].seed}
    pub closed spec fn service(&self,i:int)->Arc<Slot<T,()>> {self.entries@[i].slot}
    pub open spec fn target_address(&self,i:int)->Address {self.target(i).address()}
    pub closed spec fn frontier(&self)->Option<joint::Receipt> {self.frontier@}
    /// The source-to-target map is extracted from actual allocations, including
    /// aliases reused by subsequent calls. Its values are not caller inputs.
    pub closed spec fn mapping(&self)->Map<Address,Address> {
        Map::new(self.entries@.map(|_:int,e:Entry<T>|e.source.address()).to_set(),
            |a:Address|self.target_address(choose|i:int|0<=i<self.len_spec() && self.address(i)==a))
    }
    pub closed spec fn wf(&self)->bool {
        (self.frontier().is_some()==(self.entries.len()>0)) && (forall|i:int|0<=i<self.entries.len() ==> {
            let e=#[trigger] self.entries@[i];
            &&& e.source.wf() && e.source.namespace()==self.namespace() && e.source.number_spec().is_some()
            &&& e.seed.journal()==self.journal() && e.first.wf() && e.first.identity_spec().namespace()==self.namespace() && e.first.source().address()==e.source.address()
            &&& super::transport::values(e.first.source().before(),e.seed.initial())
            &&& seed_slot(e.seed,*e.slot)
            &&& self.frontier().is_some() && self.frontier().unwrap().events().last().state.contains_key(e.seed.address().key)
        }) && (forall|i:int,j:int|0<=i<j<self.entries.len() ==> self.address(i)!=self.address(j)
            && self.target_address(i)!=self.target_address(j))
            && (self.frontier().is_some() ==> self.frontier().unwrap().wf() && self.frontier().unwrap().journal()==self.journal())
    }
    pub open spec fn extends(&self,prior:&Self)->bool {
        self.namespace()==prior.namespace() && self.journal()==prior.journal() && self.len_spec()>=prior.len_spec()
            && forall|i:int|0<=i<prior.len_spec() ==> self.address(i)==prior.address(i) && self.target(i)==prior.target(i) && self.service(i)==prior.service(i)
    }
    /// The namespace is taken from an actual source Journal. Calls spanning
    /// independent naming namespaces require a separate bank; numeric IDs are
    /// never used to prove cross-namespace equality.
    pub fn new(_source:&joint::Journal,target:&joint::Journal)->(out:Self)
        ensures out.wf(),out.len_spec()==0,out.namespace()==_source.identity_namespace(),out.journal()==*target,
    {Self {journal:target.clone(),entries:Vec::new(),namespace:Ghost(_source.identity_namespace()),frontier:Tracked(None)}}
    pub proof fn aliases(&self,i:int,j:int)
        requires self.wf(),0<=i<self.len_spec(),0<=j<self.len_spec(),
        ensures (self.address(i)==self.address(j))==(i==j),
            (self.target_address(i)==self.target_address(j))==(i==j),
            (self.address(i)==self.address(j))==(self.target_address(i)==self.target_address(j)),
    {if i<j {} else if j<i {}}
    pub proof fn mapping_domain(&self)
        ensures forall|a:Address| #[trigger] self.mapping().contains_key(a) <==> exists|i:int|0<=i<self.len_spec() && self.address(i)==a,
    {
        let keys=self.entries@.map(|_:int,e:Entry<T>|e.source.address());keys.to_set_ensures();
        assert forall|a:Address| #[trigger] self.mapping().contains_key(a) <==> exists|i:int|0<=i<self.len_spec() && self.address(i)==a by {
            if keys.contains(a) {let i=choose|i:int|0<=i<keys.len() && keys[i]==a;assert(self.address(i)==a);}
            if exists|i:int|0<=i<self.len_spec() && self.address(i)==a {
                let i=choose|i:int|0<=i<self.len_spec() && self.address(i)==a;assert(keys[i]==a);assert(keys.contains(a));
            }
        }
    }
    pub proof fn mapping_entry(&self,i:int)
        requires self.wf(),0<=i<self.len_spec(),
        ensures self.mapping().contains_pair(self.address(i),self.target_address(i)),
    {
        self.mapping_domain();assert(self.mapping().contains_key(self.address(i)));
        let j=choose|j:int|0<=j<self.len_spec() && self.address(j)==self.address(i);
        self.aliases(i,j);
    }
    pub proof fn mapping_injective(&self)
        requires self.wf(),
        ensures forall|a:Address,b:Address|self.mapping().contains_key(a) && self.mapping().contains_key(b)
            && #[trigger] self.mapping()[a]==#[trigger] self.mapping()[b] ==> a==b,
    {
        self.mapping_domain();
        assert forall|a:Address,b:Address|self.mapping().contains_key(a) && self.mapping().contains_key(b)
            && #[trigger] self.mapping()[a]==#[trigger] self.mapping()[b] implies a==b by {
            let i=choose|i:int|0<=i<self.len_spec() && self.address(i)==a;
            let j=choose|j:int|0<=j<self.len_spec() && self.address(j)==b;
            self.mapping_entry(i);self.mapping_entry(j);self.aliases(i,j);
        }
    }
    /// Source separation now entails target separation for the existing full
    /// forward/inverse independence theorem. Equal service labels are not used.
    pub proof fn scalar_independence(&self,i:int,j:int,a:crate::reversible_value::effect::Code,b:crate::reversible_value::effect::Code)
        requires self.wf(),0<=i<self.len_spec(),0<=j<self.len_spec(),self.address(i)!=self.address(j),
            self.target(i) is Scalar,self.target(j) is Scalar,
        ensures crate::iterator_bridge::independent(
            crate::dependent_independence::equality(|_:nat,x:crate::reversible_value::ValueState,y:crate::reversible_value::ValueState|x==y),
            crate::dependent_grammar::family(crate::reversible_value::alias::library(),crate::reversible_value::alias::terminal(self.target_address(i).key,a)),(),
            crate::dependent_grammar::family(crate::reversible_value::alias::library(),crate::reversible_value::alias::terminal(self.target_address(j).key,b)),()),
    {
        self.aliases(i,j);
        assert(self.target_address(i).journal==self.target_address(j).journal);
        crate::reversible_value::alias::allocation_independence(self.target_address(i).key,self.target_address(j).key,a,b);
    }
    pub closed spec fn first(&self,i:int)->Input<T> {self.entries@[i].first}
    pub fn first_input(&self,i:usize)->(out:Option<&Input<T>>)
        requires self.wf(),
        ensures out.is_some()==(i<self.len_spec()),out.is_some() ==> *out.unwrap()==self.first(i as int) && out.unwrap().wf()
            && out.unwrap().source().address()==self.address(i as int) && out.unwrap().identity_spec().namespace()==self.namespace()
            && super::transport::values(out.unwrap().source().before(),self.target(i as int).initial()),
    {if i<self.entries.len() {Some(&self.entries[i].first)} else {None}}
    pub proof fn target_facts(&self,i:int) requires self.wf(),0<=i<self.len_spec(),ensures self.target(i).journal()==self.journal(), {}
    pub proof fn seed_facts(&self,i:int)
        requires self.wf(),0<=i<self.len_spec(),
        ensures seed_slot(self.target(i),*self.service(i)),
    {}
    /// Read-only source lookup. The established source namespace is sufficient;
    /// no numeric comparison with a target namespace is performed.
    pub fn find(&self,input:&Input<T>)->(out:Option<usize>)
        requires self.wf(),input.wf(),input.identity_spec().namespace()==self.namespace(),
        ensures out.is_some() ==> out.unwrap()<self.len_spec() && self.address(out.unwrap() as int)==input.source().address(),
    {
        let identity=input.identity();let mut i=0;
        while i<self.entries.len()
            invariant self.wf(),input.wf(),identity.wf(),identity.namespace()==self.namespace(),identity.address()==input.source().address(),i<=self.entries.len(),
            decreases self.entries.len()-i,
        {
            if self.entries[i].source.same(identity)==Some(true) {return Some(i);}
            i+=1;
        }
        None
    }
    pub fn domain(&self)->(out:&joint::Journal) ensures *out==self.journal(), {&self.journal}
    pub fn find_identity(&self,identity:&joint::identity::AllocationIdentity)->(out:Option<usize>)
        requires self.wf(),identity.wf(),identity.namespace()==self.namespace(),identity.number_spec().is_some(),
        ensures out.is_some() ==> out.unwrap()<self.len_spec() && self.address(out.unwrap() as int)==identity.address(),
            out.is_none() ==> forall|i:int|0<=i<self.len_spec() ==> self.address(i)!=identity.address(),
    {
        hide(joint::valid);hide(joint::step);
        let mut i=0;
        while i<self.entries.len()
            invariant self.wf(),identity.wf(),identity.namespace()==self.namespace(),identity.number_spec().is_some(),i<=self.entries.len(),
                forall|j:int|0<=j<i ==> self.address(j)!=identity.address(),
            decreases self.entries.len()-i,
        {if self.entries[i].source.same(identity)==Some(true) {return Some(i);}i+=1;}None
    }
    /// Clone only handles to the actual bank cells and slots. No target value
    /// is copied or read; the caller acquires these handles in one scope.
    #[verifier::rlimit(12)]
    pub(crate) fn scalar_storage(&self)->(out:Option<super::protected::Storage>)
        requires self.wf(),
        ensures out.is_some() ==> out.unwrap().matches(self),
    {
        hide(joint::valid);hide(joint::step);
        let mut values=Vec::new();let mut slots=Vec::new();let mut i=0;
        while i<self.entries.len()
            invariant self.wf(),i<=self.entries.len(),values.len()==i,slots.len()==i,
                forall|j:int|0<=j<i ==> (#[trigger] self.target(j)) is Scalar && values@[j]==self.target(j)->Scalar_0
                    && self.service(j).managed()==Some(slots@[j]) && *slots@[j].initial()==values@[j],
            decreases self.entries.len()-i,
        {
            proof {self.seed_facts(i as int);}
            let value=match &self.entries[i].seed {Seed::Scalar(value)=>value.clone(),_=>return None};
            let slot=match self.entries[i].slot.reversible() {Some(slot)=>slot.clone(),None=>{assert(false);panic!("scalar bank slot")}};
            proof {assert(self.target(i as int) is Scalar);assert(self.service(i as int).managed()==Some(slot));assert(*slot.initial()==value);}
            let ghost previous_values=values@;let ghost previous_slots=slots@;
            values.push(value);slots.push(slot);
            proof {assert forall|j:int|0<=j<i+1 implies (#[trigger] self.target(j)) is Scalar && values@[j]==self.target(j)->Scalar_0
                && self.service(j).managed()==Some(slots@[j]) && *slots@[j].initial()==values@[j] by {
                if j<i {assert(values@[j]==previous_values[j]);assert(slots@[j]==previous_slots[j]);} else {assert(values@[j]==value);assert(slots@[j]==slot);}
            }}
            i+=1;
        }
        proof {assert forall|a:int,b:int|0<=a<b<values.len() implies values@[a]!=values@[b] by {self.aliases(a,b);}}
        Some(super::protected::Storage {values,slots})
    }
    /// Clone retained handles only; the interpreter subsequently locks them.
    pub(crate) fn typed_storage(&self)->(out:Option<super::typed_protected::Storage<T>>)
        requires self.wf(),ensures out.is_some() ==> out.unwrap().matches(self),
    {
        hide(joint::valid);hide(joint::step);
        let mut values:Vec<crate::reversible_value::payload::SharedPayload<T>>=Vec::new();let mut slots:Vec<Arc<Slot<T,()>>>=Vec::new();let mut i=0;
        while i<self.entries.len()
            invariant self.wf(),i<=self.entries.len(),values.len()==i,slots.len()==i,
                forall|j:int|0<=j<i ==> (#[trigger] self.target(j)) is Payload && values@[j]==self.target(j)->Payload_0
                    && slots@[j]==self.service(j) && slots@[j].opaque_spec()==Some(values@[j]),
            decreases self.entries.len()-i,
        {
            proof {self.seed_facts(i as int);}
            let value=match &self.entries[i].seed {Seed::Payload(value)=>value.clone(),_=>return None};
            let slot=self.entries[i].slot.clone();values.push(value);slots.push(slot);i+=1;
        }
        proof {assert forall|a:int,b:int|0<=a<b<values.len() implies values@[a]!=values@[b] by {self.aliases(a,b);}}
        Some(super::typed_protected::Storage {values,slots})
    }
    pub fn len(&self)->(out:usize) ensures out==self.len_spec(), {self.entries.len()}
    pub fn is_empty(&self)->(out:bool) ensures out==(self.len_spec()==0), {self.entries.len()==0}
    pub fn seed(&self,i:usize)->(out:Option<&Seed<T>>)
        ensures out.is_some()==(i<self.len_spec()),out.is_some() ==> *out.unwrap()==self.target(i as int),
    {if i<self.entries.len() {Some(&self.entries[i].seed)} else {None}}
    pub fn slot(&self,i:usize)->(out:Option<Arc<Slot<T,()>>>)
        requires self.wf(),
        ensures out.is_some()==(i<self.len_spec()),out.is_some() ==> out.unwrap()==self.service(i as int) && seed_slot(self.target(i as int),*out.unwrap()),
    {if i<self.entries.len() {Some(self.entries[i].slot.clone())} else {None}}
    pub fn bind(&mut self,input:&Input<T>)->(out:Result<usize,Error>)
        requires old(self).wf(),input.wf(),input.identity_spec().namespace()==old(self).namespace(),
        ensures final(self).wf(),final(self).extends(old(self)),
            out.is_ok() ==> out->Ok_0<final(self).len_spec() && final(self).address(out->Ok_0 as int)==input.source().address(),
            out.is_err() ==> final(self).len_spec()==old(self).len_spec(),
            out.is_ok() && out->Ok_0>=old(self).len_spec() ==> super::transport::values(input.source().before(),final(self).target(out->Ok_0 as int).initial()),
    {
        hide(joint::valid);hide(joint::step);
        let identity=input.identity();
        if identity.number().is_none() {return Err(Error::Unnamed);}
        let mut i=0;
        while i<self.entries.len()
            invariant self.wf(),*self==*old(self),i<=self.entries.len(),
                input.wf(),identity.wf(),identity.address()==input.source().address(),identity.namespace()==self.namespace(),identity.number_spec().is_some(),
                forall|j:int|0<=j<i ==> self.address(j)!=input.source().address(),
            decreases self.entries.len()-i,
        {
            let e=&self.entries[i];
            if e.source.same(identity)==Some(true) {
                let same_kind=matches!((&e.seed,input.operand()),(Seed::Scalar(_),Operand::Scalar(_))|(Seed::Payload(_),Operand::Payload {..}));
                if !same_kind {return Err(Error::KindMismatch);}
                return Ok(i);
            }
            i+=1;
        }
        let ghost previous=*self;
        let tracked prior=match self.frontier.borrow() {Some(receipt)=>Some(receipt.duplicate()),None=>None};
        let (seed,Tracked(birth))=match input.seed_following(&self.journal,Tracked(prior)) {Ok(pair)=>pair,Err(e)=>return Err(Error::Seed(e))};
        proof {
            allocation_state(birth);
            assert forall|j:int|0<=j<self.len_spec() implies birth.events().last().state.contains_key(self.target_address(j).key)
                && self.target_address(j)!=seed.address() by {
                let e=self.entries@[j];
                assert(self.frontier().unwrap().events().last().state.contains_key(e.seed.address().key));
                fresh_after(self.frontier().unwrap(),birth,self.target_address(j).key);
            }
        }
        let ghost checkpoint=birth;
        let slot=seed.as_slot();
        self.frontier=Tracked(Some(birth));
        self.entries.push(Entry {source:identity.clone(),seed,slot,first:input.duplicate()});
        proof {
            assert(self.frontier().is_some()==(self.entries.len()>0));
            assert(self.frontier().unwrap().wf() && self.frontier().unwrap().journal()==self.journal());
            assert forall|j:int|0<=j<self.entries.len() implies {
                let e=#[trigger] self.entries@[j];
                &&& e.source.wf() && e.source.namespace()==self.namespace() && e.source.number_spec().is_some()
                &&& e.seed.journal()==self.journal() && e.first.wf() && e.first.identity_spec().namespace()==self.namespace() && e.first.source().address()==e.source.address()
                &&& super::transport::values(e.first.source().before(),e.seed.initial())
                &&& seed_slot(e.seed,*e.slot)
                &&& self.frontier().is_some() && self.frontier().unwrap().events().last().state.contains_key(e.seed.address().key)
            } by {
                assert(self.frontier()==Some(checkpoint));
                if j<i {
                    assert(self.entries@[j]==previous.entries@[j]);
                    assert(checkpoint.events().last().state.contains_key(previous.target_address(j).key));
                } else {
                    assert(self.entries@[j].seed==seed);assert(self.entries@[j].first.source()==input.source());
                    assert(checkpoint.event().key==seed.address().key);
                    assert(checkpoint.events().last().state.contains_key(seed.address().key));
                }
                let e=self.entries@[j];
                assert(e.source.wf());
                assert(e.source.namespace()==self.namespace());
                assert(e.source.number_spec().is_some());
                assert(e.seed.journal()==self.journal());
                assert(e.first.wf());
                assert(e.first.source().address()==e.source.address());
                assert(super::transport::values(e.first.source().before(),e.seed.initial()));
                assert(seed_slot(e.seed,*e.slot));
                assert(self.frontier().unwrap().events().last().state.contains_key(e.seed.address().key));
            }
            assert forall|a:int,b:int|0<=a<b<self.entries.len() implies self.address(a)!=self.address(b) && self.target_address(a)!=self.target_address(b) by {
                assert(self.address(a)==previous.address(a));assert(self.target_address(a)==previous.target_address(a));
                if b==i {
                    assert(previous.address(a)!=input.source().address());assert(self.address(b)==input.source().address());
                    assert(self.target_address(b)==seed.address());assert(previous.target_address(a)!=seed.address());
                } else {
                    assert(self.address(b)==previous.address(b));assert(previous.address(a)!=previous.address(b));
                    assert(self.target_address(b)==previous.target_address(b));assert(previous.target_address(a)!=previous.target_address(b));
                }
            }
        }
        Ok(i)
    }
}
/// An actual allocation following an actual earlier checkpoint is fresh with
/// respect to every previously retained key; no numeric identity bound is used.
proof fn allocation_state(birth:joint::Receipt)
    requires birth.wf(),birth.event().change==joint::Change::Allocate,
    ensures birth.events().last().state.contains_key(birth.event().key),
{assert(joint::step(joint::state_at(birth.events(),birth.at()),birth.events().last().state,birth.event()));}
proof fn fresh_after(earlier:joint::Receipt,birth:joint::Receipt,key:nat)
    requires earlier.wf(),birth.wf(),birth.follows(&earlier),birth.event().change==joint::Change::Allocate,
        earlier.events().last().state.contains_key(key),
    ensures birth.events().last().state.contains_key(key),key!=birth.event().key,
{
    let frames=birth.events();
    assert(joint::state_at(frames,earlier.events().len())==earlier.events().last().state);
    joint::key_persists(frames,earlier.events().len(),birth.at(),key);
    assert(joint::step(joint::state_at(frames,birth.at()),frames.last().state,birth.event()));
}
pub open spec fn seed_slot<T:?Sized>(seed:Seed<T>,slot:Slot<T,()>)->bool {
    match seed {Seed::Scalar(value)=>slot.managed().is_some() && *slot.managed().unwrap().initial()==value && slot.managed().unwrap().journal_spec()==value.journal_spec(),
        Seed::Payload(value)=>slot.opaque_spec()==Some(value)}
}
impl<T:?Sized> Seed<T> {
    pub fn as_slot(&self)->(out:Arc<Slot<T,()>>)
        ensures seed_slot(*self,*out),
    {
        match self {
            Self::Scalar(value)=>Arc::new(Slot::new_reversible(Arc::new(value.clone()),())),
            Self::Payload(value)=>Arc::new(Slot::new_opaque(value.clone(),())),
        }
    }
}
}

#[path = "managed_replay_heap.rs"]
pub mod heap;
verus! {
impl<T:?Sized> Bank<T> {
    /// A view retains the same actual allocations, source identities, slots and
    /// birth frontier. It never allocates replacement target storage.
    pub(crate) fn select(&self,indices:&[usize])->(out:Self)
        requires self.wf(),forall|i:int|0<=i<indices.len() ==> (#[trigger] indices@[i])<self.len_spec(),
            forall|i:int,j:int|0<=i<j<indices.len() ==> indices@[i]<indices@[j],
        ensures out.wf(),out.namespace()==self.namespace(),out.journal()==self.journal(),out.len_spec()==indices.len(),
            forall|i:int|0<=i<indices.len() ==> out.address(i)==self.address(indices@[i] as int)
                && out.target(i)==self.target(indices@[i] as int) && out.service(i)==self.service(indices@[i] as int),
    {
        hide(joint::valid);hide(joint::step);
        let mut entries:Vec<Entry<T>>=Vec::new();let mut i=0;
        while i<indices.len()
            invariant self.wf(),i<=indices.len(),entries.len()==i,
                forall|j:int|0<=j<indices.len() ==> (#[trigger] indices@[j])<self.len_spec(),
                forall|j:int,k:int|0<=j<k<indices.len() ==> indices@[j]<indices@[k],
                forall|j:int|0<=j<entries.len() ==> (#[trigger] entries@[j]).source==self.entries@[indices@[j] as int].source
                    && entries@[j].seed==self.entries@[indices@[j] as int].seed && entries@[j].slot==self.entries@[indices@[j] as int].slot
                    && entries@[j].first.wf() && entries@[j].first.source()==self.entries@[indices@[j] as int].first.source()
                    && entries@[j].first.identity_spec()==self.entries@[indices@[j] as int].first.identity_spec(),
            decreases indices.len()-i,
        {
            let entry=&self.entries[indices[i]];
            let seed=match &entry.seed {Seed::Scalar(value)=>Seed::Scalar(value.clone()),Seed::Payload(value)=>Seed::Payload(value.clone())};
            entries.push(Entry {source:entry.source.clone(),seed,slot:entry.slot.clone(),first:entry.first.duplicate()});i+=1;
        }
        proof {if indices.len()>0 {assert(indices@[0]<self.len_spec());assert(self.frontier().is_some());}}
        let tracked frontier=if indices.len()==0 {None} else {Some(self.frontier.borrow().tracked_borrow().duplicate())};
        let out=Self {journal:self.journal.clone(),namespace:self.namespace,entries,frontier:Tracked(frontier)};
        proof {
            assert forall|j:int|0<=j<out.entries.len() implies {
                let e=#[trigger] out.entries@[j];let old=self.entries@[indices@[j] as int];
                &&& e.source.wf() && e.source.namespace()==out.namespace() && e.source.number_spec().is_some()
                &&& e.seed.journal()==out.journal() && e.first.wf() && e.first.identity_spec().namespace()==out.namespace() && e.first.source().address()==e.source.address()
                &&& super::transport::values(e.first.source().before(),e.seed.initial()) && seed_slot(e.seed,*e.slot)
                &&& out.frontier().is_some() && out.frontier().unwrap().events().last().state.contains_key(e.seed.address().key)
            } by {assert(self.frontier().unwrap().events().last().state.contains_key(self.entries@[indices@[j] as int].seed.address().key));}
        }
        proof {
            assert forall|j:int,k:int|0<=j<k<out.len_spec() implies out.address(j)!=out.address(k) && out.target_address(j)!=out.target_address(k) by {
                self.aliases(indices@[j] as int,indices@[k] as int);
            }
        }
        out
    }
}
}
