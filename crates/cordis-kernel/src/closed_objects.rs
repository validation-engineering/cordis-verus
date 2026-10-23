//! Object names are scoped to actual native allocations. The table is built
//! by kernel allocation; callers cannot install an invented identity or an
//! opaque Rust value. Retaining an entry also retains its historical identity.
use super::{Kind, Reference, Value};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::service_composition::Address;
use crate::reversible_value::{
    joint,
    managed::replay::{bank::Bank, inputs::Seed},
    payload::SharedPayload,
    ReversibleValue,
};
use std::sync::Arc;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub enum Object {Scalar(ReversibleValue),Payload(SharedPayload<Value>)}
impl Object {
    pub open spec fn kind(&self)->Kind {match self {Self::Scalar(_)=>Kind::Scalar,Self::Payload(_)=>Kind::Payload}}
    pub open spec fn address(&self)->Address {match self {Self::Scalar(v)=>Address {journal:v.journal_spec(),key:v.object().key},Self::Payload(v)=>Address {journal:v.journal_spec(),key:v.key()}}}
    fn identity(&self)->(out:Arc<joint::identity::AllocationIdentity>) ensures out.wf(),out.address()==self.address(),
    {match self {Self::Scalar(v)=>v.identity(),Self::Payload(v)=>v.identity()}}
    fn kind_value(&self)->(out:Kind) ensures out==self.kind(), {match self {Self::Scalar(_)=>Kind::Scalar,Self::Payload(_)=>Kind::Payload}}
}
pub open spec fn service_address(slot:Arc<crate::reversible_value::managed::Slot<Value,()>>)->Address {
    if slot.managed().is_some() {let value=slot.managed().unwrap().initial();Address {journal:value.journal_spec(),key:value.object().key}}
    else {let value=slot.opaque_spec().unwrap();Address {journal:value.journal_spec(),key:value.key()}}
}
struct Entry {object:Object,identity:Arc<joint::identity::AllocationIdentity>,name:u64}
pub struct Table {journal:joint::Journal,entries:Vec<Entry>}
#[derive(Debug)]
pub enum Error {Unnamed,Kind,Reference,History,Alias,Missing {object:usize}}
impl Table {
    pub closed spec fn journal(&self)->joint::Journal {self.journal}
    pub closed spec fn len_spec(&self)->nat {self.entries@.len()}
    pub closed spec fn address(&self,i:int)->Address {self.entries@[i].object.address()}
    pub closed spec fn kinds(&self)->Seq<Kind> {self.entries@.map(|_:int,e:Entry|e.object.kind())}
    pub closed spec fn schema(&self)->Seq<Reference> {self.entries@.map(|i:int,e:Entry|Reference {index:i as usize,kind:e.object.kind(),name:e.name})}
    pub closed spec fn wf(&self)->bool {
        (forall|i:int|0<=i<self.entries.len() ==> {
            let e=#[trigger] self.entries@[i];
            &&& e.identity.wf() && e.identity.number_spec().is_some() && e.identity.address()==e.object.address()
            &&& e.object.address().journal==self.journal() && e.identity.namespace()==self.journal().identity_namespace()
        }) && forall|i:int,j:int|0<=i<j<self.entries.len() ==> self.address(i)!=self.address(j) && self.entries@[i].name!=self.entries@[j].name
    }
    pub open spec fn extends(&self,prior:&Self)->bool {self.len_spec()>=prior.len_spec() && forall|i:int|0<=i<prior.len_spec() ==> self.address(i)==prior.address(i) && self.kinds()[i]==prior.kinds()[i] && self.schema()[i]==prior.schema()[i]}
    pub open spec fn admits(&self,r:Reference)->bool {r.index<self.len_spec() && self.schema()[r.index as int]==r}
    pub open spec fn resolve(&self,r:Reference)->Address {self.address(r.index as int)}
    pub proof fn shape(&self) ensures self.kinds().len()==self.len_spec(),self.schema().len()==self.len_spec(),super::layout(self.schema()), {assert forall|i:int|0<=i<self.schema().len() implies (#[trigger] self.schema()[i]).index==i by {assert(0<=i<self.entries.len());assert(i<=usize::MAX);}}
    pub fn new(journal:&joint::Journal)->(out:Self) ensures out.wf(),out.journal()==*journal,out.len_spec()==0,
    {Self {journal:journal.clone(),entries:Vec::new()}}
    pub open spec fn contains(&self,address:Address)->bool {exists|i:int|0<=i<self.len_spec() && self.address(i)==address}
    /// Match an authentic allocation identity, never a caller's numeric name.
    pub fn contains_identity(&self,identity:&joint::identity::AllocationIdentity)->(out:bool)
        requires self.wf(),identity.wf(),identity.namespace()==self.journal().identity_namespace(),
        ensures out ==> self.contains(identity.address()),
    {
        let mut i=0;
        while i<self.entries.len()
            invariant self.wf(),identity.wf(),identity.namespace()==self.journal().identity_namespace(),i<=self.entries.len(),
            decreases self.entries.len()-i,
        {
            if self.entries[i].identity.same(identity)==Some(true) {
                proof {assert(self.address(i as int)==identity.address());}
                return true;
            }i+=1;
        }false
    }
    pub fn len(&self)->(out:usize) ensures out==self.len_spec(), {self.entries.len()}
    pub fn is_empty(&self)->(out:bool) ensures out==(self.len_spec()==0), {self.entries.is_empty()}
    pub fn domain(&self)->(out:&joint::Journal) ensures *out==self.journal(), {&self.journal}
    pub fn kind_list(&self)->(out:Vec<Kind>) ensures out@==self.kinds(),
    {
        let mut out=Vec::new();let mut i=0;
        while i<self.entries.len()
            invariant i<=self.entries.len(),out.len()==i,forall|j:int|0<=j<i ==> out@[j]==self.kinds()[j],
            decreases self.entries.len()-i,
        {out.push(self.entries[i].object.kind_value());i+=1;}
        proof {assert(out@ =~= self.kinds());}out
    }
    pub fn reference_list(&self)->(out:Vec<Reference>) ensures out@==self.schema(),
    {
        let mut out=Vec::new();let mut i=0;
        while i<self.entries.len()
            invariant i<=self.entries.len(),out.len()==i,forall|j:int|0<=j<i ==> out@[j]==self.schema()[j],
            decreases self.entries.len()-i,
        {out.push(Reference {index:i,kind:self.entries[i].object.kind_value(),name:self.entries[i].name});i+=1;}
        proof {assert(out@ =~= self.schema());}out
    }
    fn insert(&mut self,object:Object)->(out:Result<Reference,Error>)
        requires old(self).wf(),object.address().journal==old(self).journal(),
        ensures final(self).wf(),final(self).journal()==old(self).journal(),final(self).extends(old(self)),
            out.is_ok() ==> final(self).admits(out->Ok_0) && final(self).resolve(out->Ok_0)==object.address() && out->Ok_0.kind==object.kind(),
    {
        let identity=object.identity();let name=match identity.number() {Some(n)=>n,None=>return Err(Error::Unnamed)};
        self.insert_named(object,name)
    }
    // Only the checked Projection may rebind a source logical name to a new
    // physical allocation. The physical identity map is proved independently.
    fn insert_named(&mut self,object:Object,name:u64)->(out:Result<Reference,Error>)
        requires old(self).wf(),object.address().journal==old(self).journal(),
        ensures final(self).wf(),final(self).journal()==old(self).journal(),
            final(self).extends(old(self)),final(self).len_spec()<=old(self).len_spec()+1,
            forall|i:int|0<=i<old(self).len_spec() ==> final(self).address(i)==old(self).address(i) && final(self).kinds()[i]==old(self).kinds()[i],
            out.is_ok() ==> final(self).admits(out->Ok_0) && final(self).resolve(out->Ok_0)==object.address() && out->Ok_0.kind==object.kind() && out->Ok_0.name==name,
    {
        let identity=object.identity();if identity.number().is_none() {return Err(Error::Unnamed);}
        let kind=object.kind_value();let mut i=0;
        while i<self.entries.len()
            invariant self.wf(),*self==*old(self),i<=self.entries.len(),identity.wf(),identity.number_spec().is_some(),
                identity.address()==object.address(),object.address().journal==self.journal(),kind==object.kind(),
                forall|j:int|0<=j<i ==> self.address(j)!=object.address() && self.entries@[j].name!=name,
            decreases self.entries.len()-i,
        {
            if self.entries[i].identity.same(&identity)==Some(true) {
                if self.entries[i].object.kind_value()!=kind || self.entries[i].name!=name {return Err(Error::Kind);}
                return Ok(Reference {index:i,kind,name});
            }
            if self.entries[i].name==name {return Err(Error::Alias);}
            proof {assert(self.address(i as int)!=object.address());assert(self.entries@[i as int].name!=name);assert forall|j:int|0<=j<i+1 implies self.address(j)!=object.address() && self.entries@[j].name!=name by {if j<i {assert(self.address(j)!=object.address());assert(self.entries@[j].name!=name);} else {assert(j==i);}}}
            i+=1;
        }
        let ghost before=self.entries@;
        self.entries.push(Entry {object,identity,name});
        proof {
            assert forall|j:int|0<=j<self.entries.len() implies {
                let e=#[trigger] self.entries@[j];
                &&& e.identity.wf() && e.identity.number_spec().is_some() && e.identity.address()==e.object.address()
                &&& e.object.address().journal==self.journal() && e.identity.namespace()==self.journal().identity_namespace()
            } by {if j<i {assert(self.entries@[j]==before[j]);}}
            assert forall|a:int,b:int|0<=a<b<self.entries.len() implies self.address(a)!=self.address(b) && self.entries@[a].name!=self.entries@[b].name by {
                if b<i {assert(self.address(a)==old(self).address(a));assert(self.address(b)==old(self).address(b));}
                else {assert(b==i);assert(a<i);assert(old(self).address(a)!=object.address());assert(self.address(a)==old(self).address(a));}
            }
        }
        Ok(Reference {index:i,kind,name})
    }
    pub fn allocate_scalar(&mut self,value:u64)->(out:Result<Reference,Error>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).journal()==old(self).journal(),final(self).extends(old(self)),
            out.is_ok() ==> final(self).admits(out->Ok_0) && out->Ok_0.kind==Kind::Scalar,
    {let object=ReversibleValue::new_in(&self.journal,value);self.insert(Object::Scalar(object))}
    pub fn allocate_payload(&mut self,value:Value)->(out:Result<Reference,Error>)
        requires old(self).wf(),value.wf(),
        ensures final(self).wf(),final(self).journal()==old(self).journal(),final(self).extends(old(self)),
            out.is_ok() ==> final(self).admits(out->Ok_0) && out->Ok_0.kind==Kind::Payload,
    {
        if !value.check(self.reference_list().as_slice()) {return Err(Error::Reference);}
        let object=SharedPayload::new_in(&self.journal,Arc::new(value));self.insert(Object::Payload(object))
    }
    pub fn scalar(&self,r:Reference)->(out:Option<&ReversibleValue>)
        requires self.wf(),
        ensures out.is_some() ==> self.admits(r) && r.kind==Kind::Scalar && self.resolve(r)==(Address {journal:out.unwrap().journal_spec(),key:out.unwrap().object().key}),
    {
        if r.kind!=Kind::Scalar || r.index>=self.entries.len() || self.entries[r.index].name!=r.name {return None;}
        match &self.entries[r.index].object {Object::Scalar(v)=>Some(v),_=>None}
    }
    pub fn payload(&self,r:Reference)->(out:Option<&SharedPayload<Value>>)
        requires self.wf(),
        ensures out.is_some() ==> self.admits(r) && r.kind==Kind::Payload && self.resolve(r)==(Address {journal:out.unwrap().journal_spec(),key:out.unwrap().key()}),
    {
        if r.kind!=Kind::Payload || r.index>=self.entries.len() || self.entries[r.index].name!=r.name {return None;}
        match &self.entries[r.index].object {Object::Payload(v)=>Some(v),_=>None}
    }
}
/// Source and target retain the same local indices in different real tables.
/// This is an explicit change of interpretation, not global reuse of a number.
#[allow(dead_code)] // Indices and checkpoint origins tie the actual tables to their erased map.
pub struct Projection {source:Table,target:Table,indices:Vec<Option<usize>>,extras:Vec<Ghost<Option<copy::Copy>>>}
impl Projection {
    pub closed spec fn source(&self)->Table {self.source}
    pub closed spec fn target(&self)->Table {self.target}
    pub closed spec fn wf(&self,bank:&Bank<Value>)->bool {
        self.source.wf() && self.target.wf() && self.source.journal().identity_namespace()==bank.namespace() && self.target.journal()==bank.journal() && (forall|i:int|0<=i<bank.len_spec() ==> self.source.contains(#[trigger] bank.address(i))) && self.source.schema()==self.target.schema() && self.source.len_spec()==self.target.len_spec()
            && self.indices.len()==self.source.len_spec() && self.extras.len()==self.indices.len()
            && forall|i:int|0<=i<self.indices.len() ==> match (#[trigger] self.indices@[i]) {
                Some(n)=>n<bank.len_spec() && bank.address(n as int)==self.source.address(i) && bank.target_address(n as int)==self.target.address(i) && self.extras@[i]@.is_none(),
                None=>(forall|k:int|0<=k<bank.len_spec() ==> bank.address(k)!=self.source.address(i)) && self.extras@[i]@.is_some()
                    && self.extras@[i]@.unwrap().from(self.source.entries@[i].object) && self.extras@[i]@.unwrap().object.address()==self.target.address(i),
            }
    }
    pub closed spec fn mapping(&self)->Map<Address,Address> {
        Map::new(self.source.entries@.map(|_:int,e:Entry|e.object.address()).to_set(),
            |a:Address|self.target.address(choose|i:int|0<=i<self.source.len_spec() && self.source.address(i)==a))
    }
    pub fn new(source:Table,bank:&Bank<Value>)->(out:Result<Self,(Table,Error)>)
        requires source.wf(),bank.wf(),source.journal().identity_namespace()==bank.namespace(),
        ensures out.is_ok() ==> out->Ok_0.wf(bank) && out->Ok_0.source()==source,
    {Self::complete(source,bank)}
    /// Complete the table, including objects never visited by any retained
    /// invocation. Visited objects reuse the actual Bank; other objects are
    /// allocated from authenticated zero-debt snapshots or retirement records.
    pub fn complete(source:Table,bank:&Bank<Value>)->(out:Result<Self,(Table,Error)>)
        requires source.wf(),bank.wf(),source.journal().identity_namespace()==bank.namespace(),
        ensures out.is_ok() ==> out->Ok_0.wf(bank) && out->Ok_0.source()==source,
    {
        let mut checked=0;
        while checked<bank.len()
            invariant source.wf(),bank.wf(),source.journal().identity_namespace()==bank.namespace(),checked<=bank.len_spec(),
                forall|j:int|0<=j<checked ==> source.contains(#[trigger] bank.address(j)),
            decreases bank.len_spec()-checked,
        {
            let input=bank.first_input(checked).unwrap();let identity=input.identity();
            if !source.contains_identity(identity) {return Err((source,Error::Missing {object:checked}));}
            checked+=1;
        }
        let journal=bank.domain();let schema=source.reference_list();let mut target=Table::new(journal);let mut indices:Vec<Option<usize>>=Vec::new();let mut extras:Vec<Ghost<Option<copy::Copy>>>=Vec::new();let mut i=0;
        while i<source.entries.len()
            invariant *journal==bank.journal(),source.wf(),bank.wf(),
                forall|j:int|0<=j<bank.len_spec() ==> source.contains(#[trigger] bank.address(j)),source.journal().identity_namespace()==bank.namespace(),target.wf(),target.journal()==bank.journal(),schema@==source.schema(),
                i<=source.entries.len(),indices.len()==i,extras.len()==i,target.len_spec()==i,
                forall|j:int|0<=j<i ==> (#[trigger] source.schema()[j])==target.schema()[j],
                forall|j:int|0<=j<i ==> source.schema()[j]==target.schema()[j]
                    && match (#[trigger] indices@[j]) {
                        Some(n)=>n<bank.len_spec() && bank.address(n as int)==source.address(j) && bank.target_address(n as int)==target.address(j) && extras@[j]@.is_none(),
                        None=>(forall|k:int|0<=k<bank.len_spec() ==> bank.address(k)!=source.address(j)) && extras@[j]@.is_some()
                            && extras@[j]@.unwrap().from(source.entries@[j].object) && extras@[j]@.unwrap().object.address()==target.address(j),
                    },
            decreases source.entries.len()-i,
        {
            let entry=&source.entries[i];let index=bank.find_identity(&entry.identity);
            let (object,Ghost(extra))=match index {
                Some(n)=>{
                    proof {bank.target_facts(n as int);}
                    let object=match bank.seed(n).unwrap() {Seed::Scalar(v)=>Object::Scalar(v.clone()),Seed::Payload(v)=>Object::Payload(v.clone())};
                    if object.kind_value()!=entry.object.kind_value() {return Err((source,Error::Kind));}
                    (object,Ghost(None))
                },
                None=>{
                    let copied=match entry.object.copy_checkpoint(journal,schema.as_slice()) {Ok(c)=>c,Err(e)=>return Err((source,e))};
                    let ghost evidence=copied;(copied.object,Ghost(Some(evidence)))
                },
            };
            proof {assert(object.address().journal==bank.journal());}
            let ghost before=target;
            let name=match target.insert_named(object,entry.name) {Ok(r)=>r,Err(e)=>return Err((source,e))};
            // This runtime guard also rejects accidental alias collapse in a
            // future allocator extension; it is not a caller-supplied premise.
            if name.index!=i {return Err((source,Error::Alias));}
            proof {
                assert(name.kind==source.kinds()[i as int]);assert(name==source.schema()[i as int]);
                assert(before.len_spec()==i);
                assert(target.extends(&before));
                assert forall|j:int|0<=j<i+1 implies (#[trigger] source.schema()[j])==target.schema()[j] by {
                    if j<i {assert(before.address(j)==target.address(j) && before.schema()[j]==target.schema()[j]);} else {assert(target.schema()[j]==name);}
                }
            }
            indices.push(index);extras.push(Ghost(extra));i+=1;
        }
        proof {source.shape();target.shape();assert(source.len_spec()==target.len_spec());
            assert forall|j:int|0<=j<source.schema().len() implies source.schema()[j]==target.schema()[j] by {assert(j<indices.len());}
            assert(source.schema() =~= target.schema());}
        Ok(Self {source,target,indices,extras})
    }
    pub proof fn facts(&self,bank:&Bank<Value>) requires self.wf(bank),ensures self.source().wf(),self.target().wf(),self.source().schema()==self.target().schema(),self.source().journal().identity_namespace()==bank.namespace(),self.target().journal()==bank.journal(), {}
    #[allow(unused_variables)] // Bank anchors the erased physical mapping.
    pub fn service(&self,bank:&Bank<Value>,identity:&joint::identity::AllocationIdentity)->(out:Option<Arc<crate::reversible_value::managed::Slot<Value,()>>>)
        requires self.wf(bank),bank.wf(),identity.wf(),identity.namespace()==self.source().journal().identity_namespace(),
        ensures out.is_some() ==> self.mapping().contains_key(identity.address()) && service_address(out.unwrap())==self.mapping()[identity.address()]
            && (out.unwrap().managed().is_some() ==> out.unwrap().managed().unwrap().journal_spec()==bank.journal()),
    {
        let mut i=0;
        while i<self.source.entries.len()
            invariant self.wf(bank),bank.wf(),identity.wf(),identity.namespace()==self.source().journal().identity_namespace(),i<=self.source.entries.len(),
            decreases self.source.entries.len()-i,
        {
            if self.source.entries[i].identity.same(identity)==Some(true) {
                proof {let reference=self.source.schema()[i as int];self.reference(bank,reference);}
                let service=match &self.target.entries[i].object {
                    Object::Scalar(v)=>crate::reversible_value::managed::Slot::new_reversible(Arc::new(v.clone()),()),
                    Object::Payload(v)=>crate::reversible_value::managed::Slot::new_opaque(v.clone(),()),
                };
                return Some(Arc::new(service));
            }i+=1;
        }None
    }
    #[allow(unused_variables)] // The bank is the erased allocation-map witness.
    pub(crate) fn scalar_target(&self,bank:&Bank<Value>,identity:&joint::identity::AllocationIdentity)->(out:Option<Arc<ReversibleValue>>)
        requires self.wf(bank),bank.wf(),identity.wf(),identity.namespace()==self.source().journal().identity_namespace(),
        ensures out.is_some() ==> self.mapping().contains_pair(identity.address(),Address {journal:out.unwrap().journal_spec(),key:out.unwrap().object().key}),
    {
        let mut i=0;
        while i<self.source.entries.len()
            invariant self.wf(bank),bank.wf(),identity.wf(),identity.namespace()==self.source().journal().identity_namespace(),i<=self.source.entries.len(),
            decreases self.source.entries.len()-i,
        {
            if self.source.entries[i].identity.same(identity)==Some(true) {
                proof {let reference=self.source.schema()[i as int];self.reference(bank,reference);}
                return match &self.target.entries[i].object {Object::Scalar(v)=>Some(Arc::new(v.clone())),_=>None};
            }i+=1;
        }None
    }
    pub(crate) proof fn preload_cell(&self,bank:&Bank<Value>,slots:&crate::reversible_value::managed::replay::slots::Slots<Value>,p:crate::reversible_value::managed::replay::services::Preload<Value>,fallback:Arc<crate::reversible_value::managed::Slot<Value,()>>,from:Address)->(out:Address)
        requires self.wf(bank),bank.wf(),slots.wf(bank),p.wf(bank,slots),p.route.is_none() ==> p.service==fallback,
            self.mapping().contains_pair(from,service_address(fallback)),fallback.managed().is_some() ==> fallback.managed().unwrap().journal_spec()==bank.journal(),
        ensures p.route.is_none() ==> out==from,self.mapping().contains_pair(out,service_address(p.service)),p.service.managed().is_some() ==> p.service.managed().unwrap().journal_spec()==bank.journal(),
    {
        if p.route.is_some() {
            let route=p.route.unwrap();let index=route.index as int;bank.target_facts(index);self.extends_bank(bank);
            if route.slot.is_some() {slots.entry_facts(bank,route.slot.unwrap() as int);} else {bank.seed_facts(index);}
            p.service.payload_partition();assert(service_address(p.service)==bank.target_address(index));
            bank.mapping_entry(index);bank.address(index)
        } else {from}
    }
    pub fn source_table(&self)->(out:&Table) ensures *out==self.source(), {&self.source}
    pub fn target_table(&self)->(out:&Table) ensures *out==self.target(), {&self.target}
    pub proof fn reference(&self,bank:&Bank<Value>,r:Reference)
        requires self.wf(bank),bank.wf(),self.source().admits(r),
        ensures self.target().admits(r),self.mapping().contains_pair(self.source().resolve(r),self.target().resolve(r)),
            bank.mapping().contains_key(self.source().resolve(r)) ==> bank.mapping()[self.source().resolve(r)]==self.target().resolve(r),
    {
        let keys=self.source.entries@.map(|_:int,e:Entry|e.object.address());keys.to_set_ensures();
        assert(keys[r.index as int]==self.source().resolve(r));assert(keys.contains(self.source().resolve(r)));
        let j=choose|i:int|0<=i<self.source.len_spec() && self.source.address(i)==self.source().resolve(r);
        if j<r.index {assert(self.source.address(j)!=self.source.address(r.index as int));}
        else if r.index<j {assert(self.source.address(r.index as int)!=self.source.address(j));}
        assert(j==r.index);
        bank.mapping_domain();
        if bank.mapping().contains_key(self.source().resolve(r)) {
            let n=choose|n:int|0<=n<bank.len_spec() && bank.address(n)==self.source().resolve(r);
            assert(self.indices@[r.index as int].is_some());let k=self.indices@[r.index as int].unwrap();bank.mapping_entry(k as int);
        }
    }
    pub proof fn extends_bank(&self,bank:&Bank<Value>)
        requires self.wf(bank),bank.wf(),
        ensures forall|a:Address|bank.mapping().contains_key(a) ==> #[trigger] self.mapping().contains_pair(a,bank.mapping()[a]),
    {
        bank.mapping_domain();
        assert forall|a:Address|bank.mapping().contains_key(a) implies #[trigger] self.mapping().contains_pair(a,bank.mapping()[a]) by {
            let n=choose|n:int|0<=n<bank.len_spec() && bank.address(n)==a;
            assert(self.source.contains(a));let i=choose|i:int|0<=i<self.source.len_spec() && self.source.address(i)==a;
            let r=self.source.schema()[i];self.reference(bank,r);
        }
    }
    pub proof fn aliases(&self,bank:&Bank<Value>,a:Reference,b:Reference)
        requires self.wf(bank),bank.wf(),self.source().admits(a),self.source().admits(b),
        ensures (self.source().resolve(a)==self.source().resolve(b))==(self.target().resolve(a)==self.target().resolve(b)),
    {if a.index<b.index {} else if b.index<a.index {}}
    pub proof fn mapping_domain(&self)
        ensures forall|a:Address|#[trigger] self.mapping().contains_key(a) <==> self.source().contains(a),
    {
        let keys=self.source.entries@.map(|_:int,e:Entry|e.object.address());keys.to_set_ensures();
        assert forall|a:Address|#[trigger] self.mapping().contains_key(a) <==> self.source().contains(a) by {
            if keys.contains(a) {let i=choose|i:int|0<=i<keys.len() && keys[i]==a;assert(self.source.address(i)==a);}
            if self.source.contains(a) {let i=choose|i:int|0<=i<self.source.len_spec() && self.source.address(i)==a;assert(keys[i]==a);assert(keys.contains(a));}
        }
    }
    /// The complete table includes real operands and objects only referenced
    /// by stored or future values. Its map remains injective on that full set.
    pub proof fn mapping_injective(&self,bank:&Bank<Value>)
        requires self.wf(bank),
        ensures super::recovery::injective(self.mapping()),
    {
        self.mapping_domain();
        assert forall|a:Address,b:Address|self.mapping().contains_key(a) && self.mapping().contains_key(b)
            && #[trigger] self.mapping()[a]==#[trigger] self.mapping()[b] implies a==b by {
            assert(self.source.contains(a));assert(self.source.contains(b));
            let i=choose|i:int|0<=i<self.source.len_spec() && self.source.address(i)==a;
            let j=choose|j:int|0<=j<self.source.len_spec() && self.source.address(j)==b;
            if i<j {assert(self.target.address(i)!=self.target.address(j));}
            else if j<i {assert(self.target.address(j)!=self.target.address(i));}
        }
    }
    /// Complete version interpretation: unvisited live payloads use the
    /// authenticated source checkpoint and the fresh target's head zero.
    pub closed spec fn versions(&self,base:spec_fn(Address)->Map<u64,u64>,address:Address)->Map<u64,u64> {
        if self.source.contains(address) {
            let i=choose|i:int|0<=i<self.source.len_spec() && self.source.address(i)==address;
            match self.extras@[i]@ {
                Some(copy)=>match copy.origin@ {copy::Origin::Payload(c)=>Map::empty().insert(c.observation().state().head,0u64),_=>Map::empty()},
                None=>base(address),
            }
        } else {Map::empty()}
    }
    pub proof fn version_facts(&self,bank:&Bank<Value>,base:spec_fn(Address)->Map<u64,u64>,address:Address)
        requires self.wf(bank),crate::reversible_value::managed::replay::typed::injective(base(address)),crate::reversible_value::managed::replay::typed_correspondence::epochs::ordered(base(address)),
        ensures crate::reversible_value::managed::replay::typed::injective(self.versions(base,address)),crate::reversible_value::managed::replay::typed_correspondence::epochs::ordered(self.versions(base,address)),
    {
        if self.source.contains(address) {
            let i=choose|i:int|0<=i<self.source.len_spec() && self.source.address(i)==address;
            if self.extras@[i]@.is_some() {match self.extras@[i]@.unwrap().origin@ {copy::Origin::Payload(c)=>{let head=c.observation().state().head;assert(self.versions(base,address)==Map::<u64,u64>::empty().insert(head,0u64));},_=>{}}}
        }
    }
    pub proof fn versions_on_bank(&self,bank:&Bank<Value>,base:spec_fn(Address)->Map<u64,u64>,address:Address)
        requires self.wf(bank),bank.wf(),bank.mapping().contains_key(address),
        ensures self.versions(base,address)==base(address),
    {
        bank.mapping_domain();let n=choose|n:int|0<=n<bank.len_spec() && bank.address(n)==address;
        assert(self.source.contains(address));
        let i=choose|i:int|0<=i<self.source.len_spec() && self.source.address(i)==address;
        if self.indices@[i].is_none() {assert(bank.address(n)!=self.source.address(i));}
    }
    /// One complete allocation map relates the actual inverse word while
    /// framing unvisited reference targets. No target success is assumed.
    pub proof fn inverse_word<E:crate::reversible_value::effect::ScalarEffect>(&self,bank:&Bank<Value>,source:&crate::reversible_value::managed::replay::Source<E,Value>,outcome:&crate::reversible_value::managed::replay::session::Outcome<E,Value>,a:Map<Address,crate::reversible_value::managed::semantics::Value<Value>>,b:Map<Address,crate::reversible_value::managed::semantics::Value<Value>>)
        requires self.wf(bank),bank.wf(),source.wf(),source.closed_data(self.source().schema()),outcome.matches(source,bank),
            source.original().result.is_ok(),outcome.run.report.is_ok(),outcome.run.report->Ok_0.result.is_ok(),
            super::recovery::heap(self.mapping(),|k:Address|self.versions(|j:Address|outcome.versions(j),k),self.source().schema(),a,b),
        ensures super::recovery::optional(self.mapping(),|k:Address|self.versions(|j:Address|outcome.versions(j),k),self.source().schema(),
            crate::reversible_value::managed::semantics::undo(source.original().result->Ok_0.steps@,a),
            crate::reversible_value::managed::semantics::undo(outcome.run.report->Ok_0.result->Ok_0.steps@,b)),
    {
        self.extends_bank(bank);self.mapping_injective(bank);outcome.inverse_pairs(source,bank,self.source().schema());
        let x=source.original().result->Ok_0.steps@;let y=outcome.run.report->Ok_0.result->Ok_0.steps@;
        let versions=|k:Address|self.versions(|j:Address|outcome.versions(j),k);
        assert forall|i:int|0<=i<x.len() implies {
            let a=#[trigger] x[i];let b=y[i];
            &&& self.mapping().contains_pair(a.address(),b.address()) && crate::reversible_value::managed::replay::typed::injective(versions(a.address()))
            &&& super::semantics::value(versions(a.address()),self.source().schema(),a.before(),b.before())
            &&& super::semantics::value(versions(a.address()),self.source().schema(),a.after(),b.after())
        } by {self.versions_on_bank(bank,|k:Address|outcome.versions(k),x[i].address());}
        super::recovery::word(self.mapping(),versions,self.source().schema(),x,y,a,b);
    }
    /// Applies to an arbitrary future argument, including references that no
    /// instruction has followed yet. No user Clone, Eq or Drop hook is invoked.
    pub fn accepts(&self,value:&Value)->(out:bool)
        requires value.wf(),self.source().schema()==self.target().schema(),
        ensures out==value.admissible(self.source().schema()),out==value.admissible(self.target().schema()),
    {value.check(self.source.reference_list().as_slice())}
}
}

#[path = "closed_snapshots.rs"]
pub mod copy;
