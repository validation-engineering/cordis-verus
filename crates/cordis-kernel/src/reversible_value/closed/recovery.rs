//! Relate the actual retained inverse words of a protected invocation.
//! Object maps come from real allocations and head maps from real writes.
//! The arbitrary test heaps include missing cells and incorrect current states.
#[cfg(verus_keep_ghost)]
use super::semantics::{equality, value};
#[cfg(verus_keep_ghost)]
use super::Reference;
use super::Value;
use crate::reversible_value::{effect::ScalarEffect, managed::replay::session::Outcome};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{
    managed::{
        self, protected_mixed as held,
        replay::{
            bank::Bank,
            typed,
            typed_correspondence::{self as relation, epochs},
            Source,
        },
        semantics as s,
    },
    service_composition::Address,
};
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub open spec fn injective(mapping:Map<Address,Address>)->bool {
    forall|a:Address,b:Address|mapping.contains_key(a) && mapping.contains_key(b) && #[trigger] mapping[a]==#[trigger] mapping[b] ==> a==b
}
pub open spec fn names<T:?Sized>(view:Bank<T>,certificate:epochs::Certificate<T>,address:Address)->Map<u64,u64> {
    if exists|i:int|0<=i<view.len_spec() && view.address(i)==address {
        certificate.after_names[choose|i:int|0<=i<view.len_spec() && view.address(i)==address]
    } else {Map::empty()}
}
proof fn name_at<T:?Sized>(view:Bank<T>,certificate:epochs::Certificate<T>,i:int)
    requires view.wf(),0<=i<view.len_spec(),certificate.wf(),view.len_spec()==certificate.after_names.len(),
    ensures names(view,certificate,view.address(i))==certificate.after_names[i],
{
    view.mapping_entry(i);view.mapping_domain();
    assert(view.mapping().contains_key(view.address(i)));
    assert(exists|j:int|0<=j<view.len_spec() && view.address(j)==view.address(i));
    let j=choose|j:int|0<=j<view.len_spec() && view.address(j)==view.address(i);view.aliases(i,j);
}
pub open spec fn heap(mapping:Map<Address,Address>,versions:spec_fn(Address)->Map<u64,u64>,schema:Seq<Reference>,a:Map<Address,s::Value<Value>>,b:Map<Address,s::Value<Value>>)->bool {
    forall|k:Address|mapping.contains_key(k) ==> {
        &&& a.contains_key(k)==b.contains_key(#[trigger] mapping[k])
        &&& a.contains_key(k) ==> value(versions(k),schema,a[k],b[mapping[k]])
    }
}
pub open spec fn optional(mapping:Map<Address,Address>,versions:spec_fn(Address)->Map<u64,u64>,schema:Seq<Reference>,a:Option<Map<Address,s::Value<Value>>>,b:Option<Map<Address,s::Value<Value>>>)->bool {
    a.is_some()==b.is_some() && (a.is_some() ==> heap(mapping,versions,schema,a.unwrap(),b.unwrap()))
}
pub open spec fn pairs(mapping:Map<Address,Address>,versions:spec_fn(Address)->Map<u64,u64>,schema:Seq<Reference>,a:Seq<managed::Step<Value>>,b:Seq<managed::Step<Value>>)->bool {
    a.len()==b.len() && forall|i:int|0<=i<a.len() ==> {
        let x=#[trigger] a[i];let y=b[i];
        &&& mapping.contains_pair(x.address(),y.address()) && typed::injective(versions(x.address()))
        &&& value(versions(x.address()),schema,x.before(),y.before()) && value(versions(x.address()),schema,x.after(),y.after())
    }
}
proof fn write(mapping:Map<Address,Address>,versions:spec_fn(Address)->Map<u64,u64>,schema:Seq<Reference>,a:Map<Address,s::Value<Value>>,b:Map<Address,s::Value<Value>>,k:Address,x:s::Value<Value>,y:s::Value<Value>)
    requires injective(mapping),heap(mapping,versions,schema,a,b),mapping.contains_key(k),value(versions(k),schema,x,y),
    ensures heap(mapping,versions,schema,a.insert(k,x),b.insert(mapping[k],y)),
{
    assert forall|j:Address|mapping.contains_key(j) implies {
        &&& a.insert(k,x).contains_key(j)==b.insert(mapping[k],y).contains_key(#[trigger] mapping[j])
        &&& a.insert(k,x).contains_key(j) ==> value(versions(j),schema,a.insert(k,x)[j],b.insert(mapping[k],y)[mapping[j]])
    } by {if j!=k {assert(mapping[j]!=mapping[k]);}}
}
/// These are managed::semantics::undo and its real retained Step operands.
/// No premise assumes either source or target undo succeeds.
pub proof fn word(mapping:Map<Address,Address>,versions:spec_fn(Address)->Map<u64,u64>,schema:Seq<Reference>,a:Seq<managed::Step<Value>>,b:Seq<managed::Step<Value>>,x:Map<Address,s::Value<Value>>,y:Map<Address,s::Value<Value>>)
    requires injective(mapping),pairs(mapping,versions,schema,a,b),heap(mapping,versions,schema,x,y),
    ensures optional(mapping,versions,schema,s::undo(a,x),s::undo(b,y)),
    decreases a.len(),
{
    if a.len()>0 {
        let u=a.last();let v=b.last();let k=u.address();
        if x.contains_key(k) {
            equality(versions(k),schema,u.after(),v.after(),x[k],y[v.address()]);
            if x[k]==u.after() {
                write(mapping,versions,schema,x,y,k,u.before(),v.before());
                word(mapping,versions,schema,a.drop_last(),b.drop_last(),x.insert(k,u.before()),y.insert(v.address(),v.before()));
            }
        }
    }
}
impl<E:ScalarEffect> Outcome<E,Value> {
    pub open spec fn versions(&self,address:Address)->Map<u64,u64> {self.history@.unwrap().at(address)}
    pub proof fn version_facts(&self,source:&Source<E,Value>,bank:&Bank<Value>,address:Address)
        requires source.wf(),bank.wf(),self.matches(source,bank),self.run.report.is_ok(),self.run.report->Ok_0.result.is_ok(),
        ensures typed::injective(self.versions(address)),epochs::ordered(self.versions(address)),
    {self.facts(source,bank);self.history@.unwrap().facts(address);}
    /// Derive the full heterogeneous word relation from the report produced by
    /// invoke_next. Callers provide neither a version map nor paired inverses.
    pub proof fn inverse_pairs(&self,source:&Source<E,Value>,bank:&Bank<Value>,schema:Seq<Reference>)
        requires source.wf(),source.closed_data(schema),bank.wf(),self.matches(source,bank),
            source.original().result.is_ok(),self.run.report.is_ok(),self.run.report->Ok_0.result.is_ok(),
        ensures pairs(bank.mapping(),|a:Address|self.versions(a),schema,source.original().result->Ok_0.steps@,self.run.report->Ok_0.result->Ok_0.steps@),
    {
        self.facts(source,bank);source.closed_facts(schema);reveal(relation::allocations);
        let c=self.correspondence@.unwrap();let view=self.typed_bank@;c.facts();
        let a=source.original().result->Ok_0.steps@;let b=self.run.report->Ok_0.result->Ok_0.steps@;
        assert forall|i:int|0<=i<a.len() implies {
            let x=#[trigger] a[i];let y=b[i];
            &&& bank.mapping().contains_pair(x.address(),y.address()) && typed::injective(self.versions(x.address()))
            &&& value(self.versions(x.address()),schema,x.before(),y.before()) && value(self.versions(x.address()),schema,x.after(),y.after())
        } by {
            let x=a[i];let y=b[i];let versions=self.versions(x.address());
            self.version_facts(source,bank,x.address());
            if x.result is Payload {
                let n=held::payload_position(a,b,i);let j=c.routes[x.pc as int] as int;
                view.mapping_entry(j);view.mapping_injective();
                assert(view.mapping().contains_pair(x.address(),view.target_address(j)));
                assert(x.address()==view.address(j));assert(self.versions(x.address())==c.after_names[j]);
                assert(relation::paired(c.after_names,c.routes,c.source,c.target));
                assert(typed::related(c.after_names[j],x.before()->Payload_0,y.before()->Payload_0));
            } else {assert(held::pair(y,x));}
        }
    }
    pub proof fn inverse_word(&self,source:&Source<E,Value>,bank:&Bank<Value>,schema:Seq<Reference>,a:Map<Address,s::Value<Value>>,b:Map<Address,s::Value<Value>>)
        requires source.wf(),source.closed_data(schema),bank.wf(),self.matches(source,bank),
            source.original().result.is_ok(),self.run.report.is_ok(),self.run.report->Ok_0.result.is_ok(),
            heap(bank.mapping(),|k:Address|self.versions(k),schema,a,b),
        ensures optional(bank.mapping(),|k:Address|self.versions(k),schema,
            s::undo(source.original().result->Ok_0.steps@,a),s::undo(self.run.report->Ok_0.result->Ok_0.steps@,b)),
    {
        self.inverse_pairs(source,bank,schema);bank.mapping_injective();
        word(bank.mapping(),|k:Address|self.versions(k),schema,source.original().result->Ok_0.steps@,self.run.report->Ok_0.result->Ok_0.steps@,a,b);
    }
}
}
