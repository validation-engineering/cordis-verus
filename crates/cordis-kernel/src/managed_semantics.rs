//! One dependent sum carrier for scalar and typed effects. The universal law
//! includes unselected branches, strict failure domains and every inverse input.
#[cfg(verus_keep_ghost)]
use super::{Call, Effect, ResultStep};
use super::{Function, Step};
use crate::reversible_value::{effect, payload};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{joint, service_composition::Address};
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_grammar as d, fresh_grammar as f, guarded_components as c, mediated as m, Port,
};
use std::sync::Arc;
use vstd::prelude::*;

verus! {
pub ghost enum Value<T:?Sized> {Scalar(crate::reversible_value::ValueState),Payload(payload::State<T>)}
pub ghost enum Code<T:?Sized> {Scalar(effect::Code),Payload {value:Arc<T>,head:u64}}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum Outcome {Scalar(crate::reversible_value::Outcome),Replaced}
pub open spec fn selected(branch:crate::reversible_value::Branch,out:Outcome)->Option<usize> {
    match out {Outcome::Scalar(value)=>branch.selected(value),Outcome::Replaced=>branch.matched}
}
pub open spec fn operation<T:?Sized>(code:Code<T>)->m::Operation<Value<T>,Outcome> {
    |input:Value<T>|match (code,input) {
        (Code::Scalar(code),Value::Scalar(value))=>match effect::operation(code)(value) {
            None=>None,Some(y)=>{
                let after=Value::Scalar(y.value);
                Some(m::ValueYield {value:after,outcome:Outcome::Scalar(y.outcome),undo:|current:Value<T>|if current==after {Some(input)} else {None}})
            },
        },
        (Code::Payload {value,head},Value::Payload(input_value))=>match payload::restoration::operation(value,head)(input_value) {
            None=>None,Some(y)=>{
                let after=Value::Payload(y.value);
                Some(m::ValueYield {value:after,outcome:Outcome::Replaced,undo:|current:Value<T>|if current==after {Some(input)} else {None}})
            },
        },_=>None,
    }
}
pub open spec fn library<K,T:?Sized>()->d::Library<K,(K,Code<T>),(),Value<T>,Outcome> {
    d::Library {values:|_:K,_:Value<T>|true,arguments:|_:(K,Code<T>),_:()|true,
        outcomes:|a:(K,Code<T>),b:Outcome| match a.1 {Code::Scalar(_)=>b is Scalar,Code::Payload {..}=>b==Outcome::Replaced},
        key:|a:(K,Code<T>)|a.0,allowed:ISet::full(),apply:|a:(K,Code<T>),_:()|operation(a.1)}
}
pub proof fn primitive_theory<K,T:?Sized>()
    ensures d::primitive_theory(|_:K,a:Value<T>,b:Value<T>|a==b,library::<K,T>()),
{
    assert forall|a:(K,Code<T>),x:()|library::<K,T>().allowed.contains(a) && (library::<K,T>().arguments)(a,x)
        implies d::operation_typed(library::<K,T>(),a,x) && m::operation_admissible(|u:Value<T>,v:Value<T>|u==v,(library::<K,T>().apply)(a,x)) by {}
}
pub open spec fn code<E:effect::ScalarEffect,T:?Sized>(effect:Effect<E,T>,head:u64)->Code<T> {
    match effect {Effect::Scalar(e)=>Code::Scalar(e.model()),Effect::Replace(value)=>Code::Payload {value,head}}
}
pub open spec fn node<K,E:effect::ScalarEffect,T:?Sized>(calls:Seq<Call<E,T>>,resolve:spec_fn(usize)->K,heads:spec_fn(usize)->u64,pc:usize)->d::Node<K,(K,Code<T>),(),Value<T>,Outcome,usize> {
    if pc<calls.len() {d::Node::Operation {operation:(resolve(pc),code(calls[pc as int].effect,heads(pc))),argument:(),select:|out:Outcome|selected(calls[pc as int].branch,out)}} else {d::Node::Unit}
}
pub open spec fn program<K,E:effect::ScalarEffect,T:?Sized>(calls:Seq<Call<E,T>>,resolve:spec_fn(usize)->K,heads:spec_fn(usize)->u64)->d::Program<K,(K,Code<T>),(),Value<T>,Outcome,usize> {
    |pc:usize|node(calls,resolve,heads,pc)
}
pub open spec fn keys<K,E,T:?Sized>(calls:Seq<Call<E,T>>,resolve:spec_fn(usize)->K)->ISet<K> {
    ISet::new(|k:K|exists|pc:usize|pc<calls.len() && #[trigger] resolve(pc)==k)
}
pub open spec fn programs<E:effect::ScalarEffect,T:?Sized>(calls:Seq<Call<E,T>>,resolve:spec_fn(usize)->Port,heads:spec_fn(usize)->u64)->f::Programs<(Port,Code<T>),(),Value<T>,Outcome,usize> {
    |_:usize| |pc:usize|f::Node::Dependent {node:node(calls,resolve,heads,pc)}
}
impl<E:effect::ScalarEffect,T:?Sized> Function<E,T> {
    /// Any verified ScalarEffect implementation participates; the theorem is
    /// not restricted to the host's convenience Operation enumeration.
    pub proof fn member<K>(&self,resolve:spec_fn(usize)->K,heads:spec_fn(usize)->u64,pc:usize)
        requires self.valid(),
        ensures d::member(library::<K,T>(),program(self.code(),resolve,heads),keys(self.code(),resolve),ISet::empty(),pc),
        decreases if pc<self.code().len() {self.code().len()-pc} else {0},
    {
        self.shape();
        if pc<self.code().len() {
            assert(self.code()[pc as int].valid(pc as int,self.code().len()));
            let branch=self.code()[pc as int].branch;
            if branch.matched.is_some() {self.member(resolve,heads,branch.matched.unwrap());}
            if branch.unmatched.is_some() {self.member(resolve,heads,branch.unmatched.unwrap());}
            assert(keys(self.code(),resolve).contains(resolve(pc)));
            assert forall|out:Outcome| selected(branch,out).is_some() implies
                d::members(library::<K,T>(),program(self.code(),resolve,heads),keys(self.code(),resolve),ISet::empty()).contains(selected(branch,out).unwrap()) by {}
        }
        d::constructor_member(library::<K,T>(),program(self.code(),resolve,heads),keys(self.code(),resolve),ISet::empty(),pc);
    }
    proof fn fresh_member(&self,resolve:spec_fn(usize)->Port,heads:spec_fn(usize)->u64,actor:usize,dependencies:ISet<Port>,provisions:ISet<Port>,pc:usize)
        requires self.valid(),keys(self.code(),resolve).subset_of(dependencies),
        ensures f::member(library::<Port,T>(),programs(self.code(),resolve,heads),actor,dependencies,provisions,pc),
        decreases if pc<self.code().len() {self.code().len()-pc} else {0},
    {
        self.shape();
        if pc<self.code().len() {
            assert(self.code()[pc as int].valid(pc as int,self.code().len()));
            let branch=self.code()[pc as int].branch;
            assert(keys(self.code(),resolve).contains(resolve(pc)));
            if branch.matched.is_some() {self.fresh_member(resolve,heads,actor,dependencies,provisions,branch.matched.unwrap());}
            if branch.unmatched.is_some() {self.fresh_member(resolve,heads,actor,dependencies,provisions,branch.unmatched.unwrap());}
            assert forall|out:Outcome|selected(branch,out).is_some() implies
                f::members(library::<Port,T>(),programs(self.code(),resolve,heads)).contains((actor,dependencies,provisions,selected(branch,out).unwrap())) by {}
        }
        f::constructor_member(library::<Port,T>(),programs(self.code(),resolve,heads),actor,dependencies,provisions,pc);
    }
    /// Literal named-port Component theorem on its full carrier. Applying it
    /// to aliases additionally requires the explicit projection condition below.
    pub proof fn component(&self,resolve:spec_fn(usize)->Port,heads:spec_fn(usize)->u64,actor:usize,dependencies:ISet<Port>,provisions:ISet<Port>,pc:usize)
        requires self.valid(),keys(self.code(),resolve).subset_of(dependencies),
        ensures c::component(library::<Port,T>(),programs(self.code(),resolve,heads),actor,dependencies,provisions,pc),
    {
        primitive_theory::<Port,T>();self.fresh_member(resolve,heads,actor,dependencies,provisions,pc);
        c::member_is_component(|_:Port,a:Value<T>,b:Value<T>|a==b,library::<Port,T>(),programs(self.code(),resolve,heads),actor,dependencies,provisions,pc);
    }
}
impl<T:?Sized> Step<T> {
    pub open spec fn address(&self)->Address {Address {journal:self.write().journal(),key:self.write().event().key}}
    pub open spec fn before(&self)->Value<T> {match self.result {ResultStep::Scalar {inverse,..}=>Value::Scalar(inverse@.state().before),ResultStep::Payload(a)=>Value::Payload(a.inverse().before().state())}}
    pub open spec fn after(&self)->Value<T> {match self.result {ResultStep::Scalar {inverse,..}=>Value::Scalar(inverse@.state().after),ResultStep::Payload(a)=>Value::Payload(a.inverse().after().state())}}
    pub open spec fn head(&self)->u64 {match self.result {ResultStep::Scalar {..}=>0,ResultStep::Payload(a)=>a.inverse().after().state().head}}
    pub open spec fn outcome(&self)->Outcome {match self.result {ResultStep::Scalar {write,..}=>Outcome::Scalar(write.admission.outcome),ResultStep::Payload(_)=>Outcome::Replaced}}
    /// Actual argument, output, continuation and retained inverse all agree
    /// with the same primitive interpretation, on every inverse input.
    pub proof fn interpretation<E:effect::ScalarEffect,M>(&self,call:Call<E,T>,port:Port,episode:crate::lifecycle_state::services::NativeEpisode<super::Slot<T,M>>)
        requires self.corresponds(call,port,episode),
        ensures self.write().wf(),
            operation(code(call.effect,self.head()))(self.before()).is_some(),
            operation(code(call.effect,self.head()))(self.before()).unwrap().value==self.after(),
            operation(code(call.effect,self.head()))(self.before()).unwrap().outcome==self.outcome(),
            selected(call.branch,self.outcome())==self.next,
            forall|v:Value<T>| #[trigger] (operation(code(call.effect,self.head()))(self.before()).unwrap().undo)(v)==if v==self.after() {Some(self.before())} else {None},
    {
        reveal(Step::corresponds);
        match self.result {
            ResultStep::Scalar {write,inverse}=>{write.admission.registration().write().transition();reveal(joint::changes);},
            ResultStep::Payload(a)=>{a.inverse().interpretation();a.inverse().provenance();},
        }
    }
}
/// Projection preserves all aliases. Restricting this to one named binding
/// is valid precisely when no other current name selects the written address.
pub open spec fn view<K,T:?Sized>(targets:Map<K,Address>,heap:Map<Address,Value<T>>)->Map<K,Value<T>> {
    Map::new(targets.dom().filter(|k:K|heap.contains_key(targets[k])),|k:K|heap[targets[k]])
}
pub proof fn alias_frame<K,T:?Sized>(targets:Map<K,Address>,heap:Map<Address,Value<T>>,address:Address,value:Value<T>,key:K)
    requires !targets.contains_key(key) || targets[key]!=address,
    ensures view(targets,heap.insert(address,value)).contains_key(key)==view(targets,heap).contains_key(key),
        view(targets,heap).contains_key(key) ==> view(targets,heap.insert(address,value))[key]==view(targets,heap)[key],
{}
pub proof fn single_key_projection<K,T:?Sized>(targets:Map<K,Address>,heap:Map<Address,Value<T>>,address:Address,value:Value<T>,key:K)
    requires targets.contains_key(key),targets[key]==address,heap.contains_key(address),
        forall|other:K|targets.contains_key(other) && #[trigger] targets[other]==address ==> other==key,
    ensures view(targets,heap.insert(address,value))==view(targets,heap).insert(key,value),
{assert(view(targets,heap.insert(address,value)) =~= view(targets,heap).insert(key,value));}

pub open spec fn redo<T:?Sized>(step:Step<T>,heap:Map<Address,Value<T>>)->Option<Map<Address,Value<T>>> {
    if heap.contains_key(step.address()) && heap[step.address()]==step.before() {Some(heap.insert(step.address(),step.after()))} else {None}
}
pub open spec fn undo_step<T:?Sized>(step:Step<T>,heap:Map<Address,Value<T>>)->Option<Map<Address,Value<T>>> {
    if heap.contains_key(step.address()) && heap[step.address()]==step.after() {Some(heap.insert(step.address(),step.before()))} else {None}
}
pub open spec fn replay<T:?Sized>(steps:Seq<Step<T>>,heap:Map<Address,Value<T>>)->Option<Map<Address,Value<T>>>
    decreases steps.len(),
{if steps.len()==0 {Some(heap)} else {match replay(steps.drop_last(),heap) {Some(previous)=>redo(steps.last(),previous),None=>None}}}
pub open spec fn undo<T:?Sized>(steps:Seq<Step<T>>,heap:Map<Address,Value<T>>)->Option<Map<Address,Value<T>>>
    decreases steps.len(),
{if steps.len()==0 {Some(heap)} else {match undo_step(steps.last(),heap) {Some(previous)=>undo(steps.drop_last(),previous),None=>None}}}
pub proof fn roundtrip<T:?Sized>(steps:Seq<Step<T>>,heap:Map<Address,Value<T>>)
    requires replay(steps,heap).is_some(),
    ensures undo(steps,replay(steps,heap).unwrap())==Some(heap),
    decreases steps.len(),
{
    if steps.len()>0 {
        let previous=replay(steps.drop_last(),heap).unwrap();let step=steps.last();
        assert(previous.insert(step.address(),step.after()).insert(step.address(),step.before()) =~= previous);
        roundtrip(steps.drop_last(),heap);
    }
}
}
