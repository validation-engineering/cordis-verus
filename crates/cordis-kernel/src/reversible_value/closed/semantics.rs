//! All-input interpretation for the closed native instruction language.
//! These are the existing managed semantics, including failures, continuation
//! selection and strict inverses; no additional executable interpreter exists.
#[cfg(verus_keep_ghost)]
use super::Reference;
use super::Value;
use crate::reversible_value::{effect::ScalarEffect, managed};
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_grammar as d,
    reversible_value::managed::{
        replay::{typed, typed_correspondence::epochs},
        semantics as s,
    },
};
use vstd::prelude::*;

verus! {
pub open spec fn value(names:Map<u64,u64>,schema:Seq<Reference>,a:s::Value<Value>,b:s::Value<Value>)->bool {
    match (a,b) {
        (s::Value::Scalar(a),s::Value::Scalar(b))=>a==b,
        (s::Value::Payload(a),s::Value::Payload(b))=>typed::related(names,a,b) && a.value.admissible(schema),
        _=>false,
    }
}
pub open spec fn optional(names:Map<u64,u64>,schema:Seq<Reference>,a:Option<s::Value<Value>>,b:Option<s::Value<Value>>)->bool {
    a.is_some()==b.is_some() && (a.is_some() ==> value(names,schema,a.unwrap(),b.unwrap()))
}
pub proof fn equality(names:Map<u64,u64>,schema:Seq<Reference>,a:s::Value<Value>,b:s::Value<Value>,x:s::Value<Value>,y:s::Value<Value>)
    requires typed::injective(names),value(names,schema,a,b),value(names,schema,x,y),
    ensures (a==x)==(b==y),
{
    if let (s::Value::Payload(a),s::Value::Payload(b),s::Value::Payload(x),s::Value::Payload(y))=(a,b,x,y) {
        if b==y {assert(names[a.head]==names[x.head]);}
    }
}
pub proof fn primitive<E:ScalarEffect>(effect:managed::Effect<E,Value>,a_head:u64,b_head:u64,names:Map<u64,u64>,schema:Seq<Reference>,a:s::Value<Value>,b:s::Value<Value>)
    requires !(effect is Scalar),typed::injective(names),epochs::ordered(names),value(names,schema,a,b),
        effect is Replace && a is Payload ==> names.contains_pair(a_head,b_head) && effect->Replace_0.admissible(schema),
    ensures s::operation(s::code(effect,a_head))(a).is_some()==s::operation(s::code(effect,b_head))(b).is_some(),
        s::operation(s::code(effect,a_head))(a).is_some() ==> {
            let x=s::operation(s::code(effect,a_head))(a).unwrap();let y=s::operation(s::code(effect,b_head))(b).unwrap();
            &&& value(names,schema,x.value,y.value) && x.outcome==y.outcome
            &&& forall|u:s::Value<Value>,v:s::Value<Value>|value(names,schema,u,v) ==> #[trigger] optional(names,schema,(x.undo)(u),(y.undo)(v))
        },
{
    if effect is Replace && a is Payload {assert((a->Payload_0.head<a_head)==(b->Payload_0.head<b_head));}
    if s::operation(s::code(effect,a_head))(a).is_some() {
        let x=s::operation(s::code(effect,a_head))(a).unwrap();let y=s::operation(s::code(effect,b_head))(b).unwrap();
        assert forall|u:s::Value<Value>,v:s::Value<Value>|value(names,schema,u,v) implies #[trigger] optional(names,schema,(x.undo)(u),(y.undo)(v)) by {
            equality(names,schema,x.value,y.value,u,v);
        }
    }
}
pub open spec fn heap(names:Map<usize,Map<u64,u64>>,schema:Seq<Reference>,a:Map<usize,s::Value<Value>>,b:Map<usize,s::Value<Value>>)->bool {
    a.dom()==b.dom() && a.dom().subset_of(names.dom()) && forall|k:usize|a.contains_key(k) ==> #[trigger] value(names[k],schema,a[k],b[k])
}
pub open spec fn maps(names:Map<usize,Map<u64,u64>>)->bool {
    forall|k:usize|#[trigger] names.contains_key(k) ==> typed::injective(names[k]) && epochs::ordered(names[k])
}
proof fn write(names:Map<usize,Map<u64,u64>>,schema:Seq<Reference>,a:Map<usize,s::Value<Value>>,b:Map<usize,s::Value<Value>>,k:usize,x:s::Value<Value>,y:s::Value<Value>)
    requires heap(names,schema,a,b),names.contains_key(k),value(names[k],schema,x,y),
    ensures heap(names,schema,a.insert(k,x),b.insert(k,y)),
{assert forall|j:usize|a.insert(k,x).contains_key(j) implies #[trigger] value(names[j],schema,a.insert(k,x)[j],b.insert(k,y)[j]) by {}}
pub open spec fn result(names:Map<usize,Map<u64,u64>>,schema:Seq<Reference>,a:Option<crate::iterators::PartialIteration<Map<usize,s::Value<Value>>,usize>>,b:Option<crate::iterators::PartialIteration<Map<usize,s::Value<Value>>,usize>>)->bool {
    a.is_some()==b.is_some() && (a.is_some() ==> {
        &&& heap(names,schema,a.unwrap().state,b.unwrap().state) && a.unwrap().next==b.unwrap().next
        &&& forall|x:Map<usize,s::Value<Value>>,y:Map<usize,s::Value<Value>>|#[trigger] heap(names,schema,x,y) ==> {
            let u=(a.unwrap().undo)(x);let v=(b.unwrap().undo)(y);
            &&& u.is_some()==v.is_some() && (u.is_some() ==> heap(names,schema,u.unwrap(),v.unwrap()))
        }
    })
}
/// Root and any current continuation use this same statement. The test heaps
/// are arbitrary admitted inputs, not only the heap seen in one execution.
pub proof fn function<E:ScalarEffect>(program:managed::Function<E,Value>,resolve:spec_fn(usize)->usize,a_heads:spec_fn(usize)->u64,b_heads:spec_fn(usize)->u64,names:Map<usize,Map<u64,u64>>,schema:Seq<Reference>,pc:usize,a:Map<usize,s::Value<Value>>,b:Map<usize,s::Value<Value>>)
    requires program.closed_data(schema),maps(names),heap(names,schema,a,b),
        pc<program.code().len() && program.code()[pc as int].effect is Replace && a.contains_key(resolve(pc)) && a[resolve(pc)] is Payload ==>
            names.contains_key(resolve(pc)) && names[resolve(pc)].contains_pair(a_heads(pc),b_heads(pc)),
    ensures result(names,schema,
        d::run(s::library::<usize,Value>(),s::program(program.code(),resolve,a_heads)(pc),a),
        d::run(s::library::<usize,Value>(),s::program(program.code(),resolve,b_heads)(pc),b)),
{
    if pc<program.code().len() {
        let k=resolve(pc);let call=program.code()[pc as int];
        if a.contains_key(k) {
            primitive(call.effect,a_heads(pc),b_heads(pc),names[k],schema,a[k],b[k]);
            let left=s::operation(s::code(call.effect,a_heads(pc)))(a[k]);let right=s::operation(s::code(call.effect,b_heads(pc)))(b[k]);
            if left.is_some() {
                let x=left.unwrap();let y=right.unwrap();write(names,schema,a,b,k,x.value,y.value);
                assert forall|u:Map<usize,s::Value<Value>>,v:Map<usize,s::Value<Value>>|#[trigger] heap(names,schema,u,v) implies {
                    let uu=d::inverse(k,x.undo)(u);let vv=d::inverse(k,y.undo)(v);
                    &&& uu.is_some()==vv.is_some() && (uu.is_some() ==> heap(names,schema,uu.unwrap(),vv.unwrap()))
                } by {
                    if u.contains_key(k) {
                        assert(optional(names[k],schema,(x.undo)(u[k]),(y.undo)(v[k])));
                        if (x.undo)(u[k]).is_some() {write(names,schema,u,v,k,(x.undo)(u[k]).unwrap(),(y.undo)(v[k]).unwrap());}
                    }
                }
            }
        }
    }
}
impl<E:ScalarEffect> managed::replay::session::Outcome<E,Value> {
    /// The two stored functions are from the actual Source and actual target
    /// report. At pc=0 this compares roots; any pc compares continuations.
    /// Version parameters are explicit: this is the strict, admission-aware
    /// relation, not the paper's pure-table Equation (54).
    pub proof fn function_at(&self,source:&managed::replay::Source<E,Value>,bank:&managed::replay::bank::Bank<Value>,resolve:spec_fn(usize)->usize,a_heads:spec_fn(usize)->u64,b_heads:spec_fn(usize)->u64,names:Map<usize,Map<u64,u64>>,schema:Seq<Reference>,pc:usize,a:Map<usize,s::Value<Value>>,b:Map<usize,s::Value<Value>>)
        requires source.wf(),source.closed_data(schema),self.matches(source,bank),self.run.report.is_ok(),self.run.report->Ok_0.result.is_ok(),
            maps(names),heap(names,schema,a,b),
            pc<source.program().code().len() && source.program().code()[pc as int].effect is Replace && a.contains_key(resolve(pc)) && a[resolve(pc)] is Payload ==>
                names.contains_key(resolve(pc)) && names[resolve(pc)].contains_pair(a_heads(pc),b_heads(pc)),
        ensures result(names,schema,
            d::run(s::library::<usize,Value>(),s::program(source.program().code(),resolve,a_heads)(pc),a),
            d::run(s::library::<usize,Value>(),s::program(self.run.report->Ok_0.function@.code(),resolve,b_heads)(pc),b)),
    {
        self.facts(source,bank);reveal(managed::replay::TargetRun::from_source);
        function(source.program(),resolve,a_heads,b_heads,names,schema,pc,a,b);
    }
}

}
