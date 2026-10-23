//! Generate future head correspondence from admission clocks. No caller picks
//! names for unvisited instructions. This interprets the existing managed
//! primitive/program and the actual retained functions, including rejection.
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
pub open spec fn next(clock:u64)->u64 {if clock<u64::MAX {(clock+1) as u64} else {0}}
pub open spec fn room(clock:u64,depth:u64)->bool {clock as int+depth as int+2<=u64::MAX}
pub open spec fn admission(a:Map<usize,s::Value<Value>>,b:Map<usize,s::Value<Value>>,ac:Map<usize,u64>,bc:Map<usize,u64>,names:Map<usize,Map<u64,u64>>)->bool {
    a.dom().subset_of(ac.dom()) && b.dom().subset_of(bc.dom())
        && forall|k:usize|a.contains_key(k) && (#[trigger] a[k]) is Payload ==> {
            &&& typed::bounded(names[k],ac[k],bc[k])
            &&& room(ac[k],a[k]->Payload_0.depth)==room(bc[k],b[k]->Payload_0.depth)
        }
}
pub open spec fn ready<E:ScalarEffect>(program:managed::Function<E,Value>,resolve:spec_fn(usize)->usize,pc:usize,a:Map<usize,s::Value<Value>>,clocks:Map<usize,u64>)->bool {
    pc<program.code().len() && program.code()[pc as int].effect is Replace && a.contains_key(resolve(pc)) && a[resolve(pc)] is Payload
        ==> clocks.contains_key(resolve(pc)) && room(clocks[resolve(pc)],a[resolve(pc)]->Payload_0.depth)
}
pub open spec fn heads(clocks:Map<usize,u64>,resolve:spec_fn(usize)->usize)->spec_fn(usize)->u64 {|pc:usize|next(clocks[resolve(pc)])}
pub open spec fn run<E:ScalarEffect>(program:managed::Function<E,Value>,resolve:spec_fn(usize)->usize,pc:usize,a:Map<usize,s::Value<Value>>,clocks:Map<usize,u64>)->Option<crate::iterators::PartialIteration<Map<usize,s::Value<Value>>,usize>> {
    if ready(program,resolve,pc,a,clocks) {d::run(s::library::<usize,Value>(),s::program(program.code(),resolve,heads(clocks,resolve))(pc),a)} else {None}
}
pub open spec fn grows<E:ScalarEffect>(program:managed::Function<E,Value>,resolve:spec_fn(usize)->usize,pc:usize,a:Map<usize,s::Value<Value>>,clocks:Map<usize,u64>)->bool {
    pc<program.code().len() && program.code()[pc as int].effect is Replace && a.contains_key(resolve(pc)) && a[resolve(pc)] is Payload && ready(program,resolve,pc,a,clocks)
}
pub open spec fn generated<E:ScalarEffect>(program:managed::Function<E,Value>,resolve:spec_fn(usize)->usize,pc:usize,a:Map<usize,s::Value<Value>>,ac:Map<usize,u64>,bc:Map<usize,u64>,names:Map<usize,Map<u64,u64>>)->Map<usize,Map<u64,u64>> {
    if grows(program,resolve,pc,a,ac) {let k=resolve(pc);names.insert(k,names[k].insert(next(ac[k]),next(bc[k])))} else {names}
}
pub open spec fn extends(before:Map<usize,Map<u64,u64>>,after:Map<usize,Map<u64,u64>>)->bool {
    before.dom()==after.dom() && forall|k:usize|before.contains_key(k) ==> (#[trigger] before[k]).submap_of(after[k])
}
pub proof fn weaken(before:Map<usize,Map<u64,u64>>,after:Map<usize,Map<u64,u64>>,schema:Seq<Reference>,a:Map<usize,s::Value<Value>>,b:Map<usize,s::Value<Value>>)
    requires extends(before,after),super::semantics::heap(before,schema,a,b),
    ensures super::semantics::heap(after,schema,a,b),
{
    assert forall|k:usize|a.contains_key(k) implies #[trigger] super::semantics::value(after[k],schema,a[k],b[k]) by {
        assert(super::semantics::value(before[k],schema,a[k],b[k]));assert(before.contains_key(k));assert(before[k].submap_of(after[k]));
        if a[k] is Payload {assert(b[k] is Payload);assert(typed::related(before[k],a[k]->Payload_0,b[k]->Payload_0));let head=a[k]->Payload_0.head;assert(before[k].contains_pair(head,b[k]->Payload_0.head));assert(after[k].contains_pair(head,b[k]->Payload_0.head)) by {reveal(Map::submap_of);}}
    }
}
/// Exact domains on the paired admission carrier: exhausted clocks reject on
/// both sides, while successful typed steps extend the historical injection.
pub proof fn function<E:ScalarEffect>(program:managed::Function<E,Value>,resolve:spec_fn(usize)->usize,pc:usize,a:Map<usize,s::Value<Value>>,b:Map<usize,s::Value<Value>>,ac:Map<usize,u64>,bc:Map<usize,u64>,names:Map<usize,Map<u64,u64>>,schema:Seq<Reference>)
    requires program.closed_data(schema),super::semantics::maps(names),super::semantics::heap(names,schema,a,b),admission(a,b,ac,bc,names),
    ensures extends(names,generated(program,resolve,pc,a,ac,bc,names)),
        super::semantics::maps(generated(program,resolve,pc,a,ac,bc,names)),
        super::semantics::result(generated(program,resolve,pc,a,ac,bc,names),schema,run(program,resolve,pc,a,ac),run(program,resolve,pc,b,bc)),
{
    let k=resolve(pc);let out=generated(program,resolve,pc,a,ac,bc,names);
    if a.contains_key(k) {assert(super::semantics::value(names[k],schema,a[k],b[k]));assert(names.contains_key(k));
        if a[k] is Payload {assert(b[k] is Payload);assert(room(ac[k],a[k]->Payload_0.depth)==room(bc[k],b[k]->Payload_0.depth));}}
    assert(ready(program,resolve,pc,a,ac)==ready(program,resolve,pc,b,bc));
    if grows(program,resolve,pc,a,ac) {
        assert(ac[k]<u64::MAX && bc[k]<u64::MAX);
        assert(names.contains_key(k));assert(out.dom()==names.dom());
        typed::extend(names[k],ac[k],bc[k],next(ac[k]),next(bc[k]));
        epochs::ordered_extend(names[k],ac[k],bc[k],next(ac[k]),next(bc[k]));
        assert forall|j:usize|names.contains_key(j) implies (#[trigger] names[j]).submap_of(out[j]) by {
            if j==k {reveal(Map::submap_of);}
        }
        assert forall|j:usize|#[trigger] out.contains_key(j) implies typed::injective(out[j]) && epochs::ordered(out[j]) by {if j!=k {assert(out[j]==names[j]);}}
    }
    assert(extends(names,out));
    weaken(names,out,schema,a,b);
    if ready(program,resolve,pc,a,ac) {
        super::semantics::function(program,resolve,heads(ac,resolve),heads(bc,resolve),out,schema,pc,a,b);
    }
}
impl<E:ScalarEffect> managed::replay::session::Outcome<E,Value> {
    pub proof fn function_at_fresh(&self,source:&managed::replay::Source<E,Value>,bank:&managed::replay::bank::Bank<Value>,resolve:spec_fn(usize)->usize,pc:usize,a:Map<usize,s::Value<Value>>,b:Map<usize,s::Value<Value>>,ac:Map<usize,u64>,bc:Map<usize,u64>,names:Map<usize,Map<u64,u64>>,schema:Seq<Reference>)
        requires source.wf(),source.closed_data(schema),self.matches(source,bank),self.run.report.is_ok(),self.run.report->Ok_0.result.is_ok(),
            super::semantics::maps(names),super::semantics::heap(names,schema,a,b),admission(a,b,ac,bc,names),
        ensures extends(names,generated(source.program(),resolve,pc,a,ac,bc,names)),
            super::semantics::result(generated(source.program(),resolve,pc,a,ac,bc,names),schema,
                run(source.program(),resolve,pc,a,ac),run(self.run.report->Ok_0.function@,resolve,pc,b,bc)),
    {
        self.facts(source,bank);reveal(managed::replay::TargetRun::from_source);
        function(source.program(),resolve,pc,a,b,ac,bc,names,schema);
    }
}
impl managed::Step<Value> {
    /// A real write uses precisely the next actual revision in this model.
    pub proof fn fresh_head(&self)
        requires self.result is Payload,self.result->Payload_0.inverse().wf(),
        ensures self.head()==next(self.result->Payload_0.inverse().before().revision),
    {
        self.result->Payload_0.inverse().source_history();
    }
}
}
