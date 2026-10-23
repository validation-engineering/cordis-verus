//! Mixed Bank storage, authentic episode bindings and pre-invocation input
//! checks for the original heterogeneous interpreter.
use super::super::{
    protected as scalar, protected_mixed as mixed, protected_typed as payload, Effect, Slot,
};
use super::{
    bank::Bank,
    batch::Provider,
    inputs::{Input, Operand, Seed},
    Source,
};
use crate::lifecycle_state::services::NativeEpisode;
use crate::reversible_value::{
    effect::ScalarEffect, payload::SharedPayload, slot, ReversibleValue,
};
use crate::Port;
use std::sync::Arc;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
#[derive(Debug)]
pub enum Error {Slot {index:usize},Typed(payload::Error),Binding {pc:usize},Input {step:usize},Uncontrolled}
pub(crate) struct Storage<T:?Sized> {
    pub scalar_values:Vec<ReversibleValue>,pub scalar_slots:Vec<slot::Slot>,pub scalar_names:Vec<usize>,
    pub payload_values:Vec<SharedPayload<T>>,pub payload_slots:Vec<Arc<Slot<T,()>>>,pub payload_names:Vec<usize>,
}
#[verifier::opaque]
pub(crate) open spec fn names_for<T:?Sized>(bank:&Bank<T>,payload:bool,n:nat)->Seq<usize>
    decreases n,
{if n==0 {Seq::empty()} else {let p=names_for(bank,payload,(n-1) as nat);if (bank.target(n as int-1) is Payload)==payload {p.push((n-1) as usize)} else {p}}}
impl<T:?Sized> Storage<T> {
    pub(crate) open spec fn canonical(&self,bank:&Bank<T>)->bool {self.scalar_names@==names_for(bank,false,bank.len_spec()) && self.payload_names@==names_for(bank,true,bank.len_spec())}
    pub(crate) proof fn unique_view(&self,bank:&Bank<T>,view:&Bank<T>)
        requires self.matches(bank),self.canonical(bank),self.typed_view(bank,view),
        ensures forall|other:&Storage<T>|other.matches(bank) && other.canonical(bank) ==> other.typed_view(bank,view),
    {assert forall|other:&Storage<T>|other.matches(bank) && other.canonical(bank) implies other.typed_view(bank,view) by {assert(other.payload_names@==self.payload_names@);}}

    pub(crate) open spec fn scalar_entry(&self,bank:&Bank<T>,i:int)->bool {
        self.scalar_names@[i]<bank.len_spec() && bank.target(self.scalar_names@[i] as int) is Scalar
            && self.scalar_values@[i]==bank.target(self.scalar_names@[i] as int)->Scalar_0
            && bank.service(self.scalar_names@[i] as int).managed()==Some(self.scalar_slots@[i])
            && *self.scalar_slots@[i].initial()==self.scalar_values@[i]
    }
    pub(crate) open spec fn payload_entry(&self,bank:&Bank<T>,i:int)->bool {
        self.payload_names@[i]<bank.len_spec() && bank.target(self.payload_names@[i] as int) is Payload
            && self.payload_values@[i]==bank.target(self.payload_names@[i] as int)->Payload_0
            && bank.service(self.payload_names@[i] as int)==self.payload_slots@[i]
            && self.payload_slots@[i].opaque_spec()==Some(self.payload_values@[i])
    }
    pub(crate) open spec fn matches(&self,bank:&Bank<T>)->bool {
        self.scalar_values.len()==self.scalar_slots.len() && self.scalar_values.len()==self.scalar_names.len()
            && self.payload_values.len()==self.payload_slots.len() && self.payload_values.len()==self.payload_names.len()
            && (forall|i:int|0<=i<self.scalar_names.len() ==> #[trigger] self.scalar_entry(bank,i))
            && (forall|i:int|0<=i<self.payload_names.len() ==> #[trigger] self.payload_entry(bank,i))
            && (forall|i:int,j:int|0<=i<j<self.scalar_names.len() ==> self.scalar_names@[i]<self.scalar_names@[j])
            && (forall|i:int,j:int|0<=i<j<self.payload_names.len() ==> self.payload_names@[i]<self.payload_names@[j])
    }
    pub(crate) open spec fn held(&self,context:&mixed::Context<'_,T,()>)->bool {
        context.scalar->Some_0.targets()==self.scalar_values@
            && context.payload->Some_0.targets()==self.payload_values@ && context.payload->Some_0.slots()==self.payload_slots@
    }
    pub(crate) open spec fn original_slots(&self,context:&mixed::Context<'_,T,()>)->bool {context.scalar->Some_0.slot_names()==self.scalar_slots@}
    pub(crate) fn new(bank:&Bank<T>)->(out:Self)
        requires bank.wf(),ensures out.matches(bank),out.canonical(bank),
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
        proof {reveal(names_for);}
        let mut out=Self {scalar_values:Vec::new(),scalar_slots:Vec::new(),scalar_names:Vec::new(),payload_values:Vec::new(),payload_slots:Vec::new(),payload_names:Vec::new()};let mut i=0;
        while i<bank.len()
            invariant bank.wf(),i<=bank.len_spec(),out.matches(bank),out.scalar_names@==names_for(bank,false,i as nat),out.payload_names@==names_for(bank,true,i as nat),
                forall|j:int|0<=j<out.scalar_names.len() ==> out.scalar_names@[j]<i,
                forall|j:int|0<=j<out.payload_names.len() ==> out.payload_names@[j]<i,
            decreases bank.len_spec()-i,
        {
            proof {bank.seed_facts(i as int);reveal(names_for);assert(names_for(bank,false,i as nat+1)==if bank.target(i as int) is Scalar {out.scalar_names@.push(i)} else {out.scalar_names@});assert(names_for(bank,true,i as nat+1)==if bank.target(i as int) is Payload {out.payload_names@.push(i)} else {out.payload_names@});}
            let ghost prior=out;
            let service=bank.slot(i).unwrap();
            match bank.seed(i).unwrap() {
                Seed::Scalar(value)=>{
                    let selected=service.reversible().unwrap().clone();
                    out.scalar_values.push(value.clone());out.scalar_slots.push(selected);out.scalar_names.push(i);
                    proof {assert(out.scalar_entry(bank,(out.scalar_names.len()-1) as int));}
                },
                Seed::Payload(value)=>{
                    out.payload_values.push(value.clone());out.payload_slots.push(service);out.payload_names.push(i);
                    proof {assert(out.payload_entry(bank,(out.payload_names.len()-1) as int));}
                },
            }
            proof {
                assert forall|j:int|0<=j<out.scalar_names.len() implies #[trigger] out.scalar_entry(bank,j) by {if j<prior.scalar_names.len() {assert(prior.scalar_entry(bank,j));}}
                assert forall|j:int|0<=j<out.payload_names.len() implies #[trigger] out.payload_entry(bank,j) by {if j<prior.payload_names.len() {assert(prior.payload_entry(bank,j));}}
            }i+=1;
        }out
    }
    #[allow(unused_variables)] // Runtime arguments also anchor erased provenance contracts.
    pub(crate) fn acquire<'a>(&'a self,bank:&Bank<T>)->(out:Result<mixed::Context<'a,T,()>,Error>)
        requires bank.wf(),self.matches(bank),
        ensures out.is_ok() ==> out->Ok_0.wf() && self.held(&out->Ok_0) && self.original_slots(&out->Ok_0),
    {
        proof {
            assert forall|i:int,j:int|0<=i<j<self.scalar_values.len() implies self.scalar_values@[i]!=self.scalar_values@[j] by {assert(self.scalar_entry(bank,i));assert(self.scalar_entry(bank,j));bank.aliases(self.scalar_names@[i] as int,self.scalar_names@[j] as int);}
            assert forall|i:int,j:int|0<=i<j<self.payload_values.len() implies self.payload_values@[i]!=self.payload_values@[j] by {assert(self.payload_entry(bank,i));assert(self.payload_entry(bank,j));bank.aliases(self.payload_names@[i] as int,self.payload_names@[j] as int);}
        }
        proof {
            assert forall|i:int|0<=i<self.scalar_slots.len() implies *self.scalar_slots@[i].initial()==self.scalar_values@[i] by {assert(self.scalar_entry(bank,i));}
            assert forall|i:int|0<=i<self.payload_slots.len() implies (#[trigger] self.payload_slots@[i]).opaque_spec()==Some(self.payload_values@[i]) by {assert(self.payload_entry(bank,i));}
        }
        let a=match scalar::Context::acquire(self.scalar_values.as_slice(),self.scalar_slots.as_slice()) {
            Ok(a)=>a,Err(scalar::Error::ChangedSlot {index})=>return Err(Error::Slot {index}),
        };
        let mut slots=Vec::new();let mut i=0;
        while i<self.payload_slots.len()
            invariant self.matches(bank),i<=self.payload_slots.len(),slots.len()==i,forall|j:int|0<=j<i ==> slots@[j]==self.payload_slots@[j],
            decreases self.payload_slots.len()-i,
        {slots.push(self.payload_slots[i].clone());i+=1;}
        proof {assert(slots@ =~= self.payload_slots@);}
        match payload::Context::acquire(self.payload_values.as_slice(),slots) {
            Ok(b)=>Ok(mixed::Context {scalar:Some(a),payload:Some(b)}),
            Err(error)=>{a.release();Err(Error::Typed(error))},
        }
    }
    pub(crate) fn scalar_index(&self,entry:usize)->(out:Option<usize>)
        ensures out.is_some() ==> out.unwrap()<self.scalar_names.len() && self.scalar_names@[out.unwrap() as int]==entry,
    {
        let mut i=0;while i<self.scalar_names.len() invariant i<=self.scalar_names.len(),decreases self.scalar_names.len()-i,
        {if self.scalar_names[i]==entry {return Some(i);}i+=1;}None
    }
    pub(crate) fn payload_index(&self,entry:usize)->(out:Option<usize>)
        ensures out.is_some() ==> out.unwrap()<self.payload_names.len() && self.payload_names@[out.unwrap() as int]==entry,
    {
        let mut i=0;while i<self.payload_names.len() invariant i<=self.payload_names.len(),decreases self.payload_names.len()-i,
        {if self.payload_names[i]==entry {return Some(i);}i+=1;}None
    }
}
impl<'a,T:?Sized> mixed::Context<'a,T,()> {
    #[allow(unused_variables)] // Runtime arguments also anchor erased provenance contracts.
    #[verifier::rlimit(16)]
    #[verifier::spinoff_prover]
    pub(crate) fn bind_mixed<E:ScalarEffect>(&mut self,episode:&NativeEpisode<Slot<T,()>>,ports:&[Port],source:&Source<E,T>,bank:&Bank<T>,storage:&Storage<T>,providers:&[Provider<E,T>])->(out:Result<(),Error>)
        requires old(self).wf(),storage.matches(bank),storage.held(old(self)),storage.original_slots(old(self)),bank.wf(),episode.wf(),source.wf(),source.original().succeeded(),source.program().controlled(),
            ports@.len()==source.program().code().len(),
            super::selection::providers_match(bank,providers@,episode.capture().sources),
        ensures final(self).wf(),storage.held(final(self)),storage.original_slots(final(self)),
            final(self).scalar->Some_0.slot_names()==old(self).scalar->Some_0.slot_names(),final(self).scalar->Some_0.chosen()==old(self).scalar->Some_0.chosen(),
            final(self).scalar->Some_0.states()==old(self).scalar->Some_0.states(),
            final(self).payload->Some_0.states()==old(self).payload->Some_0.states(),final(self).payload->Some_0.revisions()==old(self).payload->Some_0.revisions(),
            out.is_ok() ==> final(self).supports(*episode,ports@,source.program().code(),source.original().result->Ok_0.steps@),
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);hide(Source::wf);
        let mut a:Vec<scalar::Binding>=Vec::new();let mut b:Vec<payload::Binding>=Vec::new();let mut i=0;
        while i<ports.len()
            invariant *self==*old(self),self.wf(),storage.matches(bank),storage.held(self),storage.original_slots(self),bank.wf(),episode.wf(),source.wf(),source.original().succeeded(),source.program().controlled(),ports.len()==source.program().code().len(),i<=ports.len(),
                super::selection::providers_match(bank,providers@,episode.capture().sources),
                a.len()==if storage.scalar_values.len()>0 {i} else {0},b.len()==if storage.payload_values.len()>0 {i} else {0},
                forall|j:int|0<=j<a.len() ==> (#[trigger] a@[j]).slot<storage.scalar_values.len(),
                forall|j:int|0<=j<b.len() ==> (#[trigger] b@[j]).entry<storage.payload_values.len(),
                forall|j:int|0<=j<i && source.visited(j as usize) ==> match (#[trigger] source.program().code()[j]).effect {
                    Effect::Kernel(_)=>j<a.len() && a@[j].port==ports@[j] && !episode.closed() && episode.selects_slot(a@[j].provider,ports@[j],storage.scalar_slots@[a@[j].slot as int]),
                    Effect::Replace(_)=>j<b.len() && b@[j].port@==ports@[j] && !episode.closed() && episode.selects_value(b@[j].provider@,ports@[j],storage.payload_slots@[b@[j].entry as int]),
                    _=>false,
                },
            decreases ports.len()-i,
        {
            let port=ports[i];
            // Unvisited declarations are checked at admission, but no data lock
            // or invented operand is needed for an instruction that cannot run.
            if !source.visits(i) {
                if !storage.scalar_values.is_empty() {a.push(scalar::Binding {provider:0,port,slot:0});}
                if !storage.payload_values.is_empty() {b.push(payload::Binding {provider:Ghost(0),port:Ghost(port),entry:0});}
                i+=1;continue;
            }
            if episode.declares(port) {return Err(Error::Binding {pc:i});}
            let (id,_)=match episode.read(port) {Ok(pair)=>pair,Err(_)=>return Err(Error::Binding {pc:i})};
            let mut p=0;let mut found:Option<usize>=None;
            while p<providers.len()
                invariant p<=providers.len(),found.is_some() ==> found.unwrap()<providers.len() && providers@[found.unwrap() as int].id==id && providers@[found.unwrap() as int].port==port,
                decreases providers.len()-p,
            {if providers[p].id==id && providers[p].port==port {found=Some(p);break;}p+=1;}
            let n=match found {Some(n)=>n,None=>return Err(Error::Binding {pc:i})};let entry=providers[n].index;
            proof {
                assert(episode.capture().sources[id].values.contains_pair((port.key,port.realm),bank.service(entry as int)));
                assert(episode.capture().imports[(id,port.key,port.realm)]==bank.service(entry as int));
                assert(episode.selects_value(id,port,bank.service(entry as int)));
            }
            let (s,t)=match &source.function.code[i].effect {
                Effect::Kernel(_)=>{
                    let at=match storage.scalar_index(entry) {Some(at)=>at,None=>return Err(Error::Binding {pc:i})};
                    proof {assert(storage.scalar_entry(bank,at as int));assert(episode.selects_slot(id,port,storage.scalar_slots@[at as int]));}
                    (at,0usize)
                },
                Effect::Replace(_)=>{let at=match storage.payload_index(entry) {Some(at)=>at,None=>return Err(Error::Binding {pc:i})};proof {assert(storage.payload_entry(bank,at as int));assert(episode.selects_value(id,port,storage.payload_slots@[at as int]));}(0usize,at)},
                _=>return Err(Error::Uncontrolled),
            };
            let ghost old_a=a@;let ghost old_b=b@;
            if !storage.scalar_values.is_empty() {a.push(scalar::Binding {provider:id,port,slot:s});}
            if !storage.payload_values.is_empty() {b.push(payload::Binding {provider:Ghost(id),port:Ghost(port),entry:t});}
            proof {
                assert forall|j:int|0<=j<i+1 && source.visited(j as usize) implies match (#[trigger] source.program().code()[j]).effect {
                    Effect::Kernel(_)=>j<a.len() && a@[j].port==ports@[j] && !episode.closed() && episode.selects_slot(a@[j].provider,ports@[j],storage.scalar_slots@[a@[j].slot as int]),
                    Effect::Replace(_)=>j<b.len() && b@[j].port@==ports@[j] && !episode.closed() && episode.selects_value(b@[j].provider@,ports@[j],storage.payload_slots@[b@[j].entry as int]),
                    _=>false,
                } by {if j<i {if source.program().code()[j].effect is Kernel {assert(a@[j]==old_a[j]);} else {assert(b@[j]==old_b[j]);}}}
            }
            i+=1;
        }
        self.scalar.as_mut().unwrap().bind(a);self.payload.as_mut().unwrap().bind(b);
        proof {
            reveal(mixed::Context::supports);source.mixed_plan();
            assert forall|n:int|0<=n<source.original().result->Ok_0.steps.len() implies {
                let pc=(#[trigger] source.original().result->Ok_0.steps@[n]).pc;
                &&& pc<source.program().code().len() && self.for_call(*episode,pc,ports@[pc as int],source.program().code()[pc as int])
            } by {mixed::plan_at(source.program().code(),source.original().result->Ok_0.steps@,n);assert(source.visited(source.original().result->Ok_0.steps@[n].pc));}
        }
        Ok(())
    }
}
impl<E:ScalarEffect,T:?Sized> Source<E,T> {
    pub(crate) proof fn mixed_plan(&self)
        requires self.wf(),self.original().succeeded(),self.program().controlled(),
        ensures mixed::plan(self.program().code(),self.original().result->Ok_0.steps@),
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);reveal(mixed::plan);
        let code=self.program().code();let steps=self.original().result->Ok_0.steps@;
        assert forall|i:int|0<=i<steps.len() implies {
            let s=#[trigger] steps[i];
            &&& Some(s.pc)==super::super::next(code.len(),steps.take(i)) && super::transport::step(code,s)
            &&& !(code[s.pc as int].effect is Scalar) && ((s.result is Scalar)==(code[s.pc as int].effect is Kernel))
        } by {assert(super::transport::step(code,steps[i]));}
    }
}
}
verus! {
pub(crate) open spec fn mapped_at<T:?Sized>(storage:&Storage<T>,bank:&Bank<T>,a:Seq<usize>,b:Seq<usize>,s:super::super::Step<T>)->bool {
    match s.result {
        super::super::ResultStep::Scalar {..}=>s.pc<a.len() && a[s.pc as int]<storage.scalar_names.len()
            && bank.address(storage.scalar_names@[a[s.pc as int] as int] as int)==s.address(),
        super::super::ResultStep::Payload(_)=>s.pc<b.len() && b[s.pc as int]<storage.payload_names.len()
            && bank.address(storage.payload_names@[b[s.pc as int] as int] as int)==s.address(),
    }
}
#[verifier::opaque]
pub(crate) open spec fn mapped<T:?Sized>(storage:&Storage<T>,bank:&Bank<T>,a:Seq<usize>,b:Seq<usize>,steps:Seq<super::super::Step<T>>)->bool {
    forall|i:int|0<=i<steps.len() ==> mapped_at(storage,bank,a,b,#[trigger] steps[i])
}
proof fn mapped_append<T:?Sized>(storage:&Storage<T>,bank:&Bank<T>,a:Seq<usize>,b:Seq<usize>,steps:Seq<super::super::Step<T>>,s:super::super::Step<T>)
    requires mapped(storage,bank,a,b,steps),mapped_at(storage,bank,a,b,s),
    ensures mapped(storage,bank,a,b,steps.push(s)),
{reveal(mapped);assert forall|i:int|0<=i<steps.push(s).len() implies mapped_at(storage,bank,a,b,#[trigger] steps.push(s)[i]) by {if i<steps.len() {assert(steps.push(s)[i]==steps[i]);} else {assert(steps.push(s)[i]==s);}}}
impl<'a,T:?Sized> mixed::Context<'a,T,()> {
    pub(crate) fn check_mixed<E:ScalarEffect+Copy>(&self,source:&Source<E,T>,bank:&Bank<T>,storage:&Storage<T>)->(out:Result<(),Error>)
        requires self.wf(),storage.matches(bank),storage.held(self),bank.wf(),source.wf(),source.original().succeeded(),source.program().controlled(),
            forall|i:int|0<=i<source.input_spec().len() ==> source.input_spec()[i].identity_spec().namespace()==bank.namespace(),
        ensures out.is_ok() ==> mixed::plan(source.program().code(),source.original().result->Ok_0.steps@)
            && scalar::execution(self.scalar->Some_0.states(),self.scalar->Some_0.routes(),mixed::scalars(source.original().result->Ok_0.steps@))
            && mapped(storage,bank,self.scalar->Some_0.routes(),self.payload->Some_0.routes(),source.original().result->Ok_0.steps@),
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);hide(Source::wf);reveal(mapped);
        proof {source.mixed_plan();mixed::projections_empty::<T>();scalar::empty::<T>(self.scalar->Some_0.states(),self.scalar->Some_0.routes());}
        let inputs=source.inputs();let mut values=self.scalar.as_ref().unwrap().values();let mut i=0;
        proof {assert(source.original().result->Ok_0.steps@.take(0) =~= Seq::empty());}
        while i<inputs.len()
            invariant self.wf(),storage.matches(bank),storage.held(self),bank.wf(),source.wf(),source.original().succeeded(),source.program().controlled(),
                mixed::plan(source.program().code(),source.original().result->Ok_0.steps@),
                inputs@==source.input_spec(),super::inputs::captured(inputs@,source.original().result),i<=inputs.len(),
                forall|j:int|0<=j<inputs.len() ==> (#[trigger] inputs@[j]).identity_spec().namespace()==bank.namespace(),
                values.len()==self.scalar->Some_0.states().len(),
                values@==scalar::after(self.scalar->Some_0.states(),self.scalar->Some_0.routes(),mixed::scalars(source.original().result->Ok_0.steps@.take(i as int))),
                scalar::execution(self.scalar->Some_0.states(),self.scalar->Some_0.routes(),mixed::scalars(source.original().result->Ok_0.steps@.take(i as int))),
                mapped(storage,bank,self.scalar->Some_0.routes(),self.payload->Some_0.routes(),source.original().result->Ok_0.steps@.take(i as int)),
            decreases inputs.len()-i,
        {
            let input=&inputs[i];let pc=input.pc();let entry=match bank.find(input) {Some(entry)=>entry,None=>return Err(Error::Input {step:i})};
            let ghost prefix=source.original().result->Ok_0.steps@.take(i as int);
            proof {mixed::projections_append(prefix,input.source());assert(prefix.push(input.source()) =~= source.original().result->Ok_0.steps@.take(i as int+1));}
            match input.operand() {
                Operand::Scalar(expected)=>{
                    let at=match self.scalar.as_ref().unwrap().route(pc) {Some(at)=>at,None=>return Err(Error::Input {step:i})};
                    if at>=storage.scalar_names.len() || storage.scalar_names[at]!=entry {return Err(Error::Input {step:i});}
                    if values[at].value!=expected.value || values[at].depth!=expected.depth {return Err(Error::Input {step:i});}
                    proof {assert(input.source().result is Scalar);
                        assert(input.source().address()==bank.address(entry as int));
                        assert(self.scalar->Some_0.routes()[pc as int]==at);
                        assert(bank.address(storage.scalar_names@[self.scalar->Some_0.routes()[pc as int] as int] as int)==input.source().address());
                    }
                    let after=match input.scalar_output() {Some(value)=>value,None=>return Err(Error::Input {step:i})};
                    proof {assert(values@[at as int]==*expected);scalar::append(self.scalar->Some_0.states(),self.scalar->Some_0.routes(),mixed::scalars(prefix),input.source());}
                    values.set(at,after);
                },
                Operand::Payload {..}=>{
                    proof {assert(input.source().result is Payload);}
                    let at=match self.payload.as_ref().unwrap().route(pc) {Some(at)=>at,None=>return Err(Error::Input {step:i})};
                    if at>=storage.payload_names.len() || storage.payload_names[at]!=entry {return Err(Error::Input {step:i});}
                    proof {assert(self.payload->Some_0.routes()[pc as int]==at);assert(input.source().address()==bank.address(entry as int));
                        assert(bank.address(storage.payload_names@[self.payload->Some_0.routes()[pc as int] as int] as int)==input.source().address());}
                },
            }
            proof {
                assert(mapped_at(storage,bank,self.scalar->Some_0.routes(),self.payload->Some_0.routes(),input.source()));
                mapped_append(storage,bank,self.scalar->Some_0.routes(),self.payload->Some_0.routes(),prefix,input.source());
            }i+=1;
        }
        proof {assert(source.original().result->Ok_0.steps@.take(i as int) =~= source.original().result->Ok_0.steps@);}
        Ok(())
    }
}
}
verus! {
impl<T:?Sized> Storage<T> {
    pub(crate) open spec fn typed_view(&self,bank:&Bank<T>,view:&Bank<T>)->bool {
        view.namespace()==bank.namespace() && view.journal()==bank.journal() && view.len_spec()==self.payload_names.len()
            && forall|i:int|0<=i<view.len_spec() ==> view.address(i)==bank.address(self.payload_names@[i] as int)
                && (#[trigger] view.target(i))==bank.target(self.payload_names@[i] as int) && view.service(i)==bank.service(self.payload_names@[i] as int)
    }
    pub(crate) fn payload_bank(&self,bank:&Bank<T>)->(out:Bank<T>)
        requires self.matches(bank),bank.wf(),ensures out.wf(),self.typed_view(bank,&out),
    {
        proof {assert forall|i:int|0<=i<self.payload_names.len() implies (#[trigger] self.payload_names@[i])<bank.len_spec() by {assert(self.payload_entry(bank,i));}}
        bank.select(self.payload_names.as_slice())
    }
    pub(crate) proof fn held_payload_bank(&self,bank:&Bank<T>,view:&Bank<T>,context:&mixed::Context<'_,T,()>)
        requires self.matches(bank),self.held(context),self.typed_view(bank,view),
        ensures context.payload->Some_0.bank(view),
    {assert forall|i:int|0<=i<view.len_spec() implies (#[trigger] view.target(i)) is Payload
        && context.payload->Some_0.targets()[i]==view.target(i)->Payload_0 && context.payload->Some_0.slots()[i]==view.service(i) by {assert(self.payload_entry(bank,i));}}
    pub(crate) proof fn typed_routes(&self,bank:&Bank<T>,view:&Bank<T>,context:&mixed::Context<'_,T,()>,steps:Seq<super::super::Step<T>>)
        requires self.matches(bank),self.held(context),self.typed_view(bank,view),view.wf(),mapped(self,bank,context.scalar->Some_0.routes(),context.payload->Some_0.routes(),steps),
        ensures super::protected::mapped(view,context.payload->Some_0.routes(),mixed::payloads(steps)),
    {
        reveal(mapped);
        assert forall|i:int|0<=i<mixed::payloads(steps).len() implies {
            let s=#[trigger] mixed::payloads(steps)[i];
            &&& s.pc<context.payload->Some_0.routes().len() && context.payload->Some_0.routes()[s.pc as int]<view.len_spec()
            &&& view.mapping().contains_pair(s.address(),view.target_address(context.payload->Some_0.routes()[s.pc as int] as int))
        } by {let j=mixed::payload_member(steps,i);view.mapping_entry(context.payload->Some_0.routes()[steps[j].pc as int] as int);}
    }
}
impl<E:ScalarEffect,T:?Sized> Source<E,T> {
    pub(crate) fn payload_inputs(&self,Ghost(namespace):Ghost<vstd::resource::Loc>)->(out:Vec<Input<T>>)
        requires self.wf(),self.original().succeeded(),forall|i:int|0<=i<self.input_spec().len() ==> self.input_spec()[i].identity_spec().namespace()==namespace,
        ensures super::typed_tracker::observations(out@)==mixed::payloads(self.original().result->Ok_0.steps@),
            forall|i:int|0<=i<out.len() ==> (#[trigger] out@[i]).wf() && out@[i].identity_spec().namespace()==namespace,
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);hide(Source::wf);
        let inputs=self.inputs();let mut out:Vec<Input<T>>=Vec::new();let mut i=0;
        proof {mixed::projections_empty::<T>();assert(self.original().result->Ok_0.steps@.take(0) =~= Seq::empty());}
        while i<inputs.len()
            invariant inputs@==self.input_spec(),super::inputs::captured(inputs@,self.original().result),self.wf(),self.original().succeeded(),i<=inputs.len(),
                forall|j:int|0<=j<inputs.len() ==> (#[trigger] inputs@[j]).identity_spec().namespace()==namespace,
                super::typed_tracker::observations(out@)==mixed::payloads(self.original().result->Ok_0.steps@.take(i as int)),
                forall|j:int|0<=j<out.len() ==> (#[trigger] out@[j]).wf() && out@[j].identity_spec().namespace()==namespace,
            decreases inputs.len()-i,
        {
            let input=&inputs[i];let ghost prior=out@;
            proof {mixed::projections_append(self.original().result->Ok_0.steps@.take(i as int),input.source());
                assert(self.original().result->Ok_0.steps@.take(i as int+1) =~= self.original().result->Ok_0.steps@.take(i as int).push(input.source()));}
            if matches!(input.operand(),Operand::Payload {..}) {
                out.push(input.duplicate());
                proof {assert(super::typed_tracker::observations(out@) =~= super::typed_tracker::observations(prior).push(input.source()));}
            }i+=1;
        }
        proof {assert(self.original().result->Ok_0.steps@.take(i as int) =~= self.original().result->Ok_0.steps@);}
        out
    }
}
}

verus! {
pub(crate) open spec fn advanced<T:?Sized>(before:&mixed::Context<'_,T,()>,after:&mixed::Context<'_,T,()>,steps:Seq<super::super::Step<T>>)->bool {
    &&& scalar::execution(before.scalar->Some_0.states(),after.scalar->Some_0.routes(),mixed::scalars(steps))
    &&& scalar::addressed(after.scalar->Some_0.targets(),after.scalar->Some_0.routes(),mixed::scalars(steps))
    &&& after.scalar->Some_0.states()==scalar::after(before.scalar->Some_0.states(),after.scalar->Some_0.routes(),mixed::scalars(steps))
    &&& payload::execution(before.payload->Some_0.states(),before.payload->Some_0.revisions(),after.payload->Some_0.routes(),mixed::payloads(steps))
    &&& payload::addressed(after.payload->Some_0.targets(),after.payload->Some_0.routes(),mixed::payloads(steps))
    &&& after.payload->Some_0.states()==payload::after(before.payload->Some_0.states(),after.payload->Some_0.routes(),mixed::payloads(steps))
    &&& after.payload->Some_0.revisions()==payload::clocks(before.payload->Some_0.revisions(),after.payload->Some_0.routes(),mixed::payloads(steps))
    &&& super::typed_correspondence::inputs(before.payload->Some_0.states(),after.payload->Some_0.routes(),mixed::payloads(steps))
}
}
verus! {
pub ghost struct Interval<T:?Sized> {
    pub scalar:super::protected::Interval<T>,pub typed:super::typed_protected::Interval<T>,
    pub source:Seq<super::super::Step<T>>,pub target:Seq<super::super::Step<T>>,pub admitted:bool,
}
impl<T:?Sized> Interval<T> {
    pub closed spec fn wf(&self,bank:&Bank<T>)->bool {
        self.scalar.wf() && self.typed.wf()
            && self.scalar.steps==mixed::scalars(self.target) && self.typed.steps==mixed::payloads(self.target)
            && (self.admitted ==> mixed::same(self.target,self.source)
                && super::typed_correspondence::allocations(bank,self.source,self.target)
                && self.typed.correspondence.is_some()
                && self.typed.correspondence.unwrap().source==mixed::payloads(self.source))
    }
}
impl<E:ScalarEffect,T:?Sized> super::batch::Batch<E,T> {
    pub open spec fn mixed_prefix(&self,sources:Seq<Source<E,T>>)->bool {
        self.mixed_protection@.len()==self.calls.len() && forall|i:int|0<=i<self.calls.len() ==> {
            let p=#[trigger] self.mixed_protection@[i];let call=self.calls@[i];
            &&& p.wf(&self.bank) && call.report.is_ok() && i<self.order.len() && self.order@[i]<sources.len()
            &&& p.target==super::protected::result_steps(call.report->Ok_0.result)
            &&& p.source==sources[self.order@[i] as int].original().result->Ok_0.steps@
            &&& p.admitted==call.report->Ok_0.result.is_ok()
            &&& i>0 ==> p.scalar.before==self.mixed_protection@[i-1].scalar.after
                && p.typed.before==self.mixed_protection@[i-1].typed.after
                && p.typed.before_revisions==self.mixed_protection@[i-1].typed.after_revisions
                && (p.admitted ==> self.mixed_protection@[i-1].typed.correspondence.is_some()
                    && p.typed.correspondence.unwrap().before_names==self.mixed_protection@[i-1].typed.correspondence.unwrap().after_names
                    && p.typed.correspondence.unwrap().before_source==self.mixed_protection@[i-1].typed.correspondence.unwrap().after_source)
        }
    }
    pub proof fn mixed_aliases(&self,sources:Seq<Source<E,T>>,left:int,a:int,right:int,b:int)
        requires self.bank.wf(),self.mixed_prefix(sources),0<=left<self.calls.len(),0<=right<self.calls.len(),
            self.calls@[left].report->Ok_0.result.is_ok(),self.calls@[right].report->Ok_0.result.is_ok(),
            0<=a<self.mixed_protection@[left].source.len(),0<=b<self.mixed_protection@[right].source.len(),
        ensures (self.mixed_protection@[left].source[a].address()==self.mixed_protection@[right].source[b].address())
            ==(self.mixed_protection@[left].target[a].address()==self.mixed_protection@[right].target[b].address()),
    {reveal(super::typed_correspondence::allocations);self.bank.mapping_injective();}
}
proof fn projection_at<T:?Sized>(steps:Seq<super::super::Step<T>>,i:int)->(j:int)
    requires 0<=i<steps.len(),
    ensures steps[i].result is Scalar ==> 0<=j<mixed::scalars(steps).len() && mixed::scalars(steps)[j]==steps[i],
        steps[i].result is Payload ==> 0<=j<mixed::payloads(steps).len() && mixed::payloads(steps)[j]==steps[i],
    decreases steps.len(),
{
    reveal(mixed::scalars);reveal(mixed::payloads);
    if i==steps.len()-1 {if steps[i].result is Scalar {(mixed::scalars(steps).len()-1) as int} else {(mixed::payloads(steps).len()-1) as int}}
    else {projection_at(steps.drop_last(),i)}
}
impl<T:?Sized> Storage<T> {
    pub(crate) proof fn mapped_steps(&self,bank:&Bank<T>,context:&mixed::Context<'_,T,()>,source:Seq<super::super::Step<T>>,actual:Seq<super::super::Step<T>>)
        requires self.matches(bank),self.held(context),bank.wf(),mixed::same(actual,source),
            mapped(self,bank,context.scalar->Some_0.routes(),context.payload->Some_0.routes(),source),
            scalar::addressed(context.scalar->Some_0.targets(),context.scalar->Some_0.routes(),mixed::scalars(actual)),
            payload::addressed(context.payload->Some_0.targets(),context.payload->Some_0.routes(),mixed::payloads(actual)),
        ensures super::typed_correspondence::allocations(bank,source,actual),
    {
        reveal(mapped);reveal(scalar::addressed);reveal(payload::addressed);reveal(super::typed_correspondence::allocations);
        assert forall|i:int|0<=i<source.len() implies super::selection::mapped(bank,#[trigger] source[i],actual[i]) by {
            let j=projection_at(actual,i);let pc=source[i].pc as int;
            if actual[i].result is Scalar {
                let n=context.scalar->Some_0.routes()[pc] as int;assert(self.scalar_entry(bank,n));bank.mapping_entry(self.scalar_names@[n] as int);
            } else {
                let n=context.payload->Some_0.routes()[pc] as int;assert(self.payload_entry(bank,n));bank.mapping_entry(self.payload_names@[n] as int);
            }
        }
    }
}

#[verifier::rlimit(16)]
#[verifier::spinoff_prover]
#[allow(unused_variables)] // Source journal anchors the erased namespace contract.
// The real owners, storage catalogs and erased proof inputs are distinct.
#[allow(clippy::too_many_arguments)]
pub(crate) fn run_calls<P,E:ScalarEffect+Copy,T:?Sized>(runtime:&mut super::ManagedRuntime<P,(),E,T,()>,source_journal:&crate::reversible_value::joint::Journal,sources:&[Source<E,T>],mut names:super::batch::Names,mut out:super::batch::Batch<E,T>,context:&mut Option<mixed::Context<'_,T,()>>,storage:&Storage<T>,view:&Bank<T>)->(result:super::batch::Batch<E,T>)
    requires old(runtime).wf(),out.bank.wf(),old(runtime).journal_spec()==out.bank.journal(),out.bank.namespace()==source_journal.identity_namespace(),
        super::batch::supported_namespace(sources@,*source_journal),out.calls.len()==0,out.mixed_protection@.len()==0,
        super::order::prefix(sources@,out.order@,sources@.len()),super::order::chronological(sources@,out.order@),
        forall|k:int|0<=k<out.order.len() ==> sources[out.order@[k] as int].provision_ports().len()==0,
        super::selection::providers_match(&out.bank,out.providers@,crate::lifecycle_state::services::capture::sources(old(runtime).publications().entries())),
        old(context).is_some(),old(context)->Some_0.wf(),storage.matches(&out.bank),storage.held(&old(context)->Some_0),storage.original_slots(&old(context)->Some_0),storage.typed_view(&out.bank,view),view.wf(),old(context)->Some_0.payload->Some_0.bank(view),
        forall|i:int|0<=i<view.len_spec() ==> #[trigger] old(context)->Some_0.payload->Some_0.initial_entry(view,i),
    ensures result.mixed_prefix(sources@),final(runtime).wf(),result.bank.wf(),result.actual_prefix(sources@),result.order@==out.order@,
        result.failure.is_none() ==> result.calls.len()==sources.len() && result.succeeded(),
        final(context).is_some(),final(context)->Some_0.wf(),storage.held(&final(context)->Some_0),storage.original_slots(&final(context)->Some_0),
{
    hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);hide(Source::wf);hide(super::TargetRun::from_source);
    hide(super::typed_correspondence::heaps);hide(super::typed_correspondence::aligned);hide(super::typed_correspondence::paired);
    reveal(Source::input_spec);reveal(Source::provision_ports);
    let mut tracker=super::typed_tracker::Tracker::start(view,context.as_ref().unwrap().payload.as_ref().unwrap());
    let ghost chosen=out.order@;let mut i=0;
    while i<out.order.len()
        invariant context.is_some(),context->Some_0.wf(),storage.matches(&out.bank),storage.held(&context->Some_0),storage.original_slots(&context->Some_0),storage.typed_view(&out.bank,view),view.wf(),context->Some_0.payload->Some_0.bank(view),
            tracker.wf(view),super::typed_correspondence::heaps(tracker.names(),tracker.states(),context->Some_0.payload->Some_0.states()),out.mixed_prefix(sources@),
            out.mixed_protection@.len()>0 ==> out.mixed_protection@.last().typed.correspondence.is_some()
                && out.mixed_protection@.last().typed.correspondence.unwrap().after_source==tracker.states()
                && out.mixed_protection@.last().typed.correspondence.unwrap().after_names==tracker.names()
                && out.mixed_protection@.last().typed.after==context->Some_0.payload->Some_0.states()
                && out.mixed_protection@.last().typed.after_revisions==context->Some_0.payload->Some_0.revisions()
                && out.mixed_protection@.last().scalar.after==context->Some_0.scalar->Some_0.states(),
            out.order@==chosen,super::order::prefix(sources@,chosen,sources@.len()),super::order::chronological(sources@,chosen),i<=out.order.len(),runtime.wf(),runtime.journal_spec()==out.bank.journal(),out.bank.wf(),out.bank.namespace()==source_journal.identity_namespace(),out.calls.len()==i,out.actual_prefix(sources@),out.succeeded(),
            forall|k:int|0<=k<chosen.len() ==> sources[chosen[k] as int].provision_ports().len()==0,
            super::selection::providers_match(&out.bank,out.providers@,crate::lifecycle_state::services::capture::sources(runtime.publications().entries())),super::batch::supported_namespace(sources@,*source_journal),
        decreases out.order.len()-i,
    {
        let (anchor,work_domain)=match names.take() {Some(n)=>n,None=>{out.failure=Some(super::batch::Failure::Capacity);return out;}};
        let call=out.order[i];
        proof {super::batch::supported_at(sources@,*source_journal,call as int);}
        if !sources[call].is_controlled() {out.failure=Some(super::batch::Failure::Protection {call:Some(call),error:super::protected::Error::NotControlled});return out;}
        if !sources[call].succeeded() {out.failure=Some(super::batch::Failure::Invocation {call});return out;}
        let inputs=sources[call].payload_inputs(Ghost(view.namespace()));
        let plan=match tracker.prepare_inputs(inputs.as_slice(),view) {Ok(plan)=>plan,Err(error)=>{out.failure=Some(super::batch::Failure::Protection {call:Some(call),error:super::protected::Error::Typed(error)});return out;}};
        let ghost prior=context->Some_0;let mut scalar=None;let mut typed=None;
        let mut run=match sources[call].instantiate_all(runtime,super::Destination {parent:None,anchor,host:(),work_domain},&out.bank,out.providers.as_slice(),&mut scalar,&mut typed,context,Some(storage),None,None,None) {
            Ok(run)=>run,
            Err(super::protected::Start::Before(error))=>{out.failure=Some(super::batch::Failure::Start {call,error});return out;},
            Err(super::protected::Start::After {id,owner,error})=>{out.blocked=Some((id,*owner));out.failure=Some(super::batch::Failure::Protection {call:Some(call),error});return out;},
        };
        proof {storage.held_payload_bank(&out.bank,view,&context->Some_0);}
        let ghost steps=super::protected::result_steps(run.report->Ok_0.result);
        let ghost correspondence=if run.report->Ok_0.result.is_ok() {
            storage.typed_routes(&out.bank,view,&context->Some_0,sources[call as int].original().result->Ok_0.steps@);
            plan.routes(view,context->Some_0.payload->Some_0.routes());
            mixed::same_payloads(steps,sources[call as int].original().result->Ok_0.steps@);
            storage.mapped_steps(&out.bank,&context->Some_0,sources[call as int].original().result->Ok_0.steps@,steps);
            Some(super::typed_correspondence::certify_steps(tracker.names(),tracker.states(),prior.payload->Some_0.states(),context->Some_0.payload->Some_0.routes(),plan.steps(),mixed::payloads(steps)))
        } else {None};
        let ghost scalar_interval=super::protected::Interval {before:prior.scalar->Some_0.states(),after:context->Some_0.scalar->Some_0.states(),routes:context->Some_0.scalar->Some_0.routes(),steps:mixed::scalars(steps)};
        let ghost typed_interval=super::typed_protected::Interval {correspondence,before:prior.payload->Some_0.states(),after:context->Some_0.payload->Some_0.states(),before_revisions:prior.payload->Some_0.revisions(),after_revisions:context->Some_0.payload->Some_0.revisions(),routes:context->Some_0.payload->Some_0.routes(),steps:mixed::payloads(steps)};
        proof {
            if correspondence.is_some() {correspondence.unwrap().facts();}
            if run.report->Ok_0.result.is_err() {mixed::projections_empty::<T>();scalar::empty::<T>(prior.scalar->Some_0.states(),context->Some_0.scalar->Some_0.routes());payload::empty::<T>(prior.payload->Some_0.states(),prior.payload->Some_0.revisions(),context->Some_0.payload->Some_0.routes());}
            scalar_interval.establish();typed_interval.establish();
        }
        let ghost interval=Interval {scalar:scalar_interval,typed:typed_interval,source:sources[call as int].original().result->Ok_0.steps@,target:steps,admitted:run.report->Ok_0.result.is_ok()};
        proof {assert(interval.wf(&out.bank));}
        out.mixed_protection=Ghost(out.mixed_protection@.push(interval));
        let succeeded=match &run.report {Ok(r)=>match &r.result {Ok(report)=>report.succeeded(),Err(_)=>false},Err(_)=>false};
        if !succeeded {out.calls.push(run);out.failure=Some(super::batch::Failure::Invocation {call});return out;}
        proof {correspondence.unwrap().facts();}
        tracker=plan.finish(Ghost(correspondence.unwrap().after_names));
        proof {assert(run.owner.wf()) by {reveal(super::TargetRun::from_source);}}
        let ghost before_finish=runtime.publications().entries();let ghost before_run=run;
        let finished=run.owner.finish(runtime,run.id);
        proof {
            assert(run.report==before_run.report && run.inputs==before_run.inputs && run.id==before_run.id);
            assert(run.owner.baseline()==before_run.owner.baseline() && run.owner.recovery_boundary()==before_run.owner.recovery_boundary());
            assert(run.from_source(&sources[call as int])) by {reveal(super::TargetRun::from_source);}
            super::selection::preserve_providers(&out.bank,out.providers@,before_finish,runtime.publications().entries());
        }
        out.calls.push(run);
        if let Err(error)=finished {out.failure=Some(super::batch::Failure::Finish {call,error});return out;}i+=1;
    }out
}
}
