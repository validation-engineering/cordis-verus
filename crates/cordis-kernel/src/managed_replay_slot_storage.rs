//! Protect the actual published scalar slots independently from the cell pool.
//! Catalog slots are deduplicated before taking locks; several can select one
//! canonical object and each stored inverse continues to name its own object.
use super::Slots;
use crate::lifecycle_state::services::NativeEpisode;
use crate::reversible_value::managed::{
    protected as scalar, protected_mixed as held, protected_typed as payload,
    replay::{
        bank::Bank,
        mixed,
        services::{self, Service},
        Source,
    },
    Effect, Slot,
};
use crate::reversible_value::{effect::ScalarEffect, slot};
use crate::Port;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub(crate) struct Storage {slots:Vec<slot::Slot>,captures:Vec<slot::Capture>,selected:Vec<usize>,catalog:Vec<usize>}
impl Storage {
    pub(crate) closed spec fn matches<T:?Sized>(&self,base:&mixed::Storage<T>,bank:&Bank<T>,catalog:&Slots<T>)->bool {
        self.slots.len()==self.captures.len() && self.slots.len()==self.selected.len() && self.slots.len()==self.catalog.len()
            && forall|i:int|0<=i<self.slots.len() ==> {
                let n=#[trigger] self.catalog@[i];
                &&& n<catalog.len_spec() && catalog.service(n as int).managed()==Some(self.slots@[i])
                &&& self.captures@[i].wf() && self.captures@[i].slot()==self.slots@[i]
                &&& self.captures@[i].revision_spec()==catalog.capture(n as int).revision_spec()
                &&& self.selected@[i]<base.scalar_values.len() && *self.captures@[i].value_spec()==base.scalar_values@[self.selected@[i] as int]
            }
    }
    pub(crate) closed spec fn held<T:?Sized>(&self,context:&held::Context<'_,T,()>)->bool {
        context.scalar->Some_0.slot_names()==self.slots@ && context.scalar->Some_0.chosen()==self.selected@
    }
    pub(crate) proof fn held_frame<T:?Sized>(&self,prior:&held::Context<'_,T,()>,next:&held::Context<'_,T,()>)
        requires self.held(prior),next.scalar->Some_0.slot_names()==prior.scalar->Some_0.slot_names(),next.scalar->Some_0.chosen()==prior.scalar->Some_0.chosen(),
        ensures self.held(next),
    {}
    #[allow(unused_variables)] // Bank parameters anchor erased allocation proofs.
    pub(crate) fn new<T:?Sized>(base:&mixed::Storage<T>,bank:&Bank<T>,catalog:&Slots<T>,providers:&[Service<T>],preloads:&[services::Preload<T>])->(out:Result<Self,mixed::Error>)
        requires bank.wf(),base.matches(bank),catalog.wf(bank),
        ensures out.is_ok() ==> out->Ok_0.matches(base,bank,catalog),
    {
        let mut out=Self {slots:Vec::new(),captures:Vec::new(),selected:Vec::new(),catalog:Vec::new()};let mut i=0;
        while i<catalog.len()
            invariant bank.wf(),base.matches(bank),catalog.wf(bank),i<=catalog.len_spec(),out.matches(base,bank,catalog),
            decreases catalog.len_spec()-i,
        {
            let mut p=0;let mut used=false;
            while p<providers.len() invariant p<=providers.len(),decreases providers.len()-p,
            {if providers[p].slot==Some(i) {used=true;}p+=1;}
            let mut p=0;
            while p<preloads.len() invariant p<=preloads.len(),decreases preloads.len()-p,
            {if let Some(route)=&preloads[p].route {if route.slot==Some(i) {used=true;}}p+=1;}
            if used {
                proof {catalog.entry_facts(bank,i as int);}
                let selected=catalog.selected_entry(i).unwrap();
                let index=match base.scalar_index(selected) {Some(n)=>n,None=>return Err(mixed::Error::Slot {index:i})};
                let service=catalog.published(i).unwrap();let capture=catalog.retained(i).unwrap().duplicate();
                out.slots.push(service.reversible().unwrap().clone());out.captures.push(capture);out.selected.push(index);out.catalog.push(i);
                proof {assert(base.scalar_entry(bank,index as int));}
            }i+=1;
        }Ok(out)
    }
    fn route(&self,catalog:usize)->(out:Option<usize>)
        ensures out.is_some() ==> out.unwrap()<self.catalog.len() && self.catalog@[out.unwrap() as int]==catalog,
    {
        let mut i=0;while i<self.catalog.len() invariant i<=self.catalog.len(),decreases self.catalog.len()-i,
        {if self.catalog[i]==catalog {return Some(i);}i+=1;}None
    }
    #[allow(unused_variables)] // Bank and catalog anchor erased allocation proofs.
    pub(crate) fn acquire<'a,T:?Sized>(&'a self,base:&'a mixed::Storage<T>,bank:&Bank<T>,catalog:&Slots<T>)->(out:Result<held::Context<'a,T,()>,mixed::Error>)
        requires bank.wf(),base.matches(bank),self.matches(base,bank,catalog),
        ensures out.is_ok() ==> out->Ok_0.wf(),out.is_ok() ==> self.held(&out->Ok_0) && base.held(&out->Ok_0),
    {
        proof {
            assert forall|i:int,j:int|0<=i<j<base.scalar_values.len() implies base.scalar_values@[i]!=base.scalar_values@[j] by {
                assert(base.scalar_entry(bank,i));assert(base.scalar_entry(bank,j));bank.aliases(base.scalar_names@[i] as int,base.scalar_names@[j] as int);
            }
            assert forall|i:int,j:int|0<=i<j<base.payload_values.len() implies base.payload_values@[i]!=base.payload_values@[j] by {
                assert(base.payload_entry(bank,i));assert(base.payload_entry(bank,j));bank.aliases(base.payload_names@[i] as int,base.payload_names@[j] as int);
            }
        }
        proof {
            assert forall|i:int|0<=i<self.slots.len() implies (#[trigger] self.captures@[i]).wf() && self.captures@[i].slot()==self.slots@[i]
                && self.selected@[i]<base.scalar_values.len() && *self.captures@[i].value_spec()==base.scalar_values@[self.selected@[i] as int] by {let n=self.catalog@[i];}
        }
        let selected=self.selected.clone();
        let a=match scalar::Context::acquire_selected(base.scalar_values.as_slice(),self.slots.as_slice(),self.captures.as_slice(),selected) {
            Ok(a)=>a,Err(scalar::Error::ChangedSlot {index})=>return Err(mixed::Error::Slot {index}),
        };
        let mut payload_slots=Vec::new();let mut i=0;
        while i<base.payload_slots.len()
            invariant base.matches(bank),i<=base.payload_slots.len(),payload_slots.len()==i,forall|j:int|0<=j<i ==> payload_slots@[j]==base.payload_slots@[j],
            decreases base.payload_slots.len()-i,
        {payload_slots.push(base.payload_slots[i].clone());i+=1;}
        proof {assert(payload_slots@ =~= base.payload_slots@);assert forall|i:int|0<=i<base.payload_slots.len() implies base.payload_slots@[i].opaque_spec()==Some(base.payload_values@[i]) by {assert(base.payload_entry(bank,i));}}
        match payload::Context::acquire(base.payload_values.as_slice(),payload_slots) {
            Ok(b)=>Ok(held::Context {scalar:Some(a),payload:Some(b)}),
            Err(e)=>{a.release();Err(mixed::Error::Typed(e))},
        }
    }
    #[verifier::rlimit(16)]
    #[verifier::spinoff_prover]
    #[allow(unused_variables)] // Actual storage is retained; bank/catalog are proof context here.
    #[allow(clippy::too_many_arguments)] // Both runtime pools and erased origin evidence are explicit.
    pub(crate) fn bind<T:?Sized,E:ScalarEffect>(&self,context:&mut held::Context<'_,T,()>,episode:&NativeEpisode<Slot<T,()>>,ports:&[Port],source:&Source<E,T>,base:&mixed::Storage<T>,bank:&Bank<T>,catalog:&Slots<T>,providers:&[Service<T>],owned:&[Service<T>])->(out:Result<(),mixed::Error>)
        requires old(context).wf(),self.held(old(context)),base.held(old(context)),self.matches(base,bank,catalog),base.matches(bank),bank.wf(),catalog.wf(bank),
            episode.wf(),source.wf(),source.original().succeeded(),source.program().controlled(),ports.len()==source.program().code().len(),
            services::published(bank,catalog,providers@,episode.capture().sources),services::owned(bank,catalog,owned@,*episode),
        ensures final(context).wf(),self.held(final(context)),base.held(final(context)),
            final(context).scalar->Some_0.states()==old(context).scalar->Some_0.states(),final(context).payload->Some_0.states()==old(context).payload->Some_0.states(),
            final(context).payload->Some_0.revisions()==old(context).payload->Some_0.revisions(),
            final(context).scalar->Some_0.slot_names()==old(context).scalar->Some_0.slot_names(),final(context).scalar->Some_0.chosen()==old(context).scalar->Some_0.chosen(),
            out.is_ok() ==> final(context).supports(*episode,ports@,source.program().code(),source.original().result->Ok_0.steps@),
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
        let mut a:Vec<scalar::Binding>=Vec::new();let mut b:Vec<payload::Binding>=Vec::new();let mut i=0;
        while i<ports.len()
            invariant *context==*old(context),context.wf(),self.held(context),base.held(context),self.matches(base,bank,catalog),base.matches(bank),bank.wf(),catalog.wf(bank),episode.wf(),source.wf(),source.original().succeeded(),source.program().controlled(),ports.len()==source.program().code().len(),i<=ports.len(),
                services::published(bank,catalog,providers@,episode.capture().sources),services::owned(bank,catalog,owned@,*episode),
                a.len()==if self.slots.len()>0 {i} else {0},b.len()==if base.payload_values.len()>0 {i} else {0},
                forall|j:int|0<=j<a.len() ==> (#[trigger] a@[j]).slot<self.slots.len(),
                forall|j:int|0<=j<b.len() ==> (#[trigger] b@[j]).entry<base.payload_values.len(),
                forall|j:int|0<=j<i && source.visited(j as usize) ==> match (#[trigger] source.program().code()[j]).effect {
                    Effect::Kernel(_)=>j<a.len() && a@[j].port==ports@[j] && !episode.closed() && episode.selects_slot(a@[j].provider,ports@[j],self.slots@[a@[j].slot as int]),
                    Effect::Replace(_)=>j<b.len() && b@[j].port@==ports@[j] && !episode.closed() && episode.selects_value(b@[j].provider@,ports@[j],base.payload_slots@[b@[j].entry as int]),
                    _=>false,
                },
            decreases ports.len()-i,
        {
            let port=ports[i];
            if !source.visits(i) {
                if !self.slots.is_empty() {a.push(scalar::Binding {provider:0,port,slot:0});}
                if !base.payload_values.is_empty() {b.push(payload::Binding {provider:Ghost(0),port:Ghost(port),entry:0});}
                i+=1;continue;
            }
            let own=episode.declares(port);
            let available=if own {owned} else {providers};
            let (id,_)=match episode.read(port) {Ok(pair)=>pair,Err(_)=>return Err(mixed::Error::Binding {pc:i})};
            let mut p=0;let mut found:Option<usize>=None;
            while p<available.len()
                invariant p<=available.len(),found.is_some() ==> found.unwrap()<available.len() && available@[found.unwrap() as int].id==id && available@[found.unwrap() as int].port==port,
                decreases available.len()-p,
            {if available[p].id==id && available[p].port==port {found=Some(p);break;}p+=1;}
            let n=match found {Some(n)=>n,None=>return Err(mixed::Error::Binding {pc:i})};let provider=&available[n];
            let expected=source.binding_origin(port);
            if expected.is_none() || provider.source_origin!=expected {return Err(mixed::Error::Binding {pc:i});}
            proof {assert(source.uses_origin(port,provider.source_origin.unwrap()));}
            proof {
                if own {
                    assert(provider.mapped(bank,catalog));assert(episode.owned().contains_pair((port.key,port.realm),provider.service));
                } else {
                    assert(provider.mapped(bank,catalog));assert(episode.capture().sources[id].values.contains_pair((port.key,port.realm),provider.service));
                }
                assert(episode.selects_value(id,port,provider.service));
            }
            let (s,t)=match &source.function_ref().instructions()[i].effect {
                Effect::Kernel(_)=>{
                    let entry=match provider.slot {Some(n)=>n,None=>return Err(mixed::Error::Binding {pc:i})};
                    let at=match self.route(entry) {Some(n)=>n,None=>return Err(mixed::Error::Binding {pc:i})};
                    proof {assert(episode.selects_slot(id,port,self.slots@[at as int]));}(at,0usize)
                },
                Effect::Replace(_)=>{
                    if provider.slot.is_some() {return Err(mixed::Error::Binding {pc:i});}
                    let at=match base.payload_index(provider.index) {Some(n)=>n,None=>return Err(mixed::Error::Binding {pc:i})};
                    proof {assert(base.payload_entry(bank,at as int));assert(episode.selects_value(id,port,base.payload_slots@[at as int]));}(0usize,at)
                },
                _=>return Err(mixed::Error::Uncontrolled),
            };
            let ghost old_a=a@;let ghost old_b=b@;
            if !self.slots.is_empty() {a.push(scalar::Binding {provider:id,port,slot:s});}
            if !base.payload_values.is_empty() {b.push(payload::Binding {provider:Ghost(id),port:Ghost(port),entry:t});}
            proof {
                assert forall|j:int|0<=j<i+1 && source.visited(j as usize) implies match (#[trigger] source.program().code()[j]).effect {
                    Effect::Kernel(_)=>j<a.len() && a@[j].port==ports@[j] && !episode.closed() && episode.selects_slot(a@[j].provider,ports@[j],self.slots@[a@[j].slot as int]),
                    Effect::Replace(_)=>j<b.len() && b@[j].port@==ports@[j] && !episode.closed() && episode.selects_value(b@[j].provider@,ports@[j],base.payload_slots@[b@[j].entry as int]),
                    _=>false,
                } by {if j<i {if source.program().code()[j].effect is Kernel {assert(a@[j]==old_a[j]);} else {assert(b@[j]==old_b[j]);}}}
            }
            i+=1;
        }
        context.scalar.as_mut().unwrap().bind(a);context.payload.as_mut().unwrap().bind(b);
        proof {
            reveal(held::Context::supports);source.mixed_plan();
            assert forall|n:int|0<=n<source.original().result->Ok_0.steps.len() implies {
                let pc=(#[trigger] source.original().result->Ok_0.steps@[n]).pc;
                &&& pc<source.program().code().len() && context.for_call(*episode,pc,ports@[pc as int],source.program().code()[pc as int])
            } by {held::plan_at(source.program().code(),source.original().result->Ok_0.steps@,n);assert(source.visited(source.original().result->Ok_0.steps@[n].pc));}
        }Ok(())
    }
}
}
