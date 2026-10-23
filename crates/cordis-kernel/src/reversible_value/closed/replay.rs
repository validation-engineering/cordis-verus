//! The closed-data replay entry. Every stored constant (including skipped
//! branches), retained operand and newly supplied value is checked against one
//! explicit object table. The original protected interpreter remains the only
//! executor; arbitrary `Arc<T>` continues through the ordinary generic API.
use super::{
    objects::{Projection, Table},
    Reference, Value,
};
use crate::lifecycle_state::registration::shared_child::SharedChild;
use crate::reversible_value::managed::interleaving::history::lifecycle::RecordedExecution;
use crate::reversible_value::{
    effect::ScalarEffect,
    managed::{
        replay::{self, batch, session, ManagedRuntime, Source},
        Effect, Function,
    },
};
use crate::Port;
use vstd::prelude::*;
pub(crate) mod fibers;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
impl<E> Function<E,Value> {
    pub open spec fn closed_data(&self,schema:Seq<Reference>)->bool {
        self.controlled() && forall|i:int|0<=i<self.code().len() ==> match (#[trigger] self.code()[i]).effect {
            Effect::Replace(v)=>v.admissible(schema),_=>true,
        }
    }
    /// No callback or user-supplied equality is called during this check.
    pub fn check_closed_data(&self,schema:&[Reference])->(out:bool) ensures out==self.closed_data(schema@),
    {
        let code=self.instructions();let mut i=0;
        while i<code.len()
            invariant code@==self.code(),i<=code.len(),forall|j:int|0<=j<i ==> !(#[trigger] self.code()[j].effect is Scalar)
                && match self.code()[j].effect {Effect::Replace(v)=>v.admissible(schema@),_=>true},
            decreases code.len()-i,
        {
            match &code[i].effect {
                Effect::Scalar(_)=>return false,
                Effect::Replace(v)=>{v.representation();if !v.check(schema) {return false;}},
                _=>{},
            }i+=1;
        }true
    }
}
impl<E:ScalarEffect> Source<E,Value> {
    pub open spec fn closed_data(&self,schema:Seq<Reference>)->bool {
        self.program().closed_data(schema) && forall|i:int|0<=i<self.input_spec().len() ==>
            match (#[trigger] self.input_spec()[i]).source().before() {
                crate::reversible_value::managed::semantics::Value::Payload(v)=>v.value.admissible(schema),_=>true,
            }
    }
    pub proof fn closed_facts(&self,schema:Seq<Reference>)
        requires self.wf(),self.closed_data(schema),self.original().result.is_ok(),
        ensures self.program().valid(),
            forall|i:int|0<=i<self.original().result->Ok_0.steps.len() ==> {
                let step=#[trigger] self.original().result->Ok_0.steps@[i];
                &&& match step.before() {crate::reversible_value::managed::semantics::Value::Payload(v)=>v.value.admissible(schema),_=>true}
                &&& match step.after() {crate::reversible_value::managed::semantics::Value::Payload(v)=>v.value.admissible(schema),_=>true}
            },
    {
        self.facts();
        assert forall|i:int|0<=i<self.original().result->Ok_0.steps.len() implies {
            let step=#[trigger] self.original().result->Ok_0.steps@[i];
            &&& match step.before() {crate::reversible_value::managed::semantics::Value::Payload(v)=>v.value.admissible(schema),_=>true}
            &&& match step.after() {crate::reversible_value::managed::semantics::Value::Payload(v)=>v.value.admissible(schema),_=>true}
        } by {
            let step=self.original().result->Ok_0.steps@[i];
            assert(self.input_spec()[i].source()==step);
            assert(replay::transport::step(self.program().code(),step));
            if step.after() is Payload {assert(self.program().code()[step.pc as int].effect is Replace);}
        }
    }
    pub open spec fn within(&self,table:Table)->bool {
        (forall|i:int|0<=i<self.input_spec().len() ==> table.contains((#[trigger] self.input_spec()[i]).source().address()))
            && (self.environment().is_some() ==> forall|i:int|0<=i<self.environment().unwrap().entries().len()
                && self.environment().unwrap().entries()[i].result.is_ok() ==>
                    table.contains((#[trigger] self.environment().unwrap().entries()[i]).result->Ok_0.selected.address()))
            && (self.owned_environment().is_some() ==> forall|i:int|0<=i<self.owned_environment().unwrap().entries().len()
                && self.owned_environment().unwrap().entries()[i].result.is_ok() ==>
                    table.contains((#[trigger] self.owned_environment().unwrap().entries()[i]).result->Ok_0.selected.address()))            && (self.publication_environment().is_some() ==> forall|i:int|0<=i<self.publication_environment().unwrap().entries().len()
                && self.publication_environment().unwrap().entries()[i].result.is_ok() ==>
                    table.contains((#[trigger] self.publication_environment().unwrap().entries()[i]).result->Ok_0.selected.address()))
    }
    pub fn check_objects(&self,table:&Table)->(out:bool)
        requires self.wf(),table.wf(),self.publication_environment().is_some() ==> self.publication_environment().unwrap().namespace(table.journal().identity_namespace()),self.owned_environment().is_some() ==> self.owned_environment().unwrap().namespace(table.journal().identity_namespace()),self.environment().is_some() ==> self.environment().unwrap().namespace(table.journal().identity_namespace()),forall|i:int|0<=i<self.input_spec().len() ==> self.input_spec()[i].identity_spec().namespace()==table.journal().identity_namespace(),
        ensures out ==> self.within(*table),
    {
        let inputs=self.inputs();let mut i=0;
        while i<inputs.len()
            invariant self.wf(),table.wf(),inputs@==self.input_spec(),i<=inputs.len(),
                forall|j:int|0<=j<inputs.len() ==> (#[trigger] inputs@[j]).wf() && inputs@[j].identity_spec().namespace()==table.journal().identity_namespace(),
                forall|j:int|0<=j<i ==> table.contains((#[trigger] self.input_spec()[j]).source().address()),
            decreases inputs.len()-i,
        {
            if !table.contains_identity(inputs[i].identity()) {return false;}i+=1;
        }
        if let Some(environment)=self.declared_environment() {
            let entries=environment.observations();let mut j=0;
            while j<entries.len()
                invariant self.wf(),table.wf(),self.environment().is_some(),*environment==self.environment().unwrap(),
                    environment.wf(),environment.namespace(table.journal().identity_namespace()),entries@==environment.entries(),j<=entries.len(),
                    forall|i:int|0<=i<self.input_spec().len() ==> table.contains((#[trigger] self.input_spec()[i]).source().address()),
                    forall|i:int|0<=i<j && entries@[i].result.is_ok() ==> table.contains((#[trigger] entries@[i]).result->Ok_0.selected.address()),
                decreases entries.len()-j,
            {
                if let Ok(binding)=&entries[j].result {
                    let identity=binding.selected.identity();if !table.contains_identity(&identity) {return false;}
                }j+=1;
            }
        }
        if let Some(environment)=self.owned_observations() {
            let entries=environment.observations();let mut j=0;
            while j<entries.len()
                invariant self.wf(),table.wf(),self.owned_environment().is_some(),*environment==self.owned_environment().unwrap(),
                    environment.wf(),environment.namespace(table.journal().identity_namespace()),entries@==environment.entries(),j<=entries.len(),
                    forall|i:int|0<=i<self.input_spec().len() ==> table.contains((#[trigger] self.input_spec()[i]).source().address()),
                    forall|i:int|0<=i<j && entries@[i].result.is_ok() ==> table.contains((#[trigger] entries@[i]).result->Ok_0.selected.address()),
                decreases entries.len()-j,
            {
                if let Ok(binding)=&entries[j].result {
                    let identity=binding.selected.identity();if !table.contains_identity(&identity) {return false;}
                }j+=1;
            }
        }
        if let Some(environment)=self.published_observations() {
            let entries=environment.observations();let mut j=0;
            while j<entries.len()
                invariant self.wf(),table.wf(),self.publication_environment().is_some(),*environment==self.publication_environment().unwrap(),
                    environment.wf(),environment.namespace(table.journal().identity_namespace()),entries@==environment.entries(),j<=entries.len(),
                    forall|i:int|0<=i<self.input_spec().len() ==> table.contains((#[trigger] self.input_spec()[i]).source().address()),
                    forall|i:int|0<=i<j && entries@[i].result.is_ok() ==> table.contains((#[trigger] entries@[i]).result->Ok_0.selected.address()),
                decreases entries.len()-j,
            {
                if let Ok(binding)=&entries[j].result {
                    let identity=binding.selected.identity();if !table.contains_identity(&identity) {return false;}
                }j+=1;
            }
        }true
    }
    pub fn check_closed_data(&self,schema:&[Reference])->(out:bool)
        requires self.wf(),ensures out==self.closed_data(schema@),
    {
        if !self.function_ref().check_closed_data(schema) {return false;}
        let inputs=self.inputs();let mut i=0;
        while i<inputs.len()
            invariant self.wf(),self.program().closed_data(schema@),inputs@==self.input_spec(),i<=inputs.len(),forall|j:int|0<=j<inputs.len() ==> (#[trigger] inputs@[j]).wf(),
                forall|j:int|0<=j<i ==> match (#[trigger] self.input_spec()[j]).source().before() {
                    crate::reversible_value::managed::semantics::Value::Payload(v)=>v.value.admissible(schema@),_=>true,
                },
            decreases inputs.len()-i,
        {
            if let replay::inputs::Operand::Payload {value,..}=inputs[i].operand() {
                value.representation();if !value.check(schema) {return false;}
            }i+=1;
        }true
    }
}
/// Failures after a real invocation retain its report and cleanup owner.
pub enum Error<E> {Parent {source:usize,expected:Option<usize>,actual:Option<usize>},UnmappedParent {source:usize,parent:usize},Execution(session::Error<Value>),Declarations {source:usize,error:super::objects::Error},After {outcome:Box<session::Outcome<E,Value>>,error:super::objects::Error}}
impl<E:ScalarEffect+Copy> Error<E> {
    pub open spec fn retains_completed<P>(&self,session:&Session<P,E>)->bool {
        match self {
            Error::After {outcome,..}=>outcome.source<session.inner().sources().len()
                && session.inner().ready_to_complete(outcome)
                && outcome.matches(&session.inner().source(outcome.source as int),&session.inner().bank()),
            _=>true,
        }
    }
}
// Failure retains the original owners without allocating or dropping their cleanup state.
#[allow(clippy::large_enum_variant)]
pub enum ServicesError<E> {Capacity,Read {source:usize,entry:usize},Object {source:usize,entry:usize},Publication(session::PublicationFailure<E,Value>)}
#[allow(inconsistent_fields)]
// Failure retains the original owners without allocating or dropping their cleanup state.
#[allow(clippy::large_enum_variant)]
pub enum InitializationFailure<P,E> {
    Data {runtime:ManagedRuntime<P,(),E,Value,()>,sources:Vec<Source<E,Value>>,table:Table,source:usize},
    Runtime {failure:session::InitializationFailure<P,E,Value>,table:Table},
    References {session:session::Session<P,E,Value>,table:Table,error:super::objects::Error},
    Services {session:session::Session<P,E,Value>,projection:Projection,publications:Vec<session::groups::Group<E,Value>>,error:ServicesError<E>},
}
#[allow(dead_code)] // The source allocation is erased provenance of the real publication.
struct Pending {source:Ghost<crate::reversible_value::service_composition::Address>,origin:crate::action_ledger::ActionTicket,entry:replay::services::Preload<Value>}
pub struct Session<P,E> {fibers:fibers::Fibers,aliases:super::slots::Catalog,alias_slots:Ghost<replay::slots::Slots<Value>>,inner:session::Session<P,E,Value>,projection:Projection,publications:Vec<session::groups::Group<E,Value>>}
impl<P,E:ScalarEffect+Copy> Session<P,E> {
    pub closed spec fn inner(&self)->session::Session<P,E,Value> {self.inner}
    pub closed spec fn projection(&self)->Projection {self.projection}
    pub closed spec fn wf(&self)->bool {
        self.fibers.wf() && self.inner.wf() && self.projection.wf(&self.inner.bank()) && self.aliases.wf(&self.inner.bank(),&self.alias_slots@,&self.projection)
            && (forall|i:int|0<=i<self.publications.len() ==> (#[trigger] self.publications@[i]).owner.wf())
            && (forall|i:int|0<=i<self.inner.sources().len() ==> (#[trigger] self.inner.sources()[i]).closed_data(self.projection.source().schema()) && self.inner.sources()[i].within(self.projection.source()))
    }
    pub(crate) proof fn contract_inputs(&self,index:int)
        requires self.wf(),0<=index<self.inner().sources().len(),
        ensures self.projection().wf(&self.inner().bank()),self.inner().bank().wf(),self.inner().source(index).wf(),
            self.inner().source(index).closed_data(self.projection().source().schema()),
    {self.inner.source_facts(index);}
    // Rejection returns all owned runtime state without an additional allocation.
    #[allow(clippy::result_large_err)]
    pub fn new(runtime:ManagedRuntime<P,(),E,Value,()>,sources:Vec<Source<E,Value>>,table:Table,names:batch::Names)->(out:Result<Self,InitializationFailure<P,E>>)
        requires runtime.wf(),table.wf(),batch::supported_namespace(sources@,table.journal()),
        ensures out.is_ok() ==> out->Ok_0.wf(),
    {
        let schema=table.reference_list();let mut i=0;
        while i<sources.len()
            invariant runtime.wf(),table.wf(),schema@==table.schema(),batch::supported_namespace(sources@,table.journal()),i<=sources.len(),
                forall|j:int|0<=j<i ==> (#[trigger] sources@[j]).closed_data(schema@) && sources@[j].within(table),
            decreases sources.len()-i,
        {
            proof {batch::supported_at(sources@,table.journal(),i as int);}
            if !sources[i].check_closed_data(schema.as_slice()) || !sources[i].check_objects(&table) {return Err(InitializationFailure::Data {runtime,sources,table,source:i});}i+=1;
        }
        let mut extra_names=batch::Names {anchor:names.anchor,work:names.work};
        let mut inner=match session::Session::new_unpublished(runtime,table.domain(),sources,names) {Ok(s)=>s,Err(failure)=>return Err(InitializationFailure::Runtime {failure,table})};
        let projection=match Projection::new(table,inner.objects()) {Ok(p)=>p,Err((table,error))=>return Err(InitializationFailure::References {session:inner,table,error})};
        let mut aliases=super::slots::Catalog::new();
        if let Err(error)=seed_aliases(&inner,&projection,&mut aliases) {return Err(InitializationFailure::Services {session:inner,projection,publications:Vec::new(),error});}
        if let Err(error)=install_owned(&mut inner,&projection,&mut aliases) {return Err(InitializationFailure::Services {session:inner,projection,publications:Vec::new(),error});}
        if let Err(error)=install_published(&mut inner,&projection,&mut aliases) {return Err(InitializationFailure::Services {session:inner,projection,publications:Vec::new(),error});}
        let pending=match collect_services(&inner,&projection,&mut aliases) {
            Ok(p)=>p,Err(error)=>return Err(InitializationFailure::Services {session:inner,projection,publications:Vec::new(),error}),
        };
        let ghost alias_slots=inner.slot_catalog();
        let publications=match install_groups(&mut inner,pending.as_slice(),&mut extra_names) {
            Ok(p)=>p,Err((publications,error))=>return Err(InitializationFailure::Services {session:inner,projection,publications,error}),
        };
        Ok(Self {fibers:fibers::Fibers::new(),aliases,alias_slots:Ghost(alias_slots),inner,projection,publications})
    }
    pub fn additional_providers(&self)->(out:&[session::groups::Group<E,Value>])
        requires self.wf(),ensures forall|i:int|0<=i<out.len() ==> (#[trigger] out@[i]).owner.wf(),
    {self.publications.as_slice()}
    pub fn detach_additional_provider(&mut self,position:usize)->(out:Option<session::groups::Group<E,Value>>)
        requires old(self).wf(),ensures final(self).wf(),final(self).projection()==old(self).projection(),final(self).inner()==old(self).inner(),
            out.is_some() ==> out.unwrap().owner.wf(),
    {if position>=self.publications.len() {None} else {Some(self.publications.remove(position))}}
    pub fn objects(&self)->(out:&Projection) ensures *out==self.projection(), {&self.projection}
    /// New arguments use the same exhaustive check as stored program data.
    pub fn accepts(&self,value:&Value)->(out:bool)
        requires self.wf(),value.wf(),
        ensures out==value.admissible(self.projection().source().schema()) && out==value.admissible(self.projection().target().schema()),
    {proof {self.projection.facts(&self.inner.bank());}self.projection.accepts(value)}
    pub fn invoke_next(&mut self,anchor:Port,work_domain:u64)->(out:Result<Option<session::Outcome<E,Value>>,Error<E>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).projection()==old(self).projection(),out.is_err() ==> out->Err_0.retains_completed(final(self)),
            out.is_ok() && out->Ok_0.is_some() ==> out->Ok_0.unwrap().source<final(self).inner().sources().len()
                && out->Ok_0.unwrap().matches(&final(self).inner().source(out->Ok_0.unwrap().source as int),&final(self).inner().bank())
                && final(self).parent_matches(out->Ok_0.unwrap().source as int,out->Ok_0.unwrap().parent()) && (out->Ok_0.unwrap().run.report->Ok_0.result.is_ok() ==> final(self).inner().ready_to_complete(&out->Ok_0.unwrap())) && (out->Ok_0.unwrap().finished.is_some() ==> final(self).inner().ready_to_finish(&out->Ok_0.unwrap())),
    {self.invoke_next_dynamic(anchor,work_domain,None)}
    pub fn invoke_next_dynamic(&mut self,anchor:Port,work_domain:u64,parent:Option<usize>)->(out:Result<Option<session::Outcome<E,Value>>,Error<E>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).projection()==old(self).projection(),out.is_err() ==> out->Err_0.retains_completed(final(self)),
            out.is_ok() && out->Ok_0.is_some() ==> out->Ok_0.unwrap().source<final(self).inner().sources().len()
                && out->Ok_0.unwrap().matches(&final(self).inner().source(out->Ok_0.unwrap().source as int),&final(self).inner().bank())
                && final(self).parent_matches(out->Ok_0.unwrap().source as int,out->Ok_0.unwrap().parent()) && (out->Ok_0.unwrap().run.report->Ok_0.result.is_ok() ==> final(self).inner().ready_to_complete(&out->Ok_0.unwrap())) && (out->Ok_0.unwrap().finished.is_some() ==> final(self).inner().ready_to_finish(&out->Ok_0.unwrap())),
    {
        self.validate_parent(parent)?;
        self.synchronize_before()?;
        let existing=self.existing_next();
        let out=match self.inner.invoke_prepared(anchor,work_domain,parent,None,existing) {Ok(out)=>out,Err(e)=>return Err(Error::Execution(e))};
        if let Some(mut outcome)=out {
            proof {assert(self.parent_matches(outcome.source as int,outcome.parent()));}
            let ghost parent_map=self.fibers.mapping();
            let source=self.inner.source_at(outcome.source).unwrap();
            proof {outcome.report_origins(source,&self.inner.bank());}
            let bound=self.fibers.bind(source.source_origin().id,outcome.run.id,Ghost(source.original().completion()),Ghost(outcome.run.report->Ok_0.completion()));
            proof {reveal(Map::submap_of);assert(self.parent_matches(outcome.source as int,outcome.parent()));}
            if outcome.is_admitted() {
                if !bound {return Err(Error::After {outcome:Box::new(outcome),error:super::objects::Error::Alias});}
                if let Err(error)=self.synchronize_after(outcome.source) {return Err(Error::After {outcome:Box::new(outcome),error});}
                let _finished=self.inner.retry_finish(&mut outcome);
            }Ok(Some(outcome))
        } else {Ok(None)}
    }
    pub fn invoke_next_shared(&mut self,anchor:Port,work_domain:u64,child:&SharedChild)->(out:Result<Option<session::Outcome<E,Value>>,Error<E>>)
        requires old(self).wf(),child.wf(),
        ensures final(self).wf(),final(self).projection()==old(self).projection(),out.is_err() ==> out->Err_0.retains_completed(final(self)),
            out.is_ok() && out->Ok_0.is_some() ==> out->Ok_0.unwrap().source<final(self).inner().sources().len()
                && out->Ok_0.unwrap().matches(&final(self).inner().source(out->Ok_0.unwrap().source as int),&final(self).inner().bank())
                && final(self).parent_matches(out->Ok_0.unwrap().source as int,out->Ok_0.unwrap().parent()) && (out->Ok_0.unwrap().run.report->Ok_0.result.is_ok() ==> final(self).inner().ready_to_complete(&out->Ok_0.unwrap())) && (out->Ok_0.unwrap().finished.is_some() ==> final(self).inner().ready_to_finish(&out->Ok_0.unwrap())),
    {
        self.validate_parent(Some(child.parent_id()))?;
        self.synchronize_before()?;
        let existing=self.existing_next();
        let out=match self.inner.invoke_prepared(anchor,work_domain,Some(child.parent_id()),Some(child),existing) {Ok(out)=>out,Err(e)=>return Err(Error::Execution(e))};
        if let Some(mut outcome)=out {
            proof {assert(self.parent_matches(outcome.source as int,outcome.parent()));}
            let ghost parent_map=self.fibers.mapping();
            let source=self.inner.source_at(outcome.source).unwrap();
            proof {outcome.report_origins(source,&self.inner.bank());}
            let bound=self.fibers.bind(source.source_origin().id,outcome.run.id,Ghost(source.original().completion()),Ghost(outcome.run.report->Ok_0.completion()));
            proof {reveal(Map::submap_of);assert(self.parent_matches(outcome.source as int,outcome.parent()));}
            if outcome.is_admitted() {
                if !bound {return Err(Error::After {outcome:Box::new(outcome),error:super::objects::Error::Alias});}
                if let Err(error)=self.synchronize_after(outcome.source) {return Err(Error::After {outcome:Box::new(outcome),error});}
                let _finished=self.inner.retry_finish(&mut outcome);
            }Ok(Some(outcome))
        } else {Ok(None)}
    }
    /// A parent is transported through authentic prior call identities. An
    /// absent source parent cannot be changed into a target Child implicitly.
    pub closed spec fn parent_matches(&self,index:int,parent:Option<usize>)->bool {
        match self.inner().sources()[index].registration_shape().parent {
            None=>parent.is_none(),Some(id)=>parent.is_some() && self.fibers.mapping().contains_pair(id,parent.unwrap()),
        }
    }
    fn validate_parent(&self,parent:Option<usize>)->(out:Result<(),Error<E>>)
        requires self.wf(),
        ensures out.is_ok() && self.inner().position()<self.inner().order().len() ==>
                self.parent_matches(self.inner().order()[self.inner().position() as int] as int,parent),
            out.is_err() ==> out->Err_0 is Parent || out->Err_0 is UnmappedParent,
    {
        let index=match self.inner.next_source() {Some(i)=>i,None=>return Ok(())};
        let source=self.inner.source_at(index).unwrap();
        proof {self.inner.source_facts(index as int);}
        let expected=match source.parent_id() {
            None=>None,
            Some(id)=>match self.fibers.get(id) {Some(target)=>Some(target),None=>return Err(Error::UnmappedParent {source:index,parent:id})},
        };
        if expected!=parent {return Err(Error::Parent {source:index,expected,actual:parent});}Ok(())
    }
    fn existing_next(&self)->(out:Option<usize>) requires self.wf(),
    {
        match self.inner.next_source() {
            Some(index)=>self.fibers.get(self.inner.source_at(index).unwrap().source_origin().id),None=>None,
        }
    }
    fn synchronize_before(&mut self)->(out:Result<(),Error<E>>)
        requires old(self).wf(),ensures final(self).wf(),final(self).fibers==old(self).fibers,final(self).projection()==old(self).projection(),final(self).inner()==old(self).inner(),out.is_err() ==> out->Err_0 is Declarations,
    {
        let index=match self.inner.next_source() {Some(i)=>i,None=>return Ok(())};
        let source=self.inner.source_at(index).unwrap();
        if let Some(environment)=source.declared_environment() {
            if let Err(error)=self.aliases.synchronize_environment(self.inner.objects(),&self.projection,environment,self.alias_slots) {return Err(Error::Declarations {source:index,error});}
        }
        if let Some(environment)=source.owned_observations() {
            if let Err(error)=self.aliases.synchronize_environment(self.inner.objects(),&self.projection,environment,self.alias_slots) {return Err(Error::Declarations {source:index,error});}
        }Ok(())
    }
    fn synchronize_after(&mut self,index:usize)->(out:Result<(),super::objects::Error>)
        requires old(self).wf(),index<old(self).inner().sources().len(),
        ensures final(self).wf(),final(self).fibers==old(self).fibers,final(self).projection()==old(self).projection(),final(self).inner()==old(self).inner(),
    {
        let source=self.inner.source_at(index).unwrap();
        if let Some(environment)=source.published_observations() {self.aliases.synchronize_environment(self.inner.objects(),&self.projection,environment,self.alias_slots)?;}
        Ok(())
    }
    pub fn retry_finish(&mut self,outcome:&mut session::Outcome<E,Value>)->(out:Result<(),crate::Error>)
        requires old(self).wf(),old(self).inner().ready_to_complete(old(outcome)),
        ensures final(self).wf(),final(self).projection()==old(self).projection(),final(self).inner().ready_to_complete(final(outcome)),
            final(outcome).finished.is_some() ==> final(self).inner().ready_to_finish(final(outcome)),
    {
        proof {self.inner.completion_facts(outcome);}
        if self.synchronize_after(outcome.source).is_err() {return Err(crate::Error::InvalidState);}
        if !matches!(outcome.finished,Some(Ok(()))) {self.inner.retry_finish(outcome)?;}
        Ok(())
    }
    pub fn resume_cleanup<C>(&mut self,id:usize,owner:&RecordedExecution<C,(),(),(),Value,(),()>)->(out:Result<crate::action_ledger::ActionTicket,crate::Error>)
        requires old(self).wf(),owner.wf(),ensures final(self).wf(),
    {self.inner.resume_cleanup(id,owner)}
    pub fn retire_child(&mut self,child:&SharedChild)->(out:crate::lifecycle_state::native::runtime::child_recovery::Observation)
        requires old(self).wf(),child.wf(),ensures out.0.wf(child),out.1@.is_some()==out.0.result.is_ok(),
            out.1@.is_some() ==> out.1@.unwrap().belongs_to(child),
            final(self).wf(),
    {self.inner.retire_child(child)}
    pub fn providers(&self)->(out:&[session::groups::Group<E,Value>])
        requires self.wf(),ensures forall|i:int|0<=i<out.len() ==> (#[trigger] out@[i]).owner.wf(),
    {self.publications.as_slice()}
    pub fn planned_provider_count(&self)->usize {self.inner.plan_count()}
    pub fn planned_provider_origin(&self,index:usize)->Option<crate::action_ledger::ActionTicket> {self.inner.plan_origin(index)}
    pub fn detach_provider(&mut self,position:usize)->(out:Option<session::groups::Group<E,Value>>)
        requires old(self).wf(),ensures final(self).wf(),out.is_some() ==> out.unwrap().owner.wf(),
    {self.detach_additional_provider(position)}
    /// Reuse the original target registration after actual Unload. The plan
    /// identifies an authentic source generation and all of its observed names.
    // Rejection returns all owned runtime state without an additional allocation.
    #[allow(clippy::result_large_err)]
    pub fn republish(&mut self,id:usize,plan:usize,work_domain:u64)->(out:Result<(),session::PublicationFailure<E,Value>>)
        requires old(self).wf(),ensures final(self).wf(),
    {
        let publication=self.inner.publish_plan(plan,Port {key:0,realm:0},work_domain,Some(id))?;
        let ghost prior=self.publications@;self.publications.push(publication);
        proof {assert forall|i:int|0<=i<self.publications.len() implies (#[trigger] self.publications@[i]).owner.wf() by {if i<prior.len() {assert(self.publications@[i]==prior[i]);}}
            assert(self.inner.wf());assert(self.projection.wf(&self.inner.bank()));
            assert forall|i:int|0<=i<self.inner.sources().len() implies (#[trigger] self.inner.sources()[i]).closed_data(self.projection.source().schema()) && self.inner.sources()[i].within(self.projection.source()) by {
                assert(self.inner.sources()==old(self).inner.sources());assert(self.projection==old(self).projection);
                assert((old(self).inner.sources()[i]).closed_data(old(self).projection.source().schema()));
                assert((old(self).inner.sources()[i]).within(old(self).projection.source()));
            }
        }Ok(())
    }
    // Rejection returns all owned runtime state without an additional allocation.
    #[allow(clippy::result_large_err)]
    pub fn activate_provider(&mut self,plan:usize,anchor:Port,work_domain:u64)->(out:Result<(),session::PublicationFailure<E,Value>>)
        requires old(self).wf(),ensures final(self).wf(),
    {let publication=self.inner.publish_plan(plan,anchor,work_domain,None)?;let ghost prior=self.publications@;self.publications.push(publication);
        proof {assert forall|i:int|0<=i<self.publications.len() implies (#[trigger] self.publications@[i]).owner.wf() by {if i<prior.len() {assert(self.publications@[i]==prior[i]);}}
            assert(self.inner.wf());assert(self.projection.wf(&self.inner.bank()));
            assert forall|i:int|0<=i<self.inner.sources().len() implies (#[trigger] self.inner.sources()[i]).closed_data(self.projection.source().schema()) && self.inner.sources()[i].within(self.projection.source()) by {
                assert(self.inner.sources()==old(self).inner.sources());assert(self.projection==old(self).projection);
                assert((old(self).inner.sources()[i]).closed_data(old(self).projection.source().schema()));
                assert((old(self).inner.sources()[i]).within(old(self).projection.source()));
            }
        }Ok(())}
    pub fn remove_registration(&mut self,id:usize)->(out:Result<(),crate::Error>)
        requires old(self).wf(),ensures final(self).wf(),
    {self.inner.remove_registration(id)}
    pub fn begin_cleanup<C>(&mut self,id:usize,owner:&mut RecordedExecution<C,(),(),(),Value,(),()>,retiring:bool)->(out:Result<crate::action_ledger::ActionTicket,crate::Error>)
        requires old(self).wf(),old(owner).wf(),ensures final(self).wf(),final(owner).wf(),final(owner).same_inverse_word(old(owner)),old(owner).conserved() ==> final(owner).conserved(),
    {self.inner.begin_cleanup(id,owner,retiring)}
    // The type records the native owner and each cleanup payload category.
    #[allow(clippy::type_complexity)]
    pub fn dispatch_cleanup<C>(&self,owner:&mut RecordedExecution<C,(),(),(),Value,(),()>,group:usize)->(out:Option<crate::cleanup_groups::payload::DispatchResult<(),(),std::sync::Arc<crate::reversible_value::managed::Slot<Value,()>>,Value,()>>)
        requires self.wf(),old(owner).wf(),ensures final(owner).wf(),final(owner).same_inverse_word(old(owner)),old(owner).conserved() ==> final(owner).conserved(),
    {self.inner.dispatch_cleanup(owner,group)}
    pub fn fail_cleanup<C>(&mut self,id:usize,owner:&RecordedExecution<C,(),(),(),Value,(),()>)->(out:Result<(),crate::Error>)
        requires old(self).wf(),owner.wf(),ensures final(self).wf(),
    {self.inner.fail_cleanup(id,owner)}
    pub fn retry_cleanup<C>(&mut self,id:usize,owner:&mut RecordedExecution<C,(),(),(),Value,(),()>)->(out:Result<crate::action_ledger::ActionTicket,crate::Error>)
        requires old(self).wf(),old(owner).wf(),ensures final(self).wf(),final(owner).wf(),final(owner).same_inverse_word(old(owner)),old(owner).conserved() ==> final(owner).conserved(),
    {self.inner.retry_cleanup(id,owner)}
    pub fn release<C>(&mut self,id:usize,owner:&mut RecordedExecution<C,(),(),(),Value,(),()>)->(out:Result<crate::reversible_value::managed::interleaving::history::lifecycle::native::ReleaseOutcome<(),(),Value,(),()>,crate::Error>)
        requires old(self).wf(),old(owner).wf(),ensures final(self).wf(),final(owner).wf(),final(owner).same_inverse_word(old(owner)),old(owner).conserved() ==> final(owner).conserved(),
    {self.inner.release(id,owner)}
}
}

verus! {
/// Choose each declaration slot at its first authentic observation, independent
/// of the caller's Vec order and whether the first use is an own publication.
// Rejection returns all owned runtime state without an additional allocation.
#[allow(clippy::result_large_err)]
fn seed_aliases<P,E:ScalarEffect+Copy>(inner:&session::Session<P,E,Value>,projection:&Projection,aliases:&mut super::slots::Catalog)->(out:Result<(),ServicesError<E>>)
    requires inner.wf(),projection.wf(&inner.bank()),old(aliases).wf(&inner.bank(),&inner.slot_catalog(),projection),
    ensures final(aliases).wf(&inner.bank(),&inner.slot_catalog(),projection),
{
    let mut n=0;
    while n<inner.source_count()
        invariant inner.wf(),projection.wf(&inner.bank()),aliases.wf(&inner.bank(),&inner.slot_catalog(),projection),n<=inner.sources().len(),
        decreases inner.sources().len()-n,
    {
        let index=inner.ordered_source(n).unwrap();let source=inner.source_at(index).unwrap();
        if let Some(e)=source.declared_environment() {seed_environment(inner,projection,aliases,e,index)?;}
        if let Some(e)=source.owned_observations() {seed_environment(inner,projection,aliases,e,index)?;}
        if let Some(e)=source.published_observations() {seed_environment(inner,projection,aliases,e,index)?;}
        n+=1;
    }Ok(())
}
// Rejection returns all owned runtime state without an additional allocation.
#[allow(clippy::result_large_err)]
fn seed_environment<P,E:ScalarEffect+Copy>(inner:&session::Session<P,E,Value>,projection:&Projection,aliases:&mut super::slots::Catalog,environment:&replay::environment::Environment<Value>,index:usize)->(out:Result<(),ServicesError<E>>)
    requires inner.wf(),projection.wf(&inner.bank()),old(aliases).wf(&inner.bank(),&inner.slot_catalog(),projection),environment.wf(),environment.namespace(inner.bank().namespace()),
    ensures final(aliases).wf(&inner.bank(),&inner.slot_catalog(),projection),
{
    proof {projection.facts(&inner.bank());}
    let entries=environment.observations();let mut j=0;
    while j<entries.len()
        invariant inner.wf(),projection.wf(&inner.bank()),aliases.wf(&inner.bank(),&inner.slot_catalog(),projection),environment.wf(),environment.namespace(inner.bank().namespace()),entries@==environment.entries(),j<=entries.len(),
            projection.source().journal().identity_namespace()==inner.bank().namespace(),
        decreases entries.len()-j,
    {
        if let Ok(binding)=&entries[j].result {
            let identity=binding.selected.identity();
            let fallback=match projection.service(inner.objects(),&identity) {Some(s)=>s,None=>return Err(ServicesError::Object {source:index,entry:j})};
            let candidate=inner.preload(entries[j].port,binding.origin,&binding.selected,fallback.clone());
            let ghost cell;proof {inner.slot_facts();cell=projection.preload_cell(&inner.bank(),&inner.slot_catalog(),candidate,fallback,binding.selected.address());}
            if aliases.select(inner.objects(),inner.slot_catalog_exec(),projection,&binding.selected,candidate,Ghost(cell)).is_err() {return Err(ServicesError::Object {source:index,entry:j});}
        }j+=1;
    }Ok(())
}

// Rejection returns all owned runtime state without an additional allocation.
#[allow(clippy::result_large_err)]
fn collect_services<P,E:ScalarEffect+Copy>(inner:&session::Session<P,E,Value>,projection:&Projection,aliases:&mut super::slots::Catalog)->(out:Result<Vec<Pending>,ServicesError<E>>)
    requires inner.wf(),projection.wf(&inner.bank()),old(aliases).wf(&inner.bank(),&inner.slot_catalog(),projection),
    ensures final(aliases).wf(&inner.bank(),&inner.slot_catalog(),projection),out.is_ok() ==> forall|i:int|0<=i<out->Ok_0.len() ==> {
        let p=#[trigger] out->Ok_0@[i];
        &&& inner.accepts_preload(p.entry) && projection.mapping().contains_pair(p.source@,super::objects::service_address(p.entry.service))
    },
{
    let mut pending:Vec<Pending>=Vec::new();let mut n=0;
    proof {projection.facts(&inner.bank());}
    while n<inner.source_count()
        invariant aliases.wf(&inner.bank(),&inner.slot_catalog(),projection),inner.wf(),projection.wf(&inner.bank()),n<=inner.sources().len(),
            projection.source().journal().identity_namespace()==inner.bank().namespace(),
            forall|j:int|0<=j<pending.len() ==> inner.accepts_preload((#[trigger] pending@[j]).entry) && projection.mapping().contains_pair(pending@[j].source@,super::objects::service_address(pending@[j].entry.service)),
        decreases inner.sources().len()-n,
    {
        let i=inner.ordered_source(n).unwrap();let source=inner.source_at(i).unwrap();
        if let Some(environment)=source.declared_environment() {
            let entries=environment.observations();let mut j=0;
            while j<entries.len()
                invariant aliases.wf(&inner.bank(),&inner.slot_catalog(),projection),inner.wf(),i<inner.sources().len(),projection.wf(&inner.bank()),source.wf(),environment.wf(),
                    projection.source().journal().identity_namespace()==inner.bank().namespace(),
                    environment.namespace(inner.bank().namespace()),entries@==environment.entries(),j<=entries.len(),
                    forall|k:int|0<=k<pending.len() ==> inner.accepts_preload((#[trigger] pending@[k]).entry) && projection.mapping().contains_pair(pending@[k].source@,super::objects::service_address(pending@[k].entry.service)),
                decreases entries.len()-j,
            {
                if let Ok(binding)=&entries[j].result {
                    let port=entries[j].port;let mut found=inner.provided_by_call(i,port);let mut k=0;
                    while k<pending.len() invariant k<=pending.len(),decreases pending.len()-k,
                    {if pending[k].entry.port==port && pending[k].origin==binding.origin {found=true;}k+=1;}
                    let identity=binding.selected.identity();
                    let fallback=match projection.service(inner.objects(),&identity) {Some(s)=>s,None=>return Err(ServicesError::Object {source:i,entry:j})};
                    let candidate=inner.preload(port,binding.origin,&binding.selected,fallback.clone());
                    let ghost cell;proof {inner.slot_facts();cell=projection.preload_cell(&inner.bank(),&inner.slot_catalog(),candidate,fallback,binding.selected.address());}
                    let (chosen,Ghost(cell))=match aliases.select(inner.objects(),inner.slot_catalog_exec(),projection,&binding.selected,candidate,Ghost(cell)) {Ok(p)=>p,Err(_)=>return Err(ServicesError::Object {source:i,entry:j})};
                    if !found {pending.push(Pending {entry:chosen,origin:binding.origin,source:Ghost(cell)});}
                }j+=1;
            }
        }n+=1;
    }Ok(pending)
}

// Rejection returns all owned runtime state without an additional allocation. The type records the native owner and each cleanup payload category.
#[allow(clippy::result_large_err,clippy::type_complexity)]
fn install_groups<P,E:ScalarEffect+Copy>(inner:&mut session::Session<P,E,Value>,pending:&[Pending],names:&mut batch::Names)->(out:Result<Vec<session::groups::Group<E,Value>>,(Vec<session::groups::Group<E,Value>>,ServicesError<E>)>)
    requires old(inner).wf(),forall|i:int|0<=i<pending.len() ==> #[trigger] old(inner).accepts_preload(pending@[i].entry),
    ensures final(inner).wf(),final(inner).sources()==old(inner).sources(),final(inner).bank()==old(inner).bank(),
        final(inner).position()==old(inner).position(),final(inner).order()==old(inner).order(),final(inner).slot_catalog()==old(inner).slot_catalog(),
        out.is_ok() ==> forall|i:int|0<=i<out->Ok_0.len() ==> (#[trigger] out->Ok_0@[i]).owner.wf(),
{
    let mut publications:Vec<session::groups::Group<E,Value>>=Vec::new();let mut i=0;
    while i<pending.len()
        invariant inner.wf(),inner.sources()==old(inner).sources(),inner.bank()==old(inner).bank(),inner.slot_catalog()==old(inner).slot_catalog(),
            inner.position()==old(inner).position(),inner.order()==old(inner).order(),i<=pending.len(),
            forall|j:int|0<=j<publications.len() ==> (#[trigger] publications@[j]).owner.wf(),
            forall|j:int|0<=j<pending.len() ==> #[trigger] inner.accepts_preload(pending@[j].entry),
        decreases pending.len()-i,
    {
        let origin=pending[i].origin;let mut seen=false;let mut j=0;
        while j<i invariant j<=i,i<pending.len(),decreases i-j,
        {if pending[j].origin==origin {seen=true;}j+=1;}
        if seen {i+=1;continue;}
        let mut entries:Vec<replay::services::Preload<Value>>=Vec::new();let mut j=0;
        while j<pending.len()
            invariant inner.wf(),j<=pending.len(),forall|k:int|0<=k<pending.len() ==> #[trigger] inner.accepts_preload(pending@[k].entry),
                forall|k:int|0<=k<entries.len() ==> #[trigger] inner.accepts_preload(entries@[k]),
            decreases pending.len()-j,
        {if pending[j].origin==origin {entries.push(pending[j].entry.duplicate());}j+=1;}
        let mut active=true;let mut j=0;
        while j<publications.len() invariant j<=publications.len(),decreases publications.len()-j,
        {
            if publications[j].source_origin.id==origin.id {active=false;}
            let mut a=0;
            while a<publications[j].services.len() invariant j<publications.len(),a<=publications@[j as int].services.len(),decreases publications@[j as int].services.len()-a,
            {
                let mut b=0;
                while b<entries.len() invariant j<publications.len(),a<publications@[j as int].services.len(),b<=entries.len(),decreases entries.len()-b,
                {if publications[j].services[a].port==entries[b].port {active=false;}b+=1;}a+=1;
            }j+=1;
        }
        let ghost prior=*inner;
        let plan=inner.add_plan(origin,entries);
        if active {
            let (anchor,work)=match names.take() {Some(v)=>v,None=>return Err((publications,ServicesError::Capacity))};
            let publication=match inner.publish_plan(plan,anchor,work,None) {Ok(p)=>p,Err(error)=>return Err((publications,ServicesError::Publication(error)))};
            publications.push(publication);
        }
        proof {assert forall|j:int|0<=j<pending.len() implies #[trigger] inner.accepts_preload(pending@[j].entry) by {assert(prior.accepts_preload(pending@[j].entry));}}
        i+=1;
    }Ok(publications)
}
}

verus! {
// Rejection returns all owned runtime state without an additional allocation.
#[allow(clippy::result_large_err)]
fn install_owned<P,E:ScalarEffect+Copy>(inner:&mut session::Session<P,E,Value>,projection:&Projection,aliases:&mut super::slots::Catalog)->(out:Result<(),ServicesError<E>>)
    requires old(inner).wf(),projection.wf(&old(inner).bank()),old(aliases).wf(&old(inner).bank(),&old(inner).slot_catalog(),projection),
    ensures final(aliases).wf(&final(inner).bank(),&final(inner).slot_catalog(),projection),final(inner).wf(),final(inner).sources()==old(inner).sources(),final(inner).bank()==old(inner).bank(),
        final(inner).position()==old(inner).position(),final(inner).order()==old(inner).order(),
{
    proof {projection.facts(&inner.bank());}
    let mut i=0;
    while i<inner.source_count()
        invariant aliases.wf(&inner.bank(),&inner.slot_catalog(),projection),inner.wf(),projection.wf(&inner.bank()),inner.sources()==old(inner).sources(),inner.bank()==old(inner).bank(),inner.position()==old(inner).position(),inner.order()==old(inner).order(),i<=inner.sources().len(),
            projection.source().journal().identity_namespace()==inner.bank().namespace(),
        decreases inner.sources().len()-i,
    {
        let mut preloads:Vec<replay::services::Preload<Value>>=Vec::new();
        let source=inner.source_at(i).unwrap();
        if let Some(environment)=source.owned_observations() {
            let entries=environment.observations();let mut j=0;
            while j<entries.len()
                invariant aliases.wf(&inner.bank(),&inner.slot_catalog(),projection),inner.wf(),inner.sources()==old(inner).sources(),inner.bank()==old(inner).bank(),inner.position()==old(inner).position(),inner.order()==old(inner).order(),projection.wf(&inner.bank()),source.wf(),environment.wf(),environment.namespace(inner.bank().namespace()),entries@==environment.entries(),j<=entries.len(),
                    projection.source().journal().identity_namespace()==inner.bank().namespace(),
                    forall|k:int|0<=k<preloads.len() ==> #[trigger] inner.accepts_preload(preloads@[k]),
                decreases entries.len()-j,
            {
                if let Ok(binding)=&entries[j].result {
                    let identity=binding.selected.identity();
                    let fallback=match projection.service(inner.objects(),&identity) {Some(s)=>s,None=>return Err(ServicesError::Object {source:i,entry:j})};
                    let candidate=inner.preload(entries[j].port,binding.origin,&binding.selected,fallback.clone());
                    let ghost cell;proof {inner.slot_facts();cell=projection.preload_cell(&inner.bank(),&inner.slot_catalog(),candidate,fallback,binding.selected.address());}
                    let (chosen,Ghost(_cell))=match aliases.select(inner.objects(),inner.slot_catalog_exec(),projection,&binding.selected,candidate,Ghost(cell)) {Ok(p)=>p,Err(_)=>return Err(ServicesError::Object {source:i,entry:j})};
                    preloads.push(chosen);
                }j+=1;
            }
        }
        inner.install_preloads(i,preloads);i+=1;
    }Ok(())
}

// Rejection returns all owned runtime state without an additional allocation.
#[allow(clippy::result_large_err)]
fn install_published<P,E:ScalarEffect+Copy>(inner:&mut session::Session<P,E,Value>,projection:&Projection,aliases:&mut super::slots::Catalog)->(out:Result<(),ServicesError<E>>)
    requires old(inner).wf(),projection.wf(&old(inner).bank()),old(aliases).wf(&old(inner).bank(),&old(inner).slot_catalog(),projection),
    ensures final(aliases).wf(&final(inner).bank(),&final(inner).slot_catalog(),projection),final(inner).wf(),final(inner).sources()==old(inner).sources(),final(inner).bank()==old(inner).bank(),
        final(inner).position()==old(inner).position(),final(inner).order()==old(inner).order(),
{
    proof {projection.facts(&inner.bank());}
    let mut i=0;
    while i<inner.source_count()
        invariant aliases.wf(&inner.bank(),&inner.slot_catalog(),projection),inner.wf(),projection.wf(&inner.bank()),inner.sources()==old(inner).sources(),inner.bank()==old(inner).bank(),inner.position()==old(inner).position(),inner.order()==old(inner).order(),i<=inner.sources().len(),
            projection.source().journal().identity_namespace()==inner.bank().namespace(),
        decreases inner.sources().len()-i,
    {
        let mut preloads:Vec<replay::services::Preload<Value>>=Vec::new();
        let source=inner.source_at(i).unwrap();
        if let Some(environment)=source.published_observations() {
            let entries=environment.observations();let mut j=0;
            while j<entries.len()
                invariant aliases.wf(&inner.bank(),&inner.slot_catalog(),projection),inner.wf(),inner.sources()==old(inner).sources(),inner.bank()==old(inner).bank(),inner.position()==old(inner).position(),inner.order()==old(inner).order(),projection.wf(&inner.bank()),source.wf(),environment.wf(),environment.namespace(inner.bank().namespace()),entries@==environment.entries(),j<=entries.len(),
                    projection.source().journal().identity_namespace()==inner.bank().namespace(),
                    forall|k:int|0<=k<preloads.len() ==> #[trigger] inner.accepts_preload(preloads@[k]),
                decreases entries.len()-j,
            {
                if let Ok(binding)=&entries[j].result {
                    if source.provided_before_root(entries[j].port) {j+=1;continue;}
                    let identity=binding.selected.identity();
                    let fallback=match projection.service(inner.objects(),&identity) {Some(s)=>s,None=>return Err(ServicesError::Object {source:i,entry:j})};
                    let candidate=inner.preload(entries[j].port,binding.origin,&binding.selected,fallback.clone());
                    let ghost cell;proof {inner.slot_facts();cell=projection.preload_cell(&inner.bank(),&inner.slot_catalog(),candidate,fallback,binding.selected.address());}
                    let (chosen,Ghost(_cell))=match aliases.select(inner.objects(),inner.slot_catalog_exec(),projection,&binding.selected,candidate,Ghost(cell)) {Ok(p)=>p,Err(_)=>return Err(ServicesError::Object {source:i,entry:j})};
                    preloads.push(chosen);
                }j+=1;
            }
        }
        inner.install_postloads(i,preloads);i+=1;
    }Ok(())
}
}
