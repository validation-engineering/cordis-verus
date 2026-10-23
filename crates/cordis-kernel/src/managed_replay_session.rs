//! A persistent owner of the actual target runtime, publications and replay
//! history. Calls can be separated by the original native cleanup protocol;
//! each re-entry checks actual held storage before running the source function.
use super::super::interleaving::history::lifecycle::RecordedExecution;
#[cfg(verus_keep_ghost)]
use super::super::protected_mixed as held;
#[cfg(verus_keep_ghost)]
use super::typed_correspondence as relation;
use super::typed_correspondence::epochs;
use super::{
    archive,
    bank::Bank,
    batch::{self, Names, Provider},
    mixed, protected, Destination, ManagedRuntime, Source,
};
use crate::lifecycle_state::registration::shared_child::{ChildDispatch, SharedChild};
use crate::reversible_value::{effect::ScalarEffect, joint};
use crate::{Error as NativeError, Port};
#[path = "managed_replay_publications.rs"]
pub mod groups;
use super::super::{Function, Owner};
use super::services::{self, Preload};
use crate::action_ledger::ActionTicket;
use groups::{Group, Plan};
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub struct InitializationFailure<P,E,T:?Sized> {
    pub runtime:ManagedRuntime<P,(),E,T,()>,pub sources:Vec<Source<E,T>>,pub prepared:Option<batch::Batch<E,T>>,pub error:InitializationError,
}
#[derive(Debug)]
pub enum InitializationError {Preflight(batch::PreflightError),Preparation,Protection(mixed::Error)}
pub type ChildWork=ChildDispatch<(),()>;
pub type CallOwner<T>=RecordedExecution<ChildWork,(),(),(),T,(),()>;
pub enum Error<T:?Sized> {Slot(super::slots::Error),Uncontrolled {source:usize},Incomplete {source:usize},Protection(mixed::Error),History(archive::Error),Start(protected::Start<T,ChildWork>)}
pub struct Outcome<E,T:?Sized> {pub source:usize,pub provided:usize,pub run:super::TargetRun<ChildWork,(),(),(),T,(),(),E>,pub finished:Option<Result<(),NativeError>>,pub correspondence:Ghost<Option<epochs::Certificate<T>>>,pub typed_bank:Ghost<Bank<T>>,pub history:Ghost<Option<archive::projection::Names<T>>>}
impl<E:ScalarEffect,T:?Sized> Outcome<E,T> {
    pub open spec fn parent(&self)->Option<usize> {
        self.run.report->Ok_0.completion().event().after->Recipes_state.entries[self.run.id].parent
    }
    pub fn is_admitted(&self)->(out:bool)
        ensures out==(self.run.report.is_ok() && self.run.report->Ok_0.result.is_ok()),
    {match &self.run.report {Ok(report)=>report.result.is_ok(),Err(_)=>false}}
    pub closed spec fn matches(&self,source:&Source<E,T>,bank:&Bank<T>)->bool {
        self.run.from_source(source) && self.run.report.is_ok()
            && (self.run.report->Ok_0.result.is_ok() ==> source.original().result.is_ok() && source.original().result->Ok_0.failure.is_none() && self.run.report->Ok_0.result->Ok_0.failure.is_none()
                && held::same(self.run.report->Ok_0.result->Ok_0.steps@,source.original().result->Ok_0.steps@)
                && relation::allocations(bank,source.original().result->Ok_0.steps@,self.run.report->Ok_0.result->Ok_0.steps@)
                && self.correspondence@.is_some() && self.correspondence@.unwrap().wf()
                && self.correspondence@.unwrap().source==held::payloads(source.original().result->Ok_0.steps@)
                && self.correspondence@.unwrap().target==held::payloads(self.run.report->Ok_0.result->Ok_0.steps@)
                && self.history@.is_some() && self.history@.unwrap().wf()
                && (forall|i:int|0<=i<self.typed_bank@.len_spec() ==> self.history@.unwrap().at(self.typed_bank@.address(i))==self.correspondence@.unwrap().after_names[i])
                && self.typed_bank@.wf() && self.typed_bank@.len_spec()==self.correspondence@.unwrap().after_names.len()
                && protected::mapped(&self.typed_bank@,self.correspondence@.unwrap().routes,self.correspondence@.unwrap().source))
    }
    pub(crate) proof fn report_origins(&self,source:&Source<E,T>,bank:&Bank<T>)
        requires source.wf(),self.matches(source,bank),
        ensures source.original().completed(),self.run.report.is_ok(),self.run.report->Ok_0.completed(),self.run.report->Ok_0.origin.id==self.run.id,
    {source.facts();reveal(super::TargetRun::from_source);}
    pub proof fn completion_frame(&self,prior:&Self,source:&Source<E,T>,bank:&Bank<T>)
        requires prior.matches(source,bank),self.run.owner.wf(),self.run.id==prior.run.id,self.run.report==prior.run.report,self.run.inputs==prior.run.inputs,self.run.offset==prior.run.offset,
            self.run.owner.baseline()==prior.run.owner.baseline(),self.run.owner.recovery_boundary()==prior.run.owner.recovery_boundary(),
            self.correspondence==prior.correspondence,self.typed_bank==prior.typed_bank,self.history==prior.history,
        ensures self.matches(source,bank),
    {reveal(super::TargetRun::from_source);}
    pub(crate) proof fn facts(&self,source:&Source<E,T>,bank:&Bank<T>)
        requires self.matches(source,bank),self.run.report.is_ok(),self.run.report->Ok_0.result.is_ok(),
        ensures source.original().result.is_ok(),source.original().result->Ok_0.failure.is_none(),self.run.from_source(source),held::same(self.run.report->Ok_0.result->Ok_0.steps@,source.original().result->Ok_0.steps@),
            relation::allocations(bank,source.original().result->Ok_0.steps@,self.run.report->Ok_0.result->Ok_0.steps@),
            self.correspondence@.is_some(),self.correspondence@.unwrap().wf(),
            self.correspondence@.unwrap().source==held::payloads(source.original().result->Ok_0.steps@),
            self.correspondence@.unwrap().target==held::payloads(self.run.report->Ok_0.result->Ok_0.steps@),
            self.typed_bank@.wf(),self.typed_bank@.len_spec()==self.correspondence@.unwrap().after_names.len(),self.history@.is_some(),self.history@.unwrap().wf(),
            forall|i:int|0<=i<self.typed_bank@.len_spec() ==> self.history@.unwrap().at(self.typed_bank@.address(i))==self.correspondence@.unwrap().after_names[i],
            protected::mapped(&self.typed_bank@,self.correspondence@.unwrap().routes,self.correspondence@.unwrap().source),
    {}
}
// Failure retains the original owners without allocating or dropping their cleanup state.
#[allow(clippy::large_enum_variant)]
pub enum PublicationFailure<E,T:?Sized> {Before(NativeError),After {id:usize,owner:batch::ProviderOwner<T>,report:Result<super::RegisteredReport<E,T>,super::AdmissionError>,error:NativeError}}
/// A real provider outside the operand bank (for example an unvisited service).
/// Its cleanup owner is returned to the host just like every other publication.
pub struct Publication<E,T:?Sized> {
    pub id:usize,pub port:Port,pub service:std::sync::Arc<super::super::Slot<T,()>>,
    pub owner:batch::ProviderOwner<T>,pub report:Result<super::RegisteredReport<E,T>,super::AdmissionError>,
}
pub struct Session<P,E,T:?Sized> {
    runtime:ManagedRuntime<P,(),E,T,()>,source_journal:joint::Journal,sources:Vec<Source<E,T>>,order:Vec<usize>,next:usize,
    bank:Bank<T>,providers:Vec<Provider<E,T>>,routes:Vec<super::services::Service<T>>,preloads:Vec<Vec<super::services::Preload<T>>>,postloads:Vec<Vec<super::services::Preload<T>>>,plans:Vec<groups::Plan<T>>,slots:super::slots::Slots<T>,view:Bank<T>,archive:archive::Archive<T>,
}
impl<P,E:ScalarEffect+Copy,T:?Sized> Session<P,E,T> {
    pub(crate) fn slot_catalog_exec(&self)->(out:&super::slots::Slots<T>) ensures *out==self.slot_catalog(), {&self.slots}
    pub closed spec fn slot_catalog(&self)->super::slots::Slots<T> {self.slots}
    pub open spec fn accepts_preload(&self,p:super::services::Preload<T>)->bool {p.wf(&self.bank(),&self.slot_catalog())}
    pub fn provided_by_call(&self,call:usize,port:Port)->(out:bool)
        requires self.wf(),call<self.sources().len(),
    {proof {batch::supported_at(self.sources@,self.source_journal,call as int);assert forall|i:int|0<=i<self.sources.len() implies (#[trigger] self.sources@[i]).wf() by {batch::supported_at(self.sources@,self.source_journal,i);}}batch::provided_for_source(self.sources.as_slice(),&self.sources[call],port)}
    pub closed spec fn publications(&self)->Map<usize,crate::lifecycle_state::services::NativePublication<super::super::Slot<T,()>>> {self.runtime.publications().entries()}
    pub closed spec fn sources(&self)->Seq<Source<E,T>> {self.sources@}
    pub closed spec fn source(&self,index:int)->Source<E,T> {self.sources@[index]}
    pub closed spec fn provider_spec(&self)->Seq<Provider<E,T>> {self.providers@}
    pub closed spec fn bank(&self)->Bank<T> {self.bank}
    pub closed spec fn position(&self)->usize {self.next}
    pub closed spec fn order(&self)->Seq<usize> {self.order@}
    pub closed spec fn historical_names(&self)->archive::projection::Names<T> {archive::projection::Names {bank:self.view,heads:self.archive.names()}}
    pub closed spec fn same_history_snapshot(&self,prior:&Self)->bool {self.archive==prior.archive && self.view==prior.view}
    pub open spec fn history_extends(&self,prior:&Self)->bool {
        self.historical_names().bank==prior.historical_names().bank && super::typed_correspondence::extends(self.historical_names().heads,prior.historical_names().heads)
    }
    pub proof fn history_facts(&self) requires self.wf(),ensures self.historical_names().wf(), {let names=self.archive.names_certificate(&self.view);}
    pub closed spec fn ready_to_complete(&self,outcome:&Outcome<E,T>)->bool {
        outcome.source<self.sources.len() && outcome.run.owner.wf() && outcome.run.owner.core().value_state().is_some()
            && super::services::preloaded(self.preloads@[outcome.source as int]@,outcome.run.owner.core().value_state().unwrap())
            && (outcome.finished.is_some() ==> self.ready_to_finish(outcome))
            && outcome.provided<=self.postloads@[outcome.source as int].len()
            && super::services::preloaded(self.postloads@[outcome.source as int]@.take(outcome.provided as int),outcome.run.owner.core().value_state().unwrap())
    }
    pub proof fn completion_facts(&self,outcome:&Outcome<E,T>)
        requires self.wf(),self.ready_to_complete(outcome),
        ensures outcome.source<self.sources().len(),outcome.finished.is_some() ==> self.ready_to_finish(outcome),
    {}
    pub closed spec fn ready_to_finish(&self,outcome:&Outcome<E,T>)->bool {
        outcome.source<self.sources.len() && outcome.run.owner.wf() && outcome.run.owner.core().value_state().is_some()
            && super::services::preloaded(self.preloads@[outcome.source as int]@,outcome.run.owner.core().value_state().unwrap())
            && super::services::preloaded(self.postloads@[outcome.source as int]@,outcome.run.owner.core().value_state().unwrap())
    }
    pub closed spec fn wf(&self)->bool {
        self.runtime.wf() && self.bank.wf() && self.runtime.journal_spec()==self.bank.journal() && self.bank.namespace()==self.source_journal.identity_namespace()
            && batch::supported_namespace(self.sources@,self.source_journal) && self.next<=self.order.len()
            && super::order::prefix(self.sources@,self.order@,self.sources@.len()) && super::order::chronological(self.sources@,self.order@)
            && self.slots.wf(&self.bank) && super::services::published(&self.bank,&self.slots,self.routes@,crate::lifecycle_state::services::capture::sources(self.runtime.publications().entries()))
            && (forall|i:int,j:int|0<=i<self.plans.len() && 0<=j<self.plans@[i].entries.len() ==> (#[trigger] self.plans@[i].entries@[j]).wf(&self.bank,&self.slots))
            && self.postloads.len()==self.sources.len()
            && (forall|i:int,j:int|0<=i<self.postloads.len() && 0<=j<self.postloads@[i].len() ==> (#[trigger] self.postloads@[i]@[j]).wf(&self.bank,&self.slots))
            && self.preloads.len()==self.sources.len()
            && (forall|i:int,j:int|0<=i<self.preloads.len() && 0<=j<self.preloads@[i].len() ==> (#[trigger] self.preloads@[i]@[j]).wf(&self.bank,&self.slots))
            && (forall|i:int|0<=i<self.providers.len() ==> (#[trigger] self.providers@[i]).owner.wf())
            && self.view.wf() && self.archive.wf(&self.view)
            && (forall|storage:&mixed::Storage<T>|storage.matches(&self.bank) && storage.canonical(&self.bank) ==> storage.typed_view(&self.bank,&self.view))
    }
    /// Preparation publishes actual providers but executes no source body.
    /// Failure returns the runtime and every already created cleanup owner.
    // Rejection returns all owned runtime state without an additional allocation.
    #[allow(clippy::result_large_err)]
    pub fn new(runtime:ManagedRuntime<P,(),E,T,()>,source_journal:&joint::Journal,sources:Vec<Source<E,T>>,names:Names)->(out:Result<Self,InitializationFailure<P,E,T>>)
        requires runtime.wf(),batch::supported_namespace(sources@,*source_journal),
        ensures out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.position()==0 && out->Ok_0.sources()==sources@
            && out->Ok_0.bank().namespace()==source_journal.identity_namespace(),
    {Self::new_mode(runtime,source_journal,sources,names,true)}
    // Rejection returns all owned runtime state without an additional allocation.
    #[allow(clippy::result_large_err)]
    pub(crate) fn new_unpublished(runtime:ManagedRuntime<P,(),E,T,()>,source_journal:&joint::Journal,sources:Vec<Source<E,T>>,names:Names)->(out:Result<Self,InitializationFailure<P,E,T>>)
        requires runtime.wf(),batch::supported_namespace(sources@,*source_journal),
        ensures out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.position()==0 && out->Ok_0.sources()==sources@
            && out->Ok_0.bank().namespace()==source_journal.identity_namespace(),
    {Self::new_mode(runtime,source_journal,sources,names,false)}
    // Rejection returns all owned runtime state without an additional allocation.
    #[allow(clippy::result_large_err)]
    fn new_mode(mut runtime:ManagedRuntime<P,(),E,T,()>,source_journal:&joint::Journal,sources:Vec<Source<E,T>>,names:Names,publish:bool)->(out:Result<Self,InitializationFailure<P,E,T>>)
        requires runtime.wf(),batch::supported_namespace(sources@,*source_journal),
        ensures out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.position()==0 && out->Ok_0.sources()==sources@
            && out->Ok_0.bank().namespace()==source_journal.identity_namespace(),
    {
        let result=if publish {batch::prepare(&mut runtime,source_journal,sources.as_slice(),names)} else {batch::prepare_objects(&mut runtime,source_journal,sources.as_slice(),names)};
        let prepared=match result {
            Ok(prepared)=>prepared,Err(error)=>return Err(InitializationFailure {runtime,sources,prepared:None,error:InitializationError::Preflight(error)}),
        };
        if prepared.failure.is_some() {return Err(InitializationFailure {runtime,sources,prepared:Some(prepared),error:InitializationError::Preparation});}
        let storage=mixed::Storage::new(&prepared.bank);let view=storage.payload_bank(&prepared.bank);
        let context=match storage.acquire(&prepared.bank) {Ok(context)=>context,Err(error)=>return Err(InitializationFailure {runtime,sources,prepared:Some(prepared),error:InitializationError::Protection(error)})};
        proof {storage.held_payload_bank(&prepared.bank,&view,&context);}
        if let Err(error)=context.payload.as_ref().unwrap().check_initial(&view) {
            context.release();return Err(InitializationFailure {runtime,sources,prepared:Some(prepared),error:InitializationError::Protection(mixed::Error::Typed(error))});
        }
        let archive=archive::Archive::start(&view,context.payload.as_ref().unwrap());context.release();
        let mut routes=Vec::new();let mut i=0;
        while i<prepared.providers.len()
            invariant i<=prepared.providers.len(),super::slots::published(&prepared.bank,&prepared.slots,prepared.providers@,crate::lifecycle_state::services::capture::sources(runtime.publications().entries())),
                super::services::published(&prepared.bank,&prepared.slots,routes@,crate::lifecycle_state::services::capture::sources(runtime.publications().entries())),
            decreases prepared.providers.len()-i,
        {routes.push(super::services::Service::from_provider(&prepared.providers[i]));i+=1;}
        let mut preloads:Vec<Vec<super::services::Preload<T>>>=Vec::new();let mut postloads:Vec<Vec<super::services::Preload<T>>>=Vec::new();let mut i=0;
        while i<sources.len()
            invariant i<=sources.len(),preloads.len()==i,postloads.len()==i,forall|j:int|0<=j<i ==> preloads@[j].len()==0 && postloads@[j].len()==0,
            decreases sources.len()-i,
        {preloads.push(Vec::new());postloads.push(Vec::new());i+=1;}
        let out=Self {plans:Vec::new(),postloads,preloads,routes,runtime,source_journal:source_journal.clone(),sources,order:prepared.order,next:0,bank:prepared.bank,providers:prepared.providers,slots:prepared.slots,view,archive};
        proof {storage.unique_view(&out.bank,&out.view);}
        Ok(out)
    }
    pub proof fn slot_facts(&self) requires self.wf(),ensures self.slot_catalog().wf(&self.bank()), {}
    pub(crate) fn preload(&self,port:Port,source_origin:crate::action_ledger::ActionTicket,selection:&super::environment::Selected<T>,fallback:std::sync::Arc<super::super::Slot<T,()>>)->(out:super::services::Preload<T>)
        requires self.wf(),selection.wf(),selection.namespace(self.bank().namespace()),
        ensures self.accepts_preload(out),out.port==port,out.route.is_none() ==> out.service==fallback,
    {
        if let super::environment::Selected::Scalar(capture)=selection {
            if let Some(slot)=self.slots.find_selection(&self.bank,capture) {
                let service=self.slots.published(slot).unwrap();let index=self.slots.original_entry(slot).unwrap();
                proof {self.slots.entry_facts(&self.bank,slot as int);}
                return super::services::Preload {port,service:service.clone(),route:Some(super::services::Service {id:0,port,index,source_origin:Some(source_origin),slot:Some(slot),service})};
            }
        } else {
            let identity=selection.identity();
            if identity.number().is_none() {return super::services::Preload {port,service:fallback,route:None};}
            if let Some(index)=self.bank.find_identity(&identity) {
                let service=self.bank.slot(index).unwrap();
                return super::services::Preload {port,service:service.clone(),route:Some(super::services::Service {id:0,port,index,source_origin:Some(source_origin),slot:None,service})};
            }
        }
        super::services::Preload {port,service:fallback,route:None}
    }
    pub(crate) fn install_preloads(&mut self,call:usize,entries:Vec<super::services::Preload<T>>)->(out:bool)
        requires old(self).wf(),forall|i:int|0<=i<entries.len() ==> #[trigger] old(self).accepts_preload(entries@[i]),
        ensures final(self).wf(),final(self).slot_catalog()==old(self).slot_catalog(),final(self).sources()==old(self).sources(),final(self).bank()==old(self).bank(),final(self).position()==old(self).position(),final(self).order()==old(self).order(),
    {
        if call>=self.preloads.len() {return false;}let ghost prior=self.preloads@;self.preloads.set(call,entries);
        proof {assert forall|i:int,j:int|0<=i<self.preloads.len() && 0<=j<self.preloads@[i].len() implies (#[trigger] self.preloads@[i]@[j]).wf(&self.bank,&self.slots) by {
            if i==call {assert(self.preloads@[i]@[j]==entries@[j]);assert(old(self).accepts_preload(entries@[j]));} else {assert(self.preloads@[i]==prior[i]);assert(old(self).preloads@[i]@[j].wf(&old(self).bank,&old(self).slots));}
        }}true
    }
    pub(crate) fn install_postloads(&mut self,call:usize,entries:Vec<super::services::Preload<T>>)->(out:bool)
        requires old(self).wf(),forall|i:int|0<=i<entries.len() ==> #[trigger] old(self).accepts_preload(entries@[i]),
        ensures final(self).wf(),final(self).slot_catalog()==old(self).slot_catalog(),final(self).sources()==old(self).sources(),final(self).bank()==old(self).bank(),final(self).position()==old(self).position(),final(self).order()==old(self).order(),
    {
        if call>=self.postloads.len() {return false;}let ghost prior=self.postloads@;self.postloads.set(call,entries);
        proof {assert forall|i:int,j:int|0<=i<self.postloads.len() && 0<=j<self.postloads@[i].len() implies (#[trigger] self.postloads@[i]@[j]).wf(&self.bank,&self.slots) by {
            if i==call {assert(self.postloads@[i]@[j]==entries@[j]);assert(old(self).accepts_preload(entries@[j]));} else {assert(self.postloads@[i]==prior[i]);assert(old(self).postloads@[i]@[j].wf(&old(self).bank,&old(self).slots));}
        }}true
    }
    pub fn next_source(&self)->(out:Option<usize>)
        requires self.wf(),ensures out.is_some()==(self.position()<self.order().len()),out.is_some() ==> out.unwrap()==self.order()[self.position() as int] && out.unwrap()<self.sources().len(),
    {if self.next<self.order.len() {Some(self.order[self.next])} else {None}}
    pub fn ordered_source(&self,position:usize)->(out:Option<usize>)
        requires self.wf(),ensures out.is_some()==(position<self.sources().len()),out.is_some() ==> out.unwrap()==self.order()[position as int] && out.unwrap()<self.sources().len(),
    {if position<self.order.len() {Some(self.order[position])} else {None}}
    pub fn source_count(&self)->(out:usize) ensures out==self.sources().len(), {self.sources.len()}
    pub(crate) proof fn source_facts(&self,index:int)
        requires self.wf(),0<=index<self.sources().len(),
        ensures self.bank().wf(),self.source(index)==self.sources()[index],self.source(index).wf(),
    {batch::supported_at(self.sources@,self.source_journal,index);}
    pub fn source_at(&self,index:usize)->(out:Option<&Source<E,T>>)
        requires self.wf(),ensures out.is_some()==(index<self.sources().len()),out.is_some() ==> *out.unwrap()==self.source(index as int) && out.unwrap().wf()
                && (out.unwrap().environment().is_some() ==> out.unwrap().environment().unwrap().namespace(self.bank().namespace()))
                && (out.unwrap().owned_environment().is_some() ==> out.unwrap().owned_environment().unwrap().namespace(self.bank().namespace()))
                && (out.unwrap().publication_environment().is_some() ==> out.unwrap().publication_environment().unwrap().namespace(self.bank().namespace())),
    {if index<self.sources.len() {proof {batch::supported_at(self.sources@,self.source_journal,index as int);}Some(&self.sources[index])} else {None}}
    /// Inspect the actual mapped cells. Mutating an alias between calls is
    /// permitted; the next invocation must pass the historical input check.
    pub closed spec fn source_domain_spec(&self)->joint::Journal {self.source_journal}
    pub fn source_domain(&self)->(out:&joint::Journal) ensures *out==self.source_domain_spec(), {&self.source_journal}
    pub fn objects(&self)->(out:&Bank<T>) requires self.wf(),ensures *out==self.bank(),out.wf(), {&self.bank}

    fn is_call(&self,id:usize)->(out:bool)
        ensures out ==> forall|i:int|0<=i<self.providers.len() ==> (#[trigger] self.providers@[i]).id!=id,
    {
        let mut i=0;
        while i<self.providers.len()
            invariant i<=self.providers.len(),forall|j:int|0<=j<i ==> (#[trigger] self.providers@[j]).id!=id,
            decreases self.providers.len()-i,
        {if self.providers[i].id==id {return false;}i+=1;}true
    }
    /// Withdraw the real invocation and start its native cleanup action.
    /// Provider owners are excluded; runtime ownership rejects a foreign or
    /// stale invocation without changing its retained inverse obligations.
    pub fn begin_cleanup<C>(&mut self,id:usize,owner:&mut RecordedExecution<C,(),(),(),T,(),()>,retiring:bool)->(out:Result<crate::action_ledger::ActionTicket,NativeError>)
        requires old(self).wf(),old(owner).wf(),
        ensures final(self).wf(),final(owner).wf(),final(owner).same_inverse_word(old(owner)),old(owner).conserved() ==> final(owner).conserved(),final(self).sources()==old(self).sources(),
            final(self).bank()==old(self).bank(),final(self).position()==old(self).position(),final(self).order()==old(self).order(),
    {
        if !self.is_call(id) {return Err(NativeError::InvalidState);}
        owner.withdraw(&mut self.runtime,id,retiring)?;
        proof {owner.facts();}
        self.runtime.settle_managed_execution(id,owner.execution())?;
        self.runtime.begin_cleanup(id)
    }
    /// Continue admission after an earlier withdrawal was blocked by a
    /// consumer. This does not issue a second Restart transition.
    pub fn resume_cleanup<C>(&mut self,id:usize,owner:&RecordedExecution<C,(),(),(),T,(),()>)->(out:Result<crate::action_ledger::ActionTicket,NativeError>)
        requires old(self).wf(),owner.wf(),
        ensures final(self).wf(),final(self).sources()==old(self).sources(),final(self).bank()==old(self).bank(),
            final(self).position()==old(self).position(),final(self).order()==old(self).order(),
    {
        if !self.is_call(id) {return Err(NativeError::InvalidState);}
        proof {owner.facts();}self.runtime.settle_managed_execution(id,owner.execution())?;self.runtime.begin_cleanup(id)
    }
    pub fn retire_child(&mut self,child:&SharedChild)->(out:crate::lifecycle_state::native::runtime::child_recovery::Observation)
        requires old(self).wf(),child.wf(),
        ensures out.0.wf(child),out.1@.is_some()==out.0.result.is_ok(),
            out.1@.is_some() ==> out.1@.unwrap().belongs_to(child),
            final(self).wf(),final(self).sources()==old(self).sources(),final(self).bank()==old(self).bank(),
            final(self).position()==old(self).position(),final(self).order()==old(self).order(),
    {self.runtime.retire_shared_child_observed(child)}
    /// Dispatch exactly the original cleanup queue. A failed inverse is kept
    /// by that queue and must use retry_cleanup before being dispatched again.
    // The type records the native owner and each cleanup payload category.
    #[allow(clippy::type_complexity)]
    pub fn dispatch_cleanup<C>(&self,owner:&mut RecordedExecution<C,(),(),(),T,(),()>,group:usize)->(out:Option<crate::cleanup_groups::payload::DispatchResult<(),(),std::sync::Arc<super::super::Slot<T,()>>,T,()>>)
        requires self.wf(),old(owner).wf(),
        ensures final(owner).wf(),final(owner).same_inverse_word(old(owner)),old(owner).conserved() ==> final(owner).conserved(),
    {
        if !owner.execution().contains(group) {return None;}
        Some(owner.dispatch(group))
    }
    /// Record the real queue failure in the native action ledger before retry.
    pub fn fail_cleanup<C>(&mut self,id:usize,owner:&RecordedExecution<C,(),(),(),T,(),()>)->(out:Result<(),NativeError>)
        requires old(self).wf(),owner.wf(),
        ensures final(self).wf(),final(self).sources()==old(self).sources(),final(self).bank()==old(self).bank(),
            final(self).position()==old(self).position(),final(self).order()==old(self).order(),
    {
        if !self.is_call(id) {return Err(NativeError::InvalidState);}
        proof {owner.facts();}
        self.runtime.fail_managed_execution(id,owner.execution())
    }
    pub fn retry_cleanup<C>(&mut self,id:usize,owner:&mut RecordedExecution<C,(),(),(),T,(),()>)->(out:Result<crate::action_ledger::ActionTicket,NativeError>)
        requires old(self).wf(),old(owner).wf(),
        ensures final(self).wf(),final(owner).wf(),final(owner).same_inverse_word(old(owner)),old(owner).conserved() ==> final(owner).conserved(),final(self).sources()==old(self).sources(),
            final(self).bank()==old(self).bank(),final(self).position()==old(self).position(),final(self).order()==old(self).order(),
            out.is_ok() ==> out->Ok_0.id==id && !final(owner).core().cleanup_state().any_failed()
                && final(owner).core().cleanup_state().retried_failed(&old(owner).core().cleanup_state()),
    {
        if !self.is_call(id) {return Err(NativeError::InvalidState);}
        owner.retry_native(&mut self.runtime,id)
    }
    /// The native release guard decides whether all cleanup has succeeded.
    /// On failure the original owner, dependency bindings and history remain.
    pub fn release<C>(&mut self,id:usize,owner:&mut RecordedExecution<C,(),(),(),T,(),()>)->(out:Result<super::super::interleaving::history::lifecycle::native::ReleaseOutcome<(),(),T,(),()>,NativeError>)
        requires old(self).wf(),old(owner).wf(),
        ensures final(self).wf(),final(owner).wf(),final(owner).same_inverse_word(old(owner)),old(owner).conserved() ==> final(owner).conserved(),final(self).sources()==old(self).sources(),
            final(self).bank()==old(self).bank(),final(self).position()==old(self).position(),final(self).order()==old(self).order(),
    {
        if !self.is_call(id) {return Err(NativeError::InvalidState);}
        let ghost before=self.runtime.publications().entries();
        let out=owner.release(&mut self.runtime,id);
        let ghost routes=self.routes@;
        if out.0.is_ok() {super::services::remove(&mut self.routes,id);}
        proof {
            if out.0.is_ok() {super::services::subset(&self.bank,&self.slots,routes,self.routes@,crate::lifecycle_state::services::capture::sources(before));super::services::remove_publication(&self.bank,&self.slots,self.routes@,before,self.runtime.publications().entries(),id);}
        }
        Ok(out)
    }
    pub fn invoke_next(&mut self,anchor:Port,work_domain:u64)->(out:Result<Option<Outcome<E,T>>,Error<T>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).sources()==old(self).sources(),final(self).bank()==old(self).bank(),final(self).order()==old(self).order(),final(self).history_extends(old(self)),
            out.is_ok() && out->Ok_0.is_some() ==> out->Ok_0.unwrap().source<final(self).sources().len()
                && out->Ok_0.unwrap().matches(&final(self).source(out->Ok_0.unwrap().source as int),&final(self).bank()) && (out->Ok_0.unwrap().run.report->Ok_0.result.is_ok() ==> final(self).ready_to_complete(&out->Ok_0.unwrap())) && (out->Ok_0.unwrap().finished.is_some() ==> final(self).ready_to_finish(&out->Ok_0.unwrap())),
    {self.invoke_selected(anchor,work_domain,None,None,true,None)}
    /// Remove a publication from this session's current binding catalog while
    /// retaining its actual owner. Native withdrawal/cleanup/release still
    /// enforce consumers and children before registry removal or re-publication.
    pub fn detach_provider(&mut self,position:usize)->(out:Option<Provider<E,T>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).sources()==old(self).sources(),final(self).bank()==old(self).bank(),
            final(self).position()==old(self).position(),final(self).order()==old(self).order(),
            out.is_some() ==> out.unwrap().owner.wf(),
    {
        if position>=self.providers.len() {return None;}
        let out=self.providers.remove(position);let ghost routes=self.routes@;
        super::services::remove(&mut self.routes,out.id);
        proof {super::services::subset(&self.bank,&self.slots,routes,self.routes@,crate::lifecycle_state::services::capture::sources(self.runtime.publications().entries()));}
        Some(out)
    }
    pub fn providers(&self)->(out:&[Provider<E,T>]) ensures out@==self.provider_spec(), {self.providers.as_slice()}
    /// Registry removal is a different transition from withdrawal. The
    /// underlying runtime rejects live dependencies, owners and child debt.
    pub fn remove_registration(&mut self,id:usize)->(out:Result<(),NativeError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).sources()==old(self).sources(),final(self).bank()==old(self).bank(),
            final(self).position()==old(self).position(),final(self).order()==old(self).order(),
    {
        if !self.is_call(id) {return Err(NativeError::InvalidState);}
        self.runtime.remove(id).map(|_|())
    }
    /// Begin a new generation of an existing provider after its real release.
    /// A failure after Begin returns the cleanup owner, never discards it.
    // Rejection returns all owned runtime state without an additional allocation.
    #[allow(clippy::result_large_err)]
    pub fn republish(&mut self,id:usize,port:Port,entry:usize,work_domain:u64)->(out:Result<(),PublicationFailure<E,T>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).sources()==old(self).sources(),final(self).bank()==old(self).bank(),
            final(self).position()==old(self).position(),final(self).order()==old(self).order(),
    {
        if !self.is_call(id) {return Err(PublicationFailure::Before(NativeError::InvalidState));}
        let mut service=match self.bank.slot(entry) {Some(s)=>s,None=>return Err(PublicationFailure::Before(NativeError::Unknown))};
        if self.order.is_empty() {return Err(PublicationFailure::Before(NativeError::Unknown));}
        let at=if self.next<self.order.len() {self.next} else {self.order.len()-1};let call=self.order[at];
        proof {batch::supported_at(self.sources@,self.source_journal,call as int);}
        let source_origin=self.sources[call].binding_origin(port);
        let mut catalog_slot=None;let mut initial=entry;
        if service.reversible().is_some() {
            if self.order.is_empty() {return Err(PublicationFailure::Before(NativeError::Unknown));}
            let at=if self.next<self.order.len() {self.next} else {self.order.len()-1};let call=self.order[at];let source=&self.sources[call];
            proof {batch::supported_at(self.sources@,self.source_journal,call as int);assert forall|i:int|0<=i<self.sources.len() implies (#[trigger] self.sources@[i]).wf() by {batch::supported_at(self.sources@,self.source_journal,i);}}
            let inputs=source.inputs();let ports=source.ports();let mut i=0;let mut found:Option<usize>=None;
            while i<inputs.len()
                invariant i<=inputs.len(),inputs@==source.input_spec(),source.wf(),ports@==source.original().ports@,self.bank.wf(),
                    forall|j:int|0<=j<inputs.len() ==> (#[trigger] inputs@[j]).wf() && inputs@[j].namespace(self.bank.namespace()),
                    found.is_some() ==> found.unwrap()<inputs.len() && self.bank.address(entry as int)==inputs@[found.unwrap() as int].source().address(),
                decreases inputs.len()-i,
            {
                let pc=inputs[i].pc();
                if pc<ports.len() && ports[pc]==port && inputs[i].selected_slot().is_some() && self.bank.find(&inputs[i])==Some(entry) {found=Some(i);break;}i+=1;
            }
            let i=match found {Some(i)=>i,None=>return Err(PublicationFailure::Before(NativeError::Unknown))};let ghost prior=self.slots;
            let result=self.slots.bind(&self.bank,&inputs[i],entry);
            proof {
                    super::services::extend(&self.bank,&self.slots,&prior,self.routes@,crate::lifecycle_state::services::capture::sources(self.runtime.publications().entries()));
                    assert forall|i:int,j:int|0<=i<self.preloads.len() && 0<=j<self.preloads@[i].len() implies (#[trigger] self.preloads@[i]@[j]).wf(&self.bank,&self.slots) by {let p=self.preloads@[i]@[j];if p.route.is_some() && p.route.unwrap().slot.is_some() {let n=p.route.unwrap().slot.unwrap() as int;assert(self.slots.service(n)==prior.service(n));assert(self.slots.initial(n)==prior.initial(n));}}
                    assert forall|i:int,j:int|0<=i<self.postloads.len() && 0<=j<self.postloads@[i].len() implies (#[trigger] self.postloads@[i]@[j]).wf(&self.bank,&self.slots) by {let p=self.postloads@[i]@[j];if p.route.is_some() && p.route.unwrap().slot.is_some() {let n=p.route.unwrap().slot.unwrap() as int;assert(self.slots.service(n)==prior.service(n));assert(self.slots.initial(n)==prior.initial(n));}}
                    assert forall|i:int,j:int|0<=i<self.plans.len() && 0<=j<self.plans@[i].entries.len() implies (#[trigger] self.plans@[i].entries@[j]).wf(&self.bank,&self.slots) by {let p=self.plans@[i].entries@[j];if p.route.is_some() && p.route.unwrap().slot.is_some() {let n=p.route.unwrap().slot.unwrap() as int;assert(self.slots.service(n)==prior.service(n));assert(self.slots.initial(n)==prior.initial(n));}}
                }
            let slot=match result {Ok(n)=>n,Err(_)=>return Err(PublicationFailure::Before(NativeError::InvalidState))};
            proof {self.slots.entry_facts(&self.bank,slot as int);}
            service=self.slots.published(slot).unwrap();initial=self.slots.original_entry(slot).unwrap();catalog_slot=Some(slot);
        }
        let execution:super::super::Owner<(),(),(),(),T,(),()>=match self.runtime.begin_managed_execution(id,work_domain) {Ok(owner)=>owner,Err(e)=>return Err(PublicationFailure::Before(e))};
        let (mut owner,report)=self.runtime.run_recorded_root(id,execution);
        if report.is_err() {return Err(PublicationFailure::After {id,owner,report,error:NativeError::InvalidState});}
        if owner.provide(port,service.clone()).is_err() {return Err(PublicationFailure::After {id,owner,report,error:NativeError::InvalidState});}
        let ghost before=self.runtime.publications().entries();let ghost providers=self.providers@;
        let result=owner.finish(&mut self.runtime,id);
        proof {super::services::preserve(&self.bank,&self.slots,self.routes@,before,self.runtime.publications().entries());}
        if let Err(error)=result {return Err(PublicationFailure::After {id,owner,report,error});}
        self.routes.push(super::services::Service {id,port,index:initial,slot:catalog_slot,source_origin,service:service.clone()});
        self.providers.push(Provider {id,port,index:initial,slot:catalog_slot,source_origin,service,owner,report});
        Ok(())
    }
    /// Publish a service from an authenticated object mapping. This uses the
    /// ordinary registration, Begin, provide and Finish sequence, retaining the
    /// actual owner on every post-Begin failure.
    // Rejection returns all owned runtime state without an additional allocation.
    #[allow(clippy::result_large_err)]
    pub fn publish_service(&mut self,port:Port,service:std::sync::Arc<super::super::Slot<T,()>>,anchor:Port,work_domain:u64)->(out:Result<Publication<E,T>,PublicationFailure<E,T>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).sources()==old(self).sources(),final(self).bank()==old(self).bank(),
            final(self).position()==old(self).position(),final(self).order()==old(self).order(),
            final(self).provider_spec()==old(self).provider_spec(),
            out.is_ok() ==> out->Ok_0.port==port && out->Ok_0.service==service && out->Ok_0.owner.wf()
                && final(self).publications().contains_key(out->Ok_0.id)
                && final(self).publications()[out->Ok_0.id].values().contains_pair((port.key,port.realm),service),
    {
        let mut realms=std::collections::BTreeMap::new();realms.insert(port.key,port.realm);
        let function=super::super::Function::new(Vec::new()).ok().unwrap();
        let definition=crate::lifecycle_state::registration::PluginDefinition::new(Vec::new(),vec![port.key],crate::reversible_value::function::Body::Managed(function));
        let id=match self.runtime.register(None,&realms,anchor,definition,()) {Ok(id)=>id,Err((error,_,_))=>return Err(PublicationFailure::Before(error))};
        let execution:super::super::Owner<(),(),(),(),T,(),()>=match self.runtime.begin_managed_execution(id,work_domain) {Ok(owner)=>owner,Err(e)=>return Err(PublicationFailure::Before(e))};
        let (mut owner,report)=self.runtime.run_recorded_root(id,execution);
        if report.is_err() {return Err(PublicationFailure::After {id,owner,report,error:NativeError::InvalidState});}
        if owner.provide(port,service.clone()).is_err() {return Err(PublicationFailure::After {id,owner,report,error:NativeError::InvalidState});}
        let ghost before=self.runtime.publications().entries();
        let result=owner.finish(&mut self.runtime,id);
        proof {super::services::preserve(&self.bank,&self.slots,self.routes@,before,self.runtime.publications().entries());}
        if let Err(error)=result {return Err(PublicationFailure::After {id,owner,report,error});}
        Ok(Publication {id,port,service,owner,report})
    }
    /// Synchronize each authentic source slot once before acquiring its guard.
    /// Conflicting versions inside one source call are rejected before a target
    /// slot is changed; separate calls extend the persistent version map.
    #[verifier::rlimit(16)]
    pub fn select_next_scalar(&mut self)->(out:Result<(),Error<T>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).same_history_snapshot(old(self)),final(self).sources()==old(self).sources(),final(self).bank()==old(self).bank(),
            final(self).position()==old(self).position(),final(self).order()==old(self).order(),
    {
        if self.next>=self.order.len() {return Ok(());}
        let call=self.order[self.next];let source=&self.sources[call];
        proof {batch::supported_at(self.sources@,self.source_journal,call as int);assert forall|i:int|0<=i<self.sources.len() implies (#[trigger] self.sources@[i]).wf() by {batch::supported_at(self.sources@,self.source_journal,i);}}
        let inputs=source.inputs();let ports=source.ports();
        let mut i=0;
        while i<inputs.len()
            invariant self.wf(),source.wf(),inputs@==source.input_spec(),ports@==source.original().ports@,i<=inputs.len(),
                forall|j:int|0<=j<inputs.len() ==> (#[trigger] inputs@[j]).wf() && inputs@[j].namespace(self.bank.namespace()),
            decreases inputs.len()-i,
        {
            if let Some(a)=inputs[i].selected_slot() {
                let identity=a.slot_ref().identity();let mut j=0;
                while j<i
                    invariant self.wf(),*self==*old(self),j<=i,i<inputs.len(),inputs@==source.input_spec(),source.wf(),a.wf(),identity.wf(),identity.namespace()==self.bank.namespace(),identity.address()==(crate::reversible_value::service_composition::Address {journal:a.slot().journal_spec(),key:a.slot().key()}),
                        forall|k:int|0<=k<inputs.len() ==> (#[trigger] inputs@[k]).wf() && inputs@[k].namespace(self.bank.namespace()),
                    decreases i-j,
                {
                    if let Some(b)=inputs[j].selected_slot() {
                        let other=b.slot_ref().identity();
                        if identity.same(&other)==Some(true) && !a.same_revision_at(b) {return Err(Error::Slot(super::slots::Error::ChangedSource));}
                    }j+=1;
                }
            }i+=1;
        }
        let mut i=0;
        while i<inputs.len()
            invariant self.wf(),self.sources()==old(self).sources(),self.bank()==old(self).bank(),self.position()==old(self).position(),self.order()==old(self).order(),
                source.wf(),inputs@==source.input_spec(),ports@==source.original().ports@,i<=inputs.len(),
                forall|j:int|0<=j<inputs.len() ==> (#[trigger] inputs@[j]).wf() && inputs@[j].namespace(self.bank.namespace()),
            decreases inputs.len()-i,
        {
            if inputs[i].selected_slot().is_some() {
                let pc=inputs[i].pc();if pc>=ports.len() {return Err(Error::Protection(mixed::Error::Binding {pc}));}
                let mut p=0;let mut found:Option<usize>=None;
                while p<self.routes.len()
                    invariant source.wf(),p<=self.routes.len(),pc<ports.len(),found.is_some() ==> found.unwrap()<self.routes.len(),
                    decreases self.routes.len()-p,
                {if self.routes[p].port==ports[pc] && self.routes[p].source_origin==source.binding_origin(ports[pc]) {found=Some(p);break;}p+=1;}
                let slot=if source.provides(ports[pc]) {
                    match self.slots.find_selection(&self.bank,inputs[i].selected_slot().unwrap()) {Some(n)=>n,None=>return Err(Error::Slot(super::slots::Error::Allocation))}
                } else {
                    let p=match found {Some(p)=>p,None=>return Err(Error::Protection(mixed::Error::Binding {pc}))};
                    match self.routes[p].slot {Some(n)=>n,None=>return Err(Error::Slot(super::slots::Error::NotScalar))}
                };
                let index=match self.bank.find(&inputs[i]) {Some(n)=>n,None=>return Err(Error::Protection(mixed::Error::Input {step:i}))};
                let ghost prior=self.slots;
                let result=self.slots.advance(&self.bank,slot,&inputs[i],index);
                proof {
                    super::services::extend(&self.bank,&self.slots,&prior,self.routes@,crate::lifecycle_state::services::capture::sources(self.runtime.publications().entries()));
                    assert forall|i:int,j:int|0<=i<self.preloads.len() && 0<=j<self.preloads@[i].len() implies (#[trigger] self.preloads@[i]@[j]).wf(&self.bank,&self.slots) by {let p=self.preloads@[i]@[j];if p.route.is_some() && p.route.unwrap().slot.is_some() {let n=p.route.unwrap().slot.unwrap() as int;assert(self.slots.service(n)==prior.service(n));assert(self.slots.initial(n)==prior.initial(n));}}
                    assert forall|i:int,j:int|0<=i<self.postloads.len() && 0<=j<self.postloads@[i].len() implies (#[trigger] self.postloads@[i]@[j]).wf(&self.bank,&self.slots) by {let p=self.postloads@[i]@[j];if p.route.is_some() && p.route.unwrap().slot.is_some() {let n=p.route.unwrap().slot.unwrap() as int;assert(self.slots.service(n)==prior.service(n));assert(self.slots.initial(n)==prior.initial(n));}}
                    assert forall|i:int,j:int|0<=i<self.plans.len() && 0<=j<self.plans@[i].entries.len() implies (#[trigger] self.plans@[i].entries@[j]).wf(&self.bank,&self.slots) by {let p=self.plans@[i].entries@[j];if p.route.is_some() && p.route.unwrap().slot.is_some() {let n=p.route.unwrap().slot.unwrap() as int;assert(self.slots.service(n)==prior.service(n));assert(self.slots.initial(n)==prior.initial(n));}}
                }
                if let Err(error)=result {return Err(Error::Slot(error));}
            }i+=1;
        }Ok(())
    }
    /// Resume post-root provides from the authentic successful prefix, then
    /// retry Finish. The owner and completed function report survive failures.
    pub fn retry_finish(&mut self,outcome:&mut Outcome<E,T>)->(out:Result<(),NativeError>)
        requires old(self).wf(),old(self).ready_to_complete(old(outcome)),
        ensures final(self).wf(),final(self).same_history_snapshot(old(self)),final(self).sources()==old(self).sources(),final(self).bank()==old(self).bank(),
            final(self).position()==old(self).position(),final(self).order()==old(self).order(),
            final(self).ready_to_complete(final(outcome)),final(outcome).run.owner.wf(),final(outcome).source==old(outcome).source,
            final(outcome).finished.is_some() ==> final(self).ready_to_finish(final(outcome)),
            final(outcome).run.report==old(outcome).run.report,final(outcome).run.inputs==old(outcome).run.inputs,
            final(outcome).correspondence==old(outcome).correspondence,final(outcome).typed_bank==old(outcome).typed_bank,final(outcome).history==old(outcome).history,
            final(outcome).run.id==old(outcome).run.id,final(outcome).run.offset==old(outcome).run.offset,
            final(outcome).run.owner.baseline()==old(outcome).run.owner.baseline(),final(outcome).run.owner.recovery_boundary()==old(outcome).run.owner.recovery_boundary(),
            old(outcome).matches(&old(self).source(old(outcome).source as int),&old(self).bank()) ==>
                final(outcome).matches(&final(self).source(final(outcome).source as int),&final(self).bank()),
    {
        let ghost prior=*outcome;
        let result=self.finish_prepared(outcome);
        proof {if prior.matches(&self.source(prior.source as int),&self.bank()) {
            outcome.completion_frame(&prior,&self.source(prior.source as int),&self.bank());
        }}
        result
    }
    fn finish_prepared(&mut self,outcome:&mut Outcome<E,T>)->(out:Result<(),NativeError>)
        requires old(self).wf(),old(self).ready_to_complete(old(outcome)),
        ensures final(self).wf(),final(self).same_history_snapshot(old(self)),final(self).sources()==old(self).sources(),final(self).bank()==old(self).bank(),
            final(self).position()==old(self).position(),final(self).order()==old(self).order(),
            final(self).ready_to_complete(final(outcome)),final(outcome).run.owner.wf(),final(outcome).source==old(outcome).source,
            final(outcome).finished.is_some() ==> final(self).ready_to_finish(final(outcome)),
            final(outcome).run.report==old(outcome).run.report,final(outcome).run.inputs==old(outcome).run.inputs,
            final(outcome).correspondence==old(outcome).correspondence,final(outcome).typed_bank==old(outcome).typed_bank,final(outcome).history==old(outcome).history,
            final(outcome).run.id==old(outcome).run.id,final(outcome).run.offset==old(outcome).run.offset,
            final(outcome).run.owner.baseline()==old(outcome).run.owner.baseline(),final(outcome).run.owner.recovery_boundary()==old(outcome).run.owner.recovery_boundary(),
    {
        if matches!(outcome.finished,Some(Ok(()))) {return Err(NativeError::InvalidState);}
        let call=outcome.source;let ghost before=outcome.run.owner.core().value_state().unwrap();
        let provided=super::services::install_recorded(&mut outcome.run.owner,self.postloads[call].as_slice(),outcome.provided);
        outcome.provided=provided;
        proof {super::services::retain_preloaded(self.preloads@[call as int]@,before,outcome.run.owner.core().value_state().unwrap());}
        if provided<self.postloads[call].len() {outcome.finished=None;return Err(NativeError::InvalidState);}
        let ghost publications=self.runtime.publications().entries();
        let finished=outcome.run.owner.finish(&mut self.runtime,outcome.run.id);
        proof {super::services::preserve(&self.bank,&self.slots,self.routes@,publications,self.runtime.publications().entries());}
        outcome.finished=Some(finished);
        if finished.is_ok() {
            let entries=super::services::combine(self.preloads[call].as_slice(),self.postloads[call].as_slice());
            proof {super::services::combined_loaded(self.preloads@[call as int]@,self.postloads@[call as int]@,outcome.run.owner.core().value_state().unwrap());}
            self.attach_routes(entries.as_slice(),outcome.run.id);
        }finished
    }
    fn attach_routes(&mut self,entries:&[super::services::Preload<T>],id:usize)
        requires old(self).wf(),forall|i:int|0<=i<entries.len() ==> #[trigger] old(self).accepts_preload(entries@[i]),
            old(self).publications().contains_key(id),forall|i:int|0<=i<entries.len() ==> old(self).publications()[id].values().contains_pair(((#[trigger] entries@[i]).port.key,entries@[i].port.realm),entries@[i].service),
        ensures final(self).wf(),final(self).same_history_snapshot(old(self)),final(self).sources()==old(self).sources(),final(self).bank()==old(self).bank(),final(self).position()==old(self).position(),final(self).order()==old(self).order(),
            final(self).preloads==old(self).preloads,final(self).postloads==old(self).postloads,final(self).plans==old(self).plans,final(self).slot_catalog()==old(self).slot_catalog(),final(self).publications()==old(self).publications(),
    {
        proof {assert forall|j:int|0<=j<entries.len() implies (#[trigger] entries@[j]).wf(&self.bank,&self.slots) by {assert(self.accepts_preload(entries@[j]));}}
        let own=super::services::routes(entries,id);let mut i=0;
        while i<own.len()
            invariant self.wf(),self.archive==old(self).archive,self.view==old(self).view,self.sources()==old(self).sources(),self.bank()==old(self).bank(),self.position()==old(self).position(),self.order()==old(self).order(),
                self.preloads==old(self).preloads,self.postloads==old(self).postloads,self.plans==old(self).plans,self.slot_catalog()==old(self).slot_catalog(),self.publications()==old(self).publications(),i<=own.len(),
                forall|j:int|0<=j<entries.len() ==> (#[trigger] entries@[j]).wf(&self.bank,&self.slots),
                self.publications().contains_key(id),forall|j:int|0<=j<entries.len() ==> self.publications()[id].values().contains_pair(((#[trigger] entries@[j]).port.key,entries@[j].port.realm),entries@[j].service),
                forall|k:int|0<=k<own.len() ==> (#[trigger] own@[k]).id==id && exists|j:int|0<=j<entries.len()
                    && entries@[j].route.is_some() && own@[k].port==entries@[j].port && own@[k].service==entries@[j].service
                    && own@[k].index==entries@[j].route.unwrap().index && own@[k].slot==entries@[j].route.unwrap().slot,
            decreases own.len()-i,
        {
            proof {let j=choose|j:int|0<=j<entries.len() && entries@[j].route.is_some() && own@[i as int].port==entries@[j].port && own@[i as int].service==entries@[j].service && own@[i as int].index==entries@[j].route.unwrap().index && own@[i as int].slot==entries@[j].route.unwrap().slot;assert(own@[i as int].mapped(&self.bank,&self.slots));}
            self.routes.push(own[i].duplicate());i+=1;
        }
    }
    /// Execute a root or owned Child after authentic dynamic slot selection.
    pub fn invoke_next_dynamic(&mut self,anchor:Port,work_domain:u64,parent:Option<usize>)->(out:Result<Option<Outcome<E,T>>,Error<T>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).sources()==old(self).sources(),final(self).bank()==old(self).bank(),final(self).order()==old(self).order(),final(self).history_extends(old(self)),
            out.is_ok() && out->Ok_0.is_some() ==> out->Ok_0.unwrap().source<final(self).sources().len()
                && out->Ok_0.unwrap().matches(&final(self).source(out->Ok_0.unwrap().source as int),&final(self).bank()) && (out->Ok_0.unwrap().run.report->Ok_0.result.is_ok() ==> final(self).ready_to_complete(&out->Ok_0.unwrap())) && (out->Ok_0.unwrap().finished.is_some() ==> final(self).ready_to_finish(&out->Ok_0.unwrap())),
    {self.invoke_selected(anchor,work_domain,parent,None,true,None)}
    /// Register the actual SharedChild queued by its native parent owner,
    /// retaining the paired retirement inverse and original request identity.
    pub fn invoke_next_shared(&mut self,anchor:Port,work_domain:u64,child:&SharedChild)->(out:Result<Option<Outcome<E,T>>,Error<T>>)
        requires old(self).wf(),child.wf(),
        ensures final(self).wf(),final(self).sources()==old(self).sources(),final(self).bank()==old(self).bank(),final(self).order()==old(self).order(),final(self).history_extends(old(self)),
            out.is_ok() && out->Ok_0.is_some() ==> out->Ok_0.unwrap().source<final(self).sources().len()
                && out->Ok_0.unwrap().matches(&final(self).source(out->Ok_0.unwrap().source as int),&final(self).bank()) && (out->Ok_0.unwrap().run.report->Ok_0.result.is_ok() ==> final(self).ready_to_complete(&out->Ok_0.unwrap())) && (out->Ok_0.unwrap().finished.is_some() ==> final(self).ready_to_finish(&out->Ok_0.unwrap())),
    {
        self.invoke_selected(anchor,work_domain,Some(child.parent_id()),Some(child),true,None)
    }
    #[verifier::rlimit(24)]
    #[verifier::spinoff_prover]
    pub(crate) fn invoke_prepared(&mut self,anchor:Port,work_domain:u64,parent:Option<usize>,child:Option<&SharedChild>,existing:Option<usize>)->(out:Result<Option<Outcome<E,T>>,Error<T>>)
        requires old(self).wf(),child.is_some() ==> child.unwrap().wf(),
        ensures final(self).wf(),final(self).sources()==old(self).sources(),final(self).bank()==old(self).bank(),final(self).order()==old(self).order(),final(self).history_extends(old(self)),
            out.is_ok() && out->Ok_0.is_some() ==> out->Ok_0.unwrap().source<final(self).sources().len()
                && old(self).position()<old(self).order().len()
                && out->Ok_0.unwrap().source==old(self).order()[old(self).position() as int]
                && out->Ok_0.unwrap().parent()==if child.is_some() {Some(child.unwrap().owner())} else {parent}
                && out->Ok_0.unwrap().matches(&final(self).source(out->Ok_0.unwrap().source as int),&final(self).bank()) && (out->Ok_0.unwrap().run.report->Ok_0.result.is_ok() ==> final(self).ready_to_complete(&out->Ok_0.unwrap())) && (out->Ok_0.unwrap().finished.is_some() ==> final(self).ready_to_finish(&out->Ok_0.unwrap())),
    {self.invoke_selected(anchor,work_domain,parent,child,false,existing)}
    fn invoke_selected(&mut self,anchor:Port,work_domain:u64,parent:Option<usize>,child:Option<&SharedChild>,finish:bool,existing:Option<usize>)->(out:Result<Option<Outcome<E,T>>,Error<T>>)
        requires old(self).wf(),child.is_some() ==> child.unwrap().wf(),
        ensures final(self).wf(),final(self).sources()==old(self).sources(),final(self).bank()==old(self).bank(),final(self).order()==old(self).order(),final(self).history_extends(old(self)),
            out.is_ok() && out->Ok_0.is_some() ==> out->Ok_0.unwrap().source<final(self).sources().len()
                && old(self).position()<old(self).order().len()
                && out->Ok_0.unwrap().source==old(self).order()[old(self).position() as int]
                && out->Ok_0.unwrap().parent()==if child.is_some() {Some(child.unwrap().owner())} else {parent}
                && out->Ok_0.unwrap().matches(&final(self).source(out->Ok_0.unwrap().source as int),&final(self).bank()) && (out->Ok_0.unwrap().run.report->Ok_0.result.is_ok() ==> final(self).ready_to_complete(&out->Ok_0.unwrap())) && (out->Ok_0.unwrap().finished.is_some() ==> final(self).ready_to_finish(&out->Ok_0.unwrap())),
    {
        hide(joint::valid);hide(joint::step);hide(super::TargetRun::from_source);
        if self.next>=self.order.len() {return Ok(None);}
        self.select_next_scalar()?;
        let call=self.order[self.next];let source=&self.sources[call];
        proof {batch::supported_at(self.sources@,self.source_journal,call as int);assert forall|i:int|0<=i<self.sources.len() implies (#[trigger] self.sources@[i]).wf() by {batch::supported_at(self.sources@,self.source_journal,i);}}
        if !source.is_controlled() {return Err(Error::Uncontrolled {source:call});}
        if !source.succeeded() {return Err(Error::Incomplete {source:call});}
        let active=match super::active::select(&self.bank,&self.view,source) {Ok(active)=>active,Err(error)=>return Err(Error::Protection(error))};
        let storage=active.storage;let view=active.view;let indices=active.indices;
        let mut archive=self.archive.project(&self.view,&view,indices.as_slice());
        let ghost starting_archive=archive;
        let selected=match super::slots::storage::Storage::new(&storage,&self.bank,&self.slots,self.routes.as_slice(),self.preloads[call].as_slice()) {Ok(s)=>s,Err(e)=>return Err(Error::Protection(e))};
        let context=match selected.acquire(&storage,&self.bank,&self.slots) {Ok(context)=>context,Err(error)=>return Err(Error::Protection(error))};
        proof {storage.held_payload_bank(&self.bank,&view,&context);}
        let inputs=source.payload_inputs(Ghost(view.namespace()));
        let plan=match archive.prepare(inputs.as_slice(),&view,context.payload.as_ref().unwrap()) {
            Ok(plan)=>plan,Err(error)=>{context.release();return Err(Error::History(error));},
        };
        let mut context=Some(context);let mut scalar=None;let mut typed=None;let ghost before=context->Some_0;
        let run=match source.instantiate_all(&mut self.runtime,Destination {parent,anchor,host:(),work_domain},&self.bank,self.providers.as_slice(),&mut scalar,&mut typed,&mut context,Some(&storage),Some((&self.slots,&selected,self.routes.as_slice(),self.preloads[call].as_slice())),child,existing) {
            Ok(run)=>run,Err(error)=>{context.unwrap().release();return Err(Error::Start(error));},
        };
        proof {storage.held_payload_bank(&self.bank,&view,&context->Some_0);run.input_facts(source);}
        let admitted=run.report.as_ref().unwrap().result.is_ok();
        if !admitted {context.unwrap().release();return Ok(Some(Outcome {source:call,provided:0,run,finished:None,correspondence:Ghost(None),typed_bank:Ghost(view),history:Ghost(None)}));}
        let ghost steps=run.report->Ok_0.result->Ok_0.steps@;
        let ghost certificate={
            storage.typed_routes(&self.bank,&view,&context->Some_0,source.original().result->Ok_0.steps@);
            plan.routes(&view,context->Some_0.payload->Some_0.routes());held::same_payloads(steps,source.original().result->Ok_0.steps@);
            let p=held::payloads(steps);
            assert forall|i:int|0<=i<p.len() implies (#[trigger] p[i]).result is Payload && p[i].result->Payload_0.inverse().wf() by {let n=held::payload_member(steps,i);assert(steps[n].recorded_values());}
            before.payload->Some_0.storage_facts();
            epochs::protected_inputs(before.payload->Some_0.states(),before.payload->Some_0.revisions(),context->Some_0.payload->Some_0.routes(),p);
            epochs::certify(archive.names(),plan.before(),before.payload->Some_0.states(),plan.before_clocks(),before.payload->Some_0.revisions(),context->Some_0.payload->Some_0.routes(),plan.steps(),p)
        };
        proof {
            certificate.facts();storage.mapped_steps(&self.bank,&context->Some_0,source.original().result->Ok_0.steps@,steps);
            context->Some_0.payload->Some_0.mapped_steps(&view,plan.steps(),held::payloads(steps));
        }
        let targets=typed_inputs(run.inputs.as_slice());
        proof {
            assert(super::typed_tracker::observations(run.inputs@) =~= steps) by {reveal(super::TargetRun::from_source);}
            assert forall|i:int|0<=i<targets.len() implies super::transport::step(source.program().code(),(#[trigger] targets@[i]).source()) by {
                let j=held::payload_member(steps,i);assert(targets@[i].source()==steps[j]);
                assert(super::transport::steps(source.program().code(),run.report->Ok_0.result->Ok_0)) by {reveal(super::TargetRun::from_source);}
            }
        }
        archive.record(plan,source,targets.as_slice(),&view,context.as_ref().unwrap().payload.as_ref().unwrap(),Ghost(certificate));
        context.unwrap().release();
        proof {
            assert forall|i:int|0<=i<indices.len() implies self.archive.names()[indices@[i] as int].submap_of(#[trigger] archive.names()[i]) by {
                assert(starting_archive.names()[i]==self.archive.names()[indices@[i] as int]);
            }
        }
        self.archive.merge(&self.view,&view,indices.as_slice(),archive);
        let ghost history=self.archive.names_certificate(&self.view);
        proof {
            assert forall|i:int|0<=i<view.len_spec() implies history.at(view.address(i))==certificate.after_names[i] by {
                let n=indices@[i] as int;history.entry(n);assert(view.address(i)==self.view.address(n));
            }
        }
        self.next+=1;
        proof {assert(run.owner.wf()) by {reveal(super::TargetRun::from_source);}}
        let mut outcome=Outcome {source:call,provided:0,run,finished:None,correspondence:Ghost(Some(certificate)),typed_bank:Ghost(view),history:Ghost(Some(history))};
        let ghost prior=outcome;
        if finish {let _finished=self.retry_finish(&mut outcome);}
        proof {assert(outcome.run.from_source(source)) by {reveal(super::TargetRun::from_source);}}
        Ok(Some(outcome))
    }
}
fn typed_inputs<T:?Sized>(inputs:&[super::inputs::Input<T>])->(out:Vec<super::inputs::Input<T>>)
    requires forall|i:int|0<=i<inputs.len() ==> (#[trigger] inputs@[i]).wf(),
    ensures super::typed_tracker::observations(out@)==held::payloads(super::typed_tracker::observations(inputs@)),
        forall|i:int|0<=i<out.len() ==> (#[trigger] out@[i]).wf(),
{
    let mut out:Vec<super::inputs::Input<T>>=Vec::new();let mut i=0;
    proof {held::projections_empty::<T>();assert(super::typed_tracker::observations(inputs@).take(0) =~= Seq::empty());}
    while i<inputs.len()
        invariant i<=inputs.len(),forall|j:int|0<=j<inputs.len() ==> (#[trigger] inputs@[j]).wf(),
            super::typed_tracker::observations(out@)==held::payloads(super::typed_tracker::observations(inputs@).take(i as int)),
            forall|j:int|0<=j<out.len() ==> (#[trigger] out@[j]).wf(),
        decreases inputs.len()-i,
    {
        let input=&inputs[i];let ghost prior=out@;
        proof {held::projections_append(super::typed_tracker::observations(inputs@).take(i as int),input.source());assert(super::typed_tracker::observations(inputs@).take(i as int+1) =~= super::typed_tracker::observations(inputs@).take(i as int).push(input.source()));}
        if matches!(input.operand(),super::inputs::Operand::Payload {..}) {out.push(input.duplicate());proof {assert(super::typed_tracker::observations(out@) =~= super::typed_tracker::observations(prior).push(input.source()));}}
        i+=1;
    }
    proof {assert(super::typed_tracker::observations(inputs@).take(i as int) =~= super::typed_tracker::observations(inputs@));}out
}
}

verus! {
impl<P,E:ScalarEffect+Copy,T:?Sized> Session<P,E,T> {
    pub(crate) fn add_plan(&mut self,source_origin:ActionTicket,entries:Vec<Preload<T>>)->(out:usize)
        requires old(self).wf(),forall|i:int|0<=i<entries.len() ==> #[trigger] old(self).accepts_preload(entries@[i]),
        ensures final(self).wf(),final(self).sources()==old(self).sources(),final(self).bank()==old(self).bank(),final(self).slot_catalog()==old(self).slot_catalog(),
            final(self).position()==old(self).position(),final(self).order()==old(self).order(),out<final(self).plan_count_spec(),
    {
        let n=self.plans.len();self.plans.push(Plan {source_origin,entries});
        proof {assert forall|i:int,j:int|0<=i<self.plans.len() && 0<=j<self.plans@[i].entries.len() implies (#[trigger] self.plans@[i].entries@[j]).wf(&self.bank,&self.slots) by {
            if i==n {assert(old(self).accepts_preload(entries@[j]));assert(entries@[j].wf(&self.bank,&self.slots));} else {assert(self.plans@[i]==old(self).plans@[i]);}
        }}n
    }
    pub closed spec fn plan_count_spec(&self)->nat {self.plans@.len()}
    pub fn plan_count(&self)->(out:usize) ensures out==self.plan_count_spec(), {self.plans.len()}
    pub fn plan_origin(&self,index:usize)->(out:Option<ActionTicket>) {if index<self.plans.len() {Some(self.plans[index].source_origin)} else {None}}
    // Rejection returns all owned runtime state without an additional allocation.
    #[allow(clippy::result_large_err)]
    pub(crate) fn publish_plan(&mut self,plan:usize,anchor:Port,work:u64,restart:Option<usize>)->(out:Result<Group<E,T>,PublicationFailure<E,T>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).sources()==old(self).sources(),final(self).bank()==old(self).bank(),final(self).slot_catalog()==old(self).slot_catalog(),
            final(self).position()==old(self).position(),final(self).order()==old(self).order(),out.is_ok() ==> out->Ok_0.owner.wf() && out->Ok_0.plan==plan,
    {
        if plan>=self.plans.len() {return Err(PublicationFailure::Before(NativeError::Unknown));}
        let entries=services::combine(&[],self.plans[plan].entries.as_slice());let origin=self.plans[plan].source_origin;
        proof {assert(entries@ =~= self.plans@[plan as int].entries@);assert forall|i:int|0<=i<entries.len() implies #[trigger] self.accepts_preload(entries@[i]) by {assert(self.plans@[plan as int].entries@[i].wf(&self.bank,&self.slots));}}
        let mut out=match restart {Some(id)=>self.restart_group(id,entries,origin,work)?,None=>self.publish_group(entries,origin,anchor,work)?};
        out.plan=plan;Ok(out)
    }
    // Rejection returns all owned runtime state without an additional allocation.
    #[allow(clippy::result_large_err)]
    pub(crate) fn publish_group(&mut self,entries:Vec<Preload<T>>,source_origin:ActionTicket,anchor:Port,work_domain:u64)->(out:Result<Group<E,T>,PublicationFailure<E,T>>)
        requires old(self).wf(),forall|i:int|0<=i<entries.len() ==> #[trigger] old(self).accepts_preload(entries@[i]),
        ensures final(self).wf(),final(self).sources()==old(self).sources(),final(self).bank()==old(self).bank(),
            final(self).position()==old(self).position(),final(self).order()==old(self).order(),final(self).slot_catalog()==old(self).slot_catalog(),
            out.is_ok() ==> out->Ok_0.owner.wf() && out->Ok_0.source_origin==source_origin && out->Ok_0.services@==entries@
                && final(self).publications().contains_key(out->Ok_0.id)
                && forall|i:int|0<=i<entries.len() ==> final(self).publications()[out->Ok_0.id].values().contains_pair(((#[trigger] entries@[i]).port.key,entries@[i].port.realm),entries@[i].service),
    {
        let mut realms=std::collections::BTreeMap::new();let mut keys=Vec::new();let mut i=0;
        while i<entries.len()
            invariant *self==*old(self),self.wf(),i<=entries.len(),decreases entries.len()-i,
        {
            // One registration resolves each key to exactly one realm.
            if let Some(prior)=realms.get(&entries[i].port.key) {if *prior!=entries[i].port.realm {return Err(PublicationFailure::Before(NativeError::InvalidState));}}
            realms.insert(entries[i].port.key,entries[i].port.realm);keys.push(entries[i].port.key);i+=1;
        }
        let function=Function::new(Vec::new()).ok().unwrap();
        let definition=crate::lifecycle_state::registration::PluginDefinition::new(Vec::new(),keys,crate::reversible_value::function::Body::Managed(function));
        let id=match self.runtime.register(None,&realms,anchor,definition,()) {Ok(id)=>id,Err((error,_,_))=>return Err(PublicationFailure::Before(error))};
        proof {assert forall|i:int|0<=i<entries.len() implies #[trigger] self.accepts_preload(entries@[i]) by {assert(old(self).accepts_preload(entries@[i]));}}
        self.restart_group(id,entries,source_origin,work_domain)
    }
    // Rejection returns all owned runtime state without an additional allocation.
    #[allow(clippy::result_large_err)]
    pub(crate) fn restart_group(&mut self,id:usize,entries:Vec<Preload<T>>,source_origin:ActionTicket,work_domain:u64)->(out:Result<Group<E,T>,PublicationFailure<E,T>>)
        requires old(self).wf(),forall|i:int|0<=i<entries.len() ==> #[trigger] old(self).accepts_preload(entries@[i]),
        ensures final(self).wf(),final(self).sources()==old(self).sources(),final(self).bank()==old(self).bank(),final(self).slot_catalog()==old(self).slot_catalog(),
            final(self).position()==old(self).position(),final(self).order()==old(self).order(),
            out.is_ok() ==> out->Ok_0.owner.wf() && out->Ok_0.id==id && out->Ok_0.source_origin==source_origin && out->Ok_0.services@==entries@
                && final(self).publications().contains_key(id)
                && forall|i:int|0<=i<entries.len() ==> final(self).publications()[id].values().contains_pair(((#[trigger] entries@[i]).port.key,entries@[i].port.realm),entries@[i].service),
    {
        let execution:Owner<(),(),(),(),T,(),()>=match self.runtime.begin_managed_execution(id,work_domain) {Ok(owner)=>owner,Err(e)=>return Err(PublicationFailure::Before(e))};
        let (mut owner,report)=self.runtime.run_recorded_root(id,execution);
        if report.is_err() || owner.execution().native().is_none() {return Err(PublicationFailure::After {id,owner,report,error:NativeError::InvalidState});}
        let provided=services::install_recorded(&mut owner,entries.as_slice(),0);
        if provided<entries.len() {return Err(PublicationFailure::After {id,owner,report,error:NativeError::InvalidState});}
        proof {assert(entries@.take(provided as int) =~= entries@);}
        let ghost before=self.runtime.publications().entries();
        let result=owner.finish(&mut self.runtime,id);
        proof {services::preserve(&self.bank,&self.slots,self.routes@,before,self.runtime.publications().entries());}
        if let Err(error)=result {return Err(PublicationFailure::After {id,owner,report,error});}
        proof {assert forall|i:int|0<=i<entries.len() implies #[trigger] self.accepts_preload(entries@[i]) by {assert(old(self).accepts_preload(entries@[i]));}}
        self.attach_routes(entries.as_slice(),id);
        Ok(Group {plan:0,id,source_origin,services:entries,owner,report})
    }
}
}
