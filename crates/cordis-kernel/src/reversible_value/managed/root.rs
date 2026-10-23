//! Actual stored heterogeneous root/Child dispatch and invocation-return receipt.
use super::{Function, Owner, Report, Slot};
use crate::action_ledger::ActionTicket;
use crate::lifecycle_state::native::runtime::NativeRuntime;
use crate::reversible_value::{effect::ScalarEffect, function::Body, joint};
use crate::setup_work::WorkTicket;
use crate::Port;
#[cfg(verus_keep_ghost)]
use crate::{reversible_value::registration, setup_work::RootStatus};
use vstd::prelude::*;

verus! {
#[derive(Debug)]
pub enum AdmissionError {Unknown,Opaque,InvalidProgram,MissingDependency {pc:usize},WrongOwner,NotAdmitted}
pub struct RegisteredReport<E,T:?Sized> {
    pub origin:ActionTicket,pub work:WorkTicket,pub revision:u64,pub result:Result<Report<T>,super::AdmissionError>,
    pub function:Ghost<Function<E,T>>,pub ports:Vec<Port>,pub completion:Tracked<joint::Receipt>,
    pub start:Tracked<crate::lifecycle_state::native::runtime::episode::Begin>,
}
impl<E:ScalarEffect,T:?Sized> RegisteredReport<E,T> {
    pub closed spec fn completion(&self)->joint::Receipt {self.completion@}
    pub proof fn completion_witness(tracked &self)->(tracked out:&joint::Receipt)
        ensures *out==self.completion(),
    {self.completion.borrow()}
    pub open spec fn completed(&self)->bool {
        self.completion().wf() && joint::classification::history(self.completion().events())
            && self.completion().event().change==(joint::Change::Recipes {event:joint::recipes::Event::Call {id:self.origin.id,version:self.revision,origin:self.origin,work:self.work}})
    }
    pub open spec fn effects_before_return(&self)->bool {self.result.is_ok() ==> registration::before_return(self.result->Ok_0.receipts(),self.completion())}
    pub closed spec fn start(&self)->crate::lifecycle_state::native::runtime::episode::Begin {self.start@}
    pub open spec fn episode_interval(&self)->bool {
        self.start().wf() && self.start().owner().origin==self.origin && self.start().owner().work_domain==self.work.domain_id()
            && self.completion().follows(&self.start().checkpoint()) && self.start().recorded(self.completion().events())
            && (self.result.is_ok() ==> self.result->Ok_0.after(Some(self.start().checkpoint())))
    }
    pub open spec fn succeeded(&self)->bool {self.result.is_ok() && self.result->Ok_0.failure.is_none()}
    /// Every locally recorded successful effect and retained inverse, including
    /// those before a failure, precedes this actual registered function return.
    pub proof fn execution_interval(&self)
        requires self.completed(),self.effects_before_return(),self.result.is_ok(),self.result->Ok_0.witnessed(),
        ensures forall|i:int|0<=i<self.result->Ok_0.steps.len() ==> {
            let s=#[trigger] self.result->Ok_0.steps@[i];
            &&& s.write().journal()==self.completion().journal() ==> self.completion().follows(&s.write())
            &&& s.insertion().is_some() && s.insertion().unwrap().journal()==self.completion().journal() ==> self.completion().follows(&s.insertion().unwrap())
        },
    {}
}
impl<R,H,E:ScalarEffect+Copy,T:?Sized,M> NativeRuntime<Body<R,Function<E,T>>,H,Slot<T,M>> {
    /// Function, arguments, declaration resolution, owner and revision all
    /// come from this real registration. No expected result is caller input.
    pub open spec fn managed_invocation_ready<C,G,A,Retry,X>(&self,id:usize,execution:&Owner<C,G,A,Retry,T,M,X>)->bool {
        self.root_ready(id,execution) && self.registry().entries().contains_key(id)
            && self.registry().entries()[id].recipe().payload() is Managed
            && self.registry().entries()[id].recipe().payload()->Managed_0.valid()
            && exists|ports:Seq<Port>|self.registry().entries()[id].recipe().payload()->Managed_0.bound(ports,self.registry().entries()[id].recipe())
    }
    pub(crate) open spec fn protection_ready<C,G,A,Retry,X>(&self,id:usize,execution:&Owner<C,G,A,Retry,T,M,X>,context:&super::protected::Context<'_>)->bool {
        context.wf() && execution.value_state().is_some() && self.registry().entries().contains_key(id)
            && self.registry().entries()[id].recipe().payload() is Managed
            && super::protected::kernel_only(self.registry().entries()[id].recipe().payload()->Managed_0.code())
            && forall|ports:Seq<Port>|self.registry().entries()[id].recipe().payload()->Managed_0.bound(ports,self.registry().entries()[id].recipe())
                ==> context.supports(execution.value_state().unwrap(),ports)
    }
    pub(crate) open spec fn typed_protection_ready<C,G,A,Retry,X>(&self,id:usize,execution:&Owner<C,G,A,Retry,T,M,X>,context:&super::protected_typed::Context<'_,T,M>)->bool {
        context.wf() && execution.value_state().is_some() && self.registry().entries().contains_key(id)
            && self.registry().entries()[id].recipe().payload() is Managed
            && super::protected_typed::typed_only(self.registry().entries()[id].recipe().payload()->Managed_0.code())
            && context.budget(self.registry().entries()[id].recipe().payload()->Managed_0.code().len())
            && forall|ports:Seq<Port>|self.registry().entries()[id].recipe().payload()->Managed_0.bound(ports,self.registry().entries()[id].recipe())
                ==> context.supports(execution.value_state().unwrap(),ports)
    }
    pub(crate) open spec fn mixed_protection_ready<C,G,A,Retry,X>(&self,id:usize,execution:&Owner<C,G,A,Retry,T,M,X>,context:&super::protected_mixed::Context<'_,T,M>,expected:Seq<super::Step<T>>)->bool {
        context.wf() && execution.value_state().is_some() && self.registry().entries().contains_key(id)
            && self.registry().entries()[id].recipe().payload() is Managed
            && context.payload->Some_0.budget(self.registry().entries()[id].recipe().payload()->Managed_0.code().len())
            && forall|ports:Seq<Port>|self.registry().entries()[id].recipe().payload()->Managed_0.bound(ports,self.registry().entries()[id].recipe())
                ==> context.supports(execution.value_state().unwrap(),ports,self.registry().entries()[id].recipe().payload()->Managed_0.code(),expected)
    }
    pub fn run_managed_root<C,G,A,Retry,X>(&mut self,id:usize,execution:&mut Owner<C,G,A,Retry,T,M,X>)->(out:Result<RegisteredReport<E,T>,AdmissionError>)
        requires old(self).wf(),old(execution).wf(),
        ensures out.is_ok() ==> out->Ok_0.completion().event().key==final(self).recipe_key()
                && out->Ok_0.completion().event().after is Recipes
                && out->Ok_0.completion().event().after->Recipes_state.revision==final(self).recipe_history().events.len(),
            out.is_ok() ==> out->Ok_0.completion().event().after->Recipes_state.entries==crate::lifecycle_state::native::runtime::recipes::project(crate::lifecycle_state::native::runtime::recipes::entries(final(self).registry().entries())),
            old(self).managed_invocation_ready(id,old(execution)) ==> out.is_ok(),
            final(self).wf(),final(self).registry()==old(self).registry(),final(self).state()==old(self).state(),
            final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            out.is_err() ==> final(self).recipe_history()==old(self).recipe_history(),
            out.is_ok() ==> final(self).recipe_history()==old(self).recipe_history().append(
                crate::lifecycle_state::native::runtime::recipes::entries(old(self).registry().entries()),
                joint::recipes::Event::Call {id,version:out->Ok_0.revision,origin:out->Ok_0.origin,work:out->Ok_0.work}),
            final(execution).wf(),final(execution).capture()==old(execution).capture(),final(execution).value_state()==old(execution).value_state(),
            final(execution).execution_journal()==old(execution).execution_journal(),final(execution).status_links()==old(execution).status_links(),
            out.is_err() ==> *final(execution)==*old(execution),
            out.is_ok() ==> {
                let report=out->Ok_0;let recipe=old(self).registry().entries()[id].recipe();
                &&& report.completed() && report.episode_interval() && report.completion().journal()==old(self).journal_spec() && report.effects_before_return()
                &&& report.endpoint_recovery() && report.retained_recovery(*final(execution),0,old(execution).cleanup_state().queues()[0].slots().len())
                &&& old(self).registry().entries().contains_key(id) && recipe.payload() is Managed
                &&& report.function@==recipe.payload()->Managed_0 && report.function@.valid() && report.function@.bound(report.ports@,recipe)
                &&& report.revision==recipe.version() && old(self).owns_execution(id,old(execution)) && old(self).owns_execution(id,final(execution))
                &&& report.origin==old(self).episode_owners()[id].origin && report.origin.id==id && old(self).state().root_invocation_enabled(report.origin)
                &&& report.work.domain_id()==old(execution).work_state().domain_id() && final(execution).work_state().root_status()==RootStatus::Settled
                &&& final(execution).work_state().failed()==!report.succeeded()
                &&& report.result.is_err() ==> final(execution).cleanup_state()==old(execution).cleanup_state()
                &&& report.result.is_ok() ==> {
                    let result=report.result->Ok_0;
                    &&& old(execution).value_state().is_some()
                    &&& result.queued_sources(final(execution).cleanup_state().queues()[0].link())
                    &&& result.registered(final(execution).cleanup_state().link(),0)
                    &&& result.certified(report.function@.code(),report.ports@,old(execution).value_state().unwrap()) && result.ordered() && result.recovery_history()
                    &&& result.interpreted(report.function@.code())
                    &&& result.queue_semantics(*final(execution),0,old(execution).cleanup_state().queues()[0].slots().len())
                    &&& super::retained(result.steps@,*final(execution),0,old(execution).cleanup_state().queues()[0].slots().len())
                    &&& final(execution).cleanup_state().queues()[0].protocol().waiting()==old(execution).cleanup_state().queues()[0].protocol().waiting()+super::tokens(result.steps@)
                    &&& final(execution).cleanup_state().queues()[0].slots().take(old(execution).cleanup_state().queues()[0].slots().len() as int)==old(execution).cleanup_state().queues()[0].slots()
                }
            },
    {let mut mode=None;self.run_managed_root_with(id,execution,&mut mode,Ghost(None))}

    pub(crate) fn run_managed_root_with<C,G,A,Retry,X>(&mut self,id:usize,execution:&mut Owner<C,G,A,Retry,T,M,X>,mode:&mut Option<super::protected::Context<'_>>,Ghost(expected):Ghost<Option<Seq<super::Step<T>>>>)->(out:Result<RegisteredReport<E,T>,AdmissionError>)
        requires expected.is_some() ==> old(mode).is_some()
                && super::protected::plan(old(self).registry().entries()[id].recipe().payload()->Managed_0.code(),expected.unwrap())
                && super::protected::execution(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),expected.unwrap()),
            old(mode).is_some() ==> old(self).protection_ready(id,old(execution),&old(mode)->Some_0),
            old(self).wf(),old(execution).wf(),
        ensures expected.is_some() && out.is_ok() && out->Ok_0.result.is_ok() ==>
                out->Ok_0.result->Ok_0.failure.is_none() && super::protected::same(out->Ok_0.result->Ok_0.steps@,expected.unwrap()),
            final(mode).is_some()==old(mode).is_some(),
            final(mode).is_some() ==> final(mode)->Some_0.wf() && final(mode)->Some_0.shape(&old(mode)->Some_0)
                && (out.is_err() || out->Ok_0.result.is_err() ==> final(mode)->Some_0.states()==old(mode)->Some_0.states())
                && (out.is_ok() && out->Ok_0.result.is_ok() ==> super::protected::addressed(old(mode)->Some_0.targets(),old(mode)->Some_0.routes(),out->Ok_0.result->Ok_0.steps@)
                    && super::protected::execution(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),out->Ok_0.result->Ok_0.steps@)
                    && final(mode)->Some_0.states()==super::protected::after(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),out->Ok_0.result->Ok_0.steps@)),
            out.is_ok() ==> out->Ok_0.completion().event().key==final(self).recipe_key()
                && out->Ok_0.completion().event().after is Recipes
                && out->Ok_0.completion().event().after->Recipes_state.revision==final(self).recipe_history().events.len(),
            out.is_ok() ==> out->Ok_0.completion().event().after->Recipes_state.entries==crate::lifecycle_state::native::runtime::recipes::project(crate::lifecycle_state::native::runtime::recipes::entries(final(self).registry().entries())),
            old(self).managed_invocation_ready(id,old(execution)) ==> out.is_ok(),
            final(self).wf(),final(self).registry()==old(self).registry(),final(self).state()==old(self).state(),
            final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            out.is_err() ==> final(self).recipe_history()==old(self).recipe_history(),
            out.is_ok() ==> final(self).recipe_history()==old(self).recipe_history().append(
                crate::lifecycle_state::native::runtime::recipes::entries(old(self).registry().entries()),
                joint::recipes::Event::Call {id,version:out->Ok_0.revision,origin:out->Ok_0.origin,work:out->Ok_0.work}),
            final(execution).wf(),final(execution).capture()==old(execution).capture(),final(execution).value_state()==old(execution).value_state(),
            final(execution).execution_journal()==old(execution).execution_journal(),final(execution).status_links()==old(execution).status_links(),
            out.is_err() ==> *final(execution)==*old(execution),
            out.is_ok() ==> {
                let report=out->Ok_0;let recipe=old(self).registry().entries()[id].recipe();
                &&& report.completed() && report.episode_interval() && report.completion().journal()==old(self).journal_spec() && report.effects_before_return()
                &&& report.endpoint_recovery() && report.retained_recovery(*final(execution),0,old(execution).cleanup_state().queues()[0].slots().len())
                &&& old(self).registry().entries().contains_key(id) && recipe.payload() is Managed
                &&& report.function@==recipe.payload()->Managed_0 && report.function@.valid() && report.function@.bound(report.ports@,recipe)
                &&& report.revision==recipe.version() && old(self).owns_execution(id,old(execution)) && old(self).owns_execution(id,final(execution))
                &&& report.origin==old(self).episode_owners()[id].origin && report.origin.id==id && old(self).state().root_invocation_enabled(report.origin)
                &&& report.work.domain_id()==old(execution).work_state().domain_id() && final(execution).work_state().root_status()==RootStatus::Settled
                &&& final(execution).work_state().failed()==!report.succeeded()
                &&& report.result.is_err() ==> final(execution).cleanup_state()==old(execution).cleanup_state()
                &&& report.result.is_ok() ==> {
                    let result=report.result->Ok_0;
                    &&& old(execution).value_state().is_some()
                    &&& result.queued_sources(final(execution).cleanup_state().queues()[0].link())
                    &&& result.registered(final(execution).cleanup_state().link(),0)
                    &&& result.certified(report.function@.code(),report.ports@,old(execution).value_state().unwrap()) && result.ordered() && result.recovery_history()
                    &&& result.interpreted(report.function@.code())
                    &&& result.queue_semantics(*final(execution),0,old(execution).cleanup_state().queues()[0].slots().len())
                    &&& super::retained(result.steps@,*final(execution),0,old(execution).cleanup_state().queues()[0].slots().len())
                    &&& final(execution).cleanup_state().queues()[0].protocol().waiting()==old(execution).cleanup_state().queues()[0].protocol().waiting()+super::tokens(result.steps@)
                    &&& final(execution).cleanup_state().queues()[0].slots().take(old(execution).cleanup_state().queues()[0].slots().len() as int)==old(execution).cleanup_state().queues()[0].slots()
                }
            },
    {
        let mut typed=None;
        self.run_managed_root_in(id,execution,mode,Ghost(expected),&mut typed)
    }
    pub(crate) fn run_managed_root_in<C,G,A,Retry,X>(&mut self,id:usize,execution:&mut Owner<C,G,A,Retry,T,M,X>,mode:&mut Option<super::protected::Context<'_>>,Ghost(expected):Ghost<Option<Seq<super::Step<T>>>>,typed:&mut Option<super::protected_typed::Context<'_,T,M>>)->(out:Result<RegisteredReport<E,T>,AdmissionError>)
        requires old(typed).is_some() ==> old(mode).is_none() && old(self).typed_protection_ready(id,old(execution),&old(typed)->Some_0),
            expected.is_some() ==> old(mode).is_some()
                && super::protected::plan(old(self).registry().entries()[id].recipe().payload()->Managed_0.code(),expected.unwrap())
                && super::protected::execution(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),expected.unwrap()),
            old(mode).is_some() ==> old(self).protection_ready(id,old(execution),&old(mode)->Some_0),
            old(self).wf(),old(execution).wf(),
        ensures final(typed).is_some()==old(typed).is_some(),
            final(typed).is_some() ==> final(typed)->Some_0.wf() && final(typed)->Some_0.shape(&old(typed)->Some_0)
                && (out.is_err() || out->Ok_0.result.is_err() ==> final(typed)->Some_0.states()==old(typed)->Some_0.states() && final(typed)->Some_0.revisions()==old(typed)->Some_0.revisions())
                && (out.is_ok() && out->Ok_0.result.is_ok() ==> out->Ok_0.result->Ok_0.failure.is_none()
                    && super::protected_typed::addressed(old(typed)->Some_0.targets(),old(typed)->Some_0.routes(),out->Ok_0.result->Ok_0.steps@)
                    && super::protected_typed::execution(old(typed)->Some_0.states(),old(typed)->Some_0.revisions(),old(typed)->Some_0.routes(),out->Ok_0.result->Ok_0.steps@)
                    && final(typed)->Some_0.states()==super::protected_typed::after(old(typed)->Some_0.states(),old(typed)->Some_0.routes(),out->Ok_0.result->Ok_0.steps@)
                    && final(typed)->Some_0.revisions()==super::protected_typed::clocks(old(typed)->Some_0.revisions(),old(typed)->Some_0.routes(),out->Ok_0.result->Ok_0.steps@)),
            expected.is_some() && out.is_ok() && out->Ok_0.result.is_ok() ==>
                out->Ok_0.result->Ok_0.failure.is_none() && super::protected::same(out->Ok_0.result->Ok_0.steps@,expected.unwrap()),
            final(mode).is_some()==old(mode).is_some(),
            final(mode).is_some() ==> final(mode)->Some_0.wf() && final(mode)->Some_0.shape(&old(mode)->Some_0)
                && (out.is_err() || out->Ok_0.result.is_err() ==> final(mode)->Some_0.states()==old(mode)->Some_0.states())
                && (out.is_ok() && out->Ok_0.result.is_ok() ==> super::protected::addressed(old(mode)->Some_0.targets(),old(mode)->Some_0.routes(),out->Ok_0.result->Ok_0.steps@)
                    && super::protected::execution(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),out->Ok_0.result->Ok_0.steps@)
                    && final(mode)->Some_0.states()==super::protected::after(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),out->Ok_0.result->Ok_0.steps@)),
            out.is_ok() ==> out->Ok_0.completion().event().key==final(self).recipe_key()
                && out->Ok_0.completion().event().after is Recipes
                && out->Ok_0.completion().event().after->Recipes_state.revision==final(self).recipe_history().events.len(),
            out.is_ok() ==> out->Ok_0.completion().event().after->Recipes_state.entries==crate::lifecycle_state::native::runtime::recipes::project(crate::lifecycle_state::native::runtime::recipes::entries(final(self).registry().entries())),
            old(self).managed_invocation_ready(id,old(execution)) ==> out.is_ok(),
            final(self).wf(),final(self).registry()==old(self).registry(),final(self).state()==old(self).state(),
            final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            out.is_err() ==> final(self).recipe_history()==old(self).recipe_history(),
            out.is_ok() ==> final(self).recipe_history()==old(self).recipe_history().append(
                crate::lifecycle_state::native::runtime::recipes::entries(old(self).registry().entries()),
                joint::recipes::Event::Call {id,version:out->Ok_0.revision,origin:out->Ok_0.origin,work:out->Ok_0.work}),
            final(execution).wf(),final(execution).capture()==old(execution).capture(),final(execution).value_state()==old(execution).value_state(),
            final(execution).execution_journal()==old(execution).execution_journal(),final(execution).status_links()==old(execution).status_links(),
            out.is_err() ==> *final(execution)==*old(execution),
            out.is_ok() ==> {
                let report=out->Ok_0;let recipe=old(self).registry().entries()[id].recipe();
                &&& report.completed() && report.episode_interval() && report.completion().journal()==old(self).journal_spec() && report.effects_before_return()
                &&& report.endpoint_recovery() && report.retained_recovery(*final(execution),0,old(execution).cleanup_state().queues()[0].slots().len())
                &&& old(self).registry().entries().contains_key(id) && recipe.payload() is Managed
                &&& report.function@==recipe.payload()->Managed_0 && report.function@.valid() && report.function@.bound(report.ports@,recipe)
                &&& report.revision==recipe.version() && old(self).owns_execution(id,old(execution)) && old(self).owns_execution(id,final(execution))
                &&& report.origin==old(self).episode_owners()[id].origin && report.origin.id==id && old(self).state().root_invocation_enabled(report.origin)
                &&& report.work.domain_id()==old(execution).work_state().domain_id() && final(execution).work_state().root_status()==RootStatus::Settled
                &&& final(execution).work_state().failed()==!report.succeeded()
                &&& report.result.is_err() ==> final(execution).cleanup_state()==old(execution).cleanup_state()
                &&& report.result.is_ok() ==> {
                    let result=report.result->Ok_0;
                    &&& old(execution).value_state().is_some()
                    &&& result.queued_sources(final(execution).cleanup_state().queues()[0].link())
                    &&& result.registered(final(execution).cleanup_state().link(),0)
                    &&& result.certified(report.function@.code(),report.ports@,old(execution).value_state().unwrap()) && result.ordered() && result.recovery_history()
                    &&& result.interpreted(report.function@.code())
                    &&& result.queue_semantics(*final(execution),0,old(execution).cleanup_state().queues()[0].slots().len())
                    &&& super::retained(result.steps@,*final(execution),0,old(execution).cleanup_state().queues()[0].slots().len())
                    &&& final(execution).cleanup_state().queues()[0].protocol().waiting()==old(execution).cleanup_state().queues()[0].protocol().waiting()+super::tokens(result.steps@)
                    &&& final(execution).cleanup_state().queues()[0].slots().take(old(execution).cleanup_state().queues()[0].slots().len() as int)==old(execution).cleanup_state().queues()[0].slots()
                }
            },
    {
        let mut mixed=None;
        self.run_managed_root_guarded(id,execution,mode,Ghost(expected),typed,&mut mixed,Ghost(None))
    }
    #[allow(clippy::too_many_arguments)] // Includes erased plans and borrowed guards.
    pub(crate) fn run_managed_root_guarded<C,G,A,Retry,X>(&mut self,id:usize,execution:&mut Owner<C,G,A,Retry,T,M,X>,mode:&mut Option<super::protected::Context<'_>>,Ghost(expected):Ghost<Option<Seq<super::Step<T>>>>,typed:&mut Option<super::protected_typed::Context<'_,T,M>>,mixed:&mut Option<super::protected_mixed::Context<'_,T,M>>,Ghost(mixed_expected):Ghost<Option<Seq<super::Step<T>>>>)->(out:Result<RegisteredReport<E,T>,AdmissionError>)
        requires old(mixed).is_some()==mixed_expected.is_some(),
            old(mixed).is_some() ==> old(mode).is_none() && old(typed).is_none() && expected.is_none()
                && old(self).mixed_protection_ready(id,old(execution),&old(mixed)->Some_0,mixed_expected.unwrap())
                && super::protected_mixed::plan(old(self).registry().entries()[id].recipe().payload()->Managed_0.code(),mixed_expected.unwrap())
                && super::protected::execution(old(mixed)->Some_0.scalar->Some_0.states(),old(mixed)->Some_0.scalar->Some_0.routes(),super::protected_mixed::scalars(mixed_expected.unwrap())),
            old(typed).is_some() ==> old(mode).is_none() && old(self).typed_protection_ready(id,old(execution),&old(typed)->Some_0),
            expected.is_some() ==> old(mode).is_some()
                && super::protected::plan(old(self).registry().entries()[id].recipe().payload()->Managed_0.code(),expected.unwrap())
                && super::protected::execution(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),expected.unwrap()),
            old(mode).is_some() ==> old(self).protection_ready(id,old(execution),&old(mode)->Some_0),
            old(self).wf(),old(execution).wf(),
        ensures final(mixed).is_some()==old(mixed).is_some(),
            final(mixed).is_some() ==> final(mixed)->Some_0.wf() && final(mixed)->Some_0.shape(&old(mixed)->Some_0)
                && (out.is_err() || out->Ok_0.result.is_err() ==> *final(mixed)==*old(mixed))
                && (out.is_ok() && out->Ok_0.result.is_ok() ==> out->Ok_0.result->Ok_0.failure.is_none()
                    && super::protected_mixed::same(out->Ok_0.result->Ok_0.steps@,mixed_expected.unwrap())
                    && final(mixed)->Some_0.trace(&old(mixed)->Some_0,out->Ok_0.result->Ok_0.steps@)),
            final(typed).is_some()==old(typed).is_some(),
            final(typed).is_some() ==> final(typed)->Some_0.wf() && final(typed)->Some_0.shape(&old(typed)->Some_0)
                && (out.is_err() || out->Ok_0.result.is_err() ==> final(typed)->Some_0.states()==old(typed)->Some_0.states() && final(typed)->Some_0.revisions()==old(typed)->Some_0.revisions())
                && (out.is_ok() && out->Ok_0.result.is_ok() ==> out->Ok_0.result->Ok_0.failure.is_none()
                    && super::protected_typed::addressed(old(typed)->Some_0.targets(),old(typed)->Some_0.routes(),out->Ok_0.result->Ok_0.steps@)
                    && super::protected_typed::execution(old(typed)->Some_0.states(),old(typed)->Some_0.revisions(),old(typed)->Some_0.routes(),out->Ok_0.result->Ok_0.steps@)
                    && final(typed)->Some_0.states()==super::protected_typed::after(old(typed)->Some_0.states(),old(typed)->Some_0.routes(),out->Ok_0.result->Ok_0.steps@)
                    && final(typed)->Some_0.revisions()==super::protected_typed::clocks(old(typed)->Some_0.revisions(),old(typed)->Some_0.routes(),out->Ok_0.result->Ok_0.steps@)),
            expected.is_some() && out.is_ok() && out->Ok_0.result.is_ok() ==>
                out->Ok_0.result->Ok_0.failure.is_none() && super::protected::same(out->Ok_0.result->Ok_0.steps@,expected.unwrap()),
            final(mode).is_some()==old(mode).is_some(),
            final(mode).is_some() ==> final(mode)->Some_0.wf() && final(mode)->Some_0.shape(&old(mode)->Some_0)
                && (out.is_err() || out->Ok_0.result.is_err() ==> final(mode)->Some_0.states()==old(mode)->Some_0.states())
                && (out.is_ok() && out->Ok_0.result.is_ok() ==> super::protected::addressed(old(mode)->Some_0.targets(),old(mode)->Some_0.routes(),out->Ok_0.result->Ok_0.steps@)
                    && super::protected::execution(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),out->Ok_0.result->Ok_0.steps@)
                    && final(mode)->Some_0.states()==super::protected::after(old(mode)->Some_0.states(),old(mode)->Some_0.routes(),out->Ok_0.result->Ok_0.steps@)),
            out.is_ok() ==> out->Ok_0.completion().event().key==final(self).recipe_key()
                && out->Ok_0.completion().event().after is Recipes
                && out->Ok_0.completion().event().after->Recipes_state.revision==final(self).recipe_history().events.len(),
            out.is_ok() ==> out->Ok_0.completion().event().after->Recipes_state.entries==crate::lifecycle_state::native::runtime::recipes::project(crate::lifecycle_state::native::runtime::recipes::entries(final(self).registry().entries())),
            old(self).managed_invocation_ready(id,old(execution)) ==> out.is_ok(),
            final(self).wf(),final(self).registry()==old(self).registry(),final(self).state()==old(self).state(),
            final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            out.is_err() ==> final(self).recipe_history()==old(self).recipe_history(),
            out.is_ok() ==> final(self).recipe_history()==old(self).recipe_history().append(
                crate::lifecycle_state::native::runtime::recipes::entries(old(self).registry().entries()),
                joint::recipes::Event::Call {id,version:out->Ok_0.revision,origin:out->Ok_0.origin,work:out->Ok_0.work}),
            final(execution).wf(),final(execution).capture()==old(execution).capture(),final(execution).value_state()==old(execution).value_state(),
            final(execution).execution_journal()==old(execution).execution_journal(),final(execution).status_links()==old(execution).status_links(),
            out.is_err() ==> *final(execution)==*old(execution),
            out.is_ok() ==> {
                let report=out->Ok_0;let recipe=old(self).registry().entries()[id].recipe();
                &&& report.completed() && report.episode_interval() && report.completion().journal()==old(self).journal_spec() && report.effects_before_return()
                &&& report.endpoint_recovery() && report.retained_recovery(*final(execution),0,old(execution).cleanup_state().queues()[0].slots().len())
                &&& old(self).registry().entries().contains_key(id) && recipe.payload() is Managed
                &&& report.function@==recipe.payload()->Managed_0 && report.function@.valid() && report.function@.bound(report.ports@,recipe)
                &&& report.revision==recipe.version() && old(self).owns_execution(id,old(execution)) && old(self).owns_execution(id,final(execution))
                &&& report.origin==old(self).episode_owners()[id].origin && report.origin.id==id && old(self).state().root_invocation_enabled(report.origin)
                &&& report.work.domain_id()==old(execution).work_state().domain_id() && final(execution).work_state().root_status()==RootStatus::Settled
                &&& final(execution).work_state().failed()==!report.succeeded()
                &&& report.result.is_err() ==> final(execution).cleanup_state()==old(execution).cleanup_state()
                &&& report.result.is_ok() ==> {
                    let result=report.result->Ok_0;
                    &&& old(execution).value_state().is_some()
                    &&& result.queued_sources(final(execution).cleanup_state().queues()[0].link())
                    &&& result.registered(final(execution).cleanup_state().link(),0)
                    &&& result.certified(report.function@.code(),report.ports@,old(execution).value_state().unwrap()) && result.ordered() && result.recovery_history()
                    &&& result.interpreted(report.function@.code())
                    &&& result.queue_semantics(*final(execution),0,old(execution).cleanup_state().queues()[0].slots().len())
                    &&& super::retained(result.steps@,*final(execution),0,old(execution).cleanup_state().queues()[0].slots().len())
                    &&& final(execution).cleanup_state().queues()[0].protocol().waiting()==old(execution).cleanup_state().queues()[0].protocol().waiting()+super::tokens(result.steps@)
                    &&& final(execution).cleanup_state().queues()[0].slots().take(old(execution).cleanup_state().queues()[0].slots().len() as int)==old(execution).cleanup_state().queues()[0].slots()
                }
            },
    {
        let recipe=match self.registration(id) {Some(recipe)=>recipe,None=>return Err(AdmissionError::Unknown)};
        let function=match recipe.payload_ref() {Body::Managed(function)=>function,_=>return Err(AdmissionError::Opaque)};
        if !function.check() {return Err(AdmissionError::InvalidProgram);}
        let ports=match function.bind(recipe) {Ok(ports)=>ports,Err(pc)=>return Err(AdmissionError::MissingDependency {pc})};
        if !self.matches_execution(id,execution) {return Err(AdmissionError::WrongOwner);}
        let invocation=match self.admit_managed_root(id,execution,()) {Ok(invocation)=>invocation,Err(_)=>return Err(AdmissionError::NotAdmitted)};
        let origin=invocation.lifecycle_ticket();let work=invocation.ticket();let revision=recipe.revision();
        let tracked start=self.current_begin(id);
        let tracked cause=start.receipt();
        let ghost preceding=cause;
        let result=execution.run_function_guarded(0,function,ports.as_slice(),Tracked(Some(cause)),mode,Ghost(expected),typed,mixed,Ghost(mixed_expected));
        proof {if let Ok(ref report)=result {
            report.equivalent_cause(Some(preceding),Some(start.checkpoint()));
            report.interpret(function,ports@,execution.value_state().unwrap());
            report.interpret_queue(function.code(),ports@,execution.value_state().unwrap(),*execution,0,old(execution).cleanup_state().queues()[0].slots().len());
        }}
        let successful=match &result {Ok(report)=>report.succeeded(),Err(_)=>false};
        let outcome:Result<(),()>=if successful {Ok(())} else {Err(())};
        let receipt=invocation.into_work().run(|()|->(out:Result<(),()>) ensures out==outcome, {outcome});
        proof {execution.representation();}
        let _completed=execution.complete_root(receipt);assert(_completed.is_ok());assert(self.linked(id));assert(origin.id==id);
        let ghost body=*function;
        proof {self.completed_recipe_call(id,revision,origin,work);}
        let tracked mut empty=Map::<(int,bool),joint::Receipt>::tracked_empty();
        proof {empty.tracked_insert((-1int,false),start.receipt());}
        let completion=match &result {
            Ok(_report)=>self.record_recipes_following::<(int,bool)>(Ghost(joint::recipes::Event::Call {id,version:revision,origin,work}),Tracked(_report.receipt_witnesses())),
            Err(_)=>self.record_recipes_following::<(int,bool)>(Ghost(joint::recipes::Event::Call {id,version:revision,origin,work}),Tracked(&empty)),
        };
        proof {
            match &result {
                Ok(result)=>{result.causal_return(start.checkpoint(),completion@);},
                Err(_)=>{assert(completion@.follows(&empty[(-1int,false)]));},
            }
            start.extend(&completion@);
        }
        let report=RegisteredReport {origin,work,revision,result,function:Ghost(body),ports,completion,start:Tracked(start)};
        proof {
            if report.result.is_ok() {report.execution_interval();}
            report.establish_endpoint_recovery();
            report.establish_retained_recovery(*execution,0,old(execution).cleanup_state().queues()[0].slots().len());
        }
        Ok(report)
    }
}
}

pub mod recovery;
