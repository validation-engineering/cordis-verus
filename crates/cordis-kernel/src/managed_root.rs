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
}
impl<E:ScalarEffect,T:?Sized> RegisteredReport<E,T> {
    pub closed spec fn completion(&self)->joint::Receipt {self.completion@}
    pub open spec fn completed(&self)->bool {
        self.completion().wf() && joint::classification::history(self.completion().events())
            && self.completion().event().change==(joint::Change::Recipes {event:joint::recipes::Event::Call {id:self.origin.id,version:self.revision,origin:self.origin,work:self.work}})
    }
    pub open spec fn effects_before_return(&self)->bool {self.result.is_ok() ==> registration::before_return(self.result->Ok_0.receipts(),self.completion())}
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
    pub fn run_managed_root<C,G,A,Retry,X>(&mut self,id:usize,execution:&mut Owner<C,G,A,Retry,T,M,X>)->(out:Result<RegisteredReport<E,T>,AdmissionError>)
        requires old(self).wf(),old(execution).wf(),
        ensures final(self).wf(),final(self).registry()==old(self).registry(),final(self).state()==old(self).state(),
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
                &&& report.completed() && report.completion().journal()==old(self).journal_spec() && report.effects_before_return()
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
                    &&& result.certified(report.function@.code(),report.ports@,old(execution).value_state().unwrap()) && result.ordered()
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
        let result=execution.run_function(0,function,ports.as_slice());
        proof {if let Ok(ref report)=result {
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
        let tracked empty=Map::<(int,bool),joint::Receipt>::tracked_empty();
        let completion=match &result {
            Ok(_report)=>self.record_recipes_following::<(int,bool)>(Ghost(joint::recipes::Event::Call {id,version:revision,origin,work}),Tracked(_report.receipt_witnesses())),
            Err(_)=>self.record_recipes_following::<(int,bool)>(Ghost(joint::recipes::Event::Call {id,version:revision,origin,work}),Tracked(&empty)),
        };
        let report=RegisteredReport {origin,work,revision,result,function:Ghost(body),ports,completion};
        proof {if report.result.is_ok() {report.execution_interval();}}
        Ok(report)
    }
}
}
