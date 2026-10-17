//! Stored multi-service functions used directly by native root and Child
//! dispatch. Names resolve through the actual registered recipe, while each
//! operation captures the then-current Begin-bound service allocation.
use super::program::Instruction;
use super::services::{self, Call, Program, Report};
use super::slot::ServiceSlot;
use super::{function::Body, joint};
use crate::action_ledger::ActionTicket;
use crate::execution::Execution;
use crate::lifecycle_state::native::runtime::NativeRuntime;
use crate::lifecycle_state::registration::{shared_child::ChildCleanup, RegisteredPlugin};
#[cfg(verus_keep_ghost)]
use crate::setup_work::RootStatus;
use crate::setup_work::WorkTicket;
use vstd::prelude::*;

verus! {
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct NamedCall {pub key:u64,pub instruction:Instruction}
pub struct Function {code:Vec<NamedCall>}
impl Function {
    pub closed spec fn code(&self)->Seq<NamedCall> {self.code@}
    pub closed spec fn valid(&self)->bool {
        forall|i:int| 0<=i<self.code().len() ==> #[trigger] self.code()[i].instruction.valid(i,self.code().len())
    }
    pub fn new(code:Vec<NamedCall>)->(out:Result<Self,Vec<NamedCall>>)
        ensures out.is_ok() ==> out->Ok_0.valid() && out->Ok_0.code()==code@,
            out.is_err() ==> out->Err_0==code,
    {
        let mut i=0;
        while i<code.len()
            invariant i<=code.len(),forall|j:int| 0<=j<i ==> #[trigger] code@[j].instruction.valid(j,code.len() as nat),
            decreases code.len()-i,
        {if !code[i].instruction.check(i,code.len()) {return Err(code);}i+=1;}
        Ok(Self {code})
    }
    pub fn check(&self)->(out:bool) ensures out==self.valid(),
    {
        let mut i=0;
        while i<self.code.len()
            invariant i<=self.code.len(),forall|j:int| 0<=j<i ==> #[trigger] self.code()[j].instruction.valid(j,self.code().len()),
            decreases self.code.len()-i,
        {if !self.code[i].instruction.check(i,self.code.len()) {return false;}i+=1;}
        true
    }
    pub open spec fn bound<C>(&self,code:Seq<Call>,recipe:RegisteredPlugin<C>)->bool {
        code.len()==self.code().len() && forall|i:int| 0<=i<code.len() ==> {
            let call=#[trigger] code[i];
            &&& call.instruction==self.code()[i].instruction && call.port.key==self.code()[i].key
            &&& recipe.dependencies_spec().contains(call.port)
            &&& exists|j:int| 0<=j<recipe.dependencies_spec().len() && recipe.dependencies_spec()[j]==call.port
                && forall|k:int| 0<=k<j ==> recipe.dependencies_spec()[k].key!=call.port.key
        }
    }
    /// Check all branches before issuing the root. A missing dependency cannot
    /// leave a partially executed prefix or an issued root behind.
    pub fn bind<C>(&self,recipe:&RegisteredPlugin<C>)->(out:Result<Program,usize>)
        requires self.valid(),
        ensures out.is_ok() ==> out->Ok_0.valid() && self.bound(out->Ok_0.code(),*recipe),
            out.is_err() ==> out->Err_0<self.code().len()
                && !exists|j:int| 0<=j<recipe.dependencies_spec().len() && recipe.dependencies_spec()[j].key==self.code()[out->Err_0 as int].key,
    {
        let mut code:Vec<Call>=Vec::new();let mut i=0;
        while i<self.code.len()
            invariant i<=self.code.len(),code.len()==i,
                forall|j:int| 0<=j<i ==> (#[trigger] code@[j]).instruction==self.code()[j].instruction
                    && code@[j].port.key==self.code()[j].key && recipe.dependencies_spec().contains(code@[j].port)
                    && exists|k:int| 0<=k<recipe.dependencies_spec().len() && recipe.dependencies_spec()[k]==code@[j].port
                        && forall|l:int| 0<=l<k ==> recipe.dependencies_spec()[l].key!=code@[j].port.key,
            decreases self.code.len()-i,
        {
            let call=self.code[i];
            let port=match recipe.dependency_port(call.key) {Some(port)=>port,None=>return Err(i)};
            code.push(Call {port,instruction:call.instruction});i+=1;
        }
        assert forall|j:int| 0<=j<code.len() implies #[trigger] code@[j].instruction.valid(j,code.len() as nat) by { }
        match Program::new(code) {Ok(program)=>Ok(program),Err(_)=>{assert(false);Err(0)}}
    }
}

#[derive(Debug)]
pub enum AdmissionError {Unknown,Opaque,InvalidProgram,MissingDependency {pc:usize},WrongOwner,NotAdmitted}
pub struct RegisteredReport {
    pub origin:ActionTicket,pub work:WorkTicket,pub revision:u64,
    pub result:Result<Report,services::AdmissionError>,
    pub function:Ghost<Function>,
    pub program:Ghost<Program>,
    pub completion:Tracked<joint::Receipt>,
}
impl RegisteredReport {
    pub closed spec fn completion(&self)->joint::Receipt {self.completion@}
    pub open spec fn completed(&self)->bool {
        self.completion().wf() && joint::classification::history(self.completion().events())
            && self.completion().event().change==(joint::Change::Recipes {
            event:joint::recipes::Event::Call {id:self.origin.id,version:self.revision,origin:self.origin,work:self.work}})
    }
    pub open spec fn local_inverses_registered(&self)->bool {
        self.result.is_ok() ==> forall|i:int| 0<=i<self.result->Ok_0.steps.len() ==> {
            let evidence=#[trigger] self.result->Ok_0.steps@[i].write.admission.registration();
            evidence.same_domain() && evidence.write().journal()==self.completion().journal() ==>
                !joint::pending_at(self.completion().events(),self.completion().events().len()).contains_key(evidence.write().at())
        }
    }
    pub open spec fn effects_before_return(&self)->bool {
        self.result.is_ok() ==> super::registration::before_return(self.result->Ok_0.receipts(),self.completion())
    }

    /// Both successful prefixes and actual rejections belong before this
    /// return when they share its Journal. Foreign witnesses retain identity.
    pub proof fn execution_interval(&self)
        requires self.completed(),self.effects_before_return(),self.result.is_ok(),self.result->Ok_0.witnessed(),
        ensures {
            let r=self.result->Ok_0;let end=self.completion();
            &&& joint::classification::history(end.events())
            &&& self.local_inverses_registered()
            &&& forall|i:int| 0<=i<r.steps.len() ==> {
                let e=(#[trigger] r.steps@[i]).write.admission.registration();
                &&& e.write().journal()==end.journal() ==> end.follows(&e.write())
                &&& e.insertion().is_some() && e.insertion().unwrap().journal()==end.journal() ==> end.follows(&e.insertion().unwrap())
                &&& e.same_domain() && e.write().journal()==end.journal() ==>
                    !joint::pending_at(end.events(),end.events().len()).contains_key(e.write().at())
            }
            &&& r.failure.is_some() && r.failure.unwrap().rejection().is_some()
                && r.failure.unwrap().rejection().unwrap().receipt.journal()==end.journal() ==>
                    end.follows(&r.failure.unwrap().rejection().unwrap().receipt)
        },
    {
        let r=self.result->Ok_0;let end=self.completion();end.classify();
        assert forall|i:int| 0<=i<r.steps.len() implies {
            let e=(#[trigger] r.steps@[i]).write.admission.registration();
            &&& e.write().journal()==end.journal() ==> end.follows(&e.write())
            &&& e.insertion().is_some() && e.insertion().unwrap().journal()==end.journal() ==> end.follows(&e.insertion().unwrap())
            &&& e.same_domain() && e.write().journal()==end.journal() ==>
                !joint::pending_at(end.events(),end.events().len()).contains_key(e.write().at())
        } by {super::registration::registered_before_return(r.receipts(),i,r.steps@[i].write.admission.registration(),end);
            let evidence=r.steps@[i].write.admission.registration();
            if evidence.same_domain() && evidence.write().journal()==end.journal() {evidence.settled_through(&end);}
        }
    }
    pub closed spec fn body(&self)->Function {self.function@}
    pub closed spec fn program(&self)->Program {self.program@}
    pub open spec fn succeeded(&self)->bool {self.result.is_ok() && self.result->Ok_0.failure.is_none()}
}

impl<R,H,T,M,F> NativeRuntime<Body<R,F>,H,ServiceSlot<T,M>> {
    /// The stored body, recipe revision and complete declaration binding are
    /// obtained here. The caller supplies only the actual owner/execution.
    #[verifier::rlimit(30)]
    pub fn run_service_root<C,G,Cb,X>(&mut self,id:usize,execution:&mut Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>>)
        ->(out:Result<RegisteredReport,AdmissionError>)
        requires old(self).wf(),old(execution).wf(),
        ensures final(self).wf(),final(self).registry()==old(self).registry(),final(self).state()==old(self).state(),
            final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            out.is_err() ==> final(self).recipe_history()==old(self).recipe_history(),
            out.is_ok() ==> final(self).recipe_history()==old(self).recipe_history().append(
                crate::lifecycle_state::native::runtime::recipes::entries(old(self).registry().entries()),
                crate::reversible_value::joint::recipes::Event::Call {id,version:out->Ok_0.revision,origin:out->Ok_0.origin,work:out->Ok_0.work}),
            final(execution).wf(),final(execution).capture()==old(execution).capture(),
            final(execution).value_state()==old(execution).value_state(),final(execution).execution_journal()==old(execution).execution_journal(),
            out.is_err() ==> *final(execution)==*old(execution),
            out.is_ok() ==> {
                let report=out->Ok_0;let recipe=old(self).registry().entries()[id].recipe();
                &&& report.completed() && report.completion().journal()==old(self).journal_spec() && report.effects_before_return()
                &&& report.local_inverses_registered()
                &&& old(self).registry().entries().contains_key(id) && recipe.payload() is Services
                &&& report.body()==recipe.payload()->Services_0 && report.body().valid() && report.program().valid()
                &&& report.body().bound(report.program().code(),recipe) && report.revision==recipe.version()
                &&& old(self).owns_execution(id,old(execution)) && old(self).owns_execution(id,final(execution))
                &&& report.origin==old(self).episode_owners()[id].origin && report.origin.id==id
                &&& old(self).state().root_invocation_enabled(report.origin)
                &&& report.work.domain_id()==old(execution).work_state().domain_id()
                &&& final(execution).work_state().root_status()==RootStatus::Settled
                &&& final(execution).work_state().failed()==!report.succeeded()
                &&& report.result.is_err() ==> final(execution).cleanup_state()==old(execution).cleanup_state()
                &&& report.result.is_ok() ==> {
                    let result=report.result->Ok_0;
                    &&& old(execution).value_state().is_some() && report.program().declared(old(execution).value_state().unwrap())
                    &&& result.certified(report.program().code(),old(execution).value_state().unwrap()) && result.ordered() && result.failure_ordered()
                    &&& result.dynamic_semantics(report.program().code(),old(execution).value_state().unwrap())
                    &&& services::retained(result.steps@,*final(execution),0,old(execution).cleanup_state().queues()[0].slots().len())
                    &&& result.queue_semantics(*final(execution),0,old(execution).cleanup_state().queues()[0].slots().len())
                    &&& final(execution).cleanup_state().queues()[0].protocol().waiting()==old(execution).cleanup_state().queues()[0].protocol().waiting()+services::tokens(result.steps@)
                    &&& final(execution).cleanup_state().queues()[0].slots().take(old(execution).cleanup_state().queues()[0].slots().len() as int)==old(execution).cleanup_state().queues()[0].slots()
                }
            },
            final(execution).status_links()==old(execution).status_links(),
    {
        let recipe=match self.registration(id) {Some(recipe)=>recipe,None=>return Err(AdmissionError::Unknown)};
        let function=match recipe.payload_ref() {Body::Services(function)=>function,_=>return Err(AdmissionError::Opaque)};
        if !function.check() {return Err(AdmissionError::InvalidProgram);}
        let program=match function.bind(recipe) {Ok(program)=>program,Err(pc)=>return Err(AdmissionError::MissingDependency {pc})};
        if !self.matches_execution(id,execution) {return Err(AdmissionError::WrongOwner);}
        let invocation=match self.admit_managed_root(id,execution,()) {Ok(invocation)=>invocation,Err(_)=>return Err(AdmissionError::NotAdmitted)};
        let origin=invocation.lifecycle_ticket();let work=invocation.ticket();let revision=recipe.revision();
        let result=execution.run_service_program(0,&program);
        let successful=match &result {Ok(report)=>report.succeeded(),Err(_)=>false};
        let outcome:Result<(),()>=if successful {Ok(())} else {Err(())};
        let receipt=invocation.into_work().run(|()|->(out:Result<(),()>) ensures out==outcome, {outcome});
        proof {execution.representation();}
        let _completed=execution.complete_root(receipt);assert(_completed.is_ok());assert(self.linked(id));assert(origin.id==id);
        let ghost body=*function;
        proof {self.completed_recipe_call(id,revision,origin,work);}
        let tracked empty=Map::<(int,bool),joint::Receipt>::tracked_empty();
        let completion=match &result {
            Ok(report)=>self.record_recipes_following::<(int,bool)>(Ghost(joint::recipes::Event::Call {id,version:revision,origin,work}),report.receipt_witnesses()),
            Err(_)=>self.record_recipes_following::<(int,bool)>(Ghost(joint::recipes::Event::Call {id,version:revision,origin,work}),Tracked(&empty)),
        };
        let report=RegisteredReport {origin,work,revision,result,function:Ghost(body),program:Ghost(program),completion};
        proof {if report.result.is_ok() {report.execution_interval();}}
        Ok(report)
    }
}
}
