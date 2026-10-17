//! A stored finite native root body. The same body is usable by a registered
//! root or Child; its service comes from that actual episode's Begin capture.
#[cfg(verus_keep_ghost)]
use super::program::Instruction;
use super::program::{Program, ProgramReport};
use super::slot::{ReadError, ServiceBinding, ServiceSlot};
use super::{joint, ValueError};
use crate::action_ledger::ActionTicket;
use crate::execution::Execution;
use crate::lifecycle_state::native::runtime::NativeRuntime;
use crate::lifecycle_state::registration::shared_child::ChildCleanup;
use crate::setup_work::{RootStatus, WorkTicket};
use crate::Port;
use vstd::prelude::*;

verus! {
fn root_running(status:RootStatus)->(out:bool)
    ensures out==(status==RootStatus::Queued || status==RootStatus::Running),
{status==RootStatus::Queued || status==RootStatus::Running}
pub struct Function {key:u64,program:Program}
/// The actual registration payload distinguishes proved finite code from
/// opaque callbacks. No closure is used to associate a finite body with an ID.
pub enum Body<C,F=()> {Callback(C),Value(Function),Services(super::service_function::Function),Managed(F)}
impl<C,F> Body<C,F> {
    pub fn is_managed(&self)->(out:bool) ensures out==(*self is Managed), {matches!(self,Self::Managed(_))}
    pub fn is_value(&self)->(out:bool) ensures out==(*self is Value), {matches!(self,Self::Value(_))}
    pub fn is_services(&self)->(out:bool) ensures out==(*self is Services), {matches!(self,Self::Services(_))}
    pub open spec fn callback_requires<A,O>(&self,argument:A)->bool where C:FnMut(A)->O {
        match self {Self::Callback(callback)=>callback.requires((argument,)),Self::Value(_)|Self::Services(_)|Self::Managed(_)=>true}
    }
    pub open spec fn callback_ensures<A,O>(&self,argument:A,result:O)->bool where C:FnMut(A)->O {
        match self {Self::Callback(callback)=>callback.ensures((argument,),result),Self::Value(_)|Self::Services(_)|Self::Managed(_)=>false}
    }
}
#[derive(Debug)]
pub enum Error {NotRunning,WrongKey,NoNativeOwner,Read(ReadError),Value(ValueError)}
pub struct Report {pub binding:ServiceBinding,pub program:ProgramReport}
impl Report {
    pub open spec fn captured_before_writes(&self)->bool {
        self.binding.capture_spec().commit().journal()==self.program.observation().journal_spec() ==>
            forall|i:int| 0<=i<self.program.results().len() ==>
                (#[trigger] self.program.registrations()[i]).write().follows(&self.binding.capture_spec().commit())
    }
    pub open spec fn production_steps<T,M>(&self,code:Seq<Instruction>,episode:crate::lifecycle_state::services::NativeEpisode<ServiceSlot<T,M>>)->bool {
        &&& super::access::selected(episode,self.binding)
        &&& forall|i:int| 0<=i<self.program.results().len() ==> {
            let receipt=(#[trigger] self.program.registrations()[i]).write();let before=super::joint::state_at(receipt.events(),receipt.at());let after=receipt.events().last().state;
            let instruction=code[self.program.points()[i].next.unwrap() as int];
            let run=crate::dependent_grammar::run(super::access::library(),crate::dependent_grammar::Node::Operation {
                operation:(receipt.event().key,instruction.operation),argument:(),select:|out:super::Outcome|instruction.branch.selected(out)},super::access::objects(before));
            &&& run.is_some() && run.unwrap().state==super::access::objects(after) && run.unwrap().next==self.program.points()[i+1].next
            &&& crate::lifecycle_state::services::slots::value_frame(episode.owned(),receipt.journal(),before,after,receipt.event().key)
            &&& crate::lifecycle_state::services::slots::value_frame(episode.imports(),receipt.journal(),before,after,receipt.event().key)
        }
    }
    /// Lift every successful instruction of the actual program to the whole
    /// production object carrier and the actual Begin-owned/imported services.
    #[verifier::rlimit(20)]
    pub proof fn production<T,M>(&self,code:Seq<Instruction>,episode:crate::lifecycle_state::services::NativeEpisode<ServiceSlot<T,M>>)
        requires self.program.certified(code),self.program.registered(),super::access::selected(episode,self.binding),
        ensures self.production_steps(code,episode),
    {
        assert forall|i:int| 0<=i<self.program.results().len() implies {
            let receipt=(#[trigger] self.program.registrations()[i]).write();let before=super::joint::state_at(receipt.events(),receipt.at());let after=receipt.events().last().state;
            let instruction=code[self.program.points()[i].next.unwrap() as int];
            let run=crate::dependent_grammar::run(super::access::library(),crate::dependent_grammar::Node::Operation {
                operation:(receipt.event().key,instruction.operation),argument:(),select:|out:super::Outcome|instruction.branch.selected(out)},super::access::objects(before));
            &&& run.is_some() && run.unwrap().state==super::access::objects(after) && run.unwrap().next==self.program.points()[i+1].next
            &&& crate::lifecycle_state::services::slots::value_frame(episode.owned(),receipt.journal(),before,after,receipt.event().key)
            &&& crate::lifecycle_state::services::slots::value_frame(episode.imports(),receipt.journal(),before,after,receipt.event().key)
        } by {
            let receipt=self.program.registrations()[i].write();let before=super::joint::state_at(receipt.events(),receipt.at());let after=receipt.events().last().state;
            self.program.registered_instruction(code,i);
            assert(super::joint::step(before,after,receipt.event()));
            super::access::interpret(before,after,receipt.event());
            crate::lifecycle_state::services::slots::project_value_step(episode.owned(),receipt.journal(),before,after,receipt.event());
            crate::lifecycle_state::services::slots::project_value_step(episode.imports(),receipt.journal(),before,after,receipt.event());
        }
    }

    pub open spec fn appended<T,M,C,G,Cb,X>(&self,before:Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>>,after:Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>>)->bool {self.appended_at(before,after,0)}
    pub open spec fn appended_at<T,M,C,G,Cb,X>(&self,before:Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>>,after:Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>>,id:usize)->bool {
        let a=before.cleanup_state().queues()[id].slots();let b=after.cleanup_state().queues()[id].slots();
        &&& b.len()==a.len()+self.program.results().len() && b.take(a.len() as int)==a
        &&& forall|i:int| 0<=i<self.program.results().len() ==> {
            let entry=#[trigger] b[a.len()+i];
            &&& entry.is_some() && entry.unwrap() is Value
            &&& entry.unwrap()->Value_0.target()==*self.binding.capture_spec().value_spec()
            &&& entry.unwrap()->Value_0.state().before==self.program.points()[i].state
            &&& entry.unwrap()->Value_0.state().after==self.program.points()[i+1].state
            &&& self.program.registrations()[i].records(entry.unwrap()->Value_0,after.cleanup_state().queues()[id].link(),
                after.cleanup_state().queues()[id].protocol().domain_id(),(a.len()+i) as usize)
        }
    }
}
impl Function {
    pub closed spec fn code(&self)->Seq<Instruction> {self.program.code()}
    pub closed spec fn key_spec(&self)->u64 {self.key}
    pub closed spec fn valid(&self)->bool {self.program.valid()}
    pub fn key(&self)->(out:u64) ensures out==self.key_spec(), {self.key}
    pub fn check(&self)->(out:bool) ensures out==self.valid(), {self.program.check()}
    pub fn new(key:u64,program:Program)->(out:Self)
        requires program.valid(),ensures out.valid(),out.code()==program.code(),out.key_spec()==key,
    {Self {key,program}}
    /// This quantifies over the finite program's complete scalar carrier,
    /// including overflow/failure domains and outcome-selected continuations.
    pub proof fn component(&self,port:Port,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,pc:usize)
        requires self.valid(),port.key==self.key_spec(),keys.contains(port),
        ensures crate::guarded_components::component(super::library(),super::program::programs(self.code(),port),actor,keys,provisions,pc),
    {self.program.component(port,actor,keys,provisions,pc);}
    /// The registered root dispatch calls this body while its real root ticket
    /// is queued/running. Group zero receives every successful prefix inverse,
    /// even if a later instruction overflows. No expected result is an input.
    pub fn run<T,M,C,G,Cb,X>(&self,execution:&mut Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>>,port:Port)
        ->(out:Result<Report,Error>)
        requires self.valid(),old(execution).wf(),
        ensures final(execution).wf(),final(execution).value_attempts()==old(execution).value_attempts(),final(execution).capture()==old(execution).capture(),
            final(execution).work_state()==old(execution).work_state(),final(execution).value_state()==old(execution).value_state(),
            final(execution).phase_spec()==old(execution).phase_spec(),
            out.is_err() ==> *final(execution)==*old(execution),
            out.is_ok() ==> {
                let result=out->Ok_0;let before=old(execution).cleanup_state().queues()[0].slots();
                let after=final(execution).cleanup_state().queues()[0].slots();
                &&& port.key==self.key_spec() && result.binding.wf() && result.binding.port_spec()==port
                &&& old(execution).value_state().is_some()
                &&& super::access::selected(old(execution).value_state().unwrap(),result.binding)
                &&& old(execution).value_state().unwrap().selects_slot(result.binding.provider_spec(),port,result.binding.capture_spec().slot())
                &&& result.program.certified(self.code()) && result.program.registered()
                &&& result.captured_before_writes()
                &&& result.production_steps(self.code(),old(execution).value_state().unwrap())
                &&& result.appended(*old(execution),*final(execution))
                &&& result.program.observation().object()==result.binding.capture_spec().value_spec().object()
                &&& result.program.observation().source()==result.binding.capture_spec().value_spec().source()
                &&& result.program.observation().journal_spec()==result.binding.capture_spec().value_spec().journal_spec()
                &&& old(execution).work_state().root_status()==RootStatus::Queued || old(execution).work_state().root_status()==RootStatus::Running
                &&& after.len()==before.len()+result.program.results().len() && after.take(before.len() as int)==before
                &&& forall|i:int| 0<=i<result.program.results().len() ==> {
                    let entry=#[trigger] after[before.len()+i];
                    &&& entry.is_some() && entry.unwrap() is Value
                    &&& entry.unwrap()->Value_0.target()==*result.binding.capture_spec().value_spec()
                    &&& entry.unwrap()->Value_0.state().before==result.program.points()[i].state
                    &&& entry.unwrap()->Value_0.state().after==result.program.points()[i+1].state
                }
            },
            final(execution).status_links()==old(execution).status_links(),
    {
        proof {execution.representation();}
        if !root_running(execution.work.root()) {return Err(Error::NotRunning);}
        if port.key!=self.key {return Err(Error::WrongKey);}
        execution.run_native_value_program(0,port,&self.program)
    }
}
impl<T,M,C,G,Cb,X> Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>> {
    /// Run a finite calculation from an ordinary root, Child or effect group.
    /// The actual Begin declarations and provider select the target; the same
    /// method is also the registered finite-function dispatch path.
    pub fn run_native_value_program(&mut self,id:usize,port:Port,program:&Program)
        ->(out:Result<Report,Error>)
        requires program.valid(),old(self).wf(),
        ensures final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),
            final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),
            final(self).phase_spec()==old(self).phase_spec(),
            out.is_err() ==> *final(self)==*old(self),
            out.is_ok() ==> {
                let result=out->Ok_0;let before=old(self).cleanup_state().queues()[id].slots();
                let after=final(self).cleanup_state().queues()[id].slots();
                &&& result.binding.wf() && result.binding.port_spec()==port
                &&& old(self).value_state().is_some()
                &&& super::access::selected(old(self).value_state().unwrap(),result.binding)
                &&& old(self).value_state().unwrap().selects_slot(result.binding.provider_spec(),port,result.binding.capture_spec().slot())
                &&& result.program.certified(program.code()) && result.program.registered()
                &&& result.captured_before_writes()
                &&& result.production_steps(program.code(),old(self).value_state().unwrap())
                &&& result.appended_at(*old(self),*final(self),id)
                &&& result.program.observation().object()==result.binding.capture_spec().value_spec().object()
                &&& result.program.observation().source()==result.binding.capture_spec().value_spec().source()
                &&& result.program.observation().journal_spec()==result.binding.capture_spec().value_spec().journal_spec()
                &&& after.len()==before.len()+result.program.results().len() && after.take(before.len() as int)==before
                &&& forall|i:int| 0<=i<result.program.results().len() ==> {
                    let entry=#[trigger] after[before.len()+i];
                    &&& entry.is_some() && entry.unwrap() is Value
                    &&& entry.unwrap()->Value_0.target()==*result.binding.capture_spec().value_spec()
                    &&& entry.unwrap()->Value_0.state().before==result.program.points()[i].state
                    &&& entry.unwrap()->Value_0.state().after==result.program.points()[i+1].state
                }
            },
            final(self).status_links()==old(self).status_links(),
    {
        proof {self.representation();}
        let values=match self.native() {Some(values)=>values,None=>return Err(Error::NoNativeOwner)};
        let binding=match values.read_reversible(port) {Ok(binding)=>binding,Err(error)=>return Err(Error::Read(error))};
        proof {super::access::selection_declared(*values,binding);}
        let capture=binding.capture();let Tracked(cause)=capture.selection_receipt();
        let ghost code=program.code();
        let program=match self.run_value_program_following(id,binding.value(),program,Tracked(Some(cause))) {
            Ok(program)=>program,Err(error)=>return Err(Error::Value(error)),
        };
        let report=Report {binding,program};
        proof {report.production(code,self.value_state().unwrap());}
        Ok(report)
    }
}

#[derive(Debug)]
pub enum AdmissionError {Unknown,Opaque,InvalidProgram,MissingDependency,WrongOwner,NotAdmitted}
/// An actual finite invocation. The function identity is erased, while the
/// lifecycle/work tickets, resolved port, revision and actual report remain.
#[allow(dead_code)]
pub struct RegisteredReport {
    pub origin:ActionTicket,pub work:WorkTicket,pub revision:u64,pub port:Port,
    pub result:Result<Report,Error>,pub function:Ghost<Function>,pub completion:Tracked<joint::Receipt>,
}
impl RegisteredReport {
    pub closed spec fn completion(&self)->joint::Receipt {self.completion@}
    pub open spec fn completed(&self)->bool {
        self.completion().wf() && joint::classification::history(self.completion().events())
            && self.completion().event().change==(joint::Change::Recipes {
            event:joint::recipes::Event::Call {id:self.origin.id,version:self.revision,origin:self.origin,work:self.work}})
    }
    pub open spec fn local_inverses_registered(&self)->bool {
        self.result.is_ok() ==> forall|i:int| 0<=i<self.result->Ok_0.program.results().len() ==> {
            let evidence=#[trigger] self.result->Ok_0.program.registrations()[i];
            evidence.same_domain() && evidence.write().journal()==self.completion().journal() ==>
                !joint::pending_at(self.completion().events(),self.completion().events().len()).contains_key(evidence.write().at())
        }
    }
    pub open spec fn effects_before_return(&self)->bool {
        self.result.is_ok() ==> super::registration::before_return(self.result->Ok_0.program.receipts(),self.completion())
    }

    pub closed spec fn body(&self)->Function {self.function@}
    pub open spec fn succeeded(&self)->bool {self.result.is_ok() && self.result->Ok_0.program.failure().is_none()}
    pub open spec fn certified(&self)->bool {
        self.body().valid() && self.port.key==self.body().key_spec()
            && (self.result.is_ok() ==> {
                let report=self.result->Ok_0;
                &&& report.binding.wf() && report.binding.port_spec()==self.port
                &&& report.program.certified(self.body().code()) && report.program.registered()
                &&& report.captured_before_writes()
                &&& report.program.observation().object()==report.binding.capture_spec().value_spec().object()
                &&& report.program.observation().source()==report.binding.capture_spec().value_spec().source()
                &&& report.program.observation().journal_spec()==report.binding.capture_spec().value_spec().journal_spec()
            })
    }
    /// The actual value observation, every write and every local inverse
    /// registration precede this invocation's return; unrelated commits remain.
    pub proof fn execution_interval(&self)
        requires self.certified(),self.completed(),self.effects_before_return(),self.result.is_ok(),
        ensures {
            let p=self.result->Ok_0.program;let end=self.completion();
            &&& joint::classification::history(end.events())
            &&& self.local_inverses_registered()
            &&& p.observation().journal_spec()==end.journal() ==>
                p.observation().joint_spec().events().len()<end.events().len()
                    && end.events().take(p.observation().joint_spec().events().len() as int)==p.observation().joint_spec().events()
            &&& forall|i:int| 0<=i<p.results().len() ==> {
                let e=#[trigger] p.registrations()[i];
                &&& e.write().journal()==end.journal() ==> end.follows(&e.write())
                &&& e.insertion().is_some() && e.insertion().unwrap().journal()==end.journal() ==> end.follows(&e.insertion().unwrap())
                &&& e.same_domain() && e.write().journal()==end.journal() ==>
                    !joint::pending_at(end.events(),end.events().len()).contains_key(e.write().at())
            }
        },
    {
        let p=self.result->Ok_0.program;let end=self.completion();end.classify();
        assert forall|i:int| 0<=i<p.results().len() implies {
            let e=#[trigger] p.registrations()[i];
            &&& e.write().journal()==end.journal() ==> end.follows(&e.write())
            &&& e.insertion().is_some() && e.insertion().unwrap().journal()==end.journal() ==> end.follows(&e.insertion().unwrap())
            &&& e.same_domain() && e.write().journal()==end.journal() ==>
                !joint::pending_at(end.events(),end.events().len()).contains_key(e.write().at())
        } by {super::registration::registered_before_return(p.receipts(),i,p.registrations()[i],end);
            let evidence=p.registrations()[i];
            if evidence.same_domain() && evidence.write().journal()==end.journal() {evidence.settled_through(&end);}
        }
    }
    /// Complete-carrier membership follows from the body actually fetched from
    /// the registry; it is not a caller-supplied program interpretation.
    pub proof fn component(&self,keys:ISet<Port>,provisions:ISet<Port>,pc:usize)
        requires self.certified(),keys.contains(self.port),
        ensures crate::guarded_components::component(super::library(),super::program::programs(self.body().code(),self.port),self.origin.id,keys,provisions,pc),
    {self.body().component(self.port,self.origin.id,keys,provisions,pc);}
}

impl<R,H,T,M,F> NativeRuntime<Body<R,F>,H,ServiceSlot<T,M>> {
    /// Run the stored finite root/Child against the execution actually issued
    /// by this runtime. Resolve the port from the registered declarations and
    /// settle the real root from the computed result, including failed prefixes.
    pub fn run_value_root<C,G,Cb,X>(&mut self,id:usize,execution:&mut Execution<ServiceSlot<T,M>,C,G,ChildCleanup<Cb,X>>)
        ->(out:Result<RegisteredReport,AdmissionError>)
        requires old(self).wf(),old(execution).wf(),
        ensures final(self).wf(),final(self).registry()==old(self).registry(),final(self).state()==old(self).state(),
            final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            out.is_err() ==> final(self).recipe_history()==old(self).recipe_history(),
            out.is_ok() ==> final(self).recipe_history()==old(self).recipe_history().append(
                crate::lifecycle_state::native::runtime::recipes::entries(old(self).registry().entries()),
                crate::reversible_value::joint::recipes::Event::Call {id,version:out->Ok_0.revision,origin:out->Ok_0.origin,work:out->Ok_0.work}),
            final(execution).wf(),final(execution).value_attempts()==old(execution).value_attempts(),final(execution).capture()==old(execution).capture(),
            final(execution).value_state()==old(execution).value_state(),
            out.is_err() ==> *final(execution)==*old(execution),
            out.is_ok() ==> {
                let report=out->Ok_0;let recipe=old(self).registry().entries()[id].recipe();
                &&& report.completed() && report.completion().journal()==old(self).journal_spec() && report.effects_before_return()
                &&& report.local_inverses_registered()
                &&& old(self).registry().entries().contains_key(id) && recipe.payload() is Value
                &&& report.certified() && report.body()==recipe.payload()->Value_0 && report.revision==recipe.version()
                &&& recipe.dependencies_spec().contains(report.port)
                &&& crate::guarded_components::component(super::library(),super::program::programs(report.body().code(),report.port),id,
                    old(self).state().control().paper().fibers[id].dependencies,old(self).state().control().paper().fibers[id].provisions,0)
                &&& old(self).owns_execution(id,old(execution)) && old(self).owns_execution(id,final(execution))
                &&& report.origin==old(self).episode_owners()[id].origin && report.origin.id==id
                &&& old(self).state().root_invocation_enabled(report.origin)
                &&& report.work.domain_id()==old(execution).work_state().domain_id()
                &&& final(execution).work_state().root_status()==RootStatus::Settled
                &&& final(execution).work_state().failed()==!report.succeeded()
                &&& report.result.is_err() ==> final(execution).cleanup_state()==old(execution).cleanup_state()
                &&& report.result.is_ok() && report.result->Ok_0.binding.capture_spec().value_spec().journal_spec()==old(self).journal_spec() ==>
                    report.result->Ok_0.program.observation().journal_spec()==old(self).journal_spec()
                &&& report.result.is_ok() ==> report.result->Ok_0.appended(*old(execution),*final(execution))
                    && old(execution).value_state().is_some()
                    && super::access::selected(old(execution).value_state().unwrap(),report.result->Ok_0.binding)
                    && report.result->Ok_0.production_steps(report.body().code(),old(execution).value_state().unwrap())
                    && old(execution).value_state().unwrap().selects_slot(report.result->Ok_0.binding.provider_spec(),report.port,report.result->Ok_0.binding.capture_spec().slot())
            },
            final(execution).status_links()==old(execution).status_links(),
    {
        let recipe=match self.registration(id) {Some(recipe)=>recipe,None=>return Err(AdmissionError::Unknown)};
        let function=match recipe.payload_ref() {Body::Value(function)=>function,_=>return Err(AdmissionError::Opaque)};
        if !function.check() {return Err(AdmissionError::InvalidProgram);}
        let port=match recipe.dependency_port(function.key()) {Some(port)=>port,None=>return Err(AdmissionError::MissingDependency)};
        if !self.matches_execution(id,execution) {return Err(AdmissionError::WrongOwner);}
        let invocation=match self.admit_managed_root(id,execution,()) {Ok(invocation)=>invocation,Err(_)=>return Err(AdmissionError::NotAdmitted)};
        let origin=invocation.lifecycle_ticket();let work=invocation.ticket();let revision=recipe.revision();
        let result=function.run(execution,port);
        let successful=match &result {Ok(report)=>report.program.error().is_none(),Err(_)=>false};
        let outcome:Result<(),()>=if successful {Ok(())} else {Err(())};
        let receipt=invocation.into_work().run(|()|->(out:Result<(),()>) ensures out==outcome, {outcome});
        proof {execution.representation();}
        let _completed=execution.complete_root(receipt);
        assert(_completed.is_ok());
        assert(self.linked(id));
        assert(origin.id==id);
        let ghost body=*function;
        proof {self.completed_recipe_call(id,revision,origin,work);}
        let tracked empty=Map::<(int,bool),joint::Receipt>::tracked_empty();
        let completion=match &result {
            Ok(report)=>self.record_recipes_following::<(int,bool)>(Ghost(joint::recipes::Event::Call {id,version:revision,origin,work}),report.program.receipt_witnesses()),
            Err(_)=>self.record_recipes_following::<(int,bool)>(Ghost(joint::recipes::Event::Call {id,version:revision,origin,work}),Tracked(&empty)),
        };
        let report=RegisteredReport {origin,work,revision,port,result,function:Ghost(body),completion};
        proof {
            assert(self.registry().recipe_matches(id));
            report.component(self.state().control().paper().fibers[id].dependencies,self.state().control().paper().fibers[id].provisions,0);
        }
        proof {if report.result.is_ok() {report.execution_interval();}}
        Ok(report)
    }
}

}
