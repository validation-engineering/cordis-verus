//! Opt-in executable managed invocation sources. Target execution uses the
//! original registration, Begin, interpreter and recorded cleanup owner.
//! This is not a serializer for the erased Journal or a whole-window replay.
use super::interleaving::history::lifecycle::RecordedExecution;
use super::{
    root::{AdmissionError, RegisteredReport},
    Call, Effect, Function, Owner, Slot,
};
use crate::lifecycle_state::native::runtime::NativeRuntime;
use crate::lifecycle_state::registration::PluginDefinition;
use crate::realm_context::RealmContext;
use crate::reversible_value::{effect::ScalarEffect, function::Body};
use crate::{Error, Port};
use vstd::prelude::*;
#[path = "managed_replay_bank.rs"]
pub mod bank;
#[path = "managed_replay_batch.rs"]
pub mod batch;
#[path = "managed_replay_binding.rs"]
pub mod binding;
#[path = "managed_replay_continuity.rs"]
pub mod continuity;
#[path = "managed_replay_environment.rs"]
pub mod environment;
#[path = "managed_replay_finalization.rs"]
pub mod finalization;
#[path = "managed_replay_inputs.rs"]
pub mod inputs;
#[path = "managed_replay_observation.rs"]
pub mod observation;
#[path = "managed_replay_order.rs"]
pub mod order;
#[path = "managed_replay_scalar.rs"]
pub mod scalar;
#[path = "managed_replay_selection.rs"]
pub mod selection;
#[path = "managed_replay_slots.rs"]
pub mod slots;
#[path = "managed_replay_transport.rs"]
pub mod transport;
#[path = "managed_replay_typed.rs"]
pub mod typed;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
impl<E:Copy,T:?Sized> Function<E,T> {
    /// Retain exactly the actual program, including replacement Arc identities.
    /// Explicit source capture owns these references; ordinary calls do not.
    pub fn duplicate(&self)->(out:Self)
        ensures out.code()==self.code(),out.valid()==self.valid(),
    {
        let mut code=Vec::new();let mut i=0;
        while i<self.code.len()
            invariant i<=self.code.len(),code@==self.code@.take(i as int),
            decreases self.code.len()-i,
        {
            let call=&self.code[i];
            let effect=match &call.effect {Effect::Kernel(i)=>Effect::Kernel(*i),Effect::Scalar(e)=>Effect::Scalar(*e),Effect::Replace(v)=>Effect::Replace(v.clone())};
            code.push(Call {key:call.key,effect,branch:call.branch});i+=1;
        }
        proof {assert(code@ =~= self.code@);}
        let out=Self {code};
        proof {reveal(Function::valid);assert(out.code()==self.code());}
        out
    }
}
fn copy_ports(ports:&[Port])->(out:Vec<Port>)
    ensures out@==ports@,
{
    let mut out=Vec::new();let mut i=0;
    while i<ports.len()
        invariant i<=ports.len(),out@==ports@.take(i as int),
        decreases ports.len()-i,
    {out.push(ports[i]);i+=1;}out
}
pub open spec fn key_sequence(ports:Seq<Port>)->Seq<u64> {ports.map(|_:int,p:Port|p.key)}
fn keys(ports:&[Port])->(out:Vec<u64>)
    ensures out@.no_duplicates(),out@.to_set()==key_sequence(ports@).to_set(),
{
    let mut out=Vec::new();let mut i=0;
    while i<ports.len()
        invariant i<=ports.len(),out@.no_duplicates(),forall|k:u64|#[trigger] out@.contains(k)==key_sequence(ports@.take(i as int)).contains(k),
        decreases ports.len()-i,
    {
        let ghost before=out@;let key=ports[i].key;let mut j=0;let mut found=false;
        while j<out.len()
            invariant j<=out.len(),out@==before,found==out@.take(j as int).contains(key),
                forall|k:u64|#[trigger] before.contains(k)==key_sequence(ports@.take(i as int)).contains(k),
            decreases out.len()-j,
        {if out[j]==key {found=true;}j+=1;}
        if !found {out.push(key);}
        proof {
            let a=key_sequence(ports@.take(i as int));
            let b=key_sequence(ports@.take(i+1));
            assert(b =~= a.push(key));
            before.to_set_ensures();a.to_set_ensures();b.to_set_ensures();out@.to_set_ensures();
            assert forall|k:u64|out@.contains(k)==b.contains(k) by {
                assert(before.contains(k)==a.contains(k));
            }
            assert(out@.to_set() =~= b.to_set());
        }
        i+=1;
    }out
}
fn same_ports(a:&[Port],b:&[Port])->(out:bool)
    ensures out==(a@==b@),
{
    if a.len()!=b.len() {return false;}
    let mut i=0;
    while i<a.len()
        invariant a.len()==b.len(),i<=a.len(),a@.take(i as int)==b@.take(i as int),
        decreases a.len()-i,
    {if a[i]!=b[i] {return false;}i+=1;}
    true
}
/// The proof copy is bound at the actual invocation return, never to a caller's
/// expected trace. Program and declaration inputs survive source deregistration.
#[allow(dead_code)] // The authentic source report is erased.
pub struct Source<E,T:?Sized,SM=()> {
    component_word:Option<crate::reversible_value::closed::component::accumulator::Word<T>>,
    finalized:Option<finalization::Publication<T,SM>>,parent:Option<usize>,
    function:Function<E,T>,dependencies:Vec<Port>,provisions:Vec<Port>,realms:RealmContext,ports:Vec<Port>,
    origin:crate::action_ledger::ActionTicket,work_domain:u64,stamp:order::CallPosition,inputs:Vec<inputs::Input<T>>,succeeded:bool,
    environment:Option<environment::Environment<T>>,owned:Option<environment::Environment<T>>,
    report:Ghost<RegisteredReport<E,T>>,
    completion:Tracked<crate::reversible_value::joint::Receipt>,
}
pub struct Captured<E,T:?Sized,M=()> {pub source:Source<E,T,M>,pub report:RegisteredReport<E,T>}
pub type CaptureOutcome<C,G,A,R,T,M,X,E> = (RecordedExecution<C,G,A,R,T,M,X>,Result<Captured<E,T,M>,AdmissionError>);
impl<E:ScalarEffect,T:?Sized,SM> Source<E,T,SM> {
    pub closed spec fn component_word(&self)->Option<crate::reversible_value::closed::component::accumulator::Word<T>> {self.component_word}
    pub(crate) fn attach_component_word(&mut self,word:crate::reversible_value::closed::component::accumulator::Word<T>)
        requires old(self).wf(),word.wf(),old(self).original().result.is_ok(),word.root()==old(self).original().result->Ok_0.steps@,
            word.owner().baseline().origin()==Some(old(self).original().origin),
        ensures final(self).wf(),final(self).component_word()==Some(word),final(self).original()==old(self).original(),
            final(self).program()==old(self).program(),
    {self.component_word=Some(word);}
    pub closed spec fn final_publication(&self)->Option<finalization::Publication<T,SM>> {self.finalized}
    pub closed spec fn publication_environment(&self)->Option<environment::Environment<T>> {
        match self.finalized {Some(p)=>Some(p.environment()),None=>None}
    }
    pub fn published_observations(&self)->(out:Option<&environment::Environment<T>>)
        requires self.wf(),ensures out.is_some()==self.publication_environment().is_some(),
            out.is_some() ==> *out.unwrap()==self.publication_environment().unwrap() && out.unwrap().wf() && out.unwrap().declarations(self.provision_ports()),
    {match &self.finalized {Some(p)=>{proof {p.facts(self.original().origin,self.provision_ports());}Some(p.observations())},None=>None}}
    pub closed spec fn environment(&self)->Option<environment::Environment<T>> {self.environment}
    pub fn declared_environment(&self)->(out:Option<&environment::Environment<T>>)
        requires self.wf(),ensures out.is_some()==self.environment().is_some(),
            out.is_some() ==> *out.unwrap()==self.environment().unwrap() && out.unwrap().wf(),
    {self.environment.as_ref()}
    pub closed spec fn owned_environment(&self)->Option<environment::Environment<T>> {self.owned}
    pub fn owned_observations(&self)->(out:Option<&environment::Environment<T>>)
        requires self.wf(),ensures out.is_some()==self.owned_environment().is_some(),
            out.is_some() ==> *out.unwrap()==self.owned_environment().unwrap() && out.unwrap().wf() && out.unwrap().declarations(self.provision_ports()),
    {self.owned.as_ref()}
    pub fn provided_before_root(&self,port:Port)->(out:bool)
        requires self.wf(),
    {match self.owned_observations() {Some(e)=>e.binding(port).is_some(),None=>false}}
    pub fn provides(&self,port:Port)->(out:bool)
        ensures out==self.provision_ports().contains(port),
    {
        let mut i=0;while i<self.provisions.len() invariant i<=self.provisions.len(),forall|j:int|0<=j<i ==> self.provisions@[j]!=port,decreases self.provisions.len()-i,
        {if self.provisions[i]==port {return true;}i+=1;}false
    }
    pub open spec fn uses_origin(&self,port:Port,origin:crate::action_ledger::ActionTicket)->bool {
        if self.provision_ports().contains(port) {origin==self.original().origin} else {
            self.environment().is_some() && exists|i:int|0<=i<self.environment().unwrap().entries().len() && {
                let e=#[trigger] self.environment().unwrap().entries()[i];
                &&& e.port==port && e.result.is_ok() && e.result->Ok_0.origin==origin
            }
        }
    }
    // Explicit branches preserve the erased receipt and owner relations.
    #[allow(clippy::manual_map)]
    pub fn binding_origin(&self,port:Port)->(out:Option<crate::action_ledger::ActionTicket>)
        requires self.wf(),ensures out.is_some() ==> self.uses_origin(port,out.unwrap()),
    {
        if self.provides(port) {return Some(self.source_origin());}
        let environment=self.declared_environment()?;
        match environment.binding(port) {Some(b)=>Some(b.origin),None=>None}
    }
    /// Exact declarations and parent from the recipe committed by the original
    /// invocation. This provenance survives source removal or replacement.
    pub open spec fn registration_shape(&self)->crate::reversible_value::joint::recipes::Shape {
        self.original().completion().event().after->Recipes_state.entries[self.original().origin.id]
    }
    pub fn parent_id(&self)->(out:Option<usize>) requires self.wf(),ensures out==self.registration_shape().parent, {self.parent}
    pub closed spec fn original(&self)->RegisteredReport<E,T> {self.report@}
    pub closed spec fn provision_ports(&self)->Seq<Port> {self.provisions@}
    pub closed spec fn input_spec(&self)->Seq<inputs::Input<T>> {self.inputs@}
    pub closed spec fn program(&self)->Function<E,T> {self.function}
    pub(crate) fn function_ref(&self)->(out:&Function<E,T>) ensures *out==self.program(), {&self.function}
    pub closed spec fn wf(&self)->bool {
        (self.component_word.is_some() ==> self.component_word.unwrap().wf() && self.original().result.is_ok()
            && self.component_word.unwrap().root()==self.original().result->Ok_0.steps@
            && self.component_word.unwrap().owner().baseline().origin()==Some(self.original().origin))
            && self.original().completion().event().after is Recipes
            && self.original().completion().event().after->Recipes_state.entries.contains_key(self.original().origin.id)
            && self.parent==self.registration_shape().parent && self.dependencies@==self.registration_shape().dependencies
            && self.provisions@==self.registration_shape().provisions && self.realms.mapping()==self.registration_shape().realms
            && (self.finalized.is_some() ==> self.finalized.unwrap().certified(self.original().origin,self.provisions@)
            && self.finalized.unwrap().cut().joint_spec().covers(&self.original().completion()))
            && (self.environment.is_some() ==> self.environment.unwrap().wf() && self.environment.unwrap().declarations(self.dependencies@)
                && self.environment.unwrap().origin()==self.original().origin && self.environment.unwrap().work()==self.original().work.domain_id())
            && (self.owned.is_some() ==> self.owned.unwrap().wf() && self.owned.unwrap().declarations(self.provisions@)
                && self.owned.unwrap().origin()==self.original().origin && self.owned.unwrap().work()==self.original().work.domain_id())
            && (self.original().result.is_ok() ==> self.environment.is_some() && self.owned.is_some())
            && self.stamp.stream.wf() && self.stamp.stream.address()==(crate::reversible_value::service_composition::Address {journal:self.completion@.journal(),key:self.completion@.event().key})
            && self.completion@.event().after is Recipes
            && (match self.stamp.revision {Some(n)=>n as nat==self.completion@.event().after->Recipes_state.revision,None=>self.completion@.event().after->Recipes_state.revision>u64::MAX})
            && self.completion@.wf() && self.completion@.same(&self.original().completion()) && self.work_domain==self.original().work.domain_id() && self.ports@==self.original().ports@ && self.origin==self.original().origin && self.program().valid() && self.ports.len()==self.program().code().len() && self.program().code()==self.original().function@.code()
            && self.succeeded==(self.original().result.is_ok() && self.original().result->Ok_0.failure.is_none())
            && inputs::captured(self.inputs@,self.original().result)
            && self.original().completed() && self.original().episode_interval() && self.original().effects_before_return()
            && (self.original().result.is_ok() ==> self.original().result->Ok_0.witnessed()
                && self.original().result->Ok_0.recovery_history() && self.original().result->Ok_0.interpreted(self.program().code())
                && transport::steps(self.program().code(),self.original().result->Ok_0)
                && (forall|i:int|0<=i<self.original().result->Ok_0.steps.len() ==> Some((#[trigger] self.original().result->Ok_0.steps@[i]).pc)==super::next(self.program().code().len(),self.original().result->Ok_0.steps@.take(i)))
                && (self.original().result->Ok_0.failure.is_none() ==> super::next(self.program().code().len(),self.original().result->Ok_0.steps@).is_none()))
    }
    pub closed spec fn stream_identity(&self)->std::sync::Arc<crate::reversible_value::joint::identity::AllocationIdentity> {self.stamp.stream}
    pub closed spec fn call_position(&self)->Option<u64> {self.stamp.revision}
    /// The success flag is captured at the actual invocation return.
    pub fn succeeded(&self)->(out:bool)
        requires self.wf(),ensures out==(self.original().result.is_ok() && self.original().result->Ok_0.failure.is_none()),
    {self.succeeded}
    /// Inspect the complete body, including branches that were not visited.
    pub fn is_controlled(&self)->(out:bool)
        requires self.wf(),ensures out==self.program().controlled(),
    {self.function.is_controlled()}
    /// Membership comes from retained real instructions, including their exact PCs.
    pub open spec fn visited(&self,pc:usize)->bool {
        self.original().result.is_ok() && exists|i:int|0<=i<self.original().result->Ok_0.steps.len()
            && (#[trigger] self.original().result->Ok_0.steps@[i]).pc==pc
    }
    #[verifier::rlimit(12)]
    #[verifier::spinoff_prover]
    pub fn visits(&self,pc:usize)->(out:bool)
        requires self.wf(),ensures out==self.visited(pc),
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);hide(Source::wf);
        proof {self.facts();}
        let mut i=0;
        while i<self.inputs.len()
            invariant self.wf(),inputs::captured(self.inputs@,self.original().result),i<=self.inputs.len(),forall|j:int|0<=j<i ==> (#[trigger] self.inputs@[j]).source().pc!=pc,
            decreases self.inputs.len()-i,
        {
            if self.inputs[i].pc()==pc {assert(self.original().result->Ok_0.steps@[i as int].pc==pc);return true;}i+=1;
        }
        proof {
            if self.original().result.is_ok() {
                assert forall|j:int|0<=j<self.original().result->Ok_0.steps.len() implies
                    (#[trigger] self.original().result->Ok_0.steps@[j]).pc!=pc by {assert(self.inputs@[j].source()==self.original().result->Ok_0.steps@[j]);}
            }
        }
        false
    }
    pub fn position(&self)->(out:Option<u64>)
        requires self.wf(),ensures out==self.call_position(),
            match out {Some(n)=>n as nat==self.original().completion().event().after->Recipes_state.revision,None=>self.original().completion().event().after->Recipes_state.revision>u64::MAX},
    {self.stamp.revision}
    pub proof fn facts(&self) requires self.wf(),ensures self.wf(),self.original().completed(),self.program().valid(),inputs::captured(self.input_spec(),self.original().result),
        self.original().result.is_ok() ==> transport::steps(self.program().code(),self.original().result->Ok_0), {}
    /// Capture the complete native/control source after this actual invocation.
    /// Persistent receipt comparison establishes coverage under the real Journal
    /// lock; the caller supplies no transcript or chronological-prefix premise.
    pub fn bind_control<P,H,M>(&self,runtime:&NativeRuntime<P,H,Slot<T,M>>)
        ->(out:Result<crate::lifecycle_state::native::runtime::control_source::Capture<Slot<T,M>>,crate::lifecycle_state::native::runtime::control_source::Error>)
        requires self.wf(),runtime.wf(),runtime.journal_spec()==self.original().completion().journal(),
        ensures out.is_ok()==(runtime.recording_status()==crate::lifecycle_state::native::runtime::control_source::Status::Recording),
            out.is_ok() ==> out->Ok_0.source.certified() && out->Ok_0.source.cut()==out->Ok_0.cut
                && out->Ok_0.cut.joint_spec().covers(&self.original().completion()),
    {
        let cut=runtime.publication_snapshot_following(Tracked(self.completion.borrow()));
        let source=runtime.bind_control_source(&cut)?;
        Ok(crate::lifecycle_state::native::runtime::control_source::Capture {cut,source})
    }
    pub fn ports(&self)->(out:&[Port]) requires self.wf(),ensures out@==self.original().ports@, {self.ports.as_slice()}
    /// These operands come from retained inverses of this actual invocation.
    pub fn inputs(&self)->(out:&[inputs::Input<T>])
        requires self.wf(),ensures out@==self.input_spec(),inputs::captured(out@,self.original().result),forall|i:int|0<=i<out.len() ==> (#[trigger] out@[i]).wf(),
    {self.inputs.as_slice()}
    /// Seed an actual recorded step and derive its primitive domain/result
    /// from the source contract. The caller supplies no desired input or trace.
    pub fn seed_input(&self,index:usize,journal:&crate::reversible_value::joint::Journal)->(out:Result<inputs::Seed<T>,inputs::SeedError>)
        requires self.wf(),
        ensures (out==Err(inputs::SeedError::MissingStep))==(self.original().result.is_err()
                || index>=self.original().result->Ok_0.steps.len()),
            out.is_ok() ==> self.original().result.is_ok() && index<self.original().result->Ok_0.steps.len()
                && out->Ok_0.journal()==*journal
                && inputs::initializes(self.program().code(),self.original().result->Ok_0.steps@[index as int],out->Ok_0),
    {
        if index>=self.inputs.len() {return Err(inputs::SeedError::MissingStep);}
        let input=&self.inputs[index];let seed=input.seed(journal)?;
        proof {input.seeded_operation(self.program().code(),&seed);}
        Ok(seed)
    }
    pub fn source_origin(&self)->(out:crate::action_ledger::ActionTicket) requires self.wf(),ensures out==self.original().origin,
    {self.origin}
    fn original_ports(&self)->(out:&[Port]) ensures out@==self.ports@, {self.ports.as_slice()}
}
impl<P,H,E:ScalarEffect+Copy,T:?Sized,M> NativeRuntime<Body<P,Function<E,T>>,H,Slot<T,M>> {
    /// Explicitly retain replay inputs around the existing recorded root path.
    /// Successful-prefix failures are captured too; they are not relabeled as
    /// successful source executions.
    #[verifier::rlimit(30)]
    pub fn run_replayable_root<C,G,A,R,X>(&mut self,id:usize,execution:Owner<C,G,A,R,T,M,X>)->(out:CaptureOutcome<C,G,A,R,T,M,X,E>)
        requires old(self).wf(),execution.wf(),
        ensures final(self).wf(),out.0.wf(),final(self).registry()==old(self).registry(),
            final(self).journal_spec()==old(self).journal_spec(),
            out.1.is_ok() ==> out.1->Ok_0.source.wf() && out.1->Ok_0.source.original()==out.1->Ok_0.report
                && out.1->Ok_0.report.completion().journal()==old(self).journal_spec()
                && out.1->Ok_0.report.origin.id==id
                && out.0.baseline().origin()==Some(out.1->Ok_0.report.origin)
                && (out.1->Ok_0.report.result.is_ok() ==> super::retained(out.1->Ok_0.report.result->Ok_0.steps@,out.0.baseline(),0,execution.cleanup_state().queues()[0].slots().len()))
                && out.1->Ok_0.report.retained_recovery(out.0.baseline(),0,execution.cleanup_state().queues()[0].slots().len()),
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
        let saved=match self.registration(id) {
            Some(recipe)=>match recipe.payload_ref() {
                Body::Managed(function)=>Some((function.duplicate(),copy_ports(recipe.dependencies()),recipe.provisions_vec(),recipe.realm_context(),recipe.parent())),
                _=>None,
            },None=>None,
        };
        let environment=match (&saved,execution.native()) {
            (Some(saved),Some(episode))=>Some(environment::Environment::capture(episode,saved.1.as_slice())),
            _=>None,
        };
        let owned=match (&saved,execution.native()) {
            (Some(saved),Some(episode))=>Some(environment::Environment::capture(episode,saved.2.as_slice())),
            _=>None,
        };
        let (owner,result)=self.run_recorded_root(id,execution);
        match result {
            Err(e)=>(owner,Err(e)),
            Ok(report)=>{
                let (function,dependencies,provisions,realms,parent)=match saved {Some(s)=>s,None=>{assert(false);panic!("certified managed registration")}};
                proof {if report.result.is_ok() {transport::derive(report.function@.code(),report.result->Ok_0,report.ports@,owner.baseline().value_state().unwrap());}}
                proof {reveal(super::Report::recovery_history);}
                proof {if report.result.is_ok() {inputs::selection_facts(function.code(),report.result->Ok_0,report.ports@,owner.baseline().value_state().unwrap());}}
                let inputs=inputs::capture(owner.execution(),0,&report.result,Ghost(execution.cleanup_state().queues()[0].slots().len()));
                let succeeded=match &report.result {Ok(actual)=>actual.succeeded(),Err(_)=>false};
                proof {
                    owner.facts();
                    if environment.is_some() {
                        assert(owner.baseline().wf());
                        assert(owner.baseline().origin()==Some(report.origin));
                        assert(environment.unwrap().origin()==report.origin);
                        assert(environment.unwrap().work()==report.work.domain_id());
                    }
                }
                let source=Source {component_word:None,finalized:None,parent,environment,owned,succeeded,function,dependencies,provisions,realms,ports:report.ports.clone(),origin:report.origin,work_domain:report.work.domain(),stamp:order::CallPosition::new(self.recipe_revision(),self.recipe_identity()),inputs,report:Ghost(report),completion:Tracked(report.completion_witness().duplicate())};
                assert(source.wf());
                (owner,Ok(Captured {source,report}))
            },
        }
    }
}
pub type ManagedRuntime<P,H,E,T,M> = NativeRuntime<Body<P,Function<E,T>>,H,Slot<T,M>>;
pub type TargetOutcome<H,C,G,A,R,T,M,X,E> = Result<TargetRun<C,G,A,R,T,M,X,E>,StartError<H>>;
pub struct Destination<H> {pub parent:Option<usize>,pub anchor:Port,pub host:H,pub work_domain:u64}
/// Binding/Begin failures leave an inactive target registration, named by id.
/// Registration failure returns the host to the caller. No rollback is implied.
#[derive(Debug)]
pub enum StartError<H> {ExternalEffect {host:H},ReusedDomain {host:H},Registration {error:Error,host:H},Binding {id:usize},Begin {id:usize,error:Error}}
pub struct TargetRun<C,G,A,R,T:?Sized,M,X,E> {
    pub id:usize,pub owner:RecordedExecution<C,G,A,R,T,M,X>,pub report:Result<RegisteredReport<E,T>,AdmissionError>,
    #[allow(dead_code)]
    pub offset:Ghost<nat>,
    pub inputs:Vec<inputs::Input<T>>,
}
impl<C,G,A,R,T:?Sized,M,X,E:ScalarEffect> TargetRun<C,G,A,R,T,M,X,E> {
    pub(crate) proof fn input_facts(&self,source:&Source<E,T>)
        requires self.from_source(source),self.report.is_ok(),
        ensures inputs::captured(self.inputs@,self.report->Ok_0.result),
            forall|i:int|0<=i<self.inputs.len() ==> (#[trigger] self.inputs@[i]).wf(),
            self.report->Ok_0.result.is_ok() ==> forall|i:int|0<=i<self.report->Ok_0.result->Ok_0.steps.len() ==> (#[trigger] self.report->Ok_0.result->Ok_0.steps@[i]).recorded_values(),
    {
        assert forall|i:int|0<=i<self.report->Ok_0.result->Ok_0.steps.len() && self.report->Ok_0.result.is_ok() implies (#[trigger] self.report->Ok_0.result->Ok_0.steps@[i]).recorded_values() by {self.inputs@[i].provenance();}
    }
    pub open spec fn from_source(&self,source:&Source<E,T>)->bool {
        self.owner.wf() && (self.report.is_ok() ==> {
            let r=self.report->Ok_0;let core=self.owner.baseline();
            &&& inputs::captured(self.inputs@,r.result)
            &&& r.completed() && r.episode_interval() && r.effects_before_return()
            &&& r.function@.code()==source.program().code() && r.ports@==source.original().ports@
            &&& r.origin.id==self.id && r.work.domain_id()==core.work_state().domain_id()
            &&& r.start().owner().owns(&core) && core.execution_journal()==Some(r.completion().journal())
            &&& self.owner.recovery_boundary().is_some() && self.owner.recovery_boundary().unwrap().same(&r.completion())
            &&& r.result.is_ok() ==> core.value_state().is_some()
                && r.result->Ok_0.certified(source.program().code(),r.ports@,core.value_state().unwrap())
                && r.result->Ok_0.interpreted(source.program().code()) && r.result->Ok_0.witnessed()
                && transport::steps(source.program().code(),r.result->Ok_0)
                && r.result->Ok_0.covered_by(r.completion())
                && r.result->Ok_0.registered(core.cleanup_state().link(),0)
                && super::retained(r.result->Ok_0.steps@,core,0,self.offset@)
        })
    }
}
impl<E:ScalarEffect+Copy,T:?Sized> Source<E,T> {
    /// Refuse external callback instructions before target registration, then
    /// use the original source instantiation and original root/Child interpreter.
    pub fn instantiate_controlled<P,H,C,G,A,R,M,X>(&self,runtime:&mut ManagedRuntime<P,H,E,T,M>,destination:Destination<H>)
        ->(out:TargetOutcome<H,C,G,A,R,T,M,X,E>)
        requires self.wf(),old(runtime).wf(),
        ensures final(runtime).wf(),final(runtime).journal_spec()==old(runtime).journal_spec(),
            !self.program().controlled() ==> out.is_err() && out->Err_0 is ExternalEffect && *final(runtime)==*old(runtime),
            out.is_ok() ==> self.program().controlled() && out->Ok_0.from_source(self) && out->Ok_0.report.is_ok(),
            out.is_ok() && out->Ok_0.report->Ok_0.result.is_ok() ==> out->Ok_0.report->Ok_0.result->Ok_0.no_scalar_interference(),
    {
        if !self.is_controlled() {return Err(StartError::ExternalEffect {host:destination.host});}
        assert(self.program().controlled());
        let result=self.instantiate(runtime,destination);
        proof {
            if result.is_ok() {
                let target=result->Ok_0;let report=target.report->Ok_0;
                if report.result.is_ok() {report.result->Ok_0.controlled_execution(self.program(),report.ports@,target.owner.baseline().value_state().unwrap());}
            }
        }
        result
    }
    /// Allocate a real target registration, Begin a new owner and execute the
    /// preserved program through the original managed interpreter. Target
    /// services come from the target provider capture, never the source owner.
    #[verifier::rlimit(20)]
    #[verifier::spinoff_prover]
    pub fn instantiate<P,H,C,G,A,R,M,X>(&self,runtime:&mut ManagedRuntime<P,H,E,T,M>,destination:Destination<H>)
        ->(out:TargetOutcome<H,C,G,A,R,T,M,X,E>)
        requires self.wf(),old(runtime).wf(),
        ensures final(runtime).publications()==old(runtime).publications(),
            out.is_ok() ==> out->Ok_0.owner.baseline().value_state().is_some()
                && out->Ok_0.owner.baseline().value_state().unwrap().capture().sources==crate::lifecycle_state::services::capture::sources(old(runtime).publications().entries())
                && out->Ok_0.owner.baseline().value_state().unwrap().provisions()==self.provision_ports(),
            final(runtime).wf(),final(runtime).journal_spec()==old(runtime).journal_spec(),
            out.is_err() && out->Err_0 is ReusedDomain ==> *final(runtime)==*old(runtime),
            out.is_ok() ==> out->Ok_0.report.is_ok(),
            out.is_ok() ==> out->Ok_0.from_source(self),
            out.is_ok() ==> out->Ok_0.report->Ok_0.completion().journal()==old(runtime).journal_spec(),
            out.is_ok() ==> out->Ok_0.report->Ok_0.work.domain_id()==destination.work_domain,
            out.is_ok() ==> out->Ok_0.report->Ok_0.work!=self.original().work,
            out.is_ok() ==> out->Ok_0.report->Ok_0.origin!=self.original().origin,
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
        if runtime.lifecycle().domain()==self.origin.domain || destination.work_domain==self.work_domain {
            return Err(StartError::ReusedDomain {host:destination.host});
        }
        let definition=PluginDefinition::new(keys(self.dependencies.as_slice()),keys(self.provisions.as_slice()),Body::Managed(self.function.duplicate()));
        let id=match runtime.register(destination.parent,self.realms.as_map(),destination.anchor,definition,destination.host) {
            Ok(id)=>id,Err((error,_,host))=>return Err(StartError::Registration {error,host}),
        };
        let recipe=match runtime.registration(id) {Some(recipe)=>recipe,None=>{assert(false);panic!("certified managed registration")}};
        let ports=match self.function.bind(recipe) {Ok(p)=>p,Err(_)=>return Err(StartError::Binding {id})};
        // Matching the complete resolved dependency list also rejects an
        // inherited/aliased environment that cannot be reproduced here.
        if !same_ports(recipe.dependencies(),self.dependencies.as_slice())
            || !same_ports(recipe.provisions(),self.provisions.as_slice())
            || !same_ports(ports.as_slice(),self.original_ports()) {
            return Err(StartError::Binding {id});
        }
        proof {
            reveal(Function::valid);
            assert(ports@==self.original().ports@);
            assert(recipe.payload() is Managed);
            assert(recipe.payload()->Managed_0.code()==self.program().code());
            assert(recipe.payload()->Managed_0.valid());
            self.function.equal_binding(recipe.payload()->Managed_0,*recipe,ports@);
            assert(recipe.payload()->Managed_0.bound(ports@,*recipe));
        }
        let execution:Owner<C,G,A,R,T,M,X>=match runtime.begin_managed_execution(id,destination.work_domain) {
            Ok(owner)=>owner,Err(error)=>return Err(StartError::Begin {id,error}),
        };
        proof {assert(runtime.managed_invocation_ready(id,&execution));}
        let ghost offset=execution.cleanup_state().queues()[0].slots().len();
        let (owner,report)=runtime.run_recorded_root(id,execution);
        assert(report.is_ok());
        proof {
            if report.is_ok() {
                if report->Ok_0.result.is_ok() {transport::derive(report->Ok_0.function@.code(),report->Ok_0.result->Ok_0,report->Ok_0.ports@,owner.baseline().value_state().unwrap());}
                let actual=report->Ok_0.ports@;
                assert forall|i:int|0<=i<ports.len() implies actual[i]==ports@[i] by {
                    let recipe=runtime.registry().entries()[id].recipe();
                    let a=choose|j:int|0<=j<recipe.dependencies_spec().len() && recipe.dependencies_spec()[j]==actual[i]
                        && forall|k:int|0<=k<j ==> recipe.dependencies_spec()[k].key!=actual[i].key;
                    let b=choose|j:int|0<=j<recipe.dependencies_spec().len() && recipe.dependencies_spec()[j]==ports@[i]
                        && forall|k:int|0<=k<j ==> recipe.dependencies_spec()[k].key!=ports@[i].key;
                    if a<b {assert(recipe.dependencies_spec()[a].key!=ports@[i].key);} else if b<a {assert(recipe.dependencies_spec()[b].key!=actual[i].key);}
                }
                assert(actual =~= ports@);
            }
        }
        proof {
            let r=report->Ok_0;let core=owner.baseline();
            assert(r.completed() && r.episode_interval() && r.effects_before_return());
            assert(r.function@.code()==self.program().code() && r.ports@==self.original().ports@);
            assert(r.origin.id==id && r.work.domain_id()==core.work_state().domain_id());
            assert(r.start().owner().owns(&core) && core.execution_journal()==Some(r.completion().journal()));
            assert(owner.recovery_boundary().is_some() && owner.recovery_boundary().unwrap().same(&r.completion()));
            if r.result.is_ok() {
                r.result->Ok_0.cover_return(r.completion());
                assert(core.value_state().is_some() && r.result->Ok_0.certified(self.program().code(),r.ports@,core.value_state().unwrap()));
                assert(r.result->Ok_0.interpreted(self.program().code()) && r.result->Ok_0.witnessed() && transport::steps(self.program().code(),r.result->Ok_0));
                assert(r.result->Ok_0.registered(core.cleanup_state().link(),0));
                assert(super::retained(r.result->Ok_0.steps@,core,0,offset));
            }
        }
        proof {if report->Ok_0.result.is_ok() {reveal(super::Report::recovery_history);}}
        proof {if report->Ok_0.result.is_ok() {inputs::selection_facts(self.program().code(),report->Ok_0.result->Ok_0,report->Ok_0.ports@,owner.baseline().value_state().unwrap());}}
        let inputs=inputs::capture(owner.execution(),0,&report.as_ref().unwrap().result,Ghost(offset));
        Ok(TargetRun {id,owner,report,offset:Ghost(offset),inputs})
    }
}
}

#[path = "managed_replay_protected.rs"]
pub mod protected;

#[path = "managed_replay_typed_protected.rs"]
pub(crate) mod typed_protected;

#[path = "managed_replay_typed_correspondence.rs"]
pub mod typed_correspondence;

#[path = "managed_replay_typed_tracker.rs"]
pub(crate) mod typed_tracker;

#[path = "managed_replay_mixed.rs"]
pub mod mixed;

#[path = "managed_replay_archive.rs"]
pub mod archive;

#[path = "managed_replay_session.rs"]
pub mod session;

#[path = "managed_replay_services.rs"]
pub mod services;

#[path = "managed_replay_active.rs"]
pub(crate) mod active;
