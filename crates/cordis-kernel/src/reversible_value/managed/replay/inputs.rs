//! Retain actual operands from the inverses still owned by the executing host.
//! Capturing never rereads a mutable object, consumes an inverse or fabricates
//! its pre-state. Fresh resources are individual seeds, not an alias replay.
#[cfg(verus_keep_ghost)]
use super::super::semantics;
use super::super::{AdmissionError, Owner, Report, ResultStep, Step};
use crate::cleanup_groups::payload::Cleanup;
use crate::lifecycle_state::registration::shared_child::ChildCleanup;
use crate::reversible_value::{joint, payload::SharedPayload, ReversibleValue, ValueState};
use std::sync::Arc;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
/// Runtime data retained only by explicit replay capture. Payload head/depth
/// describe the source; a freshly allocated target has its own version history.
pub enum Operand<T:?Sized> {Scalar(ValueState),Payload {value:Arc<T>,head:u64,depth:u64}}
impl<T:?Sized> Operand<T> {
    pub open spec fn value(&self)->semantics::Value<T> {
        match self {Self::Scalar(v)=>semantics::Value::Scalar(*v),Self::Payload {value,head,depth}=>
            semantics::Value::Payload(crate::reversible_value::payload::State {value:*value,head:*head,depth:*depth})}
    }
}
#[allow(dead_code)] // Step and its provenance are erased, operands are real.
pub struct Input<T:?Sized> {
    scalar_selection:Option<crate::reversible_value::slot::Capture>,
    payload_owner:Option<SharedPayload<T>>,
    payload_history:Tracked<Option<crate::reversible_value::history::Witness<crate::reversible_value::payload::State<T>>>>,
    payload_receipt:Tracked<Option<joint::Receipt>>,payload_head:Option<u64>,scalar_after:Option<ValueState>,identity:Arc<joint::identity::AllocationIdentity>,pc:usize,token:usize,operand:Operand<T>,step:Ghost<Step<T>>}
impl<T:?Sized> Input<T> {
    pub closed spec fn identity_spec(&self)->Arc<joint::identity::AllocationIdentity> {self.identity}
    pub open spec fn namespace(&self,namespace:vstd::resource::Loc)->bool {
        self.identity_spec().namespace()==namespace && (self.source().result is Scalar ==> self.source().result->Scalar_write.binding.capture_spec().slot().journal_spec().identity_namespace()==namespace)
    }
    pub closed spec fn source(&self)->Step<T> {self.step@}
    pub closed spec fn value(&self)->semantics::Value<T> {self.operand.value()}
    pub closed spec fn wf(&self)->bool {
        self.identity.wf() && self.identity.address()==self.source().address()
            && self.pc==self.source().pc && self.token==self.source().token()
            && self.value()==self.source().before() && self.source().recorded_values()
            && match self.source().result {
                ResultStep::Scalar {write,inverse}=>self.scalar_selection.is_some() && self.scalar_selection.unwrap().wf()
                    && self.scalar_selection.unwrap().slot()==write.binding.capture_spec().slot()
                    && self.scalar_selection.unwrap().value_spec()==write.binding.capture_spec().value_spec()
                    && self.scalar_selection.unwrap().value_spec().journal_spec()==self.source().address().journal && self.scalar_selection.unwrap().value_spec().object().key==self.source().address().key && self.scalar_selection.unwrap().revision_spec()==write.binding.capture_spec().revision_spec()
                    && self.payload_owner.is_none() && self.payload_history@.is_none() && self.payload_receipt@.is_none() && self.payload_head.is_none()
                    && self.scalar_after==Some(inverse@.state().after),
                ResultStep::Payload(a)=>self.scalar_selection.is_none() && self.payload_owner==Some(a.inverse().owner()) && self.scalar_after.is_none() && self.payload_history@.is_some() && self.payload_receipt@.is_some() && self.payload_head==Some(a.inverse().after().state().head)
                    && self.payload_history@.unwrap().wf() && self.payload_history@.unwrap().source()==a.inverse().owner().source()
                    && self.payload_history@.unwrap().events()==a.inverse().after().states
                    && self.payload_receipt@.unwrap().wf() && self.payload_receipt@.unwrap().same(&a.inverse().after().commit),
            }
    }
    /// Duplicate retained observations, not inverse ownership or user payloads.
    // Explicit branches preserve the erased receipt and owner relations.
    #[allow(clippy::manual_map)]
    pub fn duplicate(&self)->(out:Self)
        requires self.wf(),ensures out.wf(),out.source()==self.source(),out.identity_spec()==self.identity_spec(),
    {
        hide(joint::valid);hide(joint::step);
        let operand=match &self.operand {Operand::Scalar(v)=>Operand::Scalar(*v),Operand::Payload {value,head,depth}=>Operand::Payload {value:value.clone(),head:*head,depth:*depth}};
        let tracked history=match self.payload_history.borrow() {Some(h)=>Some(h.duplicate()),None=>None};
        let tracked receipt=match self.payload_receipt.borrow() {Some(r)=>Some(r.duplicate()),None=>None};
        Input {scalar_selection:match &self.scalar_selection {Some(c)=>Some(c.duplicate()),None=>None},payload_owner:match &self.payload_owner {Some(owner)=>Some(owner.clone()),None=>None},payload_history:Tracked(history),payload_receipt:Tracked(receipt),payload_head:self.payload_head,scalar_after:self.scalar_after,identity:self.identity.clone(),pc:self.pc,token:self.token,operand,step:self.step}
    }
    pub fn selected_slot(&self)->(out:Option<&crate::reversible_value::slot::Capture>)
        requires self.wf(),ensures out.is_some()==(self.source().result is Scalar),out.is_some() ==> out.unwrap().wf()
            && out.unwrap().slot()==self.source().result->Scalar_write.binding.capture_spec().slot()
            && out.unwrap().revision_spec()==self.source().result->Scalar_write.binding.capture_spec().revision_spec()
            && out.unwrap().value_spec()==self.source().result->Scalar_write.binding.capture_spec().value_spec()
            && out.unwrap().value_spec().journal_spec()==self.source().address().journal && out.unwrap().value_spec().object().key==self.source().address().key,
    {self.scalar_selection.as_ref()}
    pub(crate) fn scalar_output(&self)->(out:Option<ValueState>)
        requires self.wf(),ensures out.is_some()==(self.source().result is Scalar),
            out.is_some() ==> semantics::Value::Scalar(out.unwrap())==self.source().after(),
    {self.scalar_after}
    pub fn payload_after_head(&self)->(out:Option<u64>)
        requires self.wf(),
        ensures out.is_some()==(self.source().result is Payload),
            out.is_some() ==> out.unwrap()==self.source().result->Payload_0.inverse().after().revision && out.unwrap()>0,
    {hide(joint::valid);hide(joint::step);proof {if self.source().result is Payload {self.source().result->Payload_0.inverse().source_history();}}self.payload_head}
    pub proof fn provenance(&self)
        requires self.wf(),
        ensures self.source().recorded_values(),self.value()==self.source().before(),
            self.identity_spec().wf(),self.identity_spec().address()==self.source().address(),
    { }
    /// Compare actual retained states, including scalar inverse depth. Typed
    /// equality is derived from authentic history agreement, never T::eq.
    pub fn continues(&self,previous:&Self)->(out:bool)
        requires self.wf(),previous.wf(),self.source().address()==previous.source().address(),
            self.identity_spec().namespace()==previous.identity_spec().namespace(),
            self.identity_spec().number_spec().is_some(),previous.identity_spec().number_spec().is_some(),
        ensures out==(self.source().before()==previous.source().after()),
    {
        hide(joint::valid);hide(joint::step);
        match (&self.operand,&previous.operand) {
            (Operand::Scalar(current),Operand::Scalar(_))=>{
                let after=match previous.scalar_after {Some(state)=>state,None=>{assert(false);panic!("retained scalar output")}};
                current.value==after.value && current.depth==after.depth
            },
            (Operand::Payload {..},Operand::Payload {..})=>match self.continues_payload(previous) {
                Some(same)=>same,None=>{assert(false);panic!("named payload continuity")},
            },
            _=>false,
        }
    }
    pub fn identity(&self)->(out:&Arc<joint::identity::AllocationIdentity>)
        requires self.wf(),ensures out.wf(),out.address()==self.source().address(),*out==self.identity_spec(),
    {&self.identity}
    pub fn pc(&self)->(out:usize) requires self.wf(),ensures out==self.source().pc, {self.pc}
    pub fn token(&self)->(out:usize) requires self.wf(),ensures out==self.source().token(), {self.token}
    pub fn operand(&self)->(out:&Operand<T>) requires self.wf(),ensures out.value()==self.source().before(), {&self.operand}
}
pub open spec fn capturable<T:?Sized>(step:Step<T>)->bool {
    step.recorded_values() && match step.result {
        ResultStep::Scalar {write,..}=>write.binding.wf() && write.binding.capture_spec().value_spec().journal_spec()==step.address().journal && write.binding.capture_spec().value_spec().object().key==step.address().key,
        _=>true,
    }
}
pub(crate) proof fn selection_facts<E:crate::reversible_value::effect::ScalarEffect,T:?Sized,M>(code:Seq<super::super::Call<E,T>>,report:Report<T>,ports:Seq<crate::Port>,episode:crate::lifecycle_state::services::NativeEpisode<super::super::Slot<T,M>>)
    requires report.certified(code,ports,episode),forall|i:int|0<=i<report.steps.len() ==> (#[trigger] report.steps@[i]).recorded_values(),
    ensures forall|i:int|0<=i<report.steps.len() ==> capturable(#[trigger] report.steps@[i]),
{
    reveal(super::super::Step::corresponds);
    assert forall|i:int|0<=i<report.steps.len() implies capturable(#[trigger] report.steps@[i]) by {
        let s=report.steps@[i];assert(s.corresponds(code[s.pc as int],ports[s.pc as int],episode));
    }
}
pub open spec fn captured<T:?Sized>(inputs:Seq<Input<T>>,result:Result<Report<T>,AdmissionError>)->bool {
    match result {Err(_)=>inputs.len()==0,Ok(report)=>inputs.len()==report.steps.len()
        && forall|i:int|0<=i<inputs.len() ==> (#[trigger] inputs[i]).wf() && inputs[i].source()==report.steps@[i]}
}
fn scalar_input<T:?Sized>(inverse:&crate::reversible_value::Inverse,selection:&crate::reversible_value::slot::Capture,pc:usize,token:usize,Ghost(step):Ghost<Step<T>>)->(out:Input<T>)
    requires capturable(step),step.result is Scalar,selection.wf(),*selection==step.result->Scalar_write.binding.capture_spec(),step.result->Scalar_inverse@==*inverse,pc==step.pc,token==step.token(),
    ensures out.wf(),out.source()==step,
{
    hide(joint::valid);hide(joint::step);
    let identity=inverse.replay_identity();let operand=Operand::Scalar(inverse.replay_input());
    Input {scalar_selection:Some(selection.duplicate()),payload_owner:None,payload_history:Tracked(None),payload_receipt:Tracked(None),payload_head:None,scalar_after:Some(inverse.replay_output()),identity,pc,token,operand,step:Ghost(step)}
}
fn payload_input<T:?Sized>(inverse:&crate::reversible_value::payload::restoration::Inverse<T>,pc:usize,token:usize,Ghost(step):Ghost<Step<T>>)->(out:Input<T>)
    requires step.recorded_values(),step.result is Payload,step.result->Payload_0.inverse()==*inverse,pc==step.pc,token==step.token(),
    ensures out.wf(),out.source()==step,
{
    hide(joint::valid);hide(joint::step);proof {inverse.provenance();}
    let identity=inverse.replay_identity();let (value,head,depth)=inverse.replay_input();
    Input {scalar_selection:None,payload_owner:Some(inverse.retained_owner()),payload_history:Tracked(Some(inverse.history_witness())),payload_receipt:Tracked(Some(inverse.receipt())),payload_head:Some(inverse.replay_head()),scalar_after:None,identity,pc,token,operand:Operand::Payload {value,head,depth},step:Ghost(step)}
}
fn capture_one<C,G,A,R,T:?Sized,M,X>(owner:&Owner<C,G,A,R,T,M,X>,id:usize,step:&Step<T>)->(out:Input<T>)
    requires owner.cleanup_state().live(id),step.token()<owner.cleanup_state().queues()[id].slots().len(),
        step.in_slot(owner.cleanup_state().queues()[id].slots()[step.token() as int]),capturable(*step),
    ensures out.wf(),out.source()==*step,
{
    let token=match &step.result {ResultStep::Scalar {write,..}=>write.admission.token,ResultStep::Payload(a)=>a.token()};
    let retained=match owner.groups().retained(id,token) {Some(action)=>action,None=>{assert(false);panic!("retained invocation inverse")}};
    match &step.result {
        ResultStep::Scalar {write,..}=>match retained {
            ChildCleanup::Value(inverse)=>scalar_input(inverse,write.binding.capture(),step.pc,token,Ghost(*step)),
            _=>{assert(false);panic!("retained scalar inverse")},
        },
        ResultStep::Payload(_)=>match retained {
            ChildCleanup::Callback(Cleanup::Payload {inverse,..})=>payload_input(inverse,step.pc,token,Ghost(*step)),
            _=>{assert(false);panic!("retained payload inverse")},
        },
    }
}
/// Only called while the actual report's inverses remain in their queue slots.
/// Even a failed call contributes every successful-prefix operand.
pub(crate) fn capture<C,G,A,R,T:?Sized,M,X>(owner:&Owner<C,G,A,R,T,M,X>,id:usize,result:&Result<Report<T>,AdmissionError>,Ghost(offset):Ghost<nat>)
    ->(out:Vec<Input<T>>)
    requires result.is_ok() ==> super::super::retained(result->Ok_0.steps@,*owner,id,offset)
        && forall|i:int|0<=i<result->Ok_0.steps.len() ==> capturable(#[trigger] result->Ok_0.steps@[i]),
    ensures captured(out@,*result),
{
    let mut out:Vec<Input<T>>=Vec::new();
    if let Ok(report)=result {
        let mut i=0;
        while i<report.steps.len()
            invariant i<=report.steps.len(),out.len()==i,
                super::super::retained(report.steps@,*owner,id,offset),
                forall|k:int|0<=k<report.steps.len() ==> capturable(#[trigger] report.steps@[k]),
                forall|k:int|0<=k<out.len() ==> (#[trigger] out@[k]).wf() && out@[k].source()==report.steps@[k],
            decreases report.steps.len()-i,
        {
            let step=&report.steps[i];out.push(capture_one(owner,id,step));i+=1;
        }
    }out
}

#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum SeedError {MissingStep,OutstandingScalarHistory}
pub enum Seed<T:?Sized> {Scalar(ReversibleValue),Payload(SharedPayload<T>)}
impl<T:?Sized> Seed<T> {
    pub open spec fn initial(&self)->semantics::Value<T> {
        match self {Self::Scalar(v)=>semantics::Value::Scalar(v.initial()),Self::Payload(v)=>
            semantics::Value::Payload(crate::reversible_value::payload::State {value:v.initial(),head:0,depth:0})}
    }
    pub open spec fn journal(&self)->joint::Journal {match self {Self::Scalar(v)=>v.journal_spec(),Self::Payload(v)=>v.journal_spec()}}
    pub open spec fn address(&self)->crate::reversible_value::service_composition::Address {
        crate::reversible_value::service_composition::Address {journal:self.journal(),key:match self {Self::Scalar(v)=>v.object().key,Self::Payload(v)=>v.key()}}
    }
}
/// Initial-state correspondence and definedness for the preserved primitive.
/// This says nothing about a target object's later mutable state.
pub open spec fn initializes<E:crate::reversible_value::effect::ScalarEffect,T:?Sized>(code:Seq<super::super::Call<E,T>>,source:Step<T>,seed:Seed<T>)->bool {
    source.pc<code.len() && super::transport::values(source.before(),seed.initial()) && {
        let op=semantics::operation(semantics::code(code[source.pc as int].effect,1));
        &&& op(seed.initial()).is_some()
        &&& super::transport::values(source.after(),op(seed.initial()).unwrap().value)
        &&& op(seed.initial()).unwrap().outcome==source.outcome()
        &&& semantics::selected(code[source.pc as int].branch,op(seed.initial()).unwrap().outcome)==source.next
    }
}
impl<T:?Sized> Input<T> {
    /// Allocate a new target object from this actual operand. This does not
    /// publish it, recover a source inverse or rebuild a shared alias graph.
    /// Scalar depth cannot be invented without its outstanding inverse owners.
    pub fn seed(&self,journal:&joint::Journal)->(out:Result<Seed<T>,SeedError>)
        requires self.wf(),
        ensures out.is_ok()==match self.value() {semantics::Value::Scalar(v)=>v.depth==0,_=>true},
            out.is_ok() ==> out->Ok_0.journal()==*journal
                && super::transport::values(self.source().before(),out->Ok_0.initial()),
            out.is_err() ==> out==Err(SeedError::OutstandingScalarHistory),
    {
        match self.seed_following(journal,Tracked(None)) {Ok((seed,_birth))=>Ok(seed),Err(error)=>Err(error)}
    }
    /// The actual allocation returns its birth receipt, ordered after the
    /// bank's preceding allocation. No expected identity or target key is input.
    pub(crate) fn seed_following(&self,journal:&joint::Journal,Tracked(earlier):Tracked<Option<joint::Receipt>>)->(out:Result<(Seed<T>,Tracked<joint::Receipt>),SeedError>)
        requires self.wf(),earlier.is_some() ==> earlier.unwrap().wf() && earlier.unwrap().journal()==*journal,
        ensures out.is_ok()==match self.value() {semantics::Value::Scalar(v)=>v.depth==0,_=>true},
            out.is_ok() ==> out->Ok_0.0.journal()==*journal
                && super::transport::values(self.source().before(),out->Ok_0.0.initial())
                && out->Ok_0.1@.wf() && out->Ok_0.1@.journal()==*journal
                && out->Ok_0.1@.event().key==out->Ok_0.0.address().key
                && out->Ok_0.1@.event().change==joint::Change::Allocate
                && (earlier.is_some() ==> out->Ok_0.1@.follows(&earlier.unwrap())),
            out.is_err() ==> out==Err(SeedError::OutstandingScalarHistory),
    {
        match &self.operand {
            Operand::Scalar(v)=>{
                if v.depth!=0 {return Err(SeedError::OutstandingScalarHistory);}
                let (value,birth)=ReversibleValue::new_in_following(journal,v.value,Tracked(earlier));
                Ok((Seed::Scalar(value),birth))
            },
            Operand::Payload {value,..}=>{
                let (value,birth)=SharedPayload::new_in_following(journal,value.clone(),Tracked(earlier));
                Ok((Seed::Payload(value),birth))
            },
        }
    }
    /// At a supported fresh seed the source instruction is defined, including
    /// its branch outcome. This is a primitive law, not a scheduling theorem:
    /// subsequent sharing, service selection and interference remain separate.
    pub proof fn seeded_operation<E:crate::reversible_value::effect::ScalarEffect>(&self,code:Seq<super::super::Call<E,T>>,seed:&Seed<T>)
        requires self.wf(),super::transport::step(code,self.source()),
            super::transport::values(self.source().before(),seed.initial()),
        ensures initializes(code,self.source(),*seed),
    {
        match code[self.source().pc as int].effect {super::super::Effect::Scalar(_)|super::super::Effect::Kernel(_)=>{},super::super::Effect::Replace(_)=>{}}
    }
}
}

pub mod payload_history;
verus! {
impl<T:?Sized> Input<T> {
    pub fn before_capture(&self)->(out:Option<crate::reversible_value::payload::Capture<T>>)
        requires self.wf(),
        ensures out.is_some()==(self.source().result is Payload),
            out.is_some() ==> out.unwrap().wf() && out.unwrap().owner()==self.source().result->Payload_0.inverse().owner()
                && out.unwrap().observation()==self.source().result->Payload_0.inverse().before(),
    {
        hide(joint::valid);hide(joint::step);
        let (value,head,depth)=match &self.operand {Operand::Payload {value,head,depth}=>(value,*head,*depth),_=>return None};
        let after=self.payload_head.unwrap();
        let ghost inverse=self.source().result->Payload_0.inverse();
        proof {inverse.provenance();inverse.source_history();assert(after>0);}
        let tracked witness=self.payload_history.borrow().tracked_borrow().take(inverse.before().states.len());
        let tracked commit=self.payload_receipt.borrow().tracked_borrow().prefix(inverse.before().commit.events().len());
        proof {assert(witness.events() =~= inverse.before().states);}
        Some(crate::reversible_value::payload::Capture::retained(self.payload_owner.as_ref().unwrap(),after-1,head,depth,value.clone(),Ghost(inverse.before()),Tracked(witness),Tracked(commit)))
    }
    /// The caller supplies the constant from the authentic executed Replace
    /// instruction. Its equality to the recorded after-value is proved from
    /// that instruction's interpretation, never tested using arbitrary T::eq.
    pub(crate) fn after_capture(&self,value:&Arc<T>)->(out:crate::reversible_value::payload::Capture<T>)
        requires self.wf(),self.source().result is Payload,*value==self.source().after()->Payload_0.value,
        ensures out.wf(),out.owner()==self.source().result->Payload_0.inverse().owner(),out.observation()==self.source().result->Payload_0.inverse().after(),
    {
        hide(joint::valid);hide(joint::step);
        let depth=match &self.operand {Operand::Payload {depth,..}=>*depth,_=>{assert(false);panic!("retained typed observation")}};
        let head=self.payload_head.unwrap();let ghost inverse=self.source().result->Payload_0.inverse();
        proof {inverse.provenance();inverse.source_history();}
        crate::reversible_value::payload::Capture::retained(self.payload_owner.as_ref().unwrap(),head,head,depth+1,value.clone(),Ghost(inverse.after()),Tracked(self.payload_history.borrow().tracked_borrow().duplicate()),Tracked(self.payload_receipt.borrow().tracked_borrow().duplicate()))
    }
}
}
