//! Source-derived scalar definedness at a real target capture and landing.
//! Both closed instructions and scalar effects share the atomic input guard.
//! The original native effect path selects the target, executes the computation,
//! checks its owner and retains the inverse. No target-success premise is used.
use super::super::{Call, Effect, Owner, ResultStep, Step};
#[cfg(verus_keep_ghost)]
use super::{super::semantics as s, transport};
use super::{inputs::Operand, Source};
use crate::reversible_value::{
    cursor::StartError, effect::EffectError, effect::ScalarEffect, native_effect,
    payload::SharedPayload, Branch, ValueState,
};
use vstd::prelude::*;

verus! {
/// No state-changing frame for this target between its real read and landing.
/// Changes to other allocations, and rejected attempts, are allowed.
pub open spec fn quiet_input<T,M>(computation:native_effect::Computation<T,M>,landing:crate::reversible_value::joint::Receipt)->bool {
    super::super::recovery::quiet(landing.events(),computation.prepared().cause().at()+1,
        landing.at(),computation.prepared().target().object().key)
}
proof fn unchanged<T,M>(computation:native_effect::Computation<T,M>,landing:crate::reversible_value::joint::Receipt)
    requires computation.wf(),landing.wf(),landing.follows(&computation.prepared().cause()),
        landing.event().key==computation.prepared().target().object().key,
        landing.event().change is Value,quiet_input(computation,landing),
    ensures landing.event().change->Value_event.before()==computation.prepared().expected(),
{
    hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
    computation.provenance();let prepared=computation.prepared();prepared.read_evidence();
    let read=prepared.observation();read.production_state();
    let frames=landing.events();let start=prepared.cause().at()+1;let key=prepared.target().object().key;
    assert(frames.take(start as int)==read.joint_spec().events());
    assert(crate::reversible_value::joint::state_at(frames,start)==read.joint_spec().last());
    super::super::recovery::quiet_record(frames,start,landing.at(),key);
    super::super::recovery::frame_update(frames,landing.at());
    reveal(crate::reversible_value::joint::step);reveal(crate::reversible_value::joint::changes);
}
/// The diagnostic retains an authentic target read; proof data erases.
#[allow(dead_code)]
pub struct InputMismatch {
    pub expected:ValueState,pub observed:ValueState,
    read:Ghost<crate::reversible_value::Snapshot>,
    binding:Ghost<crate::reversible_value::slot::ServiceBinding>,
    receipt:Tracked<crate::reversible_value::joint::Receipt>,
}
impl InputMismatch {
    pub closed spec fn expected_spec(&self)->ValueState {self.expected}
    pub closed spec fn observed_spec(&self)->ValueState {self.observed}
    pub closed spec fn read(&self)->crate::reversible_value::Snapshot {self.read@}
    pub closed spec fn binding(&self)->crate::reversible_value::slot::ServiceBinding {self.binding@}
    pub closed spec fn receipt(&self)->crate::reversible_value::joint::Receipt {self.receipt@}
    pub closed spec fn wf(&self)->bool {
        self.read().certified() && self.observed==self.read().state() && self.expected!=self.observed
            && self.binding().wf() && self.read().source()==self.binding().capture_spec().value_spec().source()
            && self.read().object()==self.binding().capture_spec().value_spec().object()
            && self.read().journal_spec()==self.binding().capture_spec().value_spec().journal_spec()
            && self.receipt().wf() && self.receipt().journal()==self.read().journal_spec()
            && self.receipt().events()==self.read().joint_spec().events()
    }
    pub proof fn read_witness(tracked &self)->(tracked out:&crate::reversible_value::joint::Receipt)
        requires self.wf(),ensures *out==self.receipt(),out.wf(),
    {self.receipt.borrow()}
}
pub enum PrepareError {
    MissingStep,NotScalar,Capture(StartError),
    InputChanged(InputMismatch),
}
#[allow(dead_code)] // Source code/step erase; the computation and branch execute.
pub struct PreparedStep<E,T:?Sized,M> {
    computation:native_effect::Computation<SharedPayload<T>,M>,branch:Branch,pc:usize,
    source:Ghost<Step<T>>,code:Ghost<Seq<Call<E,T>>>,
}
impl<E:ScalarEffect,T:?Sized,M> PreparedStep<E,T,M> {
    pub closed spec fn source(&self)->Step<T> {self.source@}
    pub closed spec fn code(&self)->Seq<Call<E,T>> {self.code@}
    pub closed spec fn computation(&self)->native_effect::Computation<SharedPayload<T>,M> {self.computation}
    pub(super) fn capture_ref(&self)->(out:&native_effect::Capture<SharedPayload<T>,M>)
        requires self.wf(),ensures *out==self.computation().capture(),out.wf(),
            self.computation().prepared().target()==*out.binding().capture_spec().value_spec(),
    {proof {self.computation.provenance();}self.computation.capture_ref()}
    pub closed spec fn wf(&self)->bool {
        self.computation.wf() && transport::step(self.code(),self.source())
            && self.source().before() is Scalar && self.code()[self.source().pc as int].effect.scalar_code().is_some()
            && self.pc==self.source().pc && self.branch==self.code()[self.pc as int].branch
            && self.computation.prepared().code()==self.code()[self.pc as int].effect.scalar_code().unwrap()
            && self.computation.prepared().expected()==self.source().before()->Scalar_0
    }
    pub open spec fn admitted<C,G,A,R,X>(&self,owner:&Owner<C,G,A,R,T,M,X>,id:usize)->bool {
        owner.work_state().accepts() && owner.cleanup_state().acquisition_open(id)
            && self.computation().capture().owner().matches(owner,id)
    }
    /// Execute the preserved operation through the same landing path as the
    /// ordinary interpreter. Source success removes domain/capacity rejection;
    /// actual admission loss and intervening writes remain explicit outcomes.
    pub fn land<C,G,A,R,X>(self,owner:&mut Owner<C,G,A,R,T,M,X>,id:usize)->(out:Result<Step<T>,EffectError>)
        requires self.wf(),old(owner).wf(),
        ensures final(owner).wf(),final(owner).capture()==old(owner).capture(),
            final(owner).value_state()==old(owner).value_state(),
            final(owner).work_state()==old(owner).work_state(),
            final(owner).execution_journal()==old(owner).execution_journal(),
            final(owner).cleanup_state().frame(&old(owner).cleanup_state(),id),
            final(owner).cleanup_state().queues().dom()==old(owner).cleanup_state().queues().dom(),
            final(owner).cleanup_state().domain_ids()==old(owner).cleanup_state().domain_ids(),
            out.is_err() ==> final(owner).same_runtime(old(owner)),
            out.is_ok() || out==Err(EffectError::Closed) || out==Err(EffectError::Interference),
            (out==Err(EffectError::Closed))==!self.admitted(old(owner),id),
            out==Err(EffectError::Closed) ==> *final(owner)==*old(owner),
            self.admitted(old(owner),id) ==> {
                &&& final(owner).value_attempts().appended(&old(owner).value_attempts(),&self.computation().prepared().target())
                &&& final(owner).value_attempts().events().last().follows(&self.computation().prepared().cause())
                &&& out.is_ok()==(final(owner).value_attempts().event().before()==self.source().before()->Scalar_0)
            },
            self.admitted(old(owner),id) && quiet_input(self.computation(),final(owner).value_attempts().events().last()) ==> out.is_ok(),
            out==Err(EffectError::Interference) ==> {
                let receipt=final(owner).value_attempts().events().last();
                &&& crate::reversible_value::attempt::effect_rejection(final(owner).value_attempts().event(),
                    self.computation().prepared().code(),self.source().before()->Scalar_0,EffectError::Interference)
                &&& crate::reversible_value::joint::state_at(receipt.events(),receipt.at())==receipt.events().last().state
                &&& crate::reversible_value::joint::pending_at(receipt.events(),receipt.at())==receipt.events().last().pending
            },
            out.is_ok() ==> {
                let step=out->Ok_0;
                &&& step.pc==self.source().pc && transport::step(self.code(),step)
                &&& step.address()==(crate::reversible_value::service_composition::Address {journal:self.computation().prepared().target().journal_spec(),key:self.computation().prepared().target().object().key})
                &&& step.before()==self.source().before() && step.after()==self.source().after()
                &&& step.outcome()==self.source().outcome() && step.next==self.source().next
                &&& step.recorded_values()
                &&& step.corresponds(self.code()[step.pc as int],self.computation().capture().binding().port_spec(),self.computation().capture().episode())
                &&& step.token()==old(owner).cleanup_state().queues()[id].slots().len()
                &&& final(owner).cleanup_state().queues()[id].slots().len()==step.token()+1
                &&& final(owner).cleanup_state().queues()[id].slots().take(step.token() as int)==old(owner).cleanup_state().queues()[id].slots()
                &&& step.in_slot(final(owner).cleanup_state().queues()[id].slots()[step.token() as int])
                &&& step.registered(final(owner).cleanup_state().link(),id)
            },
    {
        let ghost original=self.source();let ghost code=self.code();
        let ghost computation=self.computation();
        let result=owner.apply_native_effect(id,self.computation,self.branch);
        proof {
            if result!=Err(EffectError::Closed) && quiet_input(computation,owner.value_attempts().events().last()) {
                unchanged(computation,owner.value_attempts().events().last());
                assert(result.is_ok());
            }
        }
        let write=result?;
        let ghost inverse=owner.cleanup_state().queues()[id].slots()[write.admission.token as int].unwrap()->Value_0;
        let next=write.admission.next;
        let step=Step {pc:self.pc,result:ResultStep::Scalar {write,inverse:Ghost(inverse)},next};
        proof {
            reveal(Step::corresponds);
            assert(step.corresponds(code[step.pc as int],computation.capture().binding().port_spec(),computation.capture().episode()));
            step.interpretation(code[step.pc as int],computation.capture().binding().port_spec(),computation.capture().episode());
            step.record_values(code[step.pc as int],computation.capture().binding().port_spec(),computation.capture().episode());
            transport::paired(code,original,step);
        }
        Ok(step)
    }
}
impl<E:ScalarEffect+Copy,T:?Sized> Source<E,T> {
    /// Index addresses the authentic successful-prefix steps, not arbitrary code.
    /// Resolve the preserved port in the real target owner, compare both scalar
    /// value and inverse depth, then compute the original effect outside locks.
    pub fn prepare_scalar<C,G,A,R,M,X>(&self,index:usize,owner:&Owner<C,G,A,R,T,M,X>,id:usize)
        ->(out:Result<PreparedStep<E,T,M>,PrepareError>)
        requires self.wf(),owner.wf(),
        ensures (out.is_err() && out->Err_0 is MissingStep)==(self.original().result.is_err() || index>=self.original().result->Ok_0.steps.len()),
            out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.code()==self.program().code()
                && out->Ok_0.source()==self.original().result->Ok_0.steps@[index as int]
                && owner.value_state().is_some()
                && out->Ok_0.computation().capture().episode()==owner.value_state().unwrap()
                && out->Ok_0.computation().capture().binding().port_spec()==self.original().ports@[out->Ok_0.source().pc as int]
                && out->Ok_0.computation().capture().owner().matches(owner,id),
            out.is_err() && out->Err_0 is InputChanged ==> {
                let mismatch=out->Err_0->InputChanged_0;
                &&& mismatch.wf() && owner.value_state().is_some()
                &&& s::Value::<T>::Scalar(mismatch.expected_spec())==self.original().result->Ok_0.steps@[index as int].before()
                &&& crate::reversible_value::access::selected(owner.value_state().unwrap(),mismatch.binding())
                &&& mismatch.binding().port_spec()==self.original().ports@[self.original().result->Ok_0.steps@[index as int].pc as int]
            },
    {
        if index>=self.inputs.len() {return Err(PrepareError::MissingStep);}
        let input=&self.inputs[index];
        let expected=match input.operand() {Operand::Scalar(v)=>*v,_=>return Err(PrepareError::NotScalar)};
        let pc=input.pc();let call=&self.function.code[pc];
        if matches!(&call.effect,Effect::Replace(_)) {return Err(PrepareError::NotScalar);}
        let capture=match owner.capture_native_effect(id,self.ports[pc]) {Ok(c)=>c,Err(e)=>return Err(PrepareError::Capture(e))};
        proof {capture.provenance();}
        let ghost binding=capture.binding();
        let prepared=match &call.effect {
            Effect::Scalar(effect)=>capture.prepare_at(*effect,expected),
            Effect::Kernel(instruction)=>capture.prepare_instruction_at(*instruction,expected),
            Effect::Replace(_)=>{assert(false);panic!("checked scalar instruction")},
        };
        let computation=match prepared {
            Ok(c)=>c,Err(snapshot)=>{
                let receipt=snapshot.joint_execution().checkpoint_receipt();
                return Err(PrepareError::InputChanged(InputMismatch {expected,
                    observed:ValueState {value:snapshot.value(),depth:snapshot.depth()},
                    read:Ghost(snapshot),binding:Ghost(binding),receipt}));
            },
        };
        Ok(PreparedStep {computation,branch:call.branch,pc,source:Ghost(input.source()),code:Ghost(self.program().code())})
    }
}
}

#[cfg(not(verus_keep_ghost))]
impl std::fmt::Debug for InputMismatch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("InputMismatch")
            .field("expected", &self.expected)
            .field("observed", &self.observed)
            .finish()
    }
}
#[cfg(not(verus_keep_ghost))]
impl std::fmt::Debug for PrepareError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MissingStep => f.write_str("MissingStep"),
            Self::NotScalar => f.write_str("NotScalar"),
            Self::Capture(e) => f.debug_tuple("Capture").field(e).finish(),
            Self::InputChanged(m) => f.debug_tuple("InputChanged").field(m).finish(),
        }
    }
}
