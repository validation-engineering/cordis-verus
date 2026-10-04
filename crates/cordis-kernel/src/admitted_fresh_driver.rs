//! An owning admission session for one in-flight stage.
//!
//! The session owns its machine and keeps the captured instruction private.
//! Interleaved checked calls may change targets. Landing still uses committed
//! providers, records the real inverse, and diverts on target loss. The session
//! cannot be rebound to a different machine or a later admission.
use super::{Command, DriverError, FreshDriver, Outcome, Transition};
use crate::mixed_driver as core;
#[cfg(verus_keep_ghost)]
use crate::{
    fresh_grammar as fg, fresh_semantics as fs, mixed_grammar as mx, refinement as r,
    semantics as s,
};
#[cfg(verus_keep_ghost)]
use crate::{
    mixed_driver::{Index, Receipt},
    Binding,
};
use crate::{Phase, Port};
use vstd::prelude::*;

verus! {

#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum AdmissionError { Driver(DriverError), StaleAdmission }

pub struct Rejected { pub machine:FreshDriver, pub error:AdmissionError }

/// `outcome` describes the yielded child and continuation. A diverted landing
/// enters Unloading even when that continuation is finished; it does not publish.
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct Landing { pub actor:usize, pub outcome:Outcome, pub diverted:bool }
impl Landing {
    pub open spec fn label(&self)->fs::Label {
        (self.actor,if self.diverted {r::Rule::Divert} else {core::outcome_rule(self.outcome)},super::choice(self.outcome))
    }
}

/// One private ticket, bound by ownership to this exact machine. There is no
/// detached ticket or mutable machine accessor. `into_driver` consumes it.
pub struct Admission {
    machine:FreshDriver, actor:usize, generation:u64, blueprint:usize, pc:usize,
    template:core::Instruction, consumed:bool,
}
impl Admission {
    pub closed spec fn wf(&self)->bool {self.machine.wf()}
    pub closed spec fn machine(&self)->FreshDriver {self.machine}
    pub closed spec fn identity(&self)->(usize,u64,usize,usize,core::Instruction) {
        (self.actor,self.generation,self.blueprint,self.pc,self.template)
    }
    pub closed spec fn consumed(&self)->bool {self.consumed}
    pub closed spec fn same(&self,prior:&Self)->bool {
        self.machine.same(&prior.machine) && self.identity()==prior.identity() && self.consumed==prior.consumed
    }
    pub closed spec fn bound(&self,machine:&FreshDriver)->bool {
        let driver=machine.inner;
        &&& r::registered(driver.control(),self.actor) && driver.control().fibers[self.actor].phase==Phase::Loading
        &&& driver.kernel.generation_of(self.actor)==Some(self.generation)
        &&& self.actor<driver.rows.len() && driver.rows[self.actor as int].blueprint==self.blueprint
        &&& driver.rows[self.actor as int].current==Some(self.pc)
        &&& self.blueprint<driver.blueprints.len() && self.pc<=driver.blueprints[self.blueprint as int].code().len()
        &&& self.template==if self.pc==driver.blueprints[self.blueprint as int].code().len() {core::Instruction::Unit} else {driver.blueprints[self.blueprint as int].code()[self.pc as int]}
    }
    pub fn actor(&self)->(out:usize) ensures out==self.identity().0, {self.actor}
    pub fn is_consumed(&self)->(out:bool) ensures out==self.consumed(), {self.consumed}
    pub fn phase(&self,actor:usize)->Option<Phase> {self.machine.phase(actor)}
    pub fn read(&self,actor:usize,key:Port)->Option<u64> requires self.wf(), {self.machine.read(actor,key)}
    pub fn inverse_count(&self,actor:usize)->Option<usize> requires self.wf(), {self.machine.inverse_count(actor)}
    pub fn into_driver(self)->(out:FreshDriver) ensures out==self.machine(), {self.machine}

    /// Other checked calls can run while this ticket is pending. Progress of
    /// its own actor makes the old ticket stale instead of changing its meaning.
    pub fn apply(&mut self,command:Command)->(out:Result<Transition,DriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).identity()==old(self).identity(),final(self).consumed()==old(self).consumed(),
            out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> out.unwrap().command==command && old(self).machine().ack(&final(self).machine(),
                super::label(out.unwrap()).0,super::label(out.unwrap()).1,super::label(out.unwrap()).2),
    {self.machine.apply(command)}

    #[verifier::spinoff_prover]
    #[verifier::rlimit(30)]
    pub fn land(&mut self)->(out:Result<Landing,AdmissionError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).identity()==old(self).identity(),
            out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> final(self).consumed() && !old(self).consumed() && old(self).bound(&old(self).machine())
                && out.unwrap().actor==old(self).identity().0
                && old(self).machine().ack(&final(self).machine(),out.unwrap().label().0,out.unwrap().label().1,out.unwrap().label().2)
                && final(self).machine().journal(out.unwrap().actor).len()==old(self).machine().journal(out.unwrap().actor).len()+1,
    {
        if self.consumed {return Err(AdmissionError::StaleAdmission);}
        let actor=self.actor;
        let mut draft=self.machine.inner.duplicate();let ghost initial=draft;
        if !draft.registered(actor) || draft.kernel.phase(actor)!=Some(Phase::Loading) {return Err(AdmissionError::StaleAdmission);}
        if draft.kernel.episode_generation(actor)!=Some(self.generation) {return Err(AdmissionError::StaleAdmission);}
        proof {draft.row_bounds(actor);draft.kernel.paper_observations(actor);}
        if draft.rows[actor].blueprint!=self.blueprint || draft.rows[actor].current!=Some(self.pc) {return Err(AdmissionError::StaleAdmission);}
        let blueprint=self.blueprint;let pc=self.pc;let length=draft.blueprints[blueprint].code.len();
        let template=if pc==length {core::Instruction::Unit} else {draft.blueprints[blueprint].code[pc]};
        if template!=self.template {return Err(AdmissionError::StaleAdmission);}
        let has_target=match draft.kernel.target(actor) {
            Some(_target)=>{
                proof {draft.kernel.refines_paper();draft.kernel.paper_target_vector(actor,_target@);
                    r::available_installed_coherent(draft.control(),actor,ISet::new(|b:Binding|_target@.contains(b)));}
                true
            },
            None=>{proof {draft.kernel.unavailable_not_coherent(actor);}false},
        };
        let instruction=match template {
            core::Instruction::Child {blueprint,next,..}=>core::Instruction::Child {expected:draft.rows.len(),blueprint,next},
            _=>template,
        };
        let next=match instruction {core::Instruction::Unit=>None,core::Instruction::Provide {next,..}=>next,
            core::Instruction::Xor {next,..}=>next,core::Instruction::Child {next,..}=>next};
        if let Some(next)=next {if next<=pc || next>length {return Err(AdmissionError::Driver(DriverError::InvalidInstruction));}}
        let receipt=match draft.execute(actor,blueprint,instruction) {Ok(r)=>r,Err(e)=>return Err(AdmissionError::Driver(e))};
        let ghost landed=draft;
        proof {primitive_coherent(initial.primitive_state(),landed.primitive_state(),actor,blueprint,instruction,initial.blueprints@);}
        if has_target {
            if let Err(e)=draft.commit_landing(actor,receipt,next) {return Err(AdmissionError::Driver(e));}
        } else {
            if let Err(e)=draft.commit_divert(actor,receipt) {return Err(AdmissionError::Driver(e));}
        }
        let outcome=match receipt.inverse {
            core::Inverse::Child {child}=>Outcome::Child {child,finished:next.is_none()},
            _=>if next.is_none() {Outcome::Finished} else {Outcome::Advanced},
        };
        let out=Landing {actor,outcome,diverted:!has_target};
        proof {
            draft.admitted_landing_simulation(&initial,&landed,actor,blueprint,pc,template,instruction,receipt,next,out);
            reveal(core::MixedDriver::fresh_ack);
        }
        self.machine=FreshDriver {inner:draft};self.consumed=true;Ok(out)
    }
}

impl FreshDriver {
    /// Ownership binds this ticket to this machine without a caller-supplied
    /// instance identity. Failed admission returns the original machine intact.
    // Return ownership of the complete machine on failure without an extra allocation.
    #[allow(clippy::result_large_err)]
    pub fn admit(self,actor:usize)->(out:Result<Admission,Rejected>)
        requires self.wf(),
        ensures match out {
            Ok(admitted)=>admitted.wf() && admitted.machine().same(&self) && admitted.bound(&self)
                && !admitted.consumed() && admitted.identity().0==actor && r::coherent(self.control(),actor),
            Err(rejected)=>rejected.machine.wf() && rejected.machine.same(&self),
        },
    {
        if let Err(e)=self.inner.kernel.check_iteration(actor) {
            return Err(Rejected {machine:self,error:AdmissionError::Driver(DriverError::Kernel(e))});
        }
        proof {self.inner.row_bounds(actor);self.inner.kernel.paper_observations(actor);}
        let pc=match self.inner.rows[actor].current {Some(pc)=>pc,None=>return Err(Rejected {machine:self,error:AdmissionError::StaleAdmission})};
        let blueprint=self.inner.rows[actor].blueprint;let length=self.inner.blueprints[blueprint].code.len();
        let template=if pc==length {core::Instruction::Unit} else {self.inner.blueprints[blueprint].code[pc]};
        let generation=match self.inner.kernel.episode_generation(actor) {Some(g)=>g,None=>return Err(Rejected {machine:self,error:AdmissionError::StaleAdmission})};
        Ok(Admission {machine:self,actor,generation,blueprint,pc,template,consumed:false})
    }
}

proof fn primitive_coherent(a:s::State<u64>,z:s::State<u64>,actor:usize,blueprint:usize,instruction:core::Instruction,bank:Seq<core::Blueprint>)
    requires mx::run(core::library(),core::instruction_node(bank,blueprint,instruction),a,actor).is_some(),
        z.control==mx::run(core::library(),core::instruction_node(bank,blueprint,instruction),a,actor).unwrap().state.control,
    ensures r::coherent(a.control,actor)==r::coherent(z.control,actor),
{
    match instruction {
        core::Instruction::Child {expected,..}=>{crate::child_driver::child_target_unchanged(a.control,z.control,actor,expected);},
        _=>{},
    }
}
impl core::MixedDriver {
    fn commit_divert(&mut self,actor:usize,receipt:core::Receipt)->(out:Result<(),DriverError>)
        requires old(self).wf(),actor<old(self).rows.len(),r::registered(old(self).control(),actor),
            old(self).control().fibers[actor].phase==Phase::Loading,!r::coherent(old(self).control(),actor),receipt.actor==actor,
        ensures final(self).wf(),final(self).rows.len()==old(self).rows.len(),
            final(self).tables@==old(self).tables@,final(self).blueprints@==old(self).blueprints@,
            out.is_ok() ==> {
                &&& final(self).rows[actor as int].blueprint==old(self).rows[actor as int].blueprint
                &&& final(self).rows[actor as int].current.is_none()
                &&& final(self).journal(actor)==old(self).journal(actor).push(receipt)
                &&& forall|i:int|0<=i<old(self).rows.len() && i!=actor ==> final(self).rows[i]==old(self).rows[i]
                &&& r::step(old(self).control(),final(self).control(),actor,r::Rule::Divert)
            },
    {
        if let Err(e)=self.kernel.leave_if_changed(actor) {return Err(DriverError::Kernel(e));}
        self.rows[actor].current=None;self.rows[actor].journal.push(receipt);Ok(())
    }
}

impl core::MixedDriver {
    #[verifier::spinoff_prover]
    #[verifier::rlimit(30)]
    proof fn admitted_landing_simulation(&self,initial:&Self,landed:&Self,actor:usize,blueprint:usize,pc:usize,
        template:core::Instruction,instruction:core::Instruction,receipt:Receipt,next:Option<usize>,result:Landing)
        requires self.wf(),initial.wf(),landed.wf(),actor<initial.rows.len(),
            r::registered(initial.control(),actor),initial.control().fibers[actor].phase==Phase::Loading,result.diverted==!r::coherent(initial.control(),actor),result.actor==actor,
            initial.rows[actor as int].blueprint==blueprint,initial.rows[actor as int].current==Some(pc),
            template==if pc==initial.blueprints[blueprint as int].code.len() {core::Instruction::Unit} else {initial.blueprints[blueprint as int].code[pc as int]},
            instruction==match template {core::Instruction::Child {blueprint,next,..}=>core::Instruction::Child {expected:initial.rows.len(),blueprint,next},_=>template},
            super::choice(result.outcome)==match template {core::Instruction::Child {..}=>Some(initial.rows.len()),_=>None},
            next==instruction.continuation(),core::outcome_rule(result.outcome)==if next.is_some() {r::Rule::Iter} else {r::Rule::Finish},
            initial.blueprints@==landed.blueprints@,self.blueprints@==initial.blueprints@,
            {
                let y=mx::run(core::library(),core::instruction_node(initial.blueprints@,blueprint,instruction),initial.primitive_state(),actor);
                y.is_some() && landed.physical(y.unwrap().state) && receipt.model()==y.unwrap().receipt
            },
            landed.rows.len()>=initial.rows.len(),self.rows.len()==landed.rows.len(),self.tables@==landed.tables@,
            forall|i:int| 0<=i<initial.rows.len() ==> landed.rows[i]==initial.rows[i],
            forall|i:int| 0<=i<self.rows.len() && i!=actor ==> self.rows[i]==landed.rows[i],
            self.rows[actor as int].blueprint==blueprint,self.rows[actor as int].current==if result.diverted {None} else {next},
            self.journal(actor)==initial.journal(actor).push(receipt),
            match instruction {
                core::Instruction::Child {expected,blueprint,..}=>expected==initial.rows.len() && landed.rows.len()==initial.rows.len()+1
                    && landed.rows[initial.rows.len() as int].blueprint==blueprint
                    && landed.rows[initial.rows.len() as int].current.is_none()
                    && landed.rows[initial.rows.len() as int].journal.len()==0,
                _=>landed.rows.len()==initial.rows.len(),
            },
            result.diverted ==> r::step(landed.control(),self.control(),actor,r::Rule::Divert),
            !result.diverted && next.is_none() ==> r::step(landed.control(),self.control(),actor,r::Rule::Finish),
            !result.diverted && next.is_some() ==> self.control()==landed.control(),
        ensures initial.fresh_ack(self,actor,result.label().1,super::choice(result.outcome)),
    {
        reveal(core::MixedDriver::fresh_ack);
        let length=initial.blueprints[blueprint as int].code.len();
        super::weak_theory();
            assert forall|bank:Seq<core::Blueprint>,a:mx::Configuration<u64,Index>| initial.represents(bank,a) && fs::well_formed(core::library(),super::programs(bank),a) implies {
                let rule=result.label().1;let z=fs::land(core::library(),super::programs(bank),a,actor,if rule==r::Rule::Divert {Phase::Unloading} else if rule==r::Rule::Iter {Phase::Loading} else {Phase::Active},super::choice(result.outcome));
                fs::step(core::library(),super::programs(bank),a,z,actor,rule,super::choice(result.outcome)) && self.represents(bank,z)
            } by {
                let rule=result.label().1;let phase=if rule==r::Rule::Divert {Phase::Unloading} else if rule==r::Rule::Iter {Phase::Loading} else {Phase::Active};
                let z=fs::land(core::library(),super::programs(bank),a,actor,phase,super::choice(result.outcome));
                assert(a.current[actor]==Some(Index {blueprint,pc}));
                assert(bank[blueprint as int].same(&initial.blueprints[blueprint as int]));
                assert(instruction.valid(pc,length,blueprint,initial.blueprints[blueprint as int].dependencies(),initial.blueprints[blueprint as int].provisions()));
                core::instruction_bank(initial.blueprints@,bank,blueprint,instruction);
                super::instantiate_instruction(bank,blueprint,template,initial.rows.len());
                assert(super::programs(bank)(actor)(a.current[actor].unwrap())==super::instruction_node(bank,blueprint,template));
                assert(fg::instantiate(super::programs(bank)(actor)(a.current[actor].unwrap()),super::choice(result.outcome))==Some(core::instruction_node(initial.blueprints@,blueprint,instruction)));
                core::run_payload(initial.blueprints@,blueprint,instruction,initial.primitive_state(),a.state,actor);
                let y=fg::run(core::library(),super::programs(bank)(actor)(a.current[actor].unwrap()),a.state,actor,super::choice(result.outcome)).unwrap();
                assert(landed.physical(y.state));assert(y.receipt==receipt.model());
                assert(y.next==core::continuation(blueprint,next));
                initial.paper_total(a.state);
                s::total_targets_agree(a.state,actor,a.state.control.fibers[actor].committed);
                assert(fs::step(core::library(),super::programs(bank),a,z,actor,rule,super::choice(result.outcome)));
                fs::frame(|_:Port,u:u64,v:u64|u==v,core::library(),super::programs(bank),a,z,actor,rule,super::choice(result.outcome));
                fs::state_preservation(|_:Port,u:u64,v:u64|u==v,core::library(),super::programs(bank),a,z,actor,rule,super::choice(result.outcome));
                assert(self.control().fibers.dom() =~= z.state.control.fibers.dom()) by {
                    assert forall|n:usize| self.control().fibers.dom().contains(n)==z.state.control.fibers.dom().contains(n) by {
                        if n!=actor {assert(r::registered(self.control(),n)==r::registered(landed.control(),n));}
                    }
                }
                assert(self.control().fibers =~= z.state.control.fibers) by {
                    assert forall|n:usize| r::registered(self.control(),n) implies self.control().fibers[n]==z.state.control.fibers[n] by {
                        if n!=actor {assert(self.control().fibers[n]==landed.control().fibers[n]);}
                    }
                }
                assert(self.tables() =~= z.state.tables);
                assert forall|n:usize| r::registered(self.control(),n) implies {
                    &&& n<self.rows.len()
                    &&& z.roots[n]==(Index {blueprint:self.rows[n as int].blueprint,pc:0})
                    &&& z.current[n]==core::continuation(self.rows[n as int].blueprint,self.rows[n as int].current)
                    &&& z.state.effects[n]==0 && z.state.iterators[n]==crate::dependent_lift::marker(z.current[n])
                    &&& z.state.accumulators[n].len()==self.journal(n).len()
                    &&& forall|i:int| #![trigger z.state.accumulators[n][i]] 0<=i<self.journal(n).len() ==> {
                        let token=z.state.accumulators[n][i];token<z.history.len()
                            && z.history[token as int].landed.receipt==self.journal(n)[i].model()
                    }
                } by {
                    if n<initial.rows.len() {
                        assert(r::registered(initial.control(),n));
                        if n!=actor {assert(self.rows[n as int]==initial.rows[n as int]);}
                        assert forall|i:int| #![trigger z.state.accumulators[n][i]] 0<=i<self.journal(n).len() implies {
                            let token=z.state.accumulators[n][i];token<z.history.len()
                                && z.history[token as int].landed.receipt==self.journal(n)[i].model()
                        } by {
                            if n==actor && i==initial.journal(actor).len() {
                                assert(z.history[z.state.accumulators[n][i] as int].landed.receipt==receipt.model());
                            } else {
                                assert(i<initial.journal(n).len());
                                let token=a.state.accumulators[n][i];
                                assert(a.history[token as int].landed.receipt==initial.journal(n)[i].model());
                            }
                        }
                    }
                }
                assert(self.represents(bank,z));
            }
    }
}

}

#[path = "admitted_script.rs"]
pub mod script;
