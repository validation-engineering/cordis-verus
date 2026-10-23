//! Bounded autonomous execution of one installed Fresh program.
//!
//! Every iteration calls the real transactional `step`. A checked error stops
//! the run without undoing its successful prefix. Child registration does not
//! run the child. The trace used by the proof is erased from executable Rust.
use super::{DriverError, FreshDriver, Outcome};
#[cfg(verus_keep_ghost)]
use crate::{fresh_semantics as fs, mixed_driver as core, mixed_grammar as mx, refinement as r};
use vstd::prelude::*;

verus! {

pub open spec fn labels(actor:usize,outcomes:Seq<Outcome>)->Seq<fs::Label> {
    outcomes.map(|_:int,outcome:Outcome|(actor,core::outcome_rule(outcome),super::choice(outcome)))
}

/// `steps` counts committed instructions, including the terminal instruction.
/// `error` is the first actual step error; a failed attempt is not a source step.
/// No runtime trace allocation is required for the refinement proof.
pub struct RunReport {
    pub steps:u128,
    pub error:Option<DriverError>,
    /// Erased outcomes used to relate each committed instruction to its source step.
    pub outcomes:Ghost<Seq<Outcome>>,
}
impl RunReport {
    pub closed spec fn outcomes(&self)->Seq<Outcome> {self.outcomes@}
    /// Extend any well-formed source configuration represented by the input
    /// machine with exactly the successful calls made by this invocation.
    pub closed spec fn refines(&self,before:&FreshDriver,after:&FreshDriver,actor:usize)->bool {
        forall|bank:Seq<core::Blueprint>,a:mx::Configuration<u64,core::Index>|
            before.represents(bank,a) && fs::well_formed(core::library(),super::programs(bank),a)
            ==> exists|states:Seq<mx::Configuration<u64,core::Index>>| {
                &&& fs::execution(core::library(),super::programs(bank),states,labels(actor,self.outcomes()))
                &&& states.first()==a && after.represents(bank,states.last())
                &&& forall|i:int|0<=i<states.len() ==> fs::well_formed(core::library(),super::programs(bank),states[i])
            }
    }
    /// Obtain the finite source trace when composing this executable run with
    /// a previously established representation (for example, a script prefix).
    pub proof fn advance_source(&self,before:&FreshDriver,after:&FreshDriver,
        bank:Seq<core::Blueprint>,a:mx::Configuration<u64,core::Index>,actor:usize)
        ->(states:Seq<mx::Configuration<u64,core::Index>>)
        requires self.refines(before,after,actor),before.represents(bank,a),
            fs::well_formed(core::library(),super::programs(bank),a),
        ensures fs::execution(core::library(),super::programs(bank),states,labels(actor,self.outcomes())),
            states.first()==a,after.represents(bank,states.last()),
            forall|i:int|0<=i<states.len() ==> fs::well_formed(core::library(),super::programs(bank),states[i]),
    {
        choose|states:Seq<mx::Configuration<u64,core::Index>>| {
            &&& fs::execution(core::library(),super::programs(bank),states,labels(actor,self.outcomes()))
            &&& states.first()==a && after.represents(bank,states.last())
            &&& forall|i:int|0<=i<states.len() ==> fs::well_formed(core::library(),super::programs(bank),states[i])
        }
    }
    #[verifier::spinoff_prover]
    proof fn establish(&self,before:&FreshDriver,after:&FreshDriver,actor:usize,machines:Seq<FreshDriver>)
        requires before.wf(),after.wf(),chain(machines,actor,self.outcomes()),
            machines.first()==*before,after.same(&machines.last()),
        ensures self.refines(before,after,actor),
    {
        assert forall|bank:Seq<core::Blueprint>,a:mx::Configuration<u64,core::Index>|
            before.represents(bank,a) && fs::well_formed(core::library(),super::programs(bank),a)
            implies exists|states:Seq<mx::Configuration<u64,core::Index>>| {
                &&& fs::execution(core::library(),super::programs(bank),states,labels(actor,self.outcomes()))
                &&& states.first()==a && after.represents(bank,states.last())
                &&& forall|i:int|0<=i<states.len() ==> fs::well_formed(core::library(),super::programs(bank),states[i])
            } by {
                let states=source_chain(bank,a,machines,actor,self.outcomes());
                after.same_representation(&machines.last(),bank,states.last());
            }
    }
}

spec fn chain(machines:Seq<FreshDriver>,actor:usize,outcomes:Seq<Outcome>)->bool {
    &&& machines.len()==outcomes.len()+1
    &&& forall|i:int|0<=i<machines.len() ==> machines[i].wf()
    &&& forall|i:int|0<=i<outcomes.len() ==> machines[i].ack(&machines[i+1],actor,
        core::outcome_rule(outcomes[i]),super::choice(outcomes[i]))
}

/// The witness is constructed from the acknowledged real calls, not supplied
/// as a precondition of the executable runner.
#[verifier::spinoff_prover]
proof fn source_chain(bank:Seq<core::Blueprint>,a:mx::Configuration<u64,core::Index>,
    machines:Seq<FreshDriver>,actor:usize,outcomes:Seq<Outcome>)->(states:Seq<mx::Configuration<u64,core::Index>>)
    requires chain(machines,actor,outcomes),machines.first().represents(bank,a),
        fs::well_formed(core::library(),super::programs(bank),a),
    ensures fs::execution(core::library(),super::programs(bank),states,labels(actor,outcomes)),
        states.first()==a,machines.last().represents(bank,states.last()),
        forall|i:int|0<=i<states.len() ==> fs::well_formed(core::library(),super::programs(bank),states[i]),
    decreases outcomes.len(),
{
    if outcomes.len()==0 {seq![a]} else {
        let prior=machines.drop_last();let prefix=outcomes.drop_last();
        assert(chain(prior,actor,prefix));
        let states=source_chain(bank,a,prior,actor,prefix);
        let outcome=outcomes.last();
        let label=(actor,core::outcome_rule(outcome),super::choice(outcome));
        let z=prior.last().advance_source(&machines.last(),bank,states.last(),label.0,label.1,label.2);
        super::append_source(bank,states,labels(actor,prefix),z,label);
        assert(labels(actor,outcomes)==labels(actor,prefix).push(label));
        assert forall|i:int|0<=i<states.push(z).len() implies
            fs::well_formed(core::library(),super::programs(bank),states.push(z)[i]) by {
            if i<states.len() {assert(states.push(z)[i]==states[i]);}
        }
        states.push(z)
    }
}

impl FreshDriver {
    /// Run this actor until a terminal publication or the first checked error.
    /// The bound comes from the installed forward-only continuation positions;
    /// callers need not supply fuel, a source trace, or future-success premises.
    /// Each successful prefix step remains committed if a later step blocks.
    #[verifier::spinoff_prover]
    pub fn run_until_blocked(&mut self,actor:usize)->(out:RunReport)
        requires old(self).wf(),
        ensures final(self).wf(),out.steps==out.outcomes().len(),
            out.steps<=old(self).run_budget(actor),
            out.steps==0 ==> final(self).same(old(self)),
            out.error.is_some() ==> out.steps+1<=old(self).run_budget(actor) && !final(self).step_enabled(actor),
            out.error.is_none() ==> out.steps>0 && final(self).run_finished(actor),
            actor<old(self).next_id() ==> final(self).journal(actor).len()==old(self).journal(actor).len()+out.steps,
            out.refines(old(self),final(self),actor),
            forall|i:int|0<=i<out.outcomes().len() ==> core::outcome_rule(out.outcomes()[i])==
                if out.error.is_none() && i==out.outcomes().len()-1 {r::Rule::Finish} else {r::Rule::Iter},
    {
        let ghost initial=*self;
        let ghost mut machines=seq![*self];
        let ghost mut outcomes=Seq::<Outcome>::empty();
        let mut steps:u128=0;
        proof {self.run_budget_bounds(actor);}
        loop
            invariant self.wf(),initial.wf(),initial==*old(self),
                1<=self.run_budget(actor),self.run_budget(actor)<=usize::MAX as nat+1,
                initial.run_budget(actor)<=usize::MAX as nat+1,
                steps+ self.run_budget(actor)<=initial.run_budget(actor),steps==outcomes.len(),
                machines.first()==initial,machines.last()==*self,chain(machines,actor,outcomes),
                actor<initial.next_id() ==> self.journal(actor).len()==initial.journal(actor).len()+steps,
                forall|i:int|0<=i<outcomes.len() ==> core::outcome_rule(outcomes[i])==r::Rule::Iter,
            decreases self.run_budget(actor),
        {
            let ghost before=*self;
            match self.step(actor) {
                Err(error)=>{
                    let out=RunReport {steps,error:Some(error),outcomes:Ghost(outcomes)};
                    proof {out.establish(&initial,self,actor,machines);}
                    return out;
                },
                Ok(outcome)=>{
                    steps+=1;
                    proof {
                        let previous=outcomes;
                        outcomes=outcomes.push(outcome);
                        assert(chain(machines.push(*self),actor,outcomes)) by {
                            assert forall|i:int|0<=i<outcomes.len() implies machines.push(*self)[i].ack(
                                &machines.push(*self)[i+1],actor,core::outcome_rule(outcomes[i]),super::choice(outcomes[i])) by {
                                if i<previous.len() {assert(machines.push(*self)[i+1]==machines[i+1]);}
                                else {assert(i==previous.len());assert(machines[i]==before);}
                            }
                        }
                        machines=machines.push(*self);
                        self.run_budget_bounds(actor);
                    }
                    let finished=match outcome {Outcome::Finished=>true,Outcome::Child {finished,..}=>finished,Outcome::Advanced=>false};
                    if finished {
                        let out=RunReport {steps,error:None,outcomes:Ghost(outcomes)};
                        proof {out.establish(&initial,self,actor,machines);}
                        return out;
                    }
                },
            }
        }
    }
}

}
