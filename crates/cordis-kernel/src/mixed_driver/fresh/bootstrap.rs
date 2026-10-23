//! Execute a real setup script and then one installed actor, from a new machine.
//!
//! Setup errors stop before autonomous execution. Every successful call belongs
//! to one source execution from empty; checked errors add no source transition.
use super::{Blueprint, Command, DriverError, FreshDriver, Outcome, Transition};
#[cfg(verus_keep_ghost)]
use crate::{
    fresh_semantics as fs, mixed_driver as core, mixed_grammar as mx, operation_history as oh,
    provision_coverage as pc, provision_history as ph, refinement as r, Port,
};
use vstd::prelude::*;

verus! {

#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum FromEmptyStatus {
    SetupFailed(DriverError),
    Blocked(DriverError),
    Finished,
}

/// `setup` contains the successful preparation calls. `steps` counts only
/// committed autonomous steps, including a terminal call. The returned machine
/// retains both prefixes so the caller can inspect, retry, or recover it.
pub struct FromEmptyReport {
    pub machine:FreshDriver,
    pub setup:Vec<Transition>,
    pub actor:usize,
    pub steps:u128,
    pub status:FromEmptyStatus,
    /// The real machine at the boundary between preparation and autonomous run.
    pub prepared:Ghost<FreshDriver>,
    /// The autonomous outcomes are proof data, with no runtime trace buffer.
    pub outcomes:Ghost<Seq<Outcome>>,
}
impl FromEmptyReport {
    pub closed spec fn labels(&self)->Seq<fs::Label> {
        super::labels(self.setup@)+super::runner::labels(self.actor,self.outcomes@)
    }
    /// Both the prepared and returned machines have an actual source witness
    /// in this one execution from empty. No input representation is assumed.
    pub closed spec fn refines(&self,bank:Seq<core::Blueprint>)->bool {
        exists|states:Seq<mx::Configuration<u64,core::Index>>| {
            &&& fs::execution(core::library(),super::programs(bank),states,self.labels())
            &&& states.first()==mx::empty::<u64,core::Index>()
            &&& self.prepared@.represents(bank,states[self.setup.len() as int])
            &&& self.machine.represents(bank,states.last())
            &&& forall|i:int|0<=i<states.len() ==> fs::well_formed(core::library(),super::programs(bank),states[i])
                && crate::preservation::resource_safe(states[i].state)
        }
    }
    /// Expose the established whole execution for further verified composition.
    pub proof fn source_execution(&self,bank:Seq<core::Blueprint>)->(states:Seq<mx::Configuration<u64,core::Index>>)
        requires self.refines(bank),
        ensures fs::execution(core::library(),super::programs(bank),states,self.labels()),
            states.first()==mx::empty::<u64,core::Index>(),
            self.prepared@.represents(bank,states[self.setup.len() as int]),
            self.machine.represents(bank,states.last()),
            forall|i:int|0<=i<states.len() ==> fs::well_formed(core::library(),super::programs(bank),states[i])
                && crate::preservation::resource_safe(states[i].state),
    {
        choose|states:Seq<mx::Configuration<u64,core::Index>>| {
            &&& fs::execution(core::library(),super::programs(bank),states,self.labels())
            &&& states.first()==mx::empty::<u64,core::Index>()
            &&& self.prepared@.represents(bank,states[self.setup.len() as int])
            &&& self.machine.represents(bank,states.last())
            &&& forall|i:int|0<=i<states.len() ==> fs::well_formed(core::library(),super::programs(bank),states[i])
                && crate::preservation::resource_safe(states[i].state)
        }
    }
    #[verifier::spinoff_prover]
    proof fn establish(&self,bank:Seq<core::Blueprint>,states:Seq<mx::Configuration<u64,core::Index>>)
        requires self.machine.wf(),self.prepared@.wf(),
            fs::execution(core::library(),super::programs(bank),states,self.labels()),
            states.first()==mx::empty::<u64,core::Index>(),
            self.prepared@.represents(bank,states[self.setup.len() as int]),
            self.machine.represents(bank,states.last()),
        ensures self.refines(bank),self.machine.unit_child_recovery(),self.prepared@.unit_child_recovery(),
            self.machine.provision_recovery(),self.prepared@.provision_recovery(),
            self.machine.journal_recovery(),self.prepared@.journal_recovery(),
            self.machine.owner_table_recovery(),self.prepared@.owner_table_recovery(),
    {
        super::weak_theory();
        fs::from_empty_safe(|_:Port,x:u64,y:u64|x==y,core::library(),super::programs(bank),states,self.labels());
        self.machine.unit_child_recovery_from_source(bank,states.last());
        self.prepared@.unit_child_recovery_from_source(bank,states[self.setup.len() as int]);
        ph::fresh_from_empty(|_:Port,x:u64,y:u64|x==y,core::library(),super::programs(bank),states,self.labels());
        self.machine.provision_recovery_from_source(bank,states.last());
        self.prepared@.provision_recovery_from_source(bank,states[self.setup.len() as int]);
        oh::fresh_from_empty(|_:Port,x:u64,y:u64|x==y,core::library(),super::programs(bank),states,self.labels());
        self.machine.journal_recovery_from_source(bank,states.last());
        self.prepared@.journal_recovery_from_source(bank,states[self.setup.len() as int]);
        pc::fresh_from_empty(|_:Port,x:u64,y:u64|x==y,core::library(),super::programs(bank),states,self.labels());
        self.machine.owner_table_recovery_from_source(bank,states.last());
        self.prepared@.owner_table_recovery_from_source(bank,states[self.setup.len() as int]);
    }
}

/// Join at the common state without adding an administrative or failure step.
#[verifier::spinoff_prover]
proof fn concatenate(bank:Seq<core::Blueprint>,prefix:Seq<mx::Configuration<u64,core::Index>>,
    before:Seq<fs::Label>,suffix:Seq<mx::Configuration<u64,core::Index>>,after:Seq<fs::Label>)
    ->(states:Seq<mx::Configuration<u64,core::Index>>)
    requires fs::execution(core::library(),super::programs(bank),prefix,before),
        fs::execution(core::library(),super::programs(bank),suffix,after),prefix.last()==suffix.first(),
    ensures fs::execution(core::library(),super::programs(bank),states,before+after),
        states.first()==prefix.first(),states.last()==suffix.last(),states[before.len() as int]==prefix.last(),
{
    let states=prefix.drop_last()+suffix;
    assert forall|i:int|0<=i<before.len()+after.len() implies fs::step(core::library(),super::programs(bank),
        states[i],states[i+1],(before+after)[i].0,(before+after)[i].1,(before+after)[i].2) by {
        if i<before.len() {
            assert(states[i]==prefix[i]);
            if i+1<before.len() {assert(states[i+1]==prefix[i+1]);}
            else {assert(i+1==before.len());assert(states[i+1]==suffix.first());}
            assert(fs::step(core::library(),super::programs(bank),prefix[i],prefix[i+1],before[i].0,before[i].1,before[i].2));
        } else {
            let j=i-before.len();
            assert(states[i]==suffix[j] && states[i+1]==suffix[j+1]);
            assert(fs::step(core::library(),super::programs(bank),suffix[j],suffix[j+1],after[j].0,after[j].1,after[j].2));
        }
    }
    if before.len()==0 {assert(prefix.first()==prefix.last());}
    states
}

/// Start from new/empty, run the actual preparation script, then autonomously
/// advance one actor only if every preparation command succeeded. No caller
/// supplies a machine, source history, fuel, or assumption of future success.
#[verifier::spinoff_prover]
pub fn run_from_empty(blueprints:Vec<Blueprint>,setup_commands:&[Command],actor:usize)->(out:FromEmptyReport)
    ensures out.machine.wf(),out.prepared@.wf(),out.actor==actor,
        out.machine.unit_child_recovery(),out.prepared@.unit_child_recovery(),
        out.machine.provision_recovery(),out.prepared@.provision_recovery(),
        out.machine.journal_recovery(),out.prepared@.journal_recovery(),
        out.machine.owner_table_recovery(),out.prepared@.owner_table_recovery(),
        out.refines(blueprints@.map(|_:int,bp:Blueprint|bp.compiled())),
        out.setup.len()<=setup_commands.len(),
        forall|i:int|0<=i<out.setup.len() ==> out.setup[i].command()==setup_commands[i],
        out.steps==out.outcomes@.len(),out.steps<=usize::MAX as nat+1,
        out.steps==0 ==> out.machine.same(&out.prepared@),
        actor<out.prepared@.next_id() ==> out.machine.journal(actor).len()==out.prepared@.journal(actor).len()+out.steps,
        match out.status {
            FromEmptyStatus::SetupFailed(_)=>out.setup.len()<setup_commands.len() && out.steps==0
                && (super::preparation::preparation_command(setup_commands[out.setup.len() as int])
                    ==> !out.prepared@.preparation_enabled(setup_commands[out.setup.len() as int])
                        && !out.machine.preparation_enabled(setup_commands[out.setup.len() as int])),
            FromEmptyStatus::Blocked(_)=>out.setup.len()==setup_commands.len() && !out.machine.step_enabled(actor)
                && out.steps+1<=out.prepared@.run_budget(actor),
            FromEmptyStatus::Finished=>out.setup.len()==setup_commands.len() && out.steps>0
                && out.machine.run_finished(actor) && out.steps<=out.prepared@.run_budget(actor),
        },
        forall|i:int|0<=i<out.outcomes@.len() ==> core::outcome_rule(out.outcomes@[i])==
            if out.status==FromEmptyStatus::Finished && i==out.outcomes@.len()-1 {r::Rule::Finish} else {r::Rule::Iter},
{
    let ghost bank=blueprints@.map(|_:int,bp:Blueprint|bp.compiled());
    let setup=super::run_script(blueprints,setup_commands);
    let ghost prefix=setup.source_execution(bank);
    let ghost prepared=setup.machine;
    let mut machine=setup.machine;
    let transitions=setup.transitions;
    if let Some(error)=setup.error {
        let out=FromEmptyReport {machine,setup:transitions,actor,steps:0,status:FromEmptyStatus::SetupFailed(error),
            prepared:Ghost(prepared),outcomes:Ghost(Seq::empty())};
        proof {
            assert(out.labels()==super::labels(out.setup@));
            assert(prefix[out.setup.len() as int]==prefix.last());
            out.establish(bank,prefix);
        }
        return out;
    }
    proof {machine.run_budget_bounds(actor);}
    let run=machine.run_until_blocked(actor);
    let ghost suffix=run.advance_source(&prepared,&machine,bank,prefix.last(),actor);
    let ghost states=concatenate(bank,prefix,super::labels(transitions@),suffix,super::runner::labels(actor,run.outcomes()));
    let status=match run.error {Some(error)=>FromEmptyStatus::Blocked(error),None=>FromEmptyStatus::Finished};
    let out=FromEmptyReport {machine,setup:transitions,actor,steps:run.steps,status,
        prepared:Ghost(prepared),outcomes:Ghost(run.outcomes())};
    proof {out.establish(bank,states);}
    out
}

}
