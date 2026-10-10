//! Terminal table-value recovery for the actual Fresh script result.
//!
//! A successful prefix ends in the selected owner's Unload. Its Begin and the
//! absence of an interior owner Unload identify the episode from the real
//! transition log; callers do not supply an installed interval or source trace.
//! Foreign replay is the explicit value calculation of fresh_recovery, not a
//! claim that deleting the owner leaves a legal lifecycle execution.
#[cfg(verus_keep_ghost)]
use super::{labels, programs, Transition};
use super::{FreshDriver, ScriptReport};
#[cfg(verus_keep_ghost)]
use crate::mixed_driver::{library, Blueprint, Index, MixedDriver};
#[cfg(verus_keep_ghost)]
use crate::{
    entangled as e, fresh_recovery as fr, fresh_semantics as fs, mixed_grammar as mx,
    preservation as inv, projection as p, refinement as r, semantics as s,
    terminal_episode as episode, xor_recovery_algebra as xor, Port,
};
use vstd::prelude::*;

verus! {

// Both drivers emit the same public transition enum. Reuse its episode cut;
// retain Fresh's actual allocation choice in the source execution and replay.
#[cfg(verus_keep_ghost)]
pub use crate::mixed_driver::terminal_replay::terminal_episode;

/// The snapshot is immediately after Begin. Owner landings are omitted from
/// value replay; foreign Unloads replay their actual captured inverse journals.
pub open spec fn foreign_replay(bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>,
    transitions:Seq<Transition>,owner:usize,begin:int)->IMap<Port,u64>
{
    let end=transitions.len()-1;
    e::foreign_state(fr::events(library(),programs(bank),states.subrange(begin+1,end+1),
        labels(transitions).subrange(begin+1,end),owner),p::project(states[begin+1].state,ISet::full()))
}

impl FreshDriver {
    /// All registered tables, including Loading values, as in Definition 51.
    pub closed spec fn value_observation(&self)->IMap<Port,u64> {self.inner.value_observation()}

    pub proof fn value_observation_from_source(&self,bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>)
        requires self.represents(bank,a),inv::well_formed(a.state),
        ensures self.value_observation()==p::project(a.state,ISet::full()),
            forall|owner:usize| s::registered(a.state,owner) ==> self.table(owner)==a.state.tables[owner],
    {
        reveal(FreshDriver::represents);reveal(FreshDriver::table);
        reveal(MixedDriver::represents);reveal(MixedDriver::physical);reveal(MixedDriver::tables);
        self.inner.value_observation_from_source(a.state);
    }
}

impl ScriptReport {
    /// A source witness for the actual successful prefix and the returned value
    /// equation. No equation for full registry identity is asserted.
    pub open spec fn terminal_replay_witness(&self,bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>,
        owner:usize,begin:int)->bool
    {
        &&& fs::execution(library(),programs(bank),states,labels(self.transitions@))
        &&& states.first()==mx::empty::<u64,Index>()
        &&& self.machine.represents(bank,states.last())
        &&& self.machine.table(owner).is_empty()
        &&& self.machine.value_observation()==foreign_replay(bank,states,self.transitions@,owner,begin)
    }

    /// This is automatically established by run_script, including error returns
    /// whose last successful transition is the selected owner's Unload.
    pub open spec fn terminal_recovery(&self,bank:Seq<Blueprint>)->bool {
        forall|owner:usize,begin:int| terminal_episode(self.transitions@,owner,begin)
            ==> exists|states:Seq<mx::Configuration<u64,Index>>| self.terminal_replay_witness(bank,states,owner,begin)
    }

    pub proof fn terminal_replay_from_source(&self,bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>,
        owner:usize,begin:int)
        requires self.machine.wf(),fs::execution(library(),programs(bank),states,labels(self.transitions@)),
            states.first()==mx::empty::<u64,Index>(),self.machine.represents(bank,states.last()),
            terminal_episode(self.transitions@,owner,begin),
        ensures self.terminal_replay_witness(bank,states,owner,begin),
    {
        let steps=labels(self.transitions@);let end=self.transitions.len() as int-1;
        crate::mixed_driver::library_theory();super::weak_theory();xor::scalar_interface();
        fs::from_empty_safe(|_:Port,a:u64,b:u64|a==b,library(),programs(bank),states,steps);
        assert((steps[begin].0,steps[begin].1)==(owner,r::Rule::Begin));
        assert((steps[end].0,steps[end].1)==(owner,r::Rule::Unload));
        assert forall|i:int| begin<i<end implies (steps[i].0,steps[i].1)!=(owner,r::Rule::Unload) by {
            assert((steps[i].0,steps[i].1)==self.transitions[i].label());
        }
        episode::fresh_installed_interval(|_:Port,a:u64,b:u64|a==b,library(),programs(bank),states,steps,owner,begin,end);
        fr::actual_terminal_recovery(|_:Port,a:u64,b:u64|a==b,library(),programs(bank),states,steps,owner,begin+1,end);
        assert(states[end+1]==states.last());
        self.machine.value_observation_from_source(bank,states.last());
        assert(s::registered(states.last().state,owner));
    }

    pub proof fn establish_terminal_recovery(&self,bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>)
        requires self.machine.wf(),fs::execution(library(),programs(bank),states,labels(self.transitions@)),
            states.first()==mx::empty::<u64,Index>(),self.machine.represents(bank,states.last()),
        ensures self.terminal_recovery(bank),
    {
        assert forall|owner:usize,begin:int| terminal_episode(self.transitions@,owner,begin)
            implies exists|trace:Seq<mx::Configuration<u64,Index>>| self.terminal_replay_witness(bank,trace,owner,begin) by {
            self.terminal_replay_from_source(bank,states,owner,begin);
            assert(self.terminal_replay_witness(bank,states,owner,begin));
        }
    }

    /// Extract the source and equation already guaranteed by the actual entry
    /// point. The caller selects an episode in the returned successful log.
    pub proof fn terminal_replay(&self,bank:Seq<Blueprint>,owner:usize,begin:int)
        ->(states:Seq<mx::Configuration<u64,Index>>)
        requires self.terminal_recovery(bank),terminal_episode(self.transitions@,owner,begin),
        ensures self.terminal_replay_witness(bank,states,owner,begin),
    {
        choose|states:Seq<mx::Configuration<u64,Index>>| self.terminal_replay_witness(bank,states,owner,begin)
    }
}

}
