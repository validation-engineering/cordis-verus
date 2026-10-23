//! Terminal table-value recovery for the actual Mixed script result.
//!
//! A successful prefix ends in the selected owner's Unload. Its Begin and the
//! absence of an interior owner Unload identify the episode from the real
//! transition log; callers do not supply an installed interval or source trace.
//! Foreign replay is the explicit value calculation of mixed_recovery, not a
//! claim that deleting the owner leaves a legal lifecycle execution.
#[cfg(verus_keep_ghost)]
use super::{labels, library, programs, Blueprint, Index, Transition};
use super::{MixedDriver, ScriptReport};
#[cfg(verus_keep_ghost)]
use crate::{
    entangled as e, mixed_grammar as mx, mixed_recovery as mr, preservation as inv,
    projection as p, refinement as r, semantics as s, terminal_episode as episode,
    xor_recovery_algebra as xor, Port,
};
use vstd::prelude::*;

verus! {

/// Both indices refer to successful transitions, excluding any failed command.
pub open spec fn terminal_episode(transitions:Seq<Transition>,owner:usize,begin:int)->bool {
    &&& 0<=begin<transitions.len()-1
    &&& transitions[begin].label()==(owner,r::Rule::Begin)
    &&& transitions.last().label()==(owner,r::Rule::Unload)
    &&& forall|i:int| begin<i<transitions.len()-1 ==> transitions[i].label()!=(owner,r::Rule::Unload)
}

/// The snapshot is immediately after Begin. Owner landings are omitted from
/// value replay; foreign Unloads replay their actual captured inverse journals.
pub open spec fn foreign_replay(bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>,
    transitions:Seq<Transition>,owner:usize,begin:int)->IMap<Port,u64>
{
    let end=transitions.len()-1;
    e::foreign_state(mr::events(library(),programs(bank),states.subrange(begin+1,end+1),
        labels(transitions).subrange(begin+1,end),owner),p::project(states[begin+1].state,ISet::full()))
}

impl MixedDriver {
    /// Definition 51 observes all registered tables, including Loading values;
    /// it is distinct from the Active-only publication used by target lookup.
    pub closed spec fn value_observation(&self)->IMap<Port,u64> {
        p::project(self.primitive_state(),ISet::full())
    }

    pub proof fn value_observation_from_source(&self,a:s::State<u64>)
        requires self.physical(a),inv::well_formed(a),
        ensures self.value_observation()==p::project(a,ISet::full()),
    {
        reveal(MixedDriver::physical);reveal(MixedDriver::primitive_state);
        let actual=self.primitive_state();
        p::unique_owner(a);
        assert(p::bindings_equal(a,actual)) by {
            assert forall|key:Port,n:usize| p::owns(a,key,n)==p::owns(actual,key,n)
                && (p::owns(a,key,n) ==> a.tables[n][key]==actual.tables[n][key]) by {}
        }
        assert(p::unambiguous(actual)) by {
            assert forall|key:Port,x:usize,y:usize| p::owns(actual,key,x) && p::owns(actual,key,y)
                implies x==y by {
                assert(p::owns(a,key,x));assert(p::owns(a,key,y));
            }
        }
        p::projection_equal(a,actual,ISet::full());
    }
}

impl ScriptReport {
    /// A source witness for the actual successful prefix and the returned value
    /// equation. No equation for full registry identity is asserted.
    pub open spec fn terminal_replay_witness(&self,bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>,
        owner:usize,begin:int)->bool
    {
        &&& mx::execution(library(),programs(bank),states,labels(self.transitions@))
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
        requires self.machine.wf(),mx::execution(library(),programs(bank),states,labels(self.transitions@)),
            states.first()==mx::empty::<u64,Index>(),self.machine.represents(bank,states.last()),
            terminal_episode(self.transitions@,owner,begin),
        ensures self.terminal_replay_witness(bank,states,owner,begin),
    {
        let steps=labels(self.transitions@);let end=self.transitions.len() as int-1;
        super::library_theory();xor::scalar_interface();
        mx::from_empty_safe(|_:Port,a:u64,b:u64|a==b,library(),programs(bank),states,steps);
        assert(steps[begin]==(owner,r::Rule::Begin));
        assert(steps[end]==(owner,r::Rule::Unload));
        assert forall|i:int| begin<i<end implies steps[i]!=(owner,r::Rule::Unload) by {
            assert(steps[i]==self.transitions[i].label());
        }
        episode::mixed_installed_interval(|_:Port,a:u64,b:u64|a==b,library(),programs(bank),states,steps,owner,begin,end);
        mr::actual_terminal_recovery(|_:Port,a:u64,b:u64|a==b,library(),programs(bank),states,steps,owner,begin+1,end);
        assert(states[end+1]==states.last());
        reveal(MixedDriver::represents);reveal(MixedDriver::physical);reveal(MixedDriver::tables);
        self.machine.value_observation_from_source(states.last().state);
        assert(s::registered(states.last().state,owner));
    }

    pub proof fn establish_terminal_recovery(&self,bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>)
        requires self.machine.wf(),mx::execution(library(),programs(bank),states,labels(self.transitions@)),
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
