//! Recovery at every cut of one authentic Fresh execution.
//! Equation (55) compares table values, including still-open episodes. Actual
//! interior Unloads supply Equation (56); later execution cannot change that
//! historical conclusion. Foreign replay is not a fabricated legal lifecycle.
use super::ScriptReport;
#[cfg(verus_keep_ghost)]
use super::{labels, programs};
#[cfg(verus_keep_ghost)]
use crate::mixed_driver::Transition;
#[cfg(verus_keep_ghost)]
use crate::mixed_driver::{library, Blueprint, Index};
#[cfg(verus_keep_ghost)]
use crate::{
    entangled as e, fresh_recovery as fr, fresh_semantics as fs, mixed_grammar as mx,
    mixed_recovery as mr, projection as p, refinement as r, terminal_episode as episode,
    xor_recovery_algebra as xor, Port,
};
use vstd::prelude::*;
verus! {
#[cfg(verus_keep_ghost)]
pub use crate::mixed_driver::episode_replay::{episode_cut,closing_cut};
/// All actual foreign words, including inverse journals created before Begin.
pub open spec fn replay_at(bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>,
    transitions:Seq<Transition>,owner:usize,begin:int,end:int)->IMap<Port,u64>
{
    e::foreign_state(fr::events(library(),programs(bank),states.subrange(begin+1,end+1),
        labels(transitions).subrange(begin+1,end),owner),p::project(states[begin+1].state,ISet::full()))
}
pub open spec fn recovered_at(bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>,
    transitions:Seq<Transition>,owner:usize,begin:int,end:int)->bool
{
    &&& e::restore(mr::own_word(states[end],owner),p::project(states[end].state,ISet::full()))
        ==replay_at(bank,states,transitions,owner,begin,end)
    &&& states[begin+1].state.tables[owner].is_empty()
    &&& (closing_cut(transitions,owner,begin,end) ==> {
        &&& p::project(states[end+1].state,ISet::full())==replay_at(bank,states,transitions,owner,begin,end)
        &&& states[end+1].state.tables[owner].is_empty()
    })
}

pub proof fn recover_cut(bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>,
    transitions:Seq<Transition>,owner:usize,begin:int,end:int)
    requires fs::execution(library(),programs(bank),states,labels(transitions)),
        states.first()==mx::empty::<u64,Index>(),episode_cut(transitions,owner,begin,end),
    ensures recovered_at(bank,states,transitions,owner,begin,end),
{
    crate::mixed_driver::library_theory();xor::scalar_interface();
    let steps=labels(transitions);
    assert((steps[begin].0,steps[begin].1)==(owner,r::Rule::Begin));
    assert forall|i:int| begin<i<end implies (steps[i].0,steps[i].1)!=(owner,r::Rule::Unload) by {
        assert((steps[i].0,steps[i].1)==transitions[i].label());
    }
    episode::fresh_open_interval(|_:Port,a:u64,b:u64|a==b,library(),programs(bank),states,steps,owner,begin,end);
    fr::actual_episode_recovery(|_:Port,a:u64,b:u64|a==b,library(),programs(bank),states,steps,owner,begin+1,end);
    if closing_cut(transitions,owner,begin,end) {
        assert((steps[end].0,steps[end].1)==(owner,r::Rule::Unload));
        fr::actual_terminal_recovery(|_:Port,a:u64,b:u64|a==b,library(),programs(bank),states,steps,owner,begin+1,end);
    }
}

impl ScriptReport {
    /// One source witness supplies all intervals, not a separate chosen trace
    /// per query. It represents the actual returned machine and transition log.
    pub open spec fn recovery_history_witness(&self,bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>)->bool {
        &&& fs::execution(library(),programs(bank),states,labels(self.transitions@))
        &&& states.first()==mx::empty::<u64,Index>()
        &&& self.machine.represents(bank,states.last())
        &&& forall|owner:usize,begin:int,end:int| episode_cut(self.transitions@,owner,begin,end)
            ==> #[trigger] recovered_at(bank,states,self.transitions@,owner,begin,end)
        &&& forall|owner:usize,begin:int| episode_cut(self.transitions@,owner,begin,self.transitions.len() as int)
            ==> self.machine.restored_observation(owner)==Some(#[trigger] replay_at(bank,states,self.transitions@,owner,begin,self.transitions.len() as int))
    }
    pub open spec fn recovery_history(&self,bank:Seq<Blueprint>)->bool {
        exists|states:Seq<mx::Configuration<u64,Index>>| self.recovery_history_witness(bank,states)
    }
    pub proof fn establish_recovery_history(&self,bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>)
        requires self.machine.wf(),self.machine.journal_recovery(),
            fs::execution(library(),programs(bank),states,labels(self.transitions@)),
            states.first()==mx::empty::<u64,Index>(),self.machine.represents(bank,states.last()),
        ensures self.recovery_history(bank),self.recovery_history_witness(bank,states),
    {
        assert forall|owner:usize,begin:int,end:int| episode_cut(self.transitions@,owner,begin,end)
            implies #[trigger] recovered_at(bank,states,self.transitions@,owner,begin,end) by {
            recover_cut(bank,states,self.transitions@,owner,begin,end);
        }
        crate::mixed_driver::library_theory();
        fs::from_empty_safe(|_:Port,a:u64,b:u64|a==b,library(),programs(bank),states,labels(self.transitions@));
        assert forall|owner:usize,begin:int| episode_cut(self.transitions@,owner,begin,self.transitions.len() as int)
            implies self.machine.restored_observation(owner)==Some(#[trigger] replay_at(bank,states,self.transitions@,owner,begin,self.transitions.len() as int)) by {
            let end=self.transitions.len() as int;
            assert(recovered_at(bank,states,self.transitions@,owner,begin,end));
            episode::fresh_open_interval(|_:Port,a:u64,b:u64|a==b,library(),programs(bank),states,labels(self.transitions@),owner,begin,end);
            self.machine.restored_observation_from_source(bank,states.last(),owner);
        }
        assert(self.recovery_history_witness(bank,states));
    }
    pub proof fn recovery_source(&self,bank:Seq<Blueprint>)->(states:Seq<mx::Configuration<u64,Index>>)
        requires self.recovery_history(bank),
        ensures self.recovery_history_witness(bank,states),
    {choose|states:Seq<mx::Configuration<u64,Index>>| self.recovery_history_witness(bank,states)}

    /// Connect the current stored receipts to the replay equation, including
    /// checked-error returns. This does not bypass the executable cleanup guard.
    pub proof fn current_recovery(&self,bank:Seq<Blueprint>,owner:usize,begin:int)
        ->(states:Seq<mx::Configuration<u64,Index>>)
        requires self.recovery_history(bank),
            episode_cut(self.transitions@,owner,begin,self.transitions.len() as int),
        ensures self.recovery_history_witness(bank,states),
            self.machine.restored_observation(owner)==Some(replay_at(bank,states,self.transitions@,owner,begin,self.transitions.len() as int)),
    {
        let states=self.recovery_source(bank);
        assert(self.machine.restored_observation(owner)==Some(replay_at(bank,states,self.transitions@,owner,begin,self.transitions.len() as int)));
        states
    }
}

impl super::FreshDriver {
    pub closed spec fn restored_observation(&self,owner:usize)->Option<IMap<Port,u64>> {self.inner.restored_observation(owner)}
    pub proof fn restored_observation_from_source(&self,bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>,owner:usize)
        requires self.wf(),self.journal_recovery(),self.represents(bank,a),
            crate::preservation::well_formed(a.state),crate::semantics::registered(a.state,owner),
        ensures self.restored_observation(owner)==Some(e::restore(mr::own_word(a,owner),p::project(a.state,ISet::full()))),
    {
        reveal(super::FreshDriver::wf);reveal(super::FreshDriver::represents);
        reveal(super::FreshDriver::journal_recovery);
        self.inner.restored_observation_from_source(bank,a,owner);
    }
}

}
