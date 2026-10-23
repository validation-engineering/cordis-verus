//! Recovery at every cut of one authentic Mixed execution.
//! Equation (55) compares table values, including still-open episodes. Actual
//! interior Unloads supply Equation (56); later execution cannot change that
//! historical conclusion. Foreign replay is not a fabricated legal lifecycle.
use super::ScriptReport;
#[cfg(verus_keep_ghost)]
use super::{labels, programs};
#[cfg(verus_keep_ghost)]
use super::{library, Blueprint, Index};
#[cfg(verus_keep_ghost)]
use crate::mixed_driver::Transition;
#[cfg(verus_keep_ghost)]
use crate::{
    entangled as e, mixed_grammar as mx, mixed_recovery as mr, projection as p, refinement as r,
    terminal_episode as episode, xor_recovery_algebra as xor, Port,
};
use vstd::prelude::*;
verus! {
/// End is a state index; the Begin transition is at begin. Its first
/// post-state is begin+1. An owner Unload separates, rather than joins, episodes.
pub open spec fn episode_cut(transitions:Seq<Transition>,owner:usize,begin:int,end:int)->bool {
    &&& 0<=begin<end<=transitions.len()
    &&& transitions[begin].label()==(owner,r::Rule::Begin)
    &&& forall|i:int| begin<i<end ==> transitions[i].label()!=(owner,r::Rule::Unload)
}
pub open spec fn closing_cut(transitions:Seq<Transition>,owner:usize,begin:int,end:int)->bool {
    episode_cut(transitions,owner,begin,end) && end<transitions.len()
        && transitions[end].label()==(owner,r::Rule::Unload)
}

/// All actual foreign words, including inverse journals created before Begin.
pub open spec fn replay_at(bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>,
    transitions:Seq<Transition>,owner:usize,begin:int,end:int)->IMap<Port,u64>
{
    e::foreign_state(mr::events(library(),programs(bank),states.subrange(begin+1,end+1),
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
    requires mx::execution(library(),programs(bank),states,labels(transitions)),
        states.first()==mx::empty::<u64,Index>(),episode_cut(transitions,owner,begin,end),
    ensures recovered_at(bank,states,transitions,owner,begin,end),
{
    crate::mixed_driver::library_theory();xor::scalar_interface();
    let steps=labels(transitions);
    assert(steps[begin]==(owner,r::Rule::Begin));
    assert forall|i:int| begin<i<end implies steps[i]!=(owner,r::Rule::Unload) by {
        assert(steps[i]==transitions[i].label());
    }
    episode::mixed_open_interval(|_:Port,a:u64,b:u64|a==b,library(),programs(bank),states,steps,owner,begin,end);
    mr::actual_episode_recovery(|_:Port,a:u64,b:u64|a==b,library(),programs(bank),states,steps,owner,begin+1,end);
    if closing_cut(transitions,owner,begin,end) {
        assert(steps[end]==(owner,r::Rule::Unload));
        mr::actual_terminal_recovery(|_:Port,a:u64,b:u64|a==b,library(),programs(bank),states,steps,owner,begin+1,end);
    }
}

impl ScriptReport {
    /// One source witness supplies all intervals, not a separate chosen trace
    /// per query. It represents the actual returned machine and transition log.
    pub open spec fn recovery_history_witness(&self,bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>)->bool {
        &&& mx::execution(library(),programs(bank),states,labels(self.transitions@))
        &&& states.first()==mx::empty::<u64,Index>()
        &&& self.machine.represents(bank,states.last())
        &&& super::deletion::history(bank,states,self.transitions@)
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
            mx::execution(library(),programs(bank),states,labels(self.transitions@)),
            states.first()==mx::empty::<u64,Index>(),self.machine.represents(bank,states.last()),
        ensures self.recovery_history(bank),self.recovery_history_witness(bank,states),
    {
        assert forall|owner:usize,begin:int,end:int| episode_cut(self.transitions@,owner,begin,end)
            implies #[trigger] recovered_at(bank,states,self.transitions@,owner,begin,end) by {
            recover_cut(bank,states,self.transitions@,owner,begin,end);
        }
        crate::mixed_driver::library_theory();
        mx::from_empty_safe(|_:Port,a:u64,b:u64|a==b,library(),programs(bank),states,labels(self.transitions@));
        assert forall|owner:usize,begin:int| episode_cut(self.transitions@,owner,begin,self.transitions.len() as int)
            implies self.machine.restored_observation(owner)==Some(#[trigger] replay_at(bank,states,self.transitions@,owner,begin,self.transitions.len() as int)) by {
            let end=self.transitions.len() as int;
            assert(recovered_at(bank,states,self.transitions@,owner,begin,end));
            episode::mixed_open_interval(|_:Port,a:u64,b:u64|a==b,library(),programs(bank),states,labels(self.transitions@),owner,begin,end);
            self.machine.restored_observation_from_source(bank,states.last(),owner);
        }
        super::deletion::establish(bank,states,self.transitions@);
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

impl super::MixedDriver {
    #[verifier::opaque]
    pub closed spec fn restored_observation(&self,owner:usize)->Option<IMap<Port,u64>> {
        match super::restore_receipts(self.journal(owner),self.primitive_state()) {
            None=>None,Some(a)=>Some(p::project(a,ISet::full())),
        }
    }
    /// Project the actual strict restoration result before comparing it with
    /// the source algebra. Keeping this conversion separate bounds unfolding.
    proof fn observe_restored(&self,owner:usize)
        requires super::restore_receipts(self.journal(owner),self.primitive_state()).is_some(),
        ensures self.restored_observation(owner)==Some(p::project(super::restore_receipts(self.journal(owner),self.primitive_state()).unwrap(),ISet::full())),
    { reveal(super::MixedDriver::restored_observation); }

    /// Bind stored receipts to the actual source history before reasoning
    /// about value replay. Receipt actors come from the executable invariant.
    proof fn source_journal(&self,bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>,owner:usize)
        requires self.wf(),self.represents(bank,a),crate::semantics::registered(a.state,owner),
        ensures super::payload_equal(self.primitive_state(),a.state),
            a.state.accumulators[owner].len()==self.journal(owner).len(),
            forall|i:int| #![trigger a.state.accumulators[owner][i]] 0<=i<a.state.accumulators[owner].len() ==> {
                let token=a.state.accumulators[owner][i];
                &&& token<a.history.len()
                &&& a.history[token as int].landed.receipt==self.journal(owner)[i].model()
                &&& self.journal(owner)[i].actor==owner
            },
    {
        reveal(super::MixedDriver::wf);reveal(super::MixedDriver::represents);
        reveal(super::MixedDriver::physical);reveal(super::MixedDriver::journal);
        reveal(super::MixedDriver::primitive_state);
        assert forall|i:int| #![trigger a.state.accumulators[owner][i]] 0<=i<a.state.accumulators[owner].len() implies {
            let token=a.state.accumulators[owner][i];
            &&& token<a.history.len()
            &&& a.history[token as int].landed.receipt==self.journal(owner)[i].model()
            &&& self.journal(owner)[i].actor==owner
        } by {assert(self.rows[owner as int].journal[i].actor==owner);}
    }

    proof fn source_restoration(&self,bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>,owner:usize)
        requires self.wf(),self.journal_recovery(),self.represents(bank,a),
            crate::semantics::registered(a.state,owner),
        ensures mx::restore(a.history,a.state.accumulators[owner],a.state,owner).is_some(),
            super::restore_receipts(self.journal(owner),self.primitive_state()).is_some(),
            super::payload_equal(super::restore_receipts(self.journal(owner),self.primitive_state()).unwrap(),
                mx::restore(a.history,a.state.accumulators[owner],a.state,owner).unwrap()),
    {
        self.source_journal(bank,a,owner);
        reveal(super::MixedDriver::represents);reveal(super::MixedDriver::physical);
        super::restore_journal(a.history,a.state.accumulators[owner],self.journal(owner),a.state,owner);
        super::restore_payload(self.journal(owner),self.primitive_state(),a.state);
    }

    pub proof fn restored_observation_from_source(&self,bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>,owner:usize)
        requires self.wf(),self.journal_recovery(),self.represents(bank,a),
            crate::preservation::well_formed(a.state),crate::semantics::registered(a.state,owner),
        ensures self.restored_observation(owner)==Some(e::restore(mr::own_word(a,owner),p::project(a.state,ISet::full()))),
    {
        self.source_restoration(bank,a,owner);
        self.observe_restored(owner);
        mr::restore_projection(a.history,a.state.accumulators[owner],a.state,owner);
        let restored=mx::restore(a.history,a.state.accumulators[owner],a.state,owner).unwrap();
        p::unique_owner(restored);
        p::equal_payload(restored,super::restore_receipts(self.journal(owner),self.primitive_state()).unwrap(),ISet::full());
    }
}

}
