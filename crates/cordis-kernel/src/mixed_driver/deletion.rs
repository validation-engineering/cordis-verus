//! Construct legal private-table episode deletion from the real script history.
//! The owner stays registered; foreign Child identities and actual source
//! receipts survive. Owner-created Children require a different erasure proof.
use super::ScriptReport;
#[cfg(verus_keep_ghost)]
use super::{episode_replay::closing_cut, labels, library, programs, Blueprint, Index, Transition};
#[cfg(verus_keep_ghost)]
use crate::{
    foreign_child_deletion as deletion, mixed_grammar as mx, mixed_observational_runs as obs,
    projection as p, providing_owner_deletion as private, refinement as r,
    shared_execution as shared, Port,
};
use vstd::prelude::*;

verus! {
pub open spec fn admissible(bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>,transitions:Seq<Transition>,owner:usize,begin:int,end:int)->bool {
    closing_cut(transitions,owner,begin,end)
        && private::separated(states[begin].state,owner)
        && deletion::fragment(programs(bank),states.subrange(begin,end+1),labels(transitions).subrange(begin,end),owner)
}
pub open spec fn target(bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>,transitions:Seq<Transition>,owner:usize,begin:int,end:int)->Seq<mx::Configuration<u64,Index>> {
    deletion::delete(library(),programs(bank),states.subrange(begin,end+1),labels(transitions).subrange(begin,end),owner)
}
pub open spec fn kept(transitions:Seq<Transition>,owner:usize,begin:int,end:int)->Seq<(usize,r::Rule)> {
    shared::labels_without(labels(transitions).subrange(begin,end),owner)
}
pub open spec fn deleted(bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>,transitions:Seq<Transition>,owner:usize,begin:int,end:int)->bool {
    let surviving=target(bank,states,transitions,owner,begin,end);
    &&& mx::execution(library(),programs(bank),surviving,kept(transitions,owner,begin,end))
    &&& surviving.first()==states[begin]
    &&& obs::tables_related(|_:Port,a:u64,b:u64|a==b,states[end+1].state,surviving.last().state)
    &&& surviving.last().state.tables[owner].is_empty()
    &&& p::project(states[end+1].state,ISet::full())==p::project(surviving.last().state,ISet::full())
}
proof fn slice(bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>,steps:Seq<(usize,r::Rule)>,begin:int,end:int)
    requires mx::execution(library(),programs(bank),states,steps),0<=begin<=end<states.len(),
    ensures mx::execution(library(),programs(bank),states.subrange(begin,end+1),steps.subrange(begin,end)),
{
    assert forall|i:int|0<=i<end-begin implies mx::step(library(),programs(bank),
        states.subrange(begin,end+1)[i],states.subrange(begin,end+1)[i+1],steps.subrange(begin,end)[i].0,steps.subrange(begin,end)[i].1) by {
        assert(mx::step(library(),programs(bank),states[begin+i],states[begin+i+1],steps[begin+i].0,steps[begin+i].1));
    }
}
/// Every premise is a fact or guard on the actual source. In particular,
/// legality of the surviving execution and inverse success are conclusions.
pub proof fn delete_cut(bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>,transitions:Seq<Transition>,owner:usize,begin:int,end:int)
    requires mx::execution(library(),programs(bank),states,labels(transitions)),states.first()==mx::empty::<u64,Index>(),
        admissible(bank,states,transitions,owner,begin,end),
    ensures deleted(bank,states,transitions,owner,begin,end),
{
    let eq=|_:Port,a:u64,b:u64|a==b;let steps=labels(transitions);let body=programs(bank);
    super::library_theory();crate::xor_recovery_algebra::strict_interface();
    mx::from_empty_safe(eq,library(),body,states,steps);
    crate::provision_coverage::mixed_from_empty(eq,library(),body,states,steps);
    assert(steps[begin]==(owner,r::Rule::Begin));assert(steps[end]==(owner,r::Rule::Unload));
    assert(mx::step(library(),body,states[begin],states[begin+1],owner,r::Rule::Begin));
    assert(mx::step(library(),body,states[end],states[end+1],owner,r::Rule::Unload));
    crate::isolated_deletion::inactive_table_empty(states[begin],owner);
    slice(bank,states,steps,0,begin);slice(bank,states,steps,begin,end);
    deletion::closed_deletion(eq,library(),body,states.subrange(0,begin+1),steps.subrange(0,begin),
        states.subrange(begin,end+1),steps.subrange(begin,end),owner);
    assert(states[end+1]==mx::unload(states[end],owner));
    let surviving=target(bank,states,transitions,owner,begin,end);
    obs::tables_to_projection(eq,states[end+1].state,surviving.last().state);
    assert(p::project(states[end+1].state,ISet::full()) =~= p::project(surviving.last().state,ISet::full()));
}
#[verifier::opaque]
pub open spec fn history(bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>,transitions:Seq<Transition>)->bool {
    forall|owner:usize,begin:int,end:int|admissible(bank,states,transitions,owner,begin,end)
        ==> #[trigger] deleted(bank,states,transitions,owner,begin,end)
}
pub proof fn establish(bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>,transitions:Seq<Transition>)
    requires mx::execution(library(),programs(bank),states,labels(transitions)),states.first()==mx::empty::<u64,Index>(),
    ensures history(bank,states,transitions),
{
    reveal(history);
    assert forall|owner:usize,begin:int,end:int|admissible(bank,states,transitions,owner,begin,end)
        implies #[trigger] deleted(bank,states,transitions,owner,begin,end) by {delete_cut(bank,states,transitions,owner,begin,end);}
}
impl ScriptReport {
    /// Query the same source witness retained by this actual run. A target
    /// trace, expected heap or expected successful Unload is never supplied.
    pub proof fn delete_private_episode(&self,bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>,owner:usize,begin:int,end:int)
        ->(surviving:Seq<mx::Configuration<u64,Index>>)
        requires self.recovery_history_witness(bank,states),admissible(bank,states,self.transitions@,owner,begin,end),
        ensures surviving==target(bank,states,self.transitions@,owner,begin,end),
            mx::execution(library(),programs(bank),surviving,kept(self.transitions@,owner,begin,end)),
            surviving.first()==states[begin],obs::tables_related(|_:Port,a:u64,b:u64|a==b,states[end+1].state,surviving.last().state),
            p::project(surviving.last().state,ISet::full())==super::episode_replay::replay_at(bank,states,self.transitions@,owner,begin,end),
    {
        reveal(history);assert(history(bank,states,self.transitions@));
        assert(deleted(bank,states,self.transitions@,owner,begin,end));
        assert(super::episode_replay::recovered_at(bank,states,self.transitions@,owner,begin,end));
        target(bank,states,self.transitions@,owner,begin,end)
    }
}
impl ScriptReport {
    /// Delete a source-closed family together: owner episodes, their born names,
    /// and dependent consumer episodes. This uses the same actual run witness
    /// as value recovery, and constructs all retained lifecycle steps.
    pub proof fn delete_closed_region(&self,bank:Seq<Blueprint>,states:Seq<mx::Configuration<u64,Index>>,region:crate::closed_region_deletion::Region)
        ->(surviving:Seq<mx::Configuration<u64,Index>>)
        requires self.recovery_history_witness(bank,states),crate::closed_region_deletion::trace::admissible(states,region),
        ensures surviving==crate::closed_region_deletion::trace::target(states,labels(self.transitions@),region),
            mx::execution(library(),programs(bank),surviving,crate::closed_region_deletion::trace::kept(labels(self.transitions@),region)),
            surviving.first()==mx::empty::<u64,Index>(),
            crate::closed_region_deletion::trace::settled(states.last(),region) ==>
                p::project(states.last().state,ISet::full())==p::project(surviving.last().state,ISet::full()),
    {
        super::library_theory();
        crate::closed_region_deletion::trace::from_source(|_:Port,a:u64,b:u64|a==b,library(),programs(bank),states,labels(self.transitions@),region);
        let rho=|t:nat|crate::closed_region_deletion::index(states.last().history,region,t);
        if crate::closed_region_deletion::trace::settled(states.last(),region) {
            crate::closed_region_deletion::trace::closing_observation(states.last(),region,rho);
        }
        crate::closed_region_deletion::trace::target(states,labels(self.transitions@),region)
    }
}

}
