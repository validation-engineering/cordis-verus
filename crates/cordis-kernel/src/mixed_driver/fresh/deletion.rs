//! Source-closed deletion query on the actual Fresh script report.
use super::ScriptReport;
#[cfg(verus_keep_ghost)]
use super::{labels, programs};
#[cfg(verus_keep_ghost)]
use crate::{
    closed_region_deletion::{fresh_trace, trace, Region},
    fresh_semantics as fs,
    mixed_driver::{library, library_theory, Blueprint, Index},
    mixed_grammar as g, projection as p, Port,
};
use vstd::prelude::*;
verus! {
impl ScriptReport {
    /// Preserve each retained allocation choice and its binder-produced root
    /// and continuation. No global conversion to fixed-name programs is needed.
    pub proof fn delete_closed_region(&self,bank:Seq<Blueprint>,states:Seq<g::Configuration<u64,Index>>,region:Region)
        ->(surviving:Seq<g::Configuration<u64,Index>>)
        requires self.recovery_history_witness(bank,states),trace::admissible(states,region),
        ensures surviving==fresh_trace::target(states,labels(self.transitions@),region),
            fs::execution(library(),programs(bank),surviving,fresh_trace::kept(labels(self.transitions@),region)),
            surviving.first()==g::empty::<u64,Index>(),
            trace::settled(states.last(),region) ==> p::project(states.last().state,ISet::full())==p::project(surviving.last().state,ISet::full()),
    {
        library_theory();crate::observational_grammar::exact_theory(|_:Port,a:u64,b:u64|a==b,library());fresh_trace::from_source(|_:Port,a:u64,b:u64|a==b,library(),programs(bank),states,labels(self.transitions@),region);
        if trace::settled(states.last(),region) {
            trace::closing_observation(states.last(),region,|t:nat|crate::closed_region_deletion::index(states.last().history,region,t));
        }
        fresh_trace::target(states,labels(self.transitions@),region)
    }
}
}
