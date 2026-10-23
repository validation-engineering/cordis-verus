//! Transfer collected Child endpoints to one actual later native checkpoint.
//! Fresh executable allocation, rather than a quiet native suffix, prevents
//! a removed Child ID from being interpreted as a new plugin.
#[cfg(verus_keep_ghost)]
use super::completion::Resolution;
use super::Ledger;
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::native::runtime::history::{lifetime, Snapshot};
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::registration::shared_child::SharedChild;
use vstd::prelude::*;

verus! {
impl Ledger {
    pub open spec fn cut_source<V>(&self,cut:&Snapshot<V>)->bool {
        self.wf() && cut.certified() && cut.key()==self.native()
            && cut.joint_spec().journal_spec()==self.journal() && self.covered(cut.joint_spec().events())
    }
    pub open spec fn terminal_at<V>(&self,resolution:Resolution,cut:&Snapshot<V>)->bool {
        match resolution.birth {
            None=>!self.retirements()[resolution.retirement].assigned(),
            Some(b)=>lifetime::terminal(cut.history().states.last(),self.births()[b].id()),
        }
    }
    /// Arbitrary foreign operations and separate registry removal may occur
    /// between the individual endpoints and this checkpoint.
    pub proof fn resolution_at_cut<V>(&self,child:&SharedChild,resolution:Resolution,cut:&Snapshot<V>)
        requires self.records(child,resolution),self.cut_source(cut),
        ensures self.terminal_at(resolution,cut),
            resolution.birth.is_some() ==> {
                let id=self.births()[resolution.birth.unwrap()].id();let state=cut.joint_spec().last()[self.native()]->Native_state;
                &&& !state.owners.contains_key(id) && !state.publications.contains_key(id)
                &&& crate::refinement::registered(state.control,id) ==> state.control.fibers[id].retired && state.control.fibers[id].phase==crate::Phase::Inactive
            },
    {
        reveal(Ledger::wf);cut.valid_history();self.resolution_facts(child,resolution);
        if let Some(b)=resolution.birth {
            let birth=self.births()[b];let retirement=self.retirements()[resolution.retirement];
            birth.facts();retirement.facts();
            let born=cut.source_index(&birth.checkpoint());let retired=cut.source_index(&retirement.checkpoint());
            cut.source_order(&birth.checkpoint(),&retirement.checkpoint(),born,retired);
            let h=cut.history();let id=birth.id();
            assert(crate::refinement::registered(h.states[born].control,id));
            match resolution.unload {
                None=>{
                    retirement.no_episode_is_quiescent();
                    assert(lifetime::terminal(h.states[retired],id));
                    h.terminal_retained(born,retired,h.states.len()-1,id);
                },
                Some(u)=>{
                    let end=self.unloads()[u];end.facts();let released=cut.source_index(&end.checkpoint());
                    cut.source_order(&retirement.checkpoint(),&end.checkpoint(),retired,released);
                    assert(lifetime::terminal(h.states[released],id));
                    h.terminal_retained(born,released,h.states.len()-1,id);
                },
            }
        }
    }
}
}
