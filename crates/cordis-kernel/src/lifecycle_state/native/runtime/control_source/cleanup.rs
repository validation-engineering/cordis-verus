//! Completeness, not only authenticity: every actual native Unload has its
//! successful host-cleanup witness at the corresponding shared Journal index.
#[cfg(verus_keep_ghost)]
use super::super::{child_history::Ledger, episode::Unload};
#[cfg(verus_keep_ghost)]
use super::history;
use super::Source;
#[cfg(verus_keep_ghost)]
use crate::{refinement::Rule, reversible_value::joint};
use vstd::prelude::*;
verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub open spec fn complete<V>(ledger:Ledger,h:history::History<V>,positions:Seq<nat>)->bool {
    forall|i:int|0<=i<h.labels.len() && h.labels[i].1==Rule::Unload ==>
        exists|u:int|0<=u<ledger.unloads().len() && (#[trigger] ledger.unloads()[u]).at()==positions[i+1]
}
pub proof fn non_unload<V>(ledger:Ledger,a:history::History<V>,ap:Seq<nat>,z:history::History<V>,zp:Seq<nat>,id:usize,rule:Rule)
    requires complete(ledger,a,ap),rule!=Rule::Unload,z.labels==a.labels.push((id,rule)),
        ap.len()==a.states.len(),a.states.len()==a.labels.len()+1,zp.len()==ap.len()+1,zp.take(ap.len() as int)==ap,
    ensures complete(ledger,z,zp),
{
    assert forall|i:int|0<=i<z.labels.len() && z.labels[i].1==Rule::Unload implies
        exists|u:int|0<=u<ledger.unloads().len() && (#[trigger] ledger.unloads()[u]).at()==zp[i+1] by {
        assert(i<a.labels.len());assert(zp[i+1]==ap[i+1]);
    }
}
pub proof fn unload_collected<V>(before:Ledger,after:Ledger,a:history::History<V>,ap:Seq<nat>,z:history::History<V>,zp:Seq<nat>,end:Unload,id:usize)
    requires complete(before,a,ap),a.states.len()==a.labels.len()+1,ap.len()==a.states.len(),
        z.labels==a.labels.push((id,Rule::Unload)),zp.len()==ap.len()+1,zp.take(ap.len() as int)==ap,
        after.unloads().len()==before.unloads().len()+1,after.unloads().take(before.unloads().len() as int)==before.unloads(),
        after.unloads().last().same_source(&end),end.at()==zp.last(),
    ensures complete(after,z,zp),
{
    assert forall|i:int|0<=i<z.labels.len() && z.labels[i].1==Rule::Unload implies
        exists|u:int|0<=u<after.unloads().len() && (#[trigger] after.unloads()[u]).at()==zp[i+1] by {
        if i<a.labels.len() {
            let u=choose|u:int|0<=u<before.unloads().len() && (#[trigger] before.unloads()[u]).at()==ap[i+1];
            assert(after.unloads()[u]==before.unloads()[u]);assert(after.unloads()[u].at()==zp[i+1]);
        } else {assert(after.unloads()[after.unloads().len()-1].at()==zp[i+1]);}
    }
}
impl<V> Source<V> {
    /// Derive the actual cleanup witness from a command index. The caller
    /// supplies neither a successful cleanup assumption nor a receipt mapping.
    pub proof fn unload_at(&self,i:int)->(end:Unload)
        requires self.certified(),0<=i<self.commands_spec().len(),self.commands_spec()[i].rule()==Rule::Unload,
        ensures end.wf(),end.native()==self.cut().key(),end.at()==self.cut().positions()[i+1],
            end.owner().origin.id==self.commands_spec()[i].actor(),end.recorded(self.cut().joint_spec().events()),
            self.cut().joint_spec().covers(&end.checkpoint()),end.cleanup_source(),
            end.cleanup_checkpoint().is_some() && end.cleanup_checkpoint().unwrap().journal()==self.cut().joint_spec().journal_spec() ==>
                self.cut().joint_spec().covers(&end.cleanup_checkpoint().unwrap())
                && end.cleanup_checkpoint().unwrap().at()<end.at(),
    {
        reveal(Source::certified);self.cut().valid_history();
        let ledger=self.ledger();reveal(Ledger::wf);
        let u=choose|u:int|0<=u<ledger.unloads().len() && (#[trigger] ledger.unloads()[u]).at()==self.cut().positions()[i+1];
        let end=ledger.unloads()[u];end.facts();
        assert(self.cut().joint_spec().covers(&end.checkpoint()));
        assert(self.cut().joint_spec().events()[end.at() as int]==end.checkpoint().events()[end.at() as int]);
        assert(joint::state_at(self.cut().joint_spec().events(),end.at())==joint::state_at(end.checkpoint().events(),end.at()));
        if end.cleanup_checkpoint().is_some() && end.cleanup_checkpoint().unwrap().journal()==self.cut().joint_spec().journal_spec() {
            assert(self.cut().joint_spec().events().take(end.cleanup_checkpoint().unwrap().events().len() as int) =~= end.checkpoint().events().take(end.cleanup_checkpoint().unwrap().events().len() as int));
        }
        end
    }
}
}
