//! Nonempty source client for intermediate publication/pending recovery.
//! The inputs name actual creating and closing commits, not final table values.
use super::Interval;
#[cfg(verus_keep_ghost)]
use super::Issue;
#[cfg(verus_keep_ghost)]
use crate::{
    refinement::Rule,
    reversible_value::joint::{self, pending_recovery as pending},
};
use vstd::prelude::*;

verus! {
impl<V> Interval<V> {
    /// Initial resources survive; every newly admitted lifetime has a real
    /// later Unload and every new managed forward has its actual registration.
    /// Unrelated lifecycle changes, failed cleanup and repeated episodes may
    /// interleave. This proves observation recovery, not heap value recovery.
    #[verifier::spinoff_prover]
    pub proof fn completed_lifetimes(&self)->(out:Option<Issue>)
        requires self.wf(),
            exists|i:int|self.first<=i<self.last() && self.history().labels[i].1==Rule::Begin,
            exists|write:nat|self.start<=write<self.end() && self.frames()[write as int].event.pending,
            forall|id:usize|self.history().states[self.first].publications.contains_key(id)
                || self.history().states[self.first].owners.contains_key(id) ==>
                    #[trigger] self.history().publication_registry().no_unload(id,self.first,self.last()),
            forall|i:int|self.first<=i<self.last() && (self.history().labels[i].1==Rule::Begin || self.history().labels[i].1==Rule::Finish) ==>
                exists|j:int|i<j<self.last() && #[trigger] self.history().labels[j]==(self.history().labels[i].0,Rule::Unload),
            forall|write:nat|joint::pending_at(self.frames(),self.start).contains_key(write) ==>
                #[trigger] pending::no_settlement(self.frames(),write,self.start,self.end()),
            forall|write:nat|self.start<=write<self.end() && self.frames()[write as int].event.pending ==>
                exists|at:nat|write<at<self.end() && #[trigger] pending::settles(self.frames(),write,at),
        ensures out.is_none(),self.recovered_all(),self.normalized(),
    {
        hide(joint::valid);hide(joint::step);
        self.source.valid_history();self.source.joint_spec().valid_history();self.history().recovery_registries();
        let publications=self.history().publication_registry();let owners=self.history().owner_registry();
        publications.closed_from_unloads(self.first,self.last(),self.scope().providers);
        assert forall|id:usize|self.scope().providers.contains(id) && owners.states[self.first].contains_key(id) implies
            #[trigger] owners.no_unload(id,self.first,self.last()) by {assert(publications.no_unload(id,self.first,self.last()));}
        owners.closed_from_unloads(self.first,self.last(),self.scope().providers);
        pending::closed_from_registrations(self.frames(),self.start,self.end(),self.scope().objects);
        self.check_all()
    }
    /// An actual consumed forward can be inspected before its queue insertion.
    /// This selects a nonempty microstep interval that a return-only observation
    /// would miss; after registration the obligation cannot be resurrected.
    #[verifier::spinoff_prover]
    pub proof fn registration_microsteps(&self,write:nat,at:nat)
        requires self.wf(),self.start<=write<at<self.end(),pending::settles(self.frames(),write,at),
        ensures self.frames()[write as int].event.pending,joint::forward(self.frames()[write as int].event),
            forall|n:nat|write<n<=at ==> #[trigger] joint::pending_at(self.frames(),n).contains_pair(write,self.frames()[write as int].event.key),
            forall|n:nat|at<n<=self.end() ==> !#[trigger] joint::pending_at(self.frames(),n).contains_key(write),
            forall|other:nat|#[trigger] pending::settles(self.frames(),write,other) ==> other==at,
    {
        hide(joint::valid);hide(joint::step);self.source.valid_history();self.source.joint_spec().valid_history();
        pending::settlement_source(self.frames(),write,at);joint::pending_since(self.frames(),write,at);
        assert forall|other:nat|#[trigger] pending::settles(self.frames(),write,other) implies other==at by {
            pending::unique_settlement(self.frames(),write,other,at);
        }
    }
}
}
