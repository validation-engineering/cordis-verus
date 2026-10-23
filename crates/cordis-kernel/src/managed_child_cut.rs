//! One native cut for all original Child obligations of the recorded creator.
use super::RecordedExecution;
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::native::runtime::{
    child_history::{completion::Resolution, Ledger},
    history::Snapshot,
};
use vstd::prelude::*;

verus! {
impl<C,G,A,R,T:?Sized,M,X> RecordedExecution<C,G,A,R,T,M,X> {
    pub open spec fn native_children_terminal<V>(&self,ledger:&Ledger,cut:&Snapshot<V>)->bool {
        self.native_children_resolved(ledger) && ledger.cut_source(cut)
            && forall|id:usize,token:int|(#[trigger] self.native_child_source(id,token)).is_some() ==>
                exists|resolution:Resolution|self.native_child_completion(ledger,id,token,resolution)
                    && ledger.terminal_at(resolution,cut)
    }
    /// Completion coverage is checked against original inverse identities;
    /// terminal state at this shared actual cut is then a derived conclusion.
    pub proof fn native_children_at_cut<V>(&self,ledger:&Ledger,cut:&Snapshot<V>)
        requires self.native_children_resolved(ledger),ledger.cut_source(cut),
        ensures self.native_children_terminal(ledger,cut),
    {
        assert forall|id:usize,token:int|(#[trigger] self.native_child_source(id,token)).is_some() implies
            exists|resolution:Resolution|self.native_child_completion(ledger,id,token,resolution)
                && ledger.terminal_at(resolution,cut) by {
            let resolution=self.native_child_endpoint(ledger,id,token);
            ledger.resolution_at_cut(&self.native_child_source(id,token).unwrap(),resolution,cut);
        }
    }
}
}
