//! Empty owner tables after recovery, connected to the actual inverse journal.
//!
//! Source coverage says every currently occupied owner slot has a retained
//! Provision inverse. The bridge below transfers the model's erasure theorem
//! to the same receipts and tables used by executable unload. Definedness is
//! supplied independently by journal_recovery; this property states its result.
use super::MixedDriver;
#[cfg(verus_keep_ghost)]
use super::{restore_journal, restore_payload, restore_receipts, Blueprint, Index};
#[cfg(verus_keep_ghost)]
use crate::{mixed_grammar as mx, mixed_recovery as mr, preservation as inv, refinement as r};
use vstd::prelude::*;

verus! {

impl MixedDriver {
    /// A conditional result property, separate from inverse definedness.
    /// Both are derived from the actual empty-origin execution by the scripts.
    pub open spec fn owner_table_recovery(&self)->bool {
        forall|actor:usize| r::registered(self.control(),actor)
            && restore_receipts(self.journal(actor),self.primitive_state()).is_some()
            ==> restore_receipts(self.journal(actor),self.primitive_state()).unwrap().tables[actor].is_empty()
    }

    pub proof fn owner_table_recovery_from_source(&self,bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>)
        requires self.wf(),self.represents(bank,a),inv::well_formed(a.state),mr::provided_journals(a),
        ensures self.owner_table_recovery(),
    {
        reveal(MixedDriver::wf);reveal(MixedDriver::represents);reveal(MixedDriver::physical);
        reveal(MixedDriver::primitive_state);reveal(MixedDriver::journal);
        assert forall|actor:usize| r::registered(self.control(),actor)
            && restore_receipts(self.journal(actor),self.primitive_state()).is_some()
            implies restore_receipts(self.journal(actor),self.primitive_state()).unwrap().tables[actor].is_empty() by {
            assert forall|i:int| #![trigger a.state.accumulators[actor][i]] 0<=i<a.state.accumulators[actor].len() implies {
                let token=a.state.accumulators[actor][i];
                &&& token<a.history.len()
                &&& a.history[token as int].landed.receipt==self.journal(actor)[i].model()
                &&& self.journal(actor)[i].actor==actor
            } by {assert(self.rows[actor as int].journal[i].actor==actor);}
            restore_journal(a.history,a.state.accumulators[actor],self.journal(actor),a.state,actor);
            restore_payload(self.journal(actor),self.primitive_state(),a.state);
            mr::restored_owner_empty(a,actor);
        }
    }

    /// Transactional duplication preserves both the inverse input and its
    /// owner-table result; it does not manufacture a source execution.
    pub proof fn same_owner_table_recovery(&self,other:&Self)
        requires self.wf(),other.wf(),self.same(other),
        ensures self.owner_table_recovery()==other.owner_table_recovery(),
    {
        reveal(MixedDriver::same);reveal(MixedDriver::wf);reveal(MixedDriver::journal);
        reveal(MixedDriver::tables);reveal(MixedDriver::table);reveal(MixedDriver::primitive_state);
        self.kernel.unchanged_observations(&other.kernel);
        assert(self.tables() =~= other.tables()) by {
            assert forall|n:usize| r::registered(self.control(),n) implies self.table(n)==other.table(n) by {
                self.kernel.paper_observations(n);self.row_bounds(n);other.row_bounds(n);
                self.tables[n as int].same_map(&other.tables[n as int]);
            }
        }
        assert forall|actor:usize| r::registered(self.control(),actor) implies
            self.journal(actor)==other.journal(actor) by { }
    }
}

}
