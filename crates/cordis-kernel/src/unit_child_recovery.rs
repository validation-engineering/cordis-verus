//! Recovery domains derived from the real retained journal and its source history.
//!
//! This closes only the Unit/Child fragment. It never assumes that restore
//! succeeds, and leaves strict table inverse failures unchanged.
use super::MixedDriver;
#[cfg(verus_keep_ghost)]
use super::{restore_receipts, Blueprint, Index, Inverse, Receipt};
#[cfg(verus_keep_ghost)]
use crate::{child_history as ch, mixed_grammar as mx, refinement as r, semantics as s};
use vstd::prelude::*;

verus! {

pub open spec fn unit_child_receipts(receipts:Seq<Receipt>)->bool {
    forall|i:int| 0<=i<receipts.len() ==> match #[trigger] receipts[i].inverse {
        Inverse::Unit | Inverse::Child {..}=>true,
        _=>false,
    }
}

/// Unit is the identity. Child retires its captured identity and preserves the
/// registry domain, so every remaining child stays inside the next inverse's
/// domain. No child-phase premise or future scheduler action is involved.
pub proof fn restore_unit_children(receipts:Seq<Receipt>,a:s::State<u64>,actor:usize)
    requires unit_child_receipts(receipts),r::registered(a.control,actor),
        forall|i:int| 0<=i<receipts.len() ==> receipts[i].actor==actor,
        forall|i:int| 0<=i<receipts.len() ==> match #[trigger] receipts[i].inverse {
            Inverse::Child {child}=>r::registered(a.control,child),_=>true,
        },
    ensures restore_receipts(receipts,a).is_some(),
        restore_receipts(receipts,a).unwrap().control.fibers.dom()==a.control.fibers.dom(),
        restore_receipts(receipts,a).unwrap().tables==a.tables,
        forall|n:usize| r::registered(a.control,n) ==>
            restore_receipts(receipts,a).unwrap().control.fibers[n].phase==a.control.fibers[n].phase
            && restore_receipts(receipts,a).unwrap().control.fibers[n].committed==a.control.fibers[n].committed,
    decreases receipts.len(),
{
    if receipts.len()>0 {
        let receipt=receipts.last();
        assert(receipt==receipts[receipts.len()-1]);
        match receipt.inverse {
            Inverse::Unit=>{},
            Inverse::Child {child}=>{
                assert(r::registered(a.control,child));
                let b=mx::undo(receipt.model(),a).unwrap();
                assert(b.control.fibers.dom() =~= a.control.fibers.dom());
            },
            _=>{},
        }
        assert(mx::undo(receipt.model(),a).is_some());
        let b=mx::undo(receipt.model(),a).unwrap();
        assert(b.control.fibers.dom()==a.control.fibers.dom());
        assert forall|n:usize| r::registered(a.control,n) implies
            b.control.fibers[n].phase==a.control.fibers[n].phase
            && b.control.fibers[n].committed==a.control.fibers[n].committed by { }
        assert forall|i:int| 0<=i<receipts.drop_last().len() implies
            receipts.drop_last()[i].actor==actor by {assert(receipts.drop_last()[i]==receipts[i]);}
        assert(unit_child_receipts(receipts.drop_last())) by {
            assert forall|i:int| 0<=i<receipts.drop_last().len() implies match #[trigger] receipts.drop_last()[i].inverse {
                Inverse::Unit | Inverse::Child {..}=>true,_=>false,
            } by {assert(receipts.drop_last()[i]==receipts[i]);}
        }
        assert forall|i:int| 0<=i<receipts.drop_last().len() implies match #[trigger] receipts.drop_last()[i].inverse {
            Inverse::Child {child}=>r::registered(b.control,child),_=>true,
        } by {assert(receipts.drop_last()[i]==receipts[i]);}
        restore_unit_children(receipts.drop_last(),b,actor);
        assert forall|n:usize| r::registered(a.control,n) implies
            restore_receipts(receipts,a).unwrap().control.fibers[n].phase==a.control.fibers[n].phase
            && restore_receipts(receipts,a).unwrap().control.fibers[n].committed==a.control.fibers[n].committed by {
            assert(r::registered(b.control,n));
        }
    }
}

impl MixedDriver {
    /// Classification of the actual retained receipts, not merely installed code.
    pub open spec fn unit_child_journal(&self,actor:usize)->bool {
        unit_child_receipts(self.journal(actor))
    }
    /// The useful consequence of an actual source history. Structural `wf`
    /// alone deliberately does not assert this additional provenance property.
    pub open spec fn unit_child_recovery(&self)->bool {
        forall|actor:usize| r::registered(self.control(),actor) && self.unit_child_journal(actor)
            ==> restore_receipts(self.journal(actor),self.primitive_state()).is_some()
    }

    pub proof fn retained_children_from_source(&self,bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>,actor:usize)
        requires self.wf(),self.represents(bank,a),r::registered(self.control(),actor),
            ch::retained(mx::kind(a.history),a.state),
        ensures forall|i:int| 0<=i<self.journal(actor).len() ==> match #[trigger] self.journal(actor)[i].inverse {
            Inverse::Child {child}=>r::registered(self.control(),child),_=>true,
        },
    {
        reveal(MixedDriver::represents);reveal(MixedDriver::physical);
        assert forall|i:int| 0<=i<self.journal(actor).len() implies match #[trigger] self.journal(actor)[i].inverse {
            Inverse::Child {child}=>r::registered(self.control(),child),_=>true,
        } by {
            let token=a.state.accumulators[actor][i];
            assert(a.state.accumulators[actor].contains(token));
            assert(a.history[token as int].landed.receipt==self.journal(actor)[i].model());
            if let Inverse::Child {child}=self.journal(actor)[i].inverse {
                assert(mx::kind(a.history)(token)==Some(child));
                mx::retained_child_domain(a.history,a.state,actor,token,child);
                assert(r::registered(a.state.control,child));
            }
        }
    }

    /// Both the mixed and fresh source semantics maintain the same retention
    /// predicate. Accept it directly so neither frontend needs a stronger model.
    pub proof fn unit_child_recovery_from_source(&self,bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>)
        requires self.wf(),self.represents(bank,a),ch::retained(mx::kind(a.history),a.state),
        ensures self.unit_child_recovery(),
    {
        reveal(MixedDriver::wf);reveal(MixedDriver::journal);reveal(MixedDriver::primitive_state);
        reveal(MixedDriver::represents);
        assert forall|actor:usize| r::registered(self.control(),actor) && self.unit_child_journal(actor)
            implies restore_receipts(self.journal(actor),self.primitive_state()).is_some() by {
            self.retained_children_from_source(bank,a,actor);
            assert(actor<self.rows.len());
            assert forall|i:int| 0<=i<self.journal(actor).len() implies self.journal(actor)[i].actor==actor by {
                assert(self.rows[actor as int].journal[i].actor==actor);
            }
            restore_unit_children(self.journal(actor),self.primitive_state(),actor);
        }
    }

    /// Eliminate the inverse-domain premise only for the retained Unit/Child
    /// fragment. The real kernel's dependency/phase guard remains mandatory.
    pub proof fn unit_child_unload_domain(&self,actor:usize)
        requires self.wf(),self.unit_child_recovery(),self.unit_child_journal(actor),
        ensures self.unload_enabled(actor)==self.cleanup_permitted(actor),
    {
        reveal(MixedDriver::unload_enabled);reveal(MixedDriver::cleanup_permitted);
        reveal(crate::Kernel::cleanup_enabled);
        if self.cleanup_permitted(actor) {self.kernel.paper_observations(actor);}
    }
}

}
