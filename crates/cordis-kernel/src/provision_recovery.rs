//! Defined recovery for actual Unit/Child/Provision journals.
//!
//! Live source histories supply existence and uniqueness of the retained
//! provision keys. The implementation keeps its original strict inverse checks.
use super::MixedDriver;
#[cfg(verus_keep_ghost)]
use super::{restore_payload, restore_receipts, Blueprint, Index, Inverse, Receipt};
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, mixed_grammar as mx, preservation as inv, provision_history as ph,
    refinement as r, semantics as s,
};
use vstd::prelude::*;

verus! {

pub open spec fn unit_child_provision_receipts(receipts:Seq<Receipt>)->bool {
    forall|i:int| 0<=i<receipts.len() ==> match #[trigger] receipts[i].inverse {
        Inverse::Unit | Inverse::Child {..} | Inverse::Provision {..}=>true,
        _=>false,
    }
}

pub open spec fn live_receipts(receipts:Seq<Receipt>,a:s::State<u64>,actor:usize)->bool {
    &&& forall|i:int| 0<=i<receipts.len() ==> match #[trigger] receipts[i].inverse {
        Inverse::Provision {key}=>a.tables[actor].dom().contains(key),_=>true,
    }
    &&& forall|i:int,j:int| 0<=i<j<receipts.len() ==> match #[trigger] receipts[i].inverse {
        Inverse::Provision {key}=>#[trigger] receipts[j].inverse!=(Inverse::Provision {key}),_=>true,
    }
}

/// Removing the last Provision cannot invalidate an earlier one: its key is
/// distinct. Unit and Child keep all values; Child only retires its identity.
#[verifier::spinoff_prover]
pub proof fn restore_unit_child_provisions(receipts:Seq<Receipt>,a:s::State<u64>,actor:usize)
    requires inv::well_formed(a),s::registered(a,actor),
        unit_child_provision_receipts(receipts),live_receipts(receipts,a,actor),
        forall|i:int| 0<=i<receipts.len() ==> receipts[i].actor==actor,
        forall|i:int| 0<=i<receipts.len() ==> match #[trigger] receipts[i].inverse {
            Inverse::Child {child}=>s::registered(a,child),_=>true,
        },
    ensures restore_receipts(receipts,a).is_some(),
        inv::well_formed(restore_receipts(receipts,a).unwrap()),
        restore_receipts(receipts,a).unwrap().control.fibers.dom()==a.control.fibers.dom(),
        forall|n:usize| s::registered(a,n) ==>
            restore_receipts(receipts,a).unwrap().control.fibers[n].phase==a.control.fibers[n].phase
            && restore_receipts(receipts,a).unwrap().control.fibers[n].committed==a.control.fibers[n].committed
            && (n!=actor ==> restore_receipts(receipts,a).unwrap().tables[n]==a.tables[n]),
    decreases receipts.len(),
{
    if receipts.len()>0 {
        let receipt=receipts.last();
        assert(receipt==receipts[receipts.len()-1]);
        match receipt.inverse {
            Inverse::Unit=>{},
            Inverse::Child {child}=>{assert(s::registered(a,child));},
            Inverse::Provision {key}=>{
                assert(a.tables[actor].dom().contains(key));
                assert(a.control.fibers[actor].provisions.contains(key));
            },
            _=>{},
        }
        assert(mx::undo(receipt.model(),a).is_some());
        let b=mx::undo(receipt.model(),a).unwrap();
        crate::mixed_recovery::receipt_projection(receipt.model(),a);
        assert(b.control.fibers.dom()==a.control.fibers.dom());
        assert forall|n:usize| s::registered(a,n) implies
            b.control.fibers[n].phase==a.control.fibers[n].phase
            && b.control.fibers[n].committed==a.control.fibers[n].committed
            && (n!=actor ==> b.tables[n]==a.tables[n]) by {}
        assert(unit_child_provision_receipts(receipts.drop_last())) by {
            assert forall|i:int| 0<=i<receipts.drop_last().len() implies match #[trigger] receipts.drop_last()[i].inverse {
                Inverse::Unit | Inverse::Child {..} | Inverse::Provision {..}=>true,_=>false,
            } by {assert(receipts.drop_last()[i]==receipts[i]);}
        }
        assert(live_receipts(receipts.drop_last(),b,actor)) by {
            assert forall|i:int| 0<=i<receipts.drop_last().len() implies match #[trigger] receipts.drop_last()[i].inverse {
                Inverse::Provision {key}=>b.tables[actor].dom().contains(key),_=>true,
            } by {
                assert(receipts.drop_last()[i]==receipts[i]);
                if let Inverse::Provision {key}=receipts[i].inverse {
                    assert(a.tables[actor].dom().contains(key));
                    assert(receipt.inverse!=(Inverse::Provision {key}));
                }
            }
            assert forall|i:int,j:int| 0<=i<j<receipts.drop_last().len() implies match #[trigger] receipts.drop_last()[i].inverse {
                Inverse::Provision {key}=>#[trigger] receipts.drop_last()[j].inverse!=(Inverse::Provision {key}),_=>true,
            } by {assert(receipts.drop_last()[i]==receipts[i]);assert(receipts.drop_last()[j]==receipts[j]);}
        }
        assert forall|i:int| 0<=i<receipts.drop_last().len() implies receipts.drop_last()[i].actor==actor by {assert(receipts.drop_last()[i]==receipts[i]);}
        assert forall|i:int| 0<=i<receipts.drop_last().len() implies match #[trigger] receipts.drop_last()[i].inverse {
            Inverse::Child {child}=>s::registered(b,child),_=>true,
        } by {assert(receipts.drop_last()[i]==receipts[i]);}
        restore_unit_child_provisions(receipts.drop_last(),b,actor);
        assert forall|n:usize| s::registered(a,n) implies
            restore_receipts(receipts,a).unwrap().control.fibers[n].phase==a.control.fibers[n].phase
            && restore_receipts(receipts,a).unwrap().control.fibers[n].committed==a.control.fibers[n].committed
            && (n!=actor ==> restore_receipts(receipts,a).unwrap().tables[n]==a.tables[n]) by {assert(s::registered(b,n));}
    }
}

impl MixedDriver {
    pub open spec fn unit_child_provision_journal(&self,actor:usize)->bool {
        unit_child_provision_receipts(self.journal(actor))
    }
    /// A history-derived property of actual journals, not an added structural wf.
    pub open spec fn provision_recovery(&self)->bool {
        forall|actor:usize| r::registered(self.control(),actor) && self.unit_child_provision_journal(actor)
            ==> restore_receipts(self.journal(actor),self.primitive_state()).is_some()
    }

    pub proof fn provisions_from_source(&self,bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>,actor:usize)
        requires self.wf(),self.represents(bank,a),r::registered(self.control(),actor),ph::live_provisions(a),
        ensures live_receipts(self.journal(actor),a.state,actor),
    {
        reveal(MixedDriver::represents);reveal(MixedDriver::physical);
        assert forall|i:int| 0<=i<self.journal(actor).len() implies match #[trigger] self.journal(actor)[i].inverse {
            Inverse::Provision {key}=>a.state.tables[actor].dom().contains(key),_=>true,
        } by {
            let token=a.state.accumulators[actor][i];
            assert(a.history[token as int].landed.receipt==self.journal(actor)[i].model());
            if let Inverse::Provision {key}=self.journal(actor)[i].inverse {
                assert(ph::provision_at(a,actor,i)==Some(key));
                assert(a.state.tables[actor].dom().contains(key));
            }
        }
        assert forall|i:int,j:int| 0<=i<j<self.journal(actor).len() implies match #[trigger] self.journal(actor)[i].inverse {
            Inverse::Provision {key}=>#[trigger] self.journal(actor)[j].inverse!=(Inverse::Provision {key}),_=>true,
        } by {
            let left=a.state.accumulators[actor][i];let right=a.state.accumulators[actor][j];
            assert(a.history[left as int].landed.receipt==self.journal(actor)[i].model());
            assert(a.history[right as int].landed.receipt==self.journal(actor)[j].model());
            if let Inverse::Provision {key}=self.journal(actor)[i].inverse {
                assert(ph::provision_at(a,actor,i)==Some(key));
                assert(ph::provision_at(a,actor,j)==ph::provision_key(self.journal(actor)[j].model()));
                assert(ph::provision_at(a,actor,i)!=ph::provision_at(a,actor,j));
            }
        }
    }

    pub proof fn provision_recovery_from_source(&self,bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>)
        requires self.wf(),self.represents(bank,a),inv::well_formed(a.state),
            ch::retained(mx::kind(a.history),a.state),ph::live_provisions(a),
        ensures self.provision_recovery(),
    {
        reveal(MixedDriver::wf);reveal(MixedDriver::journal);reveal(MixedDriver::represents);
        reveal(MixedDriver::physical);reveal(MixedDriver::primitive_state);
        assert forall|actor:usize| r::registered(self.control(),actor) && self.unit_child_provision_journal(actor)
            implies restore_receipts(self.journal(actor),self.primitive_state()).is_some() by {
            self.retained_children_from_source(bank,a,actor);self.provisions_from_source(bank,a,actor);
            assert forall|i:int| 0<=i<self.journal(actor).len() implies self.journal(actor)[i].actor==actor by {
                assert(self.rows[actor as int].journal[i].actor==actor);
            }
            restore_unit_child_provisions(self.journal(actor),a.state,actor);
            restore_payload(self.journal(actor),a.state,self.primitive_state());
        }
    }

    pub proof fn provision_unload_domain(&self,actor:usize)
        requires self.wf(),self.provision_recovery(),self.unit_child_provision_journal(actor),
        ensures self.unload_enabled(actor)==self.cleanup_permitted(actor),
    {
        reveal(MixedDriver::unload_enabled);reveal(MixedDriver::cleanup_permitted);
        reveal(crate::Kernel::cleanup_enabled);
        if self.cleanup_permitted(actor) {self.kernel.paper_observations(actor);}
    }
}

}
