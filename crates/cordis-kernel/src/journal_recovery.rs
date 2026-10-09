//! All four executable inverse variants have history-derived recovery domains.
//!
//! Xor's scalar inverse is total; its captured provider and occupied slot still
//! require provenance. This is a domain theorem for this executable language,
//! not totality of arbitrary plugin inverses or a foreign-replay equation.
use super::MixedDriver;
#[cfg(verus_keep_ghost)]
use super::{restore_payload, restore_receipts, Blueprint, Index, Inverse, Receipt};
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, grammar_lift as gl, mixed_grammar as mx, operation_history as oh,
    preservation as inv, provision_history as ph, refinement as r, semantics as s, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn live_xors(receipts:Seq<Receipt>,a:s::State<u64>,actor:usize)->bool {
    &&& forall|i:int| 0<=i<receipts.len() ==> match #[trigger] receipts[i].inverse {
        Inverse::Xor {provider,key,..}=>s::registered(a,provider)
            && gl::resolve(a,actor,key)==Some(provider) && a.tables[provider].dom().contains(key),
        _=>true,
    }
    &&& forall|i:int,j:int| 0<=i<j<receipts.len() ==> match #[trigger] receipts[i].inverse {
        Inverse::Xor {provider,key,..}=>provider!=actor || #[trigger] receipts[j].inverse!=(Inverse::Provision {key}),
        _=>true,
    }
}

/// Resolution depends on declarations and committed identity, not current
/// publication, retirement or the current value of a service slot.
pub proof fn resolve_frame(a:s::State<u64>,b:s::State<u64>,actor:usize,key:Port)
    requires s::registered(a,actor),s::registered(b,actor),
        r::interface_same(a.control.fibers[actor],b.control.fibers[actor]),
        a.control.fibers[actor].committed==b.control.fibers[actor].committed,
    ensures gl::resolve(a,actor,key)==gl::resolve(b,actor,key),
{}

#[verifier::spinoff_prover]
pub proof fn restore_all(receipts:Seq<Receipt>,a:s::State<u64>,actor:usize)
    requires inv::well_formed(a),s::registered(a,actor),
        super::provision_recovery::live_receipts(receipts,a,actor),live_xors(receipts,a,actor),
        forall|i:int| 0<=i<receipts.len() ==> receipts[i].actor==actor,
        forall|i:int| 0<=i<receipts.len() ==> match #[trigger] receipts[i].inverse {
            Inverse::Child {child}=>s::registered(a,child),_=>true,
        },
    ensures restore_receipts(receipts,a).is_some(),inv::well_formed(restore_receipts(receipts,a).unwrap()),
        restore_receipts(receipts,a).unwrap().control.fibers.dom()==a.control.fibers.dom(),
        forall|n:usize| s::registered(a,n) ==> {
            let node=restore_receipts(receipts,a).unwrap().control.fibers[n];
            &&& r::interface_same(a.control.fibers[n],node)
            &&& node.phase==a.control.fibers[n].phase && node.committed==a.control.fibers[n].committed
            &&& (n!=actor ==> restore_receipts(receipts,a).unwrap().tables[n].dom()==a.tables[n].dom())
        },
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
            Inverse::Xor {provider,key,..}=>{
                assert(s::registered(a,provider));assert(gl::resolve(a,actor,key)==Some(provider));
                assert(a.tables[provider].dom().contains(key));
            },
        }
        assert(mx::undo(receipt.model(),a).is_some());
        let b=mx::undo(receipt.model(),a).unwrap();
        crate::mixed_recovery::receipt_projection(receipt.model(),a);
        assert(b.control.fibers.dom()==a.control.fibers.dom());
        assert forall|n:usize| s::registered(a,n) implies {
            &&& r::interface_same(a.control.fibers[n],b.control.fibers[n])
            &&& b.control.fibers[n].phase==a.control.fibers[n].phase
            &&& b.control.fibers[n].committed==a.control.fibers[n].committed
            &&& (n!=actor ==> b.tables[n].dom()==a.tables[n].dom())
        } by {
            if let Inverse::Xor {provider,key,..}=receipt.inverse {
                if n==provider {assert(a.tables[n].dom().contains(key));}
            }
        }
        assert(super::provision_recovery::live_receipts(receipts.drop_last(),b,actor)) by {
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
        assert(live_xors(receipts.drop_last(),b,actor)) by {
            assert forall|i:int| 0<=i<receipts.drop_last().len() implies match #[trigger] receipts.drop_last()[i].inverse {
                Inverse::Xor {provider,key,..}=>s::registered(b,provider)
                    && gl::resolve(b,actor,key)==Some(provider) && b.tables[provider].dom().contains(key),
                _=>true,
            } by {
                assert(receipts.drop_last()[i]==receipts[i]);
                if let Inverse::Xor {provider,key,..}=receipts[i].inverse {
                    assert(s::registered(a,provider));assert(a.tables[provider].dom().contains(key));
                    assert(gl::resolve(a,actor,key)==Some(provider));
                    resolve_frame(a,b,actor,key);
                    assert(provider!=actor || receipt.inverse!=(Inverse::Provision {key}));
                }
            }
            assert forall|i:int,j:int| 0<=i<j<receipts.drop_last().len() implies match #[trigger] receipts.drop_last()[i].inverse {
                Inverse::Xor {provider,key,..}=>provider!=actor || #[trigger] receipts.drop_last()[j].inverse!=(Inverse::Provision {key}),
                _=>true,
            } by {assert(receipts.drop_last()[i]==receipts[i]);assert(receipts.drop_last()[j]==receipts[j]);}
        }
        assert forall|i:int| 0<=i<receipts.drop_last().len() implies receipts.drop_last()[i].actor==actor by {assert(receipts.drop_last()[i]==receipts[i]);}
        assert forall|i:int| 0<=i<receipts.drop_last().len() implies match #[trigger] receipts.drop_last()[i].inverse {
            Inverse::Child {child}=>s::registered(b,child),_=>true,
        } by {assert(receipts.drop_last()[i]==receipts[i]);}
        restore_all(receipts.drop_last(),b,actor);
        assert forall|n:usize| s::registered(a,n) implies {
            let node=restore_receipts(receipts,a).unwrap().control.fibers[n];
            &&& r::interface_same(a.control.fibers[n],node)
            &&& node.phase==a.control.fibers[n].phase && node.committed==a.control.fibers[n].committed
            &&& (n!=actor ==> restore_receipts(receipts,a).unwrap().tables[n].dom()==a.tables[n].dom())
        } by {assert(s::registered(b,n));}
    }
}

impl MixedDriver {
    /// All real receipts in this closed interpreter are covered, including Xor.
    pub open spec fn journal_recovery(&self)->bool {
        forall|actor:usize| r::registered(self.control(),actor)
            ==> restore_receipts(self.journal(actor),self.primitive_state()).is_some()
    }
    pub proof fn operations_from_source(&self,bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>,actor:usize)
        requires self.wf(),self.represents(bank,a),r::registered(self.control(),actor),oh::live_operations(a),
        ensures live_xors(self.journal(actor),a.state,actor),
    {
        reveal(MixedDriver::represents);reveal(MixedDriver::physical);
        assert forall|i:int| 0<=i<self.journal(actor).len() implies match #[trigger] self.journal(actor)[i].inverse {
            Inverse::Xor {provider,key,..}=>s::registered(a.state,provider)
                && gl::resolve(a.state,actor,key)==Some(provider) && a.state.tables[provider].dom().contains(key),
            _=>true,
        } by {
            let token=a.state.accumulators[actor][i];
            assert(a.history[token as int].landed.receipt==self.journal(actor)[i].model());
            if let Inverse::Xor {provider,key,..}=self.journal(actor)[i].inverse {
                assert(oh::operation_at(a,actor,i)==Some((provider,key)));
            }
        }
        assert forall|i:int,j:int| 0<=i<j<self.journal(actor).len() implies match #[trigger] self.journal(actor)[i].inverse {
            Inverse::Xor {provider,key,..}=>provider!=actor || #[trigger] self.journal(actor)[j].inverse!=(Inverse::Provision {key}),
            _=>true,
        } by {
            let left=a.state.accumulators[actor][i];let right=a.state.accumulators[actor][j];
            assert(a.history[left as int].landed.receipt==self.journal(actor)[i].model());
            assert(a.history[right as int].landed.receipt==self.journal(actor)[j].model());
            if let Inverse::Xor {provider,key,..}=self.journal(actor)[i].inverse {
                assert(oh::operation_at(a,actor,i)==Some((provider,key)));
                if let Inverse::Provision {key: removed}=self.journal(actor)[j].inverse {
                    assert(ph::provision_at(a,actor,j)==Some(removed));
                    assert(provider!=actor || key!=removed);
                }
            }
        }
    }
    pub proof fn journal_recovery_from_source(&self,bank:Seq<Blueprint>,a:mx::Configuration<u64,Index>)
        requires self.wf(),self.represents(bank,a),inv::well_formed(a.state),
            ch::retained(mx::kind(a.history),a.state),ph::live_provisions(a),oh::live_operations(a),
        ensures self.journal_recovery(),
    {
        reveal(MixedDriver::wf);reveal(MixedDriver::journal);reveal(MixedDriver::represents);
        reveal(MixedDriver::physical);reveal(MixedDriver::primitive_state);
        assert forall|actor:usize| r::registered(self.control(),actor)
            implies restore_receipts(self.journal(actor),self.primitive_state()).is_some() by {
            self.retained_children_from_source(bank,a,actor);self.provisions_from_source(bank,a,actor);
            self.operations_from_source(bank,a,actor);
            assert forall|i:int| 0<=i<self.journal(actor).len() implies self.journal(actor)[i].actor==actor by {
                assert(self.rows[actor as int].journal[i].actor==actor);
            }
            restore_all(self.journal(actor),a.state,actor);
            restore_payload(self.journal(actor),a.state,self.primitive_state());
        }
    }
    pub proof fn journal_unload_domain(&self,actor:usize)
        requires self.wf(),self.journal_recovery(),
        ensures self.unload_enabled(actor)==self.cleanup_permitted(actor),
    {
        reveal(MixedDriver::unload_enabled);reveal(MixedDriver::cleanup_permitted);
        reveal(crate::Kernel::cleanup_enabled);
        if self.cleanup_permitted(actor) {self.kernel.paper_observations(actor);}
    }
}

}
