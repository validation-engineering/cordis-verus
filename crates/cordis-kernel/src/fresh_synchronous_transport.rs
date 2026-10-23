//! The real synchronous departure branch survives deletion and alpha-renaming.
#[cfg(verus_keep_ghost)]
use crate::{
    alpha as n, closed_region_deletion as region, fresh_equivariance as e, fresh_grammar as f,
    fresh_semantics as fs,
    mixed_driver::fresh::{self as driver, compaction, names},
    mixed_driver::{self as core, Blueprint, Index, Transition},
    mixed_grammar as g, Port,
};
use vstd::prelude::*;
verus! {
#[verifier::spinoff_prover]
proof fn delete_inner(bank:Seq<Blueprint>,states:Seq<g::Configuration<u64,Index>>,ts:Seq<Transition>,keep:Seq<bool>,r:region::Region,rho:spec_fn(nat)->nat)
    requires fs::execution(core::library(),driver::programs(bank),states,driver::labels(ts)),
        super::trace(states,ts),compaction::source::mask(ts,keep,r),region::trace::admissible(states,r),
        forall|i:int|0<=i<states.len() ==> fs::well_formed(core::library(),driver::programs(bank),states[i]) && region::execution::numbered(states[i],r,rho),
    ensures super::trace(region::fresh_trace::delete(states,driver::labels(ts),r,rho),compaction::selected(ts,keep)),
    decreases ts.len(),
{
    if ts.len()>0 {
        let before=states.drop_last();let prior=ts.drop_last();let prior_keep=keep.drop_last();let t=ts.last();
        assert(driver::labels(prior)==driver::labels(ts).drop_last());
        region::fresh_trace::histories(core::library(),driver::programs(bank),states,driver::labels(ts));
        assert(region::trace::admissible(before,r)) by {
            assert forall|i:int|0<=i<before.last().history.len() implies region::local(before.last().history[i].landed.receipt,r) by {
                assert(before.last().history[i]==states.last().history[i]);
            }
        }
        delete_inner(bank,before,prior,prior_keep,r,rho);
        if keep.last() {
            region::fresh_trace::construct(core::library(),driver::programs(bank),before,driver::labels(prior),r,rho);
            let old=region::fresh_trace::delete(before,driver::labels(prior),r,rho);let z=region::configuration(states.last(),r,rho);
            assert(super::plain(old.last(),z,t)) by {
                if let Transition::Depart {..}=t {assert(before.last().history==states.last().history);}
            }
            super::append(old,compaction::selected(prior,prior_keep),z,t);
        }
    }
}
pub proof fn deletion(bank:Seq<Blueprint>,states:Seq<g::Configuration<u64,Index>>,ts:Seq<Transition>,keep:Seq<bool>,r:region::Region)
    requires fs::execution(core::library(),driver::programs(bank),states,driver::labels(ts)),states.first()==g::empty::<u64,Index>(),
        super::trace(states,ts),compaction::source::mask(ts,keep,r),region::trace::admissible(states,r),
    ensures super::trace(region::fresh_trace::target(states,driver::labels(ts),r),compaction::selected(ts,keep)),
{
    driver::weak_theory();fs::from_empty_safe(|_:Port,x:u64,y:u64|x==y,core::library(),driver::programs(bank),states,driver::labels(ts));
    region::fresh_trace::histories(core::library(),driver::programs(bank),states,driver::labels(ts));
    let rho=|t:nat|region::index(states.last().history,r,t);
    assert forall|i:int|0<=i<states.len() implies region::execution::numbered(states[i],r,rho) by {
        assert forall|t:nat|t<=states[i].history.len() implies rho(t)==region::index(states[i].history,r,t) by {
            region::index_prefix(states[i].history,states.last().history,r,t);
        }
    }
    delete_inner(bank,states,ts,keep,r,rho);
}
pub proof fn renaming(rho:n::Renaming,states:Seq<g::Configuration<u64,Index>>,ts:Seq<Transition>)
    requires super::trace(states,ts),
    ensures super::trace(e::configurations(rho,f::action_map(f::name_free::<Index>(),rho),states),compaction::renamed(rho,ts)),
{
    let h=f::action_map(f::name_free::<Index>(),rho);
    assert forall|i:int|0<=i<ts.len() implies super::plain(e::configurations(rho,h,states)[i],e::configurations(rho,h,states)[i+1],compaction::renamed(rho,ts)[i]) by {
        assert(super::plain(states[i],states[i+1],ts[i]));
        match ts[i] {Transition::Depart {..}=>{assert(states[i].history==states[i+1].history);},_=>{}}
        assert(compaction::renamed(rho,ts)[i]==names::renamed(rho,ts[i]));
    }
}
}
