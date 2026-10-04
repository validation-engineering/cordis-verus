//! The unconditional completion clause of original Theorem 71 has a Unit-only
//! counterexample. Definition 58 allows an open final episode, and the rules
//! impose no scheduler or fairness condition. A legal finite prefix can finish
//! in Unloading after Divert, although Unload is enabled there.
//!
//! This does not refute resolution fixity or conditional recovery after an
//! actual Unload. No finite prefix here is claimed to be maximal. Repeated
//! O-Retire steps additionally give arbitrarily long legal delays at that state.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, iterators as it, lifecycle_ordering as life, mixed_grammar as g,
    mixed_orchestration as orchestration, mixed_transposition as insertion, observation as o,
    orchestration_support_cycle as unit, preservation as inv, projection as p,
    recovery_examples as ex, refinement as r, semantics as s, Phase, Port,
};
use vstd::prelude::*;

verus! {

/// Closing is an event in this sequence, not an out-of-bounds successor or the
/// existence of some possible extension which the sequence need never take.
pub open spec fn completion_in_sequence<V>(states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>,
    actor:usize,begin:int,after:int)->bool {
    states.len()==labels.len()+1 && exists|end:int| after<end<labels.len()
        && life::episode(states,actor,begin,end) && labels[end]==(actor,r::Rule::Unload)
        && !life::installed(states[end+1],actor)
}

/// The completion obligation in the Divert branch of the printed statement.
/// Its preceding phase/coherence assertions are deliberately not negated.
pub open spec fn printed_completion<V>(states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>,
    actor:usize,begin:int,end:int)->bool {
    let last_loading=life::loading_end(states,actor,begin,end);
    life::episode(states,actor,begin,end) && 0<=last_loading<labels.len()
        && last_loading<end && labels[last_loading]==(actor,r::Rule::Divert)
        ==> completion_in_sequence(states,labels,actor,begin,last_loading)
}

#[verifier::opaque]
pub open spec fn states()->Seq<g::Configuration<int,()>> {
    let a0=g::empty::<int,()>();
    let a1=insertion::insert(a0,0,None,ISet::empty(),ISet::empty(),());
    let a2=g::edit(a1,0,Phase::Loading,ISet::empty(),Some(()),Seq::empty());
    let a3=orchestration::retire(a2,0);
    let a4=g::edit(a3,0,Phase::Unloading,ISet::empty(),None,Seq::empty());
    seq![a0,a1,a2,a3,a4]
}
pub open spec fn labels()->Seq<(usize,r::Rule)> {
    seq![(0usize,r::Rule::Insert),(0usize,r::Rule::Begin),
        (0usize,r::Rule::Retire),(0usize,r::Rule::Divert)]
}

/// The single installed component has the original total, strongly witnessed
/// Unit on every state, independently of the guarded interpreter. Empty
/// declarations mean the witness also covers the exact component interface.
pub open spec fn paper_component()->bool {
    &&& it::paper_witnessed(|a:s::State<int>,b:s::State<int>|
            o::context_equal(ex::equality(),ISet::<Port>::empty(),p::project(a,ISet::empty()),p::project(b,ISet::empty())),
            unit::unit::<s::State<int>>(),())
    &&& it::terminates(unit::unit::<s::State<int>>(),())
    &&& forall|a:s::State<int>| #[trigger] unit::unit::<s::State<int>>()((),a).state==a
            && (unit::unit::<s::State<int>>()((),a).undo)(a)==a
            && unit::unit::<s::State<int>>()((),a).next.is_none()
}
pub proof fn component_witness()
    ensures paper_component(),
{
    unit::component_witness(ISet::empty());
    o::context_equivalence(ex::equality(),ISet::<Port>::empty());
    unit::total_unit(|a:s::State<int>,b:s::State<int>|
        o::context_equal(ex::equality(),ISet::<Port>::empty(),p::project(a,ISet::empty()),p::project(b,ISet::empty())));
}

/// Both the actual fixed-program interpreter and the total Unit Model take
/// exactly these four rules from empty. No history or execution is an input.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn actual_execution()
    ensures paper_component(),states().len()==5,labels().len()==4,states().first()==g::empty::<int,()>(),
        g::execution(ex::library(),unit::programs(),states(),labels()),
        life::trace(unit::unit_model(),g::states(states()),labels()),
        forall|i:int| 0<=i<states().len() ==> g::well_formed(ex::library(),unit::programs(),states()[i]),
        forall|i:int| 0<=i<states().len() ==> states()[i].history.len()==0,
        states().last().state.control.fibers[0usize].retired,
        states().last().state.control.fibers[0usize].phase==Phase::Unloading,
        states().last().state.accumulators[0usize].len()==0,
{
    component_witness();unit::component_witness(ISet::empty());reveal(states);
    let xs=states();let es=labels();let lib=ex::library();let programs=unit::programs();
    insertion::insertion_step(lib,programs,xs[0],0,None,ISet::empty(),ISet::empty(),());
    assert(g::step(lib,programs,xs[1],xs[2],0,r::Rule::Begin));
    ch::concrete_child_retirement(xs[2].state,0);
    assert(g::step(lib,programs,xs[2],xs[3],0,r::Rule::Retire));
    assert(g::step(lib,programs,xs[3],xs[4],0,r::Rule::Divert));
    assert(g::execution(lib,programs,xs,es)) by {
        assert forall|i:int| 0<=i<es.len() implies g::step(lib,programs,xs[i],xs[i+1],es[i].0,es[i].1) by {
            if i==0 {} else if i==1 {} else if i==2 {} else {assert(i==3);}
        }
    }
    ex::primitive_theory();g::from_empty_safe(ex::equality(),lib,programs,xs,es);
    assert forall|i:int| 0<=i<es.len() implies
        s::step(unit::unit_model(),g::states(xs)[i],g::states(xs)[i+1],es[i].0,es[i].1)
            && inv::admissible_step(unit::unit_model(),g::states(xs)[i],g::states(xs)[i+1],es[i].0,es[i].1) by {
        if i==0 {} else if i==1 {} else if i==2 {} else {assert(i==3);}
    }
}

/// The episode is [2,4], and its initial Loading interval is [2,3]. Thus the
/// Divert branch really applies (3 < 4), but the given episode has not closed.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn actual_counterexample()
    ensures paper_component(),g::execution(ex::library(),unit::programs(),states(),labels()),
        states().first()==g::empty::<int,()>(),life::trace(unit::unit_model(),g::states(states()),labels()),
        life::episode(g::states(states()),0,2,4),life::loading_end(g::states(states()),0,2,4)==3,
        labels()[3]==(0usize,r::Rule::Divert),3int<4int,
        life::installed(states().last().state,0),4int==labels().len(),
        !completion_in_sequence(g::states(states()),labels(),0,2,3),
        !printed_completion(g::states(states()),labels(),0,2,4),
        g::step(ex::library(),unit::programs(),states().last(),g::unload(states().last(),0),0,r::Rule::Unload),
{
    actual_execution();reveal(states);let xs=states();let es=labels();
    assert forall|i:int| 2<=i<=4 implies life::installed(g::states(xs)[i],0) by {
        if i==2 {} else if i==3 {} else {assert(i==4);}
    }
    reveal_with_fuel(life::loading_end,3);
    assert(!completion_in_sequence(g::states(xs),es,0,2,3));
}

pub open spec fn delayed_states(count:nat)->Seq<g::Configuration<int,()>> {
    states()+Seq::new(count,|_:int|states().last())
}
pub open spec fn delayed_labels(count:nat)->Seq<(usize,r::Rule)> {
    labels()+Seq::new(count,|_:int|(0usize,r::Rule::Retire))
}

/// For every finite delay, the very same original O-Retire rule may be taken
/// repeatedly instead of the enabled Unload. This is not a maximality claim.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn arbitrary_delay(count:nat)
    ensures paper_component(),delayed_states(count).len()==5+count,delayed_labels(count).len()==4+count,
        delayed_states(count).first()==g::empty::<int,()>(),
        g::execution(ex::library(),unit::programs(),delayed_states(count),delayed_labels(count)),
        life::trace(unit::unit_model(),g::states(delayed_states(count)),delayed_labels(count)),
        forall|i:int| 0<=i<delayed_states(count).len() ==> g::well_formed(ex::library(),unit::programs(),delayed_states(count)[i]),
        life::episode(g::states(delayed_states(count)),0,2,(4+count) as int),
        life::loading_end(g::states(delayed_states(count)),0,2,(4+count) as int)==3,
        !completion_in_sequence(g::states(delayed_states(count)),delayed_labels(count),0,2,3),
        !printed_completion(g::states(delayed_states(count)),delayed_labels(count),0,2,(4+count) as int),
        forall|i:int| 4<=i<delayed_states(count).len() ==> life::installed(delayed_states(count)[i].state,0)
            && g::step(ex::library(),unit::programs(),delayed_states(count)[i],g::unload(delayed_states(count)[i],0),0,r::Rule::Unload),
{
    actual_execution();actual_counterexample();reveal(states);
    let xs=delayed_states(count);let es=delayed_labels(count);let a=states().last();
    ch::concrete_child_retirement(a.state,0);
    assert(g::step(ex::library(),unit::programs(),a,a,0,r::Rule::Retire));
    assert(s::step(unit::unit_model(),a.state,a.state,0,r::Rule::Retire));
    assert forall|i:int| 0<=i<es.len() implies g::step(ex::library(),unit::programs(),xs[i],xs[i+1],es[i].0,es[i].1)
        && s::step(unit::unit_model(),g::states(xs)[i],g::states(xs)[i+1],es[i].0,es[i].1)
        && inv::admissible_step(unit::unit_model(),g::states(xs)[i],g::states(xs)[i+1],es[i].0,es[i].1) by {
        if i<4 {assert(xs[i]==states()[i]);assert(xs[i+1]==states()[i+1]);assert(es[i]==labels()[i]);}
        else {assert(xs[i]==a);assert(xs[i+1]==a);assert(es[i]==(0usize,r::Rule::Retire));}
    }
    assert forall|i:int| 0<=i<xs.len() implies g::well_formed(ex::library(),unit::programs(),xs[i]) by {
        if i<5 {assert(xs[i]==states()[i]);}else{assert(xs[i]==a);}
    }
    assert forall|i:int| 2<=i<=4+count implies life::installed(g::states(xs)[i],0) by {
        if i==2 {} else if i==3 {} else {assert(xs[i]==a);}
    }
    reveal_with_fuel(life::loading_end,3);
    assert(!completion_in_sequence(g::states(xs),es,0,2,3)) by {
        assert forall|end:int| 3<end<es.len() implies es[end]!=(0usize,r::Rule::Unload) by {assert(es[end]==(0usize,r::Rule::Retire));}
    }
    assert forall|i:int| 4<=i<xs.len() implies life::installed(xs[i].state,0)
        && g::step(ex::library(),unit::programs(),xs[i],g::unload(xs[i],0),0,r::Rule::Unload) by {assert(xs[i]==a);}
}

} // verus!
