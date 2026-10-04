//! Lemma 75's mixed-order obstruction using only external orchestration.
//!
//! O-Insert permits a registered nonroot parent. No activation or Child stage
//! is needed to create this cycle. Every installed program is the total Unit
//! iterator, whose paper witness is proved independently of the strict runner.
//! Unit need not install its declared provisions; Definition 76 is deliberately
//! not asserted, and this example does not refute results requiring it.
#[cfg(verus_keep_ghost)]
use crate::{
    calculus, child_history as ch, dependent_grammar as d, foundations as f, global,
    grammar_lift as lift, iterators as it, mixed_grammar as g,
    mixed_orchestration as orchestration, mixed_syntax as syntax, mixed_transposition as t,
    observation as o, projection as p, quotient as q, recovery_examples as ex, refinement as r,
    semantics as s, Binding, Phase, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn programs()->g::Programs<Port,int,int,(),()> {
    |_:usize| |_:()| g::Node::Dependent {node:d::Node::Unit}
}

/// A genuine total iterator on arbitrary states, not an Option failure sink.
pub open spec fn unit<S>()->q::IteratorFamily<S,()> {
    it::embed(|a:S|f::unit(a))
}
pub proof fn total_unit<S>(eq:spec_fn(S,S)->bool)
    requires calculus::equivalence(eq),
    ensures it::paper_witnessed(eq,unit::<S>(),()),it::terminates(unit::<S>(),()),
        forall|a:S| #[trigger] unit::<S>()((),a).state==a
            && (unit::<S>()((),a).undo)(a)==a && unit::<S>()((),a).next.is_none(),
{
    assert(o::witnessed_effect(eq,|a:S|f::unit(a)));
    it::embedding_paper_witness(eq,|a:S|f::unit(a));
    it::inductive_termination(unit::<S>(),());
}
/// All Definition 48 interfaces admit this same total witnessed unit. The
/// witness is on the Definition 51 all-table projection, not lifecycle fields.
pub proof fn component_witness(keys:ISet<Port>)
    ensures it::paper_witnessed(|a:s::State<int>,b:s::State<int>|
        o::context_equal(ex::equality(),keys,p::project(a,keys),p::project(b,keys)),unit::<s::State<int>>(),()),
        it::terminates(unit::<s::State<int>>(),()),
        forall|actor:usize,provisions:ISet<Port>| syntax::member(ex::library(),programs(),actor,keys,provisions,()),
{
    o::context_equivalence(ex::equality(),keys);
    let eq=|a:s::State<int>,b:s::State<int>|o::context_equal(ex::equality(),keys,p::project(a,keys),p::project(b,keys));
    assert(calculus::equivalence(eq));total_unit(eq);
    assert forall|actor:usize,provisions:ISet<Port>| syntax::member(ex::library(),programs(),actor,keys,provisions,()) by {
        syntax::constructor_member(ex::library(),programs(),actor,keys,provisions,());
    }
}

/// The registered-domain runner returns exactly that total Unit's state,
/// continuation and inverse. Its absent-actor guard remains a real failure.
pub proof fn actual_unit(a:s::State<int>,actor:usize)
    ensures s::confined_write(a,unit::<s::State<int>>()((),a).state,actor),
        s::registered(a,actor) ==> {
            let out=g::run(ex::library(),programs()(actor)(()),a,actor).unwrap();
            &&& g::run(ex::library(),programs()(actor)(()),a,actor).is_some()
            &&& out.state==unit::<s::State<int>>()((),a).state && out.next==unit::<s::State<int>>()((),a).next
            &&& out.spawn.is_none() && out.receipt==g::Receipt::Table {receipt:lift::Receipt {actor,inverse:lift::Inverse::Unit}}
            &&& g::undo(out.receipt,out.state)==Some((unit::<s::State<int>>()((),a).undo)(a))
        },
        !s::registered(a,actor) ==> g::run(ex::library(),programs()(actor)(()),a,actor).is_none(),
{ }

pub open spec fn unit_model()->s::Model<int> {
    s::Model {iterate:|_:usize,_:nat,a:s::State<int>|s::Yield {state:a,inverse:0,next:None},undo:|_:nat,a:s::State<int>|a}
}
#[verifier::opaque]
pub open spec fn trace()->Seq<g::Configuration<int,()>> {
    let a0=g::empty::<int,()>();
    let a1=t::insert(a0,0,None,ISet::empty(),ex::provided(0),());
    let a2=t::insert(a1,1,None,ex::provided(0),ISet::empty(),());
    let a3=t::insert(a2,2,Some(1),ex::provided(2),ex::provided(1),());
    let a4=orchestration::retire(a3,0);let a5=orchestration::remove(a4,0);
    let a6=t::insert(a5,3,None,ex::provided(1),ex::provided(0),());
    seq![a0,a1,a2,a3,a4,a5,a6]
}
pub open spec fn labels()->Seq<(usize,r::Rule)> {
    seq![(0usize,r::Rule::Insert),(1usize,r::Rule::Insert),(2usize,r::Rule::Insert),
        (0usize,r::Rule::Retire),(0usize,r::Rule::Remove),(3usize,r::Rule::Insert)]
}

/// Six actual full-state steps from the empty registry. The nonroot Insert is
/// an external rule, so this proof invokes no partial Child primitive.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn actual_execution()
    ensures trace().len()==7,trace().first()==g::empty::<int,()>(),
        g::execution(ex::library(),programs(),trace(),labels()),
        s::execution(unit_model(),g::states(trace()),labels()),
        forall|i:int| 0<=i<trace().len() ==> g::well_formed(ex::library(),programs(),trace()[i]),
{
    reveal(trace);let states=trace();let steps=labels();let lib=ex::library();
    component_witness(ex::provided(0));component_witness(ex::provided(2).union(ex::provided(1)));
    component_witness(ex::provided(1).union(ex::provided(0)));
    assert(ISet::<Port>::empty().union(ex::provided(0)) =~= ex::provided(0));
    assert(ex::provided(0).union(ISet::<Port>::empty()) =~= ex::provided(0));
    t::insertion_step(lib,programs(),states[0],0,None,ISet::empty(),ex::provided(0),());
    t::insertion_step(lib,programs(),states[1],1,None,ex::provided(0),ISet::empty(),());
    t::insertion_step(lib,programs(),states[2],2,Some(1),ex::provided(2),ex::provided(1),());
    ch::concrete_child_retirement(states[3].state,0);
    assert(g::step(lib,programs(),states[3],states[4],0,r::Rule::Retire));
    assert(g::step(lib,programs(),states[4],states[5],0,r::Rule::Remove));
    t::insertion_step(lib,programs(),states[5],3,None,ex::provided(1),ex::provided(0),());
    assert(g::execution(lib,programs(),states,steps)) by {
        assert forall|i:int| 0<=i<steps.len() implies g::step(lib,programs(),states[i],states[i+1],steps[i].0,steps[i].1) by {
            if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else {assert(i==5);}
        }
    }
    ex::primitive_theory();g::from_empty_safe(ex::equality(),lib,programs(),states,steps);
    assert(s::execution(unit_model(),g::states(states),steps)) by {
        assert forall|i:int| 0<=i<steps.len() implies s::step(unit_model(),g::states(states)[i],g::states(states)[i+1],steps[i].0,steps[i].1) by {
            assert(g::step(lib,programs(),states[i],states[i+1],steps[i].0,steps[i].1));
            if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else {assert(i==5);}
        }
    }
}

/// An interface catalogue remembers the removed provider without pretending
/// it coexists with its replacement. Only declarations participate in ranks.
pub open spec fn catalogue()->r::State {global::replacement_historical_interfaces()}
pub open spec fn ranks()->Seq<nat> {seq![0nat,2nat,0nat,1nat]}

#[verifier::spinoff_prover]
pub proof fn trace_shape()
    ensures trace().len()==7,
        forall|i:int,n:usize| 0<=i<trace().len() && s::registered(trace()[i].state,n) ==> {
            let a=trace()[i].state;
            &&& n<4 && r::registered(catalogue(),n)
            &&& a.control.fibers[n].provisions==catalogue().fibers[n].provisions
            &&& a.control.fibers[n].dependencies==catalogue().fibers[n].dependencies
            &&& a.control.fibers[n].parent==catalogue().fibers[n].parent
            &&& a.control.fibers[n].phase==Phase::Inactive && a.tables[n].is_empty()
            &&& a.accumulators[n].len()==0 && a.control.fibers[n].committed.is_empty()
        },
        forall|i:int| 0<=i<trace().len() ==> trace()[i].history.len()==0,
        trace().last().state.control.fibers.dom()==ISet::empty().insert(1usize).insert(2usize).insert(3usize),
        trace().last().state.control.fibers[2usize].parent==Some(1usize),
        !trace().last().state.control.fibers[2usize].retired,
        !global::retirement_closed(trace().last().state.control),
{
    reveal(trace);
    assert forall|i:int,n:usize| 0<=i<trace().len() && s::registered(trace()[i].state,n) implies {
            let a=trace()[i].state;
            &&& n<4 && r::registered(catalogue(),n)
            &&& a.control.fibers[n].provisions==catalogue().fibers[n].provisions
            &&& a.control.fibers[n].dependencies==catalogue().fibers[n].dependencies
            &&& a.control.fibers[n].parent==catalogue().fibers[n].parent
            &&& a.control.fibers[n].phase==Phase::Inactive && a.tables[n].is_empty()
            &&& a.accumulators[n].len()==0 && a.control.fibers[n].committed.is_empty()
    } by {
        if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else if i==5 {} else {assert(i==6);}
        if n==0 {} else if n==1 {} else if n==2 {} else {assert(n==3);}
    }
    assert(trace().last().state.control.fibers.dom() =~= ISet::empty().insert(1usize).insert(2usize).insert(3usize));
    let a=trace().last().state.control;
    assert(r::registered(a,2usize));assert(a.fibers[2usize].parent==Some(1usize));
    assert(a.fibers[1usize].phase==Phase::Inactive && !a.fibers[2usize].retired);
    if global::retirement_closed(a) {assert(a.fibers[2usize].retired);}
}

/// Both every live registry and the union of all historical interfaces have
/// acyclic provider precedence. The obstruction is in the mixed parent union.
pub proof fn provider_rankings()
    ensures global::precedence_ranking(catalogue(),ranks()),
        forall|i:int| 0<=i<trace().len() ==> global::precedence_ranking(trace()[i].state.control,ranks()),
{
    global::replacement_support_cycle();trace_shape();
    assert forall|i:int| 0<=i<trace().len() implies global::precedence_ranking(trace()[i].state.control,ranks()) by {
        let a=trace()[i].state.control;
        assert forall|n:usize| r::registered(a,n) implies n<ranks().len() by {
            assert(s::registered(trace()[i].state,n));assert(n<4);
        }
        assert forall|m:usize,n:usize| global::predecessor(a,m,n) implies ranks()[m as int]<ranks()[n as int] by {
            assert(s::registered(trace()[i].state,m));assert(s::registered(trace()[i].state,n));
            assert(r::registered(catalogue(),m));assert(r::registered(catalogue(),n));
            assert(a.fibers[m].provisions==catalogue().fibers[m].provisions);
            assert(a.fibers[n].dependencies==catalogue().fibers[n].dependencies);
            let k=choose|k:Port|a.fibers[m].provisions.contains(k) && a.fibers[n].dependencies.contains(k);
            assert(catalogue().fibers[m].provisions.contains(k) && catalogue().fibers[n].dependencies.contains(k));
            assert(global::predecessor(catalogue(),m,n));
        }
    }
}

/// Every catalogue entry was actually introduced; no unexecuted interface is
/// used to make the historical acyclicity condition artificially stronger.
#[verifier::spinoff_prover]
pub proof fn catalogue_provenance()
    ensures forall|n:usize| r::registered(catalogue(),n) ==> exists|i:int|
        0<=i<trace().len() && s::registered(trace()[i].state,n)
            && trace()[i].state.control.fibers[n].provisions==catalogue().fibers[n].provisions
            && trace()[i].state.control.fibers[n].dependencies==catalogue().fibers[n].dependencies
            && trace()[i].state.control.fibers[n].parent==catalogue().fibers[n].parent,
        forall|i:int| 0<=i<labels().len() ==> labels()[i].1==r::Rule::Insert
            || labels()[i].1==r::Rule::Retire || labels()[i].1==r::Rule::Remove,
{
    trace_shape();reveal(trace);
    assert forall|n:usize| r::registered(catalogue(),n) implies exists|i:int|
        0<=i<trace().len() && s::registered(trace()[i].state,n)
            && trace()[i].state.control.fibers[n].provisions==catalogue().fibers[n].provisions
            && trace()[i].state.control.fibers[n].dependencies==catalogue().fibers[n].dependencies
            && trace()[i].state.control.fibers[n].parent==catalogue().fibers[n].parent by {
        let i=if n==0 {1int} else if n==1 {2int} else if n==2 {3int} else {6int};
        assert(0<=i<trace().len() && s::registered(trace()[i].state,n));
        assert(trace()[i].state.control.fibers[n].provisions==catalogue().fibers[n].provisions
            && trace()[i].state.control.fibers[n].dependencies==catalogue().fibers[n].dependencies
            && trace()[i].state.control.fibers[n].parent==catalogue().fibers[n].parent);
    }
}

#[verifier::spinoff_prover]
pub proof fn quiet_mixed_cycle()
    ensures s::quiet(trace().last().state),r::quiet(trace().last().state.control),
        global::predecessor(trace().last().state.control,2,3),
        global::predecessor(trace().last().state.control,3,1),
        trace().last().state.control.fibers[2usize].parent==Some(1usize),
        forall|rank:Seq<nat>| !global::support_ranking(trace().last().state.control,rank),
        global::support_solution(trace().last().state.control,ISet::empty()),
{
    trace_shape();let a=trace().last().state;let control=a.control;
    reveal(trace);
    assert forall|n:usize| s::registered(a,n) implies !(exists|view:ISet<Binding>|s::target(a,n,view)) by {
        let k=if n==1 {ex::key(0)} else if n==2 {ex::key(2)} else {ex::key(1)};
        assert(control.fibers[n].dependencies.contains(k));
        assert(!(exists|m:usize|s::publishes(a,k,m)));
    }
    s::quiet_total_agrees(a);
    assert(control.fibers[2usize].provisions.contains(ex::key(1)) && control.fibers[3usize].dependencies.contains(ex::key(1)));
    assert(control.fibers[3usize].provisions.contains(ex::key(0)) && control.fibers[1usize].dependencies.contains(ex::key(0)));
    assert(global::predecessor(control,2,3));assert(global::predecessor(control,3,1));
    assert forall|rank:Seq<nat>| !global::support_ranking(control,rank) by {
        if global::support_ranking(control,rank) {
            assert(rank[2]<rank[3]);assert(rank[3]<rank[1]);assert(rank[1]<rank[2]);
        }
    }
    assert forall|n:usize| !global::support_clause(control,ISet::empty(),n) by {
        if r::registered(control,n) {
            let k=if n==1 {ex::key(0)} else if n==2 {ex::key(2)} else {ex::key(1)};
            assert(control.fibers[n].dependencies.contains(k));
            assert(!global::provided_by(control,ISet::empty(),k));
        }
    }
}

/// The counterexample refutes well-foundedness, without claiming that its
/// support equation has several solutions: the missing z forces the empty one.
pub proof fn support_still_unique(selected:ISet<usize>)
    requires global::support_solution(trace().last().state.control,selected),
    ensures selected==ISet::<usize>::empty(),
{
    reveal(trace);let a=trace().last().state.control;
    assert(!global::provided_by(a,selected,ex::key(2)));
    assert(!selected.contains(2usize)) by {assert(a.fibers[2usize].dependencies.contains(ex::key(2)));}
    assert(!global::provided_by(a,selected,ex::key(1)));
    assert(!selected.contains(3usize)) by {assert(a.fibers[3usize].dependencies.contains(ex::key(1)));}
    assert(!global::provided_by(a,selected,ex::key(0)));
    assert(!selected.contains(1usize)) by {assert(a.fibers[1usize].dependencies.contains(ex::key(0)));}
    assert(selected =~= ISet::empty()) by {
        assert forall|n:usize| !selected.contains(n) by {assert(selected.contains(n) ==> r::registered(a,n));}
    }
}
}
