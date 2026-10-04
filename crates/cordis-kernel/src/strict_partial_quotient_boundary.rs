//! Boundary between legal-input refinement and the pure table function-field
//! base used by Equation (54). Its whole-state relation also keeps control.
//!
//! Two actual from-empty states have identical all-fiber tables, are both well
//! formed and register the actor, yet their committed provider views differ.
//! The same real root and actual accumulated inverse word fail on one input and
//! succeed on the other. Thus the strict interpreter is not self-related under
//! pure table tests. This concerns the encoded strict model, not a counterexample
//! to Lemma 60 for the paper's assumed total, witnessed Gamma components.
#[cfg(verus_keep_ghost)]
use crate::{
    iterators as it, mediated as m, mixed_grammar as g, observation as o, preservation as inv,
    projection as p, quotient as q, recovery_examples as values, semantics as s,
    strict_partial_quotient as controlled, strict_partial_quotient_example as example,
    strict_partial_quotient_per as per, Phase,
};
use vstd::prelude::*;

verus! {

pub open spec fn before()->s::State<int> {example::setup(false).last().state}
pub open spec fn after()->s::State<int> {example::left().last().state}

/// The original all-fiber key projection, with no control/registration clause.
pub open spec fn table_observation()->spec_fn(s::State<int>,s::State<int>)->bool {
    |a:s::State<int>,b:s::State<int>|o::context_equal(values::equality(),ISet::full(),p::project(a,ISet::full()),p::project(b,ISet::full()))
}
pub open spec fn actual_forward()->m::PartialMap<s::State<int>> {
    |a:s::State<int>|match g::run(example::library(),example::programs()(1)(0nat),a,1) {None=>None,Some(y)=>Some(y.state)}
}

#[verifier::spinoff_prover]
pub proof fn legal_equal_tables()
    ensures g::execution(example::library(),example::programs(),example::setup(false),example::setup_labels()),
        example::setup(false).first()==g::empty::<int,nat>(),
        g::execution(example::library(),example::programs(),example::left(),example::left_labels()),
        example::left().first()==g::empty::<int,nat>(),
        inv::well_formed(before()),inv::well_formed(after()),s::registered(before(),1),s::registered(after(),1),
        before().tables==after().tables,
        p::project(before(),ISet::full())==p::project(after(),ISet::full()),
        table_observation()(before(),after()),
        controlled::legal_input(values::equality(),1,before(),before()),controlled::legal_input(values::equality(),1,after(),after()),
        !controlled::legal_input(values::equality(),1,before(),after()),!controlled::legal_input(values::equality(),1,after(),before()),
{
    example::actual_success_and_failure();example::actual_setup(false);example::actual_left();example::theory();
    reveal(example::setup);reveal(example::left);let a=before();let b=after();
    assert(a.control.fibers.dom() =~= b.control.fibers.dom());
    assert(a.tables =~= b.tables) by {
        assert forall|actor:usize|a.tables.dom().contains(actor) implies a.tables[actor]==b.tables[actor] by {
            if actor==0 {assert(a.tables[actor] =~= b.tables[actor]);}else if actor==1{}else{assert(actor==2);}
        }
    }
    p::unique_owner(a);p::unique_owner(b);
    assert(p::bindings_equal(a,b)) by {
        assert forall|key:crate::Port,actor:usize|p::owns(a,key,actor)==p::owns(b,key,actor)
            && (p::owns(a,key,actor) ==> a.tables[actor][key]==b.tables[actor][key]) by {}
    }
    p::projection_equal(a,b,ISet::full());
    assert(o::context_equal(values::equality(),ISet::full(),p::project(a,ISet::full()),p::project(b,ISet::full())));
    assert(a.control.fibers[1usize].phase==Phase::Inactive);assert(b.control.fibers[1usize].phase==Phase::Loading);
}

/// Success and failure belong to actual programs/receipts on legal inputs;
/// no malformed receipt or missing registry entry is used to separate them.
pub proof fn strict_domains()
    ensures actual_forward()(before()).is_none(),actual_forward()(after()).is_some(),
        controlled::accumulator(example::left().last(),1)(before()).is_none(),
        controlled::accumulator(example::right().last(),1)(before()).is_none(),
        controlled::accumulator(example::left().last(),1)(after())==Some(after()),
        controlled::accumulator(example::right().last(),1)(after())==Some(after()),
{
    example::actual_success_and_failure();
}

/// A controlled self-related root/word need not pass Definition-34-style pure
/// table tests when interpreted strictly on these full State values.
pub proof fn pure_table_self_relation_fails()
    ensures !m::partial_related(table_observation(),actual_forward(),actual_forward()),
        !m::partial_related(table_observation(),controlled::accumulator(example::left().last(),1),controlled::accumulator(example::left().last(),1)),
        !m::partial_related(table_observation(),controlled::accumulator(example::right().last(),1),controlled::accumulator(example::right().last(),1)),
        !q::iterator_related(
            |a:Option<s::State<int>>,b:Option<s::State<int>>|it::optional_eq(table_observation(),a,b),
            it::encode_partial(controlled::family(example::library(),example::programs(),1)),0nat,0nat),
        controlled::iterator_related(values::equality(),example::library(),example::programs(),1,0nat,0nat),
        m::partial_related(controlled::input_relation(values::equality(),1),controlled::accumulator(example::left().last(),1),controlled::accumulator(example::left().last(),1)),
{
    legal_equal_tables();strict_domains();let eq=table_observation();let a=before();let b=after();
    assert(eq(a,b));let forward=actual_forward();
    if m::partial_related(eq,forward,forward) {assert(forward(a).is_some()==forward(b).is_some());}
    let left=controlled::accumulator(example::left().last(),1);let right=controlled::accumulator(example::right().last(),1);
    if m::partial_related(eq,left,left) {assert(left(a).is_some()==left(b).is_some());}
    if m::partial_related(eq,right,right) {assert(right(a).is_some()==right(b).is_some());}
    let lifted=|a:Option<s::State<int>>,b:Option<s::State<int>>|it::optional_eq(eq,a,b);
    let family=controlled::family(example::library(),example::programs(),1);let encoded=it::encode_partial(family);
    if q::iterator_related(lifted,encoded,0nat,0nat) {
        q::iterator_unfolding(lifted,encoded,0nat,0nat);assert(lifted(Some(a),Some(b)));
        assert(lifted(encoded(0nat,Some(a)).state,encoded(0nat,Some(b)).state));
    }
    example::theory();example::aliases(1,0nat,0nat);example::field_accumulators(1);
    per::legal_input_per(values::equality(),1);
    per::partial_map_per(controlled::input_relation(values::equality(),1),left,right,left);
}
}
