//! Step counts derived from actual lifecycle transitions and iterator fuel.
//!
//! Fuel is a local remaining-stage bound: an Iter transition strictly consumes
//! it. The control model alone erases iterator work and admits infinitely many
//! Iter stutters, so that local obligation cannot be omitted. This module counts
//! real labelled transitions; it does not assume the S/V recurrence as input.
#[cfg(verus_keep_ghost)]
use crate::global;
#[cfg(verus_keep_ghost)]
use crate::refinement as control;
#[cfg(verus_keep_ghost)]
use crate::{preservation as typed, semantics as full};
#[cfg(verus_keep_ghost)]
use crate::{Binding, Phase};
use vstd::prelude::*;

verus! {

pub open spec fn available(s: control::State, actor: usize) -> bool {
    exists|view: ISet<Binding>| control::target(s, actor, view)
}

pub open spec fn configuration(s: control::State, fuel: Seq<nat>, bound: nat) -> bool {
    control::well_formed(s) && control::name_bound(s, fuel.len())
        && forall|n: usize| control::registered(s, n) && s.fibers[n].phase == Phase::Loading
            ==> #[trigger] fuel[n as int] <= bound
}

pub open spec fn permitted(rule: control::Rule) -> bool {
    global::lifecycle_rule(rule) || rule == control::Rule::Retire
}

pub open spec fn transition(a: control::State, z: control::State,
    before: Seq<nat>, after: Seq<nat>, label: (usize, control::Rule), bound: nat) -> bool {
    &&& control::step(a, z, label.0, label.1) && permitted(label.1)
    &&& configuration(a, before, bound) && configuration(z, after, bound)
    &&& before.len() == after.len()
    &&& forall|n: int| 0 <= n < before.len() && n != label.0 ==> before[n] == after[n]
    &&& label.1 == control::Rule::Iter ==> after[label.0 as int] < before[label.0 as int]
    &&& label.1 == control::Rule::Retire ==> before == after
}

pub open spec fn potential(s: control::State, fuel: Seq<nat>, n: usize, bound: nat) -> nat {
    if !control::registered(s, n) { 0 }
    else if available(s, n) {
        match s.fibers[n].phase {
            Phase::Inactive => bound + 2,
            Phase::Loading => fuel[n as int] + 1,
            Phase::Active => 0,
            Phase::Unloading => bound + 3,
        }
    } else {
        match s.fibers[n].phase {
            Phase::Inactive => 0,
            Phase::Loading => fuel[n as int] + 2,
            Phase::Active => 2,
            Phase::Unloading => 1,
        }
    }
}

pub open spec fn cost(label: (usize, control::Rule), n: usize) -> nat {
    if label.0 == n && global::lifecycle_rule(label.1) { 1 } else { 0 }
}

pub open spec fn changed(a: control::State, z: control::State, n: usize) -> nat {
    if available(a, n) != available(z, n) { 1 } else { 0 }
}

pub proof fn potential_bounded(s: control::State, fuel: Seq<nat>, n: usize, bound: nat)
    requires configuration(s, fuel, bound),
    ensures potential(s, fuel, n, bound) <= bound + 3,
{ }

/// Available installed fibers are coherent by the actual single-source
/// invariant, so an unchanged available target excludes Leave and Divert.
proof fn available_is_coherent(s: control::State, n: usize)
    requires control::well_formed(s), control::registered(s, n),
        s.fibers[n].phase != Phase::Inactive, available(s, n),
    ensures control::coherent(s, n),
{
    let view = choose|view: ISet<Binding>| control::target(s, n, view);
    control::available_installed_coherent(s, n, view);
}

/// One actual lifecycle step consumes one credit. A target availability change
/// may replenish at most K+3 credits; foreign stable-target steps consume none.
#[verifier::rlimit(20)]
pub proof fn transition_accounting(a: control::State, z: control::State,
    before: Seq<nat>, after: Seq<nat>, label: (usize, control::Rule), n: usize, bound: nat)
    requires transition(a, z, before, after, label, bound),
    ensures cost(label, n) + potential(z, after, n, bound)
        <= potential(a, before, n, bound) + (bound + 3) * changed(a, z, n),
{
    potential_bounded(a, before, n, bound);
    potential_bounded(z, after, n, bound);
    if n != label.0 {
        assert(control::registered(a, n) == control::registered(z, n));
        if control::registered(a, n) { assert(a.fibers[n] == z.fibers[n]); }
    } else if global::lifecycle_rule(label.1) {
        assert(control::registered(a, n));
        if label.1 == control::Rule::Begin {
            assert(control::target(a, n, z.fibers[n].committed));
            assert(available(a, n));
        }
        if label.1 == control::Rule::Iter || label.1 == control::Rule::Finish {
            assert(control::target(a, n, a.fibers[n].committed));
            assert(available(a, n));
        }
        if label.1 == control::Rule::Leave || label.1 == control::Rule::Divert {
            if available(a, n) { available_is_coherent(a, n); }
            assert(!available(a, n));
        }
        assert(potential(a, before, n, bound) >= 1);
    }
}

pub open spec fn execution(states: Seq<control::State>, fuels: Seq<Seq<nat>>,
    labels: Seq<(usize, control::Rule)>, bound: nat) -> bool {
    &&& states.len() == labels.len() + 1 && fuels.len() == states.len()
    &&& forall|i: int| 0 <= i < states.len() ==> configuration(states[i], fuels[i], bound)
    &&& forall|i: int| 0 <= i < labels.len() ==>
        transition(states[i], states[i + 1], fuels[i], fuels[i + 1], labels[i], bound)
}

pub open spec fn steps(labels: Seq<(usize, control::Rule)>, n: usize) -> nat
    decreases labels.len(),
{
    if labels.len() == 0 { 0 } else { steps(labels.drop_last(), n) + cost(labels.last(), n) }
}

pub open spec fn turns(states: Seq<control::State>, n: usize) -> nat
    decreases states.len(),
{
    if states.len() <= 1 { 0 }
    else { turns(states.drop_last(), n) + changed(states[states.len() - 2], states.last(), n) }
}

/// Telescoping the actual transition costs yields the paper's per-fiber
/// S(n) <= (K+3)(V(n)+1) premise, rather than taking that premise for granted.
pub proof fn execution_accounting(states: Seq<control::State>, fuels: Seq<Seq<nat>>,
    labels: Seq<(usize, control::Rule)>, n: usize, bound: nat)
    requires execution(states, fuels, labels, bound),
    ensures steps(labels, n) + potential(states.last(), fuels.last(), n, bound)
        <= potential(states.first(), fuels.first(), n, bound) + (bound + 3) * turns(states, n),
        steps(labels, n) <= (bound + 3) * (turns(states, n) + 1),
    decreases labels.len(),
{
    potential_bounded(states.first(), fuels.first(), n, bound);
    if labels.len() > 0 {
        let index = labels.len() - 1;
        assert(execution(states.drop_last(), fuels.drop_last(), labels.drop_last(), bound)) by {
            assert forall|i: int| 0 <= i < labels.drop_last().len() implies
                transition(states.drop_last()[i], states.drop_last()[i + 1],
                    fuels.drop_last()[i], fuels.drop_last()[i + 1], labels.drop_last()[i], bound) by { }
        }
        execution_accounting(states.drop_last(), fuels.drop_last(), labels.drop_last(), n, bound);
        transition_accounting(states[index], states.last(), fuels[index], fuels.last(), labels.last(), n, bound);
        assert(turns(states, n) == turns(states.drop_last(), n) + changed(states[index], states.last(), n));
        vstd::arithmetic::mul::lemma_mul_is_distributive_add((bound + 3) as int,
            turns(states.drop_last(), n) as int, changed(states[index], states.last(), n) as int);
    }
    assert((bound + 3) * (turns(states, n) + 1) == (bound + 3) * turns(states, n) + bound + 3) by (nonlinear_arith);
}

pub open spec fn declarations_same(a: control::State, z: control::State) -> bool {
    a.fibers.dom() == z.fibers.dom() && forall|n: usize| control::registered(a, n)
        ==> control::interface_same(a.fibers[n], z.fibers[n])
}

pub proof fn transition_declarations(a: control::State, z: control::State,
    before: Seq<nat>, after: Seq<nat>, label: (usize, control::Rule), bound: nat)
    requires transition(a, z, before, after, label, bound),
    ensures declarations_same(a, z),
{
    if global::lifecycle_rule(label.1) {
        global::lifecycle_input_frame(a, z, label.0, label.1);
    } else {
        assert(a.fibers.dom() =~= z.fibers.dom()) by {
            assert forall|n: usize| a.fibers.dom().contains(n) == z.fibers.dom().contains(n) by {
                assert(control::registered(a, n) == control::registered(z, n));
            }
        }
    }
}

pub proof fn declarations_predecessors(a: control::State, z: control::State, provider: usize, consumer: usize)
    requires declarations_same(a, z),
    ensures global::predecessor(a, provider, consumer) == global::predecessor(z, provider, consumer),
{
    if control::registered(a, provider) && control::registered(a, consumer) {
        assert(control::interface_same(a.fibers[provider], z.fibers[provider]));
        assert(control::interface_same(a.fibers[consumer], z.fibers[consumer]));
    }
}

pub proof fn execution_declarations(states: Seq<control::State>, fuels: Seq<Seq<nat>>,
    labels: Seq<(usize, control::Rule)>, bound: nat)
    requires execution(states, fuels, labels, bound),
    ensures declarations_same(states.first(), states.last()),
    decreases labels.len(),
{
    if labels.len() > 0 {
        execution_declarations(states.drop_last(), fuels.drop_last(), labels.drop_last(), bound);
        transition_declarations(states[labels.len() - 1], states.last(), fuels[labels.len() - 1],
            fuels.last(), labels.last(), bound);
        assert forall|n: usize| control::registered(states.first(), n) implies
            control::interface_same(states.first().fibers[n], states.last().fibers[n]) by {
            assert(control::registered(states[labels.len() - 1], n));
        }
    }
}

pub open spec fn retirement(s: control::State, n: usize) -> nat {
    if control::registered(s, n) && s.fibers[n].retired { 1 } else { 0 }
}

pub open spec fn predecessor_cost(s: control::State, label: (usize, control::Rule), n: usize) -> nat {
    if global::lifecycle_rule(label.1) && global::predecessor(s, label.0, n) { 1 } else { 0 }
}

/// Attribute every availability change to a real provider lifecycle step or
/// this fiber's unique false-to-true retirement change. Repeated Retire calls
/// cannot supply additional credits.
pub proof fn change_attribution(a: control::State, z: control::State,
    before: Seq<nat>, after: Seq<nat>, label: (usize, control::Rule), n: usize, bound: nat)
    requires transition(a, z, before, after, label, bound), control::registered(a, n),
    ensures changed(a, z, n) + retirement(a, n) <= predecessor_cost(a, label, n) + retirement(z, n),
{
    transition_declarations(a, z, before, after, label, bound);
    if global::lifecycle_rule(label.1) {
        global::lifecycle_input_frame(a, z, label.0, label.1);
        if !global::predecessor(a, label.0, n) {
            global::lifecycle_target_frame(a, z, label.0, n, label.1);
            assert(available(a, n) == available(z, n));
        }
    } else if label.0 == n && !a.fibers[n].retired {
    } else {
        assert(a.fibers[n].retired == z.fibers[n].retired);
        assert forall|port: crate::Port, provider: usize| control::publishes(a, port, provider)
            == control::publishes(z, port, provider) by {
            assert(control::registered(a, provider) == control::registered(z, provider));
            if provider != label.0 && control::registered(a, provider) {
                assert(a.fibers[provider] == z.fibers[provider]);
            }
        }
        assert forall|view: ISet<Binding>| control::target(a, n, view) == control::target(z, n, view) by { }
        assert(available(a, n) == available(z, n));
    }
}

pub open spec fn predecessor_steps(labels: Seq<(usize, control::Rule)>, initial: control::State, n: usize) -> nat
    decreases labels.len(),
{
    if labels.len() == 0 { 0 }
    else { predecessor_steps(labels.drop_last(), initial, n) + predecessor_cost(initial, labels.last(), n) }
}

/// Derive V(n) <= 1 + provider steps from the actual execution, including
/// arbitrary repeated orchestration retirements and their monotone flag.
pub proof fn execution_changes(states: Seq<control::State>, fuels: Seq<Seq<nat>>,
    labels: Seq<(usize, control::Rule)>, n: usize, bound: nat)
    requires execution(states, fuels, labels, bound), control::registered(states.first(), n),
    ensures turns(states, n) + retirement(states.first(), n)
        <= predecessor_steps(labels, states.first(), n) + retirement(states.last(), n),
        turns(states, n) <= 1 + predecessor_steps(labels, states.first(), n),
    decreases labels.len(),
{
    if labels.len() > 0 {
        let index = labels.len() - 1;
        execution_changes(states.drop_last(), fuels.drop_last(), labels.drop_last(), n, bound);
        execution_declarations(states.drop_last(), fuels.drop_last(), labels.drop_last(), bound);
        change_attribution(states[index], states.last(), fuels[index], fuels.last(), labels.last(), n, bound);
        declarations_predecessors(states.first(), states[index], labels.last().0, n);
    }
}

/// A supplied finite topological enumeration of the actual declaration graph.
/// Allocated identity order is not used as dependency order.
pub open spec fn topological_names(s: control::State, names: Seq<usize>) -> bool {
    &&& forall|i: int| 0 <= i < names.len() ==> control::registered(s, #[trigger] names[i])
    &&& forall|n: usize| control::registered(s, n) ==> exists|i: int| 0 <= i < names.len() && names[i] == n
    &&& forall|i: int, j: int| 0 <= i < names.len() && 0 <= j < names.len()
        && global::predecessor(s, names[j], names[i]) ==> j < i
}

pub open spec fn counts(labels: Seq<(usize, control::Rule)>, names: Seq<usize>) -> Seq<nat> {
    names.map(|i: int, n: usize| steps(labels, n))
}

pub open spec fn cost_sum(label: (usize, control::Rule), names: Seq<usize>, length: nat) -> nat
    recommends length <= names.len(),
    decreases length,
{
    if length == 0 { 0 }
    else { cost_sum(label, names, (length - 1) as nat) + cost(label, names[length - 1]) }
}

proof fn sum_last_step(labels: Seq<(usize, control::Rule)>, names: Seq<usize>, length: nat)
    requires length <= names.len(), labels.len() > 0,
    ensures crate::progress::sum_prefix(counts(labels, names), length)
        == crate::progress::sum_prefix(counts(labels.drop_last(), names), length)
            + cost_sum(labels.last(), names, length),
    decreases length,
{
    if length > 0 { sum_last_step(labels, names, (length - 1) as nat); }
}

proof fn cost_sum_includes(label: (usize, control::Rule), names: Seq<usize>, length: nat, index: int)
    requires 0 <= index < length <= names.len(), global::lifecycle_rule(label.1), names[index] == label.0,
    ensures cost_sum(label, names, length) >= 1,
    decreases length,
{
    if index < length - 1 { cost_sum_includes(label, names, (length - 1) as nat, index); }
}

pub proof fn earlier_counts_bound(labels: Seq<(usize, control::Rule)>, s: control::State,
    names: Seq<usize>, index: int)
    requires topological_names(s, names), 0 <= index < names.len(),
    ensures predecessor_steps(labels, s, names[index])
        <= crate::progress::sum_prefix(counts(labels, names), index as nat),
    decreases labels.len(),
{
    if labels.len() > 0 {
        earlier_counts_bound(labels.drop_last(), s, names, index);
        sum_last_step(labels, names, index as nat);
        if predecessor_cost(s, labels.last(), names[index]) == 1 {
            let provider = labels.last().0;
            let j = choose|j: int| 0 <= j < names.len() && names[j] == provider;
            assert(j < index);
            cost_sum_includes(labels.last(), names, index as nat, j);
        }
    }
}

pub open spec fn lifecycle_steps(labels: Seq<(usize, control::Rule)>) -> nat
    decreases labels.len(),
{
    if labels.len() == 0 { 0 }
    else { lifecycle_steps(labels.drop_last()) + if global::lifecycle_rule(labels.last().1) { 1nat } else { 0nat } }
}

proof fn named_steps_bound(labels: Seq<(usize, control::Rule)>, names: Seq<usize>)
    requires forall|i: int| 0 <= i < labels.len() ==> names.contains((#[trigger] labels[i]).0),
    ensures lifecycle_steps(labels) <= crate::progress::sum_prefix(counts(labels, names), names.len()),
    decreases labels.len(),
{
    if labels.len() > 0 {
        named_steps_bound(labels.drop_last(), names);
        sum_last_step(labels, names, names.len());
        if global::lifecycle_rule(labels.last().1) {
            let index = choose|index: int| 0 <= index < names.len() && names[index] == labels.last().0;
            cost_sum_includes(labels.last(), names, names.len(), index);
        }
    }
}

proof fn execution_actors_registered(states: Seq<control::State>, fuels: Seq<Seq<nat>>,
    labels: Seq<(usize, control::Rule)>, bound: nat)
    requires execution(states, fuels, labels, bound),
    ensures forall|i: int| 0 <= i < labels.len() ==> control::registered(states.first(), (#[trigger] labels[i]).0),
    decreases labels.len(),
{
    if labels.len() > 0 {
        execution_actors_registered(states.drop_last(), fuels.drop_last(), labels.drop_last(), bound);
        execution_declarations(states.drop_last(), fuels.drop_last(), labels.drop_last(), bound);
        assert(control::registered(states[labels.len() - 1], labels.last().0));
        assert(control::registered(states.first(), labels.last().0));
        assert forall|i: int| 0 <= i < labels.len() implies
            control::registered(states.first(), (#[trigger] labels[i]).0) by {
            if i < labels.len() - 1 {
                assert(control::registered(states.drop_last().first(), labels.drop_last()[i].0));
            }
        }
    }
}

/// The finite lifecycle bound for a fixed declaration registry is now a
/// consequence of actual rules, local iterator fuel, and a topological order.
/// Counts and target changes are computed from the supplied execution; neither
/// arithmetic recurrence is assumed. Retirements may interleave but receive no
/// lifecycle-step credit. Insert/Remove and registry-changing effect stages are
/// outside this fixed-registry theorem.
pub proof fn finite_lifecycle_bound(states: Seq<control::State>, fuels: Seq<Seq<nat>>,
    labels: Seq<(usize, control::Rule)>, names: Seq<usize>, bound: nat)
    requires execution(states, fuels, labels, bound), topological_names(states.first(), names),
    ensures lifecycle_steps(labels) <= crate::progress::total_budget(names.len(), bound),
{
    let step_counts = counts(labels, names);
    let change_counts = names.map(|i: int, n: usize| turns(states, n));
    assert forall|i: int| 0 <= i < step_counts.len() implies
        step_counts[i] <= (bound + 3) * (change_counts[i] + 1)
        && change_counts[i] <= 1 + crate::progress::sum_prefix(step_counts, i as nat) by {
        execution_accounting(states, fuels, labels, names[i], bound);
        execution_changes(states, fuels, labels, names[i], bound);
        earlier_counts_bound(labels, states.first(), names, i);
    }
    crate::progress::finite_step_bound(step_counts, change_counts, bound, names.len());
    execution_actors_registered(states, fuels, labels, bound);
    assert forall|i: int| 0 <= i < labels.len() implies names.contains((#[trigger] labels[i]).0) by {
        assert(control::registered(states.first(), labels[i].0));
        let index = choose|index: int| 0 <= index < names.len() && names[index] == labels[i].0;
    }
    named_steps_bound(labels, names);
}

pub proof fn lifecycle_length(labels: Seq<(usize, control::Rule)>)
    requires forall|i: int| 0 <= i < labels.len() ==> global::lifecycle_rule((#[trigger] labels[i]).1),
    ensures lifecycle_steps(labels) == labels.len(),
    decreases labels.len(),
{
    if labels.len() > 0 { lifecycle_length(labels.drop_last()); }
}

/// Once orchestration stops, every labelled strict lifecycle execution has a
/// uniform finite length bound. Combined with control/full no-deadlock, a
/// maximal well-formed execution satisfying the iterator bound is quiescent.
pub proof fn finite_execution_bound(states: Seq<control::State>, fuels: Seq<Seq<nat>>,
    labels: Seq<(usize, control::Rule)>, names: Seq<usize>, bound: nat)
    requires execution(states, fuels, labels, bound), topological_names(states.first(), names),
        forall|i: int| 0 <= i < labels.len() ==> global::lifecycle_rule((#[trigger] labels[i]).1),
    ensures labels.len() <= crate::progress::total_budget(names.len(), bound),
{
    finite_lifecycle_bound(states, fuels, labels, names, bound);
    lifecycle_length(labels);
}

pub open spec fn ordinary_restore<V>(model: full::Model<V>, tokens: Seq<nat>, state: full::State<V>, actor: usize) -> bool
    decreases tokens.len(),
{
    tokens.len() == 0 || {
        let next = (model.undo)(tokens.last(), state);
        typed::table_map(state, next, actor) && ordinary_restore(model, tokens.drop_last(), next, actor)
    }
}

/// Primitive hypotheses for the fixed-registry, total-provision fragment.
/// Forward and inverse maps carry local table footprints, terminal stages
/// actually publish every declared provision, and real continuations decrease.
/// No successor well-formedness, completion, or normal-form equality is assumed.
pub open spec fn ordinary_model<V>(model: full::Model<V>, rank: spec_fn(usize, nat) -> nat) -> bool {
    &&& forall|actor: usize, iterator: nat, state: full::State<V>|
        #[trigger] (model.iterate)(actor, iterator, state).state.control == state.control
    &&& forall|token: nat, state: full::State<V>|
        #[trigger] (model.undo)(token, state).control == state.control
    &&& forall|state: full::State<V>, actor: usize|
        typed::well_formed(state) && full::registered(state, actor)
        && state.control.fibers[actor].phase == Phase::Loading ==> {
            let result = #[trigger] (model.iterate)(actor, state.iterators[actor].unwrap(), state);
            &&& typed::table_map(state, result.state, actor)
            &&& result.next.is_some() ==> rank(actor, result.next.unwrap()) < rank(actor, state.iterators[actor].unwrap())
            &&& result.next.is_none() ==> result.state.tables[actor].dom() == state.control.fibers[actor].provisions
        }
    &&& forall|state: full::State<V>, actor: usize|
        typed::well_formed(state) && full::registered(state, actor)
        && state.control.fibers[actor].phase == Phase::Unloading && !control::relied(state.control, actor)
            ==> #[trigger] ordinary_restore(model, state.accumulators[actor], state, actor)
}

pub open spec fn full_configuration<V>(state: full::State<V>, rank: spec_fn(usize, nat) -> nat,
    names_bound: nat, stages: nat) -> bool {
    &&& typed::well_formed(state) && full::total_active(state)
    &&& names_bound <= usize::MAX as nat + 1 && control::name_bound(state.control, names_bound)
    &&& forall|n: usize| full::registered(state, n) ==> #[trigger] rank(n, state.effects[n]) <= stages
    &&& forall|n: usize| full::registered(state, n) && state.control.fibers[n].phase == Phase::Loading
        ==> #[trigger] rank(n, state.iterators[n].unwrap()) <= stages
}

pub open spec fn fuels<V>(state: full::State<V>, rank: spec_fn(usize, nat) -> nat, names_bound: nat) -> Seq<nat> {
    Seq::new(names_bound, |i: int| if full::registered(state, i as usize) && state.iterators[i as usize].is_some() {
        rank(i as usize, state.iterators[i as usize].unwrap())
    } else { 0 })
}

pub proof fn ordinary_restore_frame<V>(model: full::Model<V>, tokens: Seq<nat>, state: full::State<V>, actor: usize)
    requires ordinary_restore(model, tokens, state, actor),
    ensures typed::admissible_restore(model, tokens, state, actor),
        full::restore(model, tokens, state).control == state.control,
        full::restore(model, tokens, state).effects == state.effects,
        full::restore(model, tokens, state).iterators == state.iterators,
        forall|n: usize| n != actor && full::registered(state, n) ==>
            full::restore(model, tokens, state).tables[n].dom() == state.tables[n].dom(),
    decreases tokens.len(),
{
    if tokens.len() > 0 {
        let next = (model.undo)(tokens.last(), state);
        ordinary_restore_frame(model, tokens.drop_last(), next, actor);
        assert forall|n: usize| n != actor && full::registered(state, n) implies
            full::restore(model, tokens, state).tables[n].dom() == state.tables[n].dom() by {
            assert(full::registered(next, n));
            assert(next.tables[n].dom() == state.tables[n].dom());
        }
    }
}

/// Simulate an actual landed full-rule transition with computed iterator fuel.
/// In particular an Iter consumes the real continuation rank and a Finish uses
/// the model's actual `None`, never an invented early completion.
#[verifier::rlimit(30)]
pub proof fn full_step_projection<V>(model: full::Model<V>, a: full::State<V>, z: full::State<V>,
    label: (usize, control::Rule), rank: spec_fn(usize, nat) -> nat, names_bound: nat, stages: nat)
    requires ordinary_model(model, rank), full_configuration(a, rank, names_bound, stages),
        global::lifecycle_rule(label.1), full::landing_step(model, a, z, label.0, label.1),
    ensures full_configuration(z, rank, names_bound, stages),
        transition(a.control, z.control, fuels(a, rank, names_bound), fuels(z, rank, names_bound), label, stages),
{
    let actor = label.0;
    let rule = label.1;
    assert(full::registered(a, actor));
    if rule == control::Rule::Iter || rule == control::Rule::Finish || rule == control::Rule::Divert {
        let result = (model.iterate)(actor, a.iterators[actor].unwrap(), a);
        assert(typed::table_map(a, result.state, actor));
    }
    if rule == control::Rule::Unload {
        assert(ordinary_restore(model, a.accumulators[actor], a, actor));
        ordinary_restore_frame(model, a.accumulators[actor], a, actor);
    }
    assert(typed::admissible_step(model, a, z, actor, rule));
    typed::full_preservation(model, a, z, actor, rule);
    full::ordinary_step_erases(model, a, z, actor, rule);
    global::lifecycle_input_frame(a.control, z.control, actor, rule);
    assert(a.effects == z.effects);
    assert forall|n: usize| full::registered(z, n) implies rank(n, z.effects[n]) <= stages by {
        assert(full::registered(a, n));
    }
    assert forall|n: usize| full::registered(z, n) && z.control.fibers[n].phase == Phase::Loading implies
        rank(n, z.iterators[n].unwrap()) <= stages by {
        assert(full::registered(a, n));
        if n != actor {
            assert(a.control.fibers[n] == z.control.fibers[n]);
            assert(a.iterators[n] == z.iterators[n]);
        }
    }
    assert(full::total_active(z)) by {
        assert forall|n: usize| full::registered(z, n) && z.control.fibers[n].phase == Phase::Active implies
            z.tables[n].dom() == z.control.fibers[n].provisions by {
            assert(full::registered(a, n));
            if n != actor {
                assert(a.control.fibers[n] == z.control.fibers[n]);
                assert(a.tables[n].dom() == z.tables[n].dom());
            }
        }
    }
    assert forall|i: int| 0 <= i < names_bound && i != actor implies
        fuels(a, rank, names_bound)[i] == fuels(z, rank, names_bound)[i] by {
        let n = i as usize;
        assert(n != actor);
        assert(full::registered(a, n) == full::registered(z, n));
        if full::registered(a, n) { assert(a.iterators[n] == z.iterators[n]); }
    }
}

pub open spec fn full_execution<V>(model: full::Model<V>, states: Seq<full::State<V>>,
    labels: Seq<(usize, control::Rule)>, rank: spec_fn(usize, nat) -> nat, names_bound: nat, stages: nat) -> bool {
    &&& states.len() == labels.len() + 1
    &&& forall|i: int| 0 <= i < states.len() ==> full_configuration(states[i], rank, names_bound, stages)
    &&& forall|i: int| 0 <= i < labels.len() ==> global::lifecycle_rule(labels[i].1)
        && full::landing_step(model, states[i], states[i + 1], labels[i].0, labels[i].1)
}

pub open spec fn landing_execution<V>(model: full::Model<V>, states: Seq<full::State<V>>,
    labels: Seq<(usize, control::Rule)>) -> bool {
    states.len() == labels.len() + 1 && forall|i: int| 0 <= i < labels.len() ==>
        global::lifecycle_rule(labels[i].1)
        && full::landing_step(model, states[i], states[i + 1], labels[i].0, labels[i].1)
}

/// Intermediate configurations follow from the primitive model laws and the
/// actual rule sequence. Only the initial configuration is an input invariant.
pub proof fn landing_execution_typed<V>(model: full::Model<V>, states: Seq<full::State<V>>,
    labels: Seq<(usize, control::Rule)>, rank: spec_fn(usize, nat) -> nat, names_bound: nat, stages: nat)
    requires ordinary_model(model, rank), landing_execution(model, states, labels),
        full_configuration(states.first(), rank, names_bound, stages),
    ensures full_execution(model, states, labels, rank, names_bound, stages),
    decreases labels.len(),
{
    if labels.len() == 0 { assert(states.first() == states[0]); }
    else {
        landing_execution_typed(model, states.drop_last(), labels.drop_last(), rank, names_bound, stages);
        assert(full_configuration(states.drop_last()[labels.len() - 1], rank, names_bound, stages));
        assert(states.drop_last()[labels.len() - 1] == states[labels.len() - 1]);
        full_step_projection(model, states[labels.len() - 1], states.last(), labels.last(), rank, names_bound, stages);
        assert forall|i: int| 0 <= i < states.len() implies full_configuration(states[i], rank, names_bound, stages) by {
            if i < states.len() - 1 { assert(states[i] == states.drop_last()[i]); }
        }
    }
}

pub proof fn full_execution_bound<V>(model: full::Model<V>, states: Seq<full::State<V>>,
    labels: Seq<(usize, control::Rule)>, rank: spec_fn(usize, nat) -> nat,
    names_bound: nat, stages: nat, names: Seq<usize>)
    requires ordinary_model(model, rank), full_execution(model, states, labels, rank, names_bound, stages),
        topological_names(states.first().control, names),
    ensures labels.len() <= crate::progress::total_budget(names.len(), stages),
{
    let controls = states.map(|i: int, s: full::State<V>| s.control);
    let counters = states.map(|i: int, s: full::State<V>| fuels(s, rank, names_bound));
    assert forall|i: int| 0 <= i < labels.len() implies
        transition(controls[i], controls[i + 1], counters[i], counters[i + 1], labels[i], stages) by {
        full_step_projection(model, states[i], states[i + 1], labels[i], rank, names_bound, stages);
    }
    assert forall|i: int| 0 <= i < states.len() implies configuration(controls[i], counters[i], stages) by { }
    finite_execution_bound(controls, counters, labels, names, stages);
}

pub proof fn arbitrary_landing_bound<V>(model: full::Model<V>, states: Seq<full::State<V>>,
    labels: Seq<(usize, control::Rule)>, rank: spec_fn(usize, nat) -> nat,
    names_bound: nat, stages: nat, names: Seq<usize>)
    requires ordinary_model(model, rank), landing_execution(model, states, labels),
        full_configuration(states.first(), rank, names_bound, stages),
        topological_names(states.first().control, names),
    ensures labels.len() <= crate::progress::total_budget(names.len(), stages),
{
    landing_execution_typed(model, states, labels, rank, names_bound, stages);
    full_execution_bound(model, states, labels, rank, names_bound, stages, names);
}

proof fn ranking_frame(a: control::State, z: control::State, ranks: Seq<nat>)
    requires declarations_same(a, z), global::precedence_ranking(a, ranks),
    ensures global::precedence_ranking(z, ranks),
{
    assert forall|n: usize| control::registered(z, n) implies n < ranks.len() by {
        assert(control::registered(a, n));
    }
    assert forall|m: usize, n: usize| global::predecessor(z, m, n) implies ranks[m as int] < ranks[n as int] by {
        declarations_predecessors(a, z, m, n);
    }
}

pub struct NormalExecution<V> {
    pub states: Seq<crate::semantics::State<V>>,
    pub labels: Seq<(usize, crate::refinement::Rule)>,
}

/// Extend an actual prefix to a quiet full state. The recursion decreases the
/// proved global step budget; it executes actual model yields and always uses
/// landed diversion. Preservation and no-deadlock supply each new successor.
pub proof fn complete_prefix<V>(model: full::Model<V>, states: Seq<full::State<V>>,
    labels: Seq<(usize, control::Rule)>, rank: spec_fn(usize, nat) -> nat,
    names_bound: nat, stages: nat, names: Seq<usize>, ranks: Seq<nat>) -> (result: NormalExecution<V>)
    requires ordinary_model(model, rank), full_execution(model, states, labels, rank, names_bound, stages),
        topological_names(states.first().control, names), global::precedence_ranking(states.last().control, ranks),
        labels.len() <= crate::progress::total_budget(names.len(), stages),
    ensures full_execution(model, result.states, result.labels, rank, names_bound, stages),
        result.states.first() == states.first(), full::quiet(result.states.last()),
        result.labels.len() <= crate::progress::total_budget(names.len(), stages),
    decreases crate::progress::total_budget(names.len(), stages) - labels.len(),
{
    let last = states.last();
    if full::quiet(last) {
        NormalExecution { states, labels }
    } else {
        full::full_no_deadlock(model, last, ranks);
        let (actor, next, rule) = choose|actor: usize, next: full::State<V>, rule: control::Rule|
            global::lifecycle_rule(rule) && full::landing_step(model, last, next, actor, rule);
        let label = (actor, rule);
        full_step_projection(model, last, next, label, rank, names_bound, stages);
        transition_declarations(last.control, next.control, fuels(last, rank, names_bound),
            fuels(next, rank, names_bound), label, stages);
        ranking_frame(last.control, next.control, ranks);
        let new_states = states.push(next);
        let new_labels = labels.push(label);
        assert(full_execution(model, new_states, new_labels, rank, names_bound, stages)) by {
            assert forall|i: int| 0 <= i < new_labels.len() implies global::lifecycle_rule(new_labels[i].1)
                && full::landing_step(model, new_states[i], new_states[i + 1], new_labels[i].0, new_labels[i].1) by {
                if i < labels.len() { assert(full::landing_step(model, states[i], states[i + 1], labels[i].0, labels[i].1)); }
            }
        }
        full_execution_bound(model, new_states, new_labels, rank, names_bound, stages, names);
        complete_prefix(model, new_states, new_labels, rank, names_bound, stages, names, ranks)
    }
}

/// Existence of a finite quiescent execution for the explicitly typed ordinary
/// full semantics. Iterator results and inverses are the supplied model's actual
/// functions; arbitrary Rust futures and dynamic child creation are not covered.
pub proof fn normal_form_exists<V>(model: full::Model<V>, initial: full::State<V>,
    rank: spec_fn(usize, nat) -> nat, names_bound: nat, stages: nat,
    names: Seq<usize>, ranks: Seq<nat>) -> (result: NormalExecution<V>)
    requires ordinary_model(model, rank), full_configuration(initial, rank, names_bound, stages),
        topological_names(initial.control, names), global::precedence_ranking(initial.control, ranks),
    ensures full_execution(model, result.states, result.labels, rank, names_bound, stages),
        result.states.first() == initial, full::quiet(result.states.last()),
        result.labels.len() <= crate::progress::total_budget(names.len(), stages),
        full::reaches(model, initial, result.states.last(), result.labels.len()),
{
    let result = complete_prefix(model, seq![initial], Seq::empty(), rank, names_bound, stages, names, ranks);
    assert(full::execution(model, result.states, result.labels)) by {
        assert forall|i: int| 0 <= i < result.labels.len() implies
            full::step(model, result.states[i], result.states[i + 1], result.labels[i].0, result.labels[i].1) by {
            assert(full::landing_step(model, result.states[i], result.states[i + 1], result.labels[i].0, result.labels[i].1));
        }
    }
    full::execution_reaches(model, result.states, result.labels);
    result
}

} // verus!
