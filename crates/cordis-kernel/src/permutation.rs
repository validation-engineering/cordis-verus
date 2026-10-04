//! Theorem 43: actual dynamically returned inverses recover in any permutation.
//!
//! A returned inverse need only undo its own actual application state. Pairwise
//! independence then lets the inverse permutation be normalized. Equal lanes
//! are derived from a permutation's range, coverage, and no-duplicates clauses.
#[cfg(verus_keep_ghost)]
use crate::history::IteratorStep;
use vstd::prelude::*;

verus! {

pub open spec fn apply<S>(effects: Seq<IteratorStep<S>>, state: S) -> S
    decreases effects.len(),
{
    if effects.len() == 0 { state }
    else { (effects.last())(apply(effects.drop_last(), state)).0 }
}

pub open spec fn returned<S>(effects: Seq<IteratorStep<S>>, state: S) -> Seq<spec_fn(S) -> S>
    decreases effects.len(),
{
    if effects.len() == 0 { Seq::empty() }
    else { returned(effects.drop_last(), state).push((effects.last())(apply(effects.drop_last(), state)).1) }
}

pub open spec fn witnessed<S>(effects: Seq<IteratorStep<S>>) -> bool {
    forall|i: int, state: S| 0 <= i < effects.len() ==>
        #[trigger] ((effects[i])(state).1)((effects[i])(state).0) == state
}

pub open spec fn independent<S>(effects: Seq<IteratorStep<S>>) -> bool {
    forall|i: int, j: int| 0 <= i < effects.len() && 0 <= j < effects.len() && i != j ==>
        #[trigger] crate::history::independent_stages(effects[i], effects[j])
}

pub proof fn returned_length<S>(effects: Seq<IteratorStep<S>>, state: S)
    ensures returned(effects, state).len() == effects.len(),
    decreases effects.len(),
{
    if effects.len() > 0 { returned_length(effects.drop_last(), state); }
}

/// The witness is instantiated at the state reached by the actual prefix.
pub proof fn dynamic_recovery<S>(effects: Seq<IteratorStep<S>>, state: S)
    requires witnessed(effects),
    ensures crate::calculus::unwind(returned(effects, state), apply(effects, state)) == state,
    decreases effects.len(),
{
    if effects.len() > 0 {
        let prefix = effects.drop_last();
        let entry = apply(prefix, state);
        let result = (effects.last())(entry);
        assert((result.1)(result.0) == entry);
        assert(returned(effects, state).drop_last() =~= returned(prefix, state));
        dynamic_recovery(prefix, state);
    }
}

pub proof fn returned_origin<S>(effects: Seq<IteratorStep<S>>, state: S, index: int)
    requires 0 <= index < effects.len(),
    ensures exists|entry: S| (#[trigger] (effects[index])(entry)).1 == returned(effects, state)[index],
    decreases effects.len(),
{
    returned_length(effects, state);
    if index == effects.len() - 1 {
        let entry = apply(effects.drop_last(), state);
        assert((effects[index])(entry).1 == returned(effects, state)[index]);
    } else {
        returned_origin(effects.drop_last(), state, index);
    }
}

pub open spec fn pairwise_commuting<S>(operations: Seq<spec_fn(S) -> S>) -> bool {
    forall|i: int, j: int| 0 <= i < operations.len() && 0 <= j < operations.len() && i != j ==>
        #[trigger] crate::history::commutes(operations[i], operations[j])
}

pub proof fn returned_commute<S>(effects: Seq<IteratorStep<S>>, state: S)
    requires independent(effects),
    ensures pairwise_commuting(returned(effects, state)),
{
    returned_length(effects, state);
    assert forall|i: int, j: int| 0 <= i < effects.len() && 0 <= j < effects.len() && i != j implies
        #[trigger] crate::history::commutes(returned(effects, state)[i], returned(effects, state)[j]) by {
        returned_origin(effects, state, i);
        returned_origin(effects, state, j);
        let a = choose|entry: S| (#[trigger] (effects[i])(entry)).1 == returned(effects, state)[i];
        let b = choose|entry: S| (#[trigger] (effects[j])(entry)).1 == returned(effects, state)[j];
        assert(crate::history::generators(effects[i]).contains(returned(effects, state)[i]));
        assert(crate::history::generators(effects[j]).contains(returned(effects, state)[j]));
        assert(crate::history::independent_stages(effects[i], effects[j]));
    }
}

pub open spec fn distinct(order: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < order.len() ==> order[i] != order[j]
}

pub open spec fn permutation(order: Seq<nat>, count: nat) -> bool {
    &&& order.len() == count && distinct(order)
    &&& forall|i: int| 0 <= i < order.len() ==> #[trigger] order[i] < count
    &&& forall|n: nat| n < count ==> order.contains(n)
}

pub open spec fn indexed_history<S>(operations: Seq<spec_fn(S) -> S>, order: Seq<nat>) -> crate::history::History<S> {
    order.map(|i: int, n: nat| (n, operations[n as int]))
}

pub open spec fn selected<S>(operations: Seq<spec_fn(S) -> S>, order: Seq<nat>) -> Seq<spec_fn(S) -> S> {
    order.map(|i: int, n: nat| operations[n as int])
}

/// Range and nonrepetition derive each lane's exact singleton (or emptiness).
pub proof fn singleton_lane<S>(operations: Seq<spec_fn(S) -> S>, order: Seq<nat>, owner: nat)
    requires distinct(order), forall|i: int| 0 <= i < order.len() ==> #[trigger] order[i] < operations.len(),
    ensures crate::history::lane(indexed_history(operations, order), owner)
        == if order.contains(owner) { seq![operations[owner as int]] } else { Seq::empty() },
    decreases order.len(),
{
    if order.len() > 0 {
        let prefix = order.drop_last();
        singleton_lane(operations, prefix, owner);
        assert(indexed_history(operations, order).drop_last() =~= indexed_history(operations, prefix));
        if order.last() == owner {
            assert(!prefix.contains(owner)) by {
                if prefix.contains(owner) {
                    let i = choose|i: int| 0 <= i < prefix.len() && prefix[i] == owner;
                    assert(order[i] != order[order.len() - 1]);
                }
            }
        } else {
            if order.contains(owner) {
                let i = choose|i: int| 0 <= i < order.len() && order[i] == owner;
                assert(i < prefix.len());
                assert(prefix[i] == owner);
            }
            if prefix.contains(owner) {
                let i = choose|i: int| 0 <= i < prefix.len() && prefix[i] == owner;
                assert(order[i] == owner);
            }
        }
    }
}

pub proof fn selected_operations<S>(operations: Seq<spec_fn(S) -> S>, order: Seq<nat>)
    ensures crate::history::operations(indexed_history(operations, order)) == selected(operations, order),
    decreases order.len(),
{
    if order.len() > 0 {
        selected_operations(operations, order.drop_last());
        assert(indexed_history(operations, order).drop_last() =~= indexed_history(operations, order.drop_last()));
        assert(selected(operations, order).drop_last() =~= selected(operations, order.drop_last()));
        assert(selected(operations, order) =~= selected(operations, order.drop_last()).push(operations[order.last() as int]));
    }
}

pub proof fn indexed_independent<S>(operations: Seq<spec_fn(S) -> S>, order: Seq<nat>)
    requires pairwise_commuting(operations), permutation(order, operations.len()),
    ensures crate::history::independent(indexed_history(operations, order)),
{
    let history = indexed_history(operations, order);
    assert forall|i: int, j: int, state: S| 0 <= i < history.len() && 0 <= j < history.len()
        && history[i].0 != history[j].0 implies
        #[trigger] (history[i].1)((history[j].1)(state)) == (history[j].1)((history[i].1)(state)) by {
        assert(crate::history::commutes(operations[order[i] as int], operations[order[j] as int]));
    }
}

pub proof fn permutation_execution<S>(operations: Seq<spec_fn(S) -> S>, left: Seq<nat>, right: Seq<nat>, state: S)
    requires pairwise_commuting(operations), permutation(left, operations.len()), permutation(right, operations.len()),
    ensures crate::calculus::run(selected(operations, left), state) == crate::calculus::run(selected(operations, right), state),
{
    let a = indexed_history(operations, left);
    let b = indexed_history(operations, right);
    indexed_independent(operations, left);
    indexed_independent(operations, right);
    assert forall|owner: nat| owner < operations.len() implies
        #[trigger] crate::history::lane(a, owner) == crate::history::lane(b, owner) by {
        singleton_lane(operations, left, owner);
        singleton_lane(operations, right, owner);
    }
    crate::history::interleaving_confluence(a, b, operations.len(), state);
    selected_operations(operations, left);
    selected_operations(operations, right);
}

pub open spec fn reverse_indices(count: nat) -> Seq<nat> {
    Seq::new(count, |i: int| (count - 1 - i) as nat)
}

pub proof fn reverse_permutation<S>(operations: Seq<spec_fn(S) -> S>)
    ensures permutation(reverse_indices(operations.len()), operations.len()),
        selected(operations, reverse_indices(operations.len())) == operations.reverse(),
{
    let order = reverse_indices(operations.len());
    assert forall|owner: nat| owner < operations.len() implies order.contains(owner) by {
        let i = operations.len() - 1 - owner;
        assert(0 <= i < order.len());
        assert(order[i] == owner);
    }
    assert(selected(operations, order) =~= operations.reverse());
}

/// Theorem 43 at exact equality. Every effect is applied once, the inverses are
/// those actually yielded along that dynamic execution, and any supplied
/// permutation of their indices restores the original context.
pub proof fn arbitrary_inverse_recovery<S>(effects: Seq<IteratorStep<S>>, state: S, order: Seq<nat>)
    requires witnessed(effects), independent(effects), permutation(order, effects.len()),
    ensures crate::calculus::run(selected(returned(effects, state), order), apply(effects, state)) == state,
{
    returned_length(effects, state);
    returned_commute(effects, state);
    dynamic_recovery(effects, state);
    let inverses = returned(effects, state);
    reverse_permutation(inverses);
    permutation_execution(inverses, order, reverse_indices(inverses.len()), apply(effects, state));
    crate::history::inverse_history(inverses, apply(effects, state));
}

} // verus!
