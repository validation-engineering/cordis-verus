//! Lemma 38: every algebraic and recovery law of Section 3.1 on an
//! arbitrary observational equivalence. Lifted contexts use the relation of
//! Definition 34 on accumulators; consequently its reflexive domain consists
//! exactly of the accumulators that respect the base relation.
#[cfg(verus_keep_ghost)]
use crate::{calculus as c, foundations as f, iterators as it, observation as o, quotient as q};
use vstd::prelude::*;

verus! {

pub open spec fn admissible<S>(eq: spec_fn(S, S) -> bool, a: f::Tracked<S>) -> bool {
    o::related_maps(eq, a.undo, a.undo)
}

/// The lifted relation is a partial equivalence, becoming an equivalence on
/// admissible contexts. This is the domain on which lifted identities live.
pub proof fn tracked_partial_equivalence<S>(eq: spec_fn(S, S) -> bool,
    a: f::Tracked<S>, b: f::Tracked<S>, d: f::Tracked<S>)
    requires c::equivalence(eq),
    ensures it::tracked_related(eq, a, a) == admissible(eq, a),
        it::tracked_related(eq, a, b) ==> it::tracked_related(eq, b, a),
        it::tracked_related(eq, a, b) && it::tracked_related(eq, b, d) ==> it::tracked_related(eq, a, d),
        it::tracked_related(eq, a, b) ==> admissible(eq, a) && admissible(eq, b),
{
    o::map_partial_equivalence(eq, a.undo, b.undo, d.undo);
}

pub proof fn exact_tracked_transport<S>(eq: spec_fn(S, S) -> bool,
    a: f::Tracked<S>, b: f::Tracked<S>, d: f::Tracked<S>)
    requires it::tracked_related(eq, a, b), f::tracked_equal(b, d),
    ensures it::tracked_related(eq, a, d),
{
    assert forall|x: S, y: S| eq(x, y) implies #[trigger] eq((a.undo)(x), (d.undo)(y)) by {
        assert((b.undo)(y) == (d.undo)(y));
    }
}

pub proof fn exact_lifted_transport<S>(eq: spec_fn(S, S) -> bool,
    a: f::Tracked<f::Tracked<S>>, b: f::Tracked<f::Tracked<S>>, d: f::Tracked<f::Tracked<S>>)
    requires it::lifted_related(eq, a, b), f::lifted_equal(b, d),
    ensures it::lifted_related(eq, a, d),
{
    exact_tracked_transport(eq, a.value, b.value, d.value);
    assert forall|x: f::Tracked<S>, y: f::Tracked<S>| it::tracked_related(eq, x, y) implies
        #[trigger] it::tracked_related(eq, (a.undo)(x), (d.undo)(y)) by {
        exact_tracked_transport(eq, (a.undo)(x), (b.undo)(y), (d.undo)(y));
    }
}

/// Composition, and therefore the twisted pair multiplication in Definition
/// 1, obeys all monoid identities in the relation of Definition 34.
pub proof fn map_monoid<S>(eq: spec_fn(S, S) -> bool,
    a: spec_fn(S) -> S, b: spec_fn(S) -> S, d: spec_fn(S) -> S)
    requires o::related_maps(eq, a, a), o::related_maps(eq, b, b), o::related_maps(eq, d, d),
    ensures o::related_maps(eq, f::compose(a, |s: S| s), a),
        o::related_maps(eq, f::compose(|s: S| s, a), a),
        o::related_maps(eq, f::compose(f::compose(a, b), d), f::compose(a, f::compose(b, d))),
{ }

pub open spec fn twisted<S>(left: (spec_fn(S) -> S, spec_fn(S) -> S),
    right: (spec_fn(S) -> S, spec_fn(S) -> S)) -> (spec_fn(S) -> S, spec_fn(S) -> S)
{
    (f::compose(left.0, right.0), f::compose(right.1, left.1))
}
pub open spec fn pair_related<S>(eq: spec_fn(S, S) -> bool,
    left: (spec_fn(S) -> S, spec_fn(S) -> S), right: (spec_fn(S) -> S, spec_fn(S) -> S)) -> bool
{
    o::related_maps(eq, left.0, right.0) && o::related_maps(eq, left.1, right.1)
}

/// Definition 1, including closure of the respecting domain, the two unit
/// identities and associativity of the opposite-order inverse multiplication.
pub proof fn twisted_monoid<S>(eq: spec_fn(S, S) -> bool,
    a: (spec_fn(S) -> S, spec_fn(S) -> S), b: (spec_fn(S) -> S, spec_fn(S) -> S),
    d: (spec_fn(S) -> S, spec_fn(S) -> S))
    requires pair_related(eq, a, a), pair_related(eq, b, b), pair_related(eq, d, d),
    ensures pair_related(eq, twisted(a, b), twisted(a, b)),
        pair_related(eq, twisted(a, (|s: S| s, |s: S| s)), a),
        pair_related(eq, twisted((|s: S| s, |s: S| s), a), a),
        pair_related(eq, twisted(twisted(a, b), d), twisted(a, twisted(b, d))),
{
    map_monoid(eq, a.0, b.0, d.0); map_monoid(eq, d.1, b.1, a.1);
    o::compose_related(eq, a.0, a.0, b.0, b.0);
    o::compose_related(eq, b.1, b.1, a.1, a.1);
}

/// Theorem 4 and both clauses of Theorem 5, including the accumulator.
pub proof fn tracking_monoid<S>(eq: spec_fn(S, S) -> bool,
    f1: spec_fn(S) -> S, g1: spec_fn(S) -> S,
    f2: spec_fn(S) -> S, g2: spec_fn(S) -> S, a: f::Tracked<S>)
    requires c::equivalence(eq), admissible(eq, a),
        o::related_maps(eq, f1, f1), o::related_maps(eq, g1, g1),
        o::related_maps(eq, f2, f2), o::related_maps(eq, g2, g2),
    ensures eq(f::track(f1, g1, a).value, f1(a.value)),
        it::tracked_related(eq, f::track(|s: S| s, |s: S| s, a), a),
        it::tracked_related(eq, f::track(f1, g1, f::track(f2, g2, a)),
            f::track(f::compose(f1, f2), f::compose(g2, g1), a)),
{
    f::track_monoid(f1, g1, f2, g2, a);
    it::track_related(eq, f2, f2, g2, g2, a, a);
    let first = f::track(f2, g2, a);
    it::track_related(eq, f1, f1, g1, g1, first, first);
    let left = f::track(f1, g1, first);
    exact_tracked_transport(eq, left, left, f::track(f::compose(f1, f2), f::compose(g2, g1), a));
}

/// Definition 6 is a respecting map on admissible contexts.
pub proof fn recovery_related<S>(eq: spec_fn(S, S) -> bool, a: f::Tracked<S>, b: f::Tracked<S>)
    requires it::tracked_related(eq, a, b),
    ensures it::tracked_related(eq, f::recover(a), f::recover(b)),
{ }

/// Theorem 7 at an actual yield; no uniform inverse is required.
pub proof fn tracking_recovery<S>(eq: spec_fn(S, S) -> bool,
    forward: spec_fn(S) -> S, inverse: spec_fn(S) -> S, a: f::Tracked<S>)
    requires c::equivalence(eq), admissible(eq, a), eq(inverse(forward(a.value)), a.value),
    ensures it::tracked_related(eq, f::recover(f::track(forward, inverse, a)), f::recover(a)),
{ }

pub open spec fn actual_tracking_trace<S>(eq: spec_fn(S, S) -> bool,
    states: Seq<f::Tracked<S>>, steps: Seq<(spec_fn(S) -> S, spec_fn(S) -> S)>) -> bool
{
    states.len() == steps.len() + 1 && forall|i: int| 0 <= i < steps.len() ==> {
        &&& f::tracked_equal(states[i + 1], f::track(steps[i].0, steps[i].1, states[i]))
        &&& eq((steps[i].1)((steps[i].0)(states[i].value)), states[i].value)
        &&& o::related_maps(eq, steps[i].1, steps[i].1)
    }
}

/// Equation (11) needs only the inverses witnessed at the states of this
/// actual trace. It does not assume global effect witnesses or respect by the
/// forwards, and derives respect of every accumulated inverse composition.
pub proof fn tracking_trace_prefix<S>(eq: spec_fn(S, S) -> bool,
    states: Seq<f::Tracked<S>>, steps: Seq<(spec_fn(S) -> S, spec_fn(S) -> S)>, count: nat)
    requires c::equivalence(eq), actual_tracking_trace(eq, states, steps), count <= steps.len(),
        admissible(eq, states[0]),
    ensures admissible(eq, states[count as int]),
        it::tracked_related(eq, f::recover(states[count as int]), f::recover(states[0])),
    decreases count,
{
    if count > 0 {
        tracking_trace_prefix(eq, states, steps, (count - 1) as nat);
        let i = count - 1; let a = states[i]; let next = f::track(steps[i].0, steps[i].1, a);
        o::compose_related(eq, a.undo, a.undo, steps[i].1, steps[i].1);
        assert(admissible(eq, next));
        assert(it::tracked_related(eq, next, next));
        assert(f::tracked_equal(next, states[count as int]));
        exact_tracked_transport(eq, next, next, states[count as int]);
        tracked_partial_equivalence(eq, next, states[count as int], states[count as int]);
        recovery_related(eq, next, states[count as int]);
        tracking_recovery(eq, steps[i].0, steps[i].1, a);
    }
}

pub proof fn tracking_trace_soundness<S>(eq: spec_fn(S, S) -> bool,
    states: Seq<f::Tracked<S>>, steps: Seq<(spec_fn(S) -> S, spec_fn(S) -> S)>)
    requires c::equivalence(eq), actual_tracking_trace(eq, states, steps), admissible(eq, states[0]),
    ensures forall|i: int| #![trigger states[i]] 0 <= i < states.len() ==> {
        &&& admissible(eq, states[i])
        &&& it::tracked_related(eq, f::recover(states[i]), f::recover(states[0]))
    },
{
    assert forall|i: int| #![trigger states[i]] 0 <= i < states.len() implies {
        &&& admissible(eq, states[i])
        &&& it::tracked_related(eq, f::recover(states[i]), f::recover(states[0]))
    } by {
        tracking_trace_prefix(eq, states, steps, i as nat);
    }
}

pub proof fn effect_composition_related<S>(eq: spec_fn(S, S) -> bool,
    f1: spec_fn(S) -> f::Tracked<S>, f2: spec_fn(S) -> f::Tracked<S>,
    g1: spec_fn(S) -> f::Tracked<S>, g2: spec_fn(S) -> f::Tracked<S>)
    requires o::related_effects(eq, f1, f2), o::related_effects(eq, g1, g2),
    ensures o::related_effects(eq, |s: S| f::diamond(f1, g1, s), |s: S| f::diamond(f2, g2, s)),
{
    assert forall|a: S, b: S| #![trigger f::diamond(f1, g1, a), f::diamond(f2, g2, b)]
        eq(a, b) implies {
            &&& eq(f::diamond(f1, g1, a).value, f::diamond(f2, g2, b).value)
            &&& o::related_maps(eq, f::diamond(f1, g1, a).undo, f::diamond(f2, g2, b).undo)
        } by {
        assert(eq(g1(a).value, g2(b).value));
        o::compose_related(eq, g1(a).undo, g2(b).undo, f1(g1(a).value).undo, f2(g2(b).value).undo);
    }
}

/// Theorem 10(1). These are laws of effect functions, not merely one fixed
/// execution: each relation compares every pair of related input states.
pub proof fn effect_monoid<S>(eq: spec_fn(S, S) -> bool,
    first: spec_fn(S) -> f::Tracked<S>, second: spec_fn(S) -> f::Tracked<S>,
    third: spec_fn(S) -> f::Tracked<S>)
    requires o::related_effects(eq, first, first), o::related_effects(eq, second, second),
        o::related_effects(eq, third, third),
    ensures o::related_effects(eq, |s: S| f::diamond(first, |s: S| f::unit(s), s), first),
        o::related_effects(eq, |s: S| f::diamond(|s: S| f::unit(s), first, s), first),
        o::related_effects(eq, |s: S| f::diamond(|s: S| f::diamond(first, second, s), third, s),
            |s: S| f::diamond(first, |s: S| f::diamond(second, third, s), s)),
{
    effect_composition_related(eq, first, first, second, second);
    let fg = |s: S| f::diamond(first, second, s);
    effect_composition_related(eq, fg, fg, third, third);
    let left = |s: S| f::diamond(fg, third, s);
    let right = |s: S| f::diamond(first, |s: S| f::diamond(second, third, s), s);
    assert forall|a: S, b: S| #![trigger left(a), right(b)] eq(a, b) implies {
        &&& eq(left(a).value, right(b).value)
        &&& o::related_maps(eq, left(a).undo, right(b).undo)
    } by {
        f::effect_monoid(first, second, third, b);
        exact_tracked_transport(eq, left(a), left(b), right(b));
    }
}

/// Theorem 10(2): the uniform-pair embedding preserves both unit and twisted
/// multiplication on the entire quotient function space.
pub proof fn uniform_homomorphism<S>(eq: spec_fn(S, S) -> bool,
    f1: spec_fn(S) -> S, g1: spec_fn(S) -> S, f2: spec_fn(S) -> S, g2: spec_fn(S) -> S)
    requires o::related_maps(eq, f1, f1), o::related_maps(eq, g1, g1),
        o::related_maps(eq, f2, f2), o::related_maps(eq, g2, g2),
    ensures o::related_effects(eq, |s: S| f::uniform(|s: S| s, |s: S| s, s), |s: S| f::unit(s)),
        o::related_effects(eq,
            |s: S| f::diamond(|s: S| f::uniform(f1, g1, s), |s: S| f::uniform(f2, g2, s), s),
            |s: S| f::uniform(f::compose(f1, f2), f::compose(g2, g1), s)),
{
    o::compose_related(eq, g2, g2, g1, g1);
}

/// Both clauses of Theorem 11, with the Definition 36 witness. In particular
/// the unit witnesses and a uniform observational left inverse witnesses.
pub proof fn witnessed_submonoid<S>(eq: spec_fn(S, S) -> bool,
    first: spec_fn(S) -> f::Tracked<S>, second: spec_fn(S) -> f::Tracked<S>,
    forward: spec_fn(S) -> S, inverse: spec_fn(S) -> S)
    requires c::equivalence(eq), o::witnessed_effect(eq, first), o::witnessed_effect(eq, second),
        o::related_maps(eq, forward, forward), o::related_maps(eq, inverse, inverse),
        forall|s: S| #[trigger] eq(inverse(forward(s)), s),
    ensures o::witnessed_effect(eq, |s: S| f::unit(s)),
        o::witnessed_effect(eq, |s: S| f::diamond(first, second, s)),
        o::witnessed_effect(eq, |s: S| f::uniform(forward, inverse, s)),
{
    o::witnessed_effect_composition(eq, first, second);
}

/// Theorem 13 preserves the entire returned lifted inverse. The quantifier in
/// lifted_related compares it at arbitrary related admissible contexts.
pub proof fn effect_homomorphism<S>(eq: spec_fn(S, S) -> bool,
    first: spec_fn(S) -> f::Tracked<S>, second: spec_fn(S) -> f::Tracked<S>,
    a: f::Tracked<S>, b: f::Tracked<S>)
    requires it::tracked_related(eq, a, b), o::related_effects(eq, first, first),
        o::related_effects(eq, second, second),
    ensures it::lifted_related(eq,
        f::diamond(|s: f::Tracked<S>| f::effect(first, s), |s: f::Tracked<S>| f::effect(second, s), a),
        f::effect(|s: S| f::diamond(first, second, s), b)),
{
    effect_composition_related(eq, first, first, second, second);
    it::effect_related(eq, second, second, a, b);
    let ga = f::effect(second, a); let gb = f::effect(second, b);
    it::effect_related(eq, first, first, ga.value, gb.value);
    let fa = f::effect(first, ga.value); let fb = f::effect(first, gb.value);
    let left = f::diamond(|s: f::Tracked<S>| f::effect(first, s), |s: f::Tracked<S>| f::effect(second, s), a);
    let middle = f::diamond(|s: f::Tracked<S>| f::effect(first, s), |s: f::Tracked<S>| f::effect(second, s), b);
    assert forall|x: f::Tracked<S>, y: f::Tracked<S>| it::tracked_related(eq, x, y) implies
        #[trigger] it::tracked_related(eq, (left.undo)(x), (middle.undo)(y)) by {
        assert(it::tracked_related(eq, (fa.undo)(x), (fb.undo)(y)));
        assert(it::tracked_related(eq, (ga.undo)((fa.undo)(x)), (gb.undo)((fb.undo)(y))));
    }
    f::effect_homomorphism(first, second, b);
    exact_lifted_transport(eq, left, middle, f::effect(|s: S| f::diamond(first, second, s), b));
}

/// Theorem 14: both lifted directions commute with projection, read at
/// related inputs. The inverse is the one yielded at this invocation.
pub proof fn effect_projection<S>(eq: spec_fn(S, S) -> bool,
    effect: spec_fn(S) -> f::Tracked<S>, a: f::Tracked<S>, b: f::Tracked<S>, x: S, y: S)
    requires c::equivalence(eq), o::related_effects(eq, effect, effect),
        eq(a.value, x), eq(b.value, y),
    ensures eq(f::effect(effect, a).value.value, effect(x).value),
        eq(((f::effect(effect, a).undo)(b)).value, (effect(a.value).undo)(y)),
{
    assert(eq(a.value, a.value));
    assert(o::related_maps(eq, effect(a.value).undo, effect(a.value).undo));
}

pub open spec fn full_recovery<S>(eq: spec_fn(S, S) -> bool,
    effect: spec_fn(S) -> f::Tracked<S>, input: S, phi: spec_fn(S) -> S) -> bool
{
    let a = f::Tracked { value: input, undo: phi }; let lifted = f::effect(effect, a);
    it::tracked_related(eq, (lifted.undo)(lifted.value), a)
}

/// Theorem 15's explicit equation and invariant: only the recovered state is
/// quotiented; the accumulator still has exactly its printed composition.
pub proof fn lifted_recovery<S>(eq: spec_fn(S, S) -> bool,
    effect: spec_fn(S) -> f::Tracked<S>, input: S, phi: spec_fn(S) -> S)
    requires c::equivalence(eq), o::witnessed_effect(eq, effect), o::related_maps(eq, phi, phi),
    ensures {
        let a = f::Tracked { value: input, undo: phi }; let lifted = f::effect(effect, a);
        let back = (lifted.undo)(lifted.value);
        &&& eq(back.value, input)
        &&& f::maps_equal(back.undo, f::compose(f::compose(phi, effect(input).undo), |s: S| effect(s).value))
        &&& eq((back.undo)(input), phi(input))
        &&& eq((back.undo)(back.value), phi(input))
        &&& it::tracked_related(eq, f::recover(back), f::recover(a))
        &&& admissible(eq, back)
    },
{
    let a = f::Tracked { value: input, undo: phi }; let lifted = f::effect(effect, a);
    o::observational_tracking(eq, effect, a);
    it::observational_revert(eq, effect, input, lifted.value);
}

/// Theorem 15's iff, with precisely the necessary observational reading:
/// every respecting accumulator is restored iff the inverse actually yielded
/// at input is a uniform left inverse up to eq. The identity accumulator proves
/// necessity; arbitrary constituent respect proves sufficiency.
pub proof fn full_accumulator_recovery_iff<S>(eq: spec_fn(S, S) -> bool,
    effect: spec_fn(S) -> f::Tracked<S>, input: S)
    requires c::equivalence(eq), o::witnessed_effect(eq, effect),
    ensures (forall|phi: spec_fn(S) -> S| o::related_maps(eq, phi, phi)
        ==> #[trigger] full_recovery(eq, effect, input, phi))
        == (forall|s: S| #[trigger] eq((effect(input).undo)(effect(s).value), s)),
{
    if forall|s: S| #[trigger] eq((effect(input).undo)(effect(s).value), s) {
        assert forall|phi: spec_fn(S) -> S| o::related_maps(eq, phi, phi) implies
            #[trigger] full_recovery(eq, effect, input, phi) by {
            let a = f::Tracked { value: input, undo: phi }; let lifted = f::effect(effect, a);
            let back = (lifted.undo)(lifted.value);
            assert(eq(back.value, input));
            assert forall|x: S, y: S| eq(x, y) implies #[trigger] eq((back.undo)(x), phi(y)) by {
                assert(eq((effect(input).undo)(effect(x).value), x));
                assert(eq((effect(input).undo)(effect(x).value), y));
            }
        }
    } else {
        let phi = |s: S| s;
        let s = choose|s: S| !#[trigger] eq((effect(input).undo)(effect(s).value), s);
        assert(o::related_maps(eq, phi, phi));
        assert(eq(s, s));
        let a = f::Tracked { value: input, undo: phi }; let lifted = f::effect(effect, a);
        let back = (lifted.undo)(lifted.value);
        assert((back.undo)(s) == (effect(input).undo)(effect(s).value));
        if full_recovery(eq, effect, input, phi) {
            assert(o::related_maps(eq, back.undo, phi));
            assert(eq((back.undo)(s), phi(s)));
        }
        assert(!full_recovery(eq, effect, input, phi));
    }
}

/// The corresponding membership claim in Theorem 15, simultaneously at
/// every state, rather than confusing a local inverse with a uniform one.
pub proof fn lifted_witness_iff<S>(eq: spec_fn(S, S) -> bool,
    effect: spec_fn(S) -> f::Tracked<S>)
    requires c::equivalence(eq), o::witnessed_effect(eq, effect),
    ensures (forall|a: f::Tracked<S>| admissible(eq, a)
        ==> #[trigger] full_recovery(eq, effect, a.value, a.undo))
        == (forall|input: S, s: S| #[trigger] eq((effect(input).undo)(effect(s).value), s)),
{
    if forall|input: S, s: S| #[trigger] eq((effect(input).undo)(effect(s).value), s) {
        assert forall|a: f::Tracked<S>| admissible(eq, a) implies
            #[trigger] full_recovery(eq, effect, a.value, a.undo) by {
            full_accumulator_recovery_iff(eq, effect, a.value);
        }
    }
    if forall|a: f::Tracked<S>| admissible(eq, a) ==> #[trigger] full_recovery(eq, effect, a.value, a.undo) {
        assert forall|input: S, s: S| #[trigger] eq((effect(input).undo)(effect(s).value), s) by {
            assert forall|phi: spec_fn(S) -> S| o::related_maps(eq, phi, phi) implies
                #[trigger] full_recovery(eq, effect, input, phi) by {
                let a = f::Tracked { value: input, undo: phi };
                assert(admissible(eq, a));
                assert(full_recovery(eq, effect, a.value, a.undo));
            }
            full_accumulator_recovery_iff(eq, effect, input);
        }
    }
}

/// Theorem 16 at every reverse boundary, including a current state merely
/// related to the actual forward yield. The originally yielded inverses and
/// their original forward maps are retained by foundations::revert_suffix.
pub proof fn revert_prefix_sound<S>(eq: spec_fn(S, S) -> bool,
    effects: Seq<spec_fn(S) -> f::Tracked<S>>, initial: f::Tracked<S>, keep: nat, current: f::Tracked<S>)
    requires c::equivalence(eq), keep <= effects.len(), admissible(eq, current),
        eq(current.value, f::apply_effects(effects, initial).value),
        forall|i: int| 0 <= i < effects.len() ==> o::witnessed_effect(eq, effects[i]),
    ensures {
        let restored = f::revert_suffix(effects, initial, keep, current);
        &&& eq(restored.value, f::apply_effects(effects.subrange(0, keep as int), initial).value)
        &&& eq((restored.undo)(restored.value), (current.undo)(current.value))
        &&& admissible(eq, restored)
    },
    decreases effects.len(),
{
    if effects.len() == keep { assert(effects.subrange(0, keep as int) =~= effects); }
    else {
        let before = f::apply_effects(effects.drop_last(), initial); let effect = effects.last();
        assert(o::witnessed_effect(eq, effect));
        it::observational_revert(eq, effect, before.value, current);
        let next = f::track(effect(before.value).undo, |s: S| effect(s).value, current);
        revert_prefix_sound(eq, effects.drop_last(), initial, keep, next);
        assert(effects.drop_last().subrange(0, keep as int) =~= effects.subrange(0, keep as int));
    }
}

/// Forward and every partial reverse run from a respecting accumulator share
/// its original recovery target. Taking initial = unit(s) is Lemma 38's
/// reachable-accumulator clause, for arbitrary finite execution lengths.
pub proof fn local_temporal_sequence<S>(eq: spec_fn(S, S) -> bool,
    effects: Seq<spec_fn(S) -> f::Tracked<S>>, initial: f::Tracked<S>, keep: nat)
    requires c::equivalence(eq), keep <= effects.len(), admissible(eq, initial),
        forall|i: int| 0 <= i < effects.len() ==> o::witnessed_effect(eq, effects[i]),
    ensures {
        let applied = f::apply_effects(effects, initial);
        let restored = f::revert_suffix(effects, initial, keep, applied);
        &&& eq(restored.value, f::apply_effects(effects.subrange(0, keep as int), initial).value)
        &&& eq((applied.undo)(applied.value), (initial.undo)(initial.value))
        &&& eq((restored.undo)(restored.value), (initial.undo)(initial.value))
        &&& admissible(eq, applied) && admissible(eq, restored)
    },
{
    o::observational_sequence_recovery(eq, effects, initial);
    let applied = f::apply_effects(effects, initial);
    revert_prefix_sound(eq, effects, initial, keep, applied);
}

/// Definitions 17/18 use actual dynamically selected continuations. The
/// entire least witnessed iterator has a completion at each input and both
/// its forward and actual returned reverse satisfy the same invariant.
pub proof fn whole_iterator_recovery<S, I>(eq: spec_fn(S, S) -> bool,
    family: q::IteratorFamily<S, I>, id: I, initial: f::Tracked<S>)
    requires c::equivalence(eq), it::paper_witnessed(eq, family, id), admissible(eq, initial),
    ensures {
        let lifted = it::whole_effectiter(family, id, initial);
        let restored = (lifted.undo)(lifted.value);
        &&& eq((lifted.value.undo)(lifted.value.value), (initial.undo)(initial.value))
        &&& eq(restored.value, initial.value)
        &&& eq((restored.undo)(restored.value), (initial.undo)(initial.value))
        &&& admissible(eq, lifted.value) && admissible(eq, restored)
    },
{
    it::inductive_termination(family, id);
    it::iterator_temporal_soundness(eq, family, Some(id), it::completion_fuel(family, id, initial), initial);
}

/// Definition 18 respects recursive iterator equivalence, including the
/// complete returned inverse, at every finite observation boundary. Related
/// continuations may have different indices; no same-schedule assumption is
/// imposed on a dynamically selected continuation.
pub proof fn effectiter_related<S, I>(eq: spec_fn(S, S) -> bool,
    family: q::IteratorFamily<S, I>, left: Option<I>, right: Option<I>, fuel: nat,
    a: f::Tracked<S>, b: f::Tracked<S>)
    requires it::tracked_related(eq, a, b),
        q::continuation(|i: I, j: I| q::iterator_related(eq, family, i, j), left, right),
    ensures it::lifted_related(eq, it::effectiter(family, left, fuel, a), it::effectiter(family, right, fuel, b)),
        q::continuation(|i: I, j: I| q::iterator_related(eq, family, i, j),
            it::run(family, left, fuel, a).next, it::run(family, right, fuel, b).next),
    decreases fuel,
{
    if fuel > 0 && left.is_some() {
        assert(right.is_some()); let i = left.unwrap(); let j = right.unwrap();
        q::iterator_unfolding(eq, family, i, j);
        assert(o::related_effects(eq, it::stage(family, i), it::stage(family, j)));
        it::effect_related(eq, it::stage(family, i), it::stage(family, j), a, b);
        let first = f::effect(it::stage(family, i), a); let other = f::effect(it::stage(family, j), b);
        let next = family(i, a.value).next; let other_next = family(j, b.value).next;
        effectiter_related(eq, family, next, other_next, (fuel - 1) as nat, first.value, other.value);
        let tail = it::effectiter(family, next, (fuel - 1) as nat, first.value);
        let other_tail = it::effectiter(family, other_next, (fuel - 1) as nat, other.value);
        let result = it::effectiter(family, left, fuel, a); let other_result = it::effectiter(family, right, fuel, b);
        assert forall|x: f::Tracked<S>, y: f::Tracked<S>| it::tracked_related(eq, x, y) implies
            #[trigger] it::tracked_related(eq, (result.undo)(x), (other_result.undo)(y)) by {
            assert(it::tracked_related(eq, (tail.undo)(x), (other_tail.undo)(y)));
            assert(it::tracked_related(eq, (first.undo)((tail.undo)(x)), (other.undo)((other_tail.undo)(y))));
        }
    }
}

/// The same congruence for the whole least iterator, with no fuel or common
/// finite height in the contract. Completion on one side transports to the
/// other; uniqueness of actual completed yields removes the different fuel
/// witnesses used by whole_effectiter.
pub proof fn whole_effectiter_related<S, I>(eq: spec_fn(S, S) -> bool,
    family: q::IteratorFamily<S, I>, left: I, right: I, a: f::Tracked<S>, b: f::Tracked<S>)
    requires it::inductive_member(family, left), it::inductive_member(family, right),
        q::iterator_related(eq, family, left, right), it::tracked_related(eq, a, b),
    ensures it::lifted_related(eq, it::whole_effectiter(family, left, a), it::whole_effectiter(family, right, b)),
{
    it::inductive_termination(family, left); it::inductive_termination(family, right);
    assert(it::has_completion(family, left, a)); assert(it::has_completion(family, right, b));
    let fuel = it::completion_fuel(family, left, a); let other_fuel = it::completion_fuel(family, right, b);
    assert(it::run(family, Some(left), fuel, a).next.is_none());
    assert(it::run(family, Some(right), other_fuel, b).next.is_none());
    effectiter_related(eq, family, Some(left), Some(right), fuel, a, b);
    assert(it::run(family, Some(right), fuel, b).next.is_none());
    it::completed_effect_unique(family, Some(right), fuel, other_fuel, b);
    exact_lifted_transport(eq, it::whole_effectiter(family, left, a),
        it::effectiter(family, Some(right), fuel, b), it::whole_effectiter(family, right, b));
}

} // verus!
