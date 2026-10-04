//! Arbitrary-index witnessed iterators and finite observations of their runs.
//!
//! Continuations are closed coinductively, without a shared termination rank.
//! Whole-iterator effects are defined on terminating runs; a finite prefix is
//! meaningful even when the iterator continues forever.
#[cfg(verus_keep_ghost)]
use crate::{calculus, observation as o, quotient as q};
use crate::{foundations as f, mediated};
use vstd::prelude::*;

verus! {

pub open spec fn stage<S, I>(family: q::IteratorFamily<S, I>, id: I) -> spec_fn(S) -> f::Tracked<S> {
    |s: S| f::Tracked { value: family(id, s).state, undo: family(id, s).undo }
}

pub open spec fn witnessed_closed<S, I>(eq: spec_fn(S, S) -> bool,
    family: q::IteratorFamily<S, I>, names: ISet<I>) -> bool
{
    forall|id: I| names.contains(id) ==> {
        &&& q::iterator_related(eq, family, id, id)
        &&& forall|s: S| #[trigger] eq((family(id, s).undo)(family(id, s).state), s)
        &&& forall|s: S| #[trigger] family(id, s).next.is_some() ==> names.contains(family(id, s).next.unwrap())
    }
}

/// Definitions 17/37: the greatest continuation-closed family of witnessed
/// iterators. `I` may be any type, including an uncountable index space.
pub open spec fn witnessed<S, I>(eq: spec_fn(S, S) -> bool,
    family: q::IteratorFamily<S, I>, id: I) -> bool
{
    exists|names: ISet<I>| names.contains(id) && witnessed_closed(eq, family, names)
}

pub proof fn witnessed_unfolding<S, I>(eq: spec_fn(S, S) -> bool,
    family: q::IteratorFamily<S, I>, id: I)
    ensures witnessed(eq, family, id) == {
        &&& q::iterator_related(eq, family, id, id)
        &&& forall|s: S| #[trigger] eq((family(id, s).undo)(family(id, s).state), s)
        &&& forall|s: S| #[trigger] family(id, s).next.is_some() ==> witnessed(eq, family, family(id, s).next.unwrap())
    },
{
    let all = ISet::new(|i: I| witnessed(eq, family, i));
    assert(witnessed_closed(eq, family, all)) by {
        assert forall|i: I| all.contains(i) implies {
            &&& q::iterator_related(eq, family, i, i)
            &&& forall|s: S| #[trigger] eq((family(i, s).undo)(family(i, s).state), s)
            &&& forall|s: S| #[trigger] family(i, s).next.is_some() ==> all.contains(family(i, s).next.unwrap())
        } by {
            let names = choose|names: ISet<I>| names.contains(i) && witnessed_closed(eq, family, names);
            assert forall|s: S| #[trigger] family(i, s).next.is_some() implies all.contains(family(i, s).next.unwrap()) by {
                assert(names.contains(family(i, s).next.unwrap()));
                assert(witnessed(eq, family, family(i, s).next.unwrap()));
            }
        }
    }
    if !witnessed(eq, family, id) {
        let extended = all.insert(id);
        if q::iterator_related(eq, family, id, id)
            && (forall|s: S| #[trigger] eq((family(id, s).undo)(family(id, s).state), s))
            && (forall|s: S| #[trigger] family(id, s).next.is_some() ==> witnessed(eq, family, family(id, s).next.unwrap())) {
            assert(witnessed_closed(eq, family, extended));
            assert(extended.contains(id));
            assert(witnessed(eq, family, id));
        }
    }
}

pub proof fn witnessed_stage<S, I>(eq: spec_fn(S, S) -> bool, family: q::IteratorFamily<S, I>, id: I, input: S)
    requires witnessed(eq, family, id),
    ensures o::witnessed_effect(eq, stage(family, id)),
        family(id, input).next.is_some() ==> witnessed(eq, family, family(id, input).next.unwrap()),
{
    witnessed_unfolding(eq, family, id);
    q::iterator_unfolding(eq, family, id, id);
}

/// Exact equality entails respect for every deterministic iterator family.
pub proof fn equality_respect<S, I>(family: q::IteratorFamily<S, I>, id: I)
    ensures q::iterator_related(|a: S, b: S| a == b, family, id, id),
{
    let diagonal = |i: I, j: I| i == j;
    assert(q::bisimulation(|a: S, b: S| a == b, family, diagonal));
    assert(diagonal(id, id));
}

/// The coinductive witness at equality is exactly local inverse recovery and
/// recursive membership; respect does not strengthen Definition 17.
pub proof fn exact_witness_family<S, I>(family: q::IteratorFamily<S, I>, names: ISet<I>, id: I)
    requires names.contains(id),
        forall|i: I, s: S| #![trigger family(i, s)] names.contains(i) ==> (family(i, s).undo)(family(i, s).state) == s
            && (family(i, s).next.is_some() ==> names.contains(family(i, s).next.unwrap())),
    ensures witnessed(|a: S, b: S| a == b, family, id),
{
    assert forall|i: I| names.contains(i) implies {
        &&& q::iterator_related(|a: S, b: S| a == b, family, i, i)
        &&& forall|s: S| #[trigger] (family(i, s).undo)(family(i, s).state) == s
        &&& forall|s: S| #[trigger] family(i, s).next.is_some() ==> names.contains(family(i, s).next.unwrap())
    } by { equality_respect(family, i); }
    assert(witnessed_closed(|a: S, b: S| a == b, family, names));
}

pub open spec fn embed<S>(effect: spec_fn(S) -> f::Tracked<S>) -> q::IteratorFamily<S, ()> {
    |_: (), s: S| q::Iteration { state: effect(s).value, undo: effect(s).undo, next: None }
}

pub proof fn embedding_witness<S>(eq: spec_fn(S, S) -> bool, effect: spec_fn(S) -> f::Tracked<S>)
    requires o::witnessed_effect(eq, effect),
    ensures witnessed(eq, embed(effect), ()),
{
    let family = embed(effect);
    let relation = |_: (), _: ()| true;
    assert(q::bisimulation(eq, family, relation));
    assert(q::iterator_related(eq, family, (), ()));
    assert(witnessed_closed(eq, family, ISet::full()));
    assert(ISet::<()>::full().contains(()));
}

#[verifier::reject_recursive_types(S)]
pub struct Prefix<S, I> { pub current: f::Tracked<S>, pub next: Option<I> }

/// Stop at a boundary or at termination. Each continuation is selected at the
/// actual forward state, and its actual returned inverse enters the journal.
pub open spec fn run<S, I>(family: q::IteratorFamily<S, I>, next: Option<I>, fuel: nat, initial: f::Tracked<S>) -> Prefix<S, I>
    decreases fuel,
{
    if fuel == 0 || next.is_none() { Prefix { current: initial, next } }
    else {
        let yielded = family(next.unwrap(), initial.value);
        let current = f::Tracked { value: yielded.state, undo: f::compose(initial.undo, yielded.undo) };
        run(family, yielded.next, (fuel - 1) as nat, current)
    }
}

pub proof fn prefix_recovery<S, I>(eq: spec_fn(S, S) -> bool, family: q::IteratorFamily<S, I>, next: Option<I>, fuel: nat, initial: f::Tracked<S>)
    requires calculus::equivalence(eq), o::related_maps(eq, initial.undo, initial.undo),
        next.is_some() ==> witnessed(eq, family, next.unwrap()),
    ensures {
        let result = run(family, next, fuel, initial);
        &&& eq((result.current.undo)(result.current.value), (initial.undo)(initial.value))
        &&& o::related_maps(eq, result.current.undo, result.current.undo)
        &&& (result.next.is_some() ==> witnessed(eq, family, result.next.unwrap()))
    },
    decreases fuel,
{
    if fuel > 0 && next.is_some() {
        let id = next.unwrap(); let yielded = family(id, initial.value);
        witnessed_stage(eq, family, id, initial.value);
        o::observational_tracking(eq, stage(family, id), initial);
        let current = f::Tracked { value: yielded.state, undo: f::compose(initial.undo, yielded.undo) };
        prefix_recovery(eq, family, yielded.next, (fuel - 1) as nat, current);
    }
}

pub proof fn exact_prefix_recovery<S, I>(family: q::IteratorFamily<S, I>, next: Option<I>, fuel: nat, initial: f::Tracked<S>)
    requires next.is_some() ==> witnessed(|a: S, b: S| a == b, family, next.unwrap()),
    ensures (run(family, next, fuel, initial).current.undo)(run(family, next, fuel, initial).current.value)
        == (initial.undo)(initial.value),
{
    prefix_recovery(|a: S, b: S| a == b, family, next, fuel, initial);
}

/// Definition 18's recursive equation, evaluated for a finite number of actual
/// yields. This is the whole-iterator effect precisely when `run.next == None`.
pub open spec fn effectiter<S, I>(family: q::IteratorFamily<S, I>, next: Option<I>, fuel: nat, initial: f::Tracked<S>) -> f::Tracked<f::Tracked<S>>
    decreases fuel,
{
    if fuel == 0 || next.is_none() { f::unit(initial) }
    else {
        let id = next.unwrap(); let yielded = family(id, initial.value);
        let first = f::effect(stage(family, id), initial);
        let tail = effectiter(family, yielded.next, (fuel - 1) as nat, first.value);
        f::Tracked { value: tail.value, undo: f::compose(first.undo, tail.undo) }
    }
}

pub proof fn effectiter_projection<S, I>(family: q::IteratorFamily<S, I>, next: Option<I>, fuel: nat, initial: f::Tracked<S>)
    ensures f::tracked_equal(effectiter(family, next, fuel, initial).value, run(family, next, fuel, initial).current),
    decreases fuel,
{
    if fuel > 0 && next.is_some() {
        let yielded = family(next.unwrap(), initial.value);
        effectiter_projection(family, yielded.next, (fuel - 1) as nat, f::effect(stage(family, next.unwrap()), initial).value);
    }
}

/// Finishing is an execution-specific condition, not a global finite rank.
/// Additional fuel cannot change any part of a completed lifted effect.
pub proof fn completed_effect_stable<S, I>(family: q::IteratorFamily<S, I>, next: Option<I>, fuel: nat, extra: nat, initial: f::Tracked<S>)
    requires run(family, next, fuel, initial).next.is_none(),
    ensures f::lifted_equal(effectiter(family, next, fuel + extra, initial), effectiter(family, next, fuel, initial)),
    decreases fuel,
{
    if next.is_some() {
        assert(fuel > 0);
        let yielded = family(next.unwrap(), initial.value);
        let first = f::effect(stage(family, next.unwrap()), initial);
        completed_effect_stable(family, yielded.next, (fuel - 1) as nat, extra, first.value);
        let left = effectiter(family, next, fuel + extra, initial);
        let right = effectiter(family, next, fuel, initial);
        let tail_left = effectiter(family, yielded.next, (fuel + extra - 1) as nat, first.value);
        let tail_right = effectiter(family, yielded.next, (fuel - 1) as nat, first.value);
        assert forall|s: f::Tracked<S>| #[trigger] f::tracked_equal((left.undo)(s), (right.undo)(s)) by {
            assert(f::tracked_equal((tail_left.undo)(s), (tail_right.undo)(s)));
            assert forall|x: S| #[trigger] (((left.undo)(s)).undo)(x) == (((right.undo)(s)).undo)(x) by {
                assert((((tail_left.undo)(s)).undo)(family(next.unwrap(), x).state)
                    == (((tail_right.undo)(s)).undo)(family(next.unwrap(), x).state));
            }
        }
    }
}

pub proof fn embedded_effectiter<S>(effect: spec_fn(S) -> f::Tracked<S>, input: f::Tracked<S>)
    ensures run(embed(effect), Some(()), 1, input).next.is_none(),
        f::lifted_equal(effectiter(embed(effect), Some(()), 1, input), f::effect(effect, input)),
{ reveal_with_fuel(run, 2); reveal_with_fuel(effectiter, 2); }

/// Lemma 38 / Theorem 15 at a related current state. The actual returned
/// inverse is retained, and the incoming accumulator need not be the original
/// accumulator. Only its respect for the observation relation is required.
pub proof fn observational_revert<S>(eq: spec_fn(S, S) -> bool,
    effect: spec_fn(S) -> f::Tracked<S>, input: S, current: f::Tracked<S>)
    requires calculus::equivalence(eq), o::witnessed_effect(eq, effect),
        o::related_maps(eq, current.undo, current.undo), eq(current.value, effect(input).value),
    ensures {
        let restored = f::track(effect(input).undo, |s: S| effect(s).value, current);
        &&& eq(restored.value, input)
        &&& eq((restored.undo)(restored.value), (current.undo)(current.value))
        &&& o::related_maps(eq, restored.undo, restored.undo)
    },
{
    let forward = |s: S| effect(s).value;
    assert(o::related_maps(eq, forward, forward));
    assert(eq(input, input));
    assert(o::related_maps(eq, effect(input).undo, effect(input).undo));
    let restored = f::track(effect(input).undo, forward, current);
    assert(eq(restored.value, (effect(input).undo)(effect(input).value)));
    assert(eq((effect(input).undo)(effect(input).value), input));
    assert(eq(restored.value, input));
    assert(eq(forward(restored.value), forward(input)));
    assert(eq(effect(input).value, current.value));
    assert(eq(forward(restored.value), current.value));
    o::compose_related(eq, current.undo, current.undo, forward, forward);
}

/// Every finite iterator prefix can be reversed with its own actual yielded
/// inverses. This proves the whole effectiter reverse equation and all prefix
/// boundaries, including observational witnesses and dynamic continuations.
pub proof fn effectiter_recovery<S, I>(eq: spec_fn(S, S) -> bool, family: q::IteratorFamily<S, I>,
    next: Option<I>, fuel: nat, initial: f::Tracked<S>, current: f::Tracked<S>)
    requires calculus::equivalence(eq),
        next.is_some() ==> witnessed(eq, family, next.unwrap()),
        eq(current.value, run(family, next, fuel, initial).current.value),
        o::related_maps(eq, current.undo, current.undo),
    ensures {
        let restored = (effectiter(family, next, fuel, initial).undo)(current);
        &&& eq(restored.value, initial.value)
        &&& eq((restored.undo)(restored.value), (current.undo)(current.value))
        &&& o::related_maps(eq, restored.undo, restored.undo)
    },
    decreases fuel,
{
    if fuel > 0 && next.is_some() {
        let id = next.unwrap(); let yielded = family(id, initial.value);
        let first = f::effect(stage(family, id), initial);
        witnessed_stage(eq, family, id, initial.value);
        effectiter_recovery(eq, family, yielded.next, (fuel - 1) as nat, first.value, current);
        let midway = (effectiter(family, yielded.next, (fuel - 1) as nat, first.value).undo)(current);
        observational_revert(eq, stage(family, id), initial.value, midway);
    }
}

/// Starting with a sound accumulator, both the forward lifted iterator and
/// its reverse retain its recovery target. Equality is obtained by choosing
/// equality for `eq`; no quotient-specific property beyond equivalence is used.
pub proof fn iterator_temporal_soundness<S, I>(eq: spec_fn(S, S) -> bool, family: q::IteratorFamily<S, I>,
    next: Option<I>, fuel: nat, initial: f::Tracked<S>)
    requires calculus::equivalence(eq), o::related_maps(eq, initial.undo, initial.undo),
        next.is_some() ==> witnessed(eq, family, next.unwrap()),
    ensures {
        let lifted = effectiter(family, next, fuel, initial);
        let restored = (lifted.undo)(lifted.value);
        &&& eq((lifted.value.undo)(lifted.value.value), (initial.undo)(initial.value))
        &&& eq(restored.value, initial.value)
        &&& eq((restored.undo)(restored.value), (initial.undo)(initial.value))
        &&& o::related_maps(eq, lifted.value.undo, lifted.value.undo)
        &&& o::related_maps(eq, restored.undo, restored.undo)
    },
{
    prefix_recovery(eq, family, next, fuel, initial);
    effectiter_projection(family, next, fuel, initial);
    let lifted = effectiter(family, next, fuel, initial);
    let result = run(family, next, fuel, initial);
    assert(o::related_maps(eq, lifted.value.undo, lifted.value.undo));
    assert(eq(lifted.value.value, result.current.value));
    effectiter_recovery(eq, family, next, fuel, initial, lifted.value);
}

pub open spec fn tracked_related<S>(eq: spec_fn(S, S) -> bool, a: f::Tracked<S>, b: f::Tracked<S>) -> bool {
    eq(a.value, b.value) && o::related_maps(eq, a.undo, b.undo)
}

pub open spec fn lifted_related<S>(eq: spec_fn(S, S) -> bool,
    a: f::Tracked<f::Tracked<S>>, b: f::Tracked<f::Tracked<S>>) -> bool
{
    tracked_related(eq, a.value, b.value)
        && forall|x: f::Tracked<S>, y: f::Tracked<S>| tracked_related(eq, x, y)
            ==> #[trigger] tracked_related(eq, (a.undo)(x), (b.undo)(y))
}

/// Theorem 3/Definition 34 lifted together: tracking preserves the entire
/// relation, including observational equivalence of accumulator maps.
pub proof fn track_related<S>(eq: spec_fn(S, S) -> bool,
    forward: spec_fn(S) -> S, other_forward: spec_fn(S) -> S,
    inverse: spec_fn(S) -> S, other_inverse: spec_fn(S) -> S,
    a: f::Tracked<S>, b: f::Tracked<S>)
    requires tracked_related(eq, a, b), o::related_maps(eq, forward, other_forward),
        o::related_maps(eq, inverse, other_inverse),
    ensures tracked_related(eq, f::track(forward, inverse, a), f::track(other_forward, other_inverse, b)),
{
    o::compose_related(eq, a.undo, b.undo, inverse, other_inverse);
}

/// Effect lifting itself descends to the observational quotient. The returned
/// lifted inverses are related at every pair of related tracked inputs.
pub proof fn effect_related<S>(eq: spec_fn(S, S) -> bool,
    left: spec_fn(S) -> f::Tracked<S>, right: spec_fn(S) -> f::Tracked<S>,
    a: f::Tracked<S>, b: f::Tracked<S>)
    requires tracked_related(eq, a, b), o::related_effects(eq, left, right),
    ensures lifted_related(eq, f::effect(left, a), f::effect(right, b)),
{
    let x = left(a.value); let y = right(b.value);
    assert(o::related_maps(eq, x.undo, y.undo));
    o::compose_related(eq, a.undo, b.undo, x.undo, y.undo);
    let forward = |s: S| left(s).value; let other = |s: S| right(s).value;
    assert(o::related_maps(eq, forward, other));
    assert forall|p: f::Tracked<S>, q: f::Tracked<S>| tracked_related(eq, p, q) implies
        #[trigger] tracked_related(eq, (f::effect(left, a).undo)(p), (f::effect(right, b).undo)(q)) by {
        track_related(eq, x.undo, y.undo, forward, other, p, q);
    }
}

/// Definition 37 is closed under the observational iterator relation, not
/// merely under equality of continuation indices. This connects witness
/// membership to the quotient's genuine recursive equivalence.
pub proof fn witnessed_transfer<S, I>(eq: spec_fn(S, S) -> bool, family: q::IteratorFamily<S, I>, id: I, other: I)
    requires calculus::equivalence(eq), witnessed(eq, family, id), q::iterator_related(eq, family, id, other),
    ensures witnessed(eq, family, other),
{
    let closure = ISet::new(|j: I| exists|i: I| witnessed(eq, family, i) && q::iterator_related(eq, family, i, j));
    q::greatest_bisimulation(eq, family);
    assert(witnessed_closed(eq, family, closure)) by {
        assert forall|j: I| closure.contains(j) implies {
            &&& q::iterator_related(eq, family, j, j)
            &&& forall|s: S| #[trigger] eq((family(j, s).undo)(family(j, s).state), s)
            &&& forall|s: S| #[trigger] family(j, s).next.is_some() ==> closure.contains(family(j, s).next.unwrap())
        } by {
            let i = choose|i: I| witnessed(eq, family, i) && q::iterator_related(eq, family, i, j);
            witnessed_unfolding(eq, family, i);
            q::iterator_partial_equivalence(eq, family, i, j, i);
            assert forall|s: S| #[trigger] eq((family(j, s).undo)(family(j, s).state), s) by {
                assert(eq(s, s));
                let x = family(i, s); let y = family(j, s);
                assert(eq(x.state, y.state));
                assert(o::related_maps(eq, x.undo, y.undo));
                assert(eq((x.undo)(x.state), (y.undo)(y.state)));
                assert(eq((x.undo)(x.state), s));
                assert(eq((y.undo)(y.state), (x.undo)(x.state)));
            }
            assert forall|s: S| #[trigger] family(j, s).next.is_some() implies closure.contains(family(j, s).next.unwrap()) by {
                assert(eq(s, s));
                let x = family(i, s); let y = family(j, s);
                assert(q::continuation(|a: I, b: I| q::iterator_related(eq, family, a, b), x.next, y.next));
                assert(x.next.is_some());
                assert(witnessed(eq, family, x.next.unwrap()));
                assert(q::iterator_related(eq, family, x.next.unwrap(), y.next.unwrap()));
            }
        }
    }
    assert(closure.contains(other));
}

pub open spec fn all_continuations<S, I>(family: q::IteratorFamily<S, I>, id: I, names: ISet<I>) -> bool {
    forall|s: S| #[trigger] family(id, s).next.is_some() ==> names.contains(family(id, s).next.unwrap())
}
pub open spec fn inductive_closed<S, I>(family: q::IteratorFamily<S, I>, names: ISet<I>) -> bool {
    forall|id: I| #[trigger] all_continuations(family, id, names) ==> names.contains(id)
}
/// The µ reading of Definition 17, distinguished from the potentially infinite
/// coalgebra used for coinductive observational equivalence. Induction is over
/// all successor states; it does not impose a natural-number height bound.
pub open spec fn inductive_member<S, I>(family: q::IteratorFamily<S, I>, id: I) -> bool {
    forall|names: ISet<I>| inductive_closed(family, names) ==> names.contains(id)
}
pub open spec fn inductive_members<S, I>(family: q::IteratorFamily<S, I>) -> ISet<I> {
    ISet::new(|id: I| inductive_member(family, id))
}
pub proof fn inductive_constructor<S, I>(family: q::IteratorFamily<S, I>, id: I)
    requires all_continuations(family, id, inductive_members(family)),
    ensures inductive_member(family, id),
{
    assert forall|names: ISet<I>| inductive_closed(family, names) implies names.contains(id) by {
        assert forall|s: S| #[trigger] family(id, s).next.is_some() implies names.contains(family(id, s).next.unwrap()) by {
            assert(inductive_member(family, family(id, s).next.unwrap()));
        }
        assert(all_continuations(family, id, names));
    }
}
pub proof fn inductive_unfolding<S, I>(family: q::IteratorFamily<S, I>, id: I)
    ensures inductive_member(family, id) == all_continuations(family, id, inductive_members(family)),
{
    if all_continuations(family, id, inductive_members(family)) { inductive_constructor(family, id); }
    if inductive_member(family, id) {
        let good = ISet::new(|i: I| inductive_member(family, i) && all_continuations(family, i, inductive_members(family)));
        assert(inductive_closed(family, good)) by {
            assert forall|i: I| #[trigger] all_continuations(family, i, good) implies good.contains(i) by {
                assert forall|s: S| #[trigger] family(i, s).next.is_some() implies inductive_members(family).contains(family(i, s).next.unwrap()) by {
                    assert(good.contains(family(i, s).next.unwrap()));
                }
                assert(all_continuations(family, i, inductive_members(family)));
                inductive_constructor(family, i);
            }
        }
        assert(good.contains(id));
    }
}

pub open spec fn has_completion<S, I>(family: q::IteratorFamily<S, I>, id: I, initial: f::Tracked<S>) -> bool {
    exists|fuel: nat| run(family, Some(id), fuel, initial).next.is_none()
}
pub open spec fn terminates<S, I>(family: q::IteratorFamily<S, I>, id: I) -> bool {
    forall|initial: f::Tracked<S>| #[trigger] has_completion(family, id, initial)
}

/// Least-type membership constructs a finite completion witness separately
/// for each actual input. There need not be any bound valid for all inputs.
pub proof fn inductive_termination<S, I>(family: q::IteratorFamily<S, I>, id: I)
    requires inductive_member(family, id),
    ensures terminates(family, id),
{
    let good = ISet::new(|i: I| terminates(family, i));
    assert(inductive_closed(family, good)) by {
        assert forall|i: I| #[trigger] all_continuations(family, i, good) implies good.contains(i) by {
            assert forall|initial: f::Tracked<S>| #[trigger] has_completion(family, i, initial) by {
                let yielded = family(i, initial.value);
                let current = f::Tracked { value: yielded.state, undo: f::compose(initial.undo, yielded.undo) };
                if yielded.next.is_some() {
                    assert(good.contains(yielded.next.unwrap()));
                    assert(terminates(family, yielded.next.unwrap()));
                    assert(has_completion(family, yielded.next.unwrap(), current));
                    let fuel = choose|fuel: nat| run(family, yielded.next, fuel, current).next.is_none();
                    assert(run(family, Some(i), fuel + 1, initial).next.is_none());
                } else {
                    reveal_with_fuel(run, 2);
                    assert(run(family, Some(i), 1, initial).next.is_none());
                }
            }
        }
    }
    assert(good.contains(id));
}

pub open spec fn completion_fuel<S, I>(family: q::IteratorFamily<S, I>, id: I, initial: f::Tracked<S>) -> nat {
    choose|fuel: nat| run(family, Some(id), fuel, initial).next.is_none()
}
pub open spec fn whole_effectiter<S, I>(family: q::IteratorFamily<S, I>, id: I, initial: f::Tracked<S>) -> f::Tracked<f::Tracked<S>>
    recommends inductive_member(family, id),
{
    effectiter(family, Some(id), completion_fuel(family, id, initial), initial)
}

pub proof fn completed_effect_unique<S, I>(family: q::IteratorFamily<S, I>, next: Option<I>, a: nat, b: nat, initial: f::Tracked<S>)
    requires run(family, next, a, initial).next.is_none(), run(family, next, b, initial).next.is_none(),
    ensures f::lifted_equal(effectiter(family, next, a, initial), effectiter(family, next, b, initial)),
{
    if a <= b {
        completed_effect_stable(family, next, a, (b - a) as nat, initial);
        let left = effectiter(family, next, a, initial); let right = effectiter(family, next, b, initial);
        assert forall|s: f::Tracked<S>| #[trigger] f::tracked_equal((left.undo)(s), (right.undo)(s)) by {
            assert(f::tracked_equal((right.undo)(s), (left.undo)(s)));
        }
    }
    else { completed_effect_stable(family, next, b, (a - b) as nat, initial); }
}

/// The unrestricted recursive equation printed in Definition 18 holds on the
/// entire least iterator type. Fuel is absent from the interface and different
/// finite completion witnesses produce the same lifted value and inverse.
pub proof fn whole_effectiter_equation<S, I>(family: q::IteratorFamily<S, I>, id: I, initial: f::Tracked<S>)
    requires inductive_member(family, id),
    ensures {
        let yielded = family(id, initial.value); let first = f::effect(stage(family, id), initial);
        let expected = if yielded.next.is_none() { first } else {
            let rest = whole_effectiter(family, yielded.next.unwrap(), first.value);
            f::Tracked { value: rest.value, undo: f::compose(first.undo, rest.undo) }
        };
        &&& run(family, Some(id), completion_fuel(family, id, initial), initial).next.is_none()
        &&& f::lifted_equal(whole_effectiter(family, id, initial), expected)
    },
{
    inductive_unfolding(family, id);
    inductive_termination(family, id);
    assert(has_completion(family, id, initial));
    let fuel = completion_fuel(family, id, initial);
    assert(run(family, Some(id), fuel, initial).next.is_none());
    assert(fuel > 0);
    let yielded = family(id, initial.value); let first = f::effect(stage(family, id), initial);
    if yielded.next.is_some() {
        let next = yielded.next.unwrap();
        assert(inductive_member(family, next));
        inductive_termination(family, next);
        assert(has_completion(family, next, first.value));
        let rest_fuel = completion_fuel(family, next, first.value);
        assert(run(family, Some(next), rest_fuel, first.value).next.is_none());
        completed_effect_unique(family, Some(next), (fuel - 1) as nat, rest_fuel, first.value);
        let left = whole_effectiter(family, id, initial);
        let rest = whole_effectiter(family, next, first.value);
        let expected = f::Tracked { value: rest.value, undo: f::compose(first.undo, rest.undo) };
        let tail = effectiter(family, Some(next), (fuel - 1) as nat, first.value);
        assert forall|s: f::Tracked<S>| #[trigger] f::tracked_equal((left.undo)(s), (expected.undo)(s)) by {
            assert(f::tracked_equal((tail.undo)(s), (rest.undo)(s)));
            assert forall|x: S| #[trigger] (((left.undo)(s)).undo)(x) == (((expected.undo)(s)).undo)(x) by {
                assert((((tail.undo)(s)).undo)(family(id, x).state) == (((rest.undo)(s)).undo)(family(id, x).state));
            }
        }
        assert(f::lifted_equal(left, expected));
    } else {
        reveal_with_fuel(effectiter, 2);
        assert(f::lifted_equal(whole_effectiter(family, id, initial), first));
    }
}

/// The witnessed µ type in Definitions 17/37. Coinductive respect is a
/// property of its members, not a replacement for their inductive membership.
pub open spec fn paper_witnessed<S, I>(eq: spec_fn(S, S) -> bool, family: q::IteratorFamily<S, I>, id: I) -> bool {
    inductive_member(family, id) && witnessed(eq, family, id)
}
pub open spec fn witnessed_constructor_closed<S, I>(eq: spec_fn(S, S) -> bool,
    family: q::IteratorFamily<S, I>, names: ISet<I>) -> bool
{
    forall|id: I| #[trigger] all_continuations(family, id, names)
        && q::iterator_related(eq, family, id, id)
        && (forall|s: S| #[trigger] eq((family(id, s).undo)(family(id, s).state), s))
        ==> names.contains(id)
}
pub proof fn paper_witnessed_unfolding<S, I>(eq: spec_fn(S, S) -> bool, family: q::IteratorFamily<S, I>, id: I)
    ensures paper_witnessed(eq, family, id) == {
        &&& q::iterator_related(eq, family, id, id)
        &&& forall|s: S| #[trigger] eq((family(id, s).undo)(family(id, s).state), s)
        &&& all_continuations(family, id, ISet::new(|i: I| paper_witnessed(eq, family, i)))
    },
{
    inductive_unfolding(family, id);
    witnessed_unfolding(eq, family, id);
}

/// This is the *least* family closed under the witnessed iterator constructor,
/// establishing the printed µ type rather than just its recursive equation.
pub proof fn paper_witnessed_least<S, I>(eq: spec_fn(S, S) -> bool, family: q::IteratorFamily<S, I>, id: I, names: ISet<I>)
    requires paper_witnessed(eq, family, id), witnessed_constructor_closed(eq, family, names),
    ensures names.contains(id),
{
    let good = ISet::new(|i: I| witnessed(eq, family, i) ==> names.contains(i));
    assert(inductive_closed(family, good)) by {
        assert forall|i: I| #[trigger] all_continuations(family, i, good) implies good.contains(i) by {
            if witnessed(eq, family, i) {
                witnessed_unfolding(eq, family, i);
                assert forall|s: S| #[trigger] family(i, s).next.is_some() implies names.contains(family(i, s).next.unwrap()) by {
                    assert(good.contains(family(i, s).next.unwrap()));
                    assert(witnessed(eq, family, family(i, s).next.unwrap()));
                }
                assert(all_continuations(family, i, names));
            }
        }
    }
    assert(good.contains(id));
}

pub proof fn embedding_paper_witness<S>(eq: spec_fn(S, S) -> bool, effect: spec_fn(S) -> f::Tracked<S>)
    requires o::witnessed_effect(eq, effect),
    ensures paper_witnessed(eq, embed(effect), ()),
{
    embedding_witness(eq, effect);
    inductive_constructor(embed(effect), ());
}

#[verifier::reject_recursive_types(S)]
pub struct PartialIteration<S, I> {
    pub state: S,
    pub undo: mediated::PartialMap<S>,
    pub next: Option<I>,
}
pub type PartialFamily<S, I> = spec_fn(I, S) -> Option<PartialIteration<S, I>>;

pub open spec fn optional_eq<S>(eq: spec_fn(S, S) -> bool, a: Option<S>, b: Option<S>) -> bool {
    match (a, b) { (Some(x), Some(y)) => eq(x, y), (None, None) => true, _ => false }
}
pub open spec fn lift_partial<S>(map: mediated::PartialMap<S>, value: Option<S>) -> Option<S> {
    match value { Some(x) => map(x), None => None }
}

/// Failure is observable: `None` is a separate context value. Inverse failure
/// remains `None` as well; it is never replaced by an identity operation.
pub open spec fn encode_partial<S, I>(family: PartialFamily<S, I>) -> q::IteratorFamily<Option<S>, I> {
    |id: I, input: Option<S>| match input {
        None => q::Iteration { state: None, undo: |s: Option<S>| s, next: None },
        Some(s) => match family(id, s) {
            None => q::Iteration { state: None, undo: |s: Option<S>| s, next: None },
            Some(y) => q::Iteration { state: Some(y.state), undo: |s: Option<S>| lift_partial(y.undo, s), next: y.next },
        },
    }
}

pub proof fn partial_inverse_encoding<S>(eq: spec_fn(S, S) -> bool, a: mediated::PartialMap<S>, b: mediated::PartialMap<S>)
    requires mediated::partial_related(eq, a, b),
    ensures o::related_maps(|x: Option<S>, y: Option<S>| optional_eq(eq, x, y),
        |x: Option<S>| lift_partial(a, x), |x: Option<S>| lift_partial(b, x)),
{
    assert forall|x: Option<S>, y: Option<S>| optional_eq(eq, x, y) implies
        #[trigger] optional_eq(eq, lift_partial(a, x), lift_partial(b, y)) by {
        match (x, y) { (Some(u), Some(v)) => { assert(a(u).is_some() == b(v).is_some()); }, _ => { } }
    }
}

pub open spec fn partial_respects<S, I>(eq: spec_fn(S, S) -> bool, family: PartialFamily<S, I>, id: I) -> bool {
    forall|a: S, b: S| #![trigger family(id, a), family(id, b)] eq(a, b) ==> {
        &&& family(id, a).is_some() == family(id, b).is_some()
        &&& (family(id, a).is_some() ==> {
            let x = family(id, a).unwrap(); let y = family(id, b).unwrap();
            &&& eq(x.state, y.state)
            &&& mediated::partial_related(eq, x.undo, y.undo)
            &&& x.next == y.next
        })
    }
}

pub open spec fn partial_witness_closed<S, I>(eq: spec_fn(S, S) -> bool, family: PartialFamily<S, I>, names: ISet<I>) -> bool {
    forall|id: I| names.contains(id) ==> {
        &&& q::iterator_related(|a: Option<S>, b: Option<S>| optional_eq(eq, a, b), encode_partial(family), id, id)
        &&& forall|s: S| #[trigger] family(id, s).is_some() ==> {
            let yielded = family(id, s).unwrap();
            &&& (yielded.undo)(yielded.state).is_some()
            &&& eq((yielded.undo)(yielded.state).unwrap(), s)
            &&& (yielded.next.is_some() ==> names.contains(yielded.next.unwrap()))
        }
    }
}

/// Definition 37 for partial stages: definedness is observed by the same
/// greatest bisimulation as total iterators, while recovery is required at
/// every actual successful yield. No claim is made about recovery of failure.
pub open spec fn partial_witnessed<S, I>(eq: spec_fn(S, S) -> bool, family: PartialFamily<S, I>, id: I) -> bool {
    exists|names: ISet<I>| names.contains(id) && partial_witness_closed(eq, family, names)
}

pub proof fn partial_family_coinduction<S, I>(eq: spec_fn(S, S) -> bool, family: PartialFamily<S, I>, names: ISet<I>, id: I)
    requires names.contains(id),
        forall|i: I| names.contains(i) ==> partial_respects(eq, family, i),
        forall|i: I, s: S| #![trigger family(i, s)] names.contains(i) && family(i, s).is_some() ==> {
            let yielded = family(i, s).unwrap();
            &&& (yielded.undo)(yielded.state).is_some()
            &&& eq((yielded.undo)(yielded.state).unwrap(), s)
            &&& (yielded.next.is_some() ==> names.contains(yielded.next.unwrap()))
        },
    ensures partial_witnessed(eq, family, id),
        q::iterator_related(|a: Option<S>, b: Option<S>| optional_eq(eq, a, b), encode_partial(family), id, id),
{
    let relation = |i: I, j: I| i == j && names.contains(i);
    let base = |a: Option<S>, b: Option<S>| optional_eq(eq, a, b);
    let encoded = encode_partial(family);
    assert(q::bisimulation(base, encoded, relation)) by {
        assert forall|i: I, j: I, a: Option<S>, b: Option<S>| #![trigger encoded(i, a), encoded(j, b)]
            relation(i, j) && base(a, b) implies {
                let x = encoded(i, a); let y = encoded(j, b);
                &&& base(x.state, y.state)
                &&& o::related_maps(base, x.undo, y.undo)
                &&& q::continuation(relation, x.next, y.next)
            } by {
            match (a, b) {
                (Some(u), Some(v)) => {
                    assert(family(i, u).is_some() == family(i, v).is_some());
                    if family(i, u).is_some() {
                        let x = family(i, u).unwrap(); let y = family(i, v).unwrap();
                        partial_inverse_encoding(eq, x.undo, y.undo);
                        if x.next.is_some() { assert(names.contains(x.next.unwrap())); }
                    }
                },
                _ => { },
            }
        }
    }
    assert forall|i: I| names.contains(i) implies
        q::iterator_related(base, encoded, i, i) by { assert(relation(i, i)); }
    assert(partial_witness_closed(eq, family, names));
}

pub open spec fn mediated_family<K, V, O>(program: mediated::Program<K, V, O>) -> PartialFamily<IMap<K, V>, nat> {
    |id: nat, input: IMap<K, V>| match mediated::run(program(id), input) {
        None => None,
        Some(y) => Some(PartialIteration { state: y.state, undo: y.undo, next: y.next }),
    }
}

/// Lemma 39's recursive conclusion is now a member of the generic witnessed
/// iterator family, rather than only a one-step respect predicate. Grammar
/// induction supplies the local facts; greatest bisimulation closes them over
/// all continuations, including outcome trees with no common finite height.
pub proof fn grammar_witnessed<K, V, O>(eq: spec_fn(K, V, V) -> bool, program: mediated::Program<K, V, O>,
    allowed: mediated::Allowed<K, V, O>, declared: ISet<K>, provisions: ISet<K>, observed: ISet<K>, id: nat)
    requires mediated::primitive_theory(eq, allowed), provisions.subset_of(declared),
        mediated::member(program, allowed, declared, provisions, id), mediated::covered(program, observed, id),
    ensures partial_witnessed(|a: IMap<K, V>, b: IMap<K, V>| o::context_equal(eq, observed, a, b), mediated_family(program), id),
        q::iterator_related(|a: Option<IMap<K, V>>, b: Option<IMap<K, V>>|
            optional_eq(|s: IMap<K, V>, t: IMap<K, V>| o::context_equal(eq, observed, s, t), a, b),
            encode_partial(mediated_family(program)), id, id),
{
    let ctx = |a: IMap<K, V>, b: IMap<K, V>| o::context_equal(eq, observed, a, b);
    let family = mediated_family(program);
    let names = ISet::new(|i: nat| mediated::member(program, allowed, declared, provisions, i)
        && mediated::covered(program, observed, i));
    assert forall|k: K| observed.contains(k) implies calculus::equivalence(|a: V, b: V| eq(k, a, b)) by {
        assert(mediated::key_equivalence(eq, k));
    }
    o::context_equivalence(eq, observed);
    assert forall|i: nat| names.contains(i) implies partial_respects(ctx, family, i) by {
        mediated::restricted_admissibility(eq, program, allowed, declared, provisions, observed, i);
    }
    assert forall|i: nat, s: IMap<K, V>| #![trigger family(i, s)] names.contains(i) && family(i, s).is_some() implies {
        let yielded = family(i, s).unwrap();
        &&& (yielded.undo)(yielded.state).is_some()
        &&& ctx((yielded.undo)(yielded.state).unwrap(), s)
        &&& (yielded.next.is_some() ==> names.contains(yielded.next.unwrap()))
    } by {
        mediated::restricted_admissibility(eq, program, allowed, declared, provisions, observed, i);
        assert(ctx(s, s));
        match program(i) {
            mediated::Node::Unit => { },
            mediated::Node::Operation { key, operation, select } => {
                assert(operation(s[key]).is_some());
                if family(i, s).unwrap().next.is_some() {
                    assert(names.contains(select(operation(s[key]).unwrap().outcome).unwrap()));
                }
            },
            mediated::Node::Provision { next, .. } => { if next.is_some() { assert(names.contains(next.unwrap())); } },
        }
    }
    partial_family_coinduction(ctx, family, names, id);
}

pub proof fn grammar_inductive<K, V, O>(program: mediated::Program<K, V, O>,
    allowed: mediated::Allowed<K, V, O>, declared: ISet<K>, provisions: ISet<K>, id: nat)
    requires mediated::member(program, allowed, declared, provisions, id),
    ensures inductive_member(encode_partial(mediated_family(program)), id),
{
    let encoded = encode_partial(mediated_family(program));
    let good = ISet::new(|i: nat| inductive_member(encoded, i));
    assert(mediated::closed(program, allowed, declared, provisions, good)) by {
        assert forall|i: nat| mediated::permitted(allowed, declared, provisions, program(i))
            && mediated::continuations(program(i), good) implies good.contains(i) by {
            assert forall|s: Option<IMap<K, V>>| #[trigger] encoded(i, s).next.is_some()
                implies inductive_members(encoded).contains(encoded(i, s).next.unwrap()) by {
                assert(s.is_some());
                match program(i) {
                    mediated::Node::Unit => { },
                    mediated::Node::Operation { key, operation, select } => {
                        let input = s.unwrap();
                        assert(operation(input[key]).is_some());
                        assert(select(operation(input[key]).unwrap().outcome).is_some());
                        assert(good.contains(select(operation(input[key]).unwrap().outcome).unwrap()));
                    },
                    mediated::Node::Provision { next, .. } => { assert(good.contains(next.unwrap())); },
                }
            }
            inductive_constructor(encoded, i);
        }
    }
    assert(good.contains(id));
}

pub open spec fn paper_partial_witnessed<S, I>(eq: spec_fn(S, S) -> bool, family: PartialFamily<S, I>, id: I) -> bool {
    inductive_member(encode_partial(family), id) && partial_witnessed(eq, family, id)
}

/// Both halves of the printed witnessed iterator type are obtained: the
/// grammar's least construction yields inductive membership, while primitive
/// respect yields greatest observational bisimulation and recursive witnesses.
pub proof fn grammar_paper_witnessed<K, V, O>(eq: spec_fn(K, V, V) -> bool, program: mediated::Program<K, V, O>,
    allowed: mediated::Allowed<K, V, O>, declared: ISet<K>, provisions: ISet<K>, observed: ISet<K>, id: nat)
    requires mediated::primitive_theory(eq, allowed), provisions.subset_of(declared),
        mediated::member(program, allowed, declared, provisions, id), mediated::covered(program, observed, id),
    ensures paper_partial_witnessed(|a: IMap<K, V>, b: IMap<K, V>| o::context_equal(eq, observed, a, b), mediated_family(program), id),
{
    grammar_inductive(program, allowed, declared, provisions, id);
    grammar_witnessed(eq, program, allowed, declared, provisions, observed, id);
}

/// The observation relation of an actual typed fiber transported into the
/// shared sum carrier. Values outside that fiber have the same failed decode;
/// every encoded operation rejects them, preserving its partial domain.
pub open spec fn codec_relation<K, U, T>(c: crate::contexts::FiberCodec<K, U, T>,
    eq: spec_fn(T, T) -> bool, a: U, b: U) -> bool
{
    optional_eq(eq, (c.decode)(a), (c.decode)(b))
}

pub proof fn codec_equivalence<K, U, T>(c: crate::contexts::FiberCodec<K, U, T>, eq: spec_fn(T, T) -> bool)
    requires calculus::equivalence(eq),
    ensures calculus::equivalence(|a: U, b: U| codec_relation(c, eq, a, b)),
{
    assert forall|a: U| #[trigger] codec_relation(c, eq, a, a) by {
        if (c.decode)(a).is_some() { assert(eq((c.decode)(a).unwrap(), (c.decode)(a).unwrap())); }
    }
    assert forall|a: U, b: U| codec_relation(c, eq, a, b) implies #[trigger] codec_relation(c, eq, b, a) by {
        if (c.decode)(a).is_some() { assert(eq((c.decode)(b).unwrap(), (c.decode)(a).unwrap())); }
    }
    assert forall|a: U, b: U, d: U| #[trigger] codec_relation(c, eq, a, b) && #[trigger] codec_relation(c, eq, b, d)
        implies codec_relation(c, eq, a, d) by {
        if (c.decode)(a).is_some() { assert(eq((c.decode)(a).unwrap(), (c.decode)(d).unwrap())); }
    }
}

pub proof fn codec_inverse_respects<K, U, T>(types: crate::contexts::Family<K, U>,
    c: crate::contexts::FiberCodec<K, U, T>, eq: spec_fn(T, T) -> bool,
    left: mediated::PartialMap<T>, right: mediated::PartialMap<T>)
    requires crate::contexts::codec(types, c), mediated::partial_related(eq, left, right),
    ensures mediated::partial_related(|a: U, b: U| codec_relation(c, eq, a, b),
        crate::contexts::encoded_inverse(c, left), crate::contexts::encoded_inverse(c, right)),
{
    let a = crate::contexts::encoded_inverse(c, left); let b = crate::contexts::encoded_inverse(c, right);
    assert forall|u: U, v: U| #![trigger a(u), b(v)] codec_relation(c, eq, u, v) implies {
        &&& a(u).is_some() == b(v).is_some()
        &&& (a(u).is_some() ==> codec_relation(c, eq, a(u).unwrap(), b(v).unwrap()))
    } by {
        if (c.decode)(u).is_some() {
            let x = (c.decode)(u).unwrap(); let y = (c.decode)(v).unwrap();
            assert(eq(x, y)); assert(left(x).is_some() == right(y).is_some());
            if left(x).is_some() {
                assert((c.decode)((c.encode)(left(x).unwrap())) == Some(left(x).unwrap()));
                assert((c.decode)((c.encode)(right(y).unwrap())) == Some(right(y).unwrap()));
            }
        }
    }
}

/// Heterogeneous key-specific value types are transported by their actual
/// bijections. Observational respect, exact recovery, inverse definedness and
/// the raw outcome survive this encoding, allowing the encoded operation to
/// enter the mediated grammar's primitive theory without an equality-only
/// restriction on the original value type.
pub proof fn codec_operation_admissible<K, U, T, O>(types: crate::contexts::Family<K, U>,
    c: crate::contexts::FiberCodec<K, U, T>, eq: spec_fn(T, T) -> bool, operation: mediated::Operation<T, O>)
    requires crate::contexts::codec(types, c), mediated::operation_admissible(eq, operation),
    ensures mediated::operation_admissible(|a: U, b: U| codec_relation(c, eq, a, b),
        crate::contexts::encoded_operation(c, operation)),
{
    let encoded = crate::contexts::encoded_operation(c, operation);
    assert(mediated::operation_admissible(|a: T, b: T| a == b, operation));
    crate::contexts::encoded_operation_witness(types, c, operation);
    assert forall|u: U, v: U| #![trigger encoded(u), encoded(v)] codec_relation(c, eq, u, v) implies {
        &&& encoded(u).is_some() == encoded(v).is_some()
        &&& (encoded(u).is_some() ==> {
            let x = encoded(u).unwrap(); let y = encoded(v).unwrap();
            &&& codec_relation(c, eq, x.value, y.value) && x.outcome == y.outcome
            &&& mediated::partial_related(|a: U, b: U| codec_relation(c, eq, a, b), x.undo, y.undo)
        })
    } by {
        if (c.decode)(u).is_some() {
            let a = (c.decode)(u).unwrap(); let b = (c.decode)(v).unwrap();
            assert(eq(a, b)); assert(operation(a).is_some() == operation(b).is_some());
            if operation(a).is_some() {
                let x = operation(a).unwrap(); let y = operation(b).unwrap();
                assert((c.decode)((c.encode)(x.value)) == Some(x.value));
                assert((c.decode)((c.encode)(y.value)) == Some(y.value));
                codec_inverse_respects(types, c, eq, x.undo, y.undo);
            }
        }
    }
}

pub enum UnboundedIndex { Start, Countdown(nat) }
pub open spec fn unbounded_family(id: UnboundedIndex, state: nat) -> q::Iteration<nat, UnboundedIndex> {
    let next = match id {
        UnboundedIndex::Start => Some(UnboundedIndex::Countdown(state)),
        UnboundedIndex::Countdown(n) => if n == 0 { None } else { Some(UnboundedIndex::Countdown((n - 1) as nat)) },
    };
    q::Iteration { state, undo: |s: nat| s, next }
}
pub proof fn countdown_inductive(n: nat)
    ensures inductive_member(|i, s| unbounded_family(i, s), UnboundedIndex::Countdown(n)),
    decreases n,
{
    if n > 0 { countdown_inductive((n - 1) as nat); }
    inductive_constructor(|i, s| unbounded_family(i, s), UnboundedIndex::Countdown(n));
}

pub proof fn countdown_run(n: nat, fuel: nat, initial: f::Tracked<nat>)
    ensures run(|i, s| unbounded_family(i, s), Some(UnboundedIndex::Countdown(n)), fuel, initial).next
        == if fuel > n { None } else { Some(UnboundedIndex::Countdown((n - fuel) as nat)) },
    decreases fuel,
{
    if fuel > 0 {
        if n > 0 {
            let yielded = unbounded_family(UnboundedIndex::Countdown(n), initial.value);
            let current = f::Tracked { value: yielded.state, undo: f::compose(initial.undo, yielded.undo) };
            countdown_run((n - 1) as nat, (fuel - 1) as nat, current);
        } else { reveal_with_fuel(run, 2); }
    }
}

/// A witnessed member of the least recursive type can require arbitrarily
/// many steps across its inputs. This machine-checked example prevents the
/// encoding from silently substituting a common finite rank for µ membership.
pub proof fn no_common_height(fuel: nat)
    ensures paper_witnessed(|a: nat, b: nat| a == b, |i, s| unbounded_family(i, s), UnboundedIndex::Start),
        run(|i, s| unbounded_family(i, s), Some(UnboundedIndex::Start), fuel, f::unit(fuel)).next.is_some(),
{
    let family = |i, s| unbounded_family(i, s);
    assert forall|s: nat| #[trigger] family(UnboundedIndex::Start, s).next.is_some()
        implies inductive_members(family).contains(family(UnboundedIndex::Start, s).next.unwrap()) by {
        countdown_inductive(s);
    }
    inductive_constructor(family, UnboundedIndex::Start);
    exact_witness_family(family, ISet::full(), UnboundedIndex::Start);
    if fuel > 0 {
        let initial = f::unit(fuel);
        let yielded = family(UnboundedIndex::Start, initial.value);
        let current = f::Tracked { value: yielded.state, undo: f::compose(initial.undo, yielded.undo) };
        countdown_run(fuel, (fuel - 1) as nat, current);
    }
}

} // verus!
