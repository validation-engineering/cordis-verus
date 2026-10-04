//! Parametric effect laws. Preconditions are the paper's explicit witness and
//! independence obligations, not assumptions about arbitrary Rust callbacks.
//! `resources` supplies a concrete executable forward/inverse implementation.
use vstd::prelude::*;
verus! {
pub open spec fn run<S>(fs: Seq<spec_fn(S) -> S>, s: S) -> S
    decreases fs.len(),
{
    if fs.len() == 0 { s } else { (fs.last())(run(fs.drop_last(), s)) }
}
pub open spec fn unwind<S>(gs: Seq<spec_fn(S) -> S>, s: S) -> S
    decreases gs.len(),
{
    if gs.len() == 0 { s } else { unwind(gs.drop_last(), (gs.last())(s)) }
}
pub open spec fn respects<S>(f: spec_fn(S) -> S, eq: spec_fn(S, S) -> bool) -> bool {
    forall|a: S, b: S| eq(a, b) ==> #[trigger] eq(f(a), f(b))
}
pub open spec fn equivalence<S>(eq: spec_fn(S, S) -> bool) -> bool {
    &&& forall|a: S| #[trigger] eq(a, a)
    &&& forall|a: S, b: S| #[trigger] eq(a, b) ==> eq(b, a)
    &&& forall|a: S, b: S, c: S| #[trigger] eq(a, b) && #[trigger] eq(b, c) ==> eq(a, c)
}
/// Composition of respecting inverses respects observational equivalence.
pub proof fn unwind_respects<S>(gs: Seq<spec_fn(S) -> S>, eq: spec_fn(S, S) -> bool, a: S, b: S)
    requires eq(a, b), forall|i: int| 0 <= i < gs.len() ==> respects(gs[i], eq),
    ensures eq(unwind(gs, a), unwind(gs, b)),
    decreases gs.len(),
{
    if gs.len() > 0 {
        let g = gs.last();
        assert(respects(g, eq));
        unwind_respects(gs.drop_last(), eq, g(a), g(b));
    }
}
/// Local temporal recovery for a finite effect iterator, up to observations.
/// The accumulator runs the returned inverses in the opposite order.
pub proof fn recover_sequence<S>(fs: Seq<spec_fn(S) -> S>, gs: Seq<spec_fn(S) -> S>, eq: spec_fn(S, S) -> bool, s: S)
    requires fs.len() == gs.len(), equivalence(eq),
        forall|i: int, state: S| 0 <= i < fs.len() ==> #[trigger] eq((gs[i])((fs[i])(state)), state),
        forall|i: int| 0 <= i < gs.len() ==> respects(gs[i], eq),
    ensures eq(unwind(gs, run(fs, s)), s),
    decreases fs.len(),
{
    if fs.len() > 0 {
        let prior = run(fs.drop_last(), s);
        let f = fs.last(); let g = gs.last();
        assert(eq(g(f(prior)), prior));
        unwind_respects(gs.drop_last(), eq, g(f(prior)), prior);
        recover_sequence(fs.drop_last(), gs.drop_last(), eq, s);
    }
}
/// Foreign steps may interleave if they commute with an accumulated inverse.
pub proof fn inverse_commutes_with_trace<S>(inverse: spec_fn(S) -> S, foreign: Seq<spec_fn(S) -> S>, s: S)
    requires forall|i: int, state: S| 0 <= i < foreign.len()
        ==> #[trigger] inverse((foreign[i])(state)) == (foreign[i])(inverse(state)),
    ensures inverse(run(foreign, s)) == run(foreign, inverse(s)),
    decreases foreign.len(),
{
    if foreign.len() > 0 {
        inverse_commutes_with_trace(inverse, foreign.drop_last(), s);
    }
}
/// Delete a closed episode without deleting independent foreign work.
pub proof fn recovery_with_interference<S>(forward: spec_fn(S) -> S, inverse: spec_fn(S) -> S, foreign: Seq<spec_fn(S) -> S>, s: S)
    requires inverse(forward(s)) == s,
        forall|i: int, state: S| 0 <= i < foreign.len()
            ==> #[trigger] inverse((foreign[i])(state)) == (foreign[i])(inverse(state)),
    ensures inverse(run(foreign, forward(s))) == run(foreign, s),
{
    inverse_commutes_with_trace(inverse, foreign, forward(s));
}
/// Two independent finite effect groups have the same result in either order.
pub proof fn independent_groups<S>(left: Seq<spec_fn(S) -> S>, right: Seq<spec_fn(S) -> S>, s: S)
    requires forall|i: int, j: int, state: S| 0 <= i < left.len() && 0 <= j < right.len()
        ==> #[trigger] (left[i])((right[j])(state)) == (right[j])((left[i])(state)),
    ensures run(left, run(right, s)) == run(right, run(left, s)),
    decreases left.len(),
{
    if left.len() > 0 {
        independent_groups(left.drop_last(), right, s);
        inverse_commutes_with_trace(left.last(), right, run(left.drop_last(), s));
    }
}

pub open spec fn interleave<S>(local: Seq<spec_fn(S) -> S>, foreign: Seq<spec_fn(S) -> S>, s: S) -> S
    recommends local.len() == foreign.len(),
    decreases local.len(),
{
    if local.len() == 0 { s } else {
        (foreign.last())((local.last())(interleave(local.drop_last(), foreign.drop_last(), s)))
    }
}
pub proof fn unwind_commutes_with_step<S>(inverses: Seq<spec_fn(S) -> S>, foreign: spec_fn(S) -> S, s: S)
    requires forall|i: int, state: S| 0 <= i < inverses.len()
        ==> #[trigger] (inverses[i])(foreign(state)) == foreign((inverses[i])(state)),
    ensures unwind(inverses, foreign(s)) == foreign(unwind(inverses, s)),
    decreases inverses.len(),
{
    if inverses.len() > 0 {
        unwind_commutes_with_step(inverses.drop_last(), foreign, (inverses.last())(s));
    }
}
/// Remove a complete local episode from an interleaved trace, retaining every
/// foreign step in its original order. A foreign step can itself be a batch.
/// Local inverses must be witnesses and commute with each foreign step; these
/// obligations are not supplied for arbitrary host callbacks.
pub proof fn recover_interleaved<S>(local: Seq<spec_fn(S) -> S>, inverses: Seq<spec_fn(S) -> S>, foreign: Seq<spec_fn(S) -> S>, s: S)
    requires local.len() == inverses.len(), local.len() == foreign.len(),
        forall|i: int, state: S| 0 <= i < local.len() ==> #[trigger] (inverses[i])((local[i])(state)) == state,
        forall|i: int, j: int, state: S| 0 <= i < inverses.len() && 0 <= j < foreign.len()
            ==> #[trigger] (inverses[i])((foreign[j])(state)) == (foreign[j])((inverses[i])(state)),
    ensures unwind(inverses, interleave(local, foreign, s)) == run(foreign, s),
    decreases local.len(),
{
    if local.len() > 0 {
        let prior = interleave(local.drop_last(), foreign.drop_last(), s);
        let f = local.last(); let g = inverses.last(); let h = foreign.last();
        assert(g(h(f(prior))) == h(prior));
        unwind_commutes_with_step(inverses.drop_last(), h, prior);
        recover_interleaved(local.drop_last(), inverses.drop_last(), foreign.drop_last(), s);
    }
}
} // verus!
