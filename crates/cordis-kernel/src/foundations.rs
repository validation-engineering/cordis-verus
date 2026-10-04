//! Section 3.1: the effect algebra, including state-dependent inverse witnesses.
//! Equalities of maps are stated extensionally at arbitrary arguments; no
//! identity of closures or uniform inverse is assumed for a witnessed effect.
use vstd::prelude::*;

verus! {

#[verifier::reject_recursive_types(S)]
pub struct Tracked<S> { pub value: S, pub undo: spec_fn(S) -> S }

pub open spec fn id<S>(x: S) -> S { x }
pub open spec fn compose<S>(f: spec_fn(S)->S, g: spec_fn(S)->S) -> spec_fn(S)->S {
    |x: S| f(g(x))
}
pub open spec fn maps_equal<S>(f: spec_fn(S)->S, g: spec_fn(S)->S) -> bool {
    forall|x: S| #[trigger] f(x) == g(x)
}
pub open spec fn tracked_equal<S>(a: Tracked<S>, b: Tracked<S>) -> bool {
    a.value == b.value && maps_equal(a.undo,b.undo)
}
pub open spec fn track<S>(f: spec_fn(S)->S,g: spec_fn(S)->S,a:Tracked<S>) -> Tracked<S> {
    Tracked { value:f(a.value), undo:compose(a.undo,g) }
}
pub open spec fn recover<S>(a:Tracked<S>) -> Tracked<S> {
    Tracked { value:(a.undo)(a.value),undo:|x:S| x }
}
pub open spec fn unit<S>(x:S) -> Tracked<S> { Tracked {value:x,undo:|x:S| x} }
pub open spec fn diamond<S>(f:spec_fn(S)->Tracked<S>,g:spec_fn(S)->Tracked<S>,x:S) -> Tracked<S> {
    let first=g(x);let second=f(first.value);
    Tracked {value:second.value,undo:compose(first.undo,second.undo)}
}
pub open spec fn witnessed<S>(e:spec_fn(S)->Tracked<S>) -> bool {
    forall|x:S| #[trigger] (e(x).undo)(e(x).value) == x
}
pub open spec fn uniform<S>(f:spec_fn(S)->S,g:spec_fn(S)->S,x:S) -> Tracked<S> {
    Tracked {value:f(x),undo:g}
}
pub open spec fn effect<S>(e:spec_fn(S)->Tracked<S>,a:Tracked<S>) -> Tracked<Tracked<S>> {
    let out=e(a.value);
    Tracked { value:Tracked {value:out.value,undo:compose(a.undo,out.undo)},
        undo:|b:Tracked<S>| track(out.undo,|x:S| e(x).value,b) }
}
pub open spec fn lifted_equal<S>(a:Tracked<Tracked<S>>,b:Tracked<Tracked<S>>) -> bool {
    tracked_equal(a.value,b.value)
        && forall|x:Tracked<S>| #[trigger] tracked_equal((a.undo)(x),(b.undo)(x))
}

/// Theorem 4: tracking has precisely the original forward projection.
pub proof fn track_projection<S>(f:spec_fn(S)->S,g:spec_fn(S)->S,a:Tracked<S>)
    ensures track(f,g,a).value == f(a.value),
{ }

/// Definition 1 and Theorem 5: identity and twisted composition.
pub proof fn track_monoid<S>(f1:spec_fn(S)->S,g1:spec_fn(S)->S,
    f2:spec_fn(S)->S,g2:spec_fn(S)->S,a:Tracked<S>)
    ensures tracked_equal(track(|x:S|x,|x:S|x,a),a),
        tracked_equal(track(f1,g1,track(f2,g2,a)),track(compose(f1,f2),compose(g2,g1),a)),
{ }

/// Theorem 7 uses only the inverse witness at the actual input state.
pub proof fn tracking_preserves_recovery<S>(f:spec_fn(S)->S,g:spec_fn(S)->S,a:Tracked<S>)
    requires g(f(a.value)) == a.value,
    ensures tracked_equal(recover(track(f,g,a)),recover(a)),
{ }

/// Theorem 10(1), with arbitrary state-dependent yielded inverses.
pub proof fn effect_monoid<S>(f:spec_fn(S)->Tracked<S>,g:spec_fn(S)->Tracked<S>,
    h:spec_fn(S)->Tracked<S>,x:S)
    ensures tracked_equal(diamond(f,|x:S|unit(x),x),f(x)),
        tracked_equal(diamond(|x:S|unit(x),f,x),f(x)),
        tracked_equal(diamond(|x:S|diamond(f,g,x),h,x),diamond(f,|x:S|diamond(g,h,x),x)),
{ }

/// Theorem 10(2): uniform pairs embed as a homomorphism.
pub proof fn uniform_homomorphism<S>(f1:spec_fn(S)->S,g1:spec_fn(S)->S,
    f2:spec_fn(S)->S,g2:spec_fn(S)->S,x:S)
    ensures tracked_equal(diamond(|x:S|uniform(f1,g1,x),|x:S|uniform(f2,g2,x),x),
        uniform(compose(f1,f2),compose(g2,g1),x)),
{ }

/// Theorem 11: witness closure, including the unit and uniform left inverse.
pub proof fn witness_composition<S>(f:spec_fn(S)->Tracked<S>,g:spec_fn(S)->Tracked<S>)
    requires witnessed(f),witnessed(g),
    ensures witnessed(|x:S|diamond(f,g,x)),witnessed(|x:S|unit(x)),
{
    assert forall|x:S| (diamond(f,g,x).undo)(diamond(f,g,x).value) == x by {
        assert((f(g(x).value).undo)(f(g(x).value).value) == g(x).value);
        assert((g(x).undo)(g(x).value) == x);
    }
}
pub proof fn uniform_witness<S>(f:spec_fn(S)->S,g:spec_fn(S)->S)
    requires forall|x:S| #[trigger] g(f(x)) == x,
    ensures witnessed(|x:S|uniform(f,g,x)),
{ }

/// Theorem 13: lifting effect composition preserves the returned lifted inverse,
/// not just the current value. The equality is pointwise at every lifted input.
pub proof fn effect_homomorphism<S>(f:spec_fn(S)->Tracked<S>,g:spec_fn(S)->Tracked<S>,a:Tracked<S>)
    ensures lifted_equal(diamond(|x:Tracked<S>|effect(f,x),|x:Tracked<S>|effect(g,x),a),
        effect(|x:S|diamond(f,g,x),a)),
{
    let left=diamond(|x:Tracked<S>|effect(f,x),|x:Tracked<S>|effect(g,x),a);
    let right=effect(|x:S|diamond(f,g,x),a);
    assert forall|x:Tracked<S>| #[trigger] tracked_equal(
        (left.undo)(x),(right.undo)(x)) by { }
}

/// Theorem 14: both directions project to the underlying effect directions.
pub proof fn effect_projection<S>(e:spec_fn(S)->Tracked<S>,a:Tracked<S>,b:Tracked<S>)
    ensures effect(e,a).value.value == e(a.value).value,
        ((effect(e,a).undo)(b)).value == (e(a.value).undo)(b.value),
{ }

/// Theorem 15: value recovery and soundness hold without a global inverse.
/// Restoring the entire accumulator for every accumulator is equivalent to a
/// uniform inverse at this actual yield, which is the stronger statement.
pub proof fn lifted_recovery<S>(e:spec_fn(S)->Tracked<S>,x:S,phi:spec_fn(S)->S)
    requires witnessed(e),
    ensures {
        let a=Tracked {value:x,undo:phi};let lifted=effect(e,a);let back=(lifted.undo)(lifted.value);
        &&& back.value == x
        &&& maps_equal(back.undo,compose(compose(phi,e(x).undo),|y:S|e(y).value))
        &&& (back.undo)(back.value) == phi(x)
        &&& tracked_equal(recover(back),recover(a))
    },
{ assert((e(x).undo)(e(x).value) == x); }

pub open spec fn full_recovery<S>(e:spec_fn(S)->Tracked<S>,x:S,phi:spec_fn(S)->S) -> bool {
    let a=Tracked {value:x,undo:phi};let lifted=effect(e,a);
    tracked_equal((lifted.undo)(lifted.value),a)
}
pub proof fn full_accumulator_recovery_iff<S>(e:spec_fn(S)->Tracked<S>,x:S)
    requires witnessed(e),
    ensures (forall|phi:spec_fn(S)->S| #[trigger] full_recovery(e,x,phi))
        == (forall|y:S| #[trigger] (e(x).undo)(e(y).value) == y),
{
    if forall|y:S| #[trigger] (e(x).undo)(e(y).value) == y {
        assert forall|phi:spec_fn(S)->S| #[trigger] full_recovery(e,x,phi)
            by { assert((e(x).undo)(e(x).value) == x); }
    } else {
        let phi=|y:S|y;
        let a=Tracked {value:x,undo:phi};let lifted=effect(e,a);
        let y=choose|y:S| #[trigger] (e(x).undo)(e(y).value) != y;
        assert((((lifted.undo)(lifted.value)).undo)(y) != phi(y));
        assert(!tracked_equal((lifted.undo)(lifted.value),a));
        assert(!full_recovery(e,x,phi));
    }
}

/// Replay actual dynamically yielded witnesses: unlike recover_sequence this
/// needs inverse correctness only at the states where each effect was invoked.
pub open spec fn apply_effects<S>(es:Seq<spec_fn(S)->Tracked<S>>,a:Tracked<S>) -> Tracked<S>
    decreases es.len(),
{
    if es.len()==0 {a} else {
        let before=apply_effects(es.drop_last(),a);let out=(es.last())(before.value);
        Tracked {value:out.value,undo:compose(before.undo,out.undo)}
    }
}
pub proof fn dynamic_sequence_sound<S>(es:Seq<spec_fn(S)->Tracked<S>>,a:Tracked<S>)
    requires forall|i:int| 0 <= i < es.len() ==> witnessed(es[i]),
    ensures tracked_equal(recover(apply_effects(es,a)),recover(a)),
    decreases es.len(),
{
    if es.len()>0 {
        dynamic_sequence_sound(es.drop_last(),a);
        let before=apply_effects(es.drop_last(),a);let e=es.last();
        assert(witnessed(e));assert((e(before.value).undo)(e(before.value).value)==before.value);
    }
}

/// Revert the originally yielded effects down to a chosen prefix. Each inverse
/// retains the forward map captured by its lifted effect, even if the current
/// accumulator differs from the accumulator at the original application.
pub open spec fn revert_suffix<S>(es:Seq<spec_fn(S)->Tracked<S>>,initial:Tracked<S>,
    keep:nat,current:Tracked<S>) -> Tracked<S>
    recommends keep<=es.len(),
    decreases es.len(),
{
    if es.len()<=keep {current} else {
        let before=apply_effects(es.drop_last(),initial);let e=es.last();
        let next=track(e(before.value).undo,|s:S|e(s).value,current);
        revert_suffix(es.drop_last(),initial,keep,next)
    }
}
pub proof fn revert_prefix_sound<S>(es:Seq<spec_fn(S)->Tracked<S>>,initial:Tracked<S>,
    keep:nat,current:Tracked<S>)
    requires keep<=es.len(),current.value==apply_effects(es,initial).value,
        forall|i:int| 0<=i<es.len() ==> witnessed(es[i]),
    ensures revert_suffix(es,initial,keep,current).value==apply_effects(es.subrange(0,keep as int),initial).value,
        (revert_suffix(es,initial,keep,current).undo)(revert_suffix(es,initial,keep,current).value)
            ==(current.undo)(current.value),
    decreases es.len(),
{
    if es.len()==keep {assert(es.subrange(0,keep as int) =~= es);}
    else {
        let before=apply_effects(es.drop_last(),initial);let e=es.last();
        let out=e(before.value);let next=track(out.undo,|s:S|e(s).value,current);
        assert(witnessed(e));assert((out.undo)(out.value)==before.value);
        assert(next.value==before.value);
        assert((next.undo)(next.value)==(current.undo)(current.value));
        revert_prefix_sound(es.drop_last(),initial,keep,next);
        assert(es.drop_last().subrange(0,keep as int) =~= es.subrange(0,keep as int));
    }
}
/// Theorem 16: every partial reverse run recovers that precise forward prefix,
/// and every such intermediate state keeps the original recovery target.
pub proof fn local_temporal_sequence<S>(es:Seq<spec_fn(S)->Tracked<S>>,initial:Tracked<S>,keep:nat)
    requires keep<=es.len(),forall|i:int| 0<=i<es.len() ==> witnessed(es[i]),
    ensures {
        let restored=revert_suffix(es,initial,keep,apply_effects(es,initial));
        &&& restored.value==apply_effects(es.subrange(0,keep as int),initial).value
        &&& (restored.undo)(restored.value)==(initial.undo)(initial.value)
    },
{
    dynamic_sequence_sound(es,initial);
    revert_prefix_sound(es,initial,keep,apply_effects(es,initial));
}
} // verus!
