//! Independence of the actual partial context-mediated grammar.
//!
//! Failure is distinct from an absent binding. Returned inverses retain their
//! domains, and operation outcomes are compared before continuation selection.
//! Equality of values may be observational; the local coeffect witness carries
//! the required commutation and raw-outcome stability.
#[cfg(verus_keep_ghost)]
use crate::mediated::{Node, Operation, PartialMap};
#[cfg(verus_keep_ghost)]
use crate::{calculus, coeffects, mediated, observation};
use vstd::prelude::*;

verus! {

pub open spec fn optional_equal<S>(eq: spec_fn(S, S) -> bool, a: Option<S>, b: Option<S>) -> bool {
    a.is_some() == b.is_some() && (a.is_some() ==> eq(a.unwrap(), b.unwrap()))
}

pub open spec fn compose<S>(f: PartialMap<S>, g: PartialMap<S>) -> PartialMap<S> {
    |s: S| match g(s) { Some(x) => f(x), None => None }
}

pub open spec fn commutes<S>(eq: spec_fn(S, S) -> bool, f: PartialMap<S>, g: PartialMap<S>) -> bool {
    forall|s: S| #[trigger] optional_equal(eq, compose(f, g)(s), compose(g, f)(s))
}

pub open spec fn respects<S>(eq: spec_fn(S, S) -> bool, f: PartialMap<S>) -> bool {
    mediated::partial_related(eq, f, f)
}

pub proof fn optional_transitive<S>(eq: spec_fn(S, S) -> bool, a: Option<S>, b: Option<S>, c: Option<S>)
    requires calculus::equivalence(eq), optional_equal(eq, a, b), optional_equal(eq, b, c),
    ensures optional_equal(eq, a, c),
{ }

pub proof fn optional_symmetric<S>(eq: spec_fn(S, S) -> bool, a: Option<S>, b: Option<S>)
    requires calculus::equivalence(eq), optional_equal(eq, a, b),
    ensures optional_equal(eq, b, a),
{ }

pub proof fn composition_respects<S>(eq: spec_fn(S, S) -> bool, f: PartialMap<S>, g: PartialMap<S>)
    requires respects(eq, f), respects(eq, g),
    ensures respects(eq, compose(f, g)),
{
    let h = compose(f, g);
    assert forall|a: S, b: S| #![trigger h(a), h(b)] eq(a, b) implies {
        &&& h(a).is_some() == h(b).is_some()
        &&& (h(a).is_some() ==> eq(h(a).unwrap(), h(b).unwrap()))
    } by {
        assert(g(a).is_some() == g(b).is_some());
        if g(a).is_some() { assert(eq(g(a).unwrap(), g(b).unwrap())); }
    }
}

/// A word is evaluated in execution order, preserving any failed application.
pub open spec fn run<S>(word: Seq<PartialMap<S>>, state: S) -> Option<S>
    decreases word.len(),
{
    if word.len() == 0 { Some(state) }
    else { match run(word.drop_last(), state) { Some(s) => (word.last())(s), None => None } }
}

pub open spec fn word_in<S>(generators: ISet<PartialMap<S>>, word: Seq<PartialMap<S>>) -> bool {
    forall|i: int| 0 <= i < word.len() ==> generators.contains(#[trigger] word[i])
}

pub open spec fn generated<S>(generators: ISet<PartialMap<S>>, f: PartialMap<S>) -> bool {
    exists|word: Seq<PartialMap<S>>| word_in(generators, word) && f == (|s: S| run(word, s))
}

pub proof fn run_respects<S>(eq: spec_fn(S, S) -> bool, word: Seq<PartialMap<S>>)
    requires calculus::equivalence(eq),
        forall|i: int| 0 <= i < word.len() ==> respects(eq, #[trigger] word[i]),
    ensures respects(eq, |s: S| run(word, s)),
    decreases word.len(),
{
    if word.len() > 0 {
        run_respects(eq, word.drop_last());
        composition_respects(eq, word.last(), |s: S| run(word.drop_last(), s));
        assert((|s: S| run(word, s)) =~= compose(word.last(), |s: S| run(word.drop_last(), s)));
    }
}

/// Commutation is stable under composition when maps respect observation.
pub proof fn commute_composition<S>(eq: spec_fn(S, S) -> bool, f: PartialMap<S>, g: PartialMap<S>, h: PartialMap<S>)
    requires calculus::equivalence(eq), respects(eq, g),
        commutes(eq, f, g), commutes(eq, f, h),
    ensures commutes(eq, f, compose(g, h)),
{
    assert forall|s: S| #[trigger] optional_equal(eq, compose(f, compose(g, h))(s), compose(compose(g, h), f)(s)) by {
        let fh = compose(f, h)(s); let hf = compose(h, f)(s);
        assert(optional_equal(eq, fh, hf));
        let middle = compose(g, compose(f, h))(s);
        assert(optional_equal(eq, compose(f, compose(g, h))(s), middle)) by {
            if h(s).is_some() {
                assert(optional_equal(eq, compose(f, g)(h(s).unwrap()), compose(g, f)(h(s).unwrap())));
            }
        }
        assert(optional_equal(eq, middle, compose(compose(g, h), f)(s))) by {
            if fh.is_some() {
                assert(eq(fh.unwrap(), hf.unwrap()));
                assert(g(fh.unwrap()).is_some() == g(hf.unwrap()).is_some());
            }
        }
        optional_transitive(eq, compose(f, compose(g, h))(s), middle, compose(compose(g, h), f)(s));
    }
}

pub open spec fn context_eq<K, V>(eq: spec_fn(K, V, V) -> bool) -> spec_fn(IMap<K, V>, IMap<K, V>) -> bool {
    |a: IMap<K, V>, b: IMap<K, V>| observation::context_equal(eq, ISet::full(), a, b)
}

pub open spec fn forward<K, V, O>(node: Node<K, V, O>) -> PartialMap<IMap<K, V>> {
    |s: IMap<K, V>| match mediated::run(node, s) { Some(y) => Some(y.state), None => None }
}

pub open spec fn outcome<K, V, O>(node: Node<K, V, O>, s: IMap<K, V>) -> Option<O> {
    match node {
        Node::Operation { key, operation, .. } => {
            if s.dom().contains(key) && operation(s[key]).is_some() { Some(operation(s[key]).unwrap().outcome) } else { None }
        },
        _ => None,
    }
}

pub open spec fn generators<K, V, O>(node: Node<K, V, O>) -> ISet<PartialMap<IMap<K, V>>> {
    ISet::new(|f: PartialMap<IMap<K, V>>| f == forward(node)
        || exists|s: IMap<K, V>| #[trigger] mediated::run(node, s).is_some() && mediated::run(node, s).unwrap().undo == f)
}

pub open spec fn stable<K, V, O>(eq: spec_fn(K, V, V) -> bool, node: Node<K, V, O>, g: PartialMap<IMap<K, V>>) -> bool {
    forall|s: IMap<K, V>| #[trigger] g(s).is_some() ==> {
        let a = mediated::run(node, s); let b = mediated::run(node, g(s).unwrap());
        &&& a.is_some() == b.is_some()
        &&& a.is_some() ==> {
            &&& mediated::partial_related(context_eq(eq), a.unwrap().undo, b.unwrap().undo)
            &&& a.unwrap().next == b.unwrap().next
            &&& outcome(node, s) == outcome(node, g(s).unwrap())
        }
    }
}

pub open spec fn independent<K, V, O, P>(eq: spec_fn(K, V, V) -> bool, left: Node<K, V, O>, right: Node<K, V, P>) -> bool {
    &&& forall|f: PartialMap<IMap<K, V>>, g: PartialMap<IMap<K, V>>| generators(left).contains(f) && generators(right).contains(g)
        ==> #[trigger] commutes(context_eq(eq), f, g)
    &&& forall|g: PartialMap<IMap<K, V>>| generators(right).contains(g) ==> #[trigger] stable(eq, left, g)
    &&& forall|f: PartialMap<IMap<K, V>>| generators(left).contains(f) ==> #[trigger] stable(eq, right, f)
}

/// Nested options distinguish a failed partial operation from removing a slot.
pub type SlotMap<V> = spec_fn(Option<V>) -> Option<Option<V>>;
pub open spec fn lift<K, V>(key: K, f: SlotMap<V>) -> PartialMap<IMap<K, V>> {
    |s: IMap<K, V>| match f(coeffects::get(s, key)) {
        Some(value) => Some(coeffects::put(s, key, value)), None => None,
    }
}

pub open spec fn slot_inverse<V>(f: PartialMap<V>) -> SlotMap<V> {
    |slot: Option<V>| match slot { None => None, Some(v) => match f(v) { None => None, Some(w) => Some(Some(w)) } }
}

pub open spec fn value_forward<V, O>(op: Operation<V, O>) -> PartialMap<V> {
    |v: V| match op(v) { None => None, Some(y) => Some(y.value) }
}
pub open spec fn value_generators<V, O>(op: Operation<V, O>) -> ISet<PartialMap<V>> {
    ISet::new(|f: PartialMap<V>| f == value_forward(op) || exists|v: V| #[trigger] op(v).is_some() && op(v).unwrap().undo == f)
}
pub open spec fn value_stable<V, O>(eq: spec_fn(V, V) -> bool, op: Operation<V, O>, g: PartialMap<V>) -> bool {
    forall|v: V| #[trigger] g(v).is_some() ==> {
        let a = op(v); let b = op(g(v).unwrap());
        &&& a.is_some() == b.is_some()
        &&& a.is_some() ==> a.unwrap().outcome == b.unwrap().outcome
            && mediated::partial_related(eq, a.unwrap().undo, b.unwrap().undo)
    }
}
pub open spec fn value_independent<V, O, P>(eq: spec_fn(V, V) -> bool, a: Operation<V, O>, b: Operation<V, P>) -> bool {
    &&& forall|f: PartialMap<V>, g: PartialMap<V>| value_generators(a).contains(f) && value_generators(b).contains(g)
        ==> #[trigger] commutes(eq, f, g)
    &&& forall|g: PartialMap<V>| value_generators(b).contains(g) ==> #[trigger] value_stable(eq, a, g)
    &&& forall|f: PartialMap<V>| value_generators(a).contains(f) ==> #[trigger] value_stable(eq, b, f)
}

pub open spec fn key<K, V, O>(node: Node<K, V, O>) -> Option<K> {
    match node { Node::Unit => None, Node::Operation { key, .. } | Node::Provision { key, .. } => Some(key) }
}

pub proof fn inverse_as_slot<K, V>(k: K, f: PartialMap<V>)
    ensures mediated::lift_inverse(k, f) == lift(k, slot_inverse(f)),
{ assert(mediated::lift_inverse(k, f) =~= lift(k, slot_inverse(f))); }

pub proof fn operation_generator<K, V, O>(k: K, op: Operation<V, O>, select: spec_fn(O) -> Option<nat>, f: PartialMap<IMap<K, V>>)
    requires generators(Node::Operation { key: k, operation: op, select }).contains(f),
    ensures exists|g: PartialMap<V>| value_generators(op).contains(g) && f == mediated::lift_inverse(k, g),
{
    let node = Node::Operation { key: k, operation: op, select };
    if f == forward(node) {
        let g = value_forward(op);
        assert(f =~= mediated::lift_inverse(k, g));
        assert(value_generators(op).contains(g));
    } else {
        let s = choose|s: IMap<K, V>| #[trigger] mediated::run(node, s).is_some() && mediated::run(node, s).unwrap().undo == f;
        let g = op(s[k]).unwrap().undo;
        assert(value_generators(op).contains(g));
    }
}

pub proof fn local_generator<K, V, O>(node: Node<K, V, O>, f: PartialMap<IMap<K, V>>)
    requires key(node).is_some(), generators(node).contains(f),
    ensures exists|g: SlotMap<V>| f == lift(key(node).unwrap(), g),
{
    match node {
        Node::Unit => { },
        Node::Operation { key: k, operation, select } => {
            operation_generator(k, operation, select, f);
            let g = choose|g: PartialMap<V>| value_generators(operation).contains(g) && f == mediated::lift_inverse(k, g);
            inverse_as_slot(k, g);
            assert(f == lift(key(node).unwrap(), slot_inverse(g)));
        },
        Node::Provision { key: k, value, .. } => {
            if f == forward(node) {
                let g = |slot: Option<V>| if slot.is_none() { Some(Some(value)) } else { None };
                assert(f =~= lift(k, g));
                assert(f == lift(key(node).unwrap(), g));
            } else {
                let s = choose|s: IMap<K, V>| #[trigger] mediated::run(node, s).is_some() && mediated::run(node, s).unwrap().undo == f;
                let g = |slot: Option<V>| if slot.is_some() { Some(None::<V>) } else { None };
                assert(f =~= lift(k, g));
                assert(f == lift(key(node).unwrap(), g));
            }
        },
    }
}

pub proof fn distinct_lifts_commute<K, V>(eq: spec_fn(K, V, V) -> bool, k: K, j: K, f: SlotMap<V>, g: SlotMap<V>)
    requires k != j, calculus::equivalence(context_eq(eq)),
    ensures commutes(context_eq(eq), lift(k, f), lift(j, g)),
{
    assert forall|s: IMap<K, V>| #[trigger] optional_equal(context_eq(eq), compose(lift(k, f), lift(j, g))(s), compose(lift(j, g), lift(k, f))(s)) by {
        if f(coeffects::get(s, k)).is_some() { coeffects::lookup_update(s, k, j, f(coeffects::get(s, k)).unwrap()); }
        if g(coeffects::get(s, j)).is_some() { coeffects::lookup_update(s, j, k, g(coeffects::get(s, j)).unwrap()); }
        if f(coeffects::get(s, k)).is_some() && g(coeffects::get(s, j)).is_some() {
            coeffects::update_commutes(s, k, j, f(coeffects::get(s, k)).unwrap(), g(coeffects::get(s, j)).unwrap());
        }
    }
}

pub proof fn foreign_stability<K, V, O>(eq: spec_fn(K, V, V) -> bool, node: Node<K, V, O>, j: K, g: SlotMap<V>)
    requires key(node).is_some(), key(node).unwrap() != j, mediated::stage_respects(eq, ISet::full(), node),
        calculus::equivalence(context_eq(eq)),
    ensures stable(eq, node, lift(j, g)),
{
    assert forall|s: IMap<K, V>| #[trigger] lift(j, g)(s).is_some() implies {
        let a = mediated::run(node, s); let b = mediated::run(node, lift(j, g)(s).unwrap());
        &&& a.is_some() == b.is_some()
        &&& a.is_some() ==> {
            &&& mediated::partial_related(context_eq(eq), a.unwrap().undo, b.unwrap().undo)
            &&& a.unwrap().next == b.unwrap().next
            &&& outcome(node, s) == outcome(node, lift(j, g)(s).unwrap())
        }
    } by {
        coeffects::lookup_update(s, j, key(node).unwrap(), g(coeffects::get(s, j)).unwrap());
        assert(context_eq(eq)(s, s));
        match node { Node::Unit => { }, Node::Operation { .. } => { }, Node::Provision { .. } => { } }
    }
}

pub proof fn distinct_nodes<K, V, O, P>(eq: spec_fn(K, V, V) -> bool, a: Node<K, V, O>, b: Node<K, V, P>)
    requires key(a).is_some(), key(b).is_some(), key(a) != key(b),
        mediated::stage_respects(eq, ISet::full(), a), mediated::stage_respects(eq, ISet::full(), b), calculus::equivalence(context_eq(eq)),
    ensures independent(eq, a, b),
{
    assert forall|f: PartialMap<IMap<K, V>>, g: PartialMap<IMap<K, V>>| generators(a).contains(f) && generators(b).contains(g)
        implies #[trigger] commutes(context_eq(eq), f, g) by {
        local_generator(a, f); local_generator(b, g);
        let x = choose|x: SlotMap<V>| f == lift(key(a).unwrap(), x);
        let y = choose|y: SlotMap<V>| g == lift(key(b).unwrap(), y);
        distinct_lifts_commute(eq, key(a).unwrap(), key(b).unwrap(), x, y);
    }
    assert forall|g: PartialMap<IMap<K, V>>| generators(b).contains(g) implies #[trigger] stable(eq, a, g) by {
        local_generator(b, g); let y = choose|y: SlotMap<V>| g == lift(key(b).unwrap(), y);
        foreign_stability(eq, a, key(b).unwrap(), y);
    }
    assert forall|f: PartialMap<IMap<K, V>>| generators(a).contains(f) implies #[trigger] stable(eq, b, f) by {
        local_generator(a, f); let x = choose|x: SlotMap<V>| f == lift(key(a).unwrap(), x);
        foreign_stability(eq, b, key(a).unwrap(), x);
    }
}

pub proof fn shared_lifts_commute<K, V>(eq: spec_fn(K, V, V) -> bool, k: K, f: PartialMap<V>, g: PartialMap<V>)
    requires commutes(|a: V, b: V| eq(k, a, b), f, g), calculus::equivalence(context_eq(eq)),
    ensures commutes(context_eq(eq), mediated::lift_inverse(k, f), mediated::lift_inverse(k, g)),
{
    let lf = mediated::lift_inverse(k, f); let lg = mediated::lift_inverse(k, g);
    assert forall|s: IMap<K, V>| #[trigger] optional_equal(context_eq(eq), compose(lf, lg)(s), compose(lg, lf)(s)) by {
        if s.dom().contains(k) {
            assert(optional_equal(|a: V, b: V| eq(k, a, b), compose(f, g)(s[k]), compose(g, f)(s[k])));
            if compose(f, g)(s[k]).is_some() {
                assert(context_eq(eq)(s, s));
                mediated::update_related(eq, ISet::full(), k, s, s, compose(f, g)(s[k]).unwrap(), compose(g, f)(s[k]).unwrap());
            }
        }
    }
}

pub proof fn shared_stability<K, V, O>(eq: spec_fn(K, V, V) -> bool, k: K, op: Operation<V, O>, select: spec_fn(O) -> Option<nat>, g: PartialMap<V>)
    requires value_stable(|a: V, b: V| eq(k, a, b), op, g),
    ensures stable(eq, Node::Operation { key: k, operation: op, select }, mediated::lift_inverse(k, g)),
{
    let node = Node::Operation { key: k, operation: op, select }; let foreign = mediated::lift_inverse(k, g);
    assert forall|s: IMap<K, V>| #[trigger] foreign(s).is_some() implies {
        let a = mediated::run(node, s); let b = mediated::run(node, foreign(s).unwrap());
        &&& a.is_some() == b.is_some()
        &&& a.is_some() ==> {
            &&& mediated::partial_related(context_eq(eq), a.unwrap().undo, b.unwrap().undo)
            &&& a.unwrap().next == b.unwrap().next
            &&& outcome(node, s) == outcome(node, foreign(s).unwrap())
        }
    } by {
        assert(g(s[k]).is_some());
        assert(op(s[k]).is_some() == op(g(s[k]).unwrap()).is_some());
        if op(s[k]).is_some() {
            mediated::inverse_lift_respects(eq, ISet::full(), k, op(s[k]).unwrap().undo, op(g(s[k]).unwrap()).unwrap().undo);
        }
    }
}

pub proof fn shared_operations<K, V, O, P>(eq: spec_fn(K, V, V) -> bool, k: K, a: Operation<V, O>, b: Operation<V, P>,
    an: spec_fn(O) -> Option<nat>, bn: spec_fn(P) -> Option<nat>)
    requires value_independent(|x: V, y: V| eq(k, x, y), a, b), calculus::equivalence(context_eq(eq)),
    ensures independent(eq, Node::Operation { key: k, operation: a, select: an }, Node::Operation { key: k, operation: b, select: bn }),
{
    let left = Node::Operation { key: k, operation: a, select: an }; let right = Node::Operation { key: k, operation: b, select: bn };
    assert forall|f: PartialMap<IMap<K, V>>, g: PartialMap<IMap<K, V>>| generators(left).contains(f) && generators(right).contains(g)
        implies #[trigger] commutes(context_eq(eq), f, g) by {
        operation_generator(k, a, an, f); operation_generator(k, b, bn, g);
        let x = choose|x: PartialMap<V>| value_generators(a).contains(x) && f == mediated::lift_inverse(k, x);
        let y = choose|y: PartialMap<V>| value_generators(b).contains(y) && g == mediated::lift_inverse(k, y);
        shared_lifts_commute(eq, k, x, y);
    }
    assert forall|g: PartialMap<IMap<K, V>>| generators(right).contains(g) implies #[trigger] stable(eq, left, g) by {
        operation_generator(k, b, bn, g);
        let y = choose|y: PartialMap<V>| value_generators(b).contains(y) && g == mediated::lift_inverse(k, y);
        shared_stability(eq, k, a, an, y);
    }
    assert forall|f: PartialMap<IMap<K, V>>| generators(left).contains(f) implies #[trigger] stable(eq, right, f) by {
        operation_generator(k, a, an, f);
        let x = choose|x: PartialMap<V>| value_generators(a).contains(x) && f == mediated::lift_inverse(k, x);
        shared_stability(eq, k, b, bn, x);
    }
}

pub proof fn commute_symmetric<S>(eq: spec_fn(S, S) -> bool, f: PartialMap<S>, g: PartialMap<S>)
    requires calculus::equivalence(eq), commutes(eq, f, g),
    ensures commutes(eq, g, f),
{
    assert forall|s: S| #[trigger] optional_equal(eq, compose(g, f)(s), compose(f, g)(s)) by {
        optional_symmetric(eq, compose(f, g)(s), compose(g, f)(s));
    }
}

pub proof fn commute_word<S>(eq: spec_fn(S, S) -> bool, f: PartialMap<S>, word: Seq<PartialMap<S>>)
    requires calculus::equivalence(eq),
        forall|i: int| 0 <= i < word.len() ==> commutes(eq, f, #[trigger] word[i]) && respects(eq, word[i]),
    ensures commutes(eq, f, |s: S| run(word, s)),
    decreases word.len(),
{
    if word.len() > 0 {
        commute_word(eq, f, word.drop_last());
        commute_composition(eq, f, word.last(), |s: S| run(word.drop_last(), s));
        assert((|s: S| run(word, s)) =~= compose(word.last(), |s: S| run(word.drop_last(), s)));
    }
}

/// Lemma 41 at partial maps, with both definedness and observational equality.
pub proof fn generated_commutation<S>(eq: spec_fn(S, S) -> bool, left: ISet<PartialMap<S>>, right: ISet<PartialMap<S>>, f: PartialMap<S>, g: PartialMap<S>)
    requires calculus::equivalence(eq), generated(left, f), generated(right, g),
        forall|a: PartialMap<S>| left.contains(a) ==> #[trigger] respects(eq, a),
        forall|b: PartialMap<S>| right.contains(b) ==> #[trigger] respects(eq, b),
        forall|a: PartialMap<S>, b: PartialMap<S>| left.contains(a) && right.contains(b) ==> #[trigger] commutes(eq, a, b),
    ensures commutes(eq, f, g),
{
    let xs = choose|word: Seq<PartialMap<S>>| word_in(left, word) && f == (|s: S| run(word, s));
    let ys = choose|word: Seq<PartialMap<S>>| word_in(right, word) && g == (|s: S| run(word, s));
    assert forall|i: int| 0 <= i < xs.len() implies commutes(eq, g, #[trigger] xs[i]) && respects(eq, xs[i]) by {
        assert forall|j: int| 0 <= j < ys.len() implies commutes(eq, xs[i], #[trigger] ys[j]) && respects(eq, ys[j]) by { }
        commute_word(eq, xs[i], ys);
        commute_symmetric(eq, xs[i], g);
    }
    commute_word(eq, g, xs);
    commute_symmetric(eq, g, f);
}

pub proof fn partial_relation_transitive<S>(eq: spec_fn(S, S) -> bool, f: PartialMap<S>, g: PartialMap<S>, h: PartialMap<S>)
    requires calculus::equivalence(eq), mediated::partial_related(eq, f, g), mediated::partial_related(eq, g, h),
    ensures mediated::partial_related(eq, f, h),
{
    assert forall|a: S, b: S| #![trigger f(a), h(b)] eq(a, b) implies {
        &&& f(a).is_some() == h(b).is_some()
        &&& f(a).is_some() ==> eq(f(a).unwrap(), h(b).unwrap())
    } by {
        assert(eq(a, a));
        assert(f(a).is_some() == g(a).is_some());
        assert(g(a).is_some() == h(b).is_some());
        if f(a).is_some() { assert(eq(f(a).unwrap(), g(a).unwrap())); assert(eq(g(a).unwrap(), h(b).unwrap())); }
    }
}

pub proof fn stable_word<K, V, O>(eq: spec_fn(K, V, V) -> bool, node: Node<K, V, O>, word: Seq<PartialMap<IMap<K, V>>>)
    requires calculus::equivalence(context_eq(eq)), mediated::stage_respects(eq, ISet::full(), node),
        forall|i: int| 0 <= i < word.len() ==> stable(eq, node, #[trigger] word[i]),
    ensures stable(eq, node, |s: IMap<K, V>| run(word, s)),
    decreases word.len(),
{
    if word.len() > 0 { stable_word(eq, node, word.drop_last()); }
    assert forall|s: IMap<K, V>| #[trigger] run(word, s).is_some() implies {
        let a = mediated::run(node, s); let b = mediated::run(node, run(word, s).unwrap());
        &&& a.is_some() == b.is_some()
        &&& a.is_some() ==> {
            &&& mediated::partial_related(context_eq(eq), a.unwrap().undo, b.unwrap().undo)
            &&& a.unwrap().next == b.unwrap().next
            &&& outcome(node, s) == outcome(node, run(word, s).unwrap())
        }
    } by {
        if word.len() == 0 { assert(context_eq(eq)(s, s)); }
        else {
            let previous = |x: IMap<K, V>| run(word.drop_last(), x);
            let middle = previous(s).unwrap();
            assert(stable(eq, node, previous));
            assert(previous(s).is_some());
            assert(mediated::run(node, s).is_some() == mediated::run(node, middle).is_some());
            assert((word.last())(middle).is_some());
            assert(stable(eq, node, word.last()));
            assert(mediated::run(node, middle).is_some() == mediated::run(node, run(word, s).unwrap()).is_some());
            if mediated::run(node, s).is_some() {
                partial_relation_transitive(context_eq(eq), mediated::run(node, s).unwrap().undo,
                    mediated::run(node, middle).unwrap().undo, mediated::run(node, run(word, s).unwrap()).unwrap().undo);
            }
        }
    }
}

pub proof fn unit_independence<K, V, O, P>(eq: spec_fn(K, V, V) -> bool, node: Node<K, V, O>)
    requires calculus::equivalence(context_eq(eq)), mediated::stage_respects(eq, ISet::full(), node),
    ensures independent(eq, Node::<K, V, P>::Unit, node), independent(eq, node, Node::<K, V, P>::Unit),
{
    let unit = Node::<K, V, P>::Unit; let identity = |s: IMap<K, V>| Some(s);
    assert forall|f: PartialMap<IMap<K, V>>| generators(unit).contains(f) implies f == identity by {
        if f == forward(unit) { assert(f =~= identity); }
        else {
            let s = choose|s: IMap<K, V>| #[trigger] mediated::run(unit, s).is_some() && mediated::run(unit, s).unwrap().undo == f;
            assert(f =~= identity);
        }
    }
    assert(stable(eq, node, identity)) by {
        assert forall|s: IMap<K, V>| #[trigger] identity(s).is_some() implies {
            let a = mediated::run(node, s); let b = mediated::run(node, identity(s).unwrap());
            &&& a.is_some() == b.is_some()
            &&& a.is_some() ==> {
                &&& mediated::partial_related(context_eq(eq), a.unwrap().undo, b.unwrap().undo)
                &&& a.unwrap().next == b.unwrap().next
                &&& outcome(node, s) == outcome(node, identity(s).unwrap())
            }
        } by { assert(context_eq(eq)(s, s)); }
    }
    assert forall|g: PartialMap<IMap<K, V>>| generators(node).contains(g) implies
        commutes(context_eq(eq), identity, g) && commutes(context_eq(eq), g, identity) && stable(eq, unit, g) by { }
}

pub proof fn generator_respects<K, V, O>(eq: spec_fn(K, V, V) -> bool, node: Node<K, V, O>, f: PartialMap<IMap<K, V>>)
    requires calculus::equivalence(context_eq(eq)), mediated::stage_respects(eq, ISet::full(), node), generators(node).contains(f),
    ensures respects(context_eq(eq), f),
{
    if f == forward(node) {
        assert forall|a: IMap<K, V>, b: IMap<K, V>| #![trigger f(a), f(b)] context_eq(eq)(a, b) implies {
            &&& f(a).is_some() == f(b).is_some()
            &&& f(a).is_some() ==> context_eq(eq)(f(a).unwrap(), f(b).unwrap())
        } by { assert(mediated::run(node, a).is_some() == mediated::run(node, b).is_some()); }
    } else {
        let s = choose|s: IMap<K, V>| #[trigger] mediated::run(node, s).is_some() && mediated::run(node, s).unwrap().undo == f;
        assert(context_eq(eq)(s, s));
    }
}

pub open spec fn reachable_closed<K, V, O>(program: mediated::Program<K, V, O>, ids: ISet<nat>) -> bool {
    forall|id: nat, s: IMap<K, V>| ids.contains(id) && (#[trigger] mediated::run(program(id), s)).is_some()
        && mediated::run(program(id), s).unwrap().next.is_some() ==> ids.contains(mediated::run(program(id), s).unwrap().next.unwrap())
}

pub open spec fn reach<K, V, O>(program: mediated::Program<K, V, O>, root: nat) -> ISet<nat> {
    ISet::new(|id: nat| forall|ids: ISet<nat>| #[trigger] ids.contains(root) && reachable_closed(program, ids) ==> ids.contains(id))
}

pub proof fn reach_least_closed<K, V, O>(program: mediated::Program<K, V, O>, root: nat, ids: ISet<nat>)
    ensures reach(program, root).contains(root), reachable_closed(program, reach(program, root)),
        ids.contains(root) && reachable_closed(program, ids) ==> reach(program, root).subset_of(ids),
{
    assert forall|id: nat, s: IMap<K, V>| reach(program, root).contains(id) && (#[trigger] mediated::run(program(id), s)).is_some()
        && mediated::run(program(id), s).unwrap().next.is_some() implies reach(program, root).contains(mediated::run(program(id), s).unwrap().next.unwrap()) by {
        let next = mediated::run(program(id), s).unwrap().next.unwrap();
        assert forall|candidate: ISet<nat>| #[trigger] candidate.contains(root) && reachable_closed(program, candidate) implies candidate.contains(next) by {
            assert(candidate.contains(id));
        }
    }
}

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(V)]
#[verifier::reject_recursive_types(O)]
pub struct Grammar<K, V, O> {
    pub program: crate::mediated::Program<K, V, O>,
    pub allowed: crate::mediated::Allowed<K, V, O>,
    pub keys: ISet<K>,
    pub provisions: ISet<K>,
    pub root: nat,
}

pub open spec fn valid<K, V, O>(eq: spec_fn(K, V, V) -> bool, grammar: Grammar<K, V, O>) -> bool {
    mediated::primitive_theory(eq, grammar.allowed) && grammar.provisions.subset_of(grammar.keys)
        && mediated::member(grammar.program, grammar.allowed, grammar.keys, grammar.provisions, grammar.root)
}

pub proof fn reachable_member<K, V, O>(eq: spec_fn(K, V, V) -> bool, grammar: Grammar<K, V, O>, id: nat)
    requires valid(eq, grammar), reach(grammar.program, grammar.root).contains(id),
    ensures mediated::member(grammar.program, grammar.allowed, grammar.keys, grammar.provisions, id),
        mediated::permitted(grammar.allowed, grammar.keys, grammar.provisions, (grammar.program)(id)),
        mediated::stage_respects(eq, ISet::full(), (grammar.program)(id)),
        mediated::stage_witness((grammar.program)(id)),
{
    let members = mediated::members(grammar.program, grammar.allowed, grammar.keys, grammar.provisions);
    assert(reachable_closed(grammar.program, members)) by {
        assert forall|n: nat, s: IMap<K, V>| members.contains(n) && (#[trigger] mediated::run((grammar.program)(n), s)).is_some()
            && mediated::run((grammar.program)(n), s).unwrap().next.is_some() implies members.contains(mediated::run((grammar.program)(n), s).unwrap().next.unwrap()) by {
            mediated::context_mediated_admissible(eq, grammar.program, grammar.allowed, grammar.keys, grammar.provisions, n);
            match (grammar.program)(n) { Node::Unit => { }, Node::Operation { .. } => { }, Node::Provision { .. } => { } }
        }
    }
    reach_least_closed(grammar.program, grammar.root, members);
    mediated::member_permitted(grammar.program, grammar.allowed, grammar.keys, grammar.provisions, id);
    assert(mediated::permitted(grammar.allowed, ISet::full(), grammar.provisions, (grammar.program)(id)));
    mediated::permitted_admissible(eq, grammar.program, grammar.allowed, ISet::full(), grammar.provisions, id);
}

pub open spec fn separated<K, V, O, P>(left: Grammar<K, V, O>, right: Grammar<K, V, P>) -> bool {
    left.provisions.disjoint(right.keys) && right.provisions.disjoint(left.keys)
}

/// The provider's local witness compares outcomes themselves. Continuation
/// selectors may be non-injective, so their equality cannot replace this law.
pub open spec fn witnessed_keys<K, V, O, P>(eq: spec_fn(K, V, V) -> bool, left: Grammar<K, V, O>, right: Grammar<K, V, P>) -> bool {
    forall|k: K, a: Operation<V, O>, b: Operation<V, P>| left.keys.contains(k) && right.keys.contains(k)
        && (#[trigger] (left.allowed)(k, a)) && (#[trigger] (right.allowed)(k, b))
        ==> value_independent(|x: V, y: V| eq(k, x, y), a, b)
}

pub proof fn context_equivalence<K, V, O>(eq: spec_fn(K, V, V) -> bool, grammar: Grammar<K, V, O>)
    requires valid(eq, grammar),
    ensures calculus::equivalence(context_eq(eq)),
{
    assert forall|k: K| ISet::<K>::full().contains(k) implies calculus::equivalence(|a: V, b: V| eq(k, a, b)) by {
        assert(mediated::key_equivalence(eq, k));
    }
    observation::context_equivalence(eq, ISet::full());
}

/// Theorem 47 at the least grammar: only actual reachable stages are compared.
/// No common finite height, totality, or context-level independence is assumed.
pub proof fn reachable_independence<K, V, O, P>(eq: spec_fn(K, V, V) -> bool, left: Grammar<K, V, O>, right: Grammar<K, V, P>, i: nat, j: nat)
    requires valid(eq, left), valid(eq, right), separated(left, right), witnessed_keys(eq, left, right),
        reach(left.program, left.root).contains(i), reach(right.program, right.root).contains(j),
    ensures independent(eq, (left.program)(i), (right.program)(j)),
{
    context_equivalence(eq, left); reachable_member(eq, left, i); reachable_member(eq, right, j);
    let a = (left.program)(i); let b = (right.program)(j);
    match a {
        Node::Unit => { unit_independence::<K, V, P, O>(eq, b); },
        _ => match b {
            Node::Unit => { unit_independence::<K, V, O, P>(eq, a); },
            _ => {
                if key(a) != key(b) { distinct_nodes(eq, a, b); }
                else {
                    match a {
                        Node::Operation { key: k, operation: x, select: xn } => match b {
                            Node::Operation { operation: y, select: yn, .. } => { shared_operations(eq, k, x, y, xn, yn); },
                            _ => { },
                        },
                        _ => { },
                    }
                }
            },
        },
    }
}

pub open spec fn reachable_generators<K, V, O>(grammar: Grammar<K, V, O>) -> ISet<PartialMap<IMap<K, V>>> {
    ISet::new(|f: PartialMap<IMap<K, V>>| exists|id: nat| reach(grammar.program, grammar.root).contains(id)
        && #[trigger] generators((grammar.program)(id)).contains(f))
}

pub proof fn reachable_generators_respect<K, V, O>(eq: spec_fn(K, V, V) -> bool, grammar: Grammar<K, V, O>)
    requires valid(eq, grammar),
    ensures forall|f: PartialMap<IMap<K, V>>| reachable_generators(grammar).contains(f) ==> #[trigger] respects(context_eq(eq), f),
{
    context_equivalence(eq, grammar);
    assert forall|f: PartialMap<IMap<K, V>>| reachable_generators(grammar).contains(f) implies #[trigger] respects(context_eq(eq), f) by {
        let id = choose|id: nat| reach(grammar.program, grammar.root).contains(id) && #[trigger] generators((grammar.program)(id)).contains(f);
        reachable_member(eq, grammar, id); generator_respects(eq, (grammar.program)(id), f);
    }
}

/// Definition 42(1), lifted from the coeffect witnesses to both complete
/// transformation monoids of reachable context-mediated partial stages.
pub proof fn grammar_monoids_commute<K, V, O, P>(eq: spec_fn(K, V, V) -> bool, left: Grammar<K, V, O>, right: Grammar<K, V, P>,
    f: PartialMap<IMap<K, V>>, g: PartialMap<IMap<K, V>>)
    requires valid(eq, left), valid(eq, right), separated(left, right), witnessed_keys(eq, left, right),
        generated(reachable_generators(left), f), generated(reachable_generators(right), g),
    ensures commutes(context_eq(eq), f, g),
{
    context_equivalence(eq, left); reachable_generators_respect(eq, left); reachable_generators_respect(eq, right);
    assert forall|a: PartialMap<IMap<K, V>>, b: PartialMap<IMap<K, V>>|
        reachable_generators(left).contains(a) && reachable_generators(right).contains(b) implies #[trigger] commutes(context_eq(eq), a, b) by {
        let i = choose|id: nat| reach(left.program, left.root).contains(id) && #[trigger] generators((left.program)(id)).contains(a);
        let j = choose|id: nat| reach(right.program, right.root).contains(id) && #[trigger] generators((right.program)(id)).contains(b);
        reachable_independence(eq, left, right, i, j);
    }
    generated_commutation(context_eq(eq), reachable_generators(left), reachable_generators(right), f, g);
}

/// Definition 42(2), including partial inverse domains and the stronger raw
/// operation outcome observation from Definition 44, for arbitrary words.
pub proof fn grammar_yields_stable<K, V, O, P>(eq: spec_fn(K, V, V) -> bool, left: Grammar<K, V, O>, right: Grammar<K, V, P>, i: nat, g: PartialMap<IMap<K, V>>)
    requires valid(eq, left), valid(eq, right), separated(left, right), witnessed_keys(eq, left, right),
        reach(left.program, left.root).contains(i), generated(reachable_generators(right), g),
    ensures stable(eq, (left.program)(i), g),
{
    context_equivalence(eq, left); reachable_member(eq, left, i);
    let word = choose|word: Seq<PartialMap<IMap<K, V>>>| word_in(reachable_generators(right), word) && g == (|s: IMap<K, V>| run(word, s));
    assert forall|n: int| 0 <= n < word.len() implies stable(eq, (left.program)(i), #[trigger] word[n]) by {
        let j = choose|id: nat| reach(right.program, right.root).contains(id) && #[trigger] generators((right.program)(id)).contains(word[n]);
        reachable_independence(eq, left, right, i, j);
    }
    stable_word(eq, (left.program)(i), word);
}

/// The concrete exchange includes enabledness, continuation, raw outcome and
/// yielded-inverse agreement. It can be consumed without totalizing the stage.
pub proof fn actual_exchange<K, V, O, P>(eq: spec_fn(K, V, V) -> bool, a: Node<K, V, O>, b: Node<K, V, P>, s: IMap<K, V>)
    requires independent(eq, a, b), mediated::run(a, s).is_some(), mediated::run(b, s).is_some(),
    ensures mediated::run(a, mediated::run(b, s).unwrap().state).is_some(),
        mediated::run(b, mediated::run(a, s).unwrap().state).is_some(),
        context_eq(eq)(mediated::run(a, mediated::run(b, s).unwrap().state).unwrap().state,
            mediated::run(b, mediated::run(a, s).unwrap().state).unwrap().state),
        mediated::run(a, s).unwrap().next == mediated::run(a, mediated::run(b, s).unwrap().state).unwrap().next,
        mediated::run(b, s).unwrap().next == mediated::run(b, mediated::run(a, s).unwrap().state).unwrap().next,
        outcome(a, s) == outcome(a, mediated::run(b, s).unwrap().state),
        outcome(b, s) == outcome(b, mediated::run(a, s).unwrap().state),
        mediated::partial_related(context_eq(eq), mediated::run(a, s).unwrap().undo,
            mediated::run(a, mediated::run(b, s).unwrap().state).unwrap().undo),
        mediated::partial_related(context_eq(eq), mediated::run(b, s).unwrap().undo,
            mediated::run(b, mediated::run(a, s).unwrap().state).unwrap().undo),
{
    assert(generators(a).contains(forward(a))); assert(generators(b).contains(forward(b)));
    assert(stable(eq, a, forward(b))); assert(stable(eq, b, forward(a)));
    assert(forward(a)(s).is_some()); assert(forward(b)(s).is_some());
    assert(commutes(context_eq(eq), forward(a), forward(b)));
    assert(optional_equal(context_eq(eq), compose(forward(a), forward(b))(s), compose(forward(b), forward(a))(s)));
}

pub open spec fn counted_increment() -> Operation<int, int> {
    |v: int| Some(mediated::ValueYield { value: v + 1, undo: |x: int| Some(x - 1), outcome: v })
}

/// Regression for the distinction required by Definition 44: discarding the
/// outcome in a continuation does not make an increment-and-return operation
/// independent of another occurrence of itself.
pub proof fn discarded_outcome_is_not_independence()
    ensures {
        let op = counted_increment();
        let select = |outcome: int| None::<nat>;
        &&& select(op(0).unwrap().outcome) == select(op(1).unwrap().outcome)
        &&& !value_stable(|x: int, y: int| x == y, op, value_forward(op))
        &&& !value_independent(|x: int, y: int| x == y, op, op)
    },
{
    let op = counted_increment(); let f = value_forward(op);
    let eq = |x: int, y: int| x == y;
    assert(f(0) == Some(1));
    assert(value_generators(op).contains(f));
    assert(op(0).unwrap().outcome != op(f(0).unwrap()).unwrap().outcome);
    assert(!value_stable(eq, op, f));
    assert(!value_independent(eq, op, op));
}

} // verus!
