//! Lemma 60: lifecycle simulation over keywise service observations.
//!
//! Control and opaque interpreter identities agree exactly. Only service values
//! vary observationally. Primitive iterator/inverse respect is lifted through
//! accumulator composition and every lifecycle and orchestration rule.
#[cfg(verus_keep_ghost)]
use crate::{observation, refinement as control, semantics as full, Binding, Phase, Port};
use vstd::prelude::*;

verus! {

pub open spec fn tables_equal<V>(eq: spec_fn(Port, V, V) -> bool,
    a: IMap<usize, IMap<Port, V>>, b: IMap<usize, IMap<Port, V>>) -> bool
{
    &&& a.dom() == b.dom()
    &&& forall|n: usize| a.dom().contains(n) ==>
        observation::context_equal(eq, ISet::full(), a[n], b[n])
}

pub open spec fn related<V>(eq: spec_fn(Port, V, V) -> bool, a: full::State<V>, b: full::State<V>) -> bool {
    &&& a.control == b.control
    &&& a.effects == b.effects && a.iterators == b.iterators && a.accumulators == b.accumulators
    &&& tables_equal(eq, a.tables, b.tables)
}

/// These are local semantic contracts at a single application, not a premise
/// that complete lifecycle steps already simulate one another.
pub open spec fn primitives_respect<V>(eq: spec_fn(Port, V, V) -> bool, m: full::Model<V>) -> bool {
    &&& forall|n: usize, k: nat, a: full::State<V>, b: full::State<V>|
        #![trigger (m.iterate)(n, k, a), (m.iterate)(n, k, b)]
        related(eq, a, b) ==> {
            let x = (m.iterate)(n, k, a);
            let y = (m.iterate)(n, k, b);
            &&& related(eq, x.state, y.state)
            &&& x.inverse == y.inverse && x.next == y.next
        }
    &&& forall|k: nat, a: full::State<V>, b: full::State<V>|
        #![trigger (m.undo)(k, a), (m.undo)(k, b)]
        related(eq, a, b) ==> related(eq, (m.undo)(k, a), (m.undo)(k, b))
}

pub proof fn table_domains<V>(eq: spec_fn(Port, V, V) -> bool, a: full::State<V>, b: full::State<V>, n: usize)
    requires related(eq, a, b), a.tables.dom().contains(n),
    ensures a.tables[n].dom() == b.tables[n].dom(),
{
    assert(observation::context_equal(eq, ISet::full(), a.tables[n], b.tables[n]));
    assert(a.tables[n].dom() =~= b.tables[n].dom()) by {
        assert forall|p: Port| a.tables[n].dom().contains(p) == b.tables[n].dom().contains(p) by {
            assert(ISet::<Port>::full().contains(p));
        }
    };
}

pub proof fn related_shaped<V>(eq: spec_fn(Port, V, V) -> bool, a: full::State<V>, b: full::State<V>)
    requires related(eq, a, b), full::shaped(a),
    ensures full::shaped(b),
{
    assert forall|n: usize| full::registered(b, n) implies {
        &&& b.tables[n].dom().subset_of(b.control.fibers[n].provisions)
        &&& (b.control.fibers[n].phase == Phase::Inactive ==> b.iterators[n].is_none()
            && b.accumulators[n].len() == 0 && b.control.fibers[n].committed.is_empty())
        &&& (b.control.fibers[n].phase == Phase::Loading ==> b.iterators[n].is_some())
        &&& (b.control.fibers[n].phase == Phase::Active || b.control.fibers[n].phase == Phase::Unloading
            ==> b.iterators[n].is_none())
    } by {
        assert(full::registered(a, n));
        table_domains(eq, a, b, n);
    }
}

pub proof fn guard_observations<V>(eq: spec_fn(Port, V, V) -> bool, a: full::State<V>, b: full::State<V>, n: usize, view: ISet<Binding>)
    requires related(eq, a, b), full::shaped(a),
    ensures full::target(a, n, view) == full::target(b, n, view),
        full::coherent(a, n) == full::coherent(b, n),
        control::relied(a.control, n) == control::relied(b.control, n),
{
    assert forall|p: Port, owner: usize| full::publishes(a, p, owner) == full::publishes(b, p, owner) by {
        if full::registered(a, owner) { table_domains(eq, a, b, owner); }
    }
}

pub proof fn restore_respects<V>(eq: spec_fn(Port, V, V) -> bool, m: full::Model<V>, tokens: Seq<nat>, a: full::State<V>, b: full::State<V>)
    requires primitives_respect(eq, m), related(eq, a, b),
    ensures related(eq, full::restore(m, tokens, a), full::restore(m, tokens, b)),
    decreases tokens.len(),
{
    if tokens.len() > 0 {
        assert(related(eq, (m.undo)(tokens.last(), a), (m.undo)(tokens.last(), b)));
        restore_respects(eq, m, tokens.drop_last(), (m.undo)(tokens.last(), a), (m.undo)(tokens.last(), b));
    }
}

pub proof fn edit_respects<V>(eq: spec_fn(Port, V, V) -> bool, a: full::State<V>, b: full::State<V>, n: usize,
    phase: Phase, committed: ISet<Binding>, iterator: Option<nat>, accumulator: Seq<nat>)
    requires related(eq, a, b),
    ensures related(eq, full::edit(a, n, phase, committed, iterator, accumulator),
        full::edit(b, n, phase, committed, iterator, accumulator)),
{ }

pub open spec fn replace_tables<V>(s: full::State<V>, tables: IMap<usize, IMap<Port, V>>) -> full::State<V> {
    full::State { control: s.control, effects: s.effects, iterators: s.iterators,
        accumulators: s.accumulators, tables }
}

/// Construct the right-hand successor by replaying the same rule. In the two
/// L-Divert alternatives, the selected branch is copied from the left step.
pub open spec fn successor<V>(m: full::Model<V>, a: full::State<V>, z: full::State<V>, b: full::State<V>, n: usize, rule: control::Rule) -> full::State<V> {
    match rule {
        control::Rule::Insert => replace_tables(z, b.tables.insert(n, IMap::empty())),
        control::Rule::Retire => replace_tables(z, b.tables),
        control::Rule::Remove => replace_tables(z, b.tables.remove(n)),
        control::Rule::Begin => full::edit(b, n, Phase::Loading, z.control.fibers[n].committed, Some(b.effects[n]), Seq::empty()),
        control::Rule::Iter | control::Rule::Finish | control::Rule::Divert => {
            let y = (m.iterate)(n, b.iterators[n].unwrap(), b);
            if rule == control::Rule::Iter {
                full::edit(y.state, n, Phase::Loading, b.control.fibers[n].committed, y.next, b.accumulators[n].push(y.inverse))
            } else if rule == control::Rule::Finish {
                full::edit(y.state, n, Phase::Active, b.control.fibers[n].committed, None, b.accumulators[n].push(y.inverse))
            } else if z == full::edit(a, n, Phase::Unloading, a.control.fibers[n].committed, None, a.accumulators[n]) {
                full::edit(b, n, Phase::Unloading, b.control.fibers[n].committed, None, b.accumulators[n])
            } else {
                full::edit(y.state, n, Phase::Unloading, b.control.fibers[n].committed, None, b.accumulators[n].push(y.inverse))
            }
        },
        control::Rule::Leave => full::edit(b, n, Phase::Unloading, b.control.fibers[n].committed, None, b.accumulators[n]),
        control::Rule::Unload => full::edit(full::restore(m, b.accumulators[n], b), n, Phase::Inactive, ISet::empty(), None, Seq::empty()),
        _ => b,
    }
}

pub proof fn insertion_tables<V>(eq: spec_fn(Port, V, V) -> bool, a: full::State<V>, z: full::State<V>, b: full::State<V>, n: usize)
    requires related(eq, a, b), full::shaped(a), full::shaped(z),
        control::step(a.control, z.control, n, control::Rule::Insert),
        full::auxiliary_frame(a, z, n), z.tables[n].is_empty(),
    ensures tables_equal(eq, z.tables, b.tables.insert(n, IMap::empty())),
{
    let bt = b.tables.insert(n, IMap::empty());
    assert(z.tables.dom() =~= bt.dom()) by {
        assert forall|x: usize| z.tables.dom().contains(x) == bt.dom().contains(x) by {
            if x != n { assert(control::registered(a.control, x) == control::registered(z.control, x)); }
        }
    }
    assert forall|x: usize| z.tables.dom().contains(x) implies observation::context_equal(eq, ISet::full(), z.tables[x], bt[x]) by {
        if x == n {
            assert(z.tables[n] =~= IMap::empty());
        } else {
            assert(full::registered(a, x));
            assert(z.tables[x] == a.tables[x]);
        }
    }
}

/// A concrete successor witnesses all nine rule cases. The conclusion is
/// derived from local iterator and inverse laws, including actual yielded
/// inverse tokens, rather than required as a simulation premise.
pub proof fn step_simulates<V>(eq: spec_fn(Port, V, V) -> bool, m: full::Model<V>, a: full::State<V>, z: full::State<V>, b: full::State<V>, n: usize, rule: control::Rule)
    requires primitives_respect(eq, m), related(eq, a, b), full::shaped(a), full::shaped(z), full::step(m, a, z, n, rule),
    ensures related(eq, z, successor(m, a, z, b, n, rule)),
        full::step(m, b, successor(m, a, z, b, n, rule), n, rule),
        full::shaped(successor(m, a, z, b, n, rule)),
{
    let out = successor(m, a, z, b, n, rule);
    related_shaped(eq, a, b);
    match rule {
        control::Rule::Insert => {
            insertion_tables(eq, a, z, b, n);
            assert(related(eq, z, out));
            related_shaped(eq, z, out);
            assert(full::auxiliary_frame(b, out, n)) by {
                assert forall|x: usize| x != n && full::registered(b, x) implies
                    out.tables[x] == b.tables[x] && out.effects[x] == b.effects[x]
                    && out.iterators[x] == b.iterators[x] && out.accumulators[x] == b.accumulators[x] by {
                    assert(full::registered(a, x));
                }
            }
        },
        control::Rule::Retire => { },
        control::Rule::Remove => {
            table_domains(eq, a, b, n);
            assert(tables_equal(eq, z.tables, out.tables)) by {
                assert forall|x: usize| z.tables.dom().contains(x) implies
                    observation::context_equal(eq, ISet::full(), z.tables[x], out.tables[x]) by {
                    assert(x != n);
                }
            }
        },
        control::Rule::Begin => {
            guard_observations(eq, a, b, n, z.control.fibers[n].committed);
            edit_respects(eq, a, b, n, Phase::Loading, z.control.fibers[n].committed, Some(a.effects[n]), Seq::empty());
        },
        control::Rule::Iter | control::Rule::Finish | control::Rule::Divert => {
            let x = (m.iterate)(n, a.iterators[n].unwrap(), a);
            let y = (m.iterate)(n, b.iterators[n].unwrap(), b);
            assert(related(eq, x.state, y.state));
            guard_observations(eq, a, b, n, a.control.fibers[n].committed);
            if rule == control::Rule::Iter {
                edit_respects(eq, x.state, y.state, n, Phase::Loading, a.control.fibers[n].committed, x.next, a.accumulators[n].push(x.inverse));
            } else if rule == control::Rule::Finish {
                edit_respects(eq, x.state, y.state, n, Phase::Active, a.control.fibers[n].committed, None, a.accumulators[n].push(x.inverse));
            } else if z == full::edit(a, n, Phase::Unloading, a.control.fibers[n].committed, None, a.accumulators[n]) {
                edit_respects(eq, a, b, n, Phase::Unloading, a.control.fibers[n].committed, None, a.accumulators[n]);
            } else {
                edit_respects(eq, x.state, y.state, n, Phase::Unloading, a.control.fibers[n].committed, None, a.accumulators[n].push(x.inverse));
            }
        },
        control::Rule::Leave => {
            guard_observations(eq, a, b, n, a.control.fibers[n].committed);
            edit_respects(eq, a, b, n, Phase::Unloading, a.control.fibers[n].committed, None, a.accumulators[n]);
        },
        control::Rule::Unload => {
            restore_respects(eq, m, a.accumulators[n], a, b);
            edit_respects(eq, full::restore(m, a.accumulators[n], a), full::restore(m, b.accumulators[n], b), n, Phase::Inactive, ISet::empty(), None, Seq::empty());
        },
        _ => { },
    }
    assert(related(eq, z, out));
    related_shaped(eq, z, out);
}

pub open spec fn key_equivalent<V>(eq: spec_fn(Port, V, V) -> bool, p: Port) -> bool {
    crate::calculus::equivalence(|a: V, b: V| eq(p, a, b))
}

pub proof fn relation_equivalence<V>(eq: spec_fn(Port, V, V) -> bool)
    requires forall|p: Port| #[trigger] key_equivalent(eq, p),
    ensures crate::calculus::equivalence(|a: full::State<V>, b: full::State<V>| related(eq, a, b)),
{
    assert forall|p: Port| ISet::<Port>::full().contains(p) implies crate::calculus::equivalence(|a: V, b: V| eq(p, a, b)) by {
        assert(key_equivalent(eq, p));
    }
    observation::context_equivalence(eq, ISet::full());
    let te = |a: IMap<Port, V>, b: IMap<Port, V>| observation::context_equal(eq, ISet::full(), a, b);
    assert(crate::calculus::equivalence(te));
    assert forall|a: full::State<V>| #[trigger] related(eq, a, a) by {
        assert forall|n: usize| a.tables.dom().contains(n) implies
            observation::context_equal(eq, ISet::full(), a.tables[n], a.tables[n]) by {
            assert(te(a.tables[n], a.tables[n]));
        }
    }
    assert forall|a: full::State<V>, b: full::State<V>| related(eq, a, b) implies #[trigger] related(eq, b, a) by {
        assert forall|n: usize| b.tables.dom().contains(n) implies
            observation::context_equal(eq, ISet::full(), b.tables[n], a.tables[n]) by {
            assert(observation::context_equal(eq, ISet::full(), a.tables[n], b.tables[n]));
            assert(te(a.tables[n], b.tables[n]));
            assert(te(b.tables[n], a.tables[n]));
        }
    }
    assert forall|a: full::State<V>, b: full::State<V>, c: full::State<V>|
        #[trigger] related(eq, a, b) && #[trigger] related(eq, b, c) implies related(eq, a, c) by {
        assert forall|n: usize| a.tables.dom().contains(n) implies
            observation::context_equal(eq, ISet::full(), a.tables[n], c.tables[n]) by {
            assert(observation::context_equal(eq, ISet::full(), a.tables[n], b.tables[n]));
            assert(observation::context_equal(eq, ISet::full(), b.tables[n], c.tables[n]));
            assert(te(a.tables[n], b.tables[n]));
            assert(te(b.tables[n], c.tables[n]));
            assert(te(a.tables[n], c.tables[n]));
        }
    }
}

pub proof fn quiet_equal<V>(eq: spec_fn(Port, V, V) -> bool, a: full::State<V>, b: full::State<V>)
    requires related(eq, a, b), full::shaped(a),
    ensures full::quiet(a) == full::quiet(b),
{
    assert forall|n: usize| full::registered(a, n) implies {
        &&& full::coherent(a, n) == full::coherent(b, n)
        &&& (exists|v: ISet<Binding>| full::target(a, n, v)) == (exists|v: ISet<Binding>| full::target(b, n, v))
    } by {
        guard_observations(eq, a, b, n, a.control.fibers[n].committed);
        if exists|v: ISet<Binding>| full::target(a, n, v) {
            let v = choose|v: ISet<Binding>| full::target(a, n, v);
            guard_observations(eq, a, b, n, v);
        }
        if exists|v: ISet<Binding>| full::target(b, n, v) {
            let v = choose|v: ISet<Binding>| full::target(b, n, v);
            guard_observations(eq, a, b, n, v);
        }
    }
    if full::quiet(a) {
        assert forall|n: usize| full::registered(b, n) implies match b.control.fibers[n].phase {
            Phase::Inactive => !(exists|v: ISet<Binding>| full::target(b, n, v)),
            Phase::Active => full::coherent(b, n),
            _ => false,
        } by { assert(full::registered(a, n)); }
    }
    if full::quiet(b) {
        assert forall|n: usize| full::registered(a, n) implies match a.control.fibers[n].phase {
            Phase::Inactive => !(exists|v: ISet<Binding>| full::target(a, n, v)),
            Phase::Active => full::coherent(a, n),
            _ => false,
        } by { assert(full::registered(b, n)); }
    }

}

pub open spec fn replay<V>(m: full::Model<V>, states: Seq<full::State<V>>, labels: Seq<(usize, control::Rule)>, initial: full::State<V>) -> Seq<full::State<V>>
    decreases labels.len(),
{
    if labels.len() == 0 { seq![initial] }
    else {
        let prefix = replay(m, states.drop_last(), labels.drop_last(), initial);
        let label = labels.last();
        prefix.push(successor(m, states[states.len() - 2], states.last(), prefix.last(), label.0, label.1))
    }
}

/// A related initial context generates a related entire execution with the
/// same labels. This construction covers every finite prefix of a trace.
pub proof fn execution_simulates<V>(eq: spec_fn(Port, V, V) -> bool, m: full::Model<V>, states: Seq<full::State<V>>, labels: Seq<(usize, control::Rule)>, initial: full::State<V>)
    requires primitives_respect(eq, m), full::execution(m, states, labels), related(eq, states.first(), initial),
        forall|i: int| 0 <= i < states.len() ==> full::shaped(states[i]),
    ensures full::execution(m, replay(m, states, labels, initial), labels),
        replay(m, states, labels, initial).len() == states.len(),
        replay(m, states, labels, initial).first() == initial,
        forall|i: int| 0 <= i < states.len() ==> related(eq, states[i], replay(m, states, labels, initial)[i])
            && full::shaped(replay(m, states, labels, initial)[i]),
    decreases labels.len(),
{
    if labels.len() == 0 {
        related_shaped(eq, states.first(), initial);
        assert forall|i: int| 0 <= i < states.len() implies related(eq, states[i], replay(m, states, labels, initial)[i])
            && full::shaped(replay(m, states, labels, initial)[i]) by {
            assert(i == 0);
        }
    } else {
        let previous = states.drop_last();
        let prefix_labels = labels.drop_last();
        assert(full::execution(m, previous, prefix_labels)) by {
            assert forall|i: int| 0 <= i < prefix_labels.len() implies
                full::step(m, previous[i], previous[i + 1], prefix_labels[i].0, prefix_labels[i].1) by {
                assert(previous[i] == states[i]);
                assert(previous[i + 1] == states[i + 1]);
                assert(prefix_labels[i] == labels[i]);
            }
        }
        assert forall|i: int| 0 <= i < previous.len() implies full::shaped(previous[i]) by {
            assert(previous[i] == states[i]);
        }
        execution_simulates(eq, m, previous, prefix_labels, initial);
        let prefix = replay(m, previous, prefix_labels, initial);
        let label = labels.last();
        assert(full::step(m, previous.last(), states.last(), label.0, label.1));
        assert(related(eq, previous.last(), prefix.last()));
        step_simulates(eq, m, previous.last(), states.last(), prefix.last(), label.0, label.1);
        let out = replay(m, states, labels, initial);
        assert forall|i: int| 0 <= i < states.len() implies related(eq, states[i], out[i]) && full::shaped(out[i]) by {
            if i < previous.len() {
                assert(previous[i] == states[i]);
                assert(out[i] == prefix[i]);
            } else { assert(i == states.len() - 1); }
        }
        assert(full::execution(m, out, labels)) by {
            assert forall|i: int| 0 <= i < labels.len() implies full::step(m, out[i], out[i + 1], labels[i].0, labels[i].1) by {
                if i < prefix_labels.len() {
                    assert(out[i] == prefix[i]);
                    assert(out[i + 1] == prefix[i + 1]);
                    assert(labels[i] == prefix_labels[i]);
                } else { assert(i == labels.len() - 1); }
            }
        }
    }
}

// Generic coinductive iterator relations (Definition 34 and Lemma 35).

#[verifier::reject_recursive_types(S)]
pub struct Iteration<S, I> {
    pub state: S,
    pub undo: spec_fn(S) -> S,
    pub next: Option<I>,
}

pub type IteratorFamily<S, I> = spec_fn(I, S) -> Iteration<S, I>;

pub open spec fn continuation<I>(relation: spec_fn(I, I) -> bool, a: Option<I>, b: Option<I>) -> bool {
    match (a, b) { (Some(x), Some(y)) => relation(x, y), (None, None) => true, _ => false }
}

pub open spec fn bisimulation<S, I>(eq: spec_fn(S, S) -> bool, family: IteratorFamily<S, I>, relation: spec_fn(I, I) -> bool) -> bool {
    forall|i: I, j: I, a: S, b: S| #![trigger family(i, a), family(j, b)]
        relation(i, j) && eq(a, b) ==> {
            let x = family(i, a);
            let y = family(j, b);
            &&& eq(x.state, y.state)
            &&& observation::related_maps(eq, x.undo, y.undo)
            &&& continuation(relation, x.next, y.next)
        }
}

/// The union of all post-fixed relations: a genuinely greatest bisimulation,
/// defined without a depth bound, a finiteness rank or a termination premise.
/// `I = nat` gives the opaque token representation used by `semantics::Model`.
pub open spec fn iterator_related<S, I>(eq: spec_fn(S, S) -> bool, family: IteratorFamily<S, I>, i: I, j: I) -> bool {
    exists|relation: spec_fn(I, I) -> bool| bisimulation(eq, family, relation) && relation(i, j)
}

pub proof fn greatest_bisimulation<S, I>(eq: spec_fn(S, S) -> bool, family: IteratorFamily<S, I>)
    ensures bisimulation(eq, family, |i: I, j: I| iterator_related(eq, family, i, j)),
{
    assert forall|i: I, j: I, a: S, b: S| #![trigger family(i, a), family(j, b)]
        iterator_related(eq, family, i, j) && eq(a, b) implies {
            let x = family(i, a);
            let y = family(j, b);
            &&& eq(x.state, y.state)
            &&& observation::related_maps(eq, x.undo, y.undo)
            &&& continuation(|k: I, l: I| iterator_related(eq, family, k, l), x.next, y.next)
        } by {
        let relation = choose|relation: spec_fn(I, I) -> bool| bisimulation(eq, family, relation) && relation(i, j);
        assert(continuation(relation, family(i, a).next, family(j, b).next));
        match (family(i, a).next, family(j, b).next) {
            (Some(k), Some(l)) => { assert(iterator_related(eq, family, k, l)); },
            _ => { },
        }
    }
}

pub proof fn reversed_bisimulation<S, I>(eq: spec_fn(S, S) -> bool, family: IteratorFamily<S, I>, relation: spec_fn(I, I) -> bool)
    requires crate::calculus::equivalence(eq), bisimulation(eq, family, relation),
    ensures bisimulation(eq, family, |i: I, j: I| relation(j, i)),
{
    assert forall|i: I, j: I, a: S, b: S| #![trigger family(i, a), family(j, b)]
        relation(j, i) && eq(a, b) implies {
            let x = family(i, a);
            let y = family(j, b);
            &&& eq(x.state, y.state)
            &&& observation::related_maps(eq, x.undo, y.undo)
            &&& continuation(|k: I, l: I| relation(l, k), x.next, y.next)
        } by {
        assert(eq(b, a));
        assert(observation::related_maps(eq, family(j, b).undo, family(i, a).undo));
        observation::map_partial_equivalence(eq, family(j, b).undo, family(i, a).undo, family(i, a).undo);
        match (family(i, a).next, family(j, b).next) { (Some(k), Some(l)) => { }, _ => { } }
    }
}

pub proof fn composed_bisimulation<S, I>(eq: spec_fn(S, S) -> bool, family: IteratorFamily<S, I>, left: spec_fn(I, I) -> bool, right: spec_fn(I, I) -> bool)
    requires crate::calculus::equivalence(eq), bisimulation(eq, family, left), bisimulation(eq, family, right),
    ensures bisimulation(eq, family, |i: I, k: I| exists|j: I| #[trigger] left(i, j) && right(j, k)),
{
    let composition = |i: I, k: I| exists|j: I| #[trigger] left(i, j) && right(j, k);
    assert forall|i: I, k: I, a: S, c: S| #![trigger family(i, a), family(k, c)]
        composition(i, k) && eq(a, c) implies {
            let x = family(i, a);
            let z = family(k, c);
            &&& eq(x.state, z.state)
            &&& observation::related_maps(eq, x.undo, z.undo)
            &&& continuation(composition, x.next, z.next)
        } by {
        let j = choose|j: I| #[trigger] left(i, j) && right(j, k);
        let x = family(i, a);
        let y = family(j, c);
        let z = family(k, c);
        assert(eq(c, c));
        assert(eq(x.state, y.state));
        assert(eq(y.state, z.state));
        observation::map_partial_equivalence(eq, x.undo, y.undo, z.undo);
        match (x.next, y.next, z.next) {
            (Some(xn), Some(yn), Some(zn)) => {
                assert(left(xn, yn) && right(yn, zn));
                assert(composition(xn, zn));
            },
            _ => { },
        }
    }
}

/// Lemma 35, including infinite continuations: symmetric/transitive, and every
/// related iterator respects the lifted relation at itself. Reflexivity is
/// deliberately derived only for related members, not asserted universally.
pub proof fn iterator_partial_equivalence<S, I>(eq: spec_fn(S, S) -> bool, family: IteratorFamily<S, I>, i: I, j: I, k: I)
    requires crate::calculus::equivalence(eq),
    ensures iterator_related(eq, family, i, j) ==> iterator_related(eq, family, j, i),
        iterator_related(eq, family, i, j) && iterator_related(eq, family, j, k) ==> iterator_related(eq, family, i, k),
        iterator_related(eq, family, i, j) ==> iterator_related(eq, family, i, i) && iterator_related(eq, family, j, j),
{
    let greatest = |x: I, y: I| iterator_related(eq, family, x, y);
    greatest_bisimulation(eq, family);
    reversed_bisimulation(eq, family, greatest);
    let reversed = |x: I, y: I| greatest(y, x);
    if iterator_related(eq, family, i, j) {
        assert(reversed(j, i));
        assert(iterator_related(eq, family, j, i));
    }
    composed_bisimulation(eq, family, greatest, greatest);
    let composition = |x: I, z: I| exists|y: I| #[trigger] greatest(x, y) && greatest(y, z);
    if iterator_related(eq, family, i, j) && iterator_related(eq, family, j, k) {
        assert(composition(i, k));
        assert(iterator_related(eq, family, i, k));
    }
    if iterator_related(eq, family, i, j) {
        assert(composition(i, i));
        assert(composition(j, j));
        assert(iterator_related(eq, family, i, i));
        assert(iterator_related(eq, family, j, j));
    }
}

pub open spec fn iterator_clause<S, I>(eq: spec_fn(S, S) -> bool, family: IteratorFamily<S, I>, i: I, j: I) -> bool {
    forall|a: S, b: S| #![trigger family(i, a), family(j, b)] eq(a, b) ==> {
        let x = family(i, a);
        let y = family(j, b);
        &&& eq(x.state, y.state)
        &&& observation::related_maps(eq, x.undo, y.undo)
        &&& continuation(|k: I, l: I| iterator_related(eq, family, k, l), x.next, y.next)
    }
}

/// The greatest post-fixed construction satisfies the recursive clause in
/// both directions. Thus the definition is the coinductive fixed point itself,
/// rather than a finite unrolling or an arbitrary chosen bisimulation.
pub proof fn iterator_unfolding<S, I>(eq: spec_fn(S, S) -> bool, family: IteratorFamily<S, I>, i: I, j: I)
    ensures iterator_related(eq, family, i, j) == iterator_clause(eq, family, i, j),
{
    greatest_bisimulation(eq, family);
    if iterator_clause(eq, family, i, j) {
        let enlarged = |k: I, l: I| iterator_related(eq, family, k, l) || (k == i && l == j);
        assert(bisimulation(eq, family, enlarged)) by {
            assert forall|k: I, l: I, a: S, b: S| #![trigger family(k, a), family(l, b)]
                enlarged(k, l) && eq(a, b) implies {
                    let x = family(k, a);
                    let y = family(l, b);
                    &&& eq(x.state, y.state)
                    &&& observation::related_maps(eq, x.undo, y.undo)
                    &&& continuation(enlarged, x.next, y.next)
                } by {
                if !iterator_related(eq, family, k, l) { assert(k == i && l == j); }
                match (family(k, a).next, family(l, b).next) {
                    (Some(next_k), Some(next_l)) => {
                        assert(iterator_related(eq, family, next_k, next_l));
                        assert(enlarged(next_k, next_l));
                    },
                    _ => { },
                }
            }
        }
        assert(enlarged(i, j));
        assert(iterator_related(eq, family, i, j));
    }
}

} // verus!
