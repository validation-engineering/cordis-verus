//! Equivariance under arbitrary bijective renaming of fiber identities.
//!
//! Service ports and values are unchanged. Registry keys, parents and committed
//! provider identities are transported together; allocation order is erased.
#[cfg(verus_keep_ghost)]
use crate::{refinement as control, semantics as full, Binding, Phase, Port};
use vstd::prelude::*;

verus! {

pub struct Renaming {
    pub forward: spec_fn(usize) -> usize,
    pub backward: spec_fn(usize) -> usize,
}

pub open spec fn bijective(r: Renaming) -> bool {
    &&& forall|n: usize| #[trigger] (r.backward)((r.forward)(n)) == n
    &&& forall|n: usize| #[trigger] (r.forward)((r.backward)(n)) == n
}

pub open spec fn inverse(r: Renaming) -> Renaming {
    Renaming { forward: r.backward, backward: r.forward }
}

pub open spec fn parent(r: Renaming, p: Option<usize>) -> Option<usize> {
    match p { Some(n) => Some((r.forward)(n)), None => None }
}

pub open spec fn binding(r: Renaming, b: Binding) -> Binding {
    Binding { key: b.key, realm: b.realm, provider: (r.forward)(b.provider) }
}

pub open spec fn view(r: Renaming, v: ISet<Binding>) -> ISet<Binding> {
    ISet::new(|b: Binding| v.contains(binding(inverse(r), b)))
}

pub open spec fn fiber(r: Renaming, f: control::Fiber) -> control::Fiber {
    control::Fiber { parent: parent(r, f.parent), retired: f.retired,
        phase: f.phase, dependencies: f.dependencies, provisions: f.provisions,
        committed: view(r, f.committed) }
}

pub open spec fn rename(r: Renaming, s: control::State) -> control::State {
    control::State { fibers: IMap::new(
        |n: usize| control::registered(s, (r.backward)(n)),
        |n: usize| fiber(r, s.fibers[(r.backward)(n)])) }
}

pub proof fn observations(r: Renaming, s: control::State, n: usize)
    requires bijective(r),
    ensures control::registered(rename(r, s), (r.forward)(n)) == control::registered(s, n),
        control::registered(s, n) ==> rename(r, s).fibers[(r.forward)(n)] == fiber(r, s.fibers[n]),
        forall|b: Binding| view(r, s.fibers[n].committed).contains(binding(r, b)) == s.fibers[n].committed.contains(b),
{ }

pub proof fn view_empty(r: Renaming, v: ISet<Binding>)
    requires bijective(r),
    ensures view(r, v).is_empty() == v.is_empty(),
{
    if v.is_empty() {
        assert forall|b: Binding| !view(r, v).contains(b) by { }
    } else {
        let b = choose|b: Binding| v.contains(b);
        assert(view(r, v).contains(binding(r, b)));
    }
}

pub proof fn target_forward(r: Renaming, s: control::State, n: usize, v: ISet<Binding>)
    requires bijective(r), control::target(s, n, v),
    ensures control::target(rename(r, s), (r.forward)(n), view(r, v)),
{
    observations(r, s, n);
    assert forall|b: Binding| view(r, v).contains(b) implies
        rename(r, s).fibers[(r.forward)(n)].dependencies.contains(Port { key: b.key, realm: b.realm })
        && control::publishes(rename(r, s), Port { key: b.key, realm: b.realm }, b.provider) by {
        let old = binding(inverse(r), b);
        assert(v.contains(old));
        observations(r, s, old.provider);
    }
    assert forall|p: Port| #[trigger] rename(r, s).fibers[(r.forward)(n)].dependencies.contains(p) implies
        exists|b: Binding| view(r, v).contains(b) && b.key == p.key && b.realm == p.realm by {
        let b = choose|b: Binding| v.contains(b) && b.key == p.key && b.realm == p.realm;
        assert(view(r, v).contains(binding(r, b)));
    }
}

pub proof fn round_trip(r: Renaming, s: control::State, v: ISet<Binding>)
    requires bijective(r),
    ensures bijective(inverse(r)), view(inverse(r), view(r, v)) == v,
        rename(inverse(r), rename(r, s)) == s,
{
    assert(view(inverse(r), view(r, v)) =~= v);
    assert(rename(inverse(r), rename(r, s)).fibers =~= s.fibers) by {
        assert forall|n: usize| control::registered(s, n) implies
            rename(inverse(r), rename(r, s)).fibers[n] == s.fibers[n] by {
            let f = s.fibers[n];
            assert(view(inverse(r), view(r, f.committed)) =~= f.committed);
            match f.parent { Some(p) => { }, None => { } }
        }
    }
}

pub proof fn target_equivariant(r: Renaming, s: control::State, n: usize, v: ISet<Binding>)
    requires bijective(r),
    ensures control::target(s, n, v) == control::target(rename(r, s), (r.forward)(n), view(r, v)),
{
    if control::target(s, n, v) { target_forward(r, s, n, v); }
    if control::target(rename(r, s), (r.forward)(n), view(r, v)) {
        round_trip(r, s, v);
        target_forward(inverse(r), rename(r, s), (r.forward)(n), view(r, v));
    }
}

pub proof fn relied_equivariant(r: Renaming, s: control::State, n: usize)
    requires bijective(r),
    ensures control::relied(s, n) == control::relied(rename(r, s), (r.forward)(n)),
{
    if control::relied(s, n) {
        let (m, b) = choose|m: usize, b: Binding| control::registered(s, m) && m != n
            && s.fibers[m].phase != Phase::Inactive && s.fibers[m].committed.contains(b) && b.provider == n;
        observations(r, s, m);
        assert((r.forward)(m) != (r.forward)(n));
        assert(rename(r, s).fibers[(r.forward)(m)].committed.contains(binding(r, b)));
    }
    if control::relied(rename(r, s), (r.forward)(n)) {
        let (m, b) = choose|m: usize, b: Binding| control::registered(rename(r, s), m) && m != (r.forward)(n)
            && rename(r, s).fibers[m].phase != Phase::Inactive
            && rename(r, s).fibers[m].committed.contains(b) && b.provider == (r.forward)(n);
        let old_m = (r.backward)(m);
        let old_b = binding(inverse(r), b);
        assert(old_m != n);
        assert(s.fibers[old_m].committed.contains(old_b));
        assert(old_b.provider == n);
    }
}

pub proof fn frame_forward(r: Renaming, a: control::State, z: control::State, n: usize)
    requires bijective(r), control::frame(a, z, n),
    ensures control::frame(rename(r, a), rename(r, z), (r.forward)(n)),
{
    assert forall|m: usize| m != (r.forward)(n) implies
        control::registered(rename(r, a), m) == control::registered(rename(r, z), m)
        && (control::registered(rename(r, a), m) ==> rename(r, a).fibers[m] == rename(r, z).fibers[m]) by {
        assert((r.backward)(m) != n);
    }
}

pub proof fn step_forward(r: Renaming, a: control::State, z: control::State, n: usize, rule: control::Rule)
    requires bijective(r), control::step(a, z, n, rule),
    ensures control::step(rename(r, a), rename(r, z), (r.forward)(n), rule),
{
    observations(r, a, n);
    observations(r, z, n);
    if control::frame(a, z, n) { frame_forward(r, a, z, n); }
    match rule {
        control::Rule::Insert => {
            view_empty(r, z.fibers[n].committed);
            match z.fibers[n].parent { Some(p) => { observations(r, a, p); }, None => { } }
            assert forall|m: usize, p: Port| control::registered(rename(r, a), m)
                && rename(r, a).fibers[m].provisions.contains(p) implies
                !rename(r, z).fibers[(r.forward)(n)].provisions.contains(p) by {
                assert(control::registered(a, (r.backward)(m)));
            }
        },
        control::Rule::Remove => {
            view_empty(r, a.fibers[n].committed);
            assert forall|m: usize| control::registered(rename(r, a), m) implies
                rename(r, a).fibers[m].parent != Some((r.forward)(n)) by {
                match a.fibers[(r.backward)(m)].parent {
                    Some(p) => { assert(p != n); }, None => { }
                }
            }
        },
        control::Rule::Begin => { target_equivariant(r, a, n, z.fibers[n].committed); },
        control::Rule::Unload => {
            view_empty(r, z.fibers[n].committed);
            relied_equivariant(r, a, n);
        },
        control::Rule::Iter | control::Rule::Finish | control::Rule::Divert | control::Rule::Leave => {
            target_equivariant(r, a, n, a.fibers[n].committed);
        },
        _ => { },
    }
}

pub proof fn step_equivariant(r: Renaming, a: control::State, z: control::State, n: usize, rule: control::Rule)
    requires bijective(r),
    ensures control::step(a, z, n, rule) == control::step(rename(r, a), rename(r, z), (r.forward)(n), rule),
{
    if control::step(a, z, n, rule) { step_forward(r, a, z, n, rule); }
    if control::step(rename(r, a), rename(r, z), (r.forward)(n), rule) {
        round_trip(r, a, a.fibers[n].committed);
        round_trip(r, z, z.fibers[n].committed);
        step_forward(inverse(r), rename(r, a), rename(r, z), (r.forward)(n), rule);
    }
}

/// Parent well-foundedness is transported, not inferred from numeric name order.
/// The finite name bound remains available because executable identities are
/// `usize`; a permutation need not preserve the original bound.
pub proof fn well_formed_forward(r: Renaming, s: control::State)
    requires bijective(r), control::well_formed(s),
    ensures control::well_formed(rename(r, s)),
{
    let z = rename(r, s);
    let limit = (usize::MAX as nat) + 1;
    assert(control::name_bound(z, limit));
    let rank = choose|rank: spec_fn(usize) -> nat| control::parent_ranking(s, rank);
    let transported = |n: usize| rank((r.backward)(n));
    assert forall|n: usize| control::registered(z, n) implies match z.fibers[n].parent {
        Some(p) => control::registered(z, p), None => true,
    } by {
        match s.fibers[(r.backward)(n)].parent {
            Some(p) => { observations(r, s, p); }, None => { }
        }
    }
    assert(control::parent_ranking(z, transported)) by {
        assert forall|n: usize| control::registered(z, n) implies match z.fibers[n].parent {
            Some(p) => transported(p) < transported(n), None => true,
        } by {
            match s.fibers[(r.backward)(n)].parent { Some(p) => { }, None => { } }
        }
    }
    assert forall|n: usize, m: usize, p: Port| control::registered(z, n) && control::registered(z, m)
        && z.fibers[n].provisions.contains(p) && z.fibers[m].provisions.contains(p) implies n == m by {
        assert((r.backward)(n) == (r.backward)(m));
        assert((r.forward)((r.backward)(n)) == n);
        assert((r.forward)((r.backward)(m)) == m);
    }
    assert forall|n: usize, b: Binding| control::registered(z, n) && z.fibers[n].committed.contains(b) implies {
        &&& z.fibers[n].phase != Phase::Inactive
        &&& z.fibers[n].dependencies.contains(Port { key: b.key, realm: b.realm })
        &&& control::registered(z, b.provider) && z.fibers[b.provider].phase != Phase::Inactive
        &&& z.fibers[b.provider].provisions.contains(Port { key: b.key, realm: b.realm })
        &&& b.provider != n
    } by {
        let old_n = (r.backward)(n);
        let old_b = binding(inverse(r), b);
        assert(s.fibers[old_n].committed.contains(old_b));
        assert(old_b.provider != old_n);
    }
    assert forall|n: usize, p: Port| control::registered(z, n) && z.fibers[n].phase != Phase::Inactive
        && z.fibers[n].dependencies.contains(p) implies exists|b: Binding|
        z.fibers[n].committed.contains(b) && b.key == p.key && b.realm == p.realm by {
        let old_n = (r.backward)(n);
        let b = choose|b: Binding| s.fibers[old_n].committed.contains(b) && b.key == p.key && b.realm == p.realm;
        assert(z.fibers[n].committed.contains(binding(r, b)));
    }
    assert forall|n: usize, a: Binding, b: Binding| control::registered(z, n)
        && z.fibers[n].committed.contains(a) && z.fibers[n].committed.contains(b)
        && a.key == b.key && a.realm == b.realm implies a.provider == b.provider by {
        let old_n = (r.backward)(n);
        let old_a = binding(inverse(r), a);
        let old_b = binding(inverse(r), b);
        assert(s.fibers[old_n].committed.contains(old_a));
        assert(s.fibers[old_n].committed.contains(old_b));
        assert(old_a.provider == old_b.provider);
    }
}

pub proof fn well_formed_equivariant(r: Renaming, s: control::State)
    requires bijective(r),
    ensures control::well_formed(s) == control::well_formed(rename(r, s)),
{
    if control::well_formed(s) { well_formed_forward(r, s); }
    if control::well_formed(rename(r, s)) {
        round_trip(r, s, ISet::empty());
        well_formed_forward(inverse(r), rename(r, s));
    }
}

pub open spec fn rename_states(r: Renaming, states: Seq<control::State>) -> Seq<control::State> {
    Seq::new(states.len(), |i: int| rename(r, states[i]))
}

pub open spec fn rename_labels(r: Renaming, labels: Seq<(usize, control::Rule)>) -> Seq<(usize, control::Rule)> {
    Seq::new(labels.len(), |i: int| ((r.forward)(labels[i].0), labels[i].1))
}

/// The labels retain their rule constructors: renaming cannot turn a restart
/// extension into a paper rule or change the length of an execution.
pub proof fn execution_equivariant(r: Renaming, states: Seq<control::State>, labels: Seq<(usize, control::Rule)>, allow_restart: bool)
    requires bijective(r),
    ensures control::execution(states, labels, allow_restart)
        == control::execution(rename_states(r, states), rename_labels(r, labels), allow_restart),
{
    assert forall|i: int| 0 <= i < labels.len() && i + 1 < states.len() implies
        control::labelled_step(states[i], states[i + 1], labels[i], allow_restart)
        == control::labelled_step(rename_states(r, states)[i], rename_states(r, states)[i + 1],
            rename_labels(r, labels)[i], allow_restart) by {
        step_equivariant(r, states[i], states[i + 1], labels[i].0, labels[i].1);
    }
}

pub proof fn reaches_forward(r: Renaming, a: control::State, z: control::State, count: nat, allow_restart: bool)
    requires bijective(r), control::reaches(a, z, count, allow_restart),
    ensures control::reaches(rename(r, a), rename(r, z), count, allow_restart),
    decreases count,
{
    if count > 0 {
        let (middle, label) = choose|middle: control::State, label: (usize, control::Rule)|
            control::labelled_step(middle, z, label, allow_restart)
            && control::reaches(a, middle, (count - 1) as nat, allow_restart);
        reaches_forward(r, a, middle, (count - 1) as nat, allow_restart);
        step_forward(r, middle, z, label.0, label.1);
        assert(control::labelled_step(rename(r, middle), rename(r, z), ((r.forward)(label.0), label.1), allow_restart));
    }
}

pub proof fn reaches_equivariant(r: Renaming, a: control::State, z: control::State, count: nat, allow_restart: bool)
    requires bijective(r),
    ensures control::reaches(a, z, count, allow_restart)
        == control::reaches(rename(r, a), rename(r, z), count, allow_restart),
{
    if control::reaches(a, z, count, allow_restart) { reaches_forward(r, a, z, count, allow_restart); }
    if control::reaches(rename(r, a), rename(r, z), count, allow_restart) {
        round_trip(r, a, ISet::empty());
        round_trip(r, z, ISet::empty());
        reaches_forward(inverse(r), rename(r, a), rename(r, z), count, allow_restart);
    }
}

pub open spec fn indexed<T>(r: Renaming, m: IMap<usize, T>) -> IMap<usize, T> {
    IMap::new(|n: usize| m.dom().contains((r.backward)(n)), |n: usize| m[(r.backward)(n)])
}

pub open spec fn context<V>(r: Renaming, s: full::State<V>) -> full::State<V> {
    full::State { control: rename(r, s.control), tables: indexed(r, s.tables),
        effects: indexed(r, s.effects), iterators: indexed(r, s.iterators),
        accumulators: indexed(r, s.accumulators) }
}

/// Tokens retain their identities while their interpreted functions are
/// conjugated. This implements renaming of opaque effects, continuations and
/// inverse maps, without requiring service values to expose a name structure.
pub open spec fn model<V>(r: Renaming, m: full::Model<V>) -> full::Model<V> {
    full::Model {
        iterate: |n: usize, k: nat, s: full::State<V>| {
            let y = (m.iterate)((r.backward)(n), k, context(inverse(r), s));
            full::Yield { state: context(r, y.state), inverse: y.inverse, next: y.next }
        },
        undo: |k: nat, s: full::State<V>| context(r, (m.undo)(k, context(inverse(r), s))),
    }
}

/// A primitive iterator must retain its own fiber. Recovery maps may retire a
/// child but cannot erase arbitrary registry entries. These are name-safety
/// contracts, not an equivariance premise or a whole-execution assumption.
pub open spec fn preserves_names<V>(m: full::Model<V>) -> bool {
    &&& forall|n: usize, k: nat, s: full::State<V>| full::registered(s, n)
        ==> #[trigger] full::registered((m.iterate)(n, k, s).state, n)
    &&& forall|n: usize, k: nat, s: full::State<V>| full::registered(s, n)
        ==> #[trigger] full::registered((m.undo)(k, s), n)
}

pub proof fn indexed_round_trip<T>(r: Renaming, m: IMap<usize, T>)
    requires bijective(r),
    ensures indexed(inverse(r), indexed(r, m)) == m,
{
    assert(indexed(inverse(r), indexed(r, m)) =~= m);
}

pub proof fn indexed_remove<T>(r: Renaming, m: IMap<usize, T>, n: usize)
    requires bijective(r),
    ensures indexed(r, m.remove(n)) == indexed(r, m).remove((r.forward)(n)),
{
    assert(indexed(r, m.remove(n)) =~= indexed(r, m).remove((r.forward)(n))) by {
        assert forall|x: usize| x == (r.forward)(n) <==> #[trigger] (r.backward)(x) == n by {
            assert((r.forward)((r.backward)(x)) == x);
        }
    }
}

pub proof fn indexed_insert<T>(r: Renaming, m: IMap<usize, T>, n: usize, value: T)
    requires bijective(r),
    ensures indexed(r, m.insert(n, value)) == indexed(r, m).insert((r.forward)(n), value),
{
    assert(indexed(r, m.insert(n, value)) =~= indexed(r, m).insert((r.forward)(n), value)) by {
        assert forall|x: usize| x == (r.forward)(n) <==> #[trigger] (r.backward)(x) == n by {
            assert((r.forward)((r.backward)(x)) == x);
        }
    }
}

pub proof fn context_round_trip<V>(r: Renaming, s: full::State<V>)
    requires bijective(r),
    ensures context(inverse(r), context(r, s)) == s, bijective(inverse(r)),
{
    round_trip(r, s.control, ISet::empty());
    indexed_round_trip(r, s.tables);
    indexed_round_trip(r, s.effects);
    indexed_round_trip(r, s.iterators);
    indexed_round_trip(r, s.accumulators);
}

pub proof fn shaped_forward<V>(r: Renaming, s: full::State<V>)
    requires bijective(r), full::shaped(s),
    ensures full::shaped(context(r, s)),
{
    let z = context(r, s);
    assert(z.tables.dom() =~= z.control.fibers.dom());
    assert(z.effects.dom() =~= z.control.fibers.dom());
    assert(z.iterators.dom() =~= z.control.fibers.dom());
    assert(z.accumulators.dom() =~= z.control.fibers.dom());
    assert forall|n: usize| full::registered(z, n) implies {
        &&& z.tables[n].dom().subset_of(z.control.fibers[n].provisions)
        &&& (z.control.fibers[n].phase == Phase::Inactive ==> z.iterators[n].is_none()
            && z.accumulators[n].len() == 0 && z.control.fibers[n].committed.is_empty())
        &&& (z.control.fibers[n].phase == Phase::Loading ==> z.iterators[n].is_some())
        &&& (z.control.fibers[n].phase == Phase::Active || z.control.fibers[n].phase == Phase::Unloading
            ==> z.iterators[n].is_none())
    } by {
        assert(full::registered(s, (r.backward)(n)));
        view_empty(r, s.control.fibers[(r.backward)(n)].committed);
    }
}

pub proof fn full_target_forward<V>(r: Renaming, s: full::State<V>, n: usize, v: ISet<Binding>)
    requires bijective(r), full::shaped(s), full::target(s, n, v),
    ensures full::target(context(r, s), (r.forward)(n), view(r, v)),
{
    observations(r, s.control, n);
    assert forall|b: Binding| view(r, v).contains(b) implies
        context(r, s).control.fibers[(r.forward)(n)].dependencies.contains(Port { key: b.key, realm: b.realm })
        && full::publishes(context(r, s), Port { key: b.key, realm: b.realm }, b.provider) by {
        let old = binding(inverse(r), b);
        assert(v.contains(old));
        observations(r, s.control, old.provider);
    }
    assert forall|p: Port| #[trigger] context(r, s).control.fibers[(r.forward)(n)].dependencies.contains(p) implies
        exists|b: Binding| view(r, v).contains(b) && b.key == p.key && b.realm == p.realm by {
        let b = choose|b: Binding| v.contains(b) && b.key == p.key && b.realm == p.realm;
        assert(view(r, v).contains(binding(r, b)));
    }
}

pub proof fn full_target_equivariant<V>(r: Renaming, s: full::State<V>, n: usize, v: ISet<Binding>)
    requires bijective(r), full::shaped(s),
    ensures full::target(s, n, v) == full::target(context(r, s), (r.forward)(n), view(r, v)),
{
    if full::target(s, n, v) { full_target_forward(r, s, n, v); }
    if full::target(context(r, s), (r.forward)(n), view(r, v)) {
        context_round_trip(r, s);
        round_trip(r, s.control, v);
        shaped_forward(r, s);
        full_target_forward(inverse(r), context(r, s), (r.forward)(n), view(r, v));
    }
}

pub proof fn edit_commutes<V>(r: Renaming, s: full::State<V>, n: usize, phase: Phase,
    committed: ISet<Binding>, iterator: Option<nat>, accumulator: Seq<nat>)
    requires bijective(r), full::registered(s, n),
    ensures context(r, full::edit(s, n, phase, committed, iterator, accumulator))
        == full::edit(context(r, s), (r.forward)(n), phase, view(r, committed), iterator, accumulator),
{
    let left = context(r, full::edit(s, n, phase, committed, iterator, accumulator));
    let right = full::edit(context(r, s), (r.forward)(n), phase, view(r, committed), iterator, accumulator);
    observations(r, s.control, n);
    assert(left.control.fibers =~= right.control.fibers) by {
        assert forall|x: usize| x == (r.forward)(n) <==> #[trigger] (r.backward)(x) == n by {
            assert((r.forward)((r.backward)(x)) == x);
        }
    }
    indexed_insert(r, s.iterators, n, iterator);
    indexed_insert(r, s.accumulators, n, accumulator);
}

pub proof fn restore_names<V>(m: full::Model<V>, tokens: Seq<nat>, s: full::State<V>, n: usize)
    requires preserves_names(m), full::registered(s, n),
    ensures full::registered(full::restore(m, tokens, s), n),
    decreases tokens.len(),
{
    if tokens.len() > 0 {
        restore_names(m, tokens.drop_last(), (m.undo)(tokens.last(), s), n);
    }
}

pub proof fn restore_commutes<V>(r: Renaming, m: full::Model<V>, tokens: Seq<nat>, s: full::State<V>)
    requires bijective(r),
    ensures context(r, full::restore(m, tokens, s)) == full::restore(model(r, m), tokens, context(r, s)),
    decreases tokens.len(),
{
    context_round_trip(r, s);
    if tokens.len() > 0 {
        restore_commutes(r, m, tokens.drop_last(), (m.undo)(tokens.last(), s));
    }
}

pub proof fn full_frame_forward<V>(r: Renaming, a: full::State<V>, z: full::State<V>, n: usize)
    requires bijective(r), full::shaped(a), full::shaped(z), full::auxiliary_frame(a, z, n),
        control::frame(a.control, z.control, n),
    ensures full::auxiliary_frame(context(r, a), context(r, z), (r.forward)(n)),
{
    assert forall|m: usize| m != (r.forward)(n) && full::registered(context(r, a), m) implies
        context(r, z).tables[m] == context(r, a).tables[m]
        && context(r, z).effects[m] == context(r, a).effects[m]
        && context(r, z).iterators[m] == context(r, a).iterators[m]
        && context(r, z).accumulators[m] == context(r, a).accumulators[m] by {
        assert((r.backward)(m) != n);
        assert(full::registered(a, (r.backward)(m)));
        assert(full::registered(z, (r.backward)(m)));
    }
}

/// All nine value-carrying rules commute with renaming. The theorem transports
/// actual yielded contexts and reverse-order accumulator interpretation; it
/// does not replace effect transitions by their erased control projection.
pub proof fn full_step_forward<V>(r: Renaming, m: full::Model<V>, a: full::State<V>, z: full::State<V>, n: usize, rule: control::Rule)
    requires bijective(r), preserves_names(m), full::shaped(a), full::shaped(z), full::step(m, a, z, n, rule),
    ensures full::step(model(r, m), context(r, a), context(r, z), (r.forward)(n), rule),
{
    observations(r, a.control, n);
    observations(r, z.control, n);
    context_round_trip(r, a);
    match rule {
        control::Rule::Insert => {
            step_forward(r, a.control, z.control, n, rule);
            shaped_forward(r, z);
            full_frame_forward(r, a, z, n);
        },
        control::Rule::Retire => { step_forward(r, a.control, z.control, n, rule); },
        control::Rule::Remove => {
            step_forward(r, a.control, z.control, n, rule);
            indexed_remove(r, a.tables, n);
            indexed_remove(r, a.effects, n);
            indexed_remove(r, a.iterators, n);
            indexed_remove(r, a.accumulators, n);
        },
        control::Rule::Begin => {
            full_target_equivariant(r, a, n, z.control.fibers[n].committed);
            edit_commutes(r, a, n, Phase::Loading, z.control.fibers[n].committed, Some(a.effects[n]), Seq::empty());
        },
        control::Rule::Iter | control::Rule::Finish | control::Rule::Divert => {
            let y = (m.iterate)(n, a.iterators[n].unwrap(), a);
            full_target_equivariant(r, a, n, a.control.fibers[n].committed);
            assert(full::registered(y.state, n));
            if rule == control::Rule::Iter {
                edit_commutes(r, y.state, n, Phase::Loading, a.control.fibers[n].committed, y.next, a.accumulators[n].push(y.inverse));
            } else if rule == control::Rule::Finish {
                edit_commutes(r, y.state, n, Phase::Active, a.control.fibers[n].committed, None, a.accumulators[n].push(y.inverse));
            } else {
                edit_commutes(r, a, n, Phase::Unloading, a.control.fibers[n].committed, None, a.accumulators[n]);
                edit_commutes(r, y.state, n, Phase::Unloading, a.control.fibers[n].committed, None, a.accumulators[n].push(y.inverse));
            }
        },
        control::Rule::Leave => {
            full_target_equivariant(r, a, n, a.control.fibers[n].committed);
            edit_commutes(r, a, n, Phase::Unloading, a.control.fibers[n].committed, None, a.accumulators[n]);
        },
        control::Rule::Unload => {
            relied_equivariant(r, a.control, n);
            restore_names(m, a.accumulators[n], a, n);
            restore_commutes(r, m, a.accumulators[n], a);
            view_empty(r, ISet::empty());
            assert(view(r, ISet::empty()) =~= ISet::empty());
            edit_commutes(r, full::restore(m, a.accumulators[n], a), n, Phase::Inactive, ISet::empty(), None, Seq::empty());
        },
        _ => { },
    }
}

pub proof fn model_round_trip<V>(r: Renaming, m: full::Model<V>)
    requires bijective(r),
    ensures model(inverse(r), model(r, m)) == m,
{
    let z = model(inverse(r), model(r, m));
    assert(z.iterate =~= m.iterate) by {
        assert forall|n: usize, k: nat, s: full::State<V>| #[trigger] (z.iterate)(n, k, s) == (m.iterate)(n, k, s) by {
            context_round_trip(r, s);
            context_round_trip(r, (m.iterate)(n, k, s).state);
        }
    }
    assert(z.undo =~= m.undo) by {
        assert forall|k: nat, s: full::State<V>| #[trigger] (z.undo)(k, s) == (m.undo)(k, s) by {
            context_round_trip(r, s);
            context_round_trip(r, (m.undo)(k, s));
        }
    }
}

pub proof fn names_forward<V>(r: Renaming, m: full::Model<V>)
    requires bijective(r), preserves_names(m),
    ensures preserves_names(model(r, m)),
{
    let z = model(r, m);
    assert forall|n: usize, k: nat, s: full::State<V>| full::registered(s, n)
        implies #[trigger] full::registered((z.iterate)(n, k, s).state, n) by {
        assert(full::registered(context(inverse(r), s), (r.backward)(n)));
        assert(full::registered((m.iterate)((r.backward)(n), k, context(inverse(r), s)).state, (r.backward)(n)));
    }
    assert forall|n: usize, k: nat, s: full::State<V>| full::registered(s, n)
        implies #[trigger] full::registered((z.undo)(k, s), n) by {
        assert(full::registered(context(inverse(r), s), (r.backward)(n)));
        assert(full::registered((m.undo)(k, context(inverse(r), s)), (r.backward)(n)));
    }
}

pub proof fn full_step_equivariant<V>(r: Renaming, m: full::Model<V>, a: full::State<V>, z: full::State<V>, n: usize, rule: control::Rule)
    requires bijective(r), preserves_names(m), full::shaped(a), full::shaped(z),
    ensures full::step(m, a, z, n, rule)
        == full::step(model(r, m), context(r, a), context(r, z), (r.forward)(n), rule),
{
    if full::step(m, a, z, n, rule) { full_step_forward(r, m, a, z, n, rule); }
    if full::step(model(r, m), context(r, a), context(r, z), (r.forward)(n), rule) {
        context_round_trip(r, a);
        context_round_trip(r, z);
        model_round_trip(r, m);
        names_forward(r, m);
        shaped_forward(r, a);
        shaped_forward(r, z);
        full_step_forward(inverse(r), model(r, m), context(r, a), context(r, z), (r.forward)(n), rule);
    }
}

pub open spec fn contexts<V>(r: Renaming, states: Seq<full::State<V>>) -> Seq<full::State<V>> {
    Seq::new(states.len(), |i: int| context(r, states[i]))
}

/// The finite trace includes full contexts and the actual rule labels. All
/// prefixes are required to be well shaped, exactly as in a paper execution;
/// no claim is made that an arbitrary opaque Model preserves those conditions.
pub proof fn full_execution_equivariant<V>(r: Renaming, m: full::Model<V>, states: Seq<full::State<V>>, labels: Seq<(usize, control::Rule)>)
    requires bijective(r), preserves_names(m),
        forall|i: int| 0 <= i < states.len() ==> full::shaped(states[i]),
    ensures full::execution(m, states, labels) == full::execution(model(r, m), contexts(r, states), rename_labels(r, labels)),
        forall|i: int| 0 <= i < states.len() ==> full::shaped(contexts(r, states)[i]),
{
    assert forall|i: int| 0 <= i < states.len() implies full::shaped(contexts(r, states)[i]) by {
        shaped_forward(r, states[i]);
    }
    assert forall|i: int| 0 <= i < labels.len() && i + 1 < states.len() implies
        full::step(m, states[i], states[i + 1], labels[i].0, labels[i].1)
        == full::step(model(r, m), contexts(r, states)[i], contexts(r, states)[i + 1],
            rename_labels(r, labels)[i].0, rename_labels(r, labels)[i].1) by {
        full_step_equivariant(r, m, states[i], states[i + 1], labels[i].0, labels[i].1);
    }
}

pub proof fn full_execution_reaches<V>(r: Renaming, m: full::Model<V>, states: Seq<full::State<V>>, labels: Seq<(usize, control::Rule)>)
    requires bijective(r), preserves_names(m), full::execution(m, states, labels),
        forall|i: int| 0 <= i < states.len() ==> full::shaped(states[i]),
    ensures full::reaches(model(r, m), context(r, states.first()), context(r, states.last()), labels.len()),
{
    full_execution_equivariant(r, m, states, labels);
    full::execution_reaches(model(r, m), contexts(r, states), rename_labels(r, labels));
}

pub proof fn confined_write_forward<V>(r: Renaming, a: full::State<V>, z: full::State<V>, n: usize)
    requires bijective(r), full::shaped(a), full::shaped(z), full::registered(a, n), full::confined_write(a, z, n),
    ensures full::confined_write(context(r, a), context(r, z), (r.forward)(n)),
{
    observations(r, a.control, n);
    assert(context(r, a).tables.dom() =~= context(r, z).tables.dom());
    assert forall|x: usize| full::registered(context(r, a), x) && x != (r.forward)(n) implies {
        &&& context(r, a).tables[x].dom() == context(r, z).tables[x].dom()
        &&& forall|p: Port| context(r, a).tables[x].dom().contains(p)
            && !context(r, a).control.fibers[(r.forward)(n)].dependencies.contains(p)
            ==> context(r, a).tables[x][p] == context(r, z).tables[x][p]
    } by {
        let old = (r.backward)(x);
        assert(old != n);
        assert(full::registered(a, old));
        assert(full::registered(z, old));
        assert forall|p: Port| context(r, a).tables[x].dom().contains(p)
            && !context(r, a).control.fibers[(r.forward)(n)].dependencies.contains(p)
            implies context(r, a).tables[x][p] == context(r, z).tables[x][p] by {
            assert(a.tables[old].dom().contains(p));
        }
    }
}

pub proof fn child_insert_forward<V>(r: Renaming, a: full::State<V>, z: full::State<V>, owner: usize, child: usize)
    requires bijective(r), full::shaped(a), full::child_insert(a, z, owner, child),
    ensures full::child_insert(context(r, a), context(r, z), (r.forward)(owner), (r.forward)(child)),
{
    step_forward(r, a.control, z.control, child, control::Rule::Insert);
    shaped_forward(r, z);
    full_frame_forward(r, a, z, child);
    observations(r, z.control, child);
}

pub proof fn child_retire_forward<V>(r: Renaming, a: full::State<V>, z: full::State<V>, child: usize)
    requires bijective(r), full::child_retire(a, z, child),
    ensures full::child_retire(context(r, a), context(r, z), (r.forward)(child)),
{
    step_forward(r, a.control, z.control, child, control::Rule::Retire);
}

pub proof fn context_iteration_forward<V>(r: Renaming, a: full::State<V>, y: full::Yield<V>, owner: usize)
    requires bijective(r), full::shaped(a), full::shaped(y.state), full::registered(a, owner),
        full::context_iteration(a, y, owner),
    ensures full::context_iteration(context(r, a), full::Yield { state: context(r, y.state), inverse: y.inverse, next: y.next }, (r.forward)(owner)),
{
    if full::confined_write(a, y.state, owner) {
        confined_write_forward(r, a, y.state, owner);
    } else {
        let child = choose|child: usize| full::child_insert(a, y.state, owner, child);
        child_insert_forward(r, a, y.state, owner, child);
    }
}

/// Actor preservation follows from the two actual primitive effect forms,
/// including a newly created child. It is not an extra condition on an
/// otherwise unconstrained future lifecycle execution.
pub proof fn primitive_iteration_preserves_actor<V>(a: full::State<V>, y: full::Yield<V>, owner: usize)
    requires full::registered(a, owner), full::context_iteration(a, y, owner),
    ensures full::registered(y.state, owner),
{
    if !full::confined_write(a, y.state, owner) {
        let child = choose|child: usize| full::child_insert(a, y.state, owner, child);
        assert(child != owner);
    }
}

pub proof fn child_recovery_preserves_names<V>(a: full::State<V>, z: full::State<V>, child: usize)
    requires full::child_retire(a, z, child),
    ensures a.control.fibers.dom() == z.control.fibers.dom(),
{
    assert(a.control.fibers.dom() =~= z.control.fibers.dom()) by {
        assert forall|n: usize| a.control.fibers.dom().contains(n) == z.control.fibers.dom().contains(n) by {
            assert(control::registered(a.control, n) == control::registered(z.control, n));
        }
    };
}

pub proof fn quiet_forward(r: Renaming, s: control::State)
    requires bijective(r), control::quiet(s),
    ensures control::quiet(rename(r, s)),
{
    assert forall|n: usize| control::registered(rename(r, s), n) implies match rename(r, s).fibers[n].phase {
        Phase::Inactive => !(exists|v: ISet<Binding>| control::target(rename(r, s), n, v)),
        Phase::Active => control::coherent(rename(r, s), n),
        _ => false,
    } by {
        let old = (r.backward)(n);
        assert(control::registered(s, old));
        target_equivariant(r, s, old, s.fibers[old].committed);
        if s.fibers[old].phase == Phase::Inactive && exists|v: ISet<Binding>| control::target(rename(r, s), n, v) {
            let v = choose|v: ISet<Binding>| control::target(rename(r, s), n, v);
            round_trip(r, s, ISet::empty());
            target_forward(inverse(r), rename(r, s), n, v);
            assert(control::target(s, old, view(inverse(r), v)));
        }
    }
}

pub proof fn quiet_equivariant(r: Renaming, s: control::State)
    requires bijective(r),
    ensures control::quiet(s) == control::quiet(rename(r, s)),
{
    if control::quiet(s) { quiet_forward(r, s); }
    if control::quiet(rename(r, s)) {
        round_trip(r, s, ISet::empty());
        quiet_forward(inverse(r), rename(r, s));
    }
}

pub proof fn full_quiet_forward<V>(r: Renaming, s: full::State<V>)
    requires bijective(r), full::shaped(s), full::quiet(s),
    ensures full::quiet(context(r, s)),
{
    assert forall|n: usize| full::registered(context(r, s), n) implies match context(r, s).control.fibers[n].phase {
        Phase::Inactive => !(exists|v: ISet<Binding>| full::target(context(r, s), n, v)),
        Phase::Active => full::coherent(context(r, s), n),
        _ => false,
    } by {
        let old = (r.backward)(n);
        assert(full::registered(s, old));
        full_target_equivariant(r, s, old, s.control.fibers[old].committed);
        if s.control.fibers[old].phase == Phase::Inactive && exists|v: ISet<Binding>| full::target(context(r, s), n, v) {
            let v = choose|v: ISet<Binding>| full::target(context(r, s), n, v);
            context_round_trip(r, s);
            shaped_forward(r, s);
            full_target_forward(inverse(r), context(r, s), n, v);
            assert(full::target(s, old, view(inverse(r), v)));
        }
    }
}

pub proof fn full_quiet_equivariant<V>(r: Renaming, s: full::State<V>)
    requires bijective(r), full::shaped(s),
    ensures full::quiet(s) == full::quiet(context(r, s)),
{
    if full::quiet(s) { full_quiet_forward(r, s); }
    if full::quiet(context(r, s)) {
        context_round_trip(r, s);
        shaped_forward(r, s);
        full_quiet_forward(inverse(r), context(r, s));
    }
}

pub open spec fn swap(left: usize, right: usize, name: usize) -> usize {
    if name == left { right } else if name == right { left } else { name }
}

pub proof fn swap_involution(left: usize, right: usize, name: usize)
    ensures swap(left, right, swap(left, right, name)) == name,
{ }

/// Extend a matching to pair two fresh allocations, by transposing two names
/// on the destination side. No numeric ordering or canonical fresh choice is
/// needed. The protected set can include all historical allocated names.
pub open spec fn extend(r: Renaming, source: usize, destination: usize) -> Renaming {
    Renaming {
        forward: |n: usize| swap((r.forward)(source), destination, (r.forward)(n)),
        backward: |n: usize| (r.backward)(swap((r.forward)(source), destination, n)),
    }
}

pub open spec fn name_image(r: Renaming, names: ISet<usize>) -> ISet<usize> {
    ISet::new(|n: usize| names.contains((r.backward)(n)))
}

pub proof fn fresh_extension(r: Renaming, names: ISet<usize>, source: usize, destination: usize)
    requires bijective(r), !names.contains(source), !name_image(r, names).contains(destination),
    ensures bijective(extend(r, source, destination)),
        (extend(r, source, destination).forward)(source) == destination,
        (extend(r, source, destination).backward)(destination) == source,
        forall|n: usize| names.contains(n) ==> (extend(r, source, destination).forward)(n) == (r.forward)(n),
        forall|n: usize| name_image(r, names).contains(n)
            ==> (extend(r, source, destination).backward)(n) == (r.backward)(n),
{
    let next = extend(r, source, destination);
    assert forall|n: usize| #[trigger] (next.backward)((next.forward)(n)) == n by {
        swap_involution((r.forward)(source), destination, (r.forward)(n));
        assert((r.backward)((r.forward)(n)) == n);
    }
    assert forall|n: usize| #[trigger] (next.forward)((next.backward)(n)) == n by {
        let swapped = swap((r.forward)(source), destination, n);
        assert((r.forward)((r.backward)(swapped)) == swapped);
        swap_involution((r.forward)(source), destination, n);
    }
    assert forall|n: usize| names.contains(n) implies (next.forward)(n) == (r.forward)(n) by {
        assert(n != source);
        assert((r.backward)((r.forward)(n)) == n);
        assert((r.backward)((r.forward)(source)) == source);
        assert((r.forward)(n) != (r.forward)(source));
        assert((r.forward)(n) != destination);
    }
    assert forall|n: usize| name_image(r, names).contains(n) implies (next.backward)(n) == (r.backward)(n) by {
        assert(n != destination);
        assert(n != (r.forward)(source));
    }
}

pub open spec fn agrees_on(r: Renaming, other: Renaming, names: ISet<usize>) -> bool {
    forall|n: usize| names.contains(n) ==> (r.forward)(n) == (other.forward)(n)
}

pub proof fn image_agrees(r: Renaming, other: Renaming, names: ISet<usize>)
    requires bijective(r), bijective(other), agrees_on(r, other, names),
    ensures name_image(r, names) == name_image(other, names),
        forall|n: usize| name_image(r, names).contains(n) ==> (r.backward)(n) == (other.backward)(n),
{
    assert(name_image(r, names) =~= name_image(other, names)) by {
        assert forall|n: usize| name_image(r, names).contains(n) == name_image(other, names).contains(n) by {
            if name_image(r, names).contains(n) {
                assert(names.contains((r.backward)(n)));
                assert((r.forward)((r.backward)(n)) == n);
                assert((other.forward)((r.backward)(n)) == n);
                assert((other.backward)(n) == (r.backward)(n));
            }
            if name_image(other, names).contains(n) {
                assert(names.contains((other.backward)(n)));
                assert((other.forward)((other.backward)(n)) == n);
                assert((r.forward)((other.backward)(n)) == n);
                assert((r.backward)(n) == (other.backward)(n));
            }
        }
    }
    assert forall|n: usize| name_image(r, names).contains(n) implies (r.backward)(n) == (other.backward)(n) by {
        assert((r.forward)((r.backward)(n)) == n);
        assert((other.forward)((r.backward)(n)) == n);
    }
}

/// An extension that agrees on registered names also agrees on every parent
/// and committed provider, since well-formedness keeps those references live.
pub proof fn state_agrees(r: Renaming, other: Renaming, s: control::State)
    requires bijective(r), bijective(other), agrees_on(r, other, s.fibers.dom()), control::well_formed(s),
    ensures rename(r, s) == rename(other, s),
{
    image_agrees(r, other, s.fibers.dom());
    assert(rename(r, s).fibers.dom() =~= name_image(r, s.fibers.dom()));
    assert(rename(other, s).fibers.dom() =~= name_image(other, s.fibers.dom()));
    assert(rename(r, s).fibers =~= rename(other, s).fibers) by {
        assert forall|n: usize| rename(r, s).fibers.dom().contains(n) implies
            rename(r, s).fibers[n] == rename(other, s).fibers[n] by {
            let old = (r.backward)(n);
            assert((other.backward)(n) == old);
            assert(control::registered(s, old));
            match s.fibers[old].parent {
                Some(p) => {
                    assert(control::registered(s, p));
                    assert((r.forward)(p) == (other.forward)(p));
                },
                None => { },
            }
            assert(view(r, s.fibers[old].committed) =~= view(other, s.fibers[old].committed)) by {
                assert forall|b: Binding| view(r, s.fibers[old].committed).contains(b)
                    == view(other, s.fibers[old].committed).contains(b) by {
                    if view(r, s.fibers[old].committed).contains(b) {
                        let original = binding(inverse(r), b);
                        assert(s.fibers[old].committed.contains(original));
                        assert(control::registered(s, original.provider));
                        assert((r.forward)(original.provider) == (other.forward)(original.provider));
                        assert((other.backward)(b.provider) == original.provider);
                    }
                    if view(other, s.fibers[old].committed).contains(b) {
                        let original = binding(inverse(other), b);
                        assert(s.fibers[old].committed.contains(original));
                        assert(control::registered(s, original.provider));
                        assert((r.forward)(original.provider) == (other.forward)(original.provider));
                        assert((r.backward)(b.provider) == original.provider);
                    }
                }
            }
        }
    }
}

pub proof fn indexed_agrees<T>(r: Renaming, other: Renaming, map: IMap<usize, T>)
    requires bijective(r), bijective(other), agrees_on(r, other, map.dom()),
    ensures indexed(r, map) == indexed(other, map),
{
    image_agrees(r, other, map.dom());
    assert(indexed(r, map) =~= indexed(other, map));
}

pub proof fn context_agrees<V>(r: Renaming, other: Renaming, s: full::State<V>)
    requires bijective(r), bijective(other), agrees_on(r, other, s.control.fibers.dom()),
        full::shaped(s), control::well_formed(s.control),
    ensures context(r, s) == context(other, s),
{
    state_agrees(r, other, s.control);
    indexed_agrees(r, other, s.tables);
    indexed_agrees(r, other, s.effects);
    indexed_agrees(r, other, s.iterators);
    indexed_agrees(r, other, s.accumulators);
}

/// Match an O-Insert choosing a different fresh destination name while leaving
/// the entire pre-state unchanged. The result is a legal allocation step,
/// not merely an assertion that two completed maps happen to be isomorphic.
pub proof fn fresh_insert_matches(r: Renaming, a: control::State, z: control::State, source: usize, destination: usize)
    requires bijective(r), control::well_formed(a),
        control::step(a, z, source, control::Rule::Insert), !control::registered(rename(r, a), destination),
    ensures {
        let next = extend(r, source, destination);
        &&& bijective(next)
        &&& agrees_on(r, next, a.fibers.dom())
        &&& rename(next, a) == rename(r, a)
        &&& control::step(rename(r, a), rename(next, z), destination, control::Rule::Insert)
    },
{
    fresh_extension(r, a.fibers.dom(), source, destination);
    state_agrees(r, extend(r, source, destination), a);
    step_forward(extend(r, source, destination), a, z, source, control::Rule::Insert);
}

/// The same fresh allocation matching retains empty service tables and every
/// auxiliary field. O-Insert does not consult the opaque iterator interpreter.
pub proof fn fresh_full_insert_matches<V>(r: Renaming, m: full::Model<V>, a: full::State<V>, z: full::State<V>, source: usize, destination: usize)
    requires bijective(r), full::shaped(a), full::shaped(z), control::well_formed(a.control),
        full::step(m, a, z, source, control::Rule::Insert), !full::registered(context(r, a), destination),
    ensures {
        let next = extend(r, source, destination);
        &&& bijective(next)
        &&& context(next, a) == context(r, a)
        &&& full::step(m, context(r, a), context(next, z), destination, control::Rule::Insert)
    },
{
    fresh_extension(r, a.control.fibers.dom(), source, destination);
    let next = extend(r, source, destination);
    context_agrees(r, next, a);
    step_forward(next, a.control, z.control, source, control::Rule::Insert);
    shaped_forward(next, z);
    full_frame_forward(next, a, z, source);
    observations(next, z.control, source);
}

} // verus!
