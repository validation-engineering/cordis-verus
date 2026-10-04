//! Recovery in the presence of provider/consumer interference.
//!
//! A consumer operation need not commute with the provider's extension. The
//! provider's *actual* inverse journal contains a restriction; LIFO recovery
//! absorbs operations at that binding. Missing-binding operations are no-ops,
//! as in paper Lemma 67. A failed value operation is additionally totalized as
//! identity in this explicit profile; the strict grammar bridge below applies
//! only on the actual forward/inverse domain. This is distinct
//! from the strict partial-transition semantics of `partial_independence`.
#[cfg(verus_keep_ghost)]
use crate::{coeffects, mediated, preservation, projection, refinement as c, Binding, Phase};
use crate::{semantics as s, Port};
use vstd::prelude::*;

verus! {

#[verifier::reject_recursive_types(V)]
pub enum Action<V> {
    Identity,
    Operation { key: Port, update: spec_fn(V) -> V },
    Provision { key: Port, value: V },
    Restriction { key: Port },
}

pub open spec fn key<V>(a: Action<V>) -> Option<Port> {
    match a {
        Action::Identity => None,
        Action::Operation { key, .. } | Action::Provision { key, .. } | Action::Restriction { key } => Some(key),
    }
}

/// This profile may totalize a partial value operation by returning its input
/// on failure. That is an additional choice, not a theorem identifying failure
/// with a strict transition. Missing-key identity is handled independently.
pub open spec fn apply<V>(a: Action<V>, state: IMap<Port, V>) -> IMap<Port, V> {
    match a {
        Action::Identity => state,
        Action::Operation { key, update } => if state.dom().contains(key) {
            state.insert(key, update(state[key]))
        } else { state },
        Action::Provision { key, value } => if state.dom().contains(key) { state } else { state.insert(key, value) },
        Action::Restriction { key } => state.remove(key),
    }
}

pub open spec fn inverse_action<V>(a: Action<V>) -> bool {
    !matches!(a, Action::Provision { .. })
}

pub open spec fn inverse_journal<V>(journal: Seq<Action<V>>) -> bool {
    forall|i: int| 0 <= i < journal.len() ==> inverse_action(#[trigger] journal[i])
}

pub open spec fn restore<V>(journal: Seq<Action<V>>, state: IMap<Port, V>) -> IMap<Port, V>
    decreases journal.len(),
{
    if journal.len() == 0 { state }
    else { restore(journal.drop_last(), apply(journal.last(), state)) }
}

pub open spec fn erases<V>(journal: Seq<Action<V>>, k: Port) -> bool {
    journal.contains(Action::Restriction { key: k })
}

pub open spec fn agrees_outside<V>(a: IMap<Port, V>, b: IMap<Port, V>, k: Port) -> bool {
    forall|j: Port| j != k ==> coeffects::get(a, j) == coeffects::get(b, j)
}

pub proof fn slot_extensionality<V>(a: IMap<Port, V>, b: IMap<Port, V>)
    requires forall|k: Port| #[trigger] coeffects::get(a, k) == coeffects::get(b, k),
    ensures a == b,
{
    assert(a.dom() =~= b.dom()) by {
        assert forall|k: Port| a.dom().contains(k) == b.dom().contains(k) by {
            assert(coeffects::get(a, k) == coeffects::get(b, k));
        }
    }
    assert(a =~= b) by {
        assert forall|k: Port| a.dom().contains(k) implies a[k] == b[k] by {
            assert(coeffects::get(a, k) == coeffects::get(b, k));
        }
    }
}

pub proof fn local_frame<V>(a: Action<V>, state: IMap<Port, V>, k: Port)
    requires key(a) != Some(k),
    ensures coeffects::get(apply(a, state), k) == coeffects::get(state, k),
{ }

pub proof fn outside_preserved<V>(a: Action<V>, left: IMap<Port, V>, right: IMap<Port, V>, k: Port)
    requires agrees_outside(left, right, k),
    ensures agrees_outside(apply(a, left), apply(a, right), k),
{
    assert forall|j: Port| j != k implies coeffects::get(apply(a, left), j) == coeffects::get(apply(a, right), j) by {
        assert(coeffects::get(left, j) == coeffects::get(right, j));
        if key(a) != Some(j) { local_frame(a, left, j); local_frame(a, right, j); }
    }
}

pub proof fn restore_outside<V>(journal: Seq<Action<V>>, left: IMap<Port, V>, right: IMap<Port, V>, k: Port)
    requires agrees_outside(left, right, k),
    ensures agrees_outside(restore(journal, left), restore(journal, right), k),
    decreases journal.len(),
{
    if journal.len() > 0 {
        outside_preserved(journal.last(), left, right, k);
        restore_outside(journal.drop_last(), apply(journal.last(), left), apply(journal.last(), right), k);
    }
}

pub proof fn absent_stays_absent<V>(journal: Seq<Action<V>>, state: IMap<Port, V>, k: Port)
    requires inverse_journal(journal), !state.dom().contains(k),
    ensures !restore(journal, state).dom().contains(k),
    decreases journal.len(),
{
    if journal.len() > 0 {
        assert(inverse_action(journal.last()));
        assert(!apply(journal.last(), state).dom().contains(k));
        absent_stays_absent(journal.drop_last(), apply(journal.last(), state), k);
    }
}

pub proof fn actual_restriction_erases<V>(journal: Seq<Action<V>>, state: IMap<Port, V>, k: Port)
    requires inverse_journal(journal), erases(journal, k),
    ensures !restore(journal, state).dom().contains(k),
    decreases journal.len(),
{
    assert(journal.len() > 0);
    if journal.last() == (Action::Restriction { key: k }) {
        absent_stays_absent(journal.drop_last(), apply(journal.last(), state), k);
    } else {
        assert(journal.drop_last().contains(Action::Restriction { key: k })) by {
            let i = choose|i: int| 0 <= i < journal.len() && journal[i] == (Action::Restriction { key: k });
            assert(i < journal.len() - 1);
            assert(journal.drop_last()[i] == (Action::Restriction { key: k }));
        }
        actual_restriction_erases(journal.drop_last(), apply(journal.last(), state), k);
    }
}

/// The entangled case: no commutation premise about consumer versus provider
/// operations is needed after the journal contains the real restriction.
pub proof fn entangled_absorption<V>(journal: Seq<Action<V>>, state: IMap<Port, V>, k: Port, update: spec_fn(V) -> V)
    requires inverse_journal(journal), erases(journal, k),
    ensures restore(journal, apply(Action::Operation { key: k, update }, state)) == restore(journal, state),
        apply(Action::Operation { key: k, update }, restore(journal, state)) == restore(journal, state),
{
    let changed = apply(Action::Operation { key: k, update }, state);
    assert(agrees_outside(state, changed, k));
    restore_outside(journal, state, changed, k);
    actual_restriction_erases(journal, state, k);
    actual_restriction_erases(journal, changed, k);
    assert forall|j: Port| #[trigger] coeffects::get(restore(journal, state), j) == coeffects::get(restore(journal, changed), j) by { }
    slot_extensionality(restore(journal, state), restore(journal, changed));
}

pub open spec fn atom_compatible<V>(inverse: Action<V>, foreign: Action<V>) -> bool {
    match (inverse, foreign) {
        (Action::Operation { key: k, update: f }, Action::Operation { key: j, update: g }) =>
            k != j || forall|v: V| #[trigger] f(g(v)) == g(f(v)),
        (_, Action::Provision { key: k, .. }) => key(inverse) != Some(k),
        _ => true,
    }
}

pub proof fn atomic_commutation<V>(inverse: Action<V>, foreign: Action<V>, state: IMap<Port, V>)
    requires inverse_action(inverse), atom_compatible(inverse, foreign),
    ensures apply(inverse, apply(foreign, state)) == apply(foreign, apply(inverse, state)),
{
    let left = apply(inverse, apply(foreign, state));
    let right = apply(foreign, apply(inverse, state));
    assert forall|k: Port| #[trigger] coeffects::get(left, k) == coeffects::get(right, k) by {
        if let Action::Operation { key: i, update: f } = inverse {
            if let Action::Operation { key: j, update: g } = foreign {
                if i == j && state.dom().contains(i) { assert(f(g(state[i])) == g(f(state[i]))); }
            }
        }
    }
    slot_extensionality(left, right);
}

pub proof fn atomwise_journal_commutation<V>(journal: Seq<Action<V>>, foreign: Action<V>, state: IMap<Port, V>)
    requires inverse_journal(journal),
        forall|i: int| 0 <= i < journal.len() ==> atom_compatible(#[trigger] journal[i], foreign),
    ensures restore(journal, apply(foreign, state)) == apply(foreign, restore(journal, state)),
    decreases journal.len(),
{
    if journal.len() > 0 {
        atomic_commutation(journal.last(), foreign, state);
        atomwise_journal_commutation(journal.drop_last(), foreign, apply(journal.last(), state));
    }
}

/// Compatibility permits entangled consumers even if their operations fail
/// every ordinary pairwise commutation check against provider operations.
pub open spec fn compatible<V>(journal: Seq<Action<V>>, foreign: Action<V>) -> bool {
    match foreign {
        Action::Operation { key, .. } if erases(journal, key) => true,
        _ => forall|i: int| 0 <= i < journal.len() ==> atom_compatible(#[trigger] journal[i], foreign),
    }
}

pub proof fn journal_commutation<V>(journal: Seq<Action<V>>, foreign: Action<V>, state: IMap<Port, V>)
    requires inverse_journal(journal), compatible(journal, foreign),
    ensures restore(journal, apply(foreign, state)) == apply(foreign, restore(journal, state)),
{
    match foreign {
        Action::Operation { key, update } if erases(journal, key) => entangled_absorption(journal, state, key, update),
        _ => atomwise_journal_commutation(journal, foreign, state),
    }
}

pub open spec fn run<V>(actions: Seq<Action<V>>, state: IMap<Port, V>) -> IMap<Port, V>
    decreases actions.len(),
{
    if actions.len() == 0 { state }
    else { apply(actions.last(), run(actions.drop_last(), state)) }
}

pub proof fn run_singleton<V>(action: Action<V>, state: IMap<Port, V>)
    ensures run(seq![action], state) == apply(action, state),
{
    assert(seq![action].drop_last() == Seq::<Action<V>>::empty());
    assert(run(Seq::<Action<V>>::empty(), state) == state);
}

pub open spec fn word_compatible<V>(journal: Seq<Action<V>>, foreign: Seq<Action<V>>) -> bool {
    forall|i: int| 0 <= i < foreign.len() ==> compatible(journal, #[trigger] foreign[i])
}

pub proof fn journal_word_commutation<V>(journal: Seq<Action<V>>, foreign: Seq<Action<V>>, state: IMap<Port, V>)
    requires inverse_journal(journal), word_compatible(journal, foreign),
    ensures restore(journal, run(foreign, state)) == run(foreign, restore(journal, state)),
    decreases foreign.len(),
{
    if foreign.len() > 0 {
        journal_word_commutation(journal, foreign.drop_last(), state);
        journal_commutation(journal, foreign.last(), run(foreign.drop_last(), state));
    }
}

#[verifier::reject_recursive_types(V)]
pub struct Event<V> {
    pub forward: Seq<Action<V>>,
    /// `Some` records the inverse actually returned by this episode's step.
    /// `None` denotes a foreign step, not an unrecorded episode iteration.
    pub returned: Option<Action<V>>,
}

pub open spec fn trace_state<V>(events: Seq<Event<V>>, initial: IMap<Port, V>) -> IMap<Port, V>
    decreases events.len(),
{
    if events.len() == 0 { initial }
    else { run(events.last().forward, trace_state(events.drop_last(), initial)) }
}

pub open spec fn journal<V>(events: Seq<Event<V>>) -> Seq<Action<V>>
    decreases events.len(),
{
    if events.len() == 0 { Seq::empty() }
    else { match events.last().returned {
        None => journal(events.drop_last()),
        Some(inverse) => journal(events.drop_last()).push(inverse),
    } }
}

pub open spec fn foreign_state<V>(events: Seq<Event<V>>, initial: IMap<Port, V>) -> IMap<Port, V>
    decreases events.len(),
{
    if events.len() == 0 { initial }
    else { match events.last().returned {
        None => run(events.last().forward, foreign_state(events.drop_last(), initial)),
        Some(_) => foreign_state(events.drop_last(), initial),
    } }
}

/// Local witnesses are demanded only at the actual forward inputs. Foreign
/// compatibility is checked against the already returned journal, not future
/// inverses and not a hypothesized replay history.
pub open spec fn admissible_trace<V>(events: Seq<Event<V>>, initial: IMap<Port, V>) -> bool
    decreases events.len(),
{
    events.len() == 0 || {
        let prefix = events.drop_last();
        let before = trace_state(prefix, initial);
        let last = events.last();
        &&& admissible_trace(prefix, initial)
        &&& match last.returned {
            Some(inverse) => inverse_action(inverse) && apply(inverse, run(last.forward, before)) == before,
            None => word_compatible(journal(prefix), last.forward),
        }
    }
}

/// Theorem 68 for the explicit key-map profile, with genuinely entangled
/// interference and arbitrary finite interleavings. The result is exact value
/// equality; observational quotients can forget more than this profile does.
pub proof fn entangled_recovery<V>(events: Seq<Event<V>>, initial: IMap<Port, V>)
    requires admissible_trace(events, initial),
    ensures inverse_journal(journal(events)),
        restore(journal(events), trace_state(events, initial)) == foreign_state(events, initial),
    decreases events.len(),
{
    if events.len() > 0 {
        let prefix = events.drop_last();
        let before = trace_state(prefix, initial);
        entangled_recovery(prefix, initial);
        match events.last().returned {
            Some(inverse) => {
                assert(journal(events).drop_last() == journal(prefix));
                assert(journal(events).last() == inverse);
                assert forall|i: int| 0 <= i < journal(events).len() implies inverse_action(#[trigger] journal(events)[i]) by {
                    if i < journal(prefix).len() { assert(journal(events)[i] == journal(prefix)[i]); }
                }
            },
            None => journal_word_commutation(journal(prefix), events.last().forward, before),
        }
    }
}

/// Interpret opaque inverse identities by their actual key-map meanings.
pub open spec fn interpret<V>(meaning: spec_fn(nat) -> Action<V>, tokens: Seq<nat>) -> Seq<Action<V>> {
    tokens.map(|_: int, token: nat| meaning(token))
}

/// This is a local primitive homomorphism, not the whole-accumulator recovery
/// claim. It can represent table operations, restrictions and child O-Retire
/// (Identity), while preserving the distinction between tables and control.
pub open spec fn inverse_projection<V>(model: s::Model<V>, meaning: spec_fn(nat) -> Action<V>, token: nat, state: s::State<V>) -> bool {
    projection::project((model.undo)(token, state), ISet::full())
        == apply(meaning(token), projection::project(state, ISet::full()))
}

pub open spec fn restore_projection_contract<V>(model: s::Model<V>, meaning: spec_fn(nat) -> Action<V>, tokens: Seq<nat>, state: s::State<V>) -> bool
    decreases tokens.len(),
{
    tokens.len() == 0 || (inverse_projection(model, meaning, tokens.last(), state)
        && restore_projection_contract(model, meaning, tokens.drop_last(), (model.undo)(tokens.last(), state)))
}

/// Bridges the abstract LIFO journal to the paper's actual full-state restore.
pub proof fn actual_restore_projection<V>(model: s::Model<V>, meaning: spec_fn(nat) -> Action<V>, tokens: Seq<nat>, state: s::State<V>)
    requires restore_projection_contract(model, meaning, tokens, state),
    ensures projection::project(s::restore(model, tokens, state), ISet::full())
        == restore(interpret(meaning, tokens), projection::project(state, ISet::full())),
    decreases tokens.len(),
{
    if tokens.len() > 0 {
        actual_restore_projection(model, meaning, tokens.drop_last(), (model.undo)(tokens.last(), state));
        assert(interpret(meaning, tokens).drop_last() =~= interpret(meaning, tokens.drop_last()));
        assert(interpret(meaning, tokens).last() == meaning(tokens.last()));
    }
}

/// A provider pinned by an installed consumer cannot unload in the full
/// partial-publication semantics, without requiring total Active provision.
pub proof fn committed_provider_blocks_unload<V>(model: s::Model<V>, state: s::State<V>, next: s::State<V>, consumer: usize, provider: usize, binding: Binding)
    requires consumer != provider, s::registered(state, consumer), state.control.fibers[consumer].phase != Phase::Inactive,
        state.control.fibers[consumer].committed.contains(binding), binding.provider == provider,
    ensures !s::step(model, state, next, provider, c::Rule::Unload),
{
    assert(c::relied(state.control, provider));
}

/// The real L-Unload observation satisfies terminal recovery once the actual
/// trace and token interpretation meet the primitive contracts above.
pub proof fn terminal_recovery<V>(model: s::Model<V>, meaning: spec_fn(nat) -> Action<V>, events: Seq<Event<V>>, initial: IMap<Port, V>, state: s::State<V>, next: s::State<V>, actor: usize)
    requires admissible_trace(events, initial),
        projection::project(state, ISet::full()) == trace_state(events, initial),
        interpret(meaning, state.accumulators[actor]) == journal(events),
        restore_projection_contract(model, meaning, state.accumulators[actor], state),
        s::step(model, state, next, actor, c::Rule::Unload),
        preservation::well_formed(state), preservation::admissible_step(model, state, next, actor, c::Rule::Unload),
    ensures projection::project(next, ISet::full()) == foreign_state(events, initial),
{
    entangled_recovery(events, initial);
    actual_restore_projection(model, meaning, state.accumulators[actor], state);
    preservation::restore_preservation(model, state.accumulators[actor], state, actor);
    let restored = s::restore(model, state.accumulators[actor], state);
    projection::unique_owner(restored);
    projection::lifecycle_edit(restored, actor, Phase::Inactive, ISet::empty(), None, Seq::empty(), ISet::full());
}


/// The iterator argument is the actual iterator identity at the landing state.
pub type ForwardMeaning<V> = spec_fn(usize, nat, s::State<V>) -> Action<V>;

pub open spec fn lands<V>(model: s::Model<V>, a: s::State<V>, z: s::State<V>, actor: usize, rule: c::Rule) -> bool {
    rule == c::Rule::Iter || rule == c::Rule::Finish || (rule == c::Rule::Divert
        && z != s::edit(a, actor, Phase::Unloading, a.control.fibers[actor].committed, None, a.accumulators[actor]))
}

pub open spec fn step_word<V>(model: s::Model<V>, meaning: spec_fn(nat) -> Action<V>, forward: ForwardMeaning<V>, a: s::State<V>, z: s::State<V>, actor: usize, rule: c::Rule) -> Seq<Action<V>> {
    if lands(model, a, z, actor, rule) { seq![forward(actor, a.iterators[actor].unwrap(), a)] }
    else if rule == c::Rule::Unload { interpret(meaning, a.accumulators[actor]).reverse() }
    else { Seq::empty() }
}

pub open spec fn step_event<V>(model: s::Model<V>, meaning: spec_fn(nat) -> Action<V>, forward: ForwardMeaning<V>, a: s::State<V>, z: s::State<V>, actor: usize, rule: c::Rule, owner: usize) -> Event<V> {
    Event { forward: step_word(model, meaning, forward, a, z, actor, rule),
        returned: if actor == owner && lands(model, a, z, actor, rule) {
            Some(meaning((model.iterate)(actor, a.iterators[actor].unwrap(), a).inverse))
        } else { None } }
}

pub proof fn run_concatenation<V>(left: Seq<Action<V>>, right: Seq<Action<V>>, state: IMap<Port, V>)
    ensures run(left + right, state) == run(right, run(left, state)),
    decreases right.len(),
{
    if right.len() == 0 { assert(left + right == left); }
    else {
        assert((left + right).drop_last() =~= left + right.drop_last());
        run_concatenation(left, right.drop_last(), state);
    }
}

pub proof fn reverse_is_restore<V>(actions: Seq<Action<V>>, state: IMap<Port, V>)
    ensures run(actions.reverse(), state) == restore(actions, state),
    decreases actions.len(),
{
    if actions.len() > 0 {
        assert(actions.reverse() =~= seq![actions.last()] + actions.drop_last().reverse());
        run_concatenation(seq![actions.last()], actions.drop_last().reverse(), state);
        reverse_is_restore(actions.drop_last(), apply(actions.last(), state));
        run_singleton(actions.last(), state);
    }
}

pub proof fn restore_accumulators<V>(model: s::Model<V>, tokens: Seq<nat>, a: s::State<V>, actor: usize)
    requires preservation::admissible_restore(model, tokens, a, actor),
    ensures s::restore(model, tokens, a).accumulators == a.accumulators,
    decreases tokens.len(),
{
    if tokens.len() > 0 {
        let z = (model.undo)(tokens.last(), a);
        if !preservation::table_map(a, z, actor) {
            let child = choose|child: usize| s::child_retire(a, z, child);
            assert(s::child_retire(a, z, child));
        }
        assert(z.accumulators == a.accumulators);
        restore_accumulators(model, tokens.drop_last(), z, actor);
    }
}

/// All nine full rules derive the episode journal update from their actual
/// yielded inverse. An open episode cannot Begin, Remove or Unload itself.
pub proof fn actual_accumulator_step<V>(model: s::Model<V>, a: s::State<V>, z: s::State<V>, actor: usize, rule: c::Rule, owner: usize)
    requires preservation::well_formed(a), s::step(model, a, z, actor, rule),
        preservation::admissible_step(model, a, z, actor, rule),
        s::registered(a, owner), a.control.fibers[owner].phase != Phase::Inactive,
        s::registered(z, owner), z.control.fibers[owner].phase != Phase::Inactive,
    ensures z.control.fibers[owner].committed == a.control.fibers[owner].committed,
        z.accumulators[owner] == if actor == owner && lands(model, a, z, actor, rule) {
        a.accumulators[owner].push((model.iterate)(actor, a.iterators[actor].unwrap(), a).inverse)
    } else { a.accumulators[owner] },
{
    if lands(model, a, z, actor, rule) {
        let y = (model.iterate)(actor, a.iterators[actor].unwrap(), a);
        preservation::forward_preservation(a, y.state, actor);
        if !preservation::table_map(a, y.state, actor) {
            let child = choose|child: usize| preservation::child_map(a, y.state, actor, child);
            assert(child != owner);
            assert(y.state.accumulators[owner] == a.accumulators[owner]);
        }
    } else if rule == c::Rule::Unload {
        restore_accumulators(model, a.accumulators[actor], a, actor);
        preservation::restore_preservation(model, a.accumulators[actor], a, actor);
        assert(actor != owner);
    } else {
        match rule {
            c::Rule::Insert | c::Rule::Remove | c::Rule::Begin => { assert(actor != owner); },
            _ => { },
        }
    }
}

/// The local diagram is required for one yielded primitive, plus each actual
/// inverse application of an Unload. It is never a whole-trace simulation
/// premise and does not posit the resulting accumulated recovery equation.
pub open spec fn primitive_projection<V>(model: s::Model<V>, meaning: spec_fn(nat) -> Action<V>, forward: ForwardMeaning<V>, a: s::State<V>, z: s::State<V>, actor: usize, rule: c::Rule) -> bool {
    &&& (lands(model, a, z, actor, rule) ==> {
        let y = (model.iterate)(actor, a.iterators[actor].unwrap(), a);
        projection::project(y.state, ISet::full())
            == apply(forward(actor, a.iterators[actor].unwrap(), a), projection::project(a, ISet::full()))
    })
    &&& (rule == c::Rule::Unload ==> restore_projection_contract(model, meaning, a.accumulators[actor], a))
}

pub proof fn actual_step_projection<V>(model: s::Model<V>, meaning: spec_fn(nat) -> Action<V>, forward: ForwardMeaning<V>, a: s::State<V>, z: s::State<V>, actor: usize, rule: c::Rule)
    requires preservation::well_formed(a), s::step(model, a, z, actor, rule),
        preservation::admissible_step(model, a, z, actor, rule),
        primitive_projection(model, meaning, forward, a, z, actor, rule),
    ensures projection::project(z, ISet::full())
        == run(step_word(model, meaning, forward, a, z, actor, rule), projection::project(a, ISet::full())),
{
    if lands(model, a, z, actor, rule) {
        run_singleton(forward(actor, a.iterators[actor].unwrap(), a), projection::project(a, ISet::full()));
        let y = (model.iterate)(actor, a.iterators[actor].unwrap(), a);
        preservation::forward_preservation(a, y.state, actor);
        projection::unique_owner(y.state);
        let phase = if rule == c::Rule::Iter { Phase::Loading } else if rule == c::Rule::Finish { Phase::Active } else { Phase::Unloading };
        let next = if rule == c::Rule::Iter { y.next } else { None };
        assert(z == s::edit(y.state, actor, phase, a.control.fibers[actor].committed, next, a.accumulators[actor].push(y.inverse)));
        projection::lifecycle_edit(y.state, actor, phase, a.control.fibers[actor].committed, next, a.accumulators[actor].push(y.inverse), ISet::full());
    } else if rule == c::Rule::Unload {
        actual_restore_projection(model, meaning, a.accumulators[actor], a);
        reverse_is_restore(interpret(meaning, a.accumulators[actor]), projection::project(a, ISet::full()));
        preservation::restore_preservation(model, a.accumulators[actor], a, actor);
        let restored = s::restore(model, a.accumulators[actor], a);
        projection::unique_owner(restored);
        projection::lifecycle_edit(restored, actor, Phase::Inactive, ISet::empty(), None, Seq::empty(), ISet::full());
    } else if rule == c::Rule::Insert {
        projection::empty_insertion(a, z, actor, ISet::full());
    } else {
        preservation::full_preservation(model, a, z, actor, rule);
        projection::unique_owner(a); projection::unique_owner(z);
        assert(projection::bindings_equal(a, z)) by {
            assert forall|k: Port, n: usize| projection::owns(a, k, n) == projection::owns(z, k, n)
                && (projection::owns(a, k, n) ==> a.tables[n][k] == z.tables[n][k]) by {
                if rule == c::Rule::Remove && n != actor { assert(c::registered(a.control, n) == c::registered(z.control, n)); }
            }
        }
        projection::projection_equal(a, z, ISet::full());
    }
}

pub open spec fn events_of<V>(model: s::Model<V>, meaning: spec_fn(nat) -> Action<V>, forward: ForwardMeaning<V>, states: Seq<s::State<V>>, labels: Seq<(usize, c::Rule)>, owner: usize) -> Seq<Event<V>>
    decreases labels.len(),
{
    if labels.len() == 0 { Seq::empty() }
    else { events_of(model, meaning, forward, states.drop_last(), labels.drop_last(), owner).push(
        step_event(model, meaning, forward, states[labels.len()-1], states[labels.len() as int], labels.last().0, labels.last().1, owner)) }
}

pub open spec fn local_episode_law<V>(model: s::Model<V>, meaning: spec_fn(nat) -> Action<V>, forward: ForwardMeaning<V>, a: s::State<V>, z: s::State<V>, actor: usize, rule: c::Rule, owner: usize) -> bool {
    let event = step_event(model, meaning, forward, a, z, actor, rule, owner);
    &&& primitive_projection(model, meaning, forward, a, z, actor, rule)
    &&& match event.returned {
        Some(inverse) => inverse_action(inverse) && apply(inverse, run(event.forward, projection::project(a, ISet::full()))) == projection::project(a, ISet::full()),
        None => word_compatible(interpret(meaning, a.accumulators[owner]), event.forward),
    }
}

/// Primitive laws along a real episode prefix. An entangled consumer can meet
/// foreign compatibility through the actual restriction in the current
/// accumulator; pairwise independence of provider/consumer forwards is absent.
pub open spec fn episode_profile<V>(model: s::Model<V>, meaning: spec_fn(nat) -> Action<V>, forward: ForwardMeaning<V>, states: Seq<s::State<V>>, labels: Seq<(usize, c::Rule)>, owner: usize) -> bool {
    &&& preservation::execution(model, states, labels)
    &&& preservation::well_formed(states.first())
    &&& states.first().accumulators[owner].len() == 0
    &&& forall|i: int| 0 <= i < states.len() ==> s::registered(states[i], owner)
        && states[i].control.fibers[owner].phase != Phase::Inactive
    &&& forall|i: int| 0 <= i < labels.len() ==> #[trigger] local_episode_law(model, meaning, forward, states[i], states[i+1], labels[i].0, labels[i].1, owner)
}

pub proof fn episode_profile_prefix<V>(model: s::Model<V>, meaning: spec_fn(nat) -> Action<V>, forward: ForwardMeaning<V>, states: Seq<s::State<V>>, labels: Seq<(usize, c::Rule)>, owner: usize)
    requires episode_profile(model, meaning, forward, states, labels, owner), labels.len() > 0,
    ensures episode_profile(model, meaning, forward, states.drop_last(), labels.drop_last(), owner),
{
    let prior = states.drop_last(); let previous = labels.drop_last();
    assert(prior.len() == previous.len()+1);
    assert forall|i: int| 0 <= i < previous.len() implies #[trigger] local_episode_law(model, meaning, forward, prior[i], prior[i+1], previous[i].0, previous[i].1, owner) by {
        assert(local_episode_law(model, meaning, forward, states[i], states[i+1], labels[i].0, labels[i].1, owner));
    }
}

pub proof fn episode_profile_shape<V>(model: s::Model<V>, meaning: spec_fn(nat) -> Action<V>, forward: ForwardMeaning<V>, states: Seq<s::State<V>>, labels: Seq<(usize, c::Rule)>, owner: usize)
    requires episode_profile(model, meaning, forward, states, labels, owner),
    ensures states.len() == labels.len()+1, states.first().accumulators[owner].len() == 0,
{ }

pub proof fn episode_profile_step<V>(model: s::Model<V>, meaning: spec_fn(nat) -> Action<V>, forward: ForwardMeaning<V>, states: Seq<s::State<V>>, labels: Seq<(usize, c::Rule)>, owner: usize, index: int)
    requires episode_profile(model, meaning, forward, states, labels, owner), 0 <= index < labels.len(),
    ensures preservation::well_formed(states[index]),
        s::step(model, states[index], states[index+1], labels[index].0, labels[index].1),
        preservation::admissible_step(model, states[index], states[index+1], labels[index].0, labels[index].1),
        s::registered(states[index], owner), states[index].control.fibers[owner].phase != Phase::Inactive,
        s::registered(states[index+1], owner), states[index+1].control.fibers[owner].phase != Phase::Inactive,
        local_episode_law(model, meaning, forward, states[index], states[index+1], labels[index].0, labels[index].1, owner),
{
    preservation::execution_preservation(model, states, labels);
}

/// Computes both the primitive replay and the inverse journal from a real full
/// execution. Neither equality is an input assumption of this theorem.
#[verifier::rlimit(30)]
pub proof fn full_episode_recovery<V>(model: s::Model<V>, meaning: spec_fn(nat) -> Action<V>, forward: ForwardMeaning<V>, states: Seq<s::State<V>>, labels: Seq<(usize, c::Rule)>, owner: usize)
    requires episode_profile(model, meaning, forward, states, labels, owner),
    ensures {
        let events = events_of(model, meaning, forward, states, labels, owner);
        let initial = projection::project(states.first(), ISet::full());
        &&& admissible_trace(events, initial)
        &&& projection::project(states.last(), ISet::full()) == trace_state(events, initial)
        &&& interpret(meaning, states.last().accumulators[owner]) == journal(events)
        &&& restore(interpret(meaning, states.last().accumulators[owner]), projection::project(states.last(), ISet::full()))
            == foreign_state(events, initial)
    },
    decreases labels.len(),
{
    hide(episode_profile);
    hide(preservation::execution);
    hide(preservation::well_formed);
    hide(s::step);
    hide(preservation::admissible_step);
    episode_profile_shape(model, meaning, forward, states, labels, owner);
    let events = events_of(model, meaning, forward, states, labels, owner);
    let initial = projection::project(states.first(), ISet::full());
    if labels.len() == 0 {
        assert(states.last() == states.first());
        assert(interpret(meaning, states.last().accumulators[owner]) =~= Seq::empty());
    } else {
        let prior = states.drop_last(); let previous = labels.drop_last();
        episode_profile_prefix(model, meaning, forward, states, labels, owner);
        full_episode_recovery(model, meaning, forward, prior, previous, owner);
        episode_profile_step(model, meaning, forward, states, labels, owner, labels.len()-1);
        let a = states[labels.len()-1]; let z = states.last();
        let actor = labels.last().0; let rule = labels.last().1;
        let prefix = events_of(model, meaning, forward, prior, previous, owner);
        let event = step_event(model, meaning, forward, a, z, actor, rule, owner);
        assert(local_episode_law(model, meaning, forward, a, z, actor, rule, owner));
        assert(primitive_projection(model, meaning, forward, a, z, actor, rule));
        assert(preservation::well_formed(a));
        assert(s::step(model, a, z, actor, rule));
        assert(preservation::admissible_step(model, a, z, actor, rule));
        assert(s::registered(a, owner) && a.control.fibers[owner].phase != Phase::Inactive);
        assert(s::registered(z, owner) && z.control.fibers[owner].phase != Phase::Inactive);
        assert(events.drop_last() == prefix); assert(events.last() == event);
        actual_accumulator_step(model, a, z, actor, rule, owner);
        assert(local_episode_law(model, meaning, forward, a, z, actor, rule, owner));
        actual_step_projection(model, meaning, forward, a, z, actor, rule);
        if event.returned.is_some() {
            let token = (model.iterate)(actor, a.iterators[actor].unwrap(), a).inverse;
            assert(interpret(meaning, z.accumulators[owner]) =~= interpret(meaning, a.accumulators[owner]).push(meaning(token)));
        }
        assert(interpret(meaning, z.accumulators[owner]) == journal(events));
        assert(local_episode_law(model, meaning, forward, a, z, actor, rule, owner));
        assert(primitive_projection(model, meaning, forward, a, z, actor, rule));
        assert(match event.returned {
            Some(inverse) => inverse_action(inverse) && apply(inverse, run(event.forward, projection::project(a, ISet::full()))) == projection::project(a, ISet::full()),
            None => word_compatible(interpret(meaning, a.accumulators[owner]), event.forward),
        });
        assert(admissible_trace(events, initial));
    }
    entangled_recovery(events, initial);
}

/// Corollary 69 now consumes the full labelled execution, rather than accepting
/// an externally supplied replay or inverse-journal equality.
pub proof fn full_terminal_recovery<V>(model: s::Model<V>, meaning: spec_fn(nat) -> Action<V>, forward: ForwardMeaning<V>, states: Seq<s::State<V>>, labels: Seq<(usize, c::Rule)>, owner: usize, after: s::State<V>)
    requires episode_profile(model, meaning, forward, states, labels, owner),
        s::step(model, states.last(), after, owner, c::Rule::Unload),
        preservation::admissible_step(model, states.last(), after, owner, c::Rule::Unload),
        restore_projection_contract(model, meaning, states.last().accumulators[owner], states.last()),
    ensures projection::project(after, ISet::full()) == foreign_state(
        events_of(model, meaning, forward, states, labels, owner), projection::project(states.first(), ISet::full())),
{
    full_episode_recovery(model, meaning, forward, states, labels, owner);
    preservation::execution_preservation(model, states, labels);
    terminal_recovery(model, meaning, events_of(model, meaning, forward, states, labels, owner),
        projection::project(states.first(), ISet::full()), states.last(), after, owner);
}


/// Once a consumer has begun, its retained provider cannot return to Loading
/// or Inactive during that consumer episode. Table-only effects and child
/// retirement preserve the provider phase even under a foreign Unload.
pub proof fn pinned_provider_phase_step<V>(model: s::Model<V>, a: s::State<V>, z: s::State<V>, actor: usize, rule: c::Rule, consumer: usize, binding: Binding)
    requires preservation::well_formed(a), s::step(model, a, z, actor, rule),
        preservation::admissible_step(model, a, z, actor, rule),
        s::registered(a, consumer), a.control.fibers[consumer].committed.contains(binding),
        a.control.fibers[binding.provider].phase == Phase::Active || a.control.fibers[binding.provider].phase == Phase::Unloading,
    ensures s::registered(z, binding.provider),
        z.control.fibers[binding.provider].phase == Phase::Active || z.control.fibers[binding.provider].phase == Phase::Unloading,
        actor == binding.provider ==> !lands(model, a, z, actor, rule) && rule != c::Rule::Unload,
{
    let provider = binding.provider;
    assert(s::registered(a, provider));
    assert(a.control.fibers[consumer].phase != Phase::Inactive);
    assert(consumer != provider);
    committed_provider_blocks_unload(model, a, z, consumer, provider, binding);
    if lands(model, a, z, actor, rule) {
        assert(actor != provider);
        let y = (model.iterate)(actor, a.iterators[actor].unwrap(), a);
        preservation::forward_preservation(a, y.state, actor);
    } else if rule == c::Rule::Unload {
        assert(actor != provider);
        preservation::restore_preservation(model, a.accumulators[actor], a, actor);
    } else {
        if actor == provider {
            assert(rule == c::Rule::Retire || rule == c::Rule::Leave);
            if rule == c::Rule::Leave { assert(z.control.fibers[provider].phase == Phase::Unloading); }
            else { assert(z.control.fibers[provider].phase == a.control.fibers[provider].phase); }
        } else {
            assert(z.control.fibers[provider].phase == a.control.fibers[provider].phase);
        }
    }
}

pub open spec fn open_episode<V>(model: s::Model<V>, states: Seq<s::State<V>>, labels: Seq<(usize, c::Rule)>, owner: usize) -> bool {
    &&& preservation::execution(model, states, labels)
    &&& preservation::well_formed(states.first())
    &&& forall|i: int| 0 <= i < states.len() ==> s::registered(states[i], owner)
        && states[i].control.fibers[owner].phase != Phase::Inactive
}

/// Lemma 59(2) and the provider half of Lemma 67, for an unbounded sequence of
/// the actual full-state rules. No phase invariant at intermediate providers is
/// supplied by the caller; it follows from the opening Active provider.
pub proof fn pinned_provider_lifetime<V>(model: s::Model<V>, states: Seq<s::State<V>>, labels: Seq<(usize, c::Rule)>, consumer: usize, binding: Binding)
    requires open_episode(model, states, labels, consumer),
        states.first().control.fibers[consumer].committed.contains(binding),
        states.first().control.fibers[binding.provider].phase == Phase::Active,
    ensures forall|i: int| 0 <= i < states.len() ==> {
        &&& states[i].control.fibers[consumer].committed == states.first().control.fibers[consumer].committed
        &&& s::registered(states[i], binding.provider)
        &&& (states[i].control.fibers[binding.provider].phase == Phase::Active || states[i].control.fibers[binding.provider].phase == Phase::Unloading)
    },
    decreases labels.len(),
{
    if labels.len() == 0 { assert(states.last() == states.first()); }
    else {
        let prefix = states.drop_last(); let previous = labels.drop_last();
        assert(open_episode(model, prefix, previous, consumer));
        pinned_provider_lifetime(model, prefix, previous, consumer, binding);
        preservation::execution_preservation(model, states, labels);
        let i = labels.len()-1;
        assert(prefix[i] == states[i]);
        assert(prefix.first() == states.first());
        assert(states[i].control.fibers[consumer].committed == states.first().control.fibers[consumer].committed);
        assert(states[i].control.fibers[consumer].committed.contains(binding));
        actual_accumulator_step(model, states[i], states[i+1], labels[i].0, labels[i].1, consumer);
        pinned_provider_phase_step(model, states[i], states[i+1], labels[i].0, labels[i].1, consumer, binding);
        assert forall|j: int| 0 <= j < states.len() implies {
            &&& states[j].control.fibers[consumer].committed == states.first().control.fibers[consumer].committed
            &&& s::registered(states[j], binding.provider)
            &&& (states[j].control.fibers[binding.provider].phase == Phase::Active || states[j].control.fibers[binding.provider].phase == Phase::Unloading)
        } by { if j < prefix.len() { assert(prefix[j] == states[j]); } }
    }
}

/// Every step acting on the committed provider has identity value map while
/// the consumer episode stays open. This discharges the provider case rather
/// than imposing pairwise independence on its extension and consumer actions.
pub proof fn entangled_provider_identity<V>(model: s::Model<V>, meaning: spec_fn(nat) -> Action<V>, forward: ForwardMeaning<V>, states: Seq<s::State<V>>, labels: Seq<(usize, c::Rule)>, consumer: usize, binding: Binding, index: int)
    requires open_episode(model, states, labels, consumer),
        states.first().control.fibers[consumer].committed.contains(binding),
        states.first().control.fibers[binding.provider].phase == Phase::Active,
        0 <= index < labels.len(), labels[index].0 == binding.provider,
    ensures step_word(model, meaning, forward, states[index], states[index+1], labels[index].0, labels[index].1).len() == 0,
        projection::project(states[index+1], ISet::full()) == projection::project(states[index], ISet::full()),
{
    pinned_provider_lifetime(model, states, labels, consumer, binding);
    preservation::execution_preservation(model, states, labels);
    let a = states[index]; let z = states[index+1]; let actor = labels[index].0; let rule = labels[index].1;
    pinned_provider_phase_step(model, a, z, actor, rule, consumer, binding);
    assert(primitive_projection(model, meaning, forward, a, z, actor, rule));
    actual_step_projection(model, meaning, forward, a, z, actor, rule);
}


/// Translate a defined grammar primitive into the explicit totalized profile.
/// Equality with the strict grammar is proved only where its transition exists.
/// The operation's selected result is still read from the actual input value.
pub open spec fn mediated_action<V, O>(node: mediated::Node<Port, V, O>) -> Action<V> {
    match node {
        mediated::Node::Unit => Action::Identity,
        mediated::Node::Operation { key, operation, .. } => Action::Operation { key,
            update: |v: V| match operation(v) { Some(y) => y.value, None => v } },
        mediated::Node::Provision { key, value, .. } => Action::Provision { key, value },
    }
}

pub open spec fn mediated_inverse<V, O>(node: mediated::Node<Port, V, O>, actual_input: IMap<Port, V>) -> Action<V> {
    match node {
        mediated::Node::Unit => Action::Identity,
        mediated::Node::Operation { key, operation, .. } => {
            let returned = operation(actual_input[key]).unwrap().undo;
            Action::Operation { key, update: |v: V| match returned(v) { Some(w) => w, None => v } }
        },
        mediated::Node::Provision { key, .. } => Action::Restriction { key },
    }
}

pub proof fn mediated_forward_meaning<V, O>(node: mediated::Node<Port, V, O>, state: IMap<Port, V>)
    requires mediated::run(node, state).is_some(),
    ensures apply(mediated_action(node), state) == mediated::run(node, state).unwrap().state,
{ }

/// The interpretation retains the actual yielded inverse, including its
/// dependence on the original value. On its domain it is the strict inverse;
/// outside that domain this profile chooses identity, without asserting a
/// corresponding strict transition or preservation of failure observations.
pub proof fn mediated_inverse_meaning<V, O>(node: mediated::Node<Port, V, O>, actual_input: IMap<Port, V>, state: IMap<Port, V>)
    requires mediated::run(node, actual_input).is_some(),
        (mediated::run(node, actual_input).unwrap().undo)(state).is_some(),
    ensures apply(mediated_inverse(node, actual_input), state)
        == (mediated::run(node, actual_input).unwrap().undo)(state).unwrap(),
        inverse_action(mediated_inverse(node, actual_input)),
{ }

pub proof fn mediated_local_witness<V, O>(node: mediated::Node<Port, V, O>, state: IMap<Port, V>)
    requires mediated::run(node, state).is_some(), mediated::stage_witness(node),
    ensures inverse_action(mediated_inverse(node, state)),
        apply(mediated_inverse(node, state), apply(mediated_action(node), state)) == state,
{
    mediated_forward_meaning(node, state);
    mediated_inverse_meaning(node, state, mediated::run(node, state).unwrap().state);
}

/// An earlier actual return remains in the accumulator throughout an open
/// episode, even across later own and foreign steps of arbitrary length.
pub proof fn returned_inverse_persists<V>(events: Seq<Event<V>>, index: int, inverse: Action<V>)
    requires 0 <= index < events.len(), events[index].returned == Some(inverse),
    ensures journal(events).contains(inverse),
    decreases events.len(),
{
    if index == events.len()-1 {
        assert(journal(events).last() == inverse);
    } else {
        returned_inverse_persists(events.drop_last(), index, inverse);
        if events.last().returned.is_some() {
            let i = choose|i: int| 0 <= i < journal(events.drop_last()).len() && journal(events.drop_last())[i] == inverse;
            assert(journal(events)[i] == inverse);
        }
    }
}

/// A provider's already landed extension supplies exactly the absorber needed
/// by a later consumer operation. This obtains compatibility from real trace
/// provenance, without asking whether the two forward operations commute.
pub proof fn consumer_after_actual_provision<V>(model: s::Model<V>, meaning: spec_fn(nat) -> Action<V>, forward: ForwardMeaning<V>, states: Seq<s::State<V>>, labels: Seq<(usize, c::Rule)>, owner: usize, birth: int, k: Port, update: spec_fn(V) -> V)
    requires episode_profile(model, meaning, forward, states, labels, owner),
        0 <= birth < labels.len(), labels[birth].0 == owner,
        lands(model, states[birth], states[birth+1], owner, labels[birth].1),
        meaning((model.iterate)(owner, states[birth].iterators[owner].unwrap(), states[birth]).inverse) == (Action::Restriction { key: k }),
    ensures erases(interpret(meaning, states.last().accumulators[owner]), k),
        compatible(interpret(meaning, states.last().accumulators[owner]), Action::Operation { key: k, update }),
{
    full_episode_recovery(model, meaning, forward, states, labels, owner);
    let events = events_of(model, meaning, forward, states, labels, owner);
    events_index(model, meaning, forward, states, labels, owner, birth);
    returned_inverse_persists(events, birth, Action::Restriction { key: k });
}

pub proof fn events_index<V>(model: s::Model<V>, meaning: spec_fn(nat) -> Action<V>, forward: ForwardMeaning<V>, states: Seq<s::State<V>>, labels: Seq<(usize, c::Rule)>, owner: usize, index: int)
    requires states.len() == labels.len()+1, 0 <= index < labels.len(),
    ensures events_of(model, meaning, forward, states, labels, owner).len() == labels.len(),
        events_of(model, meaning, forward, states, labels, owner)[index]
            == step_event(model, meaning, forward, states[index], states[index+1], labels[index].0, labels[index].1, owner),
    decreases labels.len(),
{
    if labels.len() > 1 {
        if index == labels.len()-1 {
            events_index(model, meaning, forward, states.drop_last(), labels.drop_last(), owner, index-1);
        } else {
            events_index(model, meaning, forward, states.drop_last(), labels.drop_last(), owner, index);
        }
    } else {
        assert(labels.len() == 1);
        assert(labels.drop_last().len() == 0);
        assert(events_of(model, meaning, forward, states.drop_last(), labels.drop_last(), owner) == Seq::<Event<V>>::empty());
    }
}


/// The initial Active-provider premise of `pinned_provider_lifetime` is
/// supplied by the real L-Begin target, which reads actual table presence.
pub proof fn begin_establishes_provider_pin<V>(model: s::Model<V>, a: s::State<V>, z: s::State<V>, consumer: usize, binding: Binding)
    requires preservation::well_formed(a), s::step(model, a, z, consumer, c::Rule::Begin),
        z.control.fibers[consumer].committed.contains(binding),
    ensures consumer != binding.provider, s::registered(z, binding.provider),
        z.control.fibers[binding.provider].phase == Phase::Active,
        z.tables[binding.provider].dom().contains(Port { key: binding.key, realm: binding.realm }),
{
    assert(s::target(a, consumer, z.control.fibers[consumer].committed));
    assert(s::publishes(a, Port { key: binding.key, realm: binding.realm }, binding.provider));
}

} // verus!
