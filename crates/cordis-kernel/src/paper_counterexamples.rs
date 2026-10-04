//! Counterexamples to transposition and canonical ordering in the encoded
//! full-State rules, with actual locally admissible Child calls. The original
//! Definition 48/56 total-context component representation is not instantiated
//! here, so these are not unconditional refutations of the original claims.
#[cfg(verus_keep_ghost)]
use crate::{global, preservation as typed, refinement as control, semantics as full, Phase};
use vstd::prelude::*;

verus! {

pub open spec fn creator_inserted() -> full::State<u64> {
    let empty = full::empty_state::<u64>();
    full::extend_child(empty, global::insert_fiber(empty.control, 0, None, ISet::empty(), ISet::empty()), 0, 0)
}

pub open spec fn creator_loading() -> full::State<u64> {
    full::edit(creator_inserted(), 0, Phase::Loading, ISet::empty(), Some(0), Seq::empty())
}

/// Effect 0 creates child 1 (a fresh allocation in this trace), whose effect 1
/// is idle. Effect 1 neither creates children nor changes tables. The component
/// behavior is selected by the iterator, not by an opaque actor-name branch.
pub open spec fn creation_model() -> full::Model<u64> {
    full::Model {
        iterate: |actor: usize, iterator: nat, s: full::State<u64>| full::Yield {
            state: if iterator == 0 {
                full::extend_child(s, global::insert_fiber(s.control, 1, Some(actor), ISet::empty(), ISet::empty()), 1, 1)
            } else { s },
            inverse: if iterator == 0 { 1nat } else { 0nat },
            next: None,
        },
        undo: |token: nat, s: full::State<u64>| if token == 1 {
            full::with_control(s, global::retire_fiber(s.control, 1))
        } else { s },
    }
}

pub open spec fn child_created() -> full::State<u64> {
    (creation_model().iterate)(0, 0, creator_loading()).state
}

pub open spec fn creator_finished() -> full::State<u64> {
    full::edit(child_created(), 0, Phase::Active, ISet::empty(), None, seq![1nat])
}

pub open spec fn descendant_inserted() -> full::State<u64> {
    let s = creator_finished();
    full::extend_child(s, global::insert_fiber(s.control, 2, Some(1), ISet::empty(), ISet::empty()), 2, 1)
}

/// Lemma 78(2) excludes an activation that creates the orchestration target n.
/// It must also exclude an activation that creates n's requested parent: here
/// actor 0 creates child 1, then O-Insert(2, parent=1) becomes possible. The
/// activation never creates 2, yet moving that O-Insert earlier loses its guard.
pub proof fn transposition_parent_counterexample()
    ensures
        typed::well_formed(creator_loading()), typed::well_formed(creator_finished()),
        typed::well_formed(descendant_inserted()),
        full::child_insert(creator_loading(), child_created(), 0, 1),
        !full::registered(creator_loading(), 1), full::registered(child_created(), 1),
        !full::registered(creator_loading(), 2), !full::registered(child_created(), 2),
        full::step(creation_model(), creator_loading(), creator_finished(), 0, control::Rule::Finish),
        full::step(creation_model(), creator_finished(), descendant_inserted(), 2, control::Rule::Insert),
        descendant_inserted().control.fibers[2usize].parent == Some(1usize),
        forall|middle: full::State<u64>| full::step(creation_model(), creator_loading(), middle, 2, control::Rule::Insert)
            ==> middle.control.fibers[2usize].parent != Some(1usize),
        full::same_tables(creator_loading(), (creation_model().undo)(1, child_created())),
{
    let empty = full::empty_state::<u64>();
    typed::empty_well_formed::<u64>();
    assert(empty == typed::empty::<u64>());
    assert(typed::insert_map(empty, creator_inserted(), 0));
    typed::insert_preservation(empty, creator_inserted(), 0);
    assert(full::target(creator_inserted(), 0, ISet::empty()));
    typed::begin_preservation(creator_inserted(), creator_loading(), 0);
    assert(typed::child_map(creator_loading(), child_created(), 0, 1));
    typed::child_preservation(creator_loading(), child_created(), 0, 1);
    assert(full::child_retire(child_created(), (creation_model().undo)(1, child_created()), 1));
    full::witnessed_child_lands(creation_model(), creator_loading(), 1, 0);
    assert(typed::admissible_step(creation_model(), creator_loading(), creator_finished(), 0, control::Rule::Finish));
    typed::full_preservation(creation_model(), creator_loading(), creator_finished(), 0, control::Rule::Finish);
    assert(typed::insert_map(creator_finished(), descendant_inserted(), 2));
    typed::insert_preservation(creator_finished(), descendant_inserted(), 2);
    assert(full::auxiliary_frame(creator_finished(), descendant_inserted(), 2));
    assert forall|middle: full::State<u64>| full::step(creation_model(), creator_loading(), middle, 2, control::Rule::Insert)
        implies middle.control.fibers[2usize].parent != Some(1usize) by {
        assert(!control::registered(creator_loading().control, 1));
    }
}

/// The two-step counterexample is reached from the empty registry by two prior
/// full rules. Child creation stays inside the actual iterator yield; it is not
/// replaced by a separate orchestration step in this witness.
pub proof fn transposition_counterexample_reachable()
    ensures full::reaches(creation_model(), full::empty_state::<u64>(), descendant_inserted(), 4),
{
    transposition_parent_counterexample();
    let states = seq![full::empty_state::<u64>(), creator_inserted(), creator_loading(), creator_finished(), descendant_inserted()];
    let labels = seq![(0usize, control::Rule::Insert), (0usize, control::Rule::Begin),
        (0usize, control::Rule::Finish), (2usize, control::Rule::Insert)];
    assert(full::auxiliary_frame(full::empty_state::<u64>(), creator_inserted(), 0));
    assert(full::shaped(creator_inserted()));
    assert(full::step(creation_model(), states[0], states[1], 0, control::Rule::Insert));
    assert(full::step(creation_model(), states[1], states[2], 0, control::Rule::Begin));
    assert(full::execution(creation_model(), states, labels)) by {
        assert forall|i: int| 0 <= i < labels.len() implies
            full::step(creation_model(), states[i], states[i + 1], labels[i].0, labels[i].1) by { }
    }
    full::execution_reaches(creation_model(), states, labels);
}

pub open spec fn idle_loading(s: full::State<u64>, n: usize) -> full::State<u64> {
    full::edit(s, n, Phase::Loading, ISet::empty(), Some(1), Seq::empty())
}

pub open spec fn idle_finished(s: full::State<u64>, n: usize) -> full::State<u64> {
    full::edit(idle_loading(s, n), n, Phase::Active, ISet::empty(), None, seq![0nat])
}

pub proof fn idle_activation(s: full::State<u64>, n: usize)
    requires typed::well_formed(s), full::registered(s, n), s.control.fibers[n].phase == Phase::Inactive,
        !s.control.fibers[n].retired, s.control.fibers[n].dependencies.is_empty(), s.effects[n] == 1,
    ensures
        full::step(creation_model(), s, idle_loading(s, n), n, control::Rule::Begin),
        full::step(creation_model(), idle_loading(s, n), idle_finished(s, n), n, control::Rule::Finish),
        typed::well_formed(idle_loading(s, n)), typed::well_formed(idle_finished(s, n)),
{
    assert(full::target(s, n, ISet::empty()));
    typed::begin_preservation(s, idle_loading(s, n), n);
    let a = idle_loading(s, n);
    assert((creation_model().iterate)(n, a.iterators[n].unwrap(), a).state == a);
    assert(typed::table_map(a, a, n));
    assert(full::coherent(a, n));
    assert(full::step(creation_model(), a, idle_finished(s, n), n, control::Rule::Finish));
    typed::full_preservation(creation_model(), a, idle_finished(s, n), n, control::Rule::Finish);
}

pub open spec fn canonical_counterexample_end() -> full::State<u64> {
    idle_finished(idle_finished(descendant_inserted(), 1), 2)
}

pub open spec fn canonical_counterexample_states() -> Seq<full::State<u64>> {
    let s4 = descendant_inserted();
    let s6 = idle_finished(s4, 1);
    seq![full::empty_state::<u64>(), creator_inserted(), creator_loading(), creator_finished(),
        s4, idle_loading(s4, 1), s6, idle_loading(s6, 2), idle_finished(s6, 2)]
}

pub open spec fn canonical_counterexample_labels() -> Seq<(usize, control::Rule)> {
    seq![(0usize, control::Rule::Insert), (0usize, control::Rule::Begin),
        (0usize, control::Rule::Finish), (2usize, control::Rule::Insert),
        (1usize, control::Rule::Begin), (1usize, control::Rule::Finish),
        (2usize, control::Rule::Begin), (2usize, control::Rule::Finish)]
}

/// Empty provisions are total in every shaped configuration of these
/// components, not only in the particular endpoint of the witness.
pub proof fn empty_provisions_total<V>(s: full::State<V>)
    requires full::shaped(s), forall|n: usize| full::registered(s, n) ==> s.control.fibers[n].provisions.is_empty(),
    ensures full::total_active(s),
{
    assert forall|n: usize| full::registered(s, n) && s.control.fibers[n].phase == Phase::Active implies
        s.tables[n].dom() == s.control.fibers[n].provisions by {
        assert(s.tables[n].dom().subset_of(s.control.fibers[n].provisions));
        assert(s.tables[n].dom() =~= s.control.fibers[n].provisions);
    }
}

/// Theorem 80(1)'s other hypotheses are present: an actual eight-step execution
/// reaches a well-formed quiet state, every component has empty (hence total)
/// provisions, and both provider precedence and the parent/provider union have
/// explicit ranks. All three registered fibers are supported and Active.
#[verifier::rlimit(30)]
pub proof fn canonical_counterexample_quiet()
    ensures
        full::execution(creation_model(), canonical_counterexample_states(), canonical_counterexample_labels()),
        full::reaches(creation_model(), full::empty_state::<u64>(), canonical_counterexample_end(), 8),
        typed::well_formed(canonical_counterexample_end()), full::quiet(canonical_counterexample_end()),
        full::total_active(canonical_counterexample_end()),
        global::precedence_ranking(canonical_counterexample_end().control, seq![0nat, 1nat, 2nat]),
        global::support_ranking(canonical_counterexample_end().control, seq![0nat, 1nat, 2nat]),
        global::support_solution(canonical_counterexample_end().control, canonical_counterexample_end().control.fibers.dom()),
        global::active(canonical_counterexample_end().control) == canonical_counterexample_end().control.fibers.dom(),
        forall|n: usize| full::registered(canonical_counterexample_end(), n)
            ==> canonical_counterexample_end().control.fibers[n].provisions.is_empty(),
        forall|i: int| 0 <= i < canonical_counterexample_labels().len()
            && !global::lifecycle_rule(canonical_counterexample_labels()[i].1) ==> i == 0 || i == 3,
{
    transposition_parent_counterexample();
    transposition_counterexample_reachable();
    let s4 = descendant_inserted();
    idle_activation(s4, 1);
    let s6 = idle_finished(s4, 1);
    idle_activation(s6, 2);
    let s8 = canonical_counterexample_end();
    assert forall|n: usize| full::registered(s8, n) implies n == 0 || n == 1 || n == 2 by { }
    assert forall|n: usize| full::registered(s8, n) implies {
        &&& s8.control.fibers[n].phase == Phase::Active
        &&& s8.control.fibers[n].provisions.is_empty()
        &&& s8.control.fibers[n].dependencies.is_empty()
        &&& s8.control.fibers[n].committed.is_empty()
        &&& !s8.control.fibers[n].retired
        &&& full::coherent(s8, n)
    } by { }
    empty_provisions_total(s8);
    assert(global::active(s8.control) =~= s8.control.fibers.dom());
    assert forall|provider: usize, consumer: usize| !global::predecessor(s8.control, provider, consumer) by {
        if full::registered(s8, provider) { assert(s8.control.fibers[provider].provisions.is_empty()); }
    }
    assert(global::support_ranking(s8.control, seq![0nat, 1nat, 2nat]));
    assert(global::support_solution(s8.control, s8.control.fibers.dom())) by {
        assert forall|n: usize| s8.control.fibers.dom().contains(n)
            == global::support_clause(s8.control, s8.control.fibers.dom(), n) by { }
    }
    let states = canonical_counterexample_states();
    let labels = canonical_counterexample_labels();
    assert(full::step(creation_model(), states[0], states[1], 0, control::Rule::Insert));
    assert(full::step(creation_model(), states[1], states[2], 0, control::Rule::Begin));
    assert(full::execution(creation_model(), states, labels)) by {
        assert forall|i: int| 0 <= i < labels.len() implies
            full::step(creation_model(), states[i], states[i + 1], labels[i].0, labels[i].1) by { }
    }
    full::execution_reaches(creation_model(), states, labels);
}

/// A name-independent obstruction, so a bijective renaming cannot repair the
/// canonical prefix. An empty registry followed by one Insert contains only
/// that inserted name; inserting another fiber under a third name is illegal.
pub proof fn missing_parent_prefix<V>(model: full::Model<V>, first: full::State<V>, second: full::State<V>,
    creator: usize, child: usize, descendant: usize)
    requires creator != child,
        full::step(model, full::empty_state::<V>(), first, creator, control::Rule::Insert),
        full::step(model, first, second, descendant, control::Rule::Insert),
    ensures second.control.fibers[descendant].parent != Some(child),
{
    assert(!control::registered(full::empty_state::<V>().control, child));
    assert(!control::registered(first.control, child));
}

/// The only orchestration inputs of the quiet witness are Insert(0, root) and
/// Insert(2, parent=1), in that order. Both act on fibers the orchestrator itself
/// inserted. Theorem 80(1) requires both before *every* lifecycle step, but even
/// this necessary two-input prefix does not exist under the printed O-Insert
/// parent guard. This refutes that canonical ordering, not clause (2).
pub proof fn canonical_orchestration_prefix_impossible()
    ensures !exists|first: full::State<u64>, second: full::State<u64>|
        full::step(creation_model(), full::empty_state::<u64>(), first, 0, control::Rule::Insert)
        && full::step(creation_model(), first, second, 2, control::Rule::Insert)
        && second.control.fibers[2usize].parent == Some(1usize),
{
    assert forall|first: full::State<u64>, second: full::State<u64>|
        full::step(creation_model(), full::empty_state::<u64>(), first, 0, control::Rule::Insert)
        && full::step(creation_model(), first, second, 2, control::Rule::Insert)
        implies second.control.fibers[2usize].parent != Some(1usize) by {
        missing_parent_prefix(creation_model(), first, second, 0, 1, 2);
    }
}

} // verus!
