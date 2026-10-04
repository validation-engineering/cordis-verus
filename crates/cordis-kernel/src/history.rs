//! Finite effect histories and a concrete witnessed journal.
//!
//! History normalization covers arbitrary interleavings that preserve the order
//! within each effect group. Cross-group transformations (including inverses)
//! must commute. This is a consequence of Definition 42(1), not a substitute for
//! its separate inverse/continuation stability obligation for dynamic iterators.
use crate::resources::{Cell, Inverse, ResourceError, Store};
use vstd::prelude::*;

verus! {
/// An operation tagged with the effect group that owns it.
pub type History<S> = Seq<(nat, spec_fn(S) -> S)>;

pub open spec fn operations<S>(history: History<S>) -> Seq<spec_fn(S) -> S>
    decreases history.len(),
{
    if history.len() == 0 { Seq::empty() }
    else { operations(history.drop_last()).push(history.last().1) }
}

pub open spec fn lane<S>(history: History<S>, owner: nat) -> Seq<spec_fn(S) -> S>
    decreases history.len(),
{
    if history.len() == 0 { Seq::empty() }
    else if history.last().0 == owner {
        lane(history.drop_last(), owner).push(history.last().1)
    } else { lane(history.drop_last(), owner) }
}

pub open spec fn without<S>(history: History<S>, owner: nat) -> History<S>
    decreases history.len(),
{
    if history.len() == 0 { Seq::empty() }
    else if history.last().0 == owner { without(history.drop_last(), owner) }
    else { without(history.drop_last(), owner).push(history.last()) }
}

pub open spec fn independent<S>(history: History<S>) -> bool {
    forall|i: int, j: int, state: S|
        0 <= i < history.len() && 0 <= j < history.len()
        && history[i].0 != history[j].0
        ==> #[trigger] (history[i].1)((history[j].1)(state))
            == (history[j].1)((history[i].1)(state))
}

/// Every projected operation retains an originating record.
pub proof fn operation_origin<S>(history: History<S>, index: int)
    requires 0 <= index < operations(history).len(),
    ensures exists|j: int| 0 <= j < history.len() && history[j].1 == operations(history)[index],
    decreases history.len(),
{
    if index == operations(history).len() - 1 {
        assert(history[history.len() - 1].1 == operations(history)[index]);
    } else {
        operation_origin(history.drop_last(), index);
        let j = choose|j: int| 0 <= j < history.drop_last().len()
            && history.drop_last()[j].1 == operations(history.drop_last())[index];
        assert(history[j].1 == operations(history)[index]);
    }
}

pub proof fn without_origin<S>(history: History<S>, owner: nat, index: int)
    requires 0 <= index < without(history, owner).len(),
    ensures exists|j: int| 0 <= j < history.len()
        && history[j] == without(history, owner)[index] && history[j].0 != owner,
    decreases history.len(),
{
    if history.last().0 != owner && index == without(history, owner).len() - 1 {
        assert(history[history.len() - 1] == without(history, owner)[index]);
    } else {
        without_origin(history.drop_last(), owner, index);
        let j = choose|j: int| 0 <= j < history.drop_last().len()
            && history.drop_last()[j] == without(history.drop_last(), owner)[index]
            && history.drop_last()[j].0 != owner;
        assert(history[j] == without(history, owner)[index] && history[j].0 != owner);
    }
}

/// Move one whole group to the front while preserving both relative orders.
/// There is no restriction on the number or placement of foreign operations.
pub proof fn partition<S>(history: History<S>, owner: nat, state: S)
    requires independent(history),
    ensures crate::calculus::run(operations(history), state)
        == crate::calculus::run(operations(without(history, owner)), crate::calculus::run(lane(history, owner), state)),
    decreases history.len(),
{
    reveal_with_fuel(crate::calculus::run, 2);
    reveal_with_fuel(operations, 2);
    if history.len() > 0 {
        let prefix = history.drop_last();
        partition(prefix, owner, state);
        if history.last().0 == owner {
            let current = history.last().1;
            let foreign = without(prefix, owner);
            assert forall|i: int, s: S| 0 <= i < operations(foreign).len() implies
                #[trigger] current((operations(foreign)[i])(s))
                    == (operations(foreign)[i])(current(s)) by {
                operation_origin(foreign, i);
                let j = choose|j: int| 0 <= j < foreign.len()
                    && foreign[j].1 == operations(foreign)[i];
                without_origin(prefix, owner, j);
                let k = choose|k: int| 0 <= k < prefix.len()
                    && prefix[k] == foreign[j] && prefix[k].0 != owner;
                assert(history[k].0 != history[history.len() - 1].0);
            }
            crate::calculus::inverse_commutes_with_trace(current, operations(foreign), crate::calculus::run(lane(prefix, owner), state));
            assert(lane(history, owner).drop_last() =~= lane(prefix, owner));
            assert(operations(history).drop_last() =~= operations(prefix));
            assert(crate::calculus::run(lane(history, owner), state) == current(crate::calculus::run(lane(prefix, owner), state)));
            assert(crate::calculus::run(operations(history), state) == current(crate::calculus::run(operations(prefix), state)));
            assert(crate::calculus::run(operations(history), state)
                == crate::calculus::run(operations(without(history, owner)), crate::calculus::run(lane(history, owner), state)));
        } else {
            assert(operations(history).drop_last() =~= operations(prefix));
            assert(without(history, owner).drop_last() =~= without(prefix, owner));
            assert(operations(without(history, owner)).drop_last() =~= operations(without(prefix, owner)));
            assert(crate::calculus::run(operations(history), state)
                == crate::calculus::run(operations(without(history, owner)), crate::calculus::run(lane(history, owner), state)));
        }
    }
}

/// Erasing another group leaves each surviving group's order unchanged.
pub proof fn projected_lanes<S>(history: History<S>, removed: nat, owner: nat)
    requires removed != owner,
    ensures lane(without(history, removed), owner) == lane(history, owner),
    decreases history.len(),
{
    reveal_with_fuel(lane, 2);
    if history.len() > 0 {
        projected_lanes(history.drop_last(), removed, owner);
        if history.last().0 != removed {
            assert(without(history, removed).drop_last() =~= without(history.drop_last(), removed));
        }
    }
}

/// A canonical finite assembly: decreasing group identifier, retaining each
/// group's internal order. It is a specification, not a runtime scheduler.
pub open spec fn canonical<S>(history: History<S>, count: nat, state: S) -> S
    decreases count,
{
    if count == 0 { state }
    else { canonical(history, (count - 1) as nat, crate::calculus::run(lane(history, (count - 1) as nat), state)) }
}

pub proof fn canonical_without<S>(history: History<S>, removed: nat, count: nat, state: S)
    requires count <= removed,
    ensures canonical(without(history, removed), count, state) == canonical(history, count, state),
    decreases count,
{
    if count > 0 {
        projected_lanes(history, removed, (count - 1) as nat);
        canonical_without(history, removed, (count - 1) as nat,
            crate::calculus::run(lane(history, (count - 1) as nat), state));
    }
}

/// Construct the canonical value of every bounded independent history. All
/// forward/inverse pairs across different groups are included in independence.
pub proof fn normalize<S>(history: History<S>, count: nat, state: S)
    requires independent(history),
        forall|i: int| 0 <= i < history.len() ==> (#[trigger] history[i]).0 < count,
    ensures crate::calculus::run(operations(history), state) == canonical(history, count, state),
    decreases count,
{
    if count == 0 {
        if history.len() > 0 { assert(history[0].0 < 0); }
    } else {
        let owner = (count - 1) as nat;
        let remaining = without(history, owner);
        assert forall|i: int| 0 <= i < remaining.len() implies
            (#[trigger] remaining[i]).0 < count - 1 by {
            without_origin(history, owner, i);
            let j = choose|j: int| 0 <= j < history.len()
                && history[j] == remaining[i] && history[j].0 != owner;
        }
        assert forall|i: int, j: int, s: S|
            0 <= i < remaining.len() && 0 <= j < remaining.len()
            && remaining[i].0 != remaining[j].0 implies
            #[trigger] (remaining[i].1)((remaining[j].1)(s))
                == (remaining[j].1)((remaining[i].1)(s)) by {
            without_origin(history, owner, i);
            without_origin(history, owner, j);
            let a = choose|a: int| 0 <= a < history.len()
                && history[a] == remaining[i] && history[a].0 != owner;
            let b = choose|b: int| 0 <= b < history.len()
                && history[b] == remaining[j] && history[b].0 != owner;
        }
        partition(history, owner, state);
        normalize(remaining, owner, crate::calculus::run(lane(history, owner), state));
        canonical_without(history, owner, owner, crate::calculus::run(lane(history, owner), state));
    }
}

pub proof fn canonical_same_lanes<S>(left: History<S>, right: History<S>, count: nat, state: S)
    requires forall|owner: nat| owner < count ==> #[trigger] lane(left, owner) == lane(right, owner),
    ensures canonical(left, count, state) == canonical(right, count, state),
    decreases count,
{
    if count > 0 {
        canonical_same_lanes(left, right, (count - 1) as nat,
            crate::calculus::run(lane(left, (count - 1) as nat), state));
    }
}

/// Any two legal interleavings of the same independent, ordered group histories
/// agree. This proves schedule independence of fixed witnessed histories; whole
/// lifecycle confluence additionally needs support, termination and stable yields.
pub proof fn interleaving_confluence<S>(left: History<S>, right: History<S>, count: nat, state: S)
    requires independent(left), independent(right),
        forall|i: int| 0 <= i < left.len() ==> (#[trigger] left[i]).0 < count,
        forall|i: int| 0 <= i < right.len() ==> (#[trigger] right[i]).0 < count,
        forall|owner: nat| owner < count ==> #[trigger] lane(left, owner) == lane(right, owner),
    ensures crate::calculus::run(operations(left), state) == crate::calculus::run(operations(right), state),
{
    normalize(left, count, state);
    normalize(right, count, state);
    canonical_same_lanes(left, right, count, state);
}

/// A closed group may be erased from an arbitrary interleaving, preserving all
/// foreign operations. Its recovery is needed only at the actual entry state.
pub proof fn erase_closed_group<S>(history: History<S>, owner: nat, state: S)
    requires independent(history), crate::calculus::run(lane(history, owner), state) == state,
    ensures crate::calculus::run(operations(history), state) == crate::calculus::run(operations(without(history, owner)), state),
{
    partition(history, owner, state);
}

/// Concatenation of histories agrees with sequential execution.
pub proof fn run_concatenation<S>(first: Seq<spec_fn(S) -> S>, second: Seq<spec_fn(S) -> S>, state: S)
    ensures crate::calculus::run(first + second, state) == crate::calculus::run(second, crate::calculus::run(first, state)),
    decreases second.len(),
{
    if second.len() == 0 { assert(first + second =~= first); }
    else {
        assert((first + second).drop_last() =~= first + second.drop_last());
        run_concatenation(first, second.drop_last(), state);
    }
}

pub proof fn inverse_history<S>(inverses: Seq<spec_fn(S) -> S>, state: S)
    ensures crate::calculus::run(inverses.reverse(), state) == crate::calculus::unwind(inverses, state),
    decreases inverses.len(),
{
    reveal_with_fuel(crate::calculus::run, 2);
    if inverses.len() > 0 {
        let last = inverses.last();
        assert(inverses.reverse() =~= seq![last] + inverses.drop_last().reverse());
        assert(seq![last].drop_last() =~= Seq::empty());
        assert(crate::calculus::run(seq![last], state) == last(state));
        run_concatenation(seq![last], inverses.drop_last().reverse(), state);
        inverse_history(inverses.drop_last(), last(state));
    }
}

/// Derive closed-group erasure from the yielded witnesses, rather than assuming
/// that the completed group is a no-op. Inverses within a group remain LIFO.
pub proof fn recover_group<S>(history: History<S>, owner: nat,
    forward: Seq<spec_fn(S) -> S>, inverses: Seq<spec_fn(S) -> S>, state: S)
    requires independent(history), forward.len() == inverses.len(),
        lane(history, owner) == forward + inverses.reverse(),
        forall|i: int, s: S| 0 <= i < forward.len() ==>
            #[trigger] (inverses[i])((forward[i])(s)) == s,
    ensures crate::calculus::run(operations(history), state) == crate::calculus::run(operations(without(history, owner)), state),
{
    let eq = |a: S, b: S| a == b;
    crate::calculus::recover_sequence(forward, inverses, eq, state);
    inverse_history(inverses, crate::calculus::run(forward, state));
    run_concatenation(forward, inverses.reverse(), state);
    erase_closed_group(history, owner, state);
}

/// A concrete operation refines an abstract operation through an observation
/// map. Ghost bookkeeping and unobservable concrete state may differ freely.
pub open spec fn trace_refines<S, O>(concrete: History<S>, abstract_history: History<O>,
    observe: spec_fn(S) -> O) -> bool {
    &&& concrete.len() == abstract_history.len()
    &&& forall|i: int| 0 <= i < concrete.len() ==>
        (#[trigger] concrete[i]).0 == abstract_history[i].0
    &&& forall|i: int, s: S| 0 <= i < concrete.len() ==>
        #[trigger] observe((concrete[i].1)(s)) == (abstract_history[i].1)(observe(s))
}

/// Lift one-step simulation to a whole finite effect history.
pub proof fn run_refinement<S, O>(concrete: History<S>, abstract_history: History<O>,
    observe: spec_fn(S) -> O, state: S)
    requires trace_refines(concrete, abstract_history, observe),
    ensures observe(crate::calculus::run(operations(concrete), state))
        == crate::calculus::run(operations(abstract_history), observe(state)),
    decreases concrete.len(),
{
    if concrete.len() > 0 {
        assert(operations(concrete).drop_last() =~= operations(concrete.drop_last()));
        assert(operations(abstract_history).drop_last() =~= operations(abstract_history.drop_last()));
        run_refinement(concrete.drop_last(), abstract_history.drop_last(), observe, state);
    }
}

/// Schedule independence up to observations, obtained by refinement to commuting
/// abstract generators. Concrete operations need not commute on hidden state.
pub proof fn observational_confluence<S, O>(left: History<S>, right: History<S>,
    abstract_left: History<O>, abstract_right: History<O>, observe: spec_fn(S) -> O,
    count: nat, left_state: S, right_state: S)
    requires trace_refines(left, abstract_left, observe), trace_refines(right, abstract_right, observe),
        observe(left_state) == observe(right_state),
        independent(abstract_left), independent(abstract_right),
        forall|i: int| 0 <= i < abstract_left.len() ==> (#[trigger] abstract_left[i]).0 < count,
        forall|i: int| 0 <= i < abstract_right.len() ==> (#[trigger] abstract_right[i]).0 < count,
        forall|owner: nat| owner < count ==>
            #[trigger] lane(abstract_left, owner) == lane(abstract_right, owner),
    ensures observe(crate::calculus::run(operations(left), left_state)) == observe(crate::calculus::run(operations(right), right_state)),
{
    run_refinement(left, abstract_left, observe, left_state);
    run_refinement(right, abstract_right, observe, right_state);
    interleaving_confluence(abstract_left, abstract_right, count, observe(left_state));
}

/// One dynamic iterator stage: the context, inverse and continuation are all
/// computed from the entry context. A continuation identifier names its next
/// stage; a complete iterator model must close its stage family under these IDs.
pub type IteratorStep<S> = spec_fn(S) -> (S, spec_fn(S) -> S, Option<nat>);

pub open spec fn forward_of<S>(step: IteratorStep<S>) -> spec_fn(S) -> S {
    |state: S| step(state).0
}

pub open spec fn generators<S>(step: IteratorStep<S>) -> ISet<spec_fn(S) -> S> {
    ISet::new(|operation: spec_fn(S) -> S| operation == forward_of(step)
        || exists|state: S| (#[trigger] step(state)).1 == operation)
}

pub open spec fn commutes<S>(left: spec_fn(S) -> S, right: spec_fn(S) -> S) -> bool {
    forall|state: S| #[trigger] left(right(state)) == right(left(state))
}

/// Equation (40): independence preserves both the yielded witness and the next
/// iterator, not merely the resulting context or a boolean completion flag.
pub open spec fn stable_yield<S>(step: IteratorStep<S>, foreign: spec_fn(S) -> S) -> bool {
    forall|state: S| {
        let reached = #[trigger] step(foreign(state));
        &&& reached.1 == step(state).1
        &&& reached.2 == step(state).2
    }
}

/// Definition 42 restricted to one pair of reachable stages. Its four
/// generator pairs include forward/forward, both forward/inverse orientations,
/// and inverse/inverse at every context where a witness can be yielded.
pub open spec fn independent_stages<S>(left: IteratorStep<S>, right: IteratorStep<S>) -> bool {
    &&& forall|f: spec_fn(S) -> S, g: spec_fn(S) -> S|
        generators(left).contains(f) && generators(right).contains(g) ==> #[trigger] commutes(f, g)
    &&& forall|g: spec_fn(S) -> S| generators(right).contains(g) ==> #[trigger] stable_yield(left, g)
    &&& forall|f: spec_fn(S) -> S| generators(left).contains(f) ==> #[trigger] stable_yield(right, f)
}

/// Stability extends from generators to every finite composition of them.
pub proof fn yield_stability_sequence<S>(step: IteratorStep<S>, foreign: Seq<spec_fn(S) -> S>, state: S)
    requires forall|i: int| 0 <= i < foreign.len() ==> stable_yield(step, foreign[i]),
    ensures step(crate::calculus::run(foreign, state)).1 == step(state).1,
        step(crate::calculus::run(foreign, state)).2 == step(state).2,
    decreases foreign.len(),
{
    if foreign.len() > 0 {
        yield_stability_sequence(step, foreign.drop_last(), state);
        assert(stable_yield(step, foreign.last()));
    }
}

/// Swap two dynamic iterator stages. Context, both yielded records and the
/// composed inverse agree; retaining only forward-map commutation would not
/// suffice for these conclusions. Apply to every reachable stage pair for a
/// full iterator independence witness.
pub proof fn iterator_diamond<S>(left: IteratorStep<S>, right: IteratorStep<S>, state: S, undo_state: S)
    requires independent_stages(left, right),
    ensures
        right(left(state).0).0 == left(right(state).0).0,
        left(right(state).0).1 == left(state).1,
        left(right(state).0).2 == left(state).2,
        right(left(state).0).1 == right(state).1,
        right(left(state).0).2 == right(state).2,
        (left(state).1)((right(left(state).0).1)(undo_state))
            == (right(state).1)((left(right(state).0).1)(undo_state)),
{
    assert(generators(left).contains(forward_of(left)));
    assert(generators(right).contains(forward_of(right)));
    assert(generators(left).contains(left(state).1));
    assert(generators(right).contains(right(state).1));
    assert(commutes(forward_of(left), forward_of(right)));
    assert(stable_yield(left, forward_of(right)));
    assert(stable_yield(right, forward_of(left)));
    assert(commutes(left(state).1, right(state).1));
    let f = forward_of(left);
    let g = forward_of(right);
    assert(f(g(state)) == g(f(state)));
    assert(left(g(state)).1 == left(state).1);
    assert(left(g(state)).2 == left(state).2);
    assert(right(f(state)).1 == right(state).1);
    assert(right(f(state)).2 == right(state).2);
    assert((left(state).1)((right(state).1)(undo_state))
        == (right(state).1)((left(state).1)(undo_state)));
}

/// Dynamic witnesses recover their actual application states. This avoids the
/// stronger fixed-witness premise that each returned inverse undo every context.
pub proof fn dynamic_pair_recovery<S>(left: IteratorStep<S>, right: IteratorStep<S>, state: S)
    requires
        forall|s: S| #[trigger] (left(s).1)(left(s).0) == s,
        forall|s: S| #[trigger] (right(s).1)(right(s).0) == s,
    ensures (left(state).1)((right(left(state).0).1)(right(left(state).0).0)) == state,
{ }

/// A journal owns its store and the opaque witnesses returned by that store.
/// Ghost snapshots are erased: production storage contains only Store + inverses.
/// Unlike raw Store::undo, this API cannot apply a witness to another store.
pub struct Journal {
    store: Store,
    entries: Vec<Inverse>,
    _states: Ghost<Seq<Seq<Cell>>>,
}

impl Journal {
    pub closed spec fn view(&self) -> Seq<Cell> { self.store.view() }
    pub closed spec fn initial(&self) -> Seq<Cell> { self._states@[0] }
    pub closed spec fn depth(&self) -> nat { self.entries.len() as nat }
    pub closed spec fn snapshots(&self) -> Seq<Seq<Cell>> { self._states@ }
    closed spec fn entry_valid(&self, i: int) -> bool {
        let inverse = &self.entries[i];
        &&& 0 <= inverse.slot() < self._states@[i].len()
        &&& inverse.pre() == self._states@[i][inverse.slot()]
        &&& Store::valid_cell(inverse.pre())
        &&& self._states@[i + 1] == self._states@[i].update(inverse.slot(), inverse.post())
    }
    pub closed spec fn wf(&self) -> bool {
        &&& self.store.wf()
        &&& self._states@.len() == self.entries.len() + 1
        &&& self.store.view() == self._states@.last()
        &&& forall|i: int| 0 <= i < self.entries.len() ==> #[trigger] self.entry_valid(i)
    }


    /// An empty witnessed history has exactly its initial state.
    pub proof fn empty_restored(&self)
        requires self.wf(), self.depth() == 0,
        ensures self.view() == self.initial(),
    { }

    pub fn new(values: Vec<u64>) -> (journal: Self)
        ensures journal.wf(), journal.depth() == 0, journal.initial() == journal.view(),
            journal.view().len() == values.len(),
            forall|i: int| 0 <= i < values.len() ==> journal.view()[i]
                == (Cell { value: values[i], owner: None, depth: 0 }),
    {
        let store = Store::new(values);
        let ghost states = seq![store.view()];
        Journal { store, entries: Vec::new(), _states: Ghost(states) }
    }

    pub fn resource_len(&self) -> (length:usize)
        ensures length == self.view().len(),
    { self.store.resource_len() }
    pub fn written(&self,index:usize) -> (yes:bool)
        ensures yes == (index < self.view().len() && self.view()[index as int].depth > 0),
    { self.store.written(index) }
    pub fn read(&self, index: usize) -> (value: Option<u64>)
        ensures value == if index < self.view().len() { Some(self.view()[index as int].value) } else { None },
    { self.store.read(index) }

    pub fn len(&self) -> (length: usize)
        ensures length == self.depth(),
    { self.entries.len() }

    pub fn is_empty(&self) -> (empty: bool)
        ensures empty == (self.depth() == 0),
    { self.entries.is_empty() }

    /// Successful writes extend the witnessed history; failures are atomic.
    pub fn write(&mut self, owner: u64, index: usize, value: u64) -> (result: Result<(), ResourceError>)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).initial() == old(self).initial(),
            result.is_err() ==> final(self).view() == old(self).view()
                && final(self).snapshots() == old(self).snapshots() && final(self).depth() == old(self).depth(),
            (old(self).depth() < usize::MAX && index < old(self).view().len()
                && (old(self).view()[index as int].owner.is_none() || old(self).view()[index as int].owner == Some(owner))
                && old(self).view()[index as int].depth < u64::MAX) ==> result.is_ok(),
            result.is_ok() ==> final(self).depth() == old(self).depth() + 1
                && final(self).snapshots() == old(self).snapshots().push(final(self).view())
                && index < old(self).view().len()
                && final(self).view() == old(self).view().update(index as int,
                    Cell {value,owner:Some(owner),depth:(old(self).view()[index as int].depth+1) as u64})
                && final(self).view()[index as int].value == value,
    {
        let ghost prior = *self;
        if self.entries.len() == usize::MAX { return Err(ResourceError::Capacity); }
        match self.store.write(owner, index, value) {
            Err(error) => {
                proof {
                    assert forall|i: int| 0 <= i < self.entries.len() implies #[trigger] self.entry_valid(i) by {
                        assert(prior.entry_valid(i));
                    }
                    assert(self.wf());
                }
                Err(error)
            },
            Ok(inverse) => {
                self.entries.push(inverse);
                proof {
                    self._states = Ghost(self._states@.push(self.store.view()));
                    assert forall|i: int| 0 <= i < self.entries.len() implies #[trigger] self.entry_valid(i) by {
                        if i < prior.entries.len() { assert(prior.entry_valid(i)); }
                    }
                }
                assert(self.wf());
                Ok(())
            }
        }
    }

    /// Pop exactly one witnessed effect. Undo cannot fail: the private history
    /// invariant proves that the top witness belongs to this store and state.
    pub fn rollback_one(&mut self) -> (removed: bool)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).initial() == old(self).initial(),
            removed == (old(self).depth() > 0),
            removed ==> final(self).depth() + 1 == old(self).depth()
                && final(self).snapshots() == old(self).snapshots().drop_last()
                && final(self).view() == old(self).snapshots()[old(self).depth() - 1],
            !removed ==> final(self).view() == old(self).view()
                && final(self).snapshots() == old(self).snapshots()
                && final(self).depth() == old(self).depth(),
    {
        if self.entries.is_empty() { return false; }
        let ghost prior = *self;
        assert(self.entry_valid(self.entries.len() - 1));
        let ghost previous = self._states@[self.entries.len() - 1];
        let inverse = self.entries.pop().unwrap();
        assert(self.store.view()[inverse.slot()] == inverse.post());
        let ghost slot = inverse.slot();
        let ghost before = inverse.pre();
        let _result = self.store.undo(inverse);
        assert(_result.is_ok());
        assert(self.store.view() =~= previous);
        proof {
            self._states = Ghost(self._states@.drop_last());
            assert forall|i: int| 0 <= i < self.entries.len() implies #[trigger] self.entry_valid(i) by {
                assert(prior.entry_valid(i));
            }
        }
        true
    }

    /// Restore a saved prefix; every later effect is withdrawn in reverse order.
    /// `keep == 0` restores the exact initial cells, ownership and depth included.
    pub fn rollback_to(&mut self, keep: usize) -> (valid: bool)
        requires old(self).wf(),
        ensures final(self).wf(), final(self).initial() == old(self).initial(),
            valid == (keep <= old(self).depth()),
            valid ==> final(self).depth() == keep
                && final(self).view() == old(self).snapshots()[keep as int]
                && final(self).snapshots() == old(self).snapshots().subrange(0, keep as int + 1),
            !valid ==> final(self).view() == old(self).view()
                && final(self).snapshots() == old(self).snapshots() && final(self).depth() == old(self).depth(),
    {
        if keep > self.entries.len() { return false; }
        let ghost original = self._states@;
        assert(self._states@ =~= original.subrange(0, self.depth() as int + 1));
        while self.entries.len() > keep
            invariant self.wf(), keep <= self.depth(),
                self.depth() < original.len(), original.len() > 0,
                self._states@ == original.subrange(0, self.depth() as int + 1),
                self.initial() == original[0],
            decreases self.entries.len() - keep,
        {
            let _removed = self.rollback_one();
            assert(_removed);
            assert(self._states@ =~= original.subrange(0, self.depth() as int + 1));
        }
        true
    }
}
} // verus!
