//! Canonical execution of a finite family of dynamic effect iterators.
//!
//! Independence is imposed on the primitive stages, including stability of
//! their returned inverse and continuation. Complete schedules need not be
//! supplied with equal projected histories: lawful exchange derives equality
//! of the final context and of every actual inverse accumulator. This is the
//! iterator layer of transposition, not a theorem about arbitrary lifecycle
//! orchestration, dynamic child insertion, or an unverified asynchronous host.
#[cfg(verus_keep_ghost)]
use crate::history::independent_stages;
use crate::history::IteratorStep;
#[cfg(verus_keep_ghost)]
use crate::refinement as control;
#[cfg(verus_keep_ghost)]
use crate::{Binding, Phase};
use vstd::prelude::*;

verus! {

/// A component's continuation selects its next stage from this fixed family.
pub type Family<S> = spec_fn(nat, nat) -> IteratorStep<S>;

#[verifier::reject_recursive_types(S)]
pub struct Machine<S> {
    pub context: S,
    pub pending: Seq<Option<nat>>,
    pub inverses: Seq<Seq<spec_fn(S) -> S>>,
}

pub open spec fn shaped<S>(machine: Machine<S>) -> bool {
    machine.pending.len() == machine.inverses.len()
}

pub open spec fn enabled<S>(machine: Machine<S>, owner: nat) -> bool {
    owner < machine.pending.len() && machine.pending[owner as int].is_some()
}

pub open spec fn settled<S>(machine: Machine<S>) -> bool {
    forall|owner: int| 0 <= owner < machine.pending.len() ==>
        (#[trigger] machine.pending[owner]).is_none()
}

pub open spec fn independent<S>(family: Family<S>) -> bool {
    forall|a: nat, b: nat, i: nat, j: nat| a != b ==>
        #[trigger] independent_stages(family(a, i), family(b, j))
}

pub open spec fn advance<S>(family: Family<S>, machine: Machine<S>, owner: nat) -> Machine<S> {
    let yielded = family(owner, machine.pending[owner as int].unwrap())(machine.context);
    Machine {
        context: yielded.0,
        pending: machine.pending.update(owner as int, yielded.2),
        inverses: machine.inverses.update(owner as int,
            machine.inverses[owner as int].push(yielded.1)),
    }
}

pub open spec fn tail(schedule: Seq<nat>) -> Seq<nat> {
    schedule.subrange(1, schedule.len() as int)
}

pub open spec fn execute<S>(family: Family<S>, schedule: Seq<nat>, machine: Machine<S>) -> Machine<S>
    decreases schedule.len(),
{
    if schedule.len() == 0 { machine }
    else { execute(family, tail(schedule), advance(family, machine, schedule[0])) }
}

/// Every scheduled stage must have an actual pending continuation when chosen.
pub open spec fn legal<S>(family: Family<S>, schedule: Seq<nat>, machine: Machine<S>) -> bool
    decreases schedule.len(),
{
    shaped(machine) && (schedule.len() == 0 || (enabled(machine, schedule[0])
        && legal(family, tail(schedule), advance(family, machine, schedule[0]))))
}

pub open spec fn complete<S>(family: Family<S>, schedule: Seq<nat>, machine: Machine<S>) -> bool {
    legal(family, schedule, machine) && settled(execute(family, schedule, machine))
}

/// The exact dynamic diamond includes the yielded inverse histories. Merely
/// commuting forward context maps would not establish this equality.
pub proof fn stage_exchange<S>(family: Family<S>, machine: Machine<S>, a: nat, b: nat)
    requires shaped(machine), independent(family), a != b,
        enabled(machine, a), enabled(machine, b),
    ensures enabled(advance(family, machine, a), b),
        enabled(advance(family, machine, b), a),
        shaped(advance(family, machine, a)), shaped(advance(family, machine, b)),
        advance(family, advance(family, machine, a), b)
            == advance(family, advance(family, machine, b), a),
{
    let left = family(a, machine.pending[a as int].unwrap());
    let right = family(b, machine.pending[b as int].unwrap());
    crate::history::iterator_diamond(left, right, machine.context, machine.context);
    let ab = advance(family, advance(family, machine, a), b);
    let ba = advance(family, advance(family, machine, b), a);
    assert(ab.pending =~= ba.pending);
    assert(ab.inverses =~= ba.inverses);
}

/// Pull an enabled stage to the beginning of any complete schedule. The proof
/// constructs the new legal suffix by exchanging actual independent stages,
/// not by assuming that the two schedules have matching per-owner histories.
pub proof fn pull_enabled<S>(family: Family<S>, schedule: Seq<nat>, machine: Machine<S>, owner: nat)
    -> (suffix: Seq<nat>)
    requires independent(family), complete(family, schedule, machine), enabled(machine, owner),
    ensures suffix.len() + 1 == schedule.len(),
        complete(family, suffix, advance(family, machine, owner)),
        execute(family, suffix, advance(family, machine, owner)) == execute(family, schedule, machine),
    decreases schedule.len(),
{
    if schedule.len() == 0 {
        assert(!settled(machine));
        Seq::empty()
    } else if schedule[0] == owner {
        tail(schedule)
    } else {
        let other = schedule[0];
        let after_other = advance(family, machine, other);
        stage_exchange(family, machine, owner, other);
        let rest = pull_enabled(family, tail(schedule), after_other, owner);
        let answer = seq![other] + rest;
        assert(tail(answer) =~= rest);
        answer
    }
}

/// Schedule independence for genuinely dynamic finite iterators, including
/// their witnesses and continuations. No equality of projected lanes is a
/// premise: complete legal schedules are enough under primitive independence.
pub proof fn complete_confluence<S>(family: Family<S>, left: Seq<nat>, right: Seq<nat>, machine: Machine<S>)
    requires independent(family), complete(family, left, machine), complete(family, right, machine),
    ensures execute(family, left, machine) == execute(family, right, machine),
    decreases left.len(),
{
    if left.len() == 0 {
        if right.len() > 0 {
            assert(machine.pending[right[0] as int].is_none());
        }
    } else {
        let suffix = pull_enabled(family, right, machine, left[0]);
        complete_confluence(family, tail(left), suffix, advance(family, machine, left[0]));
    }
}

/// A local iterator bound: every returned continuation has a strictly smaller
/// rank. This constrains stage results at every context, not entire executions.
pub open spec fn decreasing<S>(family: Family<S>, rank: spec_fn(nat, nat) -> nat) -> bool {
    forall|owner: nat, stage: nat, context: S| {
        let result = #[trigger] family(owner, stage)(context);
        result.2.is_some() ==> rank(owner, result.2.unwrap()) < rank(owner, stage)
    }
}

pub open spec fn weight(pending: Seq<Option<nat>>, rank: spec_fn(nat, nat) -> nat, length: nat) -> nat
    recommends length <= pending.len(),
    decreases length,
{
    if length == 0 { 0 }
    else { weight(pending, rank, (length - 1) as nat)
        + if pending[length - 1].is_some() {
            rank((length - 1) as nat, pending[length - 1].unwrap()) + 1
        } else { 0 } }
}

pub open spec fn budget<S>(machine: Machine<S>, rank: spec_fn(nat, nat) -> nat) -> nat {
    weight(machine.pending, rank, machine.pending.len())
}

proof fn weight_replace(pending: Seq<Option<nat>>, rank: spec_fn(nat, nat) -> nat,
    owner: nat, replacement: Option<nat>, length: nat)
    requires owner < length <= pending.len(), pending[owner as int].is_some(),
        replacement.is_some() ==> rank(owner, replacement.unwrap()) < rank(owner, pending[owner as int].unwrap()),
    ensures weight(pending.update(owner as int, replacement), rank, length) < weight(pending, rank, length),
    decreases length,
{
    if owner == length - 1 {
        weight_prefix_frame(pending, pending.update(owner as int, replacement), rank, (length - 1) as nat);
    } else {
        weight_replace(pending, rank, owner, replacement, (length - 1) as nat);
    }
}

proof fn weight_prefix_frame(left: Seq<Option<nat>>, right: Seq<Option<nat>>,
    rank: spec_fn(nat, nat) -> nat, length: nat)
    requires length <= left.len(), length <= right.len(),
        forall|i: int| 0 <= i < length ==> #[trigger] left[i] == right[i],
    ensures weight(left, rank, length) == weight(right, rank, length),
    decreases length,
{
    if length > 0 { weight_prefix_frame(left, right, rank, (length - 1) as nat); }
}

pub proof fn stage_decreases<S>(family: Family<S>, machine: Machine<S>, owner: nat,
    rank: spec_fn(nat, nat) -> nat)
    requires enabled(machine, owner), decreasing(family, rank),
    ensures budget(advance(family, machine, owner), rank) < budget(machine, rank),
{
    let stage = machine.pending[owner as int].unwrap();
    let result = family(owner, stage)(machine.context);
    weight_replace(machine.pending, rank, owner, result.2, machine.pending.len());
}

/// Derive the finite step count from actual legal transitions and the local
/// continuation rank. No precomputed episode or target-change counts appear.
pub proof fn execution_bound<S>(family: Family<S>, schedule: Seq<nat>, machine: Machine<S>,
    rank: spec_fn(nat, nat) -> nat)
    requires legal(family, schedule, machine), decreasing(family, rank),
    ensures schedule.len() <= budget(machine, rank),
    decreases schedule.len(),
{
    if schedule.len() > 0 {
        stage_decreases(family, machine, schedule[0], rank);
        execution_bound(family, tail(schedule), advance(family, machine, schedule[0]), rank);
    }
}

pub open spec fn serial(schedule: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < j < schedule.len() ==> schedule[i] <= schedule[j]
}

pub open spec fn first_pending(pending: Seq<Option<nat>>, length: nat) -> Option<nat>
    recommends length <= pending.len(),
    decreases length,
{
    if length == 0 { None }
    else {
        let prior = first_pending(pending, (length - 1) as nat);
        if prior.is_some() { prior }
        else if pending[length - 1].is_some() { Some((length - 1) as nat) }
        else { None }
    }
}

proof fn first_pending_correct(pending: Seq<Option<nat>>, length: nat)
    requires length <= pending.len(),
    ensures
        first_pending(pending, length).is_some() ==> {
            let owner = first_pending(pending, length).unwrap();
            &&& owner < length && pending[owner as int].is_some()
            &&& forall|i: int| 0 <= i < owner ==> (#[trigger] pending[i]).is_none()
        },
        first_pending(pending, length).is_none() ==>
            forall|i: int| 0 <= i < length ==> (#[trigger] pending[i]).is_none(),
    decreases length,
{
    if length > 0 { first_pending_correct(pending, (length - 1) as nat); }
}

/// Every shaped machine admits a complete finite execution. Well-foundedness
/// follows from the returned continuation, with no fairness/completion premise.
/// The constructed schedule is serial: each owner finishes before the next.
pub proof fn completion_exists<S>(family: Family<S>, machine: Machine<S>, rank: spec_fn(nat, nat) -> nat)
    -> (schedule: Seq<nat>)
    requires shaped(machine), decreasing(family, rank),
    ensures complete(family, schedule, machine), schedule.len() <= budget(machine, rank), serial(schedule),
        forall|i: int| 0 <= i < schedule.len() ==> enabled(machine, #[trigger] schedule[i]),
    decreases budget(machine, rank),
{
    if settled(machine) {
        Seq::empty()
    } else {
        first_pending_correct(machine.pending, machine.pending.len());
        let owner = first_pending(machine.pending, machine.pending.len()).unwrap();
        stage_decreases(family, machine, owner, rank);
        let rest = completion_exists(family, advance(family, machine, owner), rank);
        let answer = seq![owner] + rest;
        assert(tail(answer) =~= rest);
        assert forall|i: int| 0 <= i < rest.len() implies enabled(machine, #[trigger] rest[i]) by { }
        assert forall|i: int| 0 <= i < rest.len() implies owner <= #[trigger] rest[i] by {
            if rest[i] < owner { assert(machine.pending[rest[i] as int].is_none()); }
        }
        assert(serial(answer)) by {
            assert forall|i: int, j: int| 0 <= i < j < answer.len() implies answer[i] <= answer[j] by {
                if i > 0 { assert(rest[i - 1] <= rest[j - 1]); }
            }
        }
        answer
    }
}

/// Existence, finite length, and uniqueness of the normal result are obtained
/// together from stage-level laws. The result includes each actual inverse.
pub proof fn unique_complete_result<S>(family: Family<S>, machine: Machine<S>, rank: spec_fn(nat, nat) -> nat)
    -> (schedule: Seq<nat>)
    requires shaped(machine), decreasing(family, rank), independent(family),
    ensures complete(family, schedule, machine), schedule.len() <= budget(machine, rank), serial(schedule),
        forall|other: Seq<nat>| complete(family, other, machine) ==>
            execute(family, other, machine) == execute(family, schedule, machine),
{
    let schedule = completion_exists(family, machine, rank);
    assert forall|other: Seq<nat>| complete(family, other, machine) implies
        execute(family, other, machine) == execute(family, schedule, machine) by {
        complete_confluence(family, other, schedule, machine);
    }
    schedule
}

/// The witness is checked at the context where its stage actually executes.
/// Returned inverse functions need not undo the stage at unrelated contexts.
pub open spec fn witnessed<S>(family: Family<S>) -> bool {
    forall|owner: nat, stage: nat, context: S| {
        let yielded = #[trigger] family(owner, stage)(context);
        (yielded.1)(yielded.0) == context
    }
}

pub open spec fn yielded_inverses<S>(family: Family<S>, schedule: Seq<nat>, machine: Machine<S>)
    -> Seq<spec_fn(S) -> S>
    decreases schedule.len(),
{
    if schedule.len() == 0 { Seq::empty() }
    else {
        let owner = schedule[0];
        let yielded = family(owner, machine.pending[owner as int].unwrap())(machine.context);
        seq![yielded.1] + yielded_inverses(family, tail(schedule), advance(family, machine, owner))
    }
}

proof fn unwind_concatenation<S>(first: Seq<spec_fn(S) -> S>, second: Seq<spec_fn(S) -> S>, context: S)
    ensures crate::calculus::unwind(first + second, context)
        == crate::calculus::unwind(first, crate::calculus::unwind(second, context)),
    decreases second.len(),
{
    if second.len() == 0 { assert(first + second =~= first); }
    else {
        assert((first + second).drop_last() =~= first + second.drop_last());
        unwind_concatenation(first, second.drop_last(), (second.last())(context));
    }
}

/// A whole finite dynamic execution recovers by its actual returned witnesses.
/// This includes arbitrary interleavings and continuation choices made by the
/// component functions; all witnesses are retained in execution order.
pub proof fn dynamic_execution_recovery<S>(family: Family<S>, schedule: Seq<nat>, machine: Machine<S>)
    requires legal(family, schedule, machine), witnessed(family),
    ensures crate::calculus::unwind(yielded_inverses(family, schedule, machine),
        execute(family, schedule, machine).context) == machine.context,
    decreases schedule.len(),
{
    reveal_with_fuel(crate::calculus::unwind, 2);
    if schedule.len() > 0 {
        let owner = schedule[0];
        let yielded = family(owner, machine.pending[owner as int].unwrap())(machine.context);
        let after = advance(family, machine, owner);
        dynamic_execution_recovery(family, tail(schedule), after);
        unwind_concatenation(seq![yielded.1], yielded_inverses(family, tail(schedule), after),
            execute(family, schedule, machine).context);
        assert(seq![yielded.1].drop_last() =~= Seq::empty());
        assert((yielded.1)(yielded.0) == machine.context);
    }
}

/// Every saved inverse originates in an actual stage of this owner. This is a
/// primitive-generator condition, not a requirement that its later execution
/// globally undo arbitrary contexts.
pub open spec fn generated_inverse<S>(family: Family<S>, owner: nat, inverse: spec_fn(S) -> S) -> bool {
    exists|stage: nat, context: S| (#[trigger] family(owner, stage)(context)).1 == inverse
}

pub open spec fn generated_accumulator<S>(family: Family<S>, owner: nat,
    inverses: Seq<spec_fn(S) -> S>) -> bool {
    forall|i: int| 0 <= i < inverses.len() ==> generated_inverse(family, owner, #[trigger] inverses[i])
}

/// Lift primitive independence to a whole accumulated inverse, retaining the
/// foreign iterator's actual inverse and continuation as well as its context.
pub proof fn stage_under_unwind<S>(family: Family<S>, owner: nat, foreign: nat, stage: nat,
    inverses: Seq<spec_fn(S) -> S>, context: S)
    requires owner != foreign, independent(family), generated_accumulator(family, owner, inverses),
    ensures
        family(foreign, stage)(crate::calculus::unwind(inverses, context)).0
            == crate::calculus::unwind(inverses, family(foreign, stage)(context).0),
        family(foreign, stage)(crate::calculus::unwind(inverses, context)).1
            == family(foreign, stage)(context).1,
        family(foreign, stage)(crate::calculus::unwind(inverses, context)).2
            == family(foreign, stage)(context).2,
    decreases inverses.len(),
{
    if inverses.len() > 0 {
        let inverse = inverses.last();
        let (origin, entry) = choose|origin: nat, entry: S|
            (#[trigger] family(owner, origin)(entry)).1 == inverse;
        let local_step = family(owner, origin);
        let foreign_step = family(foreign, stage);
        assert(independent_stages(local_step, foreign_step));
        assert(crate::history::generators(local_step).contains(inverse));
        assert(crate::history::generators(foreign_step).contains(crate::history::forward_of(foreign_step)));
        assert(crate::history::stable_yield(foreign_step, inverse));
        assert(crate::history::commutes(inverse, crate::history::forward_of(foreign_step)));
        let forward = crate::history::forward_of(foreign_step);
        assert(inverse(forward(context)) == forward(inverse(context)));
        stage_under_unwind(family, owner, foreign, stage, inverses.drop_last(), inverse(context));
    }
}

/// Remove the owner's accumulated contribution and reset only that owner's
/// iterator bookkeeping. All foreign continuations and witnesses are retained.
pub open spec fn erase_owner<S>(machine: Machine<S>, owner: nat, original: Option<nat>) -> Machine<S> {
    Machine {
        context: crate::calculus::unwind(machine.inverses[owner as int], machine.context),
        pending: machine.pending.update(owner as int, original),
        inverses: machine.inverses.update(owner as int, Seq::empty()),
    }
}

/// A genuine witnessed local stage vanishes under owner erasure.
pub proof fn erase_local_stage<S>(family: Family<S>, machine: Machine<S>, owner: nat, original: Option<nat>)
    requires shaped(machine), enabled(machine, owner), witnessed(family),
    ensures erase_owner(advance(family, machine, owner), owner, original) == erase_owner(machine, owner, original),
{
    let yielded = family(owner, machine.pending[owner as int].unwrap())(machine.context);
    assert((yielded.1)(yielded.0) == machine.context);
    let after = erase_owner(advance(family, machine, owner), owner, original);
    let before = erase_owner(machine, owner, original);
    assert(machine.inverses[owner as int].push(yielded.1).drop_last() =~= machine.inverses[owner as int]);
    assert(after.pending =~= before.pending);
    assert(after.inverses =~= before.inverses);
}

/// A surviving foreign stage remains enabled and returns the same dynamic
/// witness/continuation after erasure. Both orders give exactly the same state.
pub proof fn erase_foreign_stage<S>(family: Family<S>, machine: Machine<S>, owner: nat,
    foreign: nat, original: Option<nat>)
    requires shaped(machine), owner < machine.pending.len(), owner != foreign,
        enabled(machine, foreign), independent(family),
        generated_accumulator(family, owner, machine.inverses[owner as int]),
    ensures enabled(erase_owner(machine, owner, original), foreign),
        advance(family, erase_owner(machine, owner, original), foreign)
            == erase_owner(advance(family, machine, foreign), owner, original),
{
    stage_under_unwind(family, owner, foreign, machine.pending[foreign as int].unwrap(),
        machine.inverses[owner as int], machine.context);
    let left = advance(family, erase_owner(machine, owner, original), foreign);
    let right = erase_owner(advance(family, machine, foreign), owner, original);
    assert(left.pending =~= right.pending);
    assert(left.inverses =~= right.inverses);
}

pub open spec fn omit(schedule: Seq<nat>, owner: nat) -> Seq<nat>
    decreases schedule.len(),
{
    if schedule.len() == 0 { Seq::empty() }
    else if schedule[0] == owner { omit(tail(schedule), owner) }
    else { seq![schedule[0]] + omit(tail(schedule), owner) }
}

/// Delete one entire owner's dynamic execution, with its accumulated recovery.
/// The surviving schedule is proved legal from the state with that owner
/// erased, and produces exactly the erased endpoint. In particular the foreign
/// effects retain their real yielded witnesses and continuation choices.
pub proof fn erase_execution<S>(family: Family<S>, schedule: Seq<nat>, machine: Machine<S>,
    owner: nat, original: Option<nat>)
    requires legal(family, schedule, machine), owner < machine.pending.len(),
        independent(family), witnessed(family),
        generated_accumulator(family, owner, machine.inverses[owner as int]),
    ensures legal(family, omit(schedule, owner), erase_owner(machine, owner, original)),
        execute(family, omit(schedule, owner), erase_owner(machine, owner, original))
            == erase_owner(execute(family, schedule, machine), owner, original),
    decreases schedule.len(),
{
    if schedule.len() > 0 {
        let actor = schedule[0];
        let after = advance(family, machine, actor);
        if actor == owner {
            erase_local_stage(family, machine, owner, original);
            let yielded = family(owner, machine.pending[owner as int].unwrap())(machine.context);
            assert(generated_inverse(family, owner, yielded.1));
            assert(generated_accumulator(family, owner, after.inverses[owner as int])) by {
                assert forall|i: int| 0 <= i < after.inverses[owner as int].len() implies
                    generated_inverse(family, owner, #[trigger] after.inverses[owner as int][i]) by { }
            }
        } else {
            erase_foreign_stage(family, machine, owner, actor, original);
            assert(tail(omit(schedule, owner)) =~= omit(tail(schedule), owner));
        }
        erase_execution(family, tail(schedule), after, owner, original);
    }
}

/// Closed-episode deletion at the dynamic iterator layer. The owner starts
/// with an empty accumulator, executes any number of stages, and is then
/// recovered by its actual saved inverses. Deleting its stages leaves a legal
/// foreign execution with the same context, continuations, and inverse stacks.
pub proof fn closed_owner_deletion<S>(family: Family<S>, schedule: Seq<nat>, machine: Machine<S>, owner: nat)
    requires legal(family, schedule, machine), owner < machine.pending.len(),
        independent(family), witnessed(family), machine.inverses[owner as int].len() == 0,
    ensures legal(family, omit(schedule, owner), machine),
        execute(family, omit(schedule, owner), machine)
            == erase_owner(execute(family, schedule, machine), owner, machine.pending[owner as int]),
{
    assert(erase_owner(machine, owner, machine.pending[owner as int]) == machine) by {
        assert(machine.inverses[owner as int] =~= Seq::empty());
        assert(erase_owner(machine, owner, machine.pending[owner as int]).pending =~= machine.pending);
        assert(erase_owner(machine, owner, machine.pending[owner as int]).inverses =~= machine.inverses);
    }
    erase_execution(family, schedule, machine, owner, machine.pending[owner as int]);
}

pub open spec fn activation(rule: control::Rule) -> bool {
    rule == control::Rule::Begin || rule == control::Rule::Iter || rule == control::Rule::Finish
}

/// An ordinary activation never withdraws an already published provider or
/// changes the target interface of a different fiber. This derives target
/// preservation from the actual control rules, rather than assuming a diamond.
pub proof fn activation_preserves_target(a: control::State, z: control::State,
    actor: usize, other: usize, rule: control::Rule, view: ISet<Binding>)
    requires activation(rule), control::step(a, z, actor, rule), actor != other,
        control::target(a, other, view),
    ensures control::target(z, other, view),
{
    assert forall|binding: Binding| view.contains(binding) implies
        z.fibers[other].dependencies.contains(crate::Port { key: binding.key, realm: binding.realm })
        && control::publishes(z, crate::Port { key: binding.key, realm: binding.realm }, binding.provider) by {
        let port = crate::Port { key: binding.key, realm: binding.realm };
        assert(control::publishes(a, port, binding.provider));
        if binding.provider == actor {
            assert(a.fibers[actor].phase != Phase::Active);
        }
    }
}

/// Exact edit that applies two disjoint control-field replacements.
pub open spec fn merged(a: control::State, left: control::State, right: control::State,
    first: usize, second: usize) -> control::State {
    control::State { fibers: a.fibers.insert(first, left.fibers[first]).insert(second, right.fibers[second]) }
}

/// The ordinary lifecycle activation diamond. Both transitions are actual
/// applicable Begin/Iter/Finish rules in the entry state. Their committed views
/// and phase changes remain applicable after the other transition, and the
/// common successor retains both edits. Effect-stage exchange is established
/// separately by `stage_exchange`; registry-changing stages need extra frames.
pub proof fn activation_diamond(a: control::State, left: control::State, right: control::State,
    first: usize, second: usize, left_rule: control::Rule, right_rule: control::Rule)
    requires first != second, activation(left_rule), activation(right_rule),
        control::step(a, left, first, left_rule), control::step(a, right, second, right_rule),
    ensures
        control::step(left, merged(a, left, right, first, second), second, right_rule),
        control::step(right, merged(a, left, right, first, second), first, left_rule),
{
    let both = merged(a, left, right, first, second);
    assert(control::registered(a, first));
    assert(control::registered(a, second));
    assert(control::frame(a, left, first));
    assert(control::frame(a, right, second));
    if right_rule == control::Rule::Begin {
        activation_preserves_target(a, left, first, second, left_rule, right.fibers[second].committed);
    } else {
        activation_preserves_target(a, left, first, second, left_rule, a.fibers[second].committed);
    }
    if left_rule == control::Rule::Begin {
        activation_preserves_target(a, right, second, first, right_rule, left.fibers[first].committed);
    } else {
        activation_preserves_target(a, right, second, first, right_rule, a.fibers[first].committed);
    }
    assert(control::frame(left, both, second)) by {
        assert forall|n: usize| n != second implies
            control::registered(left, n) == control::registered(both, n)
            && (control::registered(left, n) ==> left.fibers[n] == both.fibers[n]) by { }
    }
    assert(control::frame(right, both, first)) by {
        assert forall|n: usize| n != first implies
            control::registered(right, n) == control::registered(both, n)
            && (control::registered(right, n) ==> right.fibers[n] == both.fibers[n]) by { }
    }
    if right_rule == control::Rule::Iter {
        assert forall|n: usize| left.fibers.dom().contains(n) == both.fibers.dom().contains(n) by {
            assert(control::registered(a, n) == control::registered(left, n));
        }
        assert forall|n: usize| left.fibers.dom().contains(n) implies left.fibers[n] == both.fibers[n] by {
            assert(control::registered(left, n));
        }
        assert(left.fibers =~= both.fibers);
    }
    if left_rule == control::Rule::Iter {
        assert forall|n: usize| right.fibers.dom().contains(n) == both.fibers.dom().contains(n) by {
            assert(control::registered(a, n) == control::registered(right, n));
        }
        assert forall|n: usize| right.fibers.dom().contains(n) implies right.fibers[n] == both.fibers[n] by {
            assert(control::registered(right, n));
        }
        assert(right.fibers =~= both.fibers);
    }
}

} // verus!
