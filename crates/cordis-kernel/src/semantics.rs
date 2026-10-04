//! The paper's value-carrying lifecycle relation, including atomic effect maps.
//!
//! Unlike the kernel's total-provision erasure, publication reads each owner's
//! actual table. Iterator results contain the changed context, inverse identity,
//! and continuation; restoration evaluates those inverses in reverse order.
//! An iterator model is an explicit parameter, not a claim that arbitrary host
//! callbacks satisfy confinement, recovery, or independence.
use crate::{refinement as control, Port};
#[cfg(verus_keep_ghost)]
use crate::{Binding, Phase};
use vstd::prelude::*;

verus! {

/// Auxiliary fields are indexed by exactly the registered fiber names.
/// The effect/iterator/inverse numbers are identities interpreted by `Model`.
pub struct State<V> {
    pub control: control::State,
    pub tables: IMap<usize, IMap<Port, V>>,
    pub effects: IMap<usize, nat>,
    pub iterators: IMap<usize, Option<nat>>,
    pub accumulators: IMap<usize, Seq<nat>>,
}

pub struct Yield<V> {
    pub state: State<V>,
    pub inverse: nat,
    pub next: Option<nat>,
}

#[verifier::reject_recursive_types(V)]
pub struct Model<V> {
    pub iterate: spec_fn(usize, nat, State<V>) -> Yield<V>,
    pub undo: spec_fn(nat, State<V>) -> State<V>,
}

pub open spec fn registered<V>(s: State<V>, n: usize) -> bool {
    control::registered(s.control, n)
}

/// Partial provision is permitted: declarations bound, rather than determine,
/// the table's domain. An Inactive fiber retains no lifecycle accumulator.
pub open spec fn shaped<V>(s: State<V>) -> bool {
    &&& s.tables.dom() == s.control.fibers.dom()
    &&& s.effects.dom() == s.control.fibers.dom()
    &&& s.iterators.dom() == s.control.fibers.dom()
    &&& s.accumulators.dom() == s.control.fibers.dom()
    &&& forall|n: usize| registered(s, n) ==> {
        &&& s.tables[n].dom().subset_of(s.control.fibers[n].provisions)
        &&& (s.control.fibers[n].phase == Phase::Inactive ==> s.iterators[n].is_none()
            && s.accumulators[n].len() == 0 && s.control.fibers[n].committed.is_empty())
        &&& (s.control.fibers[n].phase == Phase::Loading ==> s.iterators[n].is_some())
        &&& (s.control.fibers[n].phase == Phase::Active || s.control.fibers[n].phase == Phase::Unloading
            ==> s.iterators[n].is_none())
    }
}

/// Equation (46) reads table presence, not merely a declared provision.
pub open spec fn publishes<V>(s: State<V>, p: Port, n: usize) -> bool {
    registered(s, n) && s.control.fibers[n].phase == Phase::Active && s.tables[n].dom().contains(p)
}

pub open spec fn target<V>(s: State<V>, n: usize, view: ISet<Binding>) -> bool {
    &&& registered(s, n) && !s.control.fibers[n].retired
    &&& forall|b: Binding| view.contains(b) ==> s.control.fibers[n].dependencies.contains(Port {key:b.key, realm:b.realm})
        && publishes(s, Port {key:b.key, realm:b.realm}, b.provider)
    &&& forall|p: Port| s.control.fibers[n].dependencies.contains(p) ==> exists|b: Binding|
        view.contains(b) && b.key == p.key && b.realm == p.realm
}

pub open spec fn coherent<V>(s: State<V>, n: usize) -> bool {
    target(s, n, s.control.fibers[n].committed)
}

pub open spec fn total_active<V>(s: State<V>) -> bool {
    forall|n: usize| registered(s, n) && s.control.fibers[n].phase == Phase::Active
        ==> s.tables[n].dom() == s.control.fibers[n].provisions
}

/// The host's total-publication check is precisely the specialization required
/// to use the executable kernel's target computation for the general calculus.
pub proof fn total_targets_agree<V>(s: State<V>, n: usize, view: ISet<Binding>)
    requires total_active(s),
    ensures target(s, n, view) == control::target(s.control, n, view),
{
    assert forall|p: Port, m: usize| publishes(s, p, m) == control::publishes(s.control, p, m) by { }
}

/// The bracket edit changes theta alone; a yielded context can contain a child
/// insertion, or dependency-table writes, and those changes are retained.
pub open spec fn edit<V>(s: State<V>, n: usize, phase: Phase, committed: ISet<Binding>,
    iterator: Option<nat>, accumulator: Seq<nat>) -> State<V>
{
    State {
        control: control::State { fibers: s.control.fibers.insert(n, control::Fiber {
            parent: s.control.fibers[n].parent,
            retired: s.control.fibers[n].retired,
            phase,
            dependencies: s.control.fibers[n].dependencies,
            provisions: s.control.fibers[n].provisions,
            committed,
        }) },
        tables: s.tables,
        effects: s.effects,
        iterators: s.iterators.insert(n, iterator),
        accumulators: s.accumulators.insert(n, accumulator),
    }
}

/// g composed with h applies h first, including O-Retire child inverses.
pub open spec fn restore<V>(model: Model<V>, inverses: Seq<nat>, s: State<V>) -> State<V>
    decreases inverses.len(),
{
    if inverses.len() == 0 { s }
    else { restore(model, inverses.drop_last(), (model.undo)(inverses.last(), s)) }
}

pub open spec fn auxiliary_frame<V>(a: State<V>, z: State<V>, n: usize) -> bool {
    forall|m: usize| m != n && registered(a, m) ==> z.tables[m] == a.tables[m]
        && z.effects[m] == a.effects[m] && z.iterators[m] == a.iterators[m]
        && z.accumulators[m] == a.accumulators[m]
}

/// The nine rules, with the two alternatives of L-Divert kept explicit.
/// Effect admissibility is the separate `context_iteration` obligation below.
pub open spec fn step<V>(model: Model<V>, a: State<V>, z: State<V>, n: usize, rule: control::Rule) -> bool {
    match rule {
        control::Rule::Insert => {
            &&& control::step(a.control, z.control, n, rule)
            &&& auxiliary_frame(a, z, n)
            &&& z.tables[n].is_empty() && z.iterators[n].is_none() && z.accumulators[n].len() == 0
            &&& shaped(z)
        },
        control::Rule::Retire => control::step(a.control, z.control, n, rule)
            && a.tables == z.tables && a.effects == z.effects && a.iterators == z.iterators && a.accumulators == z.accumulators,
        control::Rule::Remove => control::step(a.control, z.control, n, rule) && a.tables[n].is_empty()
            && z.tables == a.tables.remove(n) && z.effects == a.effects.remove(n)
            && z.iterators == a.iterators.remove(n) && z.accumulators == a.accumulators.remove(n),
        control::Rule::Begin => registered(a, n) && a.control.fibers[n].phase == Phase::Inactive
            && target(a, n, z.control.fibers[n].committed)
            && z == edit(a, n, Phase::Loading, z.control.fibers[n].committed, Some(a.effects[n]), Seq::empty()),
        control::Rule::Iter => {
            let y = (model.iterate)(n, a.iterators[n].unwrap(), a);
            &&& registered(a, n) && a.control.fibers[n].phase == Phase::Loading && a.iterators[n].is_some()
            &&& coherent(a, n) && y.next.is_some()
            &&& z == edit(y.state, n, Phase::Loading, a.control.fibers[n].committed,
                y.next, a.accumulators[n].push(y.inverse))
        },
        control::Rule::Finish => {
            let y = (model.iterate)(n, a.iterators[n].unwrap(), a);
            &&& registered(a, n) && a.control.fibers[n].phase == Phase::Loading && a.iterators[n].is_some()
            &&& coherent(a, n) && y.next.is_none()
            &&& z == edit(y.state, n, Phase::Active, a.control.fibers[n].committed,
                None, a.accumulators[n].push(y.inverse))
        },
        control::Rule::Divert => {
            let y = (model.iterate)(n, a.iterators[n].unwrap(), a);
            &&& registered(a, n) && a.control.fibers[n].phase == Phase::Loading && a.iterators[n].is_some()
            &&& !coherent(a, n)
            &&& (z == edit(a, n, Phase::Unloading, a.control.fibers[n].committed, None, a.accumulators[n])
                || z == edit(y.state, n, Phase::Unloading, a.control.fibers[n].committed,
                    None, a.accumulators[n].push(y.inverse)))
        },
        control::Rule::Leave => registered(a, n) && a.control.fibers[n].phase == Phase::Active
            && !coherent(a, n)
            && z == edit(a, n, Phase::Unloading, a.control.fibers[n].committed, None, a.accumulators[n]),
        control::Rule::Unload => registered(a, n) && a.control.fibers[n].phase == Phase::Unloading
            && !control::relied(a.control, n)
            && z == edit(restore(model, a.accumulators[n], a), n, Phase::Inactive, ISet::empty(), None, Seq::empty()),
        _ => false,
    }
}

/// Definition 55's writes for ordinary table effects: no control/iterator write,
/// only the acting table or values of declared dependency keys in other tables.
pub open spec fn confined_write<V>(a: State<V>, z: State<V>, n: usize) -> bool {
    &&& a.control == z.control && a.effects == z.effects
    &&& a.iterators == z.iterators && a.accumulators == z.accumulators
    &&& a.tables.dom() == z.tables.dom()
    &&& forall|m: usize| registered(a, m) && m != n ==> {
        &&& a.tables[m].dom() == z.tables[m].dom()
        &&& forall|p: Port| a.tables[m].dom().contains(p) && !a.control.fibers[n].dependencies.contains(p)
            ==> a.tables[m][p] == z.tables[m][p]
    }
}

/// The primitive of Definition 52. This is the effect's state map, before
/// L-Iter/L-Finish/L-Divert applies its bracket edit to the parent.
pub open spec fn child_insert<V>(a: State<V>, z: State<V>, parent: usize, child: usize) -> bool {
    &&& control::step(a.control, z.control, child, control::Rule::Insert)
    &&& z.control.fibers[child].parent == Some(parent)
    &&& auxiliary_frame(a, z, child)
    &&& z.tables[child].is_empty() && z.iterators[child].is_none() && z.accumulators[child].len() == 0
    &&& shaped(z)
}

/// Child recovery writes retirement alone, even when the child remains Active.
pub open spec fn child_retire<V>(a: State<V>, z: State<V>, child: usize) -> bool {
    control::step(a.control, z.control, child, control::Rule::Retire)
        && a.tables == z.tables && a.effects == z.effects
        && a.iterators == z.iterators && a.accumulators == z.accumulators
}

pub open spec fn context_iteration<V>(a: State<V>, y: Yield<V>, n: usize) -> bool {
    confined_write(a, y.state, n)
        || exists|child: usize| child_insert(a, y.state, n, child)
}

/// A primitive child creation is an atomic lifecycle iteration, not an external
/// orchestration event followed by an unrelated effect token. The premise names
/// the actual iterator result including the yielded inverse and continuation.
pub proof fn child_lands<V>(model: Model<V>, a: State<V>, child: usize, n: usize)
    requires registered(a, n), a.control.fibers[n].phase == Phase::Loading,
        a.iterators[n].is_some(),
        child_insert(a, (model.iterate)(n, a.iterators[n].unwrap(), a).state, n, child),
    ensures {
        let y = (model.iterate)(n, a.iterators[n].unwrap(), a);
        let phase = if !coherent(a, n) { Phase::Unloading } else if y.next.is_some() { Phase::Loading } else { Phase::Active };
        let next = if phase == Phase::Loading { y.next } else { None };
        let z = edit(y.state, n, phase, a.control.fibers[n].committed, next, a.accumulators[n].push(y.inverse));
        &&& context_iteration(a, y, n)
        &&& step(model, a, z, n, if !coherent(a, n) {control::Rule::Divert} else if y.next.is_some() {control::Rule::Iter} else {control::Rule::Finish})
        &&& registered(z, child) && z.control.fibers[child].parent == Some(n)
        &&& z.accumulators[n] == a.accumulators[n].push(y.inverse)
    },
{
    let y = (model.iterate)(n, a.iterators[n].unwrap(), a);
    assert(child != n);
}

/// The generic recovery proof is connected to the accumulator actually stored
/// by a lifecycle, instead of postulating the final recovered state.
pub proof fn accumulated_restore<V>(model: Model<V>, tokens: Seq<nat>, s: State<V>)
    ensures restore(model, tokens, s)
        == crate::calculus::unwind(Seq::new(tokens.len(), |i: int| |x: State<V>| (model.undo)(tokens[i], x)), s),
    decreases tokens.len(),
{
    let fs = Seq::new(tokens.len(), |i: int| |x: State<V>| (model.undo)(tokens[i], x));
    if tokens.len() > 0 {
        let previous = Seq::new(tokens.drop_last().len(), |i: int| |x: State<V>| (model.undo)(tokens.drop_last()[i], x));
        assert(previous =~= fs.drop_last());
        accumulated_restore(model, tokens.drop_last(), (model.undo)(tokens.last(), s));
    }
}

/// Erase an entry and every auxiliary field owned by that name.
pub open spec fn erase<V>(s: State<V>, n: usize) -> State<V> {
    State {control:control::State {fibers:s.control.fibers.remove(n)},
        tables:s.tables.remove(n), effects:s.effects.remove(n),
        iterators:s.iterators.remove(n), accumulators:s.accumulators.remove(n)}
}

pub open spec fn vestigial<V>(s: State<V>, n: usize) -> bool {
    &&& registered(s, n) && s.control.fibers[n].retired
    &&& s.control.fibers[n].phase == Phase::Inactive && s.tables[n].is_empty()
    &&& forall|m: usize| registered(s, m) ==> s.control.fibers[m].parent != Some(n)
}

/// The target/guard observations really do ignore a vestigial entry. This is
/// weaker than the paper's unrestricted Lemma 62, whose O-Remove converse needs
/// an extra parent-child exception (see `vestigial_parent_counterexample`).
pub proof fn vestigial_observations<V>(s: State<V>, n: usize, m: usize, view: ISet<Binding>)
    requires vestigial(s, n), m != n,
    ensures target(s, m, view) == target(erase(s, n), m, view),
        control::relied(s.control, m) == control::relied(erase(s, n).control, m),
{
    assert forall|p: Port, provider: usize| publishes(s, p, provider)
        == publishes(erase(s, n), p, provider) by { }
    if control::relied(s.control, m) {
        let (x,b) = choose|x:usize,b:Binding| control::registered(s.control,x)
            && x != m && s.control.fibers[x].phase != Phase::Inactive
            && s.control.fibers[x].committed.contains(b) && b.provider == m;
        assert(x != n);
        assert(control::registered(erase(s,n).control,x));
        assert(erase(s,n).control.fibers[x] == s.control.fibers[x]);
        assert(erase(s,n).control.fibers[x].committed.contains(b));
        assert(control::relied(erase(s,n).control,m));
    }
    if control::relied(erase(s,n).control,m) {
        let (x,b) = choose|x:usize,b:Binding| control::registered(erase(s,n).control,x)
            && x != m && erase(s,n).control.fibers[x].phase != Phase::Inactive
            && erase(s,n).control.fibers[x].committed.contains(b) && b.provider == m;
        assert(x != n);
        assert(control::relied(s.control,m));
    }
}

pub open spec fn empty_fiber(parent: Option<usize>, retired: bool) -> control::Fiber {
    control::Fiber {parent, retired, phase:Phase::Inactive, dependencies:ISet::empty(), provisions:ISet::empty(), committed:ISet::empty()}
}

/// Concrete counterexample to Lemma 62(2) as printed on page 42. Both fibers
/// are retired and empty. Erasing the vestigial child enables O-Remove(parent),
/// although that rule is neither excluded O-Insert case. No effect assumption
/// can repair this purely structural counterexample.
pub open spec fn counterexample_state() -> State<u64> {
    let fibers = IMap::empty().insert(0usize, empty_fiber(None, true)).insert(1usize, empty_fiber(Some(0), true));
    State::<u64> {control:control::State {fibers},
        tables:IMap::empty().insert(0usize, IMap::empty()).insert(1usize,IMap::empty()),
        effects:IMap::empty().insert(0usize,0nat).insert(1usize,0nat),
        iterators:IMap::empty().insert(0usize,None).insert(1usize,None),
        accumulators:IMap::empty().insert(0usize,Seq::empty()).insert(1usize,Seq::empty())}
}

pub proof fn vestigial_parent_counterexample()
    ensures {
        let s = counterexample_state();
        &&& vestigial(s, 1)
        &&& control::step(erase(s, 1).control, erase(erase(s, 1), 0).control, 0, control::Rule::Remove)
        &&& !control::step(s.control, erase(s, 0).control, 0, control::Rule::Remove)
    },
{
    let s = counterexample_state();
    let a = erase(s,1).control;
    let z = erase(erase(s,1),0).control;
    assert forall|m:usize| registered(s,m) implies m == 0 || m == 1 by { }
    assert forall|m:usize| registered(s,m) implies s.control.fibers[m].parent != Some(1usize) by { }
    assert(vestigial(s,1));
    assert forall|m:usize| m != 0 implies control::registered(a,m) == control::registered(z,m)
        && (control::registered(a,m) ==> a.fibers[m] == z.fibers[m]) by { }
    assert forall|m:usize| control::registered(a,m) implies a.fibers[m].parent != Some(0usize) by { }
    assert(control::registered(s.control,1));
    assert(s.control.fibers[1usize].parent == Some(0usize));
}


/// Four legal orchestration inputs reach the counterexample from the required
/// empty registry of Definition 58. This is not an unreachable malformed state.
pub proof fn counterexample_reachable()
    ensures control::reaches(control::State {fibers:IMap::empty()}, counterexample_state().control, 4, false),
{
    let a = control::State {fibers:IMap::empty()};
    let b = control::State {fibers:a.fibers.insert(0usize,empty_fiber(None,false))};
    let c = control::State {fibers:b.fibers.insert(1usize,empty_fiber(Some(0),false))};
    let d = control::State {fibers:c.fibers.insert(1usize,empty_fiber(Some(0),true))};
    let e = counterexample_state().control;
    assert(control::step(a,b,0,control::Rule::Insert));
    assert(control::step(b,c,1,control::Rule::Insert));
    assert(control::step(c,d,1,control::Rule::Retire));
    assert(control::step(d,e,0,control::Rule::Retire));
    let states = seq![a,b,c,d,e];
    let labels = seq![(0usize,control::Rule::Insert),(1usize,control::Rule::Insert),
        (1usize,control::Rule::Retire),(0usize,control::Rule::Retire)];
    assert forall|i:int| 0 <= i < labels.len() implies
        control::labelled_step(states[i],states[i+1],labels[i],false) by {
        if i == 0 { } else if i == 1 { } else if i == 2 { } else { assert(i == 3); }
    }
    control::finite_execution_refines(states,labels,false);
}

pub open spec fn no_children(s: control::State, parent: usize) -> bool {
    forall|n: usize| control::registered(s,n) ==> s.fibers[n].parent != Some(parent)
}

/// Corrected structural condition needed by Lemma 62(2): erasing the last
/// vestigial child may enable removal of its own parent. If it is not a child
/// of the acting fiber, the O-Remove guard is preserved in both directions.
pub proof fn vestigial_removal_guard<V>(s: State<V>, erased: usize, parent: usize)
    requires registered(s,erased), erased != parent,
    ensures no_children(s.control,parent)
        == (no_children(erase(s,erased).control,parent) && s.control.fibers[erased].parent != Some(parent)),
{
    if no_children(s.control,parent) {
        assert forall|n:usize| control::registered(erase(s,erased).control,n) implies
            erase(s,erased).control.fibers[n].parent != Some(parent) by {
            assert(control::registered(s.control,n));
            assert(s.control.fibers[n].parent != Some(parent));
        }
        assert(no_children(erase(s,erased).control,parent));
        assert(s.control.fibers[erased].parent != Some(parent));
    } else if no_children(erase(s,erased).control,parent)
        && s.control.fibers[erased].parent != Some(parent) {
        assert forall|n:usize| control::registered(s.control,n) implies s.control.fibers[n].parent != Some(parent) by {
            if n != erased {
                assert(control::registered(erase(s,erased).control,n));
                assert(erase(s,erased).control.fibers[n].parent != Some(parent));
            }
        }
    }
}

/// Reads for confinement compare only the actor's own table and the declared
/// portion of other tables. Registry control, phase, and unrelated values are
/// deliberately not observations available to an ordinary context stage.
pub open spec fn same_input<V>(a: State<V>, z: State<V>, n: usize, deps: ISet<Port>) -> bool {
    &&& a.tables[n] == z.tables[n]
    &&& forall|m: usize, p: Port| m != n && deps.contains(p) ==> {
        &&& (a.tables.dom().contains(m) && a.tables[m].dom().contains(p))
            == (z.tables.dom().contains(m) && z.tables[m].dom().contains(p))
        &&& (a.tables.dom().contains(m) && a.tables[m].dom().contains(p) ==> a.tables[m][p] == z.tables[m][p])
    }
}

/// A genuine observational requirement on a supplied state map, independent of
/// the step relation and its desired theorem. The inverse/continuation part of
/// Definition 42 is intentionally not reduced to commutation of forward maps.
pub open spec fn respects_input<V>(f: spec_fn(State<V>)->State<V>, n:usize, deps:ISet<Port>) -> bool {
    forall|a:State<V>,z:State<V>| same_input(a,z,n,deps)
        ==> #[trigger] same_input(f(a),f(z),n,deps)
}

pub open spec fn lookup<V>(s:State<V>,n:usize,p:Port) -> Option<V> {
    if s.tables.dom().contains(n) && s.tables[n].dom().contains(p) { Some(s.tables[n][p]) } else { None }
}

pub open spec fn same_tables<V>(a: State<V>, z: State<V>) -> bool {
    forall|n:usize,p:Port| #[trigger] lookup(a,n,p) == lookup(z,n,p)
}

/// Creating a child and its immediate retire inverse restore every table even
/// though the child's vestigial control entry remains. This is the actual
/// observation used by Definition 52, not equality of the full registry.
pub proof fn child_inverse_observation<V>(a:State<V>, created:State<V>, retired:State<V>, parent:usize, child:usize)
    requires shaped(a), child_insert(a,created,parent,child), child_retire(created,retired,child),
    ensures same_tables(a,retired),
{
    assert forall|n:usize,p:Port| #[trigger] lookup(a,n,p) == lookup(retired,n,p) by {
        if n == child { assert(retired.tables[child].is_empty()); }
        else if registered(a,n) { assert(a.tables[n] == created.tables[n]); }
    }
}


/// Extend the ghost payload fields after the concrete kernel allocated `child`.
/// Its fixed effect identity is supplied once, just as O-Insert fixes e_n.
pub open spec fn extend_child<V>(a: State<V>, registry:control::State, child:usize, effect:nat) -> State<V> {
    State {control:registry, tables:a.tables.insert(child,IMap::empty()),
        effects:a.effects.insert(child,effect), iterators:a.iterators.insert(child,None),
        accumulators:a.accumulators.insert(child,Seq::empty())}
}

/// The `Kernel::insert`/`ChildEpisode::land_child` postconditions provide the
/// control premise; no desired full-state refinement result is an assumption.
pub proof fn lift_kernel_child_effect<V>(a:State<V>, registry:control::State,
    parent:usize, child:usize, effect:nat)
    requires shaped(a), control::step(a.control,registry,child,control::Rule::Insert),
        registry.fibers[child].parent == Some(parent),
    ensures child_insert(a,extend_child(a,registry,child,effect),parent,child),
{
    let z = extend_child(a,registry,child,effect);
    assert(registry.fibers.dom() =~= a.control.fibers.dom().insert(child)) by {
        assert forall|n:usize| registry.fibers.dom().contains(n)
            == a.control.fibers.dom().insert(child).contains(n) by {
                if n != child { assert(control::registered(a.control,n) == control::registered(registry,n)); }
            }
    }
    assert forall|n:usize| registered(z,n) implies {
        &&& z.tables[n].dom().subset_of(z.control.fibers[n].provisions)
        &&& (z.control.fibers[n].phase == Phase::Inactive ==> z.iterators[n].is_none()
            && z.accumulators[n].len() == 0 && z.control.fibers[n].committed.is_empty())
        &&& (z.control.fibers[n].phase == Phase::Loading ==> z.iterators[n].is_some())
        &&& (z.control.fibers[n].phase == Phase::Active || z.control.fibers[n].phase == Phase::Unloading
            ==> z.iterators[n].is_none())
    } by {
        if n != child {
            assert(registered(a,n));
            assert(a.control.fibers[n] == registry.fibers[n]);
        }
    }
}

pub open spec fn with_control<V>(a:State<V>, registry:control::State) -> State<V> {
    State {control:registry,tables:a.tables,effects:a.effects,iterators:a.iterators,accumulators:a.accumulators}
}

pub proof fn lift_kernel_child_inverse<V>(a:State<V>, registry:control::State, child:usize)
    requires control::step(a.control,registry,child,control::Rule::Retire),
    ensures child_retire(a,with_control(a,registry),child),
{ }

/// A normal table-effect accumulator keeps control fixed. Child inverses use
/// `child_retire` instead and therefore are intentionally outside this lemma.
pub proof fn restore_control_frame<V>(model:Model<V>, tokens:Seq<nat>, s:State<V>)
    requires forall|token:nat,x:State<V>| #[trigger] (model.undo)(token,x).control == x.control,
    ensures restore(model,tokens,s).control == s.control,
    decreases tokens.len(),
{
    if tokens.len() > 0 {
        restore_control_frame(model,tokens.drop_last(),(model.undo)(tokens.last(),s));
    }
}

pub proof fn edit_control_phase<V>(a:State<V>, n:usize, phase:Phase, iterator:Option<nat>, accumulator:Seq<nat>)
    requires registered(a,n),
    ensures control::phase_change(a.control,edit(a,n,phase,a.control.fibers[n].committed,iterator,accumulator).control,n,phase),
{
    let z = edit(a,n,phase,a.control.fibers[n].committed,iterator,accumulator);
    assert forall|m:usize| m != n implies control::registered(a.control,m) == control::registered(z.control,m)
        && (control::registered(a.control,m) ==> a.control.fibers[m] == z.control.fibers[m]) by { }
}

/// Ordinary table effects refine the kernel's erased control rule under total
/// active publication. Context changes and accumulator/iterator bookkeeping
/// remain present in the source semantics; only the projection erases them.
pub proof fn ordinary_step_erases<V>(model:Model<V>, a:State<V>, z:State<V>, n:usize, rule:control::Rule)
    requires shaped(a), total_active(a), step(model,a,z,n,rule),
        forall|actor:usize,i:nat,x:State<V>| #[trigger] (model.iterate)(actor,i,x).state.control == x.control,
        forall|token:nat,x:State<V>| #[trigger] (model.undo)(token,x).control == x.control,
    ensures control::step(a.control,z.control,n,rule),
{
    total_targets_agree(a,n,a.control.fibers[n].committed);
    if rule == control::Rule::Begin {
        total_targets_agree(a,n,z.control.fibers[n].committed);
        assert(control::frame(a.control,z.control,n)) by {
            assert forall|m:usize| m != n implies control::registered(a.control,m) == control::registered(z.control,m)
                && (control::registered(a.control,m) ==> a.control.fibers[m] == z.control.fibers[m]) by { }
        }
    } else if rule == control::Rule::Iter {
        let y = (model.iterate)(n,a.iterators[n].unwrap(),a);
        assert(a.control.fibers =~= z.control.fibers) by {
            assert forall|m:usize| a.control.fibers.dom().contains(m) implies
                a.control.fibers[m] == z.control.fibers[m] by { }
        }
    } else if rule == control::Rule::Finish || rule == control::Rule::Divert || rule == control::Rule::Leave {
        assert(control::frame(a.control,z.control,n)) by {
            assert forall|m:usize| m != n implies control::registered(a.control,m) == control::registered(z.control,m)
                && (control::registered(a.control,m) ==> a.control.fibers[m] == z.control.fibers[m]) by { }
        }
    } else if rule == control::Rule::Unload {
        restore_control_frame(model,a.accumulators[n],a);
        assert(control::frame(a.control,z.control,n)) by {
            assert forall|m:usize| m != n implies control::registered(a.control,m) == control::registered(z.control,m)
                && (control::registered(a.control,m) ==> a.control.fibers[m] == z.control.fibers[m]) by { }
        }
    }
}


/// Lemma 62(1) also needs to exclude inserting a fresh fiber under the erased
/// vestigial parent. O-Insert's parent premise does not exclude retirement.
pub proof fn vestigial_insert_counterexample()
    ensures {
        let a = counterexample_state();
        let z = control::State {fibers:a.control.fibers.insert(2usize,empty_fiber(Some(1),false))};
        &&& vestigial(a,1)
        &&& control::step(a.control,z,2,control::Rule::Insert)
        &&& !control::step(erase(a,1).control,control::State {fibers:z.fibers.remove(1usize)},2,control::Rule::Insert)
    },
{
    vestigial_parent_counterexample();
    let a = counterexample_state();
    let z = control::State {fibers:a.control.fibers.insert(2usize,empty_fiber(Some(1),false))};
    assert(control::frame(a.control,z,2)) by {
        assert forall|n:usize| n != 2 implies control::registered(a.control,n) == control::registered(z,n)
            && (control::registered(a.control,n) ==> a.control.fibers[n] == z.fibers[n]) by { }
    }
}

/// Corrected forward insertion statement: the newly inserted fiber must not
/// use the erased entry as its parent. Provision exclusion is automatically
/// preserved because deletion only removes a possible conflict.
pub proof fn vestigial_insert_forward(a:control::State,z:control::State,erased:usize,actor:usize)
    requires control::registered(a,erased), erased != actor,
        control::step(a,z,actor,control::Rule::Insert), z.fibers[actor].parent != Some(erased),
    ensures control::step(control::State {fibers:a.fibers.remove(erased)},
        control::State {fibers:z.fibers.remove(erased)},actor,control::Rule::Insert),
{
    let x = control::State {fibers:a.fibers.remove(erased)};
    let y = control::State {fibers:z.fibers.remove(erased)};
    assert forall|n:usize| n != actor implies control::registered(x,n) == control::registered(y,n)
        && (control::registered(x,n) ==> x.fibers[n] == y.fibers[n]) by {
        if n != erased { assert(control::registered(a,n) == control::registered(z,n)); }
    }
    if let Some(parent) = z.fibers[actor].parent {
        assert(parent != erased);
        assert(control::registered(a,parent));
    }
    assert forall|n:usize,p:Port| control::registered(x,n) && x.fibers[n].provisions.contains(p)
        implies !y.fibers[actor].provisions.contains(p) by {
        assert(control::registered(a,n));
        assert(a.fibers[n].provisions.contains(p));
    }
}

pub open spec fn quiet<V>(s:State<V>) -> bool {
    forall|n:usize| registered(s,n) ==> match s.control.fibers[n].phase {
        Phase::Inactive => !(exists|view:ISet<Binding>| target(s,n,view)),
        Phase::Active => coherent(s,n),
        _ => false,
    }
}

pub proof fn quiet_total_agrees<V>(s:State<V>)
    requires total_active(s),
    ensures quiet(s) == control::quiet(s.control),
{
    assert forall|n:usize| registered(s,n) implies {
        match s.control.fibers[n].phase {
            Phase::Inactive => (exists|view:ISet<Binding>| target(s,n,view))
                == (exists|view:ISet<Binding>| control::target(s.control,n,view)),
            Phase::Active => coherent(s,n) == control::coherent(s.control,n),
            _ => true,
        }
    } by {
        total_targets_agree(s,n,s.control.fibers[n].committed);
        if exists|view:ISet<Binding>| target(s,n,view) {
            let view = choose|view:ISet<Binding>| target(s,n,view);
            total_targets_agree(s,n,view);
        }
        if exists|view:ISet<Binding>| control::target(s.control,n,view) {
            let view = choose|view:ISet<Binding>| control::target(s.control,n,view);
            total_targets_agree(s,n,view);
        }
    }
    if quiet(s) {
        assert forall|n:usize| control::registered(s.control,n) implies match s.control.fibers[n].phase {
            Phase::Inactive => !(exists|view:ISet<Binding>| control::target(s.control,n,view)),
            Phase::Active => control::coherent(s.control,n),
            _ => false,
        } by { assert(registered(s,n)); }
    } else if control::quiet(s.control) {
        assert forall|n:usize| registered(s,n) implies match s.control.fibers[n].phase {
            Phase::Inactive => !(exists|view:ISet<Binding>| target(s,n,view)),
            Phase::Active => coherent(s,n),
            _ => false,
        } by { assert(control::registered(s.control,n)); }
    }
}

/// The host-safe subset of lifecycle rules: a diversion always executes the
/// iterator it holds and retains that returned inverse. It cannot rely on the
/// aborting alternative of L-Divert, which an in-flight asynchronous stage lacks.
pub open spec fn landing_step<V>(model:Model<V>,a:State<V>,z:State<V>,n:usize,rule:control::Rule) -> bool {
    &&& step(model,a,z,n,rule)
    &&& (rule == control::Rule::Divert ==> {
        let y = (model.iterate)(n,a.iterators[n].unwrap(),a);
        z == edit(y.state,n,Phase::Unloading,a.control.fibers[n].committed,None,a.accumulators[n].push(y.inverse))
    })
}

/// Lift no-deadlock to the value/iterator relation. An enabled loading fiber
/// executes its actual total iterator model, taking Iter or Finish according to
/// the returned continuation. This result is rule applicability, not witness
/// validity, callback termination, or preservation for an arbitrary Model.
pub proof fn full_no_deadlock<V>(model:Model<V>,s:State<V>,ranks:Seq<nat>)
    requires shaped(s), total_active(s), control::well_formed(s.control),
        crate::global::precedence_ranking(s.control,ranks), !quiet(s),
    ensures exists|n:usize,z:State<V>,rule:control::Rule|
        crate::global::lifecycle_rule(rule) && landing_step(model,s,z,n,rule),
{
    quiet_total_agrees(s);
    crate::global::control_no_deadlock(s.control,ranks);
    let (n,erased,rule) = choose|n:usize,z:control::State,rule:control::Rule|
        crate::global::lifecycle_rule(rule) && control::step(s.control,z,n,rule);
    assert(registered(s,n));
    total_targets_agree(s,n,s.control.fibers[n].committed);
    if s.control.fibers[n].phase == Phase::Inactive {
        assert(rule == control::Rule::Begin);
        let view = erased.fibers[n].committed;
        total_targets_agree(s,n,view);
        let z = edit(s,n,Phase::Loading,view,Some(s.effects[n]),Seq::empty());
        assert(landing_step(model,s,z,n,control::Rule::Begin));
    } else if s.control.fibers[n].phase == Phase::Loading {
        assert(s.iterators[n].is_some());
        if !coherent(s,n) {
            let y = (model.iterate)(n,s.iterators[n].unwrap(),s);
            let z = edit(y.state,n,Phase::Unloading,s.control.fibers[n].committed,None,s.accumulators[n].push(y.inverse));
            assert(landing_step(model,s,z,n,control::Rule::Divert));
        } else {
            let y = (model.iterate)(n,s.iterators[n].unwrap(),s);
            if y.next.is_some() {
                let z = edit(y.state,n,Phase::Loading,s.control.fibers[n].committed,y.next,s.accumulators[n].push(y.inverse));
                assert(landing_step(model,s,z,n,control::Rule::Iter));
            } else {
                let z = edit(y.state,n,Phase::Active,s.control.fibers[n].committed,None,s.accumulators[n].push(y.inverse));
                assert(landing_step(model,s,z,n,control::Rule::Finish));
            }
        }
    } else if s.control.fibers[n].phase == Phase::Active {
        assert(rule == control::Rule::Leave);
        let z = edit(s,n,Phase::Unloading,s.control.fibers[n].committed,None,s.accumulators[n]);
        assert(landing_step(model,s,z,n,control::Rule::Leave));
    } else {
        assert(rule == control::Rule::Unload);
        let z = edit(restore(model,s.accumulators[n],s),n,Phase::Inactive,ISet::empty(),None,Seq::empty());
        assert(landing_step(model,s,z,n,control::Rule::Unload));
    }
}


/// Couple the atomic creation rule to the inverse actually returned by the
/// same iterator application. The two premises are primitive effect contracts
/// (kernel Insert and kernel Retire), from which recovery is derived.
pub proof fn witnessed_child_lands<V>(model:Model<V>,a:State<V>,child:usize,n:usize)
    requires shaped(a), registered(a,n), a.control.fibers[n].phase == Phase::Loading,
        a.iterators[n].is_some(),
        child_insert(a,(model.iterate)(n,a.iterators[n].unwrap(),a).state,n,child),
        child_retire((model.iterate)(n,a.iterators[n].unwrap(),a).state,
            (model.undo)((model.iterate)(n,a.iterators[n].unwrap(),a).inverse,
                (model.iterate)(n,a.iterators[n].unwrap(),a).state),child),
    ensures {
        let y = (model.iterate)(n,a.iterators[n].unwrap(),a);
        let phase = if !coherent(a,n) {Phase::Unloading} else if y.next.is_some() {Phase::Loading} else {Phase::Active};
        let next = if phase == Phase::Loading {y.next} else {None};
        let z = edit(y.state,n,phase,a.control.fibers[n].committed,next,a.accumulators[n].push(y.inverse));
        &&& step(model,a,z,n,if !coherent(a,n) {control::Rule::Divert} else if y.next.is_some() {control::Rule::Iter} else {control::Rule::Finish})
        &&& same_tables(a,(model.undo)(y.inverse,y.state))
        &&& (model.undo)(y.inverse,y.state).control.fibers[child].retired
    },
{
    let y = (model.iterate)(n,a.iterators[n].unwrap(),a);
    child_lands(model,a,child,n);
    child_inverse_observation(a,y.state,(model.undo)(y.inverse,y.state),n,child);
}


/// A concrete total interpretation used only by the orchestration-only
/// reachability witness. Its iterator and inverse maps are both identities.
pub open spec fn idle_model<V>() -> Model<V> {
    Model {iterate:|_n:usize,_i:nat,s:State<V>| Yield {state:s,inverse:0,next:None},
        undo:|_token:nat,s:State<V>| s}
}

pub open spec fn empty_state<V>() -> State<V> {
    State {control:control::State {fibers:IMap::empty()}, tables:IMap::empty(),
        effects:IMap::empty(), iterators:IMap::empty(), accumulators:IMap::empty()}
}

pub open spec fn reaches<V>(model:Model<V>,a:State<V>,z:State<V>,count:nat) -> bool
    decreases count,
{
    if count == 0 {a == z}
    else {exists|middle:State<V>,n:usize,rule:control::Rule|
        step(model,middle,z,n,rule) && reaches(model,a,middle,(count-1) as nat)}
}

pub open spec fn execution<V>(model:Model<V>,states:Seq<State<V>>,labels:Seq<(usize,control::Rule)>) -> bool {
    states.len() == labels.len()+1 && forall|i:int| 0 <= i < labels.len()
        ==> step(model,states[i],states[i+1],labels[i].0,labels[i].1)
}

pub proof fn execution_reaches<V>(model:Model<V>,states:Seq<State<V>>,labels:Seq<(usize,control::Rule)>)
    requires execution(model,states,labels),
    ensures reaches(model,states.first(),states.last(),labels.len()),
    decreases labels.len(),
{
    if labels.len() == 0 {assert(states.first() == states.last());}
    else {
        let previous = states.drop_last();
        let prefix = labels.drop_last();
        assert(execution(model,previous,prefix)) by {
            assert forall|i:int| 0 <= i < prefix.len()
                implies step(model,previous[i],previous[i+1],prefix[i].0,prefix[i].1) by { }
        }
        execution_reaches(model,previous,prefix);
        let middle = previous.last();
        let label = labels.last();
        assert(step(model,middle,states.last(),label.0,label.1));
        assert(reaches(model,states.first(),middle,(labels.len()-1) as nat));
    }
}

/// The two vestigial counterexamples are reachable in the complete nine-rule
/// relation, including actual auxiliary fields and empty service tables. All
/// four steps are orchestration inputs, so the explicit total idle iterator
/// interpretation is never invoked. No erased trace is assumed liftable.
pub proof fn counterexample_reachable_full()
    ensures reaches(idle_model::<u64>(),empty_state::<u64>(),counterexample_state(),4),
{
    let model = idle_model::<u64>();
    let a = empty_state::<u64>();
    let b_control = control::State {fibers:a.control.fibers.insert(0usize,empty_fiber(None,false))};
    let b = extend_child(a,b_control,0,0);
    let c_control = control::State {fibers:b.control.fibers.insert(1usize,empty_fiber(Some(0),false))};
    let c = extend_child(b,c_control,1,0);
    let d_control = control::State {fibers:c.control.fibers.insert(1usize,empty_fiber(Some(0),true))};
    let d = with_control(c,d_control);
    let e = counterexample_state();
    assert(control::step(a.control,b.control,0,control::Rule::Insert));
    assert forall|n:usize| registered(b,n) implies n == 0 by { }
    assert(shaped(b));
    assert(step(model,a,b,0,control::Rule::Insert));
    assert(control::step(b.control,c.control,1,control::Rule::Insert));
    lift_kernel_child_effect(b,c.control,0,1,0);
    assert(step(model,b,c,1,control::Rule::Insert));
    assert(step(model,c,d,1,control::Rule::Retire));
    assert(step(model,d,e,0,control::Rule::Retire));
    let states = seq![a,b,c,d,e];
    let labels = seq![(0usize,control::Rule::Insert),(1usize,control::Rule::Insert),
        (1usize,control::Rule::Retire),(0usize,control::Rule::Retire)];
    assert forall|i:int| 0 <= i < labels.len() implies step(model,states[i],states[i+1],labels[i].0,labels[i].1) by {
        if i == 0 { } else if i == 1 { } else if i == 2 { } else {assert(i == 3);}
    }
    execution_reaches(model,states,labels);
}

} // verus!
