//! Paper control rules for individual kernel calls.
//!
//! This projection erases effect values, accumulators, and iterators. Child
//! creation and retirement are separate orchestration calls here; combining
//! them into the paper's atomic effect iteration needs a further simulation.
//!
//! Ports encode the paper's keys together with their realm. Active fibers expose
//! every declared provision (the host checks total provision before publication).
//! `Restart` is the host's explicit cancellation/revision extension, not one of
//! the nine paper rules. Effect execution is a separate refinement obligation.
use crate::{Binding, Phase, Port};
use vstd::prelude::*;

verus! {

pub struct Fiber {
    pub parent: Option<usize>,
    pub retired: bool,
    pub phase: Phase,
    pub dependencies: ISet<Port>,
    pub provisions: ISet<Port>,
    pub committed: ISet<Binding>,
}

pub struct State { pub fibers: IMap<usize, Fiber> }

#[derive(Copy, Clone, PartialEq, Eq, Structural)]
pub enum Rule { Insert, Retire, Remove, Begin, Iter, Finish, Divert, Leave, Unload, Restart, Stutter }

pub open spec fn registered(s: State, n: usize) -> bool { s.fibers.dom().contains(n) }

/// Equation (46), specialized to total provisions. Retirement is deliberately
/// absent: a retired Active provider is published until L-Leave.
pub open spec fn publishes(s: State, p: Port, n: usize) -> bool {
    registered(s, n) && s.fibers[n].phase == Phase::Active && s.fibers[n].provisions.contains(p)
}

/// Definition 53: the target is a total provider-identity view on dependencies.
pub open spec fn target(s: State, n: usize, view: ISet<Binding>) -> bool {
    &&& registered(s, n) && !s.fibers[n].retired
    &&& forall|b: Binding| view.contains(b) ==> s.fibers[n].dependencies.contains(Port { key: b.key, realm: b.realm })
        && publishes(s, Port { key: b.key, realm: b.realm }, b.provider)
    &&& forall|p: Port| s.fibers[n].dependencies.contains(p) ==> exists|b: Binding| view.contains(b) && b.key == p.key && b.realm == p.realm
}

pub open spec fn coherent(s: State, n: usize) -> bool { target(s, n, s.fibers[n].committed) }

/// Definition 54. The kernel's strict commitment order rules out self edges.
pub open spec fn relied(s: State, n: usize) -> bool {
    exists|m: usize, b: Binding| registered(s, m) && m != n && s.fibers[m].phase != Phase::Inactive
        && s.fibers[m].committed.contains(b) && b.provider == n
}

/// Every other fiber, including its declarations and committed view, is fixed.
pub open spec fn frame(a: State, z: State, n: usize) -> bool {
    forall|m: usize| m != n ==> registered(a, m) == registered(z, m)
        && (registered(a, m) ==> a.fibers[m] == z.fibers[m])
}

pub open spec fn interface_same(a: Fiber, z: Fiber) -> bool {
    a.parent == z.parent && a.dependencies == z.dependencies && a.provisions == z.provisions
}

pub open spec fn phase_change(a: State, z: State, n: usize, phase: Phase) -> bool {
    &&& registered(a, n) && registered(z, n) && frame(a, z, n)
    &&& interface_same(a.fibers[n], z.fibers[n])
    &&& a.fibers[n].retired == z.fibers[n].retired
    &&& a.fibers[n].committed == z.fibers[n].committed
    &&& z.fibers[n].phase == phase
}

/// Each constructor states an independent relational rule. No implementation
/// buffers, tombstones, restoring flags, or declaration order occur here.
pub open spec fn step(a: State, z: State, n: usize, rule: Rule) -> bool {
    match rule {
        Rule::Insert => {
            &&& !registered(a, n) && registered(z, n) && frame(a, z, n)
            &&& !z.fibers[n].retired && z.fibers[n].phase == Phase::Inactive && z.fibers[n].committed.is_empty()
            &&& match z.fibers[n].parent { Some(p) => registered(a, p), None => true }
            &&& forall|m: usize, p: Port| registered(a, m) && a.fibers[m].provisions.contains(p)
                ==> !z.fibers[n].provisions.contains(p)
        },
        Rule::Retire => {
            &&& registered(a, n) && registered(z, n) && frame(a, z, n)
            &&& interface_same(a.fibers[n], z.fibers[n])
            &&& z.fibers[n].retired && z.fibers[n].phase == a.fibers[n].phase
            &&& z.fibers[n].committed == a.fibers[n].committed
        },
        Rule::Remove => {
            &&& registered(a, n) && !registered(z, n) && frame(a, z, n)
            &&& a.fibers[n].retired && a.fibers[n].phase == Phase::Inactive && a.fibers[n].committed.is_empty()
            &&& forall|m: usize| registered(a, m) ==> a.fibers[m].parent != Some(n)
        },
        Rule::Begin => {
            &&& registered(a, n) && registered(z, n) && frame(a, z, n)
            &&& a.fibers[n].phase == Phase::Inactive && z.fibers[n].phase == Phase::Loading
            &&& interface_same(a.fibers[n], z.fibers[n]) && a.fibers[n].retired == z.fibers[n].retired
            &&& target(a, n, z.fibers[n].committed)
        },
        Rule::Iter => a == z && registered(a, n) && a.fibers[n].phase == Phase::Loading && coherent(a, n),
        Rule::Finish => phase_change(a, z, n, Phase::Active) && a.fibers[n].phase == Phase::Loading && coherent(a, n),
        Rule::Divert => phase_change(a, z, n, Phase::Unloading) && a.fibers[n].phase == Phase::Loading && !coherent(a, n),
        Rule::Leave => phase_change(a, z, n, Phase::Unloading) && a.fibers[n].phase == Phase::Active && !coherent(a, n),
        Rule::Unload => {
            &&& registered(a, n) && registered(z, n) && frame(a, z, n)
            &&& a.fibers[n].phase == Phase::Unloading && !relied(a, n)
            &&& z.fibers[n].phase == Phase::Inactive && z.fibers[n].committed.is_empty()
            &&& interface_same(a.fibers[n], z.fibers[n]) && a.fibers[n].retired == z.fibers[n].retired
        },
        Rule::Restart => phase_change(a, z, n, Phase::Unloading)
            && (a.fibers[n].phase == Phase::Loading || a.fibers[n].phase == Phase::Active),
        Rule::Stutter => a == z,
    }
}

/// Structural and committed-view invariants of Definitions 49–50 and the
/// resource-safety discipline. A finite name bound witnesses a finite registry;
/// the bound is not an observable fiber identity or an activation order.
pub open spec fn name_bound(s: State, bound: nat) -> bool {
    forall|n: usize| registered(s, n) ==> n < bound
}

pub open spec fn parent_ranking(s: State, rank: spec_fn(usize) -> nat) -> bool {
    forall|n: usize| registered(s, n) ==> match s.fibers[n].parent {
        Some(p) => rank(p) < rank(n),
        None => true,
    }
}

pub open spec fn well_formed(s: State) -> bool {
    &&& exists|bound: nat| name_bound(s, bound)
    &&& forall|n: usize| registered(s, n) ==> match s.fibers[n].parent {
        Some(p) => registered(s, p),
        None => true,
    }
    &&& exists|rank: spec_fn(usize) -> nat| parent_ranking(s, rank)
    &&& forall|n: usize, m: usize, p: Port| registered(s, n) && registered(s, m)
        && s.fibers[n].provisions.contains(p) && s.fibers[m].provisions.contains(p) ==> n == m
    &&& forall|n: usize, b: Binding| registered(s, n) && s.fibers[n].committed.contains(b) ==> {
        &&& s.fibers[n].phase != Phase::Inactive
        &&& s.fibers[n].dependencies.contains(Port { key: b.key, realm: b.realm })
        &&& registered(s, b.provider) && s.fibers[b.provider].phase != Phase::Inactive
        &&& s.fibers[b.provider].provisions.contains(Port { key: b.key, realm: b.realm })
        &&& b.provider != n
    }
    &&& forall|n: usize, p: Port| registered(s, n) && s.fibers[n].phase != Phase::Inactive && s.fibers[n].dependencies.contains(p)
        ==> exists|b: Binding| s.fibers[n].committed.contains(b) && b.key == p.key && b.realm == p.realm
    &&& forall|n: usize, a: Binding, b: Binding| registered(s, n)
        && s.fibers[n].committed.contains(a) && s.fibers[n].committed.contains(b)
        && a.key == b.key && a.realm == b.realm ==> a.provider == b.provider
}

/// Provider identity, rather than equality of service values, determines a view.
pub proof fn target_unique(s: State, n: usize, left: ISet<Binding>, right: ISet<Binding>)
    requires well_formed(s), target(s, n, left), target(s, n, right),
    ensures left == right,
{
    assert(left =~= right) by {
        assert forall|b: Binding| left.contains(b) == right.contains(b) by {
            if left.contains(b) {
                let p = Port { key: b.key, realm: b.realm };
                let c = choose|c: Binding| right.contains(c) && c.key == p.key && c.realm == p.realm;
                assert(s.fibers[b.provider].provisions.contains(p));
                assert(s.fibers[c.provider].provisions.contains(p));
                assert(b.provider == c.provider);
                assert(b == c);
            }
            if right.contains(b) {
                let p = Port { key: b.key, realm: b.realm };
                let c = choose|c: Binding| left.contains(c) && c.key == p.key && c.realm == p.realm;
                assert(s.fibers[b.provider].provisions.contains(p));
                assert(s.fibers[c.provider].provisions.contains(p));
                assert(b.provider == c.provider);
                assert(b == c);
            }
        }
    }
}

/// Under single-source provisions, an installed fiber's available target can
/// only name its committed providers. A changed target therefore means bottom
/// (retirement or an unpublished dependency), rather than a different provider.
pub proof fn available_installed_coherent(s: State, n: usize, view: ISet<Binding>)
    requires well_formed(s), registered(s, n), s.fibers[n].phase != Phase::Inactive, target(s, n, view),
    ensures coherent(s, n),
{
    assert forall|b: Binding| s.fibers[n].committed.contains(b) implies
        s.fibers[n].dependencies.contains(Port { key: b.key, realm: b.realm })
        && publishes(s, Port { key: b.key, realm: b.realm }, b.provider) by {
        let p = Port { key: b.key, realm: b.realm };
        let c = choose|c: Binding| view.contains(c) && c.key == p.key && c.realm == p.realm;
        assert(publishes(s, p, c.provider));
        assert(s.fibers[b.provider].provisions.contains(p));
        assert(s.fibers[c.provider].provisions.contains(p));
        assert(b.provider == c.provider);
    }
}

/// The reflexive/transitive closure of the control rules. `allow_restart`
/// separates the runtime extension from executions of the paper's rule set.
pub open spec fn labelled_step(a: State, z: State, label: (usize, Rule), allow_restart: bool) -> bool {
    step(a, z, label.0, label.1) && (allow_restart || label.1 != Rule::Restart)
}

pub open spec fn reaches(a: State, z: State, count: nat, allow_restart: bool) -> bool
    decreases count,
{
    if count == 0 { a == z }
    else { exists|middle: State, label: (usize, Rule)| labelled_step(middle, z, label, allow_restart)
        && reaches(a, middle, (count - 1) as nat, allow_restart) }
}

pub open spec fn execution(states: Seq<State>, labels: Seq<(usize, Rule)>, allow_restart: bool) -> bool {
    states.len() == labels.len() + 1 && forall|i: int| 0 <= i < labels.len()
        ==> labelled_step(states[i], states[i + 1], labels[i], allow_restart)
}

/// Lift the per-call simulation obligations into a finite abstract execution.
/// This is composition, not a fairness, callback-correctness, or termination
/// premise. Restarts cannot be smuggled into the strict-paper closure.
pub proof fn finite_execution_refines(states: Seq<State>, labels: Seq<(usize, Rule)>, allow_restart: bool)
    requires execution(states, labels, allow_restart),
    ensures reaches(states.first(), states.last(), labels.len(), allow_restart),
    decreases labels.len(),
{
    if labels.len() == 0 {
        assert(states.first() == states.last());
    } else {
        let prefix = states.drop_last();
        let prefix_labels = labels.drop_last();
        assert(execution(prefix, prefix_labels, allow_restart)) by {
            assert forall|i: int| 0 <= i < prefix_labels.len()
                implies labelled_step(prefix[i], prefix[i + 1], prefix_labels[i], allow_restart) by {
                assert(prefix[i] == states[i]);
                assert(prefix[i + 1] == states[i + 1]);
                assert(prefix_labels[i] == labels[i]);
            }
        }
        finite_execution_refines(prefix, prefix_labels, allow_restart);
        let middle = prefix.last();
        let label = labels.last();
        assert(labelled_step(middle, states.last(), label, allow_restart));
        assert(prefix.first() == states.first());
        assert(reaches(states.first(), middle, (labels.len() - 1) as nat, allow_restart));
    }
}

pub open spec fn quiet(s: State) -> bool {
    forall|n: usize| registered(s, n) ==> match s.fibers[n].phase {
        Phase::Inactive => !(exists|view: ISet<Binding>| target(s, n, view)),
        Phase::Active => coherent(s, n),
        _ => false,
    }
}

} // verus!
