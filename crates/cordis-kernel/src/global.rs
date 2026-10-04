//! Global control theorems derived from the paper state, rather than supplied
//! as a precomputed support solution. Total provisions are represented by the
//! publishing predicate in `refinement`; effect/iterator steps refine this
//! control projection separately.
#[cfg(verus_keep_ghost)]
use crate::refinement::{self as paper, Fiber, Rule, State};
#[cfg(verus_keep_ghost)]
use crate::{Binding, Phase, Port};
use vstd::prelude::*;

verus! {

pub open spec fn active(s: State) -> ISet<usize> {
    ISet::new(|n: usize| paper::registered(s, n) && s.fibers[n].phase == Phase::Active)
}

/// The consequence of running a creator's child-retirement inverses. It is
/// needed at quiescence, not asserted of intermediate unloading states.
pub open spec fn retirement_closed(s: State) -> bool {
    forall|n: usize, p: usize| paper::registered(s, n) && s.fibers[n].parent == Some(p)
        && s.fibers[p].phase == Phase::Inactive ==> s.fibers[n].retired
}

pub open spec fn predecessor(s: State, provider: usize, consumer: usize) -> bool {
    paper::registered(s, provider) && paper::registered(s, consumer)
        && exists|p: Port| s.fibers[provider].provisions.contains(p)
            && s.fibers[consumer].dependencies.contains(p)
}

/// A finite topological certificate for Definition 72. Names need not coincide
/// with ranks, and unrelated fibers may share a rank.
pub open spec fn precedence_ranking(s: State, ranks: Seq<nat>) -> bool {
    &&& forall|n: usize| paper::registered(s, n) ==> n < ranks.len()
    &&& forall|m: usize, n: usize| predecessor(s, m, n) ==> ranks[m as int] < ranks[n as int]
}

pub open spec fn support_ranking(s: State, ranks: Seq<nat>) -> bool {
    precedence_ranking(s, ranks) && forall|n: usize, p: usize|
        paper::registered(s, n) && s.fibers[n].parent == Some(p)
            ==> ranks[p as int] < ranks[n as int]
}

pub open spec fn provided_by(s: State, selected: ISet<usize>, p: Port) -> bool {
    exists|m: usize| selected.contains(m) && paper::registered(s, m) && s.fibers[m].provisions.contains(p)
}

/// The actual clauses of Definition 74, reading only the registry's immutable
/// interfaces, parent identities and retirement bits.
pub open spec fn support_clause(s: State, selected: ISet<usize>, n: usize) -> bool {
    &&& paper::registered(s, n) && !s.fibers[n].retired
    &&& match s.fibers[n].parent { Some(p) => selected.contains(p), None => true }
    &&& forall|p: Port| s.fibers[n].dependencies.contains(p) ==> provided_by(s, selected, p)
}

pub open spec fn support_solution(s: State, selected: ISet<usize>) -> bool {
    forall|n: usize| selected.contains(n) == support_clause(s, selected, n)
}

pub proof fn target_iff_available(s: State, n: usize)
    requires paper::registered(s, n),
    ensures (exists|view: ISet<Binding>| paper::target(s, n, view)) ==
        (!s.fibers[n].retired && forall|p: Port| s.fibers[n].dependencies.contains(p)
            ==> exists|m: usize| paper::publishes(s, p, m)),
{
    if exists|view: ISet<Binding>| paper::target(s, n, view) {
        let view = choose|view: ISet<Binding>| paper::target(s, n, view);
        assert forall|p: Port| s.fibers[n].dependencies.contains(p) implies
            exists|m: usize| paper::publishes(s, p, m) by {
            let b = choose|b: Binding| view.contains(b) && b.key == p.key && b.realm == p.realm;
            assert(paper::publishes(s, p, b.provider));
        }
    }
    if !s.fibers[n].retired && forall|p: Port| s.fibers[n].dependencies.contains(p)
        ==> exists|m: usize| paper::publishes(s, p, m) {
        let view = ISet::new(|b: Binding| s.fibers[n].dependencies.contains(Port { key: b.key, realm: b.realm })
            && paper::publishes(s, Port { key: b.key, realm: b.realm }, b.provider));
        assert forall|p: Port| s.fibers[n].dependencies.contains(p) implies
            exists|b: Binding| view.contains(b) && b.key == p.key && b.realm == p.realm by {
            let m = choose|m: usize| paper::publishes(s, p, m);
            let b = Binding { key: p.key, realm: p.realm, provider: m };
            assert(view.contains(b));
        }
        assert(paper::target(s, n, view));
    }
}

/// Lemma 77's fixed-point obligation is derived here. In particular the parent
/// clause follows from the child inverse's retirement consequence, rather than
/// treating ownership as an implicit service dependency.
pub proof fn quiet_active_support(s: State)
    requires paper::well_formed(s), paper::quiet(s), retirement_closed(s),
    ensures support_solution(s, active(s)),
{
    assert forall|n: usize| active(s).contains(n) == support_clause(s, active(s), n) by {
        if paper::registered(s, n) {
            target_iff_available(s, n);
            assert(active(s).contains(n) == (exists|view: ISet<Binding>| paper::target(s, n, view)));
            if active(s).contains(n) {
                if let Some(p) = s.fibers[n].parent {
                    assert(paper::registered(s, p));
                    assert(s.fibers[p].phase != Phase::Inactive);
                    assert(active(s).contains(p));
                }
            }
            assert forall|p: Port| s.fibers[n].dependencies.contains(p) implies
                ((exists|m: usize| paper::publishes(s, p, m)) == provided_by(s, active(s), p)) by {
                if exists|m: usize| paper::publishes(s, p, m) {
                    let m = choose|m: usize| paper::publishes(s, p, m);
                    assert(active(s).contains(m));
                    assert(provided_by(s, active(s), p));
                }
                if provided_by(s, active(s), p) {
                    let m = choose|m: usize| active(s).contains(m) && paper::registered(s, m)
                        && s.fibers[m].provisions.contains(p);
                    assert(paper::publishes(s, p, m));
                }
            }
            if support_clause(s, active(s), n) {
                assert forall|p: Port| s.fibers[n].dependencies.contains(p) implies
                    exists|m: usize| paper::publishes(s, p, m) by {
                    assert(provided_by(s, active(s), p));
                }
                assert(exists|view: ISet<Binding>| paper::target(s, n, view));
                assert(active(s).contains(n));
            }
            assert(active(s).contains(n) ==> support_clause(s, active(s), n));
        }
    }
}

proof fn support_unique_at(s: State, ranks: Seq<nat>, left: ISet<usize>, right: ISet<usize>, n: usize)
    requires paper::well_formed(s), support_ranking(s, ranks),
        support_solution(s, left), support_solution(s, right), paper::registered(s, n),
    ensures left.contains(n) == right.contains(n),
    decreases ranks[n as int],
{
    assert forall|m: usize| paper::registered(s, m)
        && (s.fibers[n].parent == Some(m) || predecessor(s, m, n)) implies
        left.contains(m) == right.contains(m) by {
        support_unique_at(s, ranks, left, right, m);
    }
    assert forall|p: Port| s.fibers[n].dependencies.contains(p) implies
        (provided_by(s, left, p) == provided_by(s, right, p)) by {
        if exists|m: usize| left.contains(m) && paper::registered(s, m) && s.fibers[m].provisions.contains(p) {
            let m = choose|m: usize| left.contains(m) && paper::registered(s, m) && s.fibers[m].provisions.contains(p);
            assert(predecessor(s, m, n));
            assert(right.contains(m));
        }
        if exists|m: usize| right.contains(m) && paper::registered(s, m) && s.fibers[m].provisions.contains(p) {
            let m = choose|m: usize| right.contains(m) && paper::registered(s, m) && s.fibers[m].provisions.contains(p);
            assert(predecessor(s, m, n));
            assert(left.contains(m));
        }
    }
    if let Some(p) = s.fibers[n].parent {
        assert(paper::registered(s, p));
        assert(left.contains(p) == right.contains(p));
    }
    assert(support_clause(s, left, n) == support_clause(s, right, n));
}

pub proof fn support_unique(s: State, ranks: Seq<nat>, left: ISet<usize>, right: ISet<usize>)
    requires paper::well_formed(s), support_ranking(s, ranks),
        support_solution(s, left), support_solution(s, right),
    ensures left == right,
{
    assert(left =~= right) by {
        assert forall|n: usize| left.contains(n) == right.contains(n) by {
            if paper::registered(s, n) { support_unique_at(s, ranks, left, right, n); }
        }
    }
}

/// Equal orchestration/static data; lifecycle phases and committed views may
/// differ. This does not assume that both schedules chose the same active set.
pub open spec fn same_input(left: State, right: State) -> bool {
    left.fibers.dom() == right.fibers.dom() && forall|n: usize| paper::registered(left, n) ==>
        paper::interface_same(left.fibers[n], right.fibers[n])
            && left.fibers[n].retired == right.fibers[n].retired
}

pub proof fn quiet_active_unique(left: State, right: State, ranks: Seq<nat>)
    requires paper::well_formed(left), paper::well_formed(right),
        paper::quiet(left), paper::quiet(right), retirement_closed(left), retirement_closed(right),
        same_input(left, right), support_ranking(left, ranks),
    ensures active(left) == active(right),
{
    quiet_active_support(left);
    quiet_active_support(right);
    assert forall|n: usize| support_clause(left, active(right), n) == support_clause(right, active(right), n) by {
        assert(paper::registered(left, n) == paper::registered(right, n));
        if paper::registered(left, n) {
            assert(paper::interface_same(left.fibers[n], right.fibers[n]));
            assert(left.fibers[n].retired == right.fibers[n].retired);
        }
        assert forall|p: Port| #[trigger] provided_by(left, active(right), p) == provided_by(right, active(right), p) by {
            if provided_by(left, active(right), p) {
                let m = choose|m: usize| active(right).contains(m) && paper::registered(left, m) && left.fibers[m].provisions.contains(p);
                assert(paper::interface_same(left.fibers[m], right.fibers[m]));
                assert(provided_by(right, active(right), p));
            }
            if provided_by(right, active(right), p) {
                let m = choose|m: usize| active(right).contains(m) && paper::registered(right, m) && right.fibers[m].provisions.contains(p);
                assert(paper::registered(left, m));
                assert(paper::interface_same(left.fibers[m], right.fibers[m]));
                assert(provided_by(left, active(right), p));
            }
        }
        if paper::registered(left, n) {
            assert(left.fibers[n].dependencies == right.fibers[n].dependencies);
            assert forall|p: Port| left.fibers[n].dependencies.contains(p) implies
                provided_by(left, active(right), p) == provided_by(right, active(right), p) by { }
            assert(support_clause(left, active(right), n) ==> support_clause(right, active(right), n));
            assert(support_clause(right, active(right), n) ==> support_clause(left, active(right), n));
        }
    }
    support_unique(left, ranks, active(left), active(right));
}


/// Target's fixed point reads providers and retirement only. This equation has
/// a unique solution under acyclic precedence even when the support union with
/// retired ownership entries contains a cycle.
pub open spec fn dependency_clause(s: State, selected: ISet<usize>, n: usize) -> bool {
    paper::registered(s, n) && !s.fibers[n].retired && forall|p: Port|
        s.fibers[n].dependencies.contains(p) ==> provided_by(s, selected, p)
}
pub open spec fn dependency_solution(s: State, selected: ISet<usize>) -> bool {
    forall|n: usize| selected.contains(n) == dependency_clause(s, selected, n)
}

pub proof fn quiet_dependency_solution(s: State)
    requires paper::quiet(s),
    ensures dependency_solution(s, active(s)),
{
    assert forall|n: usize| active(s).contains(n) == dependency_clause(s, active(s), n) by {
        if paper::registered(s, n) {
            target_iff_available(s, n);
            assert(active(s).contains(n) == (exists|view: ISet<Binding>| paper::target(s, n, view)));
            assert forall|p: Port| s.fibers[n].dependencies.contains(p) implies
                ((exists|m: usize| paper::publishes(s, p, m)) == provided_by(s, active(s), p)) by {
                if exists|m: usize| paper::publishes(s, p, m) {
                    let m = choose|m: usize| paper::publishes(s, p, m);
                    assert(active(s).contains(m));
                    assert(provided_by(s, active(s), p));
                }
                if provided_by(s, active(s), p) {
                    let m = choose|m: usize| active(s).contains(m) && paper::registered(s, m)
                        && s.fibers[m].provisions.contains(p);
                    assert(paper::publishes(s, p, m));
                }
            }
            if dependency_clause(s, active(s), n) {
                assert forall|p: Port| s.fibers[n].dependencies.contains(p) implies
                    exists|m: usize| paper::publishes(s, p, m) by {
                    assert(provided_by(s, active(s), p));
                }
            }
        }
    }
}

proof fn dependency_unique_at(s: State, ranks: Seq<nat>, left: ISet<usize>, right: ISet<usize>, n: usize)
    requires precedence_ranking(s, ranks), dependency_solution(s, left),
        dependency_solution(s, right), paper::registered(s, n),
    ensures left.contains(n) == right.contains(n),
    decreases ranks[n as int],
{
    assert forall|m: usize| predecessor(s, m, n) implies left.contains(m) == right.contains(m) by {
        dependency_unique_at(s, ranks, left, right, m);
    }
    assert forall|p: Port| s.fibers[n].dependencies.contains(p) implies
        (provided_by(s, left, p) == provided_by(s, right, p)) by {
        if provided_by(s, left, p) {
            let m = choose|m: usize| left.contains(m) && paper::registered(s, m) && s.fibers[m].provisions.contains(p);
            assert(predecessor(s, m, n));
            assert(right.contains(m));
        }
        if provided_by(s, right, p) {
            let m = choose|m: usize| right.contains(m) && paper::registered(s, m) && s.fibers[m].provisions.contains(p);
            assert(predecessor(s, m, n));
            assert(left.contains(m));
        }
    }
    assert(dependency_clause(s, left, n) == dependency_clause(s, right, n));
}

/// A stronger usable active-set conclusion than the support-ranking route:
/// provider precedence alone suffices. The theorem does not pretend that it
/// establishes acyclicity of the union disproved by replacement_support_cycle.
pub proof fn quiet_active_unique_by_precedence(left: State, right: State, ranks: Seq<nat>)
    requires paper::quiet(left), paper::quiet(right), same_input(left, right), precedence_ranking(left, ranks),
    ensures active(left) == active(right),
{
    quiet_dependency_solution(left);
    quiet_dependency_solution(right);
    assert forall|n: usize| dependency_clause(left, active(right), n) == dependency_clause(right, active(right), n) by {
        assert(paper::registered(left, n) == paper::registered(right, n));
        if paper::registered(left, n) {
            assert(paper::interface_same(left.fibers[n], right.fibers[n]));
            assert(left.fibers[n].retired == right.fibers[n].retired);
        }
        assert forall|p: Port| #[trigger] provided_by(left, active(right), p) == provided_by(right, active(right), p) by {
            if provided_by(left, active(right), p) {
                let m = choose|m: usize| active(right).contains(m) && paper::registered(left, m) && left.fibers[m].provisions.contains(p);
                assert(paper::interface_same(left.fibers[m], right.fibers[m]));
                assert(provided_by(right, active(right), p));
            }
            if provided_by(right, active(right), p) {
                let m = choose|m: usize| active(right).contains(m) && paper::registered(right, m) && right.fibers[m].provisions.contains(p);
                assert(paper::registered(left, m));
                assert(paper::interface_same(left.fibers[m], right.fibers[m]));
                assert(provided_by(left, active(right), p));
            }
        }
        if paper::registered(left, n) {
            assert(left.fibers[n].dependencies == right.fibers[n].dependencies);
            assert forall|p: Port| left.fibers[n].dependencies.contains(p) implies
                provided_by(left, active(right), p) == provided_by(right, active(right), p) by { }
            assert(dependency_clause(left, active(right), n) ==> dependency_clause(right, active(right), n));
            assert(dependency_clause(right, active(right), n) ==> dependency_clause(left, active(right), n));
        }
    }
    assert(dependency_solution(left, active(right)));
    assert(active(left) =~= active(right)) by {
        assert forall|n: usize| active(left).contains(n) == active(right).contains(n) by {
            if paper::registered(left, n) {
                dependency_unique_at(left, ranks, active(left), active(right), n);
            }
        }
    }
}


/// Complete control normal forms, including committed provider identities,
/// coincide under the same orchestration/static input. Table values, dynamic
/// names, and hidden effects belong to the separate observational proof.
pub proof fn quiet_control_unique(left: State, right: State, ranks: Seq<nat>)
    requires paper::well_formed(left), paper::well_formed(right),
        paper::quiet(left), paper::quiet(right), same_input(left, right), precedence_ranking(left, ranks),
    ensures left == right,
{
    quiet_active_unique_by_precedence(left, right, ranks);
    assert forall|p: Port, m: usize| paper::publishes(left, p, m) == paper::publishes(right, p, m) by {
        assert(paper::registered(left, m) == paper::registered(right, m));
        if paper::registered(left, m) {
            assert(paper::interface_same(left.fibers[m], right.fibers[m]));
            assert(active(left).contains(m) == active(right).contains(m));
        }
    }
    assert(left.fibers =~= right.fibers) by {
        assert(left.fibers.dom() == right.fibers.dom());
        assert forall|n: usize| left.fibers.dom().contains(n) implies left.fibers[n] == right.fibers[n] by {
            assert(paper::registered(left, n));
            assert(paper::registered(right, n));
            assert(paper::interface_same(left.fibers[n], right.fibers[n]));
            assert(left.fibers[n].retired == right.fibers[n].retired);
            assert(active(left).contains(n) == active(right).contains(n));
            assert(left.fibers[n].phase == right.fibers[n].phase);
            if left.fibers[n].phase == Phase::Inactive {
                assert(left.fibers[n].committed =~= ISet::empty()) by {
                    assert forall|b: Binding| !left.fibers[n].committed.contains(b) by { }
                }
                assert(right.fibers[n].committed =~= ISet::empty()) by {
                    assert forall|b: Binding| !right.fibers[n].committed.contains(b) by { }
                }
            } else {
                assert(paper::coherent(left, n));
                assert(paper::coherent(right, n));
                assert forall|b: Binding| right.fibers[n].committed.contains(b) implies
                    left.fibers[n].dependencies.contains(Port { key: b.key, realm: b.realm })
                        && paper::publishes(left, Port { key: b.key, realm: b.realm }, b.provider) by {
                    assert(paper::publishes(right, Port { key: b.key, realm: b.realm }, b.provider));
                }
                assert(paper::target(left, n, right.fibers[n].committed));
                paper::target_unique(left, n, left.fibers[n].committed, right.fibers[n].committed);
            }
        }
    }
}

pub open spec fn promptly_enabled(s: State, n: usize) -> bool {
    paper::registered(s, n) && match s.fibers[n].phase {
        Phase::Inactive => exists|view: ISet<Binding>| paper::target(s, n, view),
        Phase::Loading => true,
        Phase::Active => !paper::coherent(s, n),
        Phase::Unloading => false,
    }
}

pub open spec fn lifecycle_rule(rule: Rule) -> bool {
    rule == Rule::Begin || rule == Rule::Iter || rule == Rule::Finish
        || rule == Rule::Divert || rule == Rule::Leave || rule == Rule::Unload
}


/// A lifecycle rule preserves the input fields used by support/target; this is
/// derived from each rule, rather than an assumed frame for an entire trace.
pub proof fn lifecycle_input_frame(a: State, z: State, actor: usize, rule: Rule)
    requires paper::step(a, z, actor, rule), lifecycle_rule(rule),
    ensures same_input(a, z),
{
    assert(a.fibers.dom() =~= z.fibers.dom()) by {
        assert forall|n: usize| a.fibers.dom().contains(n) == z.fibers.dom().contains(n) by {
            if n != actor { assert(paper::registered(a, n) == paper::registered(z, n)); }
        }
    }
    assert forall|n: usize| paper::registered(a, n) implies
        paper::interface_same(a.fibers[n], z.fibers[n]) && a.fibers[n].retired == z.fibers[n].retired by {
        if n != actor { assert(a.fibers[n] == z.fibers[n]); }
    }
}

/// Theorem 73(B), for ordinary control lifecycle steps: a target can change
/// only at a declared provider's step. Child-retirement effect maps add the
/// separate monotone retirement cause in the full semantics.
pub proof fn lifecycle_target_frame(a: State, z: State, actor: usize, n: usize, rule: Rule)
    requires paper::step(a, z, actor, rule), lifecycle_rule(rule),
        paper::registered(a, n), !predecessor(a, actor, n),
    ensures forall|view: ISet<Binding>| paper::target(a, n, view) == paper::target(z, n, view),
{
    lifecycle_input_frame(a, z, actor, rule);
    assert(paper::registered(z, n));
    assert(paper::interface_same(a.fibers[n], z.fibers[n]));
    assert(a.fibers[n].retired == z.fibers[n].retired);
    assert forall|p: Port, provider: usize| a.fibers[n].dependencies.contains(p) implies
        paper::publishes(a, p, provider) == paper::publishes(z, p, provider) by {
        if provider != actor {
            assert(paper::registered(a, provider) == paper::registered(z, provider));
            if paper::registered(a, provider) { assert(a.fibers[provider] == z.fibers[provider]); }
        } else {
            assert(paper::registered(a, actor));
            assert(!a.fibers[actor].provisions.contains(p));
            assert(paper::interface_same(a.fibers[actor], z.fibers[actor]));
        }
    }
    assert forall|view: ISet<Binding>| paper::target(a, n, view) == paper::target(z, n, view) by {
        assert forall|b: Binding| view.contains(b) && a.fibers[n].dependencies.contains(Port { key: b.key, realm: b.realm }) implies
            paper::publishes(a, Port { key: b.key, realm: b.realm }, b.provider)
                == paper::publishes(z, Port { key: b.key, realm: b.realm }, b.provider) by { }
    }
}

pub proof fn target_change_strictly_precedes(a: State, z: State, ranks: Seq<nat>, actor: usize, n: usize, rule: Rule,
    view: ISet<Binding>)
    requires paper::step(a, z, actor, rule), lifecycle_rule(rule), precedence_ranking(a, ranks),
        paper::registered(a, n), paper::target(a, n, view) != paper::target(z, n, view),
    ensures predecessor(a, actor, n), actor != n, ranks[actor as int] < ranks[n as int],
{
    if !predecessor(a, actor, n) { lifecycle_target_frame(a, z, actor, n, rule); }
}

pub open spec fn successor(s: State, n: usize, phase: Phase, committed: ISet<Binding>) -> State {
    State { fibers: s.fibers.insert(n, Fiber {
        parent: s.fibers[n].parent, retired: s.fibers[n].retired,
        dependencies: s.fibers[n].dependencies, provisions: s.fibers[n].provisions,
        phase, committed,
    }) }
}

proof fn immediate_successor(s: State, n: usize)
    requires promptly_enabled(s, n),
    ensures exists|z: State, rule: Rule| lifecycle_rule(rule) && paper::step(s, z, n, rule),
{
    match s.fibers[n].phase {
        Phase::Inactive => {
            let view = choose|view: ISet<Binding>| paper::target(s, n, view);
            let z = successor(s, n, Phase::Loading, view);
            assert(paper::step(s, z, n, Rule::Begin));
        },
        Phase::Loading => {
            if paper::coherent(s, n) {
                assert(paper::step(s, s, n, Rule::Iter));
            } else {
                let z = successor(s, n, Phase::Unloading, s.fibers[n].committed);
                assert(paper::step(s, z, n, Rule::Divert));
            }
        },
        Phase::Active => {
            let z = successor(s, n, Phase::Unloading, s.fibers[n].committed);
            assert(paper::step(s, z, n, Rule::Leave));
        },
        Phase::Unloading => { },
    }
}

pub open spec fn rank_sum(ranks: Seq<nat>) -> nat
    decreases ranks.len(),
{
    if ranks.len() == 0 { 0 } else { ranks.last() + rank_sum(ranks.drop_last()) }
}
proof fn rank_bounded(ranks: Seq<nat>, n: int)
    requires 0 <= n < ranks.len(),
    ensures ranks[n] <= rank_sum(ranks),
    decreases ranks.len(),
{
    if n < ranks.len() - 1 { rank_bounded(ranks.drop_last(), n); }
}

proof fn unloading_chain(s: State, ranks: Seq<nat>, n: usize)
    requires paper::well_formed(s), precedence_ranking(s, ranks),
        forall|m: usize| !promptly_enabled(s, m),
        paper::registered(s, n), s.fibers[n].phase == Phase::Unloading,
    ensures exists|m: usize| paper::registered(s, m) && s.fibers[m].phase == Phase::Unloading && !paper::relied(s, m),
    decreases rank_sum(ranks) - ranks[n as int],
{
    if paper::relied(s, n) {
        let (m, b) = choose|m: usize, b: Binding| paper::registered(s, m) && m != n
            && s.fibers[m].phase != Phase::Inactive && s.fibers[m].committed.contains(b) && b.provider == n;
        let p = Port { key: b.key, realm: b.realm };
        assert(s.fibers[n].provisions.contains(p));
        assert(s.fibers[m].dependencies.contains(p));
        assert(predecessor(s, n, m));
        assert(!paper::publishes(s, p, n));
        assert(!paper::coherent(s, m));
        assert(!promptly_enabled(s, m));
        assert(s.fibers[m].phase == Phase::Unloading);
        rank_bounded(ranks, m as int);
        unloading_chain(s, ranks, m);
    }
}

/// No deadlock for the lifecycle control relation, deriving the unloadable
/// maximal consumer rather than assuming one exists. Loading is an abstract
/// iteration here: a concrete async host must additionally land its pending
/// stage; this theorem does not claim that an arbitrary future terminates.
pub proof fn control_no_deadlock(s: State, ranks: Seq<nat>)
    requires paper::well_formed(s), precedence_ranking(s, ranks), !paper::quiet(s),
    ensures exists|n: usize, z: State, rule: Rule| lifecycle_rule(rule) && paper::step(s, z, n, rule),
{
    if exists|n: usize| promptly_enabled(s, n) {
        let n = choose|n: usize| promptly_enabled(s, n);
        immediate_successor(s, n);
    } else {
        let n = choose|n: usize| paper::registered(s, n) && match s.fibers[n].phase {
            Phase::Inactive => exists|view: ISet<Binding>| paper::target(s, n, view),
            Phase::Active => !paper::coherent(s, n),
            _ => true,
        };
        assert(!promptly_enabled(s, n));
        assert(s.fibers[n].phase == Phase::Unloading);
        unloading_chain(s, ranks, n);
        let m = choose|m: usize| paper::registered(s, m) && s.fibers[m].phase == Phase::Unloading && !paper::relied(s, m);
        let z = successor(s, m, Phase::Inactive, ISet::empty());
        assert(paper::step(s, z, m, Rule::Unload));
    }
}

/// A finite state reached by the executable regression in `paper_support.rs`.
/// It retains an inactive retired child after its creator unloads, then replaces
/// the removed provider. All provisions are total whenever Active (none is).
pub open spec fn replacement_cycle_state() -> State {
    let x = Port { key: 0, realm: 0 };
    let y = Port { key: 1, realm: 0 };
    let z = Port { key: 2, realm: 0 };
    State { fibers: IMap::empty()
        .insert(1usize, Fiber { parent: None, retired: false, phase: Phase::Inactive,
            dependencies: ISet::empty().insert(x), provisions: ISet::empty(), committed: ISet::empty() })
        .insert(2usize, Fiber { parent: Some(1usize), retired: true, phase: Phase::Inactive,
            dependencies: ISet::empty().insert(z), provisions: ISet::empty().insert(y), committed: ISet::empty() })
        .insert(3usize, Fiber { parent: None, retired: false, phase: Phase::Inactive,
            dependencies: ISet::empty().insert(y), provisions: ISet::empty().insert(x), committed: ISet::empty() }) }
}

/// Declaration-only union of all names introduced by the counterexample.
/// The removed old provider is retained here only to check historical
/// precedence, not as a claim that simultaneous registry provisions overlap.
pub open spec fn replacement_historical_interfaces() -> State {
    State { fibers: replacement_cycle_state().fibers.insert(0usize, Fiber {
        parent: None, retired: true, phase: Phase::Inactive, dependencies: ISet::empty(),
        provisions: ISet::empty().insert(Port { key: 0, realm: 0 }), committed: ISet::empty(),
    }) }
}

/// The raw support-union acyclicity statement of Lemma 75 needs an additional
/// restriction across removal/replacement: pointwise single-source provisions
/// and acyclic provider precedence do not establish it. This is a proved
/// counterexample to that implication, not an axiom or a failed proof accepted
/// as evidence. The corrected uniqueness theorem above carries its certificate.
pub proof fn replacement_support_cycle()
    ensures
        paper::well_formed(replacement_cycle_state()),
        paper::quiet(replacement_cycle_state()),
        retirement_closed(replacement_cycle_state()),
        precedence_ranking(replacement_cycle_state(), seq![0nat, 2nat, 0nat, 1nat]),
        precedence_ranking(replacement_historical_interfaces(), seq![0nat, 2nat, 0nat, 1nat]),
        forall|ranks: Seq<nat>| !support_ranking(replacement_cycle_state(), ranks),
        support_solution(replacement_cycle_state(), ISet::empty()),
{
    let s = replacement_cycle_state();
    let parent_rank = |n: usize| n as nat;
    assert(paper::name_bound(s, 4));
    assert(paper::parent_ranking(s, parent_rank));
    assert(paper::well_formed(s));
    assert forall|n: usize| paper::registered(s, n) implies
        !(exists|view: ISet<Binding>| paper::target(s, n, view)) by {
        target_iff_available(s, n);
        let p = if n == 1 { Port { key: 0, realm: 0 } }
            else if n == 2 { Port { key: 2, realm: 0 } }
            else { Port { key: 1, realm: 0 } };
        assert(s.fibers[n].dependencies.contains(p));
        assert(!(exists|m: usize| paper::publishes(s, p, m)));
    }
    assert(paper::quiet(s));
    assert(retirement_closed(s));
    quiet_active_support(s);
    assert(active(s) =~= ISet::empty());
    assert forall|ranks: Seq<nat>| !support_ranking(s, ranks) by {
        if support_ranking(s, ranks) {
            let x = Port { key: 0, realm: 0 };
            let y = Port { key: 1, realm: 0 };
            assert(s.fibers[2usize].provisions.contains(y) && s.fibers[3usize].dependencies.contains(y));
            assert(s.fibers[3usize].provisions.contains(x) && s.fibers[1usize].dependencies.contains(x));
            assert(predecessor(s, 2usize, 3usize));
            assert(predecessor(s, 3usize, 1usize));
            assert(ranks[2] < ranks[3]);
            assert(ranks[3] < ranks[1]);
            assert(ranks[1] < ranks[2]);
        }
    }
}

/// The counterexample concerns the claimed well-foundedness, not a fabricated
/// ambiguity in its normal form. Its retired child forces the unique support
/// solution to be empty despite the union cycle.
pub proof fn replacement_support_still_unique(selected: ISet<usize>)
    requires support_solution(replacement_cycle_state(), selected),
    ensures selected == ISet::<usize>::empty(),
{
    let s = replacement_cycle_state();
    let x = Port { key: 0, realm: 0 };
    let y = Port { key: 1, realm: 0 };
    assert(!selected.contains(2usize));
    assert(!provided_by(s, selected, y));
    assert(!selected.contains(3usize)) by {
        assert(s.fibers[3usize].dependencies.contains(y));
    }
    assert(!provided_by(s, selected, x));
    assert(!selected.contains(1usize)) by {
        assert(s.fibers[1usize].dependencies.contains(x));
    }
    assert(selected =~= ISet::empty()) by {
        assert forall|n: usize| !selected.contains(n) by {
            assert(selected.contains(n) ==> paper::registered(s, n));
        }
    }
}

pub open spec fn insert_fiber(s: State, n: usize, parent: Option<usize>, dependencies: ISet<Port>, provisions: ISet<Port>) -> State {
    State { fibers: s.fibers.insert(n, Fiber { parent, retired: false, phase: Phase::Inactive,
        dependencies, provisions, committed: ISet::empty() }) }
}
pub open spec fn retire_fiber(s: State, n: usize) -> State {
    State { fibers: s.fibers.insert(n, Fiber { parent: s.fibers[n].parent, retired: true,
        phase: s.fibers[n].phase, dependencies: s.fibers[n].dependencies,
        provisions: s.fibers[n].provisions, committed: s.fibers[n].committed }) }
}

/// Reachability of the counterexample in the strict paper control rules. The
/// child insertion/retirement are the two control projections of Definition 52;
/// their actual host/kernel ordering is also exercised by the regression.
pub proof fn replacement_cycle_reachable()
    ensures paper::reaches(State { fibers: IMap::empty() }, replacement_cycle_state(), 16, false),
{
    let x = Port { key: 0, realm: 0 };
    let y = Port { key: 1, realm: 0 };
    let z = Port { key: 2, realm: 0 };
    let empty = ISet::empty();
    let s0 = State { fibers: IMap::empty() };
    let s1 = insert_fiber(s0, 0, None, empty, ISet::empty().insert(x));
    let s2 = insert_fiber(s1, 1, None, ISet::empty().insert(x), empty);
    let s3 = successor(s2, 0, Phase::Loading, ISet::empty());
    let s4 = successor(s3, 0, Phase::Active, ISet::empty());
    let bound = ISet::empty().insert(Binding { key: 0, realm: 0, provider: 0 });
    let s5 = successor(s4, 1, Phase::Loading, bound);
    let s6 = insert_fiber(s5, 2, Some(1), ISet::empty().insert(z), ISet::empty().insert(y));
    let s7 = s6;
    let s8 = successor(s7, 1, Phase::Active, bound);
    let s9 = retire_fiber(s8, 0);
    let s10 = successor(s9, 0, Phase::Unloading, ISet::empty());
    let s11 = successor(s10, 1, Phase::Unloading, bound);
    let s12 = retire_fiber(s11, 2);
    let s13 = successor(s12, 1, Phase::Inactive, ISet::empty());
    let s14 = successor(s13, 0, Phase::Inactive, ISet::empty());
    let s15 = State { fibers: s14.fibers.remove(0usize) };
    let s16 = insert_fiber(s15, 3, None, ISet::empty().insert(y), ISet::empty().insert(x));
    let states = seq![s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16];
    let labels = seq![(0usize, Rule::Insert), (1usize, Rule::Insert), (0usize, Rule::Begin),
        (0usize, Rule::Finish), (1usize, Rule::Begin), (2usize, Rule::Insert), (1usize, Rule::Iter),
        (1usize, Rule::Finish), (0usize, Rule::Retire), (0usize, Rule::Leave), (1usize, Rule::Leave),
        (2usize, Rule::Retire), (1usize, Rule::Unload), (0usize, Rule::Unload), (0usize, Rule::Remove),
        (3usize, Rule::Insert)];
    assert(paper::step(s0, s1, 0, Rule::Insert));
    assert(paper::step(s1, s2, 1, Rule::Insert));
    assert(paper::step(s2, s3, 0, Rule::Begin));
    assert(paper::step(s3, s4, 0, Rule::Finish));
    let binding = Binding { key: 0, realm: 0, provider: 0 };
    assert(bound.contains(binding));
    assert(paper::publishes(s4, x, 0));
    assert(paper::target(s4, 1, bound));
    assert(paper::step(s4, s5, 1, Rule::Begin));
    assert(paper::step(s5, s6, 2, Rule::Insert));
    assert(paper::step(s6, s7, 1, Rule::Iter));
    assert(paper::step(s7, s8, 1, Rule::Finish));
    assert(paper::step(s8, s9, 0, Rule::Retire));
    assert(paper::step(s9, s10, 0, Rule::Leave));
    assert(s10.fibers[1usize].committed.contains(binding));
    assert(!paper::publishes(s10, x, 0));
    assert(!paper::coherent(s10, 1));
    assert(paper::step(s10, s11, 1, Rule::Leave));
    assert(paper::step(s11, s12, 2, Rule::Retire));
    assert(paper::step(s12, s13, 1, Rule::Unload));
    assert(paper::step(s13, s14, 0, Rule::Unload));
    assert(paper::step(s14, s15, 0, Rule::Remove));
    assert(paper::step(s15, s16, 3, Rule::Insert));
    assert forall|i: int| 0 <= i < labels.len() implies paper::labelled_step(states[i], states[i + 1], labels[i], false) by { }
    assert(paper::execution(states, labels, false));
    assert(s16.fibers =~= replacement_cycle_state().fibers);
    assert(s16 == replacement_cycle_state());
    paper::finite_execution_refines(states, labels, false);
}
} // verus!
