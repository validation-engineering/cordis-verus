//! Finite, topologically ranked support and the arithmetic termination bound.
//! Edges include both providers and parents for support (Definition 74).
//! Applying these lemmas to a runtime requires a supplied topological order and
//! the paper's bounded-iterator/target-change premises; fresh IDs are not ranks.
use vstd::prelude::*;

verus! {
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum DagError { Shape, NotTopological }

pub open spec fn ranked(edges: Seq<Seq<usize>>, n: nat) -> bool {
    edges.len() == n && forall|i: int, j: int| 0 <= i < n && 0 <= j < edges[i].len()
        ==> #[trigger] edges[i][j] < i
}
pub open spec fn supported(edges: Seq<Seq<usize>>, selected: Seq<bool>, i: int) -> bool {
    forall|j: int| 0 <= j < edges[i].len() ==> #[trigger] selected[edges[i][j] as int]
}
pub open spec fn solution(enabled: Seq<bool>, edges: Seq<Seq<usize>>, selected: Seq<bool>) -> bool {
    selected.len() == enabled.len() && forall|i: int| 0 <= i < enabled.len()
        ==> selected[i] == (enabled[i] && supported(edges, selected, i))
}

/// The unique support set for a finite ranked registry with total provisions.
/// `enabled` means not retired and no dependency key is missing a provider.
/// Every parent/provider must appear in the edge list; inputs are explicit.
pub fn support(enabled: Vec<bool>, predecessors: Vec<Vec<usize>>) -> (result: Result<Vec<bool>, DagError>)
    ensures result.is_ok() ==> ranked(predecessors@.map(|i: int, v: Vec<usize>| v@), enabled.len() as nat)
        && solution(enabled@, predecessors@.map(|i: int, v: Vec<usize>| v@), result.unwrap()@),
        result.is_err() ==> !ranked(predecessors@.map(|i: int, v: Vec<usize>| v@), enabled.len() as nat),
{
    if predecessors.len() != enabled.len() { return Err(DagError::Shape); }
    let ghost edges = predecessors@.map(|i: int, v: Vec<usize>| v@);
    let mut selected: Vec<bool> = Vec::new();
    let mut i = 0;
    while i < enabled.len()
        invariant i <= enabled.len(), predecessors.len() == enabled.len(), selected.len() == i,
            edges == predecessors@.map(|i: int, v: Vec<usize>| v@),
            forall|a: int, b: int| 0 <= a < i && 0 <= b < edges[a].len() ==> #[trigger] edges[a][b] < a,
            forall|a: int| 0 <= a < i ==> selected[a] == (enabled[a] && supported(edges, selected@, a)),
        decreases enabled.len() - i,
    {
        let mut ok = enabled[i];
        let mut j = 0;
        while j < predecessors[i].len()
            invariant i < enabled.len(), predecessors.len() == enabled.len(), selected.len() == i,
                edges == predecessors@.map(|i: int, v: Vec<usize>| v@), j <= predecessors[i as int].len(),
                forall|b: int| 0 <= b < j ==> edges[i as int][b] < i,
                ok == (enabled[i as int] && forall|b: int| 0 <= b < j ==> #[trigger] selected[edges[i as int][b] as int]),
            decreases predecessors[i as int].len() - j,
        {
            let p = predecessors[i][j];
            if p >= i {
                assert(edges[i as int][j as int] == p);
                return Err(DagError::NotTopological);
            }
            ok = ok && selected[p];
            j += 1;
        }
        let ghost prior = selected@;
        selected.push(ok);
        proof {
            assert forall|a: int| 0 <= a < i + 1 implies selected[a] == (enabled[a] && supported(edges, selected@, a)) by {
                assert forall|b: int| 0 <= b < edges[a].len() implies selected[edges[a][b] as int] == prior[edges[a][b] as int] by {
                    assert(edges[a][b] < i);
                }
                assert(supported(edges, selected@, a) == supported(edges, prior, a));
            }
        }
        i += 1;
    }
    Ok(selected)
}

proof fn support_prefix_unique(enabled: Seq<bool>, edges: Seq<Seq<usize>>, left: Seq<bool>, right: Seq<bool>, n: nat)
    requires ranked(edges, enabled.len()), solution(enabled, edges, left), solution(enabled, edges, right), n <= enabled.len(),
    ensures forall|a: int| 0 <= a < n ==> left[a] == right[a],
    decreases n,
{
    if n > 0 {
        support_prefix_unique(enabled, edges, left, right, (n - 1) as nat);
        let i = n - 1;
        assert forall|j: int| 0 <= j < edges[i].len() implies left[edges[i][j] as int] == right[edges[i][j] as int] by {
            assert(edges[i][j] < i);
        }
        assert(supported(edges, left, i) == supported(edges, right, i));
        assert(left[i] == right[i]);
    }
}
/// A quiescent total-provision registry satisfying the support clauses has
/// one active set, independent of the schedule that reached it.
pub proof fn support_unique(enabled: Seq<bool>, edges: Seq<Seq<usize>>, left: Seq<bool>, right: Seq<bool>)
    requires ranked(edges, enabled.len()), solution(enabled, edges, left), solution(enabled, edges, right),
    ensures left == right,
{
    support_prefix_unique(enabled, edges, left, right, enabled.len());
    assert(left =~= right);
}

pub open spec fn sum_prefix(counts: Seq<nat>, n: nat) -> nat
    recommends n <= counts.len(),
    decreases n,
{
    if n == 0 { 0 } else { sum_prefix(counts, (n - 1) as nat) + counts[n - 1] }
}
/// Conservative form of Theorem 73's B recurrence, counting every earlier
/// ranked fiber as a possible predecessor. Natural arithmetic has no overflow.
pub open spec fn total_budget(n: nat, stages: nat) -> nat
    decreases n,
{
    if n == 0 { 0 } else {
        let prior = total_budget((n - 1) as nat, stages);
        prior + (stages + 3) * (2 + prior)
    }
}

/// Mechanical induction for S(n) <= (K+3)(V(n)+1),
/// V(n) <= 1 + sum of predecessor steps. This proves the finite bound, not
/// the applicability of those hypotheses to arbitrary futures/restarts.
pub proof fn finite_step_bound(counts: Seq<nat>, changes: Seq<nat>, stages: nat, n: nat)
    requires n <= counts.len(), counts.len() == changes.len(),
        forall|i: int| 0 <= i < counts.len() ==> counts[i] <= (stages + 3) * (changes[i] + 1)
            && changes[i] <= 1 + sum_prefix(counts, i as nat),
    ensures sum_prefix(counts, n) <= total_budget(n, stages),
    decreases n,
{
    if n > 0 {
        finite_step_bound(counts, changes, stages, (n - 1) as nat);
        let prior = sum_prefix(counts, (n - 1) as nat);
        let bound = total_budget((n - 1) as nat, stages);
        assert(changes[n - 1] + 1 <= 2 + prior);
        vstd::arithmetic::mul::lemma_mul_inequality((changes[n - 1] + 1) as int, (2 + prior) as int, (stages + 3) as int);
        vstd::arithmetic::mul::lemma_mul_inequality((2 + prior) as int, (2 + bound) as int, (stages + 3) as int);
    }
}
} // verus!
