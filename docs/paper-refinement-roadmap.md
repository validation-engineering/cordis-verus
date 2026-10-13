# Whole-paper refinement milestones

[简体中文](paper-refinement-roadmap.zh-CN.md)

The goal is to connect the constraints in the Cordis paper to the code that
actually runs, and make the resulting guarantees useful to plugin authors.
The [original ledger](paper-obligations.json) remains the authority for the
81 numbered items and four integration obligations. The
[work map](paper-refinement-map.md) assigns every item to a work package and
records review entry points, unresolved premises and acceptance criteria.

R0 is complete as a planning baseline. R1 is complete for the explicit
[finite strict interpretation](r1-semantics.md), with required revisions recorded
separately from the original paper. R2–R4 have partial results; R5 remains planned. These are work milestones, not percentages of correctness.
Encoding a definition does not establish that a production component satisfies it.

| Milestone | Deliverable | Exit condition |
| --- | --- | --- |
| R0 · Acceptance baseline | All 81 items and four integration obligations allocated, with source roles, gaps and concrete next actions | Inventory, source-reference and dependency checks pass; the original audit gate stays unchanged |
| R1 · Semantics and representation | A consistent context/Component interpretation and its implementation representation | Establish full-carrier membership, editor and observation laws, and the exact treatment of strict failure; separate necessary revisions from original statements |
| R2 · Production execution | Actual arguments, outcomes, continuations, inverses, concurrent actions and host protocol composition | Public managed calls establish their premises and refine paper steps, observation-preserving internal steps or explicitly specified extensions |
| R3 · General recovery | Owner-created Child, owner services with consumers, multiple episodes and general recovery expressions | Derive inverse definedness and a legal surviving execution from the actual source history, including the Equation (55) correspondence |
| R4 · Global lifecycle properties | Preservation, ordering, legal reordering, progress and applicable confluence | Connect all boundedness, component and scheduling premises to code or explicit environment contracts; retain original refutations |
| R5 · Review and delivery | A frozen, reproducible implementation and its complete audit trail | Close the numbered audit and the four integration obligations against their actual targets; complete verification, runtime, packaging and declared-platform installation checks |

R0 precedes R1. Once the representation is established, R2 and R3 can progress
alongside one another; R4 combines their results, and R5 audits the full chain.
Runtime cases and review evidence accumulate during each milestone.

## Current work and next steps

R1 now supplies a semantic contract for the spawning parent, every continuation
and dynamic child on the full stated carrier. The reified context identifies
actual values, code and retained inverse functions. `run_inspected` constructs
the source execution itself and connects those contracts to a nonempty runtime
case. See the [R1 review and reproduction guide](r1-semantics.md).

The original total-function context is not silently equated with strict failure.
Three explicit revisions record finite code representation, separate admission
and recovery observations, and strict function-field interpretation. Original
items 28, 47, 55, 56 and 57 retain their audit status.

R2 now connects actual publication payloads, lease-selected values, awaited
cleanup results and landed inverse/continuation decisions to production callers.
Native call contracts also preserve actual factory arguments/results, and one
verified container now owns all Rust/static cleanup queues, bulk retries and sealing.
Root setup and actual Child/group dispatch receipts participate in bound lifecycle
admission, failure, retry and release; Child requests and inverses are admitted
atomically. Native registration now resolves authoritative parent/realm ports,
stores the actual recipe, and directly invokes that `FnMut` after checking the
current setup action and recipe revision. Child retirement uses the identity
produced by real allocation. Its shared native slot permits one assignment in
the originating episode and closes pending allocation when its inverse runs first.
Native service values now join actual Begin/Finish/Unload: complete committed
imports, complete-value publication and drain-gated payload transfer are checked
in the production path. NativeHost now owns actual registration/host entries
and the lifecycle graph together, preserving their membership and resolved
interfaces through insertion, update, borrowing and removal. Shared native Child
requests and inverses are now constructed together, with verified slot synchronization
and persistent terminal agreement excluding allocation after cancellation. See [R2 execution contracts](r2-execution.md) for the proved scope and review path.
Effect requests now allocate their actual cleanup group atomically, and private poll
receipts bind actual iterator payloads/results to that group and current attempt.
Cancellation and nested acquisition read the actual stage state.
Execution now owns the actual work, native values, phase, runners and checkout
records. Managed publication, direct withdrawal and release compose these states;
actual Poll normalization is verified. R2 remains open for concrete plugin effect
laws, the complete production-state interpretation and whole-trace correspondence;
its exit criteria are unchanged.

R3 then expands in three work packages: owner-created Child, consumers of owner
publications, and repeated episodes/interior owner Unload. R4 follows with legal
trace reordering and dynamic-registry progress under the resulting semantics.
The [detailed technical roadmap](roadmap.md) retains the proof-specific obligations.

## Acceptance for each increment

Each increment identifies a paper obligation, closes a stated representation or
execution gap, and records the actual public caller. It supplies a nonempty
runtime case, the applicable proof and a targeted negative control where the
contract changes. Proof and execution records must refer to the same source.

Every premise needs a source: an established invariant, a checked plugin effect
contract, or an explicit environment obligation. Arbitrary JS callbacks and
external I/O do not inherit effect-correctness proofs from the native protocol.
Moving a missing core semantic obligation into an environment assumption does
not close that obligation.

Original refutations remain refuted. Completing the original audit and proving
an explicitly revised specification are distinct results. The existing
`check-paper-coverage.py --require-complete` gate continues to reject partial or
refuted original claims; this plan does not weaken or replace it.

## Maintaining the baseline

Edit `paper-refinement-plan.json` for allocation, review paths and milestone
criteria. Edit `paper-obligations.json` for original-paper evidence and scope.
Regenerate their views and run the normal development checks:

```sh
python3 scripts/check-paper-coverage.py --write
python3 scripts/check-paper-refinement.py --write
./scripts/check-development.sh --offline
```

The refinement-plan checker requires all 81 items exactly once, all four
integration obligations, an acyclic milestone graph and existing source symbols
with the stated roles. Its generated map reads claim statuses from the original
ledger. These are consistency checks; Verus checks the contracts, and reviewers
must still inspect semantic correspondence and the actual calling path.

The product/adoption milestones in the [adoption plan](adoption-plan.md) continue
independently. Independent users and maintainers provide adoption evidence;
maintainer-run clean installations do not establish external adoption.

The reversible-value production path now proves concrete operation/inverse laws,
all-carrier membership for finite programs, actual value-state interpretation and
whole program/source traces. It uses the normal Runtime cleanup owner, including
failure retention and retry. This does not close the complete host-state and
native/Node trace obligations. See the [case and review path](cases/reversible-values.md).

The shared production lifecycle owner now maintains a continuous ghost control history from empty to its actual state, classifying paper steps, internal steps and exact extensions. This closes the control-history link, while the joint R1 interpretation remains open.

The native Runtime now also uses one checked owner for actual registrations and
published slots, with a continuous joint control/publication history. Complete
Active publication, retention during Unloading and owner-local release are
invariants across the real entry points. Shared episodes, slot interiors,
function meanings and Node versions remain outside this joint observation;
R2 remains in progress. See [the review path](r2-execution.md#joint-native-registry-and-publication-history).

Begin provenance is now preserved through the production episode, publication and
release contracts. Captured imports retain their original provider slots across
withdrawal and retry, and mismatched work domains are rejected. The snapshot is
erased and does not retain extra runtime values. See [the contracts and remaining
shared-owner boundary](r2-execution.md#begin-provenance-through-publication-and-release).

The production owner registry now retains each Begin-issued setup/work identity
until successful Unload and checks every managed boundary against it. Delayed
root invocation revalidates the live episode immediately before the stored
callback runs. Continuous-history induction establishes the Begin origin and
retention of those owner records. Shared adapter locks, arbitrary function
semantics and the complete Node/native R1 interpretation remain open; see the
[R2 ownership contract](r2-execution.md#issued-episode-ownership-and-delayed-root-calls).
