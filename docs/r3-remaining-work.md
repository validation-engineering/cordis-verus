# Remaining R3 acceptance work

The [whole-paper inventory](paper-mapping-inventory.md) now decomposes these unchanged acceptance packages: R3-A → R01/R02; R3-B → R03/R04; R3-C → R05/R06/R07; R3-D → R08/R09/D01/D02. It also makes the semantic, controlled-access and independence prerequisites explicit. The recovery equation and legal episode deletion have separate acceptance conditions.

[简体中文](r3-remaining-work.zh-CN.md) · [Milestones](paper-refinement-roadmap.md) · [Target execution](r3-target-execution.md)

**R3 is in progress. The remaining work includes executable composition and
proofs, not just tests.** This inventory keeps the milestone's existing exit
criteria: real histories must construct a legal surviving execution and defined
inverses, covering owner-created Child, actual consumers of owner publications,
repeated episodes and interior Unload, with the audited recovery expression
related to Equation (55). R1's interpretation and the original paper audit stay
unchanged. R4 global termination and confluence are separate milestones.

The [source-derived scalar landing](r3-scalar-landing.md) now checks an actual target input and proves that a still-admitted, unchanged landing produces the corresponding result and real queued inverse. This closes a primitive obligation; automatic input and interference-condition derivation across the batch remains open. The return-value law of `ScalarEffect` alone does not prove absence of shared-state effects during computation.

## Established building blocks

- Actual owner/cleanup histories supply forward creation, inverse registration,
  unique consumption, failed attempts, retries, Child completion and a common
  native recovery cut.
- Closed synchronous Mixed/Fresh profiles have executable deletion results.
  Production native histories automatically supply commands; their selected
  control trace runs through the real Kernel with compacted names/generations.
- A retained managed root can register and execute on a real target native host
  and use its actual cleanup/retry owner. The preserved function and genuine
  source operands survive source deregistration.
- Operand capture now reads the inverse still in its actual queue slot, including
  a failed invocation's successful prefix. Individual target resources can be
  seeded from these values. A scalar input with outstanding depth is rejected;
  typed seeds start a new head/revision history. The source instruction is
  defined at each supported seed with the corresponding result and branch.

- A [shared target batch](r3-shared-target-batch.md) now binds executable names
  to actual allocations, selects one initial operand per source object, publishes
  shared target slots and runs multiple real root calls. It retains reports and
  cleanup owners on failure. The formal contract requires a common naming
  namespace. [Real Call ordering, typed continuity and atomic native landing](r3-source-schedule.md) are now implemented; complete lifecycle scheduling and target-current-state simulation remain.

These are different layers. A legal ghost Journal and a real Kernel control
replay do not by themselves execute the surviving managed operations. Nor does
initializing independent objects preserve aliases or establish later inputs.

## Fixed remaining packages

| ID | Remaining deliverable | Acceptance condition | Dependency |
| --- | --- | --- | --- |
| **R3-A** | Complete native target execution | Retain executable allocation/reference identity; select initial operands per shared object; reconstruct publication payloads; schedule retained registration, Begin, calls, Finish, departure, cleanup/retry and Unload through the original executor. Generate target action/work/inverse maps from actual target returns. Prove target input correspondence and operation success, rather than assuming a successful target step. | Current source capture/control replay |
| **R3-B** | Ownership and general admitted interleavings | Derive the complete effect selection from production Episode ownership, including late producer obligations. Compose owner-created Child, consumers, repeated activation and interior Unload; preserve aliases and admitted slot/revision changes across calls. Obtain required read/restore conditions from actual producer histories. | R3-A plus existing Child/census contracts |
| **R3-C** | Remaining execution-profile transport | Connect episode-specific Mixed/Fresh selection and fixed-name code transport; discharge admitted asynchronous landing obligations; establish the separate Node protocol recovery path. Each supported path must produce its own source-to-target execution witness. Opaque callback bodies and external I/O retain their explicit contracts; acknowledgement alone is not completion. | R3-A/B contracts; profile work can then proceed independently |
| **R3-D** | One recovery theorem and joint acceptance | Compose actual surviving execution, inverse definedness and final observation equality into the audited Equation (55) recovery statement. Audit public premises and paper links, then run the integrated proofs, required runtime cases, strict selected negative controls and an independent reproduction. | R3-A/B/C |

R3-A requires particular care: Journal addresses remain erased proof values.
The shared-target batch now supplies executable names tied to those addresses;
the general scheduler must preserve that correspondence across its full window.
Matching service names or making a new object per instruction is not a valid
substitute. Later scalar inputs can have nonzero depth precisely because
earlier retained operations still own inverses. That depth must arise by
executing those operations in the target. Similarly, target typed heads and
anti-stale revisions belong to target storage, not copied source counters.

A concrete counterexample now shows that a verified scalar return law alone does not constrain hidden shared writes. Resolving that effect boundary is required before claiming general replay success. The two largest composition uncertainties are **R3-A's target-state simulation** and
**R3-B's automatic closure under sharing/interleaving**. If an allowed source
interaction cannot be replayed under the stated contract, record the obstacle
or counterexample and resolve the contract explicitly; do not turn target
success into a new caller precondition or silently narrow the milestone.

## Work estimate

The earlier 7–11 batch estimate is superseded by the fixed obligation inventory. The controlled-effect architecture has a first implementation, but complete target-state simulation and ownership composition remain substantive proof work. Estimate implementation and acceptance separately after the high-risk premises are resolved; proof counts and passing examples do not measure R3 completion.

A batch counts only when it closes an identified acceptance obligation. Additional
lemmas and passing examples are useful evidence but do not independently close
one of these packages. Historical five-package deliveries were sub-results;
they did not remove the milestone's general executable-recovery obligation.

## Current validation boundary and next scenarios

The operand-capture and shared-target batches have scoped proof/runtime checks.
Use the source-bound [development record](development-report.json) for integrated
check results and verify that its hashes match the current tree. Development
checks do not establish general recovery, full negative regression or release
acceptance. The milestone remains `in_progress` in the machine-readable plan.

The fixed-binding two-invocation and failure/retry scenarios now run. Next, consolidate:

- shared scalar/payload aliases across two invocations, with changed provider or
  slot binding and target input/result correspondence;
- provider publication consumed by a retained Child, repeated episodes and an
  interior owner Unload in one executable selected window;
- failure/retry, stale replies, failed prefixes and exhausted recording capacity;
- a negative implementation that duplicates an alias or skips a required target
  operation, rejected at the corresponding proof contract;
- each included Node/landing path, followed by a single source-bound acceptance
  record for the combined recovery theorem.

The first controlled-effect implementation closes the hidden scalar-callback boundary for accepted programs. It does not close complete target-state simulation, general ownership closure or the fixed R3-A/B/C/D acceptance criteria.
