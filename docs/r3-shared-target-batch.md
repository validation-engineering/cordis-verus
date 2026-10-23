# R3: shared objects and actual multi-call target execution

[简体中文](r3-shared-target-batch.zh-CN.md) · [Target invocation](r3-target-execution.md) · [Remaining R3 work](r3-remaining-work.md)

The opt-in replay path can now initialize shared target services, publish them
through actual native providers, and execute a finite sequence of retained root
functions. Calls using different service names for the same source object reuse
one target object. Returned reports and cleanup owners belong to the actual
target execution, including a failed call's successful prefix.

**This is a native target-execution building block. R3 remains in progress.**
It does not yet derive the entire surviving source schedule or prove that every
admitted source window must finish successfully on the target.

The [source-derived scalar landing](r3-scalar-landing.md) now checks an actual target input and proves that a still-admitted, unchanged landing produces the corresponding result and real queued inverse. This closes a primitive obligation; automatic input and interference-condition derivation across the batch remains open. The return-value law of `ScalarEffect` alone does not prove absence of shared-state effects during computation.


The opt-in [`run_checked_scalar` entry](native-operation-contracts.md#checked-source-continuity-and-actual-scalar-observations)
now checks source continuity before registration and actual scalar target inputs
before Finish or the next call. A clean return proves matching actual inputs,
results, branches and strict inverse states. A post-invocation mismatch preserves
the report and cleanup owner; it is not an atomic pre-write guard. The mixed
`run_controlled` path remains available with its existing contract.


The checked scalar path also verifies the actual committed provider and captured
slot revision against the bank. A clean return now establishes the allocation
map and cross-call aliases for the actual reports, as described in the
[selection contract](native-operation-contracts.md#actual-provider-and-allocation-selection).
Nonzero captured slot revisions are rejected; dynamic rebinding remains open.


## What executes

1. The real Journal allocator assigns an executable name to each allocation.
   A persistent issuer receipt binds that number to its qualified Journal/key
   address. A separate canonical Journal receipt prevents one allocation from
   receiving two names. Scalar handles and typed payload handles expose the
   same identity after cloning; typed identity survives retirement.
2. `run_replayable_root` captures each operand and identity from the actual
   inverse still in the returned owner's queue. It does not reread a possibly
   changed service. No inverse permission is duplicated.
3. `Bank::bind` looks up the qualified source allocation. First use creates a
   real target scalar/payload and a shared service slot. Later uses return the
   existing entry, including operands with nonzero scalar depth. A first scalar
   operand with outstanding depth is rejected: its earlier target operations
   have not been executed. Typed targets start their own head/revision history.
4. `batch::run` derives a chronological permutation from actual Call positions, checks the common source stream, and prepares the port bindings, registers real providers, performs
   their Begin and empty managed root, publishes the shared slots, and Finishes
   them. It then invokes each retained function through `Source::instantiate`
   and the existing registered root interpreter, followed by real Finish.
5. Every returned call has its actual action/work provenance, report and
   `RecordedExecution`; providers retain their reports and owners too. On a
   failure, the batch returns the completed prefix and the failed call's owner
   when one was created. It does not roll back, discard inverses or pretend an
   unfinished cleanup succeeded. Registration/Begin errors retain the created
   registration ID when applicable.

The executable entry is
[`reversible_value/managed/replay/batch.rs`](../crates/cordis-kernel/src/reversible_value/managed/replay/batch.rs).
Callers retain `Source` values from actual invocations, supply a target runtime,
source naming Journal and starting anchor/work numbers, then inspect `failure`,
`calls`, `providers` and `bank`. Successful calls can use the existing withdrawal,
cleanup, retry and release APIs. Anchor/work exhaustion is checked.

## Proven contracts and their limits

| Contract | Result |
| --- | --- |
| `AllocationIdentity::same` | Within a common certified naming namespace, two available executable names compare equal exactly when the qualified source allocation addresses are equal. Exhaustion returns no identity rather than reusing a number. |
| `Input::wf` and capture | The retained identity, operand, program counter and queue token refer to the same real source step and its retained inverse. |
| `Bank::bind` | Source addresses have unique entries; existing target entries remain unchanged; a successful result names the requested source allocation. First-use target initial values come from that actual operand. |
| `Batch::actual_prefix` | Returned calls are an ordered prefix of the automatically sorted retained functions; `order` maps them back to source indices. They are executed by the real target interpreter with authentic reports and retained inverses. All call completions belong to the bank's actual target Journal. |
| Successful batch return | Every supplied function has an actual successful invocation report; there is no fabricated successful target step. This is conditional on the real execution succeeding, not a source-to-target success theorem. |

The current constructors use one private process issuer. The proof interface
still requires a **common certified naming namespace** for the collected source
inputs (`supported_namespace`). Automatic discharge when assembling arbitrary
cross-Journal sources is still open. Numbers are not portable identifiers for
another process, persisted execution or an independently created issuer.

The issuer's authority maps, canonical allocation map, source steps and
correspondence evidence erase. Runtime cost includes one atomic issuance and
an allocation identity handle per Journal allocation. Replay capture additionally
retains actual operands and shared target handles; ordinary calls do not retain
the replay input list. Identity exhaustion does not disable ordinary operations,
but a batch cannot prepare an unnamed input.

## Current executable profile

The batch accepts finite root functions whose declared dependencies can be
initialized from captured successful-step operands. It explicitly rejects root
provisions, missing captured dependencies, incompatible operand kinds and a port
rebound to another source allocation. Different ports may share an object.

Calls run in **actual source Call order**, derived and checked by [the source planner](r3-source-schedule.md), with provider preparation before the calls.
This is not the full original Journal schedule. Existing target services or
external concurrent writes can change selection or cause actual invocation
failure. Returning an honest failure is useful operational behavior, but is not
a proof of the paper's surviving-execution existence claim.

The remaining proof work includes deriving the complete selected lifecycle schedule from actual
source commands/ownership, maintaining target-current-state correspondence and
proving primitive success, transporting dynamic bindings and owner publications,
and composing Child, departure, cleanup/retry and Unload. General target
allocation injectivity and the complete action/work/inverse correspondence also
need composition into that source-to-target simulation. These remain in R3-A/B;
Mixed/Fresh, Node and Equation (55) retain their existing R3-C/D obligations.

## Concentrated acceptance

The runtime cases in
[`reversible_value/managed/replay.rs`](../crates/cordis-kernel/tests/managed_replay.rs) cover:

- two real invocations, four service names and two shared scalar/typed objects;
- target scalar depth `0 → 1 → 2`, generated by actual operations;
- failed early cleanup, retained dependency/owner, later cleanup and successful
  retry restoring the initial scalar and typed value;
- a failed second invocation retaining both actual owners and its successful
  operation prefix;
- correction of reversed input order, rejection of mixed source streams, missing earlier operations and changed source port binding;
- distinct Journal allocations and stable typed identity after retirement.

These runtime and proof cases have a defined scope. Integrated development
results must be read from a source-matching [development record](development-report.json);
none of these checks alone establishes R3, full negative regression or release acceptance.
