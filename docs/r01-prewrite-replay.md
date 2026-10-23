# R01: replay from authentic inputs and shared storage

[简体中文](r01-prewrite-replay.zh-CN.md) · [Fixed obligations](paper-mapping-inventory.md#r01) · [Operation contracts](native-operation-contracts.md)

The opt-in `closed::replay::Session` derives object mappings and historical inputs
from actual managed calls, then invokes the original native registration, Begin,
protected root interpreter, Finish and cleanup paths. Mixed scalar and typed
instructions share the same target objects across calls and after real cleanup.
The caller supplies no desired target heap, inverse word or head-number map.

**R01 remains open.** The data execution connection below is implemented; its
whole-function and complete resource-boundary dependencies must also close.
The fixed acceptance criteria and original paper audit have not been narrowed.

The current delivery priority is the separately scoped [provider/consumer/Child update case](cases/update-recovery.md). General R01 composition is deferred; this delivery does not change or close the obligations below.

## Closed values and the ordinary compatibility path

The guaranteed data path accepts `closed::Value`: an immutable finite graph of
primitive values, sequences, maps and explicit object references. References
include their authentic name and kind, not just a vector index. The checker
visits every stored node and every instruction constant, including skipped
branches. It also checks captured inputs against the explicit `objects::Table`.
No user equality function, callback or destructor participates in these checks.

A reference keeps its logical meaning while `objects::Projection` maps it to a
different physical allocation. The table includes unvisited and retired objects;
a foreign table with the same indices and kinds is rejected. Shared references
remain shared. The schema is fixed for the session; accepting a future value
checks that same schema rather than extending it implicitly.

Arbitrary `Arc<T>` remains available through the generic managed API. Equality
of its retained pointer does not prove equality of mutable interiors, hidden
handles, destructor behavior or external effects. The closed path rejects every
`ScalarEffect` callback instruction, including unvisited ones. Adding an admitted
primitive requires extending the checked instruction language, its actual
commit/inverse implementation and corresponding laws.

## Actual execution and failure behavior

| Connection | Actual implementation and guarantee |
| --- | --- |
| Objects and first inputs | [Bank](../crates/cordis-kernel/src/managed_replay_bank.rs) authenticates birth/operand records and constructs an injective physical allocation map. [Projection](../crates/cordis-kernel/src/closed_objects.rs) covers the complete declared table. Unvisited objects with unsupported inverse debt are rejected. |
| Mixed root and Child bodies | [Session](../crates/cordis-kernel/src/managed_replay_session.rs) acquires the original locks, checks retained source inputs and reserves revision space before running the [original interpreter](../crates/cordis-kernel/src/managed_function.rs). Successful reports establish scalar value/depth and typed value/head/depth correspondence. |
| History across calls | [Archive](../crates/cordis-kernel/src/managed_replay_archive.rs) retains historical checkpoints and monotonically extends head maps. Real cleanup can restore an earlier head while the anti-stale revision advances; a later call checks this state before proceeding. Retired payloads that a later body does not visit do not prevent that body from running. |
| Slots and aliases | [Operand slots](../crates/cordis-kernel/src/managed_replay_slots.rs) and [declaration slots](../crates/cordis-kernel/src/closed_slots.rs) distinguish slot identity from object identity. Aliases of one source slot share one target slot; independent slots selecting the same object stay independent. Replacements use real compare-and-swap and preserve historical version maps. |
| Publications | [Finalization](../crates/cordis-kernel/src/managed_replay_finalization.rs) binds post-root own services to the real successful Finish. Services belonging to one source provider share one target cleanup owner. Early and late provides retain their original phase; Finish retries retain the already installed prefix. |
| Plugin identity | [Fiber records](../crates/cordis-kernel/src/managed_replay_fibers.rs) bind source/target IDs to real call receipts. A repeated source plugin reuses its target registration and obtains a new Episode ticket. The closed wrapper checks the actual source parent against prior mapped calls; it rejects an unknown or different parent. |
| Cleanup and retries | The original native protocol retains dependencies, inverse owners and failed attempts. `Error::After` retains the real report and cleanup owner when post-root declaration synchronization fails. Completing or retrying Finish preserves the report correspondence. |

First observations are chosen in authentic call order, independently of the input
`Vec` order. Declared but unvisited slots are included. Contradictory observations
of the same slot in one declaration capture reject explicitly, as do unnamed
identities, stale target versions and unsupported source histories.

Normal returns release the held locks. The APIs retain owners after partial
execution; an error is not a rollback. Admission, capacity, source selection and
interference remain explicit failure domains. Locks and tickets provide safety
contracts, not fairness or eventual termination.

## Paper-facing function evidence

[`paper_contract`](../crates/cordis-kernel/src/closed_contract.rs) selects the
actual source program, target report, object projection and retained inverse
words. It does not accept replacement programs or an expected result.

- `functions` relates root/current calls at arbitrary paired test inputs. Bindings
  belong to the input context. Future typed heads are generated from the actual
  admission clocks, extending the retained historical maps.
- `inverses` relates the strict domains and results of the real scalar/typed
  inverse words, including missing objects and incorrect current states.
- `allocations` exports injectivity for the complete object projection.

These are a **strict, admission-aware revision**, not the original pure-table
Equation (54). The existing refutation of that unrestricted reading remains.
The function theorem interprets one invocation and its continuation; it must not
be described as the complete parent function including arbitrary host operations
performed after that invocation. In particular, the data inverse word does not
already contain the parent's separately enqueued native Child inverse.

## Remaining closure work

The [fixed dependency graph](paper-mapping-inventory.md#r01) remains authoritative.
The substantial remaining connections are:

1. Compose the complete native parent/Child control and cleanup word with the
   managed data function interpretation, including all-input admission and
   failure domains. A real Child runtime demonstration is not this theorem.
2. Close the resource boundary for the whole admitted component, including
   operations surrounding the protected call. The generic public owner still
   supports ordinary host actions; those do not acquire a closed-data proof by
   association. Source namespace prerequisites also need their verified producer
   at the public closed entry.
3. Finish the S01/S02 whole-paper interpretation audit and propagate the named
   domain/read/write revisions into the remaining recovery/reordering statements.
4. Run integration acceptance and the necessary designated negative controls on
   the final source. Scoped checks and runtime cases are separate evidence.

This does not claim Equation (55), arbitrary schedule recovery, Lemma 79,
termination, confluence, arbitrary Rust/JS plugin correctness or paper-wide
completion. Node.js is not required for this native path, and proofs erase from
ordinary Cargo builds.

## Reproduce

```sh
cargo test -p cordis-kernel --test closed_replay --locked --offline
cargo test -p cordis-kernel --test managed_replay --locked --offline
python3 -B scripts/check-profile-controls.py r01-exclusive
python3 -B scripts/record-development.py --offline
```

[The closed-data cases](../crates/cordis-kernel/tests/closed_replay.rs) cover mixed
calls, failure/retry/resume, source/target Child ownership, repeated Episodes,
early/late publication, multi-service providers, slot aliases and replacements,
retired references, foreign names and external interference. Older scalar and
typed batch helpers remain available with their narrower supported domains.
The last development record must be refreshed after the final source changes;
old totals are not evidence for the current tree. Full negative regression is
independent and remains `not_run` unless actually executed.
