# R3: recovery at a common production checkpoint

[简体中文](r3-common-recovery-cut.zh-CN.md) · [Child sources](r3-child-recovery.md) · [Value recovery](r3-interleaved-recovery.md)

Complete native intermediate publication/owner/pending observation recovery is now covered by [package 2](r3-observation-recovery.md). Related boundaries below describe this earlier entry point; ordinary-host migration and general legal deletion remain open.

A parent can unload before its retired Child is able to release. Recovery evidence
therefore needs to refer to one actual later checkpoint, not a collection of
unrelated terminal observations. The managed recovery path now combines restored
values, the original native Child obligations and settled forward registrations at
that checkpoint. **This is a scoped composition; R3 remains in progress.**

## What is established

`RegisteredReport::unload_recovers_with_children` uses the actual registered
function report, recorded execution, its own native Unload, the runtime's collected
Child sources and a real native `Snapshot`. It derives these results together:

| Projection at the common checkpoint | Result |
| --- | --- |
| Allocations touched by the registered invocation | Decoded scalar/typed values equal their actual Begin values |
| Every assigned native Child in the creator's original retained inverses | No episode owner or retained publication remains; if still registered, the Child is retired and Inactive |
| Cancelled or rejected unassigned requests | The retained persistent decision is unassigned; it cannot later become Assigned |
| Successful managed writes represented in this report | Their original forward positions are absent from the checkpoint's pending-registration map |

The checkpoint comes from the existing `NativeRuntime::publication_snapshot`
read. Its contract includes the Child ledger's source coverage. No caller supplies
the desired final values, an empty pending map or a fabricated Child state.
All new collections, source comparisons and traversals erase; this batch adds no
runtime history buffer, extra snapshot read or lock.

## Why a Child endpoint stays valid

The executable Kernel allocates plugin identities above all previously allocated
identities. Removal does not rewind this allocation bound. The registration and
Begin wrappers now export those facts through their real call chains.
`NativeRuntime` maintains `History::allocated_below` and `fresh_insertions` as
part of its invariant. Certified native snapshots retain that property.

`terminal_retained` proves that a retired Inactive Child without an owner or
publication stays terminal through later actual native transitions. Other plugins
can register, run and release; the Child may be separately removed. A later Insert
cannot reinterpret its old identity as a new plugin. This is derived from the
actual allocation history, rather than an assumption that the native suffix is
quiet. `Ledger::resolution_at_cut` locates the authentic birth, retirement and
Unload receipts in that complete history and carries their conclusions to the
shared checkpoint.

Cancellation has no birth or Unload to transport. Its persistent shared-slot
decision excludes later assignment independently of the native Journal position.
It is not represented as an invented native cancellation event.

## Values and pending registrations

The value part first invokes the existing source-based recovery theorem at the
episode's real Unload. `observe_later` decodes the same allocations at the later
checkpoint. It requires the actual Journal suffix to contain no further mutation
of those allocations. A post-restoration write invalidates this condition even
when it writes the same visible value. Unrelated values and native lifecycle
events may still change.

The scalar and typed interpreter paths now export that a same-Journal inverse
registration settles its exact forward position. `registered_pending_at_cut`
derives absence of those positions at the later checkpoint using the actual
registration receipts and the Journal's non-reappearance theorem. Other calls may
still have pending writes. This does not assert that the entire pending map is
empty or that every possible intermediate staging state has recovered.

The [observed-owner variant](r3-observed-recovery.md),
`unload_recovers_from_observed_owners`, now derives foreign restoration closure
from actual registered steps, terminal groups and covered dispatch histories.
Its executable observed entries maintain existing dispatch coverage across calls
and retries. The original entry above retains its explicit closure premise.

## Source conditions and remaining work

Child completion coverage remains explicit: `native_children_resolved` checks
every original native inverse across the recorded groups. Parent drain or parent
Unload does not imply it. The proof derives the terminal state at the common cut
from that source coverage. It does not schedule Child cleanup or assume fairness.

Value recovery retains its existing conditions: authentic complete relevant
observations, value continuity, matching successful foreign restorations and
unchanged value tails. The new endpoint must cover the real Unload and collected
Child sources from the same native member and Journal. It does not combine
independent Journals into an invented global clock.

Remaining R3 work includes deriving the required observation/closure coverage
through full host orchestration, general publication and pending-effect recovery
across intermediate cuts, ordinary-host migration, and construction of a legal
surviving execution after deleting the target episode, including owner-created
Children and consumers. The original paper audit outcomes and R3 exit criteria
remain unchanged. This batch contributes to the recovery correspondence around
Equations (55)/(56), Theorem 68 and Corollary 69; it does not prove the unrestricted
original claims.

## Review and validation

| Source | Review entry |
| --- | --- |
| [lifecycle_state/native/runtime/history/lifetime.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/history/lifetime.rs) | Actual allocation bounds, fresh insertions, terminal preservation and source indices |
| [lifecycle_state/native/runtime.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime.rs) | Invariant maintained by actual transitions; existing snapshot exports source coverage |
| [lifecycle_state/native/runtime/child_history/cut.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/child_history/cut.rs) | Each assigned Child's terminal state at the actual later checkpoint |
| [reversible_value/managed/interleaving/history/lifecycle/children/completion/cut.rs](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/children/completion/cut.rs) | All original native Child obligations use the same checkpoint |
| [reversible_value/managed/interleaving/history/lifecycle/recovery/cut/pending.rs](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/recovery/cut/pending.rs) | Actual forward registrations stay settled at that checkpoint |
| [reversible_value/managed/interleaving/history/lifecycle/recovery/cut.rs](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/recovery/cut.rs) | Value decoding and the composed `unload_recovers_with_children` theorem |

Validation results and commands are maintained in the [interleaved recovery
guide](r3-interleaved-recovery.md#review-and-validation). New mutation controls and
full integration acceptance remain pending; full negative regression/calibration
remain `not_run`.

At integrated acceptance, cover reused allocation IDs, removal followed by fresh
registration, omitted or future Child sources, a different native member or
Journal, parent Unload preceding Child release, value writes after restoration,
and registration that fails to settle its actual forward position. Include a
proof client with nonempty value and Child obligations; runtime rejection cases
alone do not validate the composed proof's source conditions.

The stronger [`unload_recovers_from_source_history`](r3-source-continuity.md) entry derives value continuity and outstanding-inverse membership from authenticated owned sources and actual trace guards before applying this common-cut theorem.
