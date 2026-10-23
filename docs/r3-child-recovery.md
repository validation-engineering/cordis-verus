# R3: native Child retirement and release

[简体中文](r3-child-recovery.zh-CN.md) · [Interleaved recovery](r3-interleaved-recovery.md) · [Milestones](paper-refinement-roadmap.md)

Complete native intermediate publication/owner/pending observation recovery is now covered by [package 2](r3-observation-recovery.md). Related boundaries below describe this earlier entry point; ordinary-host migration and general legal deletion remain open.

A successful Child cleanup request retires the Child. It does not establish that
the Child has released its own episode. The native recovery path now connects the
actual shared-slot decision to that Child's actual Unload, including its retained
publication, cleanup guard and episode identity. **R3 remains in progress.**

## What the running code establishes

`NativeRuntime::retire_shared_child_observed` calls the existing shared-slot
retirement operation. Its erased `Retirement` witness retains the persistent
slot decision and the native runtime's actual Journal receipt. It distinguishes:

| Actual observation | Established result |
| --- | --- |
| Pending request cancelled, or previously rejected request | This shared slot is unassigned and cannot later become Assigned. There is no Child episode to unload for this request. |
| Assigned Child with no outstanding episode | At this observation there is no episode owner or retained publication for that Child; a still-registered Child is Inactive and retired. |
| Assigned Child with an outstanding episode | Retirement preserves the exact episode owner and publication. Completion needs that episode's own successful release. |

`Retirement::belongs_to` checks the actual shared-slot source and creating parent
episode. `matches_unload` checks the native member and Journal, the exact captured
`EpisodeOwner` (action origin and work domain), the parent, and retirement before
Unload. The executable release path makes its actual native commit follow both
the retirement receipt and the sealed cleanup membership. It reuses the existing
Journal write lock; the retained receipts and comparisons erase.

`Unload::lifecycle_source` exposes the real native and paper lifecycle Unload
transition, with the actual pre/post projections. From these sources,
`unload_releases_assigned_episode` derives that:

- the Child is still registered, Inactive and retired;
- its episode owner and publication are absent from the native runtime;
- no other non-Inactive committed consumer relies on it at the Unload guard;
- the endpoint carries the actual cleanup source.

`from_release` connects this result to the exact successful return and its drained
cleanup groups. `released_child_cannot_begin` rules out Begin at that endpoint.
Registry removal remains a separate operation. Removing the runtime's publication
does not prove destruction of escaped `Arc` values or restoration of external I/O.

## Calling the executable entry

Ordinary Rust callers can use the integrated entry without supplying proof state:

```rust,ignore
// The host has already withdrawn the Child and driven its cleanup.
let result = runtime
    .retire_and_release_child(&child_handle, &mut child_execution)
    .into_release()
    .0;
```

The entry performs real retirement, checks that the supplied execution belongs
to the assigned Child's current episode, and attempts guarded release. A parent
execution, obsolete execution, live consumer or undrained cleanup is rejected.
Success carries the Child-specific release relation automatically. Failure
produces no Unload or drained-group witness and preserves the supplied execution
and publications; retirement may already have succeeded. This call does not
withdraw, poll, retry or wait for cleanup on the caller's behalf.

A cancelled/unassigned request returns `InvalidState` from this combined release
entry because there is no assigned episode to release. Use the retirement
observation when cancellation itself is the desired result. Repeated release is
rejected; it does not create another completion witness.

Verified callers can retain `Retirement` and use `release_retired_child` directly.
Its explicit source conditions require the same native member, Journal, captured
episode and actual parent. `ChildRelease` also exposes erased witness borrows for
proof clients; the ordinary runtime result keeps the existing release shape.

## Automatic source collection

The native runtime now owns an erased `Ledger`. The existing mutation entries
maintain its three append-only source sequences:

| Actual successful operation | Retained source |
| --- | --- |
| `register_shared_child` | A `Birth` with the persistent Assigned decision, the exact native Insert receipt and the creating parent's actual `EpisodeOwner` |
| `retire_shared_child_observed` (also used by ordinary retirement) | The real cancellation or assigned retirement observation |
| `release_managed_execution_following` (also used by ordinary managed release) | The episode's own actual Unload and cleanup source |

`Birth::retirement_agrees` uses the persistent shared-slot identity to connect
registration and retirement. Matching numeric plugin IDs is insufficient. The
birth also retains the parent's action ticket and work domain, so a later parent
episode cannot substitute for the creator. Every stored native receipt is covered
by the same native member's committed Journal prefix. Other native operations
preserve these sources; they cannot reset the history or import a future receipt.
The collections, indices and traversals erase: there is no new runtime history
buffer, payload clone or lock.

`Ledger::records` distinguishes unassigned cancellation, an assigned Child with
no outstanding episode at retirement, and retirement followed by that Child's own
Unload. The actual retirement entry derives the first two cases when their source
conditions hold. A successful `retire_and_release_child` derives the third when
the Child's birth was collected by this runtime. A blocked or failed release cannot
manufacture an Unload endpoint; already recorded endpoints remain available.
These are retained historical observations. The [common-cut composition](r3-common-recovery-cut.md)
now transports covered assigned endpoints to one actual later native checkpoint
using the executable allocator's freshness guarantee.

`RecordedExecution::native_children_resolved` checks completeness against **every
original native inverse** retained across all recorded groups, including groups
removed before the parent's final release. It checks the original shared slot and
creating episode; an assigned Child's birth must also match the exact parent action
and work domain. `native_child_endpoint` then extracts
the corresponding authentic sources and terminal facts; later ledger extension
preserves that evidence. This completeness predicate is not inferred from parent
drain or parent Unload. The supported source collector covers the shared-slot and
managed-release entries above; it does not certify arbitrary raw registration or
host paths that bypass them.

## Connection to the creating episode and paper

`RecordedExecution::owned_child_retirement` relates the retained inverse's actual
shared slot to the creating parent episode and Journal. It continues to use the
original action after that token leaves the live queue. `native_child_unassigned`
excludes late assignment after cancellation; `native_child_released` uses the
matching Child Unload to derive the terminal native state. A parent's successful
acknowledgement or Unload does not satisfy this endpoint relation.

These are source obligations for the recovery correspondence around Equations
(55)/(56), Theorem 68 and Corollary 69. They connect concrete retirement and Unload
rules to the production path; they do not establish the complete equations for
all production effects or change the original paper audit statuses.

| Review entry | Role |
| --- | --- |
| [lifecycle_state/registration/shared_child.rs](../crates/cordis-kernel/src/lifecycle_state/registration/shared_child.rs): `Decision`, `retain_decision`, `agrees` | Persistent evidence from the real shared slot, with terminal agreement |
| [lifecycle_state/native/runtime.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime.rs): `retire_shared_child_observed`, `release_managed_execution_following` | Actual retirement observation and causally ordered release |
| [lifecycle_state/native/runtime/child_recovery.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/child_recovery.rs): `Retirement`, `retire_and_release_child`, `release_retired_child` | Executable composition, exact endpoint relation and derived release facts |
| [lifecycle_state/native/runtime/episode.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/episode.rs): `lifecycle_source`, `current_unload` | Actual Unload transition and pre/post projections |
| [managed_lifecycle_children.rs](../crates/cordis-kernel/src/managed_lifecycle_children.rs): `owned_child_retirement`, `native_child_released`, `native_child_unassigned` | Relation to the creating episode's retained inverse |
| [lifecycle_state/native/runtime/child_history.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/child_history.rs): `Birth`, `Ledger`, `child_birth`, `covered` | Actual Insert/parent provenance, automatic collection and committed-prefix coverage |
| [lifecycle_state/native/runtime/child_history/completion.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/child_history/completion.rs): `records`, `settle_retirement`, `settle_release` | Source-derived cancellation, quiescent retirement or own-Unload completion |
| [managed_child_completion.rs](../crates/cordis-kernel/src/managed_child_completion.rs): `native_children_resolved`, `native_child_endpoint` | Completeness against retained original inverses and exact creating-episode identity |

## Evidence and remaining work

The [native runtime tests](../crates/cordis-kernel/tests/native_runtime.rs) exercise
a parent that unloads while its retired Child remains blocked by a consumer,
consumer cleanup failure and fresh retry, successful Child release and separate
Remove. They also cover substituting the parent execution, repeated release,
Begin at the retired endpoint, and cancellation before late request dispatch.
The current scoped verification results and reproduction commands are recorded
in [interleaved recovery](r3-interleaved-recovery.md#review-and-validation).
New mutation controls and full development acceptance remain pending; full
negative regression/calibration remain `not_run`.

Birth, retirement and managed Unload sources are now automatically collected.
The [common-cut theorem](r3-common-recovery-cut.md) combines covered Child endpoints,
restored invocation values and the invocation's settled registrations at one real
checkpoint. General publication/pending effects across intermediate cuts remain
open. Complete external observations, value-source
continuity, legal surviving executions and ordinary-host migration remain open.
In particular, parent release does not establish `native_children_resolved`.
No fairness, eventual cleanup or global termination is inferred.

At integrated acceptance, add mutation controls for omitted birth/retirement/
Unload sources, reset histories, substituted shared slots or parent action/work
domains, receipts outside the actual native prefix, and treating parent drain as
Child completion. These proof controls remain pending; the existing runtime cases
do not replace them.
