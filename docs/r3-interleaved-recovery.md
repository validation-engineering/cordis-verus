# R3: foreign writes, blocked cleanup and recovery

[简体中文](r3-interleaved-recovery.zh-CN.md) · [Cleanup contracts](r3-cleanup-recovery.md) · [Production recovery](r3-production-recovery.md)

Complete native intermediate publication/owner/pending observation recovery is now covered by [package 2](r3-observation-recovery.md). Related boundaries below describe this earlier entry point; ordinary-host migration and general legal deletion remain open.

The production recovery proof now includes finite histories containing foreign
managed writes, failed cleanup attempts, foreign restoration and later successful
cleanup. It preserves the real strict inverse domains and permits restoration
to interleave across independent allocations. **R3 remains in progress**: the
result covers the invocation's touched values at a real native Unload under
explicit source conditions. The [common-cut theorem](r3-common-recovery-cut.md)
now combines these values with completed native Child endpoints and settled
forward registrations. General publication/pending recovery and legal lifecycle
execution deletion remain open.

## Evidence from running code

The history has three sources:

| Event | Actual evidence |
| --- | --- |
| Forward write | The captured scalar or typed inverse, including its actual input, output, allocation and forward Journal position |
| Managed cleanup | The real `dispatch_payload_cleanup` completion, with its selected inverse, before/after queues, locked read or scalar commit, and acknowledgement |
| Direct restoration | The scalar `restore_observed` receipt or typed `restore_observed` attempt, including failures |

Both ordinary `restore` methods delegate to `restore_observed`; they retain their
existing behavior. The additional return component is erased evidence for verified
clients. The typed path still distinguishes monotone read revision from reversible
semantic head. No additional runtime history buffer or payload clone is introduced.

The inverse identity includes the Journal, allocation, captured input/output and
forward position. A successful restore must correspond to an outstanding captured
inverse. The proof does not accept a replacement expected result supplied by a host.

## Why interleaving is permitted

Every supported managed scalar or typed write increases its semantic depth by one.
This is derived from the actual forward contract, including extensible scalar
effects; it is not an axiom about arbitrary callbacks.

`recovery_obligations` proves that an inverse enabled in a recoverable history is
the last outstanding inverse **on its allocation**. A later outstanding inverse
on the same allocation would require a strictly larger current depth. Therefore,
the enabled inverse may be removed across later inverses on other allocations.
Their exact domains and results commute because they update different addresses.
Global LIFO and caller-supplied commutation laws are not required.

The constructed recovery record evolves as follows:

1. A foreign forward write adds its actual inverse and updates the observed value.
2. A blocked restoration keeps both the outstanding record and the attempted value.
3. A successful restoration consumes its matching inverse and records its actual
   restored value, including when other allocations still have pending inverses.

This permits a same-value typed foreign write to block an older inverse: semantic
head/depth still changed. Its actual restoration can then enable a retry while
the monotone revision continues to advance.

## Registered Begin recovery

`RegisteredReport::interleaved_progress` starts from the actual function's retained
queue suffix and established Begin/return contract. `outstanding` constructs the
remaining inverses and `values` constructs the projected values from the emitted
evidence. Every finite prefix preserves recovery to the actual Begin values.
Once all relevant inverses are consumed, `interleaved_recovers_begin` proves the
constructed final values equal those Begin values.

The `linked` source condition checks:

- authentic forward/attempt/completion contracts;
- a common Journal and ordered real receipt prefixes/read cuts, starting at the
  actual registered return;
- each observed input on a tracked allocation agrees with the preceding value
  trajectory;
- each successful restoration names an inverse retained by that prefix.

It does **not** require all attempts to succeed, the inverse word to be defined
after each step, or a caller-provided final value. Definedness follows from the
actual initial queue and the preservation proof. Failed and repeated raw attempts
can be represented without consuming another inverse; queue retry identities and
old-reply rejection retain their existing production contracts.

The projection covers allocations touched by the registered invocation. Foreign
effects on other allocations remain in the authentic receipt history but do not
change this projection. The selected event evidence is not claimed to enumerate
every lifecycle event. Actual reads constrain its interpretation; an unrestricted
raw replacement, retirement or opaque callback is not silently treated as a
reversible managed forward.

## At the actual native Unload

`release_managed_execution_observed` returns an erased `Unload` witness only when
actual release succeeds. The ordinary release entry delegates to it. Its
constructor uses the native host's indexed history to identify the last actual
Unload commit and the owner immediately before it, including the action ticket
and work domain. The native record afterward contains neither that episode owner
nor its publication. A rejected release produces no witness.

`RegisteredReport::unload_recovers_begin` then relates the finite trajectory to
**one common Journal cut at that actual Unload**. It checks the same native host
and episode as the retained Begin, receipt prefixes, and the absence of changes
to each touched allocation between its last observed event and Unload. Allocations
with no subsequent event use the actual registered-return observation. Typed
values are decoded through the source history of the last real write or attempt,
so advancing revisions do not require fabricated values or stale histories.

The `settled` history condition checks that each initial captured inverse, and
each relevant foreign forward, has a later matching actual successful restore.
`drained` proves that this leaves no inverse outstanding. It uses the real depth
law to show that consuming an enabled inverse cannot leave a duplicate of that
inverse in a recoverable word. Failed attempts remain permitted throughout.
The caller does not assert the constructed inverse word is empty.

Under these source conditions, the values decoded at actual Unload equal the
values at actual Begin. The stronger release-based variant below derives the
local part of finite-history closure. If a foreign write occurs after the last
included restoration, the quiet-tail condition
does not hold. A reused plugin id with another generation/work domain, or a
checkpoint from a different native host, cannot substitute for this endpoint.

## From the actual release guard to successful restoration

The real release path now retains its cleanup membership receipt in `Unload`.
The native commit follows that receipt in the same Journal, using the existing
write lock. The witness identifies the exact sealed membership and episode;
cleanup membership identity is preserved through the complete release call chain. The
additional receipt and causal argument are erased, with no new runtime buffer,
clone or lock. Unattached or foreign-Journal executions are not assigned an
invented common cut.

The source proof follows three concrete transitions:

| Source fact | Derived result |
| --- | --- |
| A group is present at an actual inverse registration and absent in the sealed membership | A real `Remove` or `Seal` checked that exact queue drained; this includes dynamically created groups removed before final Unload |
| A registered slot was occupied, but the queue passed that drain check | A real non-failed `Complete` discharged that token before Unload; moving it out with `Pop` or leaving it failed is insufficient |
| That completion is covered by an authentic managed dispatch acknowledgement | The real scalar/typed restoration succeeded; a callback's `Drained` cannot substitute for it |

`RegisteredReport::unload_recovers_from_cleanup` applies those results to the
actual insertion receipt and inverse of each retained function step. `covered`
checks actual registration membership, receipt prefixes and matching emitted
acknowledgements for every consuming completion of the relevant queue/token.
It checks the captured inverse identity but does not require restoration success.
Success, local closure and recovery at the common Unload cut are conclusions.

This entry point takes complete acknowledgement coverage as a source condition.
The recorded-history entry point below derives that coverage for a continuously
maintained queue path; integration across the full production lifecycle remains
open. Raw `pop`/`complete` APIs support opaque callbacks and
cannot, merely by emptying a queue, certify a managed restoration. The separate
`foreign_settled` condition checks actual later restoration of relevant foreign
writes; native release does not cause or schedule those restorations. Publication,
Child effects, pending-registration semantics and legal execution deletion remain
separate composition work.

## Registration ownership from the running interpreter

`CleanupGroups::register_following` now borrows its actual membership capability
into the queue's existing Journal write epoch. The inverse insertion receipt
therefore records the live group ID, exact queue key and queue domain at the
insertion itself. This erased observation adds no runtime history buffer, clone
or lock. A detached queue keeps its separate, explicit boundary.

The scalar and typed producers propagate this fact through `Step::registered`
and `Report::registered`. The typed contract also binds its public token to the
token of its actual insertion receipt. The registered root/Child dispatcher
exports these facts for every retained effect, including a successful prefix
before failure and an empty invocation.

`before_seal` proves that an authentic insertion into this live membership
precedes the sealed membership used by actual Unload: a sealed group cannot
reopen. `unload_recovers_registered` then uses the production report's membership
postcondition in the value-recovery theorem. Neither the caller's numeric group
ID nor an unrelated later membership snapshot can supply this evidence.

The interpreter also exports `queued_sources`: each insertion names the exact
retained queue's Journal and key. This connects its registration evidence to the
recorded dispatcher history below.

## Constructing acknowledgement coverage from actual dispatch

`History::new` starts with the actual queue's retained slots. The executable
`Execution::dispatch_recorded` calls the existing production mixed dispatcher
and records its output in erased proof state. Failed managed attempts stay in
the log and retain their original inverse. `retry_recorded` calls the real retry
entry point, preserving slots and allocating the actual newer attempt ticket.
Rejected retries and empty or rejected dispatches preserve the recorded path.

For each recorded managed slot, the collector maintains a concrete
alternative: the exact original action remains, or an authentic successful
managed dispatch consumed that queue/token and inverse. Ordinary callbacks do
not supply this evidence. `History::frame` follows changes such as later
registration only when the original managed slots are preserved; `foreign`
records actual external writes or restores without silently consuming a local
slot. `History::extend` appends the actual newly registered slots to the same
obligations, preserving each earlier token and its consumption witness. The
field `initial` records each token's original action; the sequence can grow.
Recovery uses the preserved original function-return prefix rather than requiring
that no later registrations exist. All collected sequences and receipt maps
erase at runtime.

`unique_consumption` proves that an already consumed token cannot be consumed
again, including across retries and later registrations. `Receipt::compare`
uses persistent tracked witnesses to compare actual prefixes from the same
Journal without acquiring another lock. Together with the release guard, these
facts identify the collector's acknowledgement with the completion required
before actual Unload. An old reply, a duplicate reply or a callback `Drained`
cannot stand in for a missing managed restore.

`RegisteredReport::unload_recovers_from_history` therefore derives local
acknowledgement coverage from the actual registration report, the continuously
maintained collector and its matching drained terminal queue. It no longer
requires the caller to provide `cleanup_emitted` or local restoration success.
The resulting values at the actual Unload equal the invocation's Begin values
under the existing value-source, read-order, foreign-closure and quiet-tail
conditions.

The ordinary removal path now delegates to `remove_observed`, which returns the
exact removed queue only on success, with its drain guard established. Ordinary
native release already delegates to `release_managed_execution_observed`; its
`ReleaseObservation` now bundles the actual result, authentic Unload and erased
pre-release cleanup groups. Rejection supplies neither endpoint nor terminal
groups. `unload_recovers_from_release` consumes that same successful return, so
a caller does not assemble a terminal queue or assert its drain status. A group
removed earlier uses its `remove_observed` boundary with the later actual Unload.

## Keeping the history in the lifecycle owner

`RecordedExecution` owns the real `Execution`, its return-time baseline, one
tracked history per captured or subsequently allocated cleanup group, and the
actual terminal queues. Each group also retains its actual origin queue; adding
a group does not replace the original function-return baseline.
`NativeRuntime::run_recorded_root` runs the stored root/Child function through
`run_managed_root` and attaches this owner to its actual returned queues.
The wrapper exposes immutable inspection; it has no mutable core escape.

| Executable operation | Maintained evidence |
| --- | --- |
| `enqueue_effect` / `enqueue_native_effect` / `register` | Actual group allocation records its new origin queue; later registration appends a new token obligation without resetting earlier consumption evidence. |
| `take_group` / `take_child` / `complete_request` | The actual request moves through `WorkItem` and its synchronous or awaited receipt. Only the matching outstanding work identity is completed; queue histories are preserved. |
| `take_effect` / `put_effect` / `admit_scoped_effect` | Checkout ownership and the actual admitted group scope are preserved. Abandoning a runner still blocks removal/release. |
| `land_effect` / `cancel` | The real callback reply is checked against its group and poll serial. A returned inverse extends the obligations even after cancellation; `Pending`, errors and rejected replies cannot fabricate one. |
| `enqueue_owned_child` / `enqueue_native_child` | The request and inverse enter atomically. Native admission constructs the same shared allocation for the request, inverse and returned handle. This does not yet prove Child termination or Child-effect recovery. |
| `run_function` | The real interpreter's complete successful prefix—including a prefix before failure—extends the obligations, and each actual forward value event enters all retained group histories. Local writes follow the retained invocation or cleanup boundary; a real return checkpoint covers local write, registration and failure receipts. |
| `dispatch` | The real mixed dispatch result enters its queue's history. Authentic managed results also enter the other captured groups' histories as foreign observations. The actual Pop follows the retained recovery boundary; the actual acknowledgement becomes the next boundary, including on failure. |
| `retry` / `retry_native` | Single-queue or actual native action retry retains every inverse, queue identity and prior observation. Native retry gives a fresh lifecycle action and a strictly newer attempt for each failed queue. |
| `complete_result` / `complete_future` | Only an issued host action can receive a host confirmation. Retry payloads have a type that excludes managed inverses; a stale/duplicate reply or callback `Drained` cannot consume a managed obligation. The Future entry keeps its actual awaited output paired with the ticket. |
| `finish` / `withdraw` | The existing native publication or withdrawal runs against the owned Execution; cleanup histories remain matched to its actual queues. |
| `remove` / `retire_effect` | Successful early removal or checked-out runner retirement retains that exact drained queue; rejection leaves the owner unchanged. |
| `release` | Actual native Unload retains the pre-release drained queues alongside earlier removed queues; rejection creates neither a terminal queue nor an Unload witness. |

The invariant partitions every recorded group into a live queue or its retained
terminal observation. `unload_recovers_from_owner` borrows the stored history
and terminal queue directly. Callers of this path no longer carry a separate
collector or supply a drained snapshot to the recovery theorem. These histories,
map traversal and snapshots erase; runtime operations still use the existing
production implementations.

The ordinary Rust host has not been migrated to this owner. Work dispatch,
runner checkout/admission/landing, cancellation, Child admission and runner
retirement now have explicit invariant-preserving entry points; no `DerefMut`
or unchecked mutation bypass is provided. The [Child endpoint bridge](r3-child-recovery.md)
now relates the retained native inverse to its actual retirement and own Unload.
Actual shared-slot births, retirements and managed Unloads are now collected by
the native runtime. Completeness is checked against every original native inverse
of the creating execution. The [common-cut theorem](r3-common-recovery-cut.md) now
combines these endpoints with invocation values and settled registrations. Host
acknowledgement alone does not establish Child release or external I/O success.

Subsequent managed `run_function` calls automatically collect their actual
forward value observations and retain their inverses, without replacing the
original return-time baseline. The report supplies the real arguments, selected
continuations, failed prefix and registered sources. Generic registration or
opaque iterator output alone does not establish the forward semantic law of an
external effect. Complete external observation, foreign restoration closure
and quiet tails remain theorem conditions; `observe_foreign` remains the explicit
external-observation entry. Publishing values through `finish` does not yet prove
recovery of publication or dynamic Child effects. General pending-registration
composition remains open.

### Authentic boundaries between managed calls and cleanup

For an execution returned by `NativeRuntime::begin_managed_execution`,
`run_recorded_root` retains the authentic registered return receipt as its first
`recovery_boundary`. The same-Journal equality supplied by native Begin is checked in
the proof; a detached or foreign execution is not assigned an invented boundary.
Subsequent `run_function` delegates to the existing `run_function_following` with
a duplicate of that tracked receipt. Its actual local writes therefore follow
the preceding invocation or managed cleanup boundary.

At return, `Execution::observe_execution_following` takes one real Journal read
epoch, certifies the actual work and cleanup state, and includes this report's
same-Journal receipts. The resulting checkpoint becomes the next boundary. This
includes successful writes, inverse registrations and available failure receipts;
an empty invocation still carries its predecessor through. Admission rejection
preserves the entire owner. Lifecycle/work/effect operations preserve the boundary;
managed cleanup advances it using the actual acknowledgement below.

`Report::covered_by`, `after_call_receipts`, `after_call` and `extend_boundary`
compose these actual returns: later local writes follow prior local writes,
registrations and recorded failures. A forward event's read cut is at least the
preceding boundary length. The argument does not require a successful or nonempty
preceding invocation, and coverage can be carried through a finite series of
calls. Receipt witnesses and the retained field erase; the return observation
adds one real Journal read and no new Journal event or runtime history buffer.

The recorded dispatcher passes that same predecessor to the actual queue Pop
commit through `dispatch_recorded_following`. The scalar/typed restoration follows
this real issue receipt, including its locked read and failed attempts. The actual
cleanup acknowledgement becomes the next `recovery_boundary`. Retry preserves it;
the next dispatch or managed invocation therefore continues the chain. Detached
queues and restorations in another Journal retain their explicit domain boundary.

`Dispatch::follows_boundary` exports the acknowledgement order and, for local
restoration, the read cut and checkpoint prefix. `Report::before_cleanup` derives
that these follow every local receipt covered by the previous invocation return.
Together with `extend_boundary` and the existing call contracts, this composes
finite managed-call/cleanup sequences, including failures, empty calls and retries.
Cleanup reuses the existing Pop write epoch: its predecessor and retained
acknowledgement erase, with no additional cleanup lock or runtime history buffer.

This establishes the order of these owned managed operations. It does not collect
every external mutation, prove that a read has the expected value, or impose a
common clock on different Journals. Complete external observation, value continuity,
foreign restoration and quiet tails remain conditions of `linked` and the Unload
theorem.

### Native Child retirement and actual release

The actual `NativeRuntime::retire_shared_child` entry now exports the underlying
shared-slot decision and lifecycle transition. A pending allocation is cancelled;
an assigned live Child receives `Retire`; failure preserves its state. The
registered recipes, publications and episode owners remain present. The contract
never equates a successful retirement request with cleanup completion.

`retire_shared_child_observed` now retains a persistent slot decision and actual
native receipt. `retire_and_release_child` checks the actual episode and composes
retirement with its guarded release, making Unload follow both retirement and
cleanup seal. The resulting Child-specific endpoint proves owner/publication
removal and the consumer guard. Cancellation instead excludes later assignment.
The [Child recovery guide](r3-child-recovery.md) documents the executable entry,
source contracts and automatic birth/retirement/Unload collection. The collected
birth retains the actual parent's action and work domain. Completion queries use
the original inverse sources across all recorded groups; parent drain is not a
Child completion condition. The [common-cut composition](r3-common-recovery-cut.md) transports covered Child
endpoints through arbitrary native activity and combines them with restored values
and this invocation's settled forward registrations at one real checkpoint.
General publication/pending recovery across intermediate cuts remains open.

The [native runtime regression](../crates/cordis-kernel/tests/native_runtime.rs)
`child_retirement_acknowledgement_does_not_release_a_consumers_provider` runs the
following actual operations:

1. A parent creates a Child; the Child publishes a service and a consumer captures it.
2. The parent's native Child inverse requests retirement and is acknowledged.
   With no service dependency on its parent, the Child does not prevent the
   parent from unloading, but the Child remains active with its publication.
3. After Child retirement and withdrawal, new lookup cannot see the service. The consumer's committed
   dependency and value remain, and actual Child cleanup/release are rejected.
4. Consumer cleanup fails and retains those resources. After an actual fresh
   retry and successful consumer release, the Child can clean up and produce
   its own real Unload; registry removal is checked separately.

This tests the distinction needed by recovery composition. A parent acknowledgement
or parent Unload cannot substitute for the Child's `release_managed_execution_observed`
evidence. A legal surviving-execution constructor must account for the Child's
birth and the consumer's admission when deleting the creating episode. That
constructor and full Child/publication recovery are still open; this example
neither assumes Child termination nor proves general legal deletion.

## Foreign closure from actual execution owners

The [observed-owner recovery path](r3-observed-recovery.md) binds every returned
step to its original registered queue/token. Executable `run_function_observed`
and `dispatch_observed` append the actual forwards and managed attempts to both
owners, preserving existing observation coverage and same-Journal boundaries.
A foreign owner's retained terminal group and slot conservation then derive the
successful restoration; a supplied success list is unnecessary. The composed
`unload_recovers_from_observed_owners` uses these sources at the common native cut.
Complete coverage of relevant sources and the existing value-trajectory/Child
conditions remain explicit.

## Review and validation

- [managed_interleaving.rs](../crates/cordis-kernel/src/managed_interleaving.rs):
  source carriers, actual receipt/read conditions, initial retained queue and
  registered finite-history recovery.
- [managed_interleaving_completion.rs](../crates/cordis-kernel/src/managed_interleaving_completion.rs):
  actual later-restore coverage and derived exhaustion of the inverse record.
- [managed_release_path.rs](../crates/cordis-kernel/src/managed_release_path.rs):
  source coverage, derived local success and `unload_recovers_from_cleanup`.
- [managed_release_membership.rs](../crates/cordis-kernel/src/managed_release_membership.rs):
  actual insertion membership, the ordering before seal, and
  `unload_recovers_registered`.
- [managed_cleanup_history.rs](../crates/cordis-kernel/src/managed_cleanup_history.rs):
  the actual dispatch/retry recording entries and retained-slot conservation.
- [managed_lifecycle_history.rs](../crates/cordis-kernel/src/managed_lifecycle_history.rs):
  actual Execution ownership, continuous dispatch/retry histories, authentic
  recovery boundaries, cross-group observations, dynamic origins and retained removal boundaries.
- [cleanup_recovery.rs](../crates/cordis-kernel/src/cleanup_recovery.rs) and
  [payload_cleanup.rs](../crates/cordis-kernel/src/payload_cleanup.rs):
  actual Pop/restore/acknowledgement causality and same-Journal read boundaries.
- [managed_lifecycle_callbacks.rs](../crates/cordis-kernel/src/managed_lifecycle_callbacks.rs):
  restricted host retry payloads, synchronous/awaited acknowledgement and
  separation from managed inverse consumption.
- [managed_lifecycle_work.rs](../crates/cordis-kernel/src/managed_lifecycle_work.rs):
  actual request receipts, effect checkout/scope/landing and drained retirement.
- [managed_lifecycle_children.rs](../crates/cordis-kernel/src/managed_lifecycle_children.rs):
  atomic Child admission, retained inverse obligations and the creating-episode
  relation to actual cancellation or Child release.
- [lifecycle_state/native/runtime/child_recovery.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/child_recovery.rs) and
  [lifecycle_state/registration/shared_child.rs](../crates/cordis-kernel/src/lifecycle_state/registration/shared_child.rs): persistent slot
  decisions, actual retirement/Unload composition and the ordinary Rust entry.
- [lifecycle_state/native/runtime/child_history.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/child_history.rs),
  [lifecycle_state/native/runtime/child_history/completion.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/child_history/completion.rs)
  and [managed_child_completion.rs](../crates/cordis-kernel/src/managed_child_completion.rs):
  automatic birth/retirement/Unload sources, committed-prefix coverage and
  completeness against the creating execution's original native inverses.
- [managed_lifecycle_function.rs](../crates/cordis-kernel/src/managed_lifecycle_function.rs):
  actual subsequent managed calls, return checkpoints and call/cleanup receipt composition.
- [execution.rs](../crates/cordis-kernel/src/execution.rs):
  `observe_execution_following` certifies actual owner state and receipt inclusion in one read epoch.
- [managed_lifecycle_native.rs](../crates/cordis-kernel/src/managed_lifecycle_native.rs):
  real registered-root attachment, Finish, withdrawal, native retry and Unload.
- [managed_owned_release.rs](../crates/cordis-kernel/src/managed_owned_release.rs):
  recovery using the lifecycle owner's stored evidence.
- [managed_history_release.rs](../crates/cordis-kernel/src/managed_history_release.rs):
  derived acknowledgement coverage, `unload_recovers_from_history` and direct
  composition with the successful `ReleaseObservation`.
- [group_release_history.rs](../crates/cordis-kernel/src/group_release_history.rs)
  and [cleanup_release_history.rs](../crates/cordis-kernel/src/cleanup_release_history.rs):
  real removal/seal guards and the earlier token completion they require.
- [managed_interleaving_endpoint.rs](../crates/cordis-kernel/src/managed_interleaving_endpoint.rs):
  actual final-cut decoding, quiet tails and `unload_recovers_begin`.
- [lifecycle_state/native/runtime/episode.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/episode.rs)
  and [lifecycle_state/native/runtime.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime.rs): real
  successful release, indexed owner provenance and erased Unload evidence.
- [recovery_obligations.rs](../crates/cordis-kernel/src/recovery_obligations.rs):
  depth bounds, derived per-allocation ordering and inverse removal.
- [reversible_value.rs](../crates/cordis-kernel/src/reversible_value.rs) and
  [payload_inverse.rs](../crates/cordis-kernel/src/payload_inverse.rs): the real
  `restore_observed` entry points and forward source law.

The combined value-storage, cleanup, execution, work/effect/Child, host status,
lifecycle actions and native recovery scope, including allocation freshness and
the common-cut and observed-owner compositions, passed Verus verification: **1,455 verified, 0 errors**
(`is-verifying-entire-crate: false`). All-target, all-feature Clippy passed for
`cordis-kernel` and the `cordis-verus` host. Nine existing suites passed
**84 tests**: `managed_function`, `native_runtime`, `cleanup_groups`,
`cleanup_queue`, `execution`, `async_completion`, `effect_work`, `setup_work`
and `shared_child`. The mixed-alias regression covers actual root return,
Finish/Restart, dynamic effect groups, awaited work, subsequent managed calls
including a failed prefix followed by an empty call,
atomic Child admission, cancellation followed by inverse landing, rejected
undrained retirement, successful early retirement, synchronous/awaited host
confirmation, retained failure, rejected release, native retry with fresh
action/attempt tickets, successful Unload and repeated-release rejection. The new native Child case also
covers parent Unload while its retired Child remains blocked by a consumer,
consumer failure/retry, and separate Child Unload and Remove through the new
entry. It rejects parent-episode substitution, repeated release and Begin at the
retired endpoint. A second case cancels a pending request before late dispatch,
with no Child allocation or Unload.
The added two-owner case covers a failed call prefix, typed same-value
interference, rejected target release, actual foreign restoration/release and
fresh native retry. These runtime checks do not establish all source-coverage
and value-trajectory premises of the composed proof. Formatting, paper
inventory/refinement/review consistency and local documentation links also passed. These are scoped development checks, not whole
kernel, release or paper-wide acceptance.

Reproduce this scope with:

```sh
source scripts/toolchain-env.sh
./scripts/verify.sh --verify-module reversible_value \
  --verify-module cleanup_groups --verify-module cleanup_queue \
  --verify-module execution --verify-module lifecycle_state \
  --verify-module lifecycle_actions \
  --verify-module setup_work --verify-module effect_work \
  --verify-module setup_context --verify-module host_status \
  --num-threads 2 --triggers-mode silent --output-json --time
CARGO_INCREMENTAL=0 cargo clippy -p cordis-kernel -p cordis-verus \
  --all-targets --all-features --locked --offline -- -D warnings
CARGO_INCREMENTAL=0 cargo test -p cordis-kernel \
  --test managed_function --test native_runtime --test cleanup_groups \
  --test cleanup_queue --test execution --test async_completion \
  --test effect_work --test setup_work --test shared_child --locked --offline
```

At integrated acceptance, extend the existing foreign-write/retry regression
with retained raw attempt evidence and add negative controls for dropping a
foreign inverse, consuming a failed attempt, substituting a forward identity,
or bypassing the actual input observation. Cover multiple foreign writers,
same-value typed writes, aliases, independent allocations and repeated failures.
Add an actual Begin/return/failure/foreign-restore/retry/Unload proof client, with
negative controls for a different episode or native host, a post-restore write,
an omitted outstanding inverse and a substituted typed source history. Cover
retired dynamic groups, registration outside the actual membership, missing
consuming acknowledgements, changed inverse identity, callback `Drained`, and
unattached or foreign-Journal release sources. Also reject substituting the
typed token while keeping its insertion receipt, or observing a different group
capability during registration. For the collector, cover omitted managed
consumption, a changed queue/key/token/inverse, duplicate acknowledgements,
failed attempts followed by retry, later registrations, and separate foreign
events; a callback's `Drained` must not discharge an initial managed slot.
Rejected removal/release must yield no terminal evidence; early removal and
final release must retain their own exact pre-call queue boundaries. For the
recorded owner, cover dynamically added groups, registration after a consumed prefix, a failed
dispatch observed by another group, early removal followed by final Unload, rejected native retry,
and attempts to bypass owned histories or substitute their baseline. Keep native
retry action freshness distinct from each queue's attempt freshness. Reject
resetting the original prefix during extension, reusing a retired group identity,
forgetting a late managed inverse, bypassing the host-issued invariant, and
accepting a stale Future result or a managed inverse as a host retry payload.
Also reject a forged effect reply/group/poll serial, dropping an inverse returned
after cancellation, completing foreign/duplicate work, retiring an undrained or
abandoned runner, substituting a Child request's shared slot, and omitting the
successful prefix or a forward event of a later managed call. For invocation
boundaries, reject discarding the retained predecessor, substituting an unrelated
return receipt, skipping receipt certification at the real read lock, omitting a
failed-prefix receipt and assuming cross-Journal order. Include empty calls and
admission rejection between successful calls. Cleanup-order controls should reject
dropping the predecessor at Pop, replacing an acknowledgement, ignoring a failed
attempt boundary, or asserting same-Journal read order for a foreign allocation.
Child controls should reject replacing a Child Unload with retirement, its
parent's Unload or an unrelated episode, substituting the shared source/native
member/parent, omitting the retirement or cleanup-seal cause, fabricating completion
after rejection, or allowing assignment after cancellation. These controls remain
pending; runtime rejection cases do not replace proof mutation checks.
The [Child source collection checklist](r3-child-recovery.md#evidence-and-remaining-work)
adds omitted-source, parent-identity, prefix and completeness mutations.
New controls and full development acceptance remain pending; full negative
regression/calibration remain `not_run`.

## Remaining boundary

General publication/pending recovery and legal lifecycle execution deletion remain
open beyond the common-cut composition. Registration membership comes from actual
managed execution; complete
managed acknowledgement coverage is now constructed for the recorded queue path.
The recorded owner now maintains that collector through its supported lifecycle
operations, work/effect/Child admission and subsequent managed calls. Complete
ordinary-host integration and complete external-effect observations remain open.
Child birth/retirement/Unload sources are now automatically retained, with
completeness checked against the creating execution's original native inverses;
the scoped [common-cut theorem](r3-common-recovery-cut.md) now combines their
terminal native state, invocation values and settled forward positions. Full
publication/pending semantics across intermediate cuts remain open. Managed
invocation and cleanup boundaries now come from actual returns, Pop issues and
acknowledgements, with same-Journal scope. The Child bridge composes a real
retirement decision with that episode's own successful Unload; retirement alone
still preserves its publication and episode owner. Foreign closure can now be derived from covered recorded owners and their actual
terminal groups; arbitrary external histories still need independent closure
evidence. Local release does not force another owner to drain. Legal surviving
execution construction remains a separate part of general recovery. No scheduler fairness, eventual foreign
restoration or eventual retry is inferred. The original paper audit outcomes and
R3 exit criteria are unchanged.
