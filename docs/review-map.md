# Ownership and review map

English · [简体中文](review-map.zh-CN.md) · [Plan](verification-plan.md) · [Generated evidence](cases/generated-lifecycle.md)

Start with the state an operation owns. The production function and its Verus
contract remain together. The tables classify responsibilities and review paths;
they do not declare every function in a directory to be a production caller.

The cleanup and handle audits below implement the
[structural work plan](verification-plan.md#remaining-structural-work).
It distinguishes actual state owners, checked transitions and ordinary-host
responsibilities; it is not a repository-wide mutation or proof-dependency audit.

## Five guarantees, five review paths

| Guarantee / paper basis | State owner and mutation entry | Real caller and observation | Evidence / boundary |
| --- | --- | --- | --- |
| Unresolved dependents protect their provider; definitions 53–54 and L-Unload | `Kernel` owns registered identities, phases and committed bindings. [`LifecycleState`](../crates/cordis-kernel/src/lifecycle_state/cleanup.rs) owns action receipts and `execute_cleanup`; managed release uses the same `cleanup_step`. | Shared Driver calls the dispatcher; Native `RecordedExecution::release` calls managed release. Observe target **and** committed IDs through failure and retry. | `failed_child_keeps_chain` in [`cleanup/update.rs`](../crates/cordis-kernel/src/lifecycle_state/cleanup/update.rs), strict dispatcher controls, generated histories. A parent relation alone is not a service dependency. |
| Failed restore retains the inverse and payload; witnessed effects with explicit R1-DOMAIN interpretation | [`Inverse::restore_following`](../crates/cordis-kernel/src/reversible_value.rs) owns the actual shared value/depth under its lock; [`CleanupQueue`](../crates/cordis-kernel/src/cleanup_queue.rs) owns occupied payload slots and restore journal. | Actual `RecordedExecution::dispatch`, real shared values and destructor-observed payload tests. | Inspect strict inverse-domain and payload-retention contracts together. A consumed ordinary `FnOnce` failure is not managed recovery. |
| Old/duplicate replies cannot finish a new attempt; implementation mechanism | [`ActionLedger`](../crates/cordis-kernel/src/action_ledger.rs), [`CleanupJournal`](../crates/cordis-kernel/src/cleanup_journal.rs), queue completion and retry. | Actual `ActionTicket` and `RestoreTicket`, refreshed attempt, unchanged rejected state, old replies against a new Episode. | Existing receipt tests plus generated failure/retry histories. No assumption that an arbitrary asynchronous callback eventually replies. |
| A Child inverse retires its own Child; definitions 52 and 54 | [`shared_child`](../crates/cordis-kernel/src/lifecycle_state/registration/shared_child.rs) atomically creates request/inverse ownership; Native registration associates the real identity. | Original returned `SharedChild`, actual request dispatch, parent Episode and explicit provider/consumer bindings. | Exact handle/registration checks, split-handle mutation and its contract rejection. Ownership and dependency remain distinct. |
| Supported updates recover after the cause is removed; scoped evidence toward theorems 68–70 | [`NativeRuntime`](../crates/cordis-kernel/src/lifecycle_state/native/runtime.rs) owns registration, publications and actual recorded execution; the owner retains cleanup state until release. | Real roots, Child requests, interfering writes, restored causes, explicit retry, another update and complete shutdown. | Existing fixed case plus generated admitted/adverse strata. This is not general recovery equivalence, confluence or global liveness. |

The [paper inventory](paper-mapping-inventory.md) remains authoritative for open
generality obligations. A test model checks observations; it never supplies the
production history or substitutes for a refinement proof.

## Cleanup ownership audit

Scope: the provider/consumer/one-Child update path, its failed cleanup and explicit
retry, plus the corresponding Node acknowledgement/release boundary. This review
follows executable calls and their contracts. The entries below name the selected
state and its mutation families; they do not enumerate every service, interface,
configuration or general replay operation elsewhere in those owners.

| Authoritative state | Mutation entries and actual caller | Contract or boundary to preserve |
| --- | --- | --- |
| [`Kernel`](../crates/cordis-kernel/src/lib.rs): `nodes`, `declarations`, `links` | Construction/registration and provision/dependency changes establish identities; `begin` captures committed bindings; `leave`, `retire`, `begin_cleanup`, `finish_cleanup`, `remove` and compaction update control/storage through their checked APIs. [`LifecycleState`](../crates/cordis-kernel/src/lifecycle_state.rs) owns the kernel and records control transitions. | `resource_safe`, `ordering`, `cleanup_enabled`, `bindings_except` and the attached refinement step. A changed target does not replace the running episode's committed provider. Compaction preserves observations; retirement and removal differ. |
| [`LifecycleActions`](../crates/cordis-kernel/src/lifecycle_actions.rs): `ledger`, `cleanups`; [`ActionLedger`](../crates/cordis-kernel/src/action_ledger.rs): `domain`, `next`, `entries` | `begin`/cleanup request issue tickets; `complete_setup`/`complete_cleanup` consume them; `retry_cleanup` replaces a failed attempt; finish removes its cleanup record. The ledger's only post-construction mutators are `issue` and `complete`. | `wf`, `cleanup_reply_enabled`, `history_preserved`, `eligible`, `finish_enabled`. One accepted report applies to its exact domain/action/owner/generation/kind. Error paths retain state. `execute_cleanup` composes these contracts; it is not a second store. |
| [`CleanupJournal`](../crates/cordis-kernel/src/cleanup_journal.rs): `stages`, `domain`, `next`, `current`, `failed` | Scope/iterator construction; register/land/admit/end/cancel; `begin_restore`, `complete`, `retry`. Calls come from the queue, not an independent host ticket counter. | A `RestoreTicket` identifies one inverse attempt. Failed completion keeps the selected token; retry advances the attempt; stale/duplicate replies cannot consume the current attempt. This is distinct from the whole-episode `ActionTicket`. |
| [`CleanupQueue`](../crates/cordis-kernel/src/cleanup_queue.rs): `journal`, `payloads`, `in_flight`, `joint` | Registration/landing populate slots; attachment joins the execution journal; pop/dispatch checks out one payload; complete/restore returns or consumes it; retry retains slots. `*_following` variants additionally connect actual journal causes. | `wf`, `completion_enabled`, `same`, `retry_enabled` and the completion contracts tie the selected token to a real slot. [`complete_future`/`complete_failure`](../crates/cordis-kernel/src/cleanup_queue/completion.rs) return rejected payloads. Host acknowledgements cannot substitute for a managed inverse. |
| Managed value and retained inverse | [`Inverse::restore_following`](../crates/cordis-kernel/src/reversible_value.rs) checks the actual value/depth while holding its lock. [`payload::Inverse`](../crates/cordis-kernel/src/reversible_value/payload/restoration.rs) checks its retained payload version; the payload dispatcher reinserts failure. | Scalar failure returns the same inverse. Payload failure retains the version/inverse needed for retry. Shared-value mutation and publication-slot replacement are separate operations; arbitrary `Arc<T>` interiors remain outside this guarantee. |
| [`SharedChild`](../crates/cordis-kernel/src/lifecycle_state/registration/shared_child.rs): shared `inner` cell, immutable `origin` and retained execution Journal | `enqueue_native_child` creates the request and inverse together. `register_shared_child` assigns the real identity under the same lock; `reject`/`retire_shared_child` settle or retire that same slot. The host dispatches the returned handle. | Request/inverse identity, parent generation and before/after `ChildTransition` agree. A pending cancellation prevents later assignment. A parent/Child ownership relation does not introduce a service dependency. |
| Native episode, recorded execution and poll control | [`NativeRuntime`](../crates/cordis-kernel/src/lifecycle_state/native/runtime.rs) owns `host`, `services`, `owners` and the connected histories. [`RecordedExecution`](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle.rs) owns actual work/cleanup state and its history witnesses. [`PollControl`](../crates/cordis-kernel/src/poll_control.rs) owns episode/work identity, failure and restart state. Controlled begin/retry/release and failure recording are the mutation entries on this path. | `owns_execution`, `matches`, idle work and drained queues are checked at the actual API. The factory establishes `bound`; the Driver checks the retained Native allocation before using a control, as audited below. Other execution/representation premises remain separate. Retry clears failure through the checked transition. Release removes the matching owner/publications only after guarded unload, returning values to be dropped by the host. |
| Node cleanup state and retained publications | [`NodeRuntime`](../crates/cordis-kernel/src/node_runtime.rs) owns `control`, `store`, `admissions`, `episodes`, `restoring` and released handles. `begin`, `cleanup_with_error`, episode commands and release update the episode; [`resources`](../crates/cordis-kernel/src/node_runtime/resources.rs) derives/updates retained manifests; handle draining transfers released values to the adapter. | `wf` and `history::operation` connect these observations. `cleanup_allowed` rejects raw `Release`; resource-aware `release`/`release_reservation` checks actual admissions/leases/publications. `cleanup_failed` and diagnostics are checked host-state observations, not another release authority. JS disposal success remains a host report. |
| Ordinary Rust callback attempt | [`RunningCleanup`](../crates/cordis/src/runtime/cleanup/attempt.rs) privately owns the ticket, actual Future and retry factory. `start` and `poll` produce an opaque `CleanupCompletion`; `CleanupCompletion::acknowledge` consumes it through the existing verified completion APIs. [`Runtime`](../crates/cordis/src/runtime/cleanup.rs) and [`StaticCleanupFuture`](../crates/cordis/src/runtime/static_host.rs) store/remove the pending attempt. | Pending retains both Future and factory. A ready result carries its own factory, without separate caller-selected pairing. Callers acknowledge under the Episode lock, then drop rejected/discarded payloads and the completed Future outside it. Rust privacy and runtime regressions support this wrapper; they are not a Verus proof of callback effects or scheduler progress. |

### Call and proof dependencies

| Review route | Required code and proof support | Premise source / limit |
| --- | --- | --- |
| Host callback → attempt → `RecordedExecution::complete_future` / `complete_failure` → `Execution` → queue → restore journal | [`async_completion`](../crates/cordis-kernel/src/async_completion.rs), [`poll_result`](../crates/cordis-kernel/src/poll_result.rs), recorded [`callbacks`](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/callbacks.rs) / [`host`](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/host.rs), queue completion and journal contracts | The actual awaited result remains paired with the captured ticket. The host still polls/catches panics and chooses its failure policy. Ordinary Runtime uses `DrainConsumed`; static host uses `RetainFailure`; a retryable failure remains blocked under both. `Drained` is not successful restoration. |
| Native poll/retry/release → shared `NativeDriver` → recorded controlled APIs → `NativeRuntime` / `PollControl` → `NativeHost` → `LifecycleState` | Recorded [`native`](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/native.rs), [`native/managed`](../crates/cordis-kernel/src/lifecycle_state/native/managed.rs), [`services`](../crates/cordis-kernel/src/lifecycle_state/services.rs), [`execution`](../crates/cordis-kernel/src/lifecycle_state/execution.rs), cleanup groups and shared action/control contracts | Real owner identity, idle work and drained queues are checked. The release outcome comes from those queues. The native history/Child receipt code is a required bridge to the actual unload, not disposable research because it is ghost code. |
| Node facade/driver → `NodeRuntime::complete` / resource release → shared cleanup/control and publication store | [`NodeDriver`](../crates/cordis-driver/src/node.rs), [`node_runtime::history`](../crates/cordis-kernel/src/node_runtime/history.rs), [`Admission`](../crates/cordis-kernel/src/availability/admission.rs), [`PublicationStore`](../crates/cordis-kernel/src/publication/values.rs), [`resource release`](../crates/cordis-kernel/src/lifecycle_actions/resources.rs) | The verified state owner checks its represented associations. N-API handle association, JS object internals and external cleanup truth retain their host boundary; a report alone cannot bypass publication/lease release guards. |
| Shared cleanup execution → finite-history guarantees → paper transition | [`cleanup_step`](../crates/cordis-kernel/src/lifecycle_state/cleanup.rs), `failed_prefix_retains_dependencies`, `consumed_ticket_never_returns`, `release_has_accepted_report`; then `LifecycleActions`, `ActionLedger`, `Kernel::ordering`, [`refinement`](../crates/cordis-kernel/src/refinement.rs) and the required invariant/history lemmas | Definitions 52–54 and L-Unload motivate ownership, committed dependency protection and unload. Ticket freshness is an implementation mechanism. These finite-history safety statements do not supply general recovery, fair scheduling or termination. |

These are reviewed dependency routes for the selected guarantees, not a generated
transitive symbol graph for the whole crate. Keep the required history/refinement
support when reorganizing sources; classify other general proof branches only
after checking their callers and claims. Runtime/build dependencies are different:
the Rust library uses `cordis-driver` and `cordis-kernel`; Node/N-API is an optional
adapter, and erased history/lemma code does not require Node at runtime.

### One receipt gate for release

[`lifecycle_actions/finish.rs`](../crates/cordis-kernel/src/lifecycle_actions/finish.rs)
owns receipt selection, lifecycle/reservation finish and final record removal.
The public methods remain on `LifecycleActions`; their preconditions, results and
frame guarantees are unchanged. The private `finish_index` replaces three copies
of the generation/outcome/mode check. It returns an index consumed within the same
call; the public resource preflight returns a generation, not a release capability.

The complete write inventory for this owner's `cleanups` table is:

| Entry | Mutation and required support |
| --- | --- |
| `new` → `issue` through Begin or cleanup request | Initialize the empty table; append a Pending cleanup record after `ActionLedger::issue`. Capacity preflight and `wf` establish unique owners, fresh action identity and its pending ledger entry. Setup actions do not append a cleanup record. |
| `complete_cleanup` | Require the exact pending ticket, consume its ledger entry, then replace the record with the reported outcome. `cleanup_reply_enabled`, ledger completion and `completion_frame` preserve other owners and the history bounds. |
| `retry_cleanup` | Require a Failed record in the current restoring/reservation generation, issue a fresh ticket and replace that one record with Pending. `retry_enabled`, ledger uniqueness and the frame proof retain other records. |
| `remove_cleanup`, private to the finish module | Remove the acknowledged record only after `finish_index` accepts it; ordinary finish first calls `Kernel::finish_cleanup`. Its proof preserves `wf`, `history_preserved` and `no_new_release`. No independent host receipt cache participates. |

Read-only selection uses `cleanup_index`, the record-table invariant and actual
Kernel generation/phase observations to establish `finish_enabled` or
`reservation_finish_enabled`. Normal finish retains the `Kernel::finish_cleanup`
→ `refinement::Rule::Unload` dependency. Reservation finish leaves the Kernel
unchanged. Resource release keeps its separate
[`PublicationRegistry::cleanup_batch`](../crates/cordis-kernel/src/publication/cleanup.rs)
validation before commitment release, including rejection with the entire prior
registry/control/receipt state retained. The resource preflight is repeated at
commit; an earlier read cannot be reused as authority after state changes.

`None`/Failed reports, mismatched generations and the wrong release mode still
return `InvalidState`. Succeeded and Drained retain their existing distinct host
meanings. Callback truth, queue restoration and dependency ordering remain their
own obligations; this consolidation does not prove them from a report.

The ordinary host's [`record_cleanup_report`](../crates/cordis/src/runtime/cleanup.rs)
handles both synchronous Child results and paired callback completions after
acknowledgement leaves the Episode lock. It drops discarded factories before
recording errors and only marks Failed as blocking. The two acknowledgement APIs,
rejected-payload handling, Future lifetime and static-host policy remain distinct.

Existing cleanup-outcome/resource, retry, static-host and update-recovery tests
cover the preserved behavior. Selected controls reject accepting Failed reports,
ignoring the generation, bypassing the receipt and committing before resource
validation. Fresh positive checks, whole-mutant compilation and the named contract
failures remain required; this is separate from the complete negative suite.

### Execution ownership and queue writes

[`Episode`](../crates/cordis/src/runtime/episode.rs) directly owns its
`RecordedExecution`. Setup, root, Child, service and cleanup operations use that
same execution, after `SharedEpisode::checked_lock` validates its association.
There is no separate `Cleanups` owner or host-side receipt cache. The ordinary
`register_cleanup` helper only asserts the existing live-group admission result;
it neither decides eligibility nor stores another copy of the payload.

The concrete writes below complete the selected queue/receipt inventory. They
are not an inventory of every operation supported by `RecordedExecution`.

| Owned fields | Construction and all subsequent write entries | Required invariant / use |
| --- | --- | --- |
| `CleanupQueue.payloads`, `in_flight` | `scope`/`iterator`; `register_following`, `land`, `pop_following`, `complete_following`. `register`, `pop`, `complete` delegate; completion, dispatch and landing adapters call these entries. | `local_wf` couples occupied slots, waiting tokens and the selected issued attempt. `same` frames rejected operations; `retry` does not change payload slots. |
| `CleanupQueue.journal` | Construction; `register_following`/`land`, `pop_following`, `complete_following`, `retry`, `admit`/`end`/`cancel` call the owned journal. | [`CleanupJournal`](../crates/cordis-kernel/src/cleanup_journal.rs) owns stage state and the attempt counter. `begin_restore`/`retry` allocate attempts; `complete` retains a failed selection. `current` hides failed receipts; `receipt` still exposes the retained selection. They are not interchangeable. |
| `CleanupQueue.joint` | Starts absent; `attach_execution` allocates the member once. `commit`/`commit_following` update that member's history after a real queue change. | `cleanup_step`, `traces` and `wf` connect observed occupancy with the same Journal. `issue_receipt`, `latest_receipt` and `drained_observation` support the production history; they are not a second mutable authority. |
| Callback ticket, Future and retry factory | [`RunningCleanup::start`/`poll`](../crates/cordis/src/runtime/cleanup/attempt.rs) construct the attempt and paired completion; consuming `CleanupCompletion::acknowledge` forwards that pair to the owned execution. | The host retains Pending work, acknowledges under the Episode lock and drops rejected/discarded payloads and completed Futures outside it. Synchronous Child reports have a separate entry with no retry-factory argument. |

[`reply_pending`](../crates/cordis-kernel/src/cleanup_queue.rs) is the single
executable receipt predicate for direct queue completion, callback results,
Future results, failure reports and managed value restoration. Its exact contract
requires an issued, selected, non-failed matching ticket. The managed path checks
it **before** restoring the value. `complete_following` additionally checks that
only a Failed outcome may retain a payload; `completion_condition` exposes the
combined condition to proof callers. Neither the public completion contracts nor
this retention rule was weakened when the duplicate receipt branch was removed.

This reduces the review surface for a receipt-rule change to one predicate and
its adapters, instead of parallel guards. Action tickets and inverse tickets,
`DrainConsumed` and `RetainFailure`, and checked payload restoration versus host
callbacks keep their distinct contracts. Existing `retry_cleanup`, `static_host`
and `update_recovery` regressions cover failure/retry, panic handling, reentrant
factory destruction and provider/consumer/Child execution. The final-source
[acceptance gate](cases/generated-lifecycle.md) also pairs actual behavior with
strict proof rejection. This does not prove callback effects or fair scheduling.

## Episode and handle ownership

The ordinary host now keeps `Episode`, immutable `SharedEpisode` metadata and
its checked lock in [`runtime/episode.rs`](../crates/cordis/src/runtime/episode.rs).
[`runtime/effect_handle.rs`](../crates/cordis/src/runtime/effect_handle.rs) owns
handle construction, status access and all waiter/notification fields. The public
`EffectHandle`, `EffectJoin` and `AsyncSetup::effect` paths remain unchanged.

This audit covers the association and handle fields below. It does not claim that
all mutable Episode fields have been encapsulated. The next section separately
audits Child ownership and the external host-report boundary.

| State / owner | Mutation entries for this slice | Contract or host boundary |
| --- | --- | --- |
| `SharedEpisode`: association, generation, context, service metadata, anchor and Episode mutex | `native` derives metadata from the execution actually stored; `external` derives association/generation from its checked static values and checks that association. Fields are private, with read-only metadata accessors. | `Association::native` / `matches` and `static_values::Values::from_definition` supply the identity contracts. Every `checked_lock` tests the original execution association. Static realms/anchor still come from the embedding host. |
| `Episode`: values, recorded cleanup execution and host bookkeeping | Native `Runtime::start` and static `begin_inner` assemble it; setup, poll, cleanup and static-host code mutate it only through the checked guard after publication. `withdraw`, `seal_external` and `provide` retain their checked protocol calls. | This mutable guard remains broad for values and cleanup dispatch. Child retention and private notification/capability state are audited below; moving or encapsulating them adds no kernel proof. |
| `EffectStatus`: checked owner and weak Episode allocation | `AsyncSetup::effect` allocates/adopts the real group status before the handle can escape; `EffectHandle::service` creates the service status from the locked execution. No production rebind entry exists. | The weak reference avoids an Episode/group/handle ownership cycle. `matches_episode` checks both allocation identity and the kernel-issued execution association before polling or cancellation. `HostStatus` remains the semantic authority. |
| Effect cancellation, initialization and completion | `cancel`, `mark_cancelled` and `poll_driver` request cancellation. `initialize_effect` and `retire_effect` call the existing Execution gates using the actual group/runner. | Cancellation does not complete work. `initialize_effect_status` requires settled work; `retire_observed_effect` checks the actual queue and records its removal before completion. The selected cleanup policy still determines retirement. |
| Service reports and status error payloads | `assign_service_child`, `initialize_service`, `fail_service_cleanup`, `finish_service`; `record_error` and `record_unique_error` append actual errors. | These use the existing `HostStatus` contracts, including one Child assignment and retained first terminal error. A service report cannot finish an effect; terminal failure is not successful removal. Whether external cleanup really succeeded remains a host premise. |
| Join IDs and waiter map | `EffectJoin::poll` allocates/registers/replaces or removes a waiter; its `Drop` unregisters. Effect initialization/retirement and service assignment/initialization/terminal/removal drain waiters at their existing notification points. | Each join retains its own ID. Initialization wakeup does not complete a join. The external Child wait-edge guard is unchanged. Waker clone, replacement destruction and invocation occur outside the status lock. |
| Handle driver waker and notify callback | Construction captures the optional callback; `poll_driver` replaces the driver. `cancel`, `replace_service_value` and `refresh_driver` take the driver and clone the callback; `finish_service` takes both for disposal. | Private `Notification` moves them out before invoking anything. Service value replacement remains atomic with the cancellation/finished check; rejected/previous payloads are dropped before notification and outside the lock. |

The compound lock order remains Episode → status → checked cell → Journal.
Handle-only operations never acquire Episode while holding status. Service
callbacks, wakers and returned payload destruction run after unlocking. Native
service initialization retains its existing no-join-wakeup policy; static service
initialization wakes joiners. Driver-owned cancellation still avoids notifying the
already-running driver. These policies are not merged merely because both hosts
use the same status owner.

The proof route is `host_context` / `static_values` for association, then
[`host_status`](../crates/cordis-kernel/src/host_status.rs), the Execution
[`status gates`](../crates/cordis-kernel/src/host_status.rs), recorded
[`host transitions`](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/host.rs)
and [`joint/host`](../crates/cordis-kernel/src/reversible_value/joint/host.rs).
It preserves the Definitions 58/63 observation and cleanup connections described
in [R2 execution](r2-execution.md#actual-shared-handle-status-in-the-execution-trajectory).
Rust privacy narrows the adapter's mutation surface; it is not a new Verus proof
of ordinary mutexes, arbitrary callbacks, fair scheduling or whole-paper recovery.

A change to handle wakeup ownership now has one implementation location, instead
of direct field edits across setup, services, polling and cleanup. Callers retain
their explicit scheduling and failure policies. Existing identity-corruption
checks moved beside the private storage rather than adding production escape
hatches. [`runtime_waiters`](../crates/cordis/tests/runtime_waiters.rs),
[`static_host_join`](../crates/cordis/tests/static_host_join.rs) and
[`static_host`](../crates/cordis/tests/static_host.rs) cover cancellation, waiter
replacement/re-registration, reentrant destruction, external wait edges and
notification reentry. No new test framework or runtime dependency was introduced.

## Child request and completion ownership

[`runtime/child.rs`](../crates/cordis/src/runtime/child.rs) owns Child admission,
the original handle and pending request payloads, and native request application.
[`child/external.rs`](../crates/cordis/src/runtime/child/external.rs) owns the
external allocation report, retirement/removal state and completion notifications.
`ChildHandle` and `runtime::static_host::StaticChildControl` keep their public APIs.

| State / owner | Mutation entries for this slice | Contract or host boundary |
| --- | --- | --- |
| Native pending recipe and diagnostic error | Only `mount_request` constructs `NativeChildInput` and the returned handle. `apply_child_request` consumes the checked request, passes its exact `SharedChild` to `mount_inner`, and records an error only if `SharedChild::reject` accepts. | Actual identity remains in the kernel-owned shared slot. The ordinary diagnostic string is not another assignment authority. The checked allocator validates parent/domain/generation; cancellation can preclude assignment. |
| External allocation and immutable owner/generation | `mount_request` creates one control from its Episode. Handle, pending request, inverse and retained list clone that control. `complete_mount` writes `allocation: Option<Result<PluginId, String>>` exactly once. | The former separate identity cell and `assigned` flag are gone. No external inverse can contain a Native handle or lack its control. This pairing is enforced by ordinary Rust construction/privacy; graph identity and truthful allocation reports remain host premises. |
| External retirement and removal | `request_retirement` and `cleanup_failed` set retirement. Pre-allocation rejection sets `removed`; successful allocations require `removed()` after actual graph removal. Repeated allocation reports reject without changing the first result. | Cancellation after handoff retains a late real ID and waits for removal. Retirement alone does not resolve cleanup. Rejected requests never allocated a graph node. Ownership does not create a service dependency. |
| Retained Child cleanup failure and service status | `cleanup_failed` keeps the first cleanup error and reports terminal service failure; `record_error` reports setup/application errors. `mark_initialized`, `complete_mount` and `removed` use the private service-status methods. | `removed` rejects after a failed Child inverse. There is no reset of this sticky external-Child error; it is distinct from retryable callback factories. Service failure may resolve a join with an error while `finished` remains false. |
| External notify callback and cleanup waiter | Construction captures the callback. Retirement clones it; rejection/removal takes it for release. `poll_retired` replaces the waiter; allocation, cleanup failure and removal take it for notification. | Waker clone happens before locking; replaced wakers, captured callbacks and notifications are dropped/invoked after unlocking. Service notifications also run outside the Child lock. Reading the original Child handle from a completion notification is safe. |
| Episode's `ExternalChildren` retention list | Its private insertion is called only after successful admission. Static cancellation/cleanup snapshots the list; draining and `child_controls` prune only removed/rejected controls; successful Episode sealing takes the list for destruction outside the Episode lock. | The list retains the actual controls, including failures; it is not a graph or a second lifecycle authority. The broader mutable Episode guard still needs separate consolidation. |

The native call chain is `mount_request` → recorded
[`enqueue_native_child`](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/children.rs)
→ Execution/SetupWork admission → `SharedChild`; dispatch consumes the original
work item and completes its receipt. `mount_inner` uses `register_shared_child`;
the cleanup dispatcher calls `retire_shared_child` and the runtime's retirement
handling. `terminal_agrees`, `cancellation_precludes_assignment`, the recorded
queue/history frame and the native lifecycle contracts remain required. Native
Child retirement is not itself removal; actual removal still follows the lifecycle
and dependency guards.

The external chain uses `enqueue_owned_child` with the same control in request
and inverse → `StaticEpisode::drain_child_requests` → host allocation report →
`StaticCleanupFuture` → `poll_retired` → the original restoration ticket. The
[Node adapter](../crates/cordis-node/src/typed_children.rs) checks the original
owner/generation during handoff and reports allocation/application/cleanup
observations; [`forget_typed`](../crates/cordis-node/src/typed.rs) reports removal.
The embedding host must supply truthful graph observations. Queue receipts prove
which work/inverse is consumed, not that an arbitrary external report is true.
Neither path adds a dependency on Node to pure Rust.

The maintenance change removes identity/control pairing from callers and the
unrepresentable “external inverse without a control” fallback. Kernel contracts,
public APIs and scheduling/failure policies are retained. Existing native Child,
static-host and Node dynamic-Child regressions stay active; the static-host
allocation regression also checks late/duplicate reports against the original
handle and notification reentry. No paper obligation is closed by this refactor.

## Episode notifications and root progress

[`runtime/episode.rs`](../crates/cordis/src/runtime/episode.rs) now owns private
capability and notification fields. [`runtime/root.rs`](../crates/cordis/src/runtime/root.rs)
owns each actual root Future together with its work ticket;
[`static_host/progress.rs`](../crates/cordis/src/runtime/static_host/progress.rs)
owns the external setup/cleanup handshake. These are ordinary Rust owners calling
the existing checked execution, not additional lifecycle authorities.

| State / owner | Mutation entries for this slice | Contract or host boundary |
| --- | --- | --- |
| Episode host capabilities and retained unsupported request | `for_native` / `for_external` set the host mode and optional callbacks. `require_feature` accepts a typed `Feature` and retains the first unsupported request; `reject_child_batch` preserves the existing batch-error precedence. Successful `seal_external` takes the callbacks for release. | The same operations remain available to each host. Service-update phase checks remain in `check_service_update`; immutable metadata is not permission to write after withdrawal. |
| Episode driver and selected notifications | `replace_driver`, `take_driver`, `service_notification` and `child_notification` are the only post-construction mutation entries, besides successful external sealing. Setup, service, Child, poll and cleanup callers use these methods. | Callers clone wakers before locking and drop displaced wakers after unlocking. Shared `Notification` invokes callback before driver, outside locks, and has no Drop callback. Sharing this transport does not merge effect/service/host policies. |
| External closure resources | `seal_external` first calls the checked execution gate, then detaches values, driver, callbacks and the retained Child list into `ClosedEpisode`. `release_notifications` runs after unlocking. Native `poll_settle` takes its driver only after successful `release_controlled`. | External release keeps its order: driver, callbacks/children, completion bookkeeping, values. Failed sealing detaches nothing. Native release still requires its checked work/cleanup/dependency guards. |
| Root Future and exact work ticket | Private `RootState` is constructed by `initialize_callback` / `initialize_reply`; `RootSetup::poll` owns all queued/running transitions. Native and static callers cannot construct or split a pending pair. | `issue_root`, `start_root`, `cancel_queued_root`, `complete_root` and `fail_root` still operate on the actual work/receipt. Withdrawal may discard an unpolled root; a started root remains owned until it lands. |
| Static setup completion and abandonment | `setup_landed` records a landed result. Dropping an unfinished setup cancels it, calls checked `abandon_root`, then `abandon_setup` records the sticky error. | `start_cleanup` requires a landed setup and rejects abandonment. Dropping a Future does not certify restoration. No new scheduler or termination theorem is claimed. |
| Static cleanup in flight and retained error | `start_cleanup` preserves guard/error precedence and calls checked retry before clearing the old error; `cleanup_succeeded` clears running state; `cleanup_failed` retains the new error and returns a displaced one. | Compound locking is Episode → progress, never the reverse. Opaque errors are returned for destruction outside both locks. Consumed failures, retryable factories and sticky Child failures keep their distinct policies. |

The proof route remains the actual work/closure gates in
[`Execution`](../crates/cordis-kernel/src/execution.rs), recorded lifecycle/work
history, and the existing native release contracts. Future polling, callback
truth and destructor behavior remain host boundaries. The broader guard still
exposes values, cleanup dispatch and the Child-list interface to runtime modules;
this batch is not complete encapsulation of Episode or a new paper proof.

This audit also found and repaired two concrete ownership defects:

- A closed native Episode could retain its driver through an escaped setup
  context. `closed_native_episode_releases_driver_even_when_context_escapes` in
  [`runtime_waiters`](../crates/cordis/tests/runtime_waiters.rs) checks that a real
  pending cleanup releases this reference after checked closure.
- A static setup's sticky unsupported-feature error could replace and destroy an
  opaque application error while holding the Episode lock. The displaced result
  now leaves the lock before destruction. The `setup_override_drops_application_error_outside_episode_lock`
  test beside the private Episode checks the actual error destructor's lock access
  and preserves the diagnostic and cleanup behavior.

Both regressions reject temporarily restored old behavior. They are runtime
checks, not Verus negative controls; final-source integration results belong to
the [development record](development-report.json). Root cancellation, pending
work, cleanup retry and abandonment retain their existing regression coverage.

## Native decisions and control ownership

The production review route is [`Runtime::poll_settle`](../crates/cordis/src/runtime/poll.rs)
→ [`runtime/control.rs`](../crates/cordis/src/runtime/control.rs) →
[`NativeDriver`](../crates/cordis-driver/src/shared/native.rs) → the existing
[`NativeRuntime`](../crates/cordis-kernel/src/lifecycle_state/native/runtime.rs),
[`PollControl`](../crates/cordis-kernel/src/poll_control.rs) and recorded execution
contracts. A `Decision` is a candidate from observations, not a capability.

| State or observation | Owner, writers and actual use | Required distinction |
| --- | --- | --- |
| Phase, retirement, target, committed bindings and cleanup admission | Kernel/LifecycleState remain authoritative; `NativeRuntime` records their actual transitions. Shared `decision`/`coherent` read them, and checked begin/withdraw/cleanup/release/remove entries enforce represented guards. | Target/committed mismatch can be a legal transient. Scheduling a withdrawal is different from violating an invariant. Child ownership does not authorize provider release. |
| Polling owner, episode/work identity, setup error, cleanup error and restart | `PollControl` owns them. `poll_control` constructs; failure recorders retain the first payload; `request_restart`, controlled Begin/retry/release are the reset/binding entries. `poll_flags` derives failure from setup **or** cleanup error. | Restart clears setup failure, never retained cleanup failure. Retry requires the real failed execution/receipt. Rejected attempts retain their existing contract; no copied booleans become another authority. |
| Production host's original control object | Private `Control` in `runtime/control.rs` permits read access and failure recording, but no mutable control escape. `bind_control` obtains it from this Runtime's driver after actual registration. `with_control` is the sole take/return path for Begin, retry, release and restart. | Owner ID is checked before dispatch. The same object returns to its slot before success/error handling and payload destruction. This is ordinary Rust ownership; it does not add panic recovery inside the checked owner. |
| Native availability and decision | `NativeDriver::observe_decision` invokes the supplied predicate at the existing native observation points, then uses `decision_with_control` and shared `decision`. `Runtime::services_available` resolves actual target slots, anchor identities, context and injection configuration. | Loading/Active evaluates only while coherent; Inactive only while not retired and without setup failure. Other phases do not call it. Nothing is cached. A user predicate's truth and side effects remain a host premise. |
| Node and standalone Driver observations | Node uses its sealed/ready/failure/restart observations; the standalone `LifecycleDriver` also accepts `HostStatus` and derives current tickets from the checked ledger. | Node readiness is not a synchronous native user predicate. These policies and the action/restore ledgers are not merged. Ticket views remain observations; the checked ledger authorizes completion. The wider public API/cache audit remains open. |

`poll_control` now retains the Native member's actual `Arc<AllocationIdentity>`
in place of its separate ghost Native key. Its strengthened `wf`,
`binding_identity` and `binding_correspondence` connect that allocation to exactly
the Journal/key pair required by `bound(native)`. `NativeRuntime::poll_control_identity`
borrows the original member allocation with the matching contract.

`NativeDriver::owns_poll_control` compares these borrowed allocations with
`Arc::ptr_eq`. Every Driver entry accepting a control checks this before calling
the kernel: both decision entries, restart, Begin, raw/recorded retry and release,
and the controlled/scoped service and payload checkpoints. Rejection returns
`None` or `InvalidState` before predicates, failure extraction or lifecycle
mutation. `rejected_release` returns no Unload receipt or terminal queue evidence.
The factory clones an existing allocation once; repeated checks add no Journal
lock, counter allocation or Arc clone. Identity comparison needs no numeric name,
including when the allocation-name issuer is exhausted. Holding the Arc prevents
reuse of that allocation while an old control survives.

**The identity meaning is verified; `Arc::ptr_eq` and its ordinary Driver callers
remain a Rust/standard-library boundary.** This is an executable check of control
provenance, not a Verus proof of the whole adapter. The raw `NativeRuntime` API
retains its `bound` preconditions. Identity does not establish registration,
current episode, cleanup readiness, or provenance of separately supplied
executions/configurations/scopes; their contracts and guards remain necessary.
Those other public API premises remain open. Pending ticket observations are
covered by the dedicated audit below.

Previously four runtime entries independently took/returned a raw optional
control, and native observation gating lived beside host value lookup. The
control module now owns those writes and Driver owns the observation policy.
Failure payloads still leave the Episode/Journal locks before destruction; retry
still restores the control before extracting the displaced error and waker.
Existing transition guards and error/result contracts, the public Runtime API
and Node policy are retained. The control representation now adds the certified
Native identity above; the Driver entries have actual Runtime callers.

The [service parity regression](../crates/cordis/tests/service_parity.rs)
`failed_and_retired_consumers_do_not_recheck_user_predicates` checks a real failed
consumer, repeated settle/diagnostics, explicit restart and removal. It also
rejects an eager-predicate mutation of the new entry. Existing
[`retry_cleanup`](../crates/cordis/tests/retry_cleanup.rs),
[`update_recovery`](../crates/cordis/tests/update_recovery.rs) and
[`shared_lifecycle`](../crates/cordis-driver/tests/shared_lifecycle.rs) cover retained
failure, binding replacement, consumer protection and old tickets. These runtime
checks do not prove arbitrary predicates or scheduler progress; final integration
results remain in the [development record](development-report.json).

The [control ownership regressions](../crates/cordis-driver/src/shared/native/control_tests.rs)
create two real Native owners with deliberately identical domain, plugin,
generation and work numbers. They check observation rejection before callbacks,
exact failure-payload retention, raw/recorded failed cleanup and successful local
retry/release, all three control-bearing checkpoints, and a replacement Runtime
after the original owner is dropped. Removing the identity guard makes all three
tests fail. A separate compilable mutation that captures the control member's
identity instead of the Native member's identity is rejected by the factory's
Verus postconditions. These are scoped falsification checks; they do not stand in
for the independent full negative-control suite.

## Execution, configuration and scope provenance

Native Driver now checks the separately supplied owners before entering the
kernel. These are production entry checks, backed by verified identity getters
and factories; they do not change the meaning of paper lifecycle transitions.

| Object | Actual authority and check | Rejection and remaining boundary |
| --- | --- | --- |
| Raw or recorded execution | `Execution::execution_domain` borrows the cleanup owner's actual Journal. `NativeRuntime::execution_domain` borrows the Native member's Journal. `owns_execution` compares their backing allocations and checks the existing current-Episode selector. | All Driver entries receiving an execution or recorded owner check this before root admission/dispatch, publication, withdrawal, settle/failure/retry, release or joint observation. Rejection returns the original argument/owner where the API consumes one; it cannot issue a successful release receipt. Phase/readiness checks still apply. |
| Recorded configuration | `Recorded::execution_domain` reaches its actual history ledger through `domain_ref`; `owns_configuration` compares it with the Native Journal. | `NativeDriver::configuration_snapshot` returns `None` for a foreign Journal before a joint read. Direct construction with a clone of the same Journal is accepted. Loader keeps both owners private and retains its infallible high-level checkpoint, asserting that private association at the checked return. Configuration targets and adoption use the additional Native allocation checks described below. |
| Root/effect scope | `scope_for_group` retains the actual live queue's `Arc<AllocationIdentity>`. Its contract proves `linked_to(execution)` for an attached execution; the exact clone contract preserves this binding. `owns_setup_scope` checks execution provenance, the numeric selector and the retained queue allocation. | Both scoped service/payload checkpoints reject foreign or removed queues. `SetupScope` is an explicitly clonable handle; it retains neither queue payloads nor the Journal. `belongs` and raw `EffectRun::call_scoped` still describe numeric selection; standalone/static scopes have no Journal allocation and do not gain a general authenticity theorem. |

[`Journal::runtime_identity`](../crates/cordis-kernel/src/reversible_value/joint.rs)
borrows an opaque wrapper around the existing lock allocation. The wrapper
exposes no lock or mutation authority, and `identity_correspondence` connects its
identity to exact Journal equality. There is no additional allocation or counter
per Journal, and the repeated Driver checks do not lock or clone it. A linked
scope clones its queue identity when issued or explicitly cloned.

**Verus proves the returned identities' meaning and the Scope factories;
`Arc::ptr_eq` and the ordinary Driver remain a Rust/standard-library boundary.**
Raw `NativeRuntime` checkpoint APIs retain their Journal premises. Invocation tokens and configuration targets/adoption are covered below. Child
tokens and earlier recovery snapshots retain distinct contracts and audit work.
Pending views are also covered below. This slice does not
prove arbitrary callbacks, all host inputs, scheduler progress or a new general
paper obligation.

The [five provenance regressions](../crates/cordis-driver/src/shared/native/provenance_tests.rs)
use deliberately colliding domain/Episode/work numbers, equal configuration
contents and real failed/ready cleanup owners. They check non-consumption of root
arguments, retained failures, rejection when both releases are ready, all scoped
checkpoint forms, typed root paths, accepted local calls, Journal clones and a
replacement Runtime after the original is dropped. A weak Journal reference also
checks that an escaped scope does not retain the original domain.
[Shared test support](../crates/cordis-driver/src/shared/native/test_support.rs)
keeps the same collision fixture as the earlier control regressions.

Scoped falsification checks replace the queue binding in `scope_for_group` with
`None` (compiles, then Verus rejects its postcondition), make `same_journal` always
accept (all five regressions fail), and bypass only the queue pointer comparison
(the scope regression fails). They are not the full negative suite. Final source
and development acceptance remain bound by [the development record](development-report.json).

## Pending action observations

The action ledger is the sole owner of outstanding tickets. `LifecycleDriver`
now derives `pending_action` from `LifecycleState::pending`, as Native and Node
Drivers already do. The separate `pending_views` map and its eight insertion and
eight removal sites are gone. A new lifecycle entry therefore has no second
pending-ticket state to synchronize.

| State / observation | Authority and actual entry families | Review consequence |
| --- | --- | --- |
| Current action | `ActionLedger` owns domain, monotonic action counter and exact pending records. `begin`, checked admission, raw/native Begin, cleanup request and retry issue through the checked protocol. | `pending` returns the unique current ticket or its absence. Under `wf`, `out == Some(ticket)` is equivalent to recorded membership for that owner; the contract is propagated through `LifecycleActions` and `LifecycleState`. |
| Completion and failure | Setup settlement, `complete_action`, `complete_cleanup`, raw/native Finish, failure and release call the existing owners. `pending_matches` now uses the exact read contract. | Withdrawal/retirement retain an in-flight ticket; accepted completion consumes it. Rejected stale/foreign replies retain the current ticket. A failed Finish can settle setup before rejecting activation, so an error does not imply that a pending ticket still exists. |
| Cleanup receipt and resource release | `LifecycleActions` retains failed/succeeded/drained receipts independently of outstanding actions. Release and Remove retain their original guards. | An empty pending view is **not** release permission: a failed cleanup has no outstanding reply but still blocks release until a fresh retry succeeds. |
| Host wire value | `pending_action` returns an owned `ActionTicket`; `host_ticket`/`kernel_ticket` convert the five fields, and serde encodes the wire representation. | Retained or modified values do not mutate the ledger; a reply is revalidated by the checked protocol. Conversion, serialization and ordinary Driver wiring remain Rust boundaries, covered by runtime regressions. |

The low-level `LifecycleDriver::pending_action` API changes from
`Option<&ActionTicket>` to `Option<ActionTicket>`, matching both other Drivers.
This removes the map and write-side allocation/synchronization, while standalone
lookups change from a tree lookup to the existing ledger's linear scan. Native
and Node already use that scan. This is a maintenance improvement, not a measured
throughput claim; there is no new cache, index, crate or runtime dependency.

[Four production-path regressions](../crates/cordis-driver/tests/pending_actions.rs)
cover raw failed cleanup/retry/release/new generation, failed Finish after setup
settlement, Native publication/release, and checked admission/resource release.
They compare actual owner/admission tickets, exact wire fields, retained old
views, rejected calls and an unrelated pending owner. Existing cleanup outcome,
resource and shared-lifecycle tests retain their original assertions.
A scoped omission in the ledger must compile and fail the exact `pending`
postcondition; an adapter hiding every current ticket is rejected by all four
new regressions. These are scoped controls, not full negative acceptance.

This slice connects the stale-reply guarantee to current observations; it does
not change paper lifecycle rules or close a general paper obligation. Invocation,
configuration/adoption and Child provenance are audited below; historical
recovery inputs remain a separate audit. Final acceptance is bound to the
[development record](development-report.json).

## Source organization and dependency direction

| Area | Ownership / purpose | Review classification |
| --- | --- | --- |
| [`lifecycle_state/`](../crates/cordis-kernel/src/lifecycle_state/), [`lifecycle_actions/`](../crates/cordis-kernel/src/lifecycle_actions/), action/cleanup ledgers | Shared lifecycle authority and committed-provider protection | Production state with attached contracts and trace composition |
| [`reversible_value/`](../crates/cordis-kernel/src/reversible_value/), [`cleanup_queue/`](../crates/cordis-kernel/src/cleanup_queue/), [`cleanup_groups/`](../crates/cordis-kernel/src/cleanup_groups/) | Managed operations, retained inverses, actual execution origins and histories | Production primitives plus interpretation/transport proofs; generality limits remain explicit |
| [`lifecycle_state/native/`](../crates/cordis-kernel/src/lifecycle_state/native/), [`node_runtime/`](../crates/cordis-kernel/src/node_runtime/) | Separate Native and Node state owners establish their own premises for the shared protocol | Production connections. Node records publications/handles/scopes; it does not prove JS object interiors. |
| [`refinement.rs`](../crates/cordis-kernel/src/refinement.rs), [`dependent_grammar.rs`](../crates/cordis-kernel/src/dependent_grammar.rs), grammar/history/recovery modules and [`mixed_driver/`](../crates/cordis-kernel/src/mixed_driver/) | Paper semantics, conditional theorems, reference executors and bridges from actual histories | Specification and proof support, including executable research drivers; being erased or not called by a host does not make it redundant |
| [`paper_counterexamples.rs`](../crates/cordis-kernel/src/paper_counterexamples.rs), recovery/mixed examples, scoped controls and frozen evidence | Counterexamples, repaired interpretations, admitted examples and falsification | Retained research evidence; separate navigation, same active verification targets |
| [`cordis-driver/src/shared/`](../crates/cordis-driver/src/shared/), [`cordis-driver/src/node.rs`](../crates/cordis-driver/src/node.rs) | Shared scheduling policy, command decoding and host state adapters | Ordinary Rust bridge, not an additional verified scheduler theorem |
| [`runtime/setup.rs`](../crates/cordis/src/runtime/setup.rs), [`services.rs`](../crates/cordis/src/runtime/services.rs), [`cleanup.rs`](../crates/cordis/src/runtime/cleanup.rs), [`poll.rs`](../crates/cordis/src/runtime/poll.rs) | Episode-bound API, service handle access, cleanup dispatch and cooperative polling; opaque callback attempts live in [`cleanup/attempt.rs`](../crates/cordis/src/runtime/cleanup/attempt.rs) | Ordinary host; Episode association and handles now live in `runtime/episode.rs` and `runtime/effect_handle.rs`. Child admission and external controls live in `runtime/child.rs` and `runtime/child/external.rs`. Root Future/ticket ownership lives in `runtime/root.rs`, and the static handshake in `runtime/static_host/progress.rs`. Native control binding/lending and reset entries live in `runtime/control.rs`. Other lifecycle entry points remain in [`runtime.rs`](../crates/cordis/src/runtime.rs) |
| Optional Node facade / N-API / process / cdylib adapters | Language semantics, callback execution, transport and external I/O | Tested host boundary. Rust applications do not require Node; Harness stays a separate application. |

The dependency direction remains host → shared Driver → verified state owners →
shared lifecycle and resource protocols. Mathematical support supplies theorems
to attached contracts. It is not a runtime dependency on Node or a second copy of
the implementation. The [architecture guide](architecture.md) explains toolchain,
library, compiler, verifier and FFI trust assumptions.

## Disposition of accumulated material

| Material before refactoring | Disposition and rationale | Check |
| --- | --- | --- |
| 253 flat files connected by `#[path]` | Moved to their **existing logical module paths**: 41 lifecycle files, then 212 remaining files. All 255 path attributes removed, including two redundant attributes. No public module identity changed. | Exact body/contract comparison after path directives and source-reference updates; compile, full Verus, packaging and canonical mutation-anchor checks |
| 5,195-line ordinary `runtime.rs` | Cleanup extracted first; setup, service handle methods and poll loop extracted next. Root had 3,139 lines at the end of that layout batch. Public types/exports remained stable; only necessary internal method visibility changes. | Method-body comparison, Cargo/lints, original host regressions and extracted package builds |
| 15 wrappers around the same strict control runner | Replaced by `check-profile-controls.py PROFILE` | The same canonical selections, fresh positives, full mutant compile and exact rejection diagnostics; unique full/R2 runners retained |
| Separate callback reply/factory arguments in two ordinary hosts | One opaque completion and private attempt owner in `runtime/cleanup/attempt.rs`; the checked queue and host failure policies are retained | All-target compilation, existing retry/static-host/update regressions and final development acceptance; no added kernel theorem claim |
| Identity/control pairs spread across setup and static host | Child admission owns request/handle/inverse construction; a single private external allocation replaces the duplicate identity cell and assignment flag | Original-handle/duplicate-reply/notification-reentry regression, existing Child cases and final development acceptance; external graph truth remains a host premise |
| Distributed Episode flags, notification fields and root/progress writes | Private Episode capability/notification methods, root ticket/Future pairing and static progress owner; one shared notification transport after comparing callback order and Drop behavior | Existing cancellation/retry/abandonment coverage plus two regressions rejecting old retention and locked-error destruction; public APIs and checked contracts retained |
| Four copies of native control take/return and host-local observation gating | One private control owner and transition helper; native lazy availability policy in Driver, used by Runtime | Same checked calls/error handling, real failed/restarted/retired consumer regression and an eager-observation mutation; lower-level factory provenance remains explicit |
| Repeated entry-point lists | One task-based documentation index, this ownership map and one campaign CLI | Links, source bindings and bilingual review entry points |
| General models, conditional recovery branches, unique failures and frozen reports | Retained under research navigation and their existing verification targets | No obligation is closed by moving a file; historical reports keep their original source binding |

The fixed archive is `codex/archive-before-refactor-2026-10-24` at `60bdd89`.
The layout before the second batch is also preserved at `c47d111`. Neither branch
history nor the upstream lock is rewritten. This iteration has **no approved
semantic deletion**: more removal requires comparing premises/results, callers,
proof dependencies and unique counterexamples. The archive alone is not a reason
to delete a theorem still used by a current claim.

## Invocation and configuration target provenance

`Runtime::start` / recorded root admission →
[`NativeDriver`](../crates/cordis-driver/src/shared/native.rs) →
[`NativeRuntime::admit_managed_root`](../crates/cordis-kernel/src/lifecycle_state/native/runtime.rs)
issues the actual invocation. Loader captures a configuration target from the
same Driver and passes it through preflight and batch adoption. Neither path
accepts equal domain, plugin, generation and revision numbers as sufficient
proof of Native ownership.

| State / owner | Construction and checked use | Remaining boundary |
| --- | --- | --- |
| `RegisteredInvocation` | Private `bind_native` retains the actual Native member allocation while preserving argument, work ticket, lifecycle ticket, owner and recipe version. Native and recorded admission prove `bound_to(control_address())`. `owns_invocation` guards both `call_root` and `call_opaque_root` before callback dispatch. | Generic `LifecycleState` admission stays unbound and usable by its own standalone path. Kernel dispatch still checks owner, current episode, loading state and recipe version. An authentic but stale token remains invalid. |
| Configuration `Target` | The real factory proves numeric freshness and exact Native binding. Its verified `Clone` preserves both. Driver guards current-target queries and replacement using the retained allocation. Queries and replacement borrow the target; they do not renew it or clone its Arc. | Raw kernel freshness intentionally remains a numeric predicate. Driver allocation comparison is an additional ordinary Rust guard. Historical `Allocation` evidence does not become a current-target capability. |
| Owned configuration batch | Driver reuses the verified complete preflight and merges the first foreign target at or before its first failure. A foreign target takes precedence over a duplicate/capacity error at the same position. All rejection paths return the complete input before any replacement or metadata callback. | Successful batches enter the existing verified adoption loop, which preflights again. This adds a read-only pass, not a second policy implementation. The opaque metadata callback still has its existing contract/panic boundary; preflight atomicity does not claim arbitrary callback rollback. |

The allocation is the existing `Arc<AllocationIdentity>`; no new identity table,
per-token heap allocation or counter is introduced. Tokens retain no Journal,
Native host or recipe payload. Invocation arguments retain their ordinary owned
lifetime. Configuration targets explicitly clone when a caller needs another
handle, and no longer implement `Copy`, `Debug` or equality traits.

Verus checks the exact factory/clone meanings and the existing version/lifecycle
and all-or-nothing preflight contracts. `Arc::ptr_eq`, adapter guard execution and
opaque callbacks remain ordinary Rust/standard-library boundaries. This is an
implementation identity mechanism supporting the lifecycle model, not another
numbered paper theorem or closure of a general obligation.

The [seven regressions](../crates/cordis-driver/src/shared/native/authority_tests.rs)
deliberately reuse all numeric selectors, exercise both callback forms and the
standalone path, preserve arguments/recipes/metadata, check batch error order and
successful adoption, and observe weak Journal references after dropping owners.
Existing kernel tests retain activation, revision, withdrawal and restart checks.
Scoped negative checks bind real factories to the wrong recipe allocation and
remove numeric freshness comparisons; matching fresh positives and compiled
mutants must produce the named contract failure. Separate adapter mutations
exercise the ordinary guards. Current integration evidence is in the
[development record](development-report.json); these are not the full negative
suite or paper-wide acceptance.

## Child request and cleanup provenance

Dynamic `Setup::mount` follows the actual recorded
[`enqueue_native_child`](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/children.rs)
→ Execution → SetupWork → `SharedChild::from_work` path. Request, returned handle
and inverse share one decision cell. The factory now retains the creating work's
actual Journal; exact contracts propagate that association through both wrappers.
This supplements the existing atomic request/inverse and parent/episode contracts.

Direct `Runtime::mount(..., Some(parent), ...)` uses
[`NativeRuntime::registered_child`](../crates/cordis-kernel/src/lifecycle_state/registration/shared_child.rs)
through the Driver. The factory reads the actual registration, binds the Native
Journal and produces a certified assignment snapshot. `Mounted::owned` retains
that same `SharedChild` before Begin; an active parent's cleanup queue receives
it directly. `Runtime::start` drains the retained objects without reconstructing
cleanup authority from numeric identities.

| Check / owner | Guarantee and remaining premise |
| --- | --- |
| `SetupWork::execution_domain`, Child factories and `Clone` | Exact contracts identify the retained Journal and preserve the shared decision. Raw, unlinked work and `SharedChild::from_identity` remain unbound. |
| `NativeDriver::owns_shared_child` | Before registration or retirement, compare the retained Journal allocation with this Native owner. A foreign/unbound request cannot mutate its slot or the receiver; rejected registration returns the original definition and host payload. The pointer comparison and wrapper are ordinary Rust boundaries. |
| Kernel shared-slot transitions | The original numeric domain, parent, episode, phase and terminal-state guards still apply. A cancelled request cannot later allocate. Matching Journals alone do not prove arbitrary same-Journal reconstruction safe or grant a fresh episode. |
| Runtime cleanup → retirement → guarded Unload/removal | The actual inverse passes the retained Child to the Driver. A local assignment witness is not a lifecycle-completion certificate; retired entries still need the existing cleanup/dependency gates before removal. Ownership is not a service dependency. |

The binding retains Journal metadata until the last Child clone is dropped. It
does not retain Native recipe or host payloads through this association. Creation
adds a Journal Arc clone; `SharedChild::clone` also clones it. No identity table,
new counter or per-handle Journal allocation is introduced. Raw `ChildIdentity`
remains `Copy`; low-level callers of raw `NativeHost` APIs retain their existing
provenance premises. Use the Native factory or the actual enqueue result when
passing a Child to `NativeDriver`.

[Seven Driver regressions](../crates/cordis-driver/src/shared/native/child_tests.rs)
cover colliding numeric selectors, original payloads, cancellation/restart,
recorded request/inverse sharing, local success/idempotence and metadata lifetime.
The [actual Runtime regression](../crates/cordis/tests/runtime.rs) mounts children
before and after activation and checks eventual registry removal. Scoped proof
controls remove each factory's Journal and require a fresh matching positive,
whole mutant compilation and the exact contract failure. Separate runtime
mutations bypass the Driver guard or restore numeric cleanup reconstruction;
both are rejected by behavioral tests. The full negative suite is separate.

This is an implementation-provenance mechanism supporting Definitions 52/54,
not a general Child recovery theorem. Native historical snapshot provenance is
audited below; general recovery, arbitrary callbacks and global progress retain
their own obligations. Final integration
results are bound to the [development record](development-report.json).

## Native historical snapshots

[`shared/native/snapshots.rs`](../crates/cordis-driver/src/shared/native/snapshots.rs)
owns the Driver's 13 existing observation entry points and the source check.
The forwarding guards and one-epoch service/payload observations remain intact.
Lifecycle mutation and callback dispatch stay in the Native Driver owner.

| Owner / route | Contract and remaining boundary |
| --- | --- |
| Native [`history::Snapshot`](../crates/cordis-kernel/src/lifecycle_state/native/runtime/history.rs) | The private constructor retains the actual Native allocation alongside the Journal. `certified` ties that allocation to both the Journal and Native key; `native_identity` exposes the exact borrowed source. Publication, episode, slot, payload and configuration factories supply the real owner's allocation. Typed histories remain erased. |
| Configuration observation | `native_snapshot` borrows the Native component at the same configuration/source cut. It neither copies history nor renews an earlier observation. |
| Driver `recovery_snapshot(&native_cut)` | `owns_snapshot` compares retained Native allocations before calling the kernel. Foreign cuts return `None`; local cuts remain valid through later publications, failed cleanup, retry, Unload and new Episodes. Pointer equality is an ordinary Rust/standard-library boundary. |
| Kernel `recovery_snapshot_from` → raw `recovery_snapshot` | The typed cut's invariant supplies the Native-record premise. The shared `Capture::describes` predicate preserves the exact earlier cut, ordered extension, normalized interval and conditional recovery/obstruction results. The raw API retains its explicit same-Journal/Native-record premises for proof clients using interior cuts. |
| Capture versus mutation | `Some(Capture)` means the source was accepted. Its `Ghost` issue is not an executable cleanup-success flag. A snapshot cannot replace a current invocation, execution, retry ticket or release gate; capturing it neither restores values nor consumes cleanup. |

The ordinary Driver API now takes `&history::Snapshot<V>` and returns `Option`;
it is available for generic Native values, not only managed slots. Use its actual
`publication_snapshot()` result or a configuration's borrowed Native snapshot.
A raw `joint::Snapshot` does not establish the Native-record premise of this API.
`into_joint` intentionally drops the Native association; `joint().refresh()`
refreshes only the raw Journal observation, not the typed Native history.

Each Native snapshot adds one clone of the existing Native allocation Arc. No
identity table, counter, extra Journal lock or runtime history is added. Snapshots
retain Journal/identity metadata but no recipe, host or publication payload through
the erased history. Projection to `joint::Snapshot` drops the extra identity
reference; retaining the projected Journal keeps its ordinary metadata lifetime.

[Five regressions](../crates/cordis-driver/src/shared/native/snapshot_tests.rs)
exercise colliding numeric selectors, real failed cleanup/retry/restart, borrowed
configuration cuts, eight actual factory paths and payload/metadata destruction.
Scoped proof controls substitute the recipe allocation or discard the earlier
cut; matching positives and whole mutant compilation must precede the exact
contract rejection. Ordinary guard bypass/always-reject controls check both
rejection and usable admission. They are distinct from the full negative suite.

This closes the selected Native observation-input association, not general
source/target heap recovery, semantic independence, Node history or host liveness.
Current integration results remain in the [development record](development-report.json).

## Node publication command ownership

[`Driver::set`, `revoke` and `reclaim`](../crates/cordis-driver/src/services.rs)
now call the verified [`NodeRuntime` service operations](../crates/cordis-kernel/src/node_runtime/services.rs).
The former ordinary-Rust `owned_publication` decision and `NodeDriver::replace_value`
forwarder are removed. The service module is another implementation of the same
state owner: it adds no publication table, permission cache or runtime history.
`publish`, `resolve` and service error translation share the Driver service module;
public method names, wire results and error precedence remain unchanged.

| Authoritative state / actual entry | Checks, writes and proof dependency |
| --- | --- |
| Publication owner/generation and current Kernel generation | Private `owned_publication` reads the actual registry and control. Its exact `ownership` contract rejects unknown IDs, foreign owners and an earlier episode even when the old slot still has matching owner/generation fields. Rejection leaves the observation and history unchanged. |
| Payload, revision and displaced handles | `replace_service` uses `check_replacement` then `replace_admitted` → the existing `replace`/`PublicationStore::replace_checked`. Admission is checked before ownership, then visibility. `service_replaced` identifies the actual Replace event and result; existing handle-delivery contracts retain the displaced reference. |
| Visibility and cleanup lookup selections | `revoke_service` → `revoke`/`revoke_with_restoring`/`forget_restoring`. Current ownership is required, but retirement/restoration does not itself disable cleanup. Revocation remains idempotent and does not release a consumer lease. `service_revoked` identifies the exact recorded call. |
| Retained payload, checked marker and dynamic reservation | `reclaim_service` checks current ownership, returns true for an already reclaimed slot, and calls the real `reclaim` for retained slots. A live lease produces false. Only successful reclamation clears the checked marker and calls the existing complete `reconcile_declarations` traversal. `service_reclaimed`/`reclaim_tail` compose its actual history with `batch_result`. A later reconciliation error retains the completed prefix; it is not rollback. |
| Actual object table and Node state | [`Bridge::replace_service`](../crates/cordis-kernel/src/node_runtime/bridge.rs) uses the same `check_replacement`/`replace_admitted` pair under one exclusive Node borrow, validating its own domain and real object key between them. [`Driver::set_host_object`](../crates/cordis-driver/src/objects.rs), used by the Node object path, no longer supplies a separate ownership assertion. Bridge errors preserve Node state; a successful write uses the actual issued key. |

The `interfaces` map retains initial setup requirements and current dependencies;
`dynamic` records later declaration ownership. Publication visibility, a retained
old slot, a committed consumer lease and the current dynamic declaration are
different facts. The service commands reuse their existing owners and history
contracts. Internal withdrawal, adoption and cleanup-release primitives retain
separate purposes and are not replaced by the host-command admission rule.

The [kernel regressions](../crates/cordis-kernel/tests/node_services.rs) exercise
foreign/old owners, a real retained lease, retirement-time cleanup and transfer to
a prepared successor. The [Driver regression](../crates/cordis-driver/tests/service_ownership.rs)
compares metadata and object-table writes, error precedence and the actual retained
object. `python3 -B scripts/check-profile-controls.py node-services` checks two
canonical mutations: omitting owner equality or omitting the current Kernel
generation. It requires fresh positives, compiling mutants and exact ownership
postcondition rejection. `--check` validates anchors only.

These contracts cover the represented publication protocol. Arbitrary JS object
interiors, callback effects, FFI conversion, first-activation orchestration and
whole-host recovery keep their own boundaries. Node remains optional for Rust
applications; this batch introduces no dependency or additional validation runner.
