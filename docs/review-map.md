# Ownership and review map

English · [简体中文](review-map.zh-CN.md) · [Plan](verification-plan.md) · [Generated evidence](cases/generated-lifecycle.md)

Start with the state an operation owns. The production function and its Verus
contract remain together. The tables classify responsibilities and review paths;
they do not declare every function in a directory to be a production caller.

The cleanup-path audit below is the first implementation of the
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
| [`SharedChild`](../crates/cordis-kernel/src/lifecycle_state/registration/shared_child.rs): shared `inner` cell and immutable `origin` | `enqueue_native_child` creates the request and inverse together. `register_shared_child` assigns the real identity under the same lock; `reject`/`retire_shared_child` settle or retire that same slot. The host dispatches the returned handle. | Request/inverse identity, parent generation and before/after `ChildTransition` agree. A pending cancellation prevents later assignment. A parent/Child ownership relation does not introduce a service dependency. |
| Native episode, recorded execution and poll control | [`NativeRuntime`](../crates/cordis-kernel/src/lifecycle_state/native/runtime.rs) owns `host`, `services`, `owners` and the connected histories. [`RecordedExecution`](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle.rs) owns actual work/cleanup state and its history witnesses. [`PollControl`](../crates/cordis-kernel/src/poll_control.rs) owns episode/work identity, failure and restart state. Controlled begin/retry/release and failure recording are the mutation entries on this path. | `owns_execution`, `bound`, `matches`, idle work and drained queues are established or checked by the actual API. Retry clears failure through the checked transition. Release removes the matching owner/publications only after guarded unload, returning values to be dropped by the host. |
| Node cleanup state and retained publications | [`NodeRuntime`](../crates/cordis-kernel/src/node_runtime.rs) owns `control`, `store`, `admissions`, `episodes`, `restoring` and released handles. `begin`, `cleanup_with_error`, episode commands and release update the episode; [`resources`](../crates/cordis-kernel/src/node_runtime/resources.rs) derives/updates retained manifests; handle draining transfers released values to the adapter. | `wf` and `history::operation` connect these observations. `cleanup_allowed` rejects raw `Release`; resource-aware `release`/`release_reservation` checks actual admissions/leases/publications. `cleanup_failed` and diagnostics are checked host-state observations, not another release authority. JS disposal success remains a host report. |
| Ordinary Rust callback attempt | [`RunningCleanup`](../crates/cordis/src/runtime/cleanup/attempt.rs) privately owns the ticket, actual Future and retry factory. `start` and `poll` produce an opaque `CleanupCompletion`; `Cleanups::complete_reply` consumes it through the existing verified completion APIs. [`Runtime`](../crates/cordis/src/runtime/cleanup.rs) and [`StaticCleanupFuture`](../crates/cordis/src/runtime/static_host.rs) store/remove the pending attempt. | Pending retains both Future and factory. A ready result carries its own factory, without separate caller-selected pairing. Callers acknowledge under the Episode lock, then drop rejected/discarded payloads and the completed Future outside it. Rust privacy and runtime regressions support this wrapper; they are not a Verus proof of callback effects or scheduler progress. |

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

### First ownership consolidation

Previously, `initialize_cleanup`, `poll_cleanup_callback`, completion enums and
`Cleanups::complete_reply` were scattered through `runtime.rs`; both hosts passed
the reply and retry factory separately. They now share
[`cleanup/attempt.rs`](../crates/cordis/src/runtime/cleanup/attempt.rs). Its private
fields prevent other runtime modules from constructing or splitting a completed
attempt, and both callers keep the Future alive through acknowledgement/error
handling before dropping it outside locks. No public API or kernel contract changed.

The two failure policies and the action/restore ledgers remain separate because
their semantics differ. `Episode`/`SharedEpisode`, effect-handle ownership and wider
Node interfaces remain further review work. This batch establishes one bounded
maintenance improvement; it does not complete the structural roadmap or R01.

Existing regression coverage includes [`retry_cleanup`](../crates/cordis/tests/retry_cleanup.rs)
(distinct failed groups, factory/Future panics, retained pending work and reentrant
factory destruction), [`static_host`](../crates/cordis/tests/static_host.rs)
(sticky consumed failures and Child cleanup) and
[`update_recovery`](../crates/cordis/tests/update_recovery.rs) (provider/consumer/Child).
Use the final-source development record for integration results; historical
campaign/negative-control records retain their own source bindings.

## Source organization and dependency direction

| Area | Ownership / purpose | Review classification |
| --- | --- | --- |
| [`lifecycle_state/`](../crates/cordis-kernel/src/lifecycle_state/), [`lifecycle_actions/`](../crates/cordis-kernel/src/lifecycle_actions/), action/cleanup ledgers | Shared lifecycle authority and committed-provider protection | Production state with attached contracts and trace composition |
| [`reversible_value/`](../crates/cordis-kernel/src/reversible_value/), [`cleanup_queue/`](../crates/cordis-kernel/src/cleanup_queue/), [`cleanup_groups/`](../crates/cordis-kernel/src/cleanup_groups/) | Managed operations, retained inverses, actual execution origins and histories | Production primitives plus interpretation/transport proofs; generality limits remain explicit |
| [`lifecycle_state/native/`](../crates/cordis-kernel/src/lifecycle_state/native/), [`node_runtime/`](../crates/cordis-kernel/src/node_runtime/) | Separate Native and Node state owners establish their own premises for the shared protocol | Production connections. Node records publications/handles/scopes; it does not prove JS object interiors. |
| [`refinement.rs`](../crates/cordis-kernel/src/refinement.rs), [`dependent_grammar.rs`](../crates/cordis-kernel/src/dependent_grammar.rs), grammar/history/recovery modules and [`mixed_driver/`](../crates/cordis-kernel/src/mixed_driver/) | Paper semantics, conditional theorems, reference executors and bridges from actual histories | Specification and proof support, including executable research drivers; being erased or not called by a host does not make it redundant |
| [`paper_counterexamples.rs`](../crates/cordis-kernel/src/paper_counterexamples.rs), recovery/mixed examples, scoped controls and frozen evidence | Counterexamples, repaired interpretations, admitted examples and falsification | Retained research evidence; separate navigation, same active verification targets |
| [`cordis-driver/src/shared/`](../crates/cordis-driver/src/shared/), [`cordis-driver/src/node.rs`](../crates/cordis-driver/src/node.rs) | Shared scheduling policy, command decoding and host state adapters | Ordinary Rust bridge, not an additional verified scheduler theorem |
| [`runtime/setup.rs`](../crates/cordis/src/runtime/setup.rs), [`services.rs`](../crates/cordis/src/runtime/services.rs), [`cleanup.rs`](../crates/cordis/src/runtime/cleanup.rs), [`poll.rs`](../crates/cordis/src/runtime/poll.rs) | Episode-bound API, service handle access, cleanup dispatch and cooperative polling; opaque callback attempts live in [`cleanup/attempt.rs`](../crates/cordis/src/runtime/cleanup/attempt.rs) | Ordinary Rust host. Other state owners and lifecycle entry points remain in [`runtime.rs`](../crates/cordis/src/runtime.rs); preserve lock/drop order. |
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
| Repeated entry-point lists | One task-based documentation index, this ownership map and one campaign CLI | Links, source bindings and bilingual review entry points |
| General models, conditional recovery branches, unique failures and frozen reports | Retained under research navigation and their existing verification targets | No obligation is closed by moving a file; historical reports keep their original source binding |

The fixed archive is `codex/archive-before-refactor-2026-10-24` at `60bdd89`.
The layout before the second batch is also preserved at `c47d111`. Neither branch
history nor the upstream lock is rewritten. This iteration has **no approved
semantic deletion**: more removal requires comparing premises/results, callers,
proof dependencies and unique counterexamples. The archive alone is not a reason
to delete a theorem still used by a current claim.
