# R2: Node protocol execution history

[简体中文](r2-node-execution.zh-CN.md) · [Execution contracts](r2-execution.md)

The production Node driver now owns one checked `NodeRuntime` containing its
actual lifecycle state, publication handles and versions, leases, availability
checks, checked-publication selection, retained admissions, episode status, live
callback scopes, withdrawn-publication lookup selections and pending handle-release
candidates, actual interface descriptors, dynamic declaration ownership and frozen profile policy.
Its operation entry points append
their real arguments, results and before/after observations to one erased history.
The driver cannot borrow the constituent owners mutably. No old JS objects or
runtime event log are retained for this proof.

## Guarantees and review path

| Behavior | Actual path | Checked relationship |
| --- | --- | --- |
| Replace a service slot | `Driver::set` → `NodeRuntime::replace` → `PublicationStore::replace_checked` | Actual handle and revision change together. Lifecycle state, publication identity, owner and leases remain unchanged. |
| Accept or invalidate a check | `check_actions` / `CompleteCheck` → `request_check` / `complete_check` | Requests capture the real value/version. Replies use the same owner's current lifecycle, publications and checks. Consumed or invalidated replies cannot authorize a new result. |
| Begin a consumer episode | `drive` → `NodeRuntime::begin` → `Availability::begin_setup` | One call checks availability, captures exact provider/publication choices, records Begin and allocates the corresponding leases. It retains the actual `Admission` under the same consumer ID and returns only the setup ticket. A retained admission cannot be overwritten by another Begin. |
| Fail, retry and release cleanup | `complete` / `retry_cleanup` → `cleanup` / `release` | Failure retains resources. Successful release uses the retained admission's leases and a complete publication manifest derived from the actual registry. Raw control release is rejected by this owner so it cannot bypass the resource protocol. |
| Prepare, fail, restart or seal | `prepare`, `fail_episode`, `restart`, `seal` → `episode_command`; `complete` → `complete` | Actual flags and error strings enter the same history. Stale replies preserve them; failure and restart prevent Finish. Retry clears the cleanup-failure gate only after the protocol issues a fresh ticket. |
| Issue, complete or wait from a callback | `NativeInvocation` → `begin_invocation` / `finish_invocation` / `invocation_live` / `check_invocation_wait` | Actual receipts, query inputs/results and the current committed dependency graph share one history. Completion consumes only its own receipt; stale live scopes cannot authorize waits. |
| Capture, withdraw and release publications | `withdraw_publications` / `release_owned` / `release_owned_reservation` | The capture selects actually visible own slots. Batch withdrawal hides every retained own slot without changing payloads or leases. Release enumerates all retained versions, including invisible ones, excluding reclaimed and foreign slots. |
| Deliver released JS handles | `Driver::command(Drive)` → `NodeRuntime::drain_released` → JS `Domain._pump` | Successful replacement/reclaim/release enqueues the actual old payload. Delivery filters against every current slot, including invisible ones, consumes the candidates and preserves order/multiplicity. |
| Read an actual service | `Resolve`, typed imports and call authority → `NodeRuntime::resolve` | Exact committed/own/cleanup/root selection and current payload/version enter the history; stale generations reject and reads preserve all state. |
| Change dynamic declarations or adopt initial publications | `publish`, `configure`, `reconcile_publications`, `drive` | Declaration changes and generation-zero adoption are recorded explicitly. Adoption preserves payload/revision, publication identity and existing leases. |

The executable owner is [`node_runtime.rs`](../crates/cordis-kernel/src/node_runtime.rs);
the transition relations and interval proofs are in
[`node_history.rs`](../crates/cordis-kernel/src/node_history.rs). The ordinary
[`Node adapter`](../crates/cordis-driver/src/node.rs) translates errors and wire
tickets; [`availability.rs`](../crates/cordis-driver/src/availability.rs) retains
only availability diagnostic text. The private checked maps retain the actual
`Admission` and [`Episode`](../crates/cordis-kernel/src/node_episode.rs) payloads;
the adapter reads them immutably. Pending wire tickets come directly from the
action ledger, with no separate Node pending-ticket cache.

`History::replacement_rejects_old_check` follows the actual request, a successful
replacement and the eventual reply through arbitrary intervening recorded calls.
Revision monotonicity makes the old reply invalid even after an A→B→A handle
sequence. Returning to the same handle does not return to the earlier version.
Cached acceptance still follows Cordis's explicit notification policy: replacing
a value does not itself schedule a new predicate evaluation.

Four finite-history contracts connect ownership to execution:

- `admission_origin`: every retained admission comes from an actual successful
  Begin in this same history, with its real source observation.
- `admission_retained`: until its own successful managed release, intervening
  operations preserve that exact admission, including failure, restart and retry.
- `rejected_reply_preserves_episode`: a rejected cleanup/setup reply changes
  neither retained admissions nor status/error payloads.
- `release_has_origin`: a successful release consumes the retained Begin owner
  at its original generation under the real cleanup/resource guard.

The actual [`scope owner`](../crates/cordis-kernel/src/node_scopes.rs) additionally
proves `scope_origin`, `scope_retained`, `scope_block_has_origin` and
`finished_scope_stays_inactive`. A live receipt comes from a real issuance at the
then-current generation. Cleanup and release do not implicitly finish callbacks;
late completion may still consume its original receipt, while a wait validates
current generation and committed dependency/ownership relationships. Issuance
also supports preparation and cleanup callbacks; it does not assert that every
callback owns an active admission or a service lease.

The [`resource path`](../crates/cordis-kernel/src/node_resources.rs) proves
`publication_origin`, `restoring_origin` and `released_publication_has_origin`.
The release list is derived from the authoritative registry, in allocation order,
without a second per-node cache. The scan includes retained invisible versions;
registry release still checks generation, cleanup success and all outstanding
leases before any resource is consumed. A captured cleanup lookup must come from
a real visible slot. Explicit revoke or reclaim removes its fallback selection;
a failed cleanup preserves the remaining selection and resources. Successful
release removes it. The batch withdrawal contract also preserves the original
history prefix and proves every selected slot hidden, with payloads, revisions
and leases unchanged. The registry scan allocates only a temporary ID vector;
no runtime proof trace or duplicate historical payloads are introduced.

The actual [`handle-delivery path`](../crates/cordis-kernel/src/node_handles.rs)
now owns the former driver's `released` queue. The same transition that replaces,
reclaims or releases a slot enqueues its actual old payload; rejected operations
and same-value replacements do not add candidates. `removed_is_queued` proves the
reverse obligation: a slot cannot lose its old payload without enqueueing it.
`payload_origin`, `queued_handle_origin` and `delivered_handle_origin` trace every
delivered number to a successful write and a later retiring operation in this
same execution. `queued_until_drain` preserves candidates through failure, retry,
stale replies and unrelated calls until an explicit delivery operation.

Delivery equals the exact ordered filter of the real queue by absence from the
real payload table. It excludes a handle retained by **any** slot, even a withdrawn
one; no global uniqueness assumption is imposed on numeric handles. A filtered
candidate is consumed, and later removal of the remaining reference enqueues a
new candidate. A→B→A therefore preserves A at delivery. Duplicate candidates may
produce duplicate notifications, as before; JS `Map.delete` is idempotent. This is
not an exactly-once delivery guarantee across process failures. The queue is
existing runtime state moved into the checked owner, not a proof log.

Publication and replacement check this same owner's episode admission, including
preparation before generation-zero writes. Preparation and generation-zero cleanup
use the same status owner. Failure
retains the prepared state and publication manifest obligations. During reservation
cleanup only successful resource release clears preparation; a first successful
Begin instead transfers preparation into the newly retained admission. These are implementation extension contracts
alongside the paper's Begin/Unload control projection.

`History::control_classified` connects each full event's **control projection** to
the existing paper/control history. Begin, Finish and Unload use the existing
paper rules; dynamic interfaces, reservation adoption and coherent forced restart
retain their explicit extension meaning. A value/check event may leave control
unchanged while changing the full observation. This is not a proof that those
changes are whole-context paper stutters or arbitrary Component functions.

## Actual reads and the paper connection

[`NodeRuntime::resolve`](../crates/cordis-kernel/src/node_reads.rs) now executes the
selection previously implemented in `Driver::resolve`. The JSON command and
Rust/Node typed-import and call-authority paths use this same operation. It checks
actual membership and optional generation, returns the real handle and revision,
and records the request/result in the erased history without changing any
managed state. Wire fields remain publication, owner and value; Rust also retains
the exact selection source in its result.

| Read context | Selection rule |
| --- | --- |
| Unowned lookup | Current visible publication, only while its owner is active and not retired; no consumer lease is acquired |
| Admitted consumer | First matching real Begin resource; use its retained lease, even if another publication now occupies that name |
| Own service without a committed match | Current visible own publication, including preparation/setup |
| Own cleanup fallback | Last retained matching entry in the actual withdrawal capture; never the newly visible foreign provider |

`admission_leases_live` derives live lease ownership from the complete execution
history. Other episodes' successful release cannot consume a retained admission's
leases. `committed_read_origin` ties the selected port/provider to its real Begin
and that Begin's declared dependency interface. `committed_selection_retained`
keeps the selected publication through arbitrary intervening calls until its own
successful release, including failed cleanup and retry. It preserves slot identity,
not the old payload: a legal replacement within that slot is visible on later reads.

`restoring_read_origin` traces cleanup fallback to a real earlier capture of that
owner's visible publication. `read_has_origin` traces returned handles to actual
publish/replace operations. `read_context_lift` relates the actual result to the
read operation of Definition 29 / equation (31), on the caller's projected handle
table; forward and inverse are identity, and the entire recorded observation is
unchanged. This caller-specific table includes retained bindings and is distinct
from global current visibility. It interprets handle lookup, not methods invoked
on a JavaScript object, arbitrary callback effects or an entire Component body.

The regression follows setup, two publications at one name, replacement under a
lease, withdrawal, failed cleanup, stale completion, retry, successful release and
a new generation. It also checks generation-zero adoption. Three added compiling
controls substitute the returned payload, ignore generation validation or bypass
the committed-binding branch. These are selected development controls; the
source-bound development record and full negative-suite acceptance remain distinct.

## Actual interfaces and dynamic provider handoff

The [`interface owner`](../crates/cordis-kernel/src/node_interfaces.rs) now holds
`NodeRuntime::{interfaces, dynamic}`. The driver reads the real parent, initial
provisions and current dependency vector directly; it no longer stores its own
Node/interface or declaration maps. Insert, successful dependency reconfiguration,
declaration release and node removal update these fields in the same recorded
operation as the lifecycle change. Failure preserves the corresponding fields.
Removing a node deletes only its own dynamic entries in place.

`interface_correspondence` derives membership, parent and dependency equality
with the paper control projection from actual history. `mount_origin` retains the
real initial setup requirements; `dynamic_correspondence` and `declaration_origin`
connect each tracked dynamic owner to a present declaring fiber and a successful
real declaration. Initial provisions are mount requirements, not a second copy of
the current dynamic interface. These facts are derived from the empty initial
state and recorded calls, not supplied by the adapter as assumptions.

`Driver::publish` now calls `publish_service`. Its exact trace covers admission,
visible conflict, capacity rejection, the declaration result and the actual
publication result. A declaration conflict is tolerated only for an existing
tracked dynamic reservation. This preserves the legal transition in which a new
publication is visible while consumers still commit to the old declaring owner.
It does not identify the new publication owner with those old commitments.

The whole reconciliation loop now calls `reconcile_declarations` in verified code.
`ports_cover` enumerates every original dynamic port; `batch_result` joins each
actual per-port call, including an error, to the same continuous history. A
successful return covers the complete list. A declaration-release failure with
`Relied` retains ownership; other failures stop at the real completed prefix.
`reconciled_transfer` requires the actual visible eligible successor, preceded by
a successful release of the old reservation. `release_requires_drained_commitments`
proves that this release has no remaining commitment to that exact owner/port.
The cleanup dispatcher also exports the precise control projection for each
command, including unchanged projection on rejection.

Dynamic declaration and dependency changes remain explicit **extensions** to the
paper's fixed-interface lifecycle. This establishes the actual reservation and
control connection, not a proof of arbitrary JS objects, callback effects or the
complete configuration/Component interpretation.

This implementation batch uses scoped Verus and workspace compilation/lints.
New runtime cases and strict negative controls remain on the
[deferred integration checklist](r2-state-inventory.md#deferred-integration-evidence).
The previous development report is historical after these source changes;
whole-development, full-negative and release/platform acceptance have not been
rerun for this batch. No R2 completion claim follows from these local contracts.

## Admission policy and notification selection

[`node_policy.rs`](../crates/cordis-kernel/src/node_policy.rs) owns the real
`Policy { profile, configured }`. `Driver` no longer stores either field or
selects notification retries. Its configure, mount, seal and notify commands call
this same executable owner; the JSON profile enum is translated at the boundary.

| Entry | Contract on actual execution |
| --- | --- |
| `configure_profile` | A configuration or successful first allocation freezes the profile. `frozen_profile` and `registration_freezes_profile` preserve it through all later history, including removal of the last plugin. Failed allocation does not freeze it. |
| `mount` | Check the real parent's membership, retirement and unloading state, then allocate the supplied declarations and seal the actual returned episode. `mount_trace` describes the exact gate/allocation/seal calls, results and completed failure prefix. |
| `seal_declarations` | Reject an unknown or already sealed reservation. A retired unsealed reservation remains a no-op. Otherwise update the actual dependencies before sealing; `seal_trace` records both real results in order. |
| `notify` | Under Harness, select exactly the consumers whose real dependency list intersects the notified ports and whose cleanup has not failed. Cordis retains the setup failure. `notification_frame` preserves every other episode field, all unrelated episodes and every failed cleanup. |

Rejected gates preserve the complete recorded observation. Configure and Notify
have explicit host-extension meaning: configure changes policy, while successful
notification updates checks and the specified failure flags. Their lifecycle
projection is unchanged; they are **not** whole-observation stutters. Parent
admission and sealing compose these extensions with the existing paper/control
steps. Ordinary JSON conversion, JS dispatch and callback truth remain boundaries.

Integrated regressions exercise rejected allocation, duplicate seal, retirement,
unloading, removal, both profiles, empty/duplicate notifications, separate realms,
retained cleanup leases and stale replies after retry. The real JS cleanup case
also sends a notification after failure and requires explicit cleanup retry.
Three new compiling controls reopen a frozen profile, bypass parent admission or
clear failed cleanup through notification; each must fail its named contract.
On that historical source, 152 scoped Node Verus checks, 81 Rust regressions, 20
actual Node regressions and all three selected controls passed, along with strict
workspace Clippy. The selected results do not claim full negative-suite or
whole-R2 acceptance.

## Captured callback ancestry

The production path is JS `beginInvocation` → Node-API `NativeInvocation` →
`Driver::begin_invocation` → the checked
[`NodeRuntime::begin_invocation`](../crates/cordis-kernel/src/node_scope_path.rs).
The constructor validates every selected parent handle before issuing a new
receipt and returns a private `Path`: exactly the parent's captured chain followed
by the new receipt. No mutable handle-list access is exported. Node-API passes
this actual native object to subsequent queries; JS no longer rebuilds a list at
each wait. The binding advertises `scopeProtocol: 2` and requires a matching addon.

| Contract | User-visible consequence |
| --- | --- |
| `begin_invocation`: exact parent prefix, real final issuance and preserved history prefix | Nested callbacks cannot silently discard a selected ancestor when creating their path. Parent validation and issuance enter the same Node history. |
| `check_invocation_wait`: success iff every captured handle is safe against the current control graph | A completed nested callback cannot hide a still-live setup, cleanup or task ancestor. A blocker identifies a real captured receipt and retained provider/owner relation. |
| `finish_invocation` / `invocation_own_live` | Completion and task self-join checks use only that callback's own receipt. Finishing a child cannot finish its parent or sibling. |
| `known_scope_origin` plus `finished_scope_stays_inactive` | Even inactive handles in escaped paths come from an earlier real issuance. Old/duplicate completion cannot consume a newer callback. |

Only live receipts remain in the ledger. A captured path costs O(depth) handles
and belongs to the callback context; an escaped context retains that vector until
it is collected, without retaining completed ledger records. The proof history
remains erased. The low-level JSON scope-list commands remain available with
caller-supplied ancestry; they do not inherit the stronger path-construction claim.

This closes preservation of the **selected native parent path**. JS still chooses
that parent through AsyncLocalStorage and dispatches the actual callback. The
contract does not prove complete JS causal ancestry, callback termination,
arbitrary callback effects or HMR module semantics. Reverse Rust calls retain
their separately checked request authority. The path protocol is a host execution
extension with an unchanged paper lifecycle projection, not proof that opaque
callback work is a paper stutter or a new Cordis paper axiom.

The [actual Node regression](../tests/node-compat/invocation-ledger.test.mjs)
checks an already completed nested callback waiting under a live setup, both
profiles, cancellation, exact completion and forged/foreign native objects.
[Driver regressions](../crates/cordis-driver/tests/invocation_scopes.rs) extend
completed paths, reject stale generations and duplicate completion, and confirm
the live-record count returns to zero. Two compiling negative controls truncate
the copied parent prefix or query only the leaf; each must fail its exact named
contract after a fresh matching positive.

## Evidence and remaining boundaries

The preceding captured-ancestry slice passed **179 scoped Verus checks, 29 Rust regressions, 805
Node/Loader regressions and both new strict negative controls**. Formatting,
strict workspace Clippy and all 297 canonical anchors also passed. Earlier policy
counts below describe their historical source. A prior concurrent run's five
timeouts remain recorded; the final Node run used unchanged concurrency, assertions
and limits after build/proof work completed. This is scoped implementation evidence,
not whole-kernel, full-negative, development, release or R2 acceptance.
These counts are historical source-bound results. The subsequent shared-driver
identity allocator is tracked in [native issuance](r2-execution.md#verified-native-identity-issuance).

[`node_execution.rs`](../crates/cordis-kernel/tests/node_execution.rs) exercises
version ABA, notification, actual Begin capture, replacement under a live lease,
provider withdrawal, failed cleanup, rejected old replies, fresh retry and final
resource release through this owner. It also exercises initial publication
adoption and dynamic dependency declarations. The decimal-string
[`Driver regression`](../crates/cordis-driver/tests/check_protocol.rs) covers ABA
through the real JSON command boundary. The
[episode regression](../crates/cordis-driver/tests/episode_failure.rs) also follows
failure/retry into a new generation and rejects late errors without replacing its
actual pending ticket. Scope regressions also exercise preparation-to-Begin
adoption, nested callbacks, failed cleanup and a later generation. Resource cases
combine multiple versions, explicit revoke, reclaim, a foreign provider and
retry with a registry-derived release list. Handle cases also cover shared and
withdrawn references, the largest numeric handle, ABA, rejected operations and
repeated delivery. The actual JS
[cleanup regression](../tests/node-compat/disposal-failure.test.mjs) reads the
replacement object during failed cleanup and retry in both compatibility profiles.
Sixteen earlier registered controls change the handle/check result,
bypass managed release, store an admission under the wrong owner, discard it on
failure, hide the cleanup-failure flag, misattribute a callback, skip its
completion, omit withdrawn slots, stop withdrawal early, deliver a retained handle,
enqueue the wrong payload, omit replacement retirement, return the wrong read payload,
ignore a read generation, or bypass its committed binding. Each must compile and then fail its
named contract. The three new policy controls are listed above. The previous
[development record](development-report.json) binds integration results to its
recorded source and is historical for this checkout. Selected negative checks
are separate from full negative-suite acceptance.

```sh
source scripts/toolchain-env.sh
export CARGO_INCREMENTAL=0
./scripts/verify.sh --verify-module node_runtime --num-threads 2
cargo test -p cordis-kernel --test node_execution --offline
cargo test -p cordis-driver --test check_protocol --test episode_failure --test invocation_scopes --offline
node scripts/build-node.mjs --offline
node --test --test-concurrency=4 --test-timeout=30000 tests/node-compat/*.test.mjs tests/node-loader/*.test.mjs tests/benchmarks/*.test.mjs
```

The history is continuous within **one Node owner**, initialized from its real
empty state. It does not invent an order between separate native Journals, Node
instances or processes. JavaScript object contents, N-API/JSON translation, actual
predicate and I/O truth, JS scheduling, Fiber effects/Child bodies, HMR module
behavior still require their own connection. Profile selection, mount/seal admission,
notification retry selection, parent/interface state and declaration reconciliation
now belong to the checked owner. The returned
handle batch now comes from the checked owner; JSON encoding, delivery to the JS
map and actual object deletion remain ordinary adapter operations. Actual scope receipts and publication selection now belong to the
checked owner; JavaScript still supplies callback dispatch and ALS parent selection.
The native path preserves that selected parent; it does not prove complete JS
causal ancestry or callback termination. The registry-derived manifest does not prove destruction of
the JS object or arbitrary effects inside it. Notification failure clearing now
derives its complete affected-consumer selection from the real checked interface map.
R2-D/E/F and whole R2 remain **in progress**.
