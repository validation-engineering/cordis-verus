# R2 production state inventory

Current R2 status is defined by [package 5 acceptance](r2-acceptance.md): managed-production/v1 is complete. Earlier checkpoints below retain their original evidence and scope.

## Historical implementation and verification checkpoints

See [package 4](r2-production-composition.md) for the current production composition and exact interpretation boundaries. Earlier checkpoints below retain their historical scope.

The [configuration interpretation](r2-configuration-semantics.md) now places actual module selection, scope key ownership, schema/default normalization and save merge/round-trip decisions in checked producers. Complete production-step composition remains open.

[简体中文](r2-state-inventory.zh-CN.md) · [Execution contracts](r2-execution.md)

The [host composition package](r2-host-composition.md) adds the actual foreign
reference owner, dispatch claims, static typed slot assembly and checked shared
Episode association. Their current scope is recorded below. Configuration value interpretation is
covered by package 3; whole-host trace composition remains open.

This is the working inventory for R2-C/E. It follows the actual native Runtime,
including escaped setup handles and cleanup. **It is not a complete shared-state
interpretation or a proof of the whole-host production trace.** The Node and loader
rows identify the next integration surfaces; their individual fields still need
the same audit. A field with no semantic interpretation is an open obligation,
not automatically an observation-preserving implementation detail.

A multi-service finite body now checks all Begin declarations before its first write, resolves each actual slot, and retains its successful inverse prefix in the real receiving group. `Report::production`, `source_trace`, `failed_trace` and `frame` connect those calls to actual allocation state, ordered local histories and the derived alias footprint. Rejected computations have their own capture/receipt witness. Fixed-port independence with aliases, arbitrary callbacks, foreign-domain total order and static/Node/configuration composition remain explicit boundaries.

Native extensible calculations now use `native_effect::{Capture, Computation}`:
real declaration/owner capture, actual input checkpoint, unlocked computation and
checked landing. `value_alias` supplies the complete local scalar alias projection
and its conditional single-key specialization; this does not close arbitrary
callback, static-host or other value-carrier semantics.

## Declared service call boundary

`value_access::{Read, Write}` joins actual Begin declarations, the selected slot
and retained allocation to scalar read/write receipts. `observe_reversible`,
`apply_native_value` and `run_native_value_program` are used by the native host;
the latter also serves registered finite root/Child bodies. Selection receipts
precede same-domain reads/writes, and each program write has production-object
semantics and a frame over actual owned/imported services. Cleanup registration
names the same allocation and actual root/effect group.

The declared port set and the allocation footprint are distinct. A port-level
frame additionally requires alias closure; it is not inferred from different
names or assumed by the host. Native computed effects now share this declared
boundary. General multi-service function bodies, opaque payload interior meaning and static host associations
remain open. See the [contracts](r2-execution.md#declared-native-calls-and-production-function-steps).

## Owners, mutations and remaining interpretation

| Actual owner and fields | Mutation / invocation entries | Established contract and remaining work |
| --- | --- | --- |
| `NativeRuntime::{host, services, owners, history, positions, joint, recipes}`; `NativeHost::{lifecycle, entries}` | Register/Child registration, Begin, root admission/call, Finish, withdrawal, retry, Unload, Remove, recipe update | Verified membership, issued episode identity, publications and continuous joint control/slot/owner history. Callback bodies and opaque `Mounted` interiors are not interpreted by that history. |
| `NativeEpisode`: shared immutable `NativeContext` (origin/work domain/registered realms/anchor/provisions/bindings), imports, own values, closed state, erased `Capture`; `NativePublication`: origin, slots, same capture | `begin_managed_execution`, `Execution::provide`, `finish_managed_execution`, `release_managed_execution` | Imports come from the real Begin bindings and published slots; Finish/Unload preserve that provenance. Interior mutation of a slot requires its own semantics. |
| `Execution::{work, groups, values, initialized, effects, checked_out, attempts}` | Root/request admission and completion, group admission, runner checkout/return/retirement, cancellation, cleanup, retry, seal | One verified owner binds pending work, all cleanup queues, native values and phase. Opaque iterator/Future bodies still require interpretation, including while checked out. |
| `AsyncSetup::{state, scope}`; `SharedEpisode::{generation, context, services, anchor, episode}`; `Episode::{cleanups, values}` | Setup reads/provides, clone/escape, nested effects/Child, service replacement and polling | One allocation shares immutable metadata and the mutable Episode. Native `services` is the same checked `NativeContext` as the actual Begin owner; native effects read its bindings inside the kernel. Realm/anchor come from the same registered Begin; checked scope admission/call and the actual checkpoint connect the live queue. The five production identity allocators now use checked CAS issuance. Every shared Episode lock now checks its issued execution association. Static metadata and exact Arc slots are assembled by `static_values::from_definition`. Standard Arc/Mutex semantics, other namespaces and external static lease truth remain boundaries. |
| `Episode::{driver, static_only, dynamic_host, external_children, service_updates, unsupported}` | Setup/effect registration, Child submission, service notification and static-host polling | Waking is scheduler bookkeeping, while external Child results and unsupported-operation flags affect outcomes. Their omission from the control projection is not proof that they stutter in the full observation. |
| `ServiceSlot::{payload, metadata}`; scalar slot or `SharedPayload<dyn Any + Send + Sync>`; `ServiceHandle` retaining a slot | `ServiceSlot::{get, accepts, replace}`, `AsyncSetup::{provide, publish, set, refresh}` and handle operations | The verified shared owner binds actual payload/version history, its lock and Journal. Real Runtime checkpoints collect complete published/owned/imported payload observations; replacements frame unrelated scalar/payload aliases. Predicates, arbitrary interiors, general inverse laws and outer Episode mutex association remain open. |
| `ReversibleValue`: actual value/depth and erased continuous history in its private lock; `Inverse`: actual target/before/after | Existing `apply`/`run_value_program`, new `prepare_effect`/managed commit, queued inverse dispatch | Verified scalar write and strict restoration domain; a later unmatched state blocks restore and retains the inverse. Histories interpret this value, not all service object interiors. |
| `effect::Prepared::{target, expected, decision, code}` | `ReversibleValue::prepare_effect` → `Execution::apply_prepared_effect` | Real computation runs after releasing the snapshot lock. Private fields bind its result/model to that input; commit checks current value/depth and current acquisition, writes and retains the actual inverse. Dropping preparation causes no managed write. Arbitrary side effects inside user computation are outside this contract. |
| `SharedChild`: locked slot, origin and persistent terminal witness; request and inverse share it | `enqueue_native_child`, `register_shared_child`, `retire_shared_child`, rejection/snapshot | Verified real allocation identity, request/inverse pairing and terminal consistency. Finite registered Child bodies now have an execution interpretation; arbitrary Child bodies and the full context remain open. |
| Registered root callback/revision; `Mounted::{episode, root_setup, root_running}`; `GroupState::{iterator, running, handle}` | `Runtime::{start, drain_requests, poll_groups, poll_cleanup}`, `RootSetup::poll`, completion landing | Stored callback, actual arguments, returned Future and poll result have provenance. The meanings of arbitrary roots, iterators, continuations and external cleanup are not established by payload transport. |
| `Mounted::{next_config_update, config_update, injection_config, declared_dependencies, declared_injection_config, context, owned, service, name}` | Registration, update, Begin, Child ownership transfer, failure/retry, restart and removal | Declarations/recipe identity enter checked registration; configuration callbacks and remaining settings still control ordinary host behavior. Name is diagnostic; actual failures/restart have the checked owner in the next row. |
| `poll_control::PollControl::{owner, episode, work_domain, failed, cleanup_failure, restart}` in `Mounted::control` | Guarded Begin, restart, failure reports, actual retry and Unload; `poll_flags` and joint snapshot | Exact retained error payloads and real polling inputs. Successful native operations own reset paths; same-domain/membership premises and availability truth remain explicit. |
| `Execution::statuses` and checked `host_status::Cell`; `HostStatus` owns errors/terminal/Child payloads with an erased linear permission; adapter owns waiters/driver/notify | Single-owner factory, owner-selected initialization/retirement, payload reports and receipt-backed observations | The actual stored link determines Journal, Begin/work and group ownership. Raw and observed retirement share removal-before-completion; rejection preserves ownership. No conditional status-Journal premise remains at those entries. Whole-Episode Arc/Weak/mutex association, scheduling and callback truth remain open. |
| `Runtime::{cleanup_errors, maintenance_changes, shutdown_failures}` alongside its checked driver | Maintenance, cleanup reporting, shutdown aggregation | These report actual host decisions. Error aggregation is observable and cannot be assumed irrelevant to full refinement. |
| Node `Domain` / Fibers, JavaScript object/publication tables, lease and invocation handles; native `Driver` and addon backend | Publish/replace/read, awaited callbacks, native command replies, cleanup/retry, dynamic interfaces and HMR | The checked Node owner now composes actual lifecycle/publication/version/lease/check changes in one history. The checked Bridge now owns actual Node-API weak references, Fiber bindings and pending-ticket recipe claims; sealed selections feed typed imports. Arbitrary JS object/function interiors, HMR module effects, full dispatch/diagnostic observations and whole-step interpretation remain open. |
| `Loader::{runtime, root, parent, registry, configuration}`; `Snapshot`, `Transaction`, `UpdateKey`, `SourceTracking` | Apply/recover, includes/groups, callback update, file load/reload, prepare/commit save | Runtime identity is preserved by private fields and the RuntimeAccess operation view; a checked native factory and one-epoch snapshot bind configuration/sources to the actual native member. Configuration owns the actual Batch and plans; Reversible owns their real forward/inverse Futures. Native Target checks domain/ID/generation/recipe; commit requires all updates and recovery requires inverse drain. Native allocation snapshots and ordered structural forward/recovery phases are connected. Package 3 supplies actual module/scope binding, schema/default normalization, recursive save merge and full source round-trip checks. Whole tree-to-component and joint production-step composition remain open (R2-I). |
| `Recorded::{inner, ledger, sources, source_ledger}`; actual configuration candidate/recovery payload/Batch and typed history positions | begin, forward/inverse/structural polls, commit, reconstruction, refresh | Same Journal as the actual Runtime; complete projection, original commit candidate and accepted-state origins are proved. Callbacks run outside the lock. Source load/clear/save history authenticates its bound configuration at the same Journal epoch. Package 3 supplies the configuration value interpretation; composition of the complete production sequence remains open. |

Source entry points:
[`runtime.rs`](../crates/cordis/src/runtime.rs),
[`static_host.rs`](../crates/cordis/src/runtime/static_host.rs),
[`native_runtime.rs`](../crates/cordis-kernel/src/native_runtime.rs),
[`execution.rs`](../crates/cordis-kernel/src/execution.rs),
[`scalar_effect.rs`](../crates/cordis-kernel/src/scalar_effect.rs),
[`Node runtime`](../packages/compat-cordis/runtime.js),
[`loader.rs`](../crates/cordis/src/loader.rs).

The shared status connection is described in
[execution contracts](r2-execution.md#actual-shared-handle-status-in-the-execution-trajectory).
The actual failure/restart fields now live in `poll_control::PollControl`, with
checked native Begin/retry/Unload reset paths and a common snapshot. Native
handles carry Begin/work provenance and the host checks the exact Weak Episode
allocation before any poll side effect. The remaining association boundary is
the ordinary `Arc`/`Weak` comparison, other identity namespaces and static
embedding inputs, not a claim that numeric domains authenticate arbitrary shared objects.
See [shared context contracts](r2-execution.md#shared-begin-context-and-effect-admission) and
[Episode/control contracts](r2-execution.md#episode-association-and-actual-polling-control).

## Node and configuration state now in checked owners

| Actual fields | Mutations | Contract / remaining boundary |
| --- | --- | --- |
| `PublicationStore::{registry, payloads, revisions}` | publish/replace/revoke, acquire/release/reclaim, cleanup | Actual payload and replacement version follow the publication and its retained leases. |
| `availability::Availability::{domain, records, pending, next_action, notification}` | request/current/complete/notify/remove_consumer | Actual lifecycle/domain/dependency/provider/publication/version checks; complete ticket matching and one-time acknowledgement. Predicate truth is external. |
| `NodeRuntime::checked` and adapter `availability.errors` | Checked registration/revocation and diagnostic replies | Select checks and report errors; no shadow revision and no diagnostic admission authority. |
| `NodeRuntime::{admissions, episodes}`; real `Admission` and `Episode` status/error payloads | Begin, prepare/seal/fail/restart, accepted completion, cleanup/retry/release/remove | Same continuous protocol history proves real Begin origin and retention until successful release. Stale replies preserve status and resources. Pending tickets are read directly from the action ledger. |
| `NodeRuntime::{scopes, restoring}` and registry-derived publication lists | BeginScope/FinishScope/ScopesLive/CheckScopeWait, capture/revoke/reclaim and managed release | Same history binds actual callback receipts, current wait graph and withdrawn lookup selections. Complete release manifests come from the actual registry. Publication/scope origins and non-reused callback identity have finite-history proofs. |
| `NodeRuntime::released` | Successful replacement/reclaim/release; `drain_released` before the Drive reply | Actual payload candidates and ordered filtering share the history. Write/retirement provenance, complete enqueueing and exclusion of retained slots are checked. Bridge removal now checks actual publication/Fiber/claim retention before JS root deletion; JSON transfer and garbage collection remain external. |
| Actual Node read arguments, selected publication/source, handle and revision | `Driver::resolve`, typed imports/call authority → `NodeRuntime::resolve` | State-preserving history event; real Begin lease/capture/write provenance, exact selection and caller-relative read lift. Object methods and wire translation remain external. |
| `NodeRuntime::{interfaces, dynamic}`; actual parent, initial provisions, current dependencies and dynamic owners | insert/configure, declare/release/remove, `publish_service`, `reconcile_declarations` | Same-history correspondence and mount/declaration provenance; exact publication branches and complete reconciliation with partial-failure prefixes. Dynamic interfaces remain explicit extensions; no duplicate driver maps remain. |
| `NodeRuntime::policy`: actual `profile` / `configured` | configure, successful allocation, mount/seal gates and notification retry selection | Same history proves permanent profile freezing, exact call/failure prefixes and complete affected-consumer selection. Cleanup failures and unrelated episodes are preserved. |
| `NativeInvocation` owns private `paths::Path`; `NodeRuntime::scopes` owns live receipts | `begin_invocation`, `finish_invocation`, `invocation_live`, `invocation_own_live`, `check_invocation_wait` | Exact selected-parent prefix, complete path queries and real issuance origins. Escaped contexts own inactive path entries; the ledger retains only live receipts. ALS parent selection and arbitrary JS behavior remain external. |
| `Bridge<WeakReference<NativeObject>>::{objects, fibers, claims}`; private JS box/root maps | Object issue/read/publish/replace/remove; Fiber bind/unbind; callback begin/complete; explicit snapshot | Exact issued reference and pending-ticket association; retained publication/Fiber/recipe prevents release; checked complete snapshot coverage. JS reference dereferencing, box adapter and payload interiors remain audited boundaries. |
| `static_values::Values<ServiceSlot>` and its shared `Context` | Static definition assembly, read and provide | Actual realms/declarations/inherited ports and exact Arc inputs compose; duplicate/missing/extra imports and foreign-owner writes reject. External static lease authority remains separate. |
| `SharedEpisode::association` and actual Episode mutex | Native/static creation and every shared lock access | The checked association is issued with the real context and compared with the locked execution before access. Standard Arc/Mutex semantics remain trusted. |
| JS callback dispatch and remaining driver dispatch/diagnostics | Callback scheduling, ALS parent selection, response encoding | Native captured paths preserve the selected parent. Complete JS causal ancestry, scheduling and object/effect interpretation still require composition. |
| `Configuration::{current, revision, pending, updates, structure}`; pending candidate/recovery | begin/work/commit/recover/refresh | Pending edits preserve accepted state/revision and cannot mutate the batch. Actual callbacks drive an ordered success prefix and reverse retry stack. Commit requires complete updates; recovery requires empty inverse obligations. See [configuration execution](r2-configuration-execution.md). |
| `Transaction::{before, created}`; actual checked Tree nodes and native Allocation records | apply_prepared/recover, mount, awaited update/rollback | Actual parent-local preparation, complete retirement dispatch and saved-recipe reconstruction run in the checked tree, with unique allocations and exact failure prefixes. Old factories and inverses remain held across cancellation; factory Component meaning and the joint Journal remain open. |
| Owned configuration adoption changes, actual registered recipe versions and returned displaced values | `Runtime::adopt_config_recipes` → `NativeRuntime::adopt_configurations` | Complete checked preflight and actual ordered recipe/metadata swaps; errors return unchanged native owner and intact inputs, success preserves live state/publications. Recipe registration/replacement/call records now share the Journal; metadata effects/destruction, Plugin conversion and full semantics remain boundaries. |
| `Snapshot::{tree, nodes}`, registry factories/services/revisions | prepare, load/reload | Actual expansion/planning preserves payloads, order, read origins and real parent contexts. Parsing/conversion, grouped Component and source projection/merge meaning remain open. |
| `Save::{origin, documents, phases, cursor, halted}`; immutable document payload/text | `SaveStamp::start`, `step`, `Configuration::accept_saved_sources` | Original review is bound before execution and preserved. Actual returns drive phases; replacement differs from durability. Acceptance checks the original revision/domain and no pending recovery; unreviewed/stale saves preserve sources. |
| `Loader::configuration.sources` → `sources::Source::{root, contents, checkpoints, resolutions}`; `Checkpoint::{value, pending_sync}` | `load`, `clear`, acceptance of actual saves | One erased history indexed in the same Journal; checkpoint origin is a real load/processed document tied to an exact earlier accepted configuration state. Untouched keys are framed and Sync retains retries. Reports cannot mutate state; loaded text is preserved. See [source contracts](r2-configuration-execution.md#source-checkpoints-derived-from-the-actual-save). |

The remaining driver dispatch/diagnostics, callback ancestry, handle-batch serialization/JS deletion,
compaction counters, plus JS Domain/Fiber/object state,
still need their joint interpretation. These tables do not mark R2-C/D/E/F complete.

## Scalar invocation: the connected execution slice

| Actual step | Checked result | Scope of classification |
| --- | --- | --- |
| Snapshot, then `ScalarEffect::compute` outside value/episode locks | Actual output equals the implementation's model when that implementation is verified | Local preparation; arbitrary extra callback effects have no interpretation here. |
| Acquire episode owner; recheck ticket/work/queue identity, phase and group admission | Closed/cancelled acquisition cannot reach the managed write | Rejection preserves the execution owner; the ordinary mutex/host association remains a boundary. |
| Compare the current value/depth with the private captured state | Mismatch records `StaleComputation` and rejects; overflow/rejected computation also leaves scalar state unchanged | The actual rejection preserves the recorded Journal state and pending obligations. Exact restoration to the captured state permits commit. |
| Write actual result and append actual inverse to the owning cleanup queue | Real target/before/after, branch and inverse; prior queue prefix and unrelated groups/runners retained | Dependent-grammar scalar operation and managed registration; not yet a full R1 context step. |
| Dispatch that queued inverse | Restore succeeds only at its captured post-state; interference retains the inverse for retry | Existing scalar history and cleanup contracts apply to new primitives too. |

`ThenScalar` and `ChooseScalar` compose local computations. They perform one
managed write with one inverse; their intermediate results are not separately
published states. The terminal component theorem covers the scalar operation's
full declared carrier. An outer plugin continuation or Child body still needs
its own function interpretation.

The actual alias projection and slot replacement now have separate contracts in
`value_alias`, linked by `Write::general_semantics` and `Replacement::production_aliases`.
Additional effects from a user computation still need their own contracts; a
local scalar result does not prove the entire callback.

## Deferred integration evidence

Interface/publication cases still awaiting integrated runtime and negative evidence:

- Two dynamic providers and a committed consumer: withdrawal, failed cleanup,
  stale reply, fresh retry and eventual handoff. Reject bypass of `Relied` or a
  substituted successor owner.
- Initial versus dynamic requirements, dependency reconfiguration rejection and
  removal of one owner with foreign declarations retained. Reject a wrong stored
  dependency vector, wrongly tracked static port or cross-owner deletion.
- Generation-zero preparation, retired/unloading successors, and static versus
  tracked-dynamic conflicts through the real JSON publish path. Reject a bypassed
  eligibility or conflict guard.
- Multiple ports in the actual reconciliation loop, with a blocked port and a
  later successful transfer; injected errors preserve partial progress. Reject
  early successful return or dispatch of a different port.


The alias/effect batch now exercises native Child `ScaleAdd`/`ThenScalar`/both
`ChooseScalar` branches, replacement during calculation, same-owner reentry,
interference, rejection, panic, withdrawal and actual inverse cleanup. The
source-bound record in [execution contracts](r2-execution.md#native-extensible-effects-and-the-alias-aware-paper-mapping)
also checks owner/cause/alias mutations. The table below remains the broader R2-G/H
checklist: static computation, exact restoration between prepare/commit, group
cancellation and remaining payload/branch mutations still require acceptance.

| Caller / boundary | Guarantee to exercise | Intended regression or mutation |
| --- | --- | --- |
| Native and static `update_reversible_with` | New primitive, checked overflow and actual branch selection; one managed write | `ScaleAdd`, `ThenScalar`, both `ChooseScalar` branches and rejected intermediate computation; mutate returned value/branch to disagree with its model. |
| Computation before managed commit | No plugin code under host/value locks; panic preserves its error kind | Reenter setup, mutate through another handle, panic or drop captures; no managed write/inverse from the rejected outer call. |
| Escaped handle / concurrent operation | Commit uses captured value/depth and still-open admission | Mismatch, same-value deeper write, exact restoration, group cancellation and owner withdrawal between prepare and commit. Mutate state/admission guards. |
| Managed registration and cleanup | Actual inverse, original queue prefix, unrelated group/frame retained | Wrong-target inverse, dropped earlier entry or unrelated-runner mutation must violate contracts. Exercise failed restore, intervening restoration and successful retry. |
| Actual scalar history | Accepted computation has source meaning; rejection preserves scalar observation | Omit/change a history event or its before/after values; the named history/interpretation contract must reject the compiling mutant. |

Additional deferred cases: same-payload replacement and predicate/destructor
reentry; notification/value/publication interleavings and foreign control domains;
transaction cancellation around candidate edits, capacity rejection and recovery
without revision advance. Selected mutations must remove freshness guards or
substitute a committed snapshot. Existing host regressions are checked separately;
these new scenarios and negative controls are not reported as complete.

The implementation batch uses compilation and scoped Verus verification.
Integrated runtime/negative evidence and full source-bound acceptance remain
separate pending work. No milestone status changes follow from this inventory.

The actual `Admission` now stays in `NodeRuntime::admissions`. Actual preparation,
seal, failure/restart and cleanup flags and errors are in `NodeRuntime::episodes`.
Their history proves issuance by Begin, preservation until successful release,
and unchanged status on stale replies. Read-only resource access and direct
ledger ticket observations replace the adapter's separate fields; JS object and
remaining adapter-cache semantics stay open. See the [Node contracts](r2-node-execution.md).

Additional deferred admission cases: foreign-domain stores/check ledgers;
missing, rejected or stale-generation publications without lease allocation;
all prerequisites satisfied must admit; multi-dependency capacity exhaustion;
zero-dependency stale admissions and old replies cannot release a later generation.
Retained-owner/failure/retry and late-error cases are now covered by the Node
integration batch. Further mutants should omit a selected
provider, bypass availability, always reject valid admission, mis-tag a lease or
skip the domain/generation release guard. Existing Driver regressions are run
for integration but do not replace these new negative controls.

## Risk-first shared-history connection

`ReversibleValue::Cell` now owns an erased authoritative history resource;
`Snapshot` owns persistent evidence for its prefix. `Cursor` retains actual
program/target/owner/continuation, a checkpoint, and erased indices of its calls.
The checked owner advances it and registers the actual inverse before return.
`observe` extends its checkpoint without admitting work. All scalar events,
including intervening writers and blocked/successful cleanup, have a continuous
table interpretation. The real Child example exercises this path and exposes
two ports aliasing the same object. The whole-host interpretation must model
port/version-to-object bindings and retained old allocations before claiming a
full frame. Arbitrary root/Child bodies and the complete host history remain
open; see [the connected probe](r2-execution.md#risk-first-connection-interleaved-continuations-and-recovery).

Deferred follow-up cases: overflow then retry after an intervening restore;
same-content distinct allocations; same-value deeper writes; group cancellation;
slot replacement retaining the cursor's original allocation; multiple nested
Child bodies sharing one value. These are not reported as complete acceptance.

## Typed slots, captures and aliases

The native table instantiates `ServiceSlot<T,M>` with a checked `SharedPayload`
for non-scalar storage, alongside the scalar `slot::Slot`. `Slot::Cell` owns the actual typed
`VersionedValue<Arc<ReversibleValue>>` and erased authoritative history.
`Capture` retains slot, revision, actual object and prefix evidence; `Cursor`
optionally retains the actual `ServiceBinding`. Mutations enter through slot
replacement, object operations/restoration, and authenticated cursor advances.
`begin_native_value_program` resolves the actual committed provider inside the
checked Execution rather than accepting a host-supplied binding.

`heap::Observation` separates port selections from object state. Its write
footprint includes every alias of the modified allocation. A slot replacement
changes all current selections of that slot, while captured old versions stay
fixed. This remains the earlier retained-view theorem. The common Journal now
derives local slot/object integrity and actual service observations through live
replacement/control interleavings; full host/function interpretation remains open. See [the current scope](r2-execution.md#actual-slot-versions-and-shared-object-identity).

Implemented integration cases supersede the earlier deferred slot-replacement
item: the real Child example now replaces a slot while its cursor runs, fails
cleanup and retries on the old allocation; dynamic publication has a regression
for the same target retention. Equal-object republication invalidates old
predicate captures and generic/static reads retain the actual Arc. Whole-R2
acceptance, alias-aware declared footprints, multi-object interleavings and
nested Child body interpretation remain pending.

## Publication and import slots in a shared checkpoint

The specialized actual service maps collect receipts from every reversible slot
before the Journal read epoch. The checkpoint relates retained publications,
owned values and Begin imports to same-domain slot records; captures carry the
exact revision/object commit. Collection creates no executable map or payload
owners. A target object receipt is required at each actual slot allocation or
replacement. The shared history proves local reference closure at every prefix,
so a slot replaced after collection still resolves at the read epoch. Production
projections cover every publication/import/owned key, explicitly distinguishing
opaque payloads, foreign slots/objects and local values. Alias writes/restores and
retained old-object resolution have corresponding theorems; historical records
do not assert that retired allocations remain live. Both host snapshot entries
use these producers. See [contracts and current evidence](r2-execution.md#actual-publication-slots-and-captured-commits).

## Connected native execution domain

`joint_execution::Journal` owns the common lock and erased authoritative map/
history; each real value, typed slot and NativeRuntime owns a private `Member`.
`Cell::record_following`, `Slot::replace` and executable `NativeRuntime::transition` update
the matching member before returning. The shared state maps member keys to
object value/depth, slot revision/object selection or actual native control,
episode ownership and publication projection. Exact generic publications and
Begin captures remain in typed history, completely indexed into real commits.
Snapshots retain their real Journal instance, and value snapshots prove equality
with their joint entry. No plugin callback runs under the journal lock.

`RegisteredPlugin<Body<C>>` directly stores single-service `Body::Value` and
multi-service `Body::Services` functions, alongside opaque callbacks.
`run_value_root` and `run_service_root` obtain the actual current recipe and
issued owner, resolve its registered declarations and settle the same root
from the computed result. Multi-service binding checks every branch before root
issuance; subsequent operations capture the current Begin-bound slot.
`service_composition` joins full finite control flow, real rejection and
qualified allocation identities. `service_stack` identifies the semantic
inverse stack with the actual retained queue suffix, including failed prefixes.
See [stored function contracts](r2-function-semantics.md).

`Function::{key, program}` is the stored finite root/Child body;
`Function::run` checks the actual root status and Begin-bound slot, and deposits
the actual prefix inverses in group zero. The host constructor is
`Plugin::native_value_program`; allocation uses `Runtime::reversible_value`.
`Member::latest` retains the authoritative joint prefix; scalar `positions`
map local events into it. Program reports and cursors derive ordered positions
for their actual steps; the registered report associates the finite root/Child
with its body and results. Actual work and queue projections now have their own
private members in the same map. CleanupGroups now adds its actual live
membership, guarded removal/sealing and sticky consumed failure. Complete
host/resource interpretation, the remaining Node observations and loader state
are still open. Host status/control members already contribute their checked
observations. Cross-domain slot targets retain separate histories; finite
function addresses include the actual Journal and never conflate local keys.
See [the connected domain scope](r2-execution.md#one-native-execution-domain).

`SetupWork::joint` and `CleanupQueue::joint` are optional private members, attached
by native Begin; `CleanupGroups::execution` carries the same Journal into every
new iterator queue. Their observations include real tickets, root failure,
pending/issued work, slot occupancy, retained cleanup failure and fresh attempts.
`Execution::observe_execution` certifies work and all live queues under one read
guard; `observe_execution_after` preserves an earlier joint prefix. Opaque
payload meaning and host flags remain separate obligations. Group removal and
sealing now certify the real queues under one write guard before updating their
owner record; historical queue entries are distinguished from live membership.
See the [membership contracts](r2-execution.md#live-cleanup-membership-and-guarded-retirement).

`NativeRuntime::publication_snapshot` exports the complete typed-history
projection. `History::interval` excludes skipped native commits and
`Snapshot::complete_projection` covers every event for that member. The erased
revision/positions do not retain runtime Arc values. `episode_snapshot` certifies
the current native member, work and cleanup family in one read epoch;
`Runtime::plugin_execution_snapshot` uses it with the mounted episode mutex.
The native domain premise follows from Begin and managed frames; this does not
prove arbitrary host mutex association or generic slot interior semantics.

## Actual inverse origin and registration edges

`Inverse::origin` is a persistent, erased receipt of its actual successful
forward commit. `Execution::register_inverse` is the shared typed insertion
entry for direct writes, prepared effects, finite programs and cursor steps.
It takes the cause from that exact payload, preserves the queue prefix, and
exports the queue identity, domain and real token in `registration::Evidence`.
Finite registered root/Child reports also export the certificates.

For one Journal, `RegisterInverse { write }` is a classified cleanup append
whose index must name an earlier actual successful write. Foreign-domain and
unlinked queues remain explicit cases without that global edge. The extra
receipt fields are erased; the existing journal lock authenticates the order.

The managed pending owner is now represented by `Applied::pending` and the
finite interpreter's actual `Batch::items`. The common Journal owns the erased
`GhostMapAuth` indexed by forward position; each pending payload holds its
unique points-to capability. Forward commit allocates the entry, queue commit
consumes it, and `Evidence::pending_interval` proves retention at every state
between them. `Snapshot::pending` exposes the authoritative projection. The
four managed scalar paths enable it only for the actual same-domain queue;
raw operations, foreign objects and unlinked queues remain explicit boundaries.

`Execution::attempts` now retains erased receipts appended by the actual
producer under the value lock. Every admitted direct/prepared call appends one;
success names its registration and failure names its actual rejected cause.
Cursor errors use the real checkpoint; finite programs must register their
successful prefix before returning a report. Work, cleanup, root/Child and
native lifecycle contracts frame the history. `Ledger::rejection_step` proves
that the actual rejection commit preserves the whole joint and pending maps.
This receipt sequence is not a complete census of arbitrary host operations.

Typed scalar dispatch now returns `restoration::Evidence` naming the exact
inverse taken from the slot, its real restore/block receipt and the matching
acknowledgement. Same-domain receipts occur in that order within one continuous
Journal trace; failure restores the original inverse to the selected slot.
`Execution::dispatch_cleanup` exports the evidence and preserves the queue and
trace on an error/no-action return. Existing retry advances the attempt without
changing the payload. See the
[restoration contracts](r2-execution.md#from-issued-inverse-to-actual-restoration-and-acknowledgement).

The typed result now also proves **issued responsibility at every intermediate
state**. The producer establishes the interval from its actual receipts, using
the real next-attempt counter and shared transition rules. The selected ticket
stays active/issued and its slot vacant until the first acknowledgement; any
later authentic extension keeps that completed attempt inactive. Exact inverse
identity and failure retention remain the typed owner contract. Successful
restore consumes the inverse value before acknowledgement: responsibility
persists, not the consumed Rust object. See the
[interval contract](r2-execution.md#issued-responsibility-at-every-intervening-state).

Still open: compose the established live cleanup membership with
shared host state, generic slot interiors and arbitrary callbacks for a complete resource census. Current pending entries
express unregistered managed writes; the issued interval adds the typed scalar
responsibility, not a complete paper context or atomic paper step. See the
[write/registration contracts](r2-execution.md#from-the-actual-write-to-the-actual-inverse-registration).

## Node protocol composition update

[`NodeRuntime`](../crates/cordis-kernel/src/node_runtime.rs) now owns the actual
`LifecycleState`, `PublicationStore<u64>`, `Availability` and checked-publication
set. Their mutation methods append one continuous history and preserve a common
domain invariant. Dynamic declarations and publication adoption remain explicit
extensions; value/check changes are not whole-observation stutters. The availability adapter
retains only diagnostic errors; wire action tickets come from the core.
Retained admissions and episode status/error payloads now use those same checked
mutations. Actual callback scopes and withdrawn-publication selections now share
this history, and release lists are derived from the actual registry. The remaining
JS Domain/Fiber caches, callback ancestry and effects above remain open. See the [review path](r2-node-execution.md) for guarantees,
evidence and the boundary between this Node history and the native Journal.

## Registered recipe history and actual call versions

`NativeRuntime::recipes` owns the exact typed registry history and a common
Journal member. Mutation entries are registration/SharedChild registration,
replacement, removal and callback/Value/Service-root return. Mutable metadata
borrows preserve every recipe. Snapshots certify recipes and the native owner
in one read epoch; call commits check the actual Episode ticket and work domain
under the write lock. See the [recipe-history review](r2-configuration-execution.md#registered-recipes-in-the-common-execution-history).

`ProgramReport::receipts` and the multi-service `Report::receipts` retain erased
persistent witnesses collected by the actual interpreters. Each successful
instruction contributes its write and optional inverse-registration receipt;
failed service attempts duplicate the authentic last witness in
`Execution::attempts`. A Value report also retains its complete object
observation. `RegisteredReport::completion` names the real recipe Call commit.
`record_recipes_following` certifies all local predecessors in that commit's
held write epoch. The return interval includes local inverse registration even
for a foreign forward value, without claiming cross-domain ordering. See the
[function return contract](r2-function-semantics.md#effects-joined-to-the-actual-invocation-return).

The native identity allocation boundary is narrowed by [checked issuance](r2-execution.md#verified-native-identity-issuance). Its no-reuse guarantee is per issuer; it does not discharge shared Episode/Journal ownership.

The [Execution-owned status contract](r2-execution.md#execution-owned-shared-effect-status) now closes the effect-status Journal association independently of numeric allocator uniqueness. It does not close the whole shared-Episode interpretation.

## Integrated status-binding frames

These 61 actual methods carry link-frame contracts. `retire_effect` removes only its retiring entry; the other methods preserve the entire map. Both program loops preserve the same relation. Status creation and observed retirement separately specify exact insertion/removal; see the [complete history](r2-execution.md#status-continuity-across-real-calls-and-interleavings). This is not an inventory of full-host semantic coverage.

| Kernel file | Actual methods |
| --- | --- |
| [`execution.rs`](../crates/cordis-kernel/src/execution.rs) | `attach_execution`, `take_effect`, `put_effect`, `activate_effect`, `retire_effect`, `withdraw`, `activate_external`, `seal_external`, `provide`, `issue_root`, `start_root`, `cancel_queued_root`, `complete_root`, `fail_root`, `abandon_root`, `take_child`, `take_group`, `complete_request`, `register`, `cancel`, `pop`, `complete_future`, `complete_failure`, `complete_result`, `retry`, `remove`, `enqueue_owned_child`, `enqueue_effect`, `admit_effect`, `land_effect`, `enqueue_native_child`, `apply_value`, `apply_value_following`, `dispatch_cleanup` |
| [`managed_native.rs`](../crates/cordis-kernel/src/managed_native.rs) | `finish_managed_execution`, `release_managed_execution`, `withdraw_managed_execution`, `admit_managed_root`, `retry_managed_execution` |
| [`native_effect.rs`](../crates/cordis-kernel/src/native_effect.rs) | `apply_native_effect` |
| [`native_runtime.rs`](../crates/cordis-kernel/src/native_runtime.rs) | `finish_managed_execution`, `release_managed_execution`, `admit_managed_root`, `withdraw_managed_execution`, `retry_managed_execution` |
| [`poll_control.rs`](../crates/cordis-kernel/src/poll_control.rs) | `retry_controlled_execution`, `release_controlled_execution` |
| [`scalar_effect.rs`](../crates/cordis-kernel/src/scalar_effect.rs) | `apply_prepared_effect` |
| [`service_function.rs`](../crates/cordis-kernel/src/service_function.rs) | `run_service_root` |
| [`service_program.rs`](../crates/cordis-kernel/src/service_program.rs) | `run_service_program` |
| [`setup_context.rs`](../crates/cordis-kernel/src/setup_context.rs) | `admit_scoped_effect`, `enqueue_native_effect` |
| [`value_access.rs`](../crates/cordis-kernel/src/value_access.rs) | `apply_native_value`, `apply_native_value_chained` |
| [`value_cursor.rs`](../crates/cordis-kernel/src/value_cursor.rs) | `advance_value_program` |
| [`value_function.rs`](../crates/cordis-kernel/src/value_function.rs) | `run`, `run_native_value_program`, `run_value_root` |
| [`value_program.rs`](../crates/cordis-kernel/src/value_program.rs) | `run_value_program`, `run_value_program_following` |
| [`value_registration.rs`](../crates/cordis-kernel/src/value_registration.rs) | `register_inverse` |

## Complete recorded-carrier classification boundary

`joint::classification::Observation` retains all thirteen Record variants and pending obligations together. Actual snapshots and function returns export the complete classification. Both presence and value of unrelated records are framed; whole recorded-state stutter requires both maps to remain equal. This does not interpret the ordinary host/JS/configuration function interiors left open in this inventory. See [actual producers and limits](r2-execution.md#complete-classification-of-the-recorded-native-carrier).


## Shared typed payload owner

`SharedPayload<T: ?Sized>` now owns the actual Arc, version, private lock, erased
typed history and common Journal member. Native `provide`/`publish` allocate it
through the real Execution; reads, replacements and checks retain that owner.
All published, owned and imported slots enter the complete service projection
at one Journal read epoch. Local payload replacements change every alias while
framing unrelated scalar/payload observations; foreign domains stay explicit.
See [contracts, paper links and deferred acceptance](r2-execution.md#shared-typed-payloads-in-the-actual-execution).
A checked retirement returns the payload and leaves a terminal Journal record;
the host final-slot guard invokes it, preserving payload destruction outside locks.
This closes the ordinary payload-storage lock boundary, not the outer Episode
association, arbitrary T interiors or heterogeneous function/inverse semantics.

## Typed payload restoration state

The actual payload cell also owns semantic head/depth and a revision reserve.
Typed inverse construction authenticates its original state history; the real
cleanup variant owns that inverse plus the exact retained service-slot Arc.
`apply_native_payload` resolves the committed service; `apply_payload` registers
the inverse; `dispatch_payload_cleanup` selects, restores and acknowledges it.
Failed restoration keeps the original queue entry. Histories and registration
witnesses erase; no runtime history of old payloads is added. See
[paper interpretation and boundaries](r2-execution.md#reversible-typed-payload-replacement).

The inverse also retains its actual Journal for authenticated reads after payload
retirement. Its real cleanup returns erased issue/read/write/acknowledgement
receipts. A failed attempt has a read cut and no invented write; same-domain
custody and completed-ticket non-reuse follow from the actual full history.
See [typed cleanup intervals](r2-execution.md#typed-cleanup-issue-read-and-acknowledgement).
