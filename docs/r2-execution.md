# R2: production execution contracts

[简体中文](r2-execution.zh-CN.md) · [Paper milestones](paper-refinement-roadmap.md)

R2 connects the paper's constraints to production managed calls. **R2 remains
in progress.** The contracts below run in the Rust and Node adapters; they close
payload, registration and result-transfer gaps, but do not yet establish whole-host semantic
refinement or Component membership for arbitrary plugin callbacks.

## Issued episode ownership and delayed root calls

The production `NativeRuntime` now records the setup ticket and work domain
actually issued at Begin. Its invariant gives every Loading, Active or
Unloading plugin exactly one current owner; Inactive and removed plugins have
none. A publication must belong to that owner. Root admission and invocation,
Finish, withdrawal, settlement, failure, retry and Unload check the supplied
execution or invocation against this retained record. Editing opaque host
bookkeeping cannot replace it. Successful Unload removes it; failures and
retries retain it.

`RegisteredInvocation` also retains the admitted lifecycle ticket. Immediately
before invoking the stored callback, `NativeHost::call` rechecks the pending
setup action, current generation, Loading phase and retirement flag, in addition
to the existing owner/domain/recipe revision checks. A root whose invocation has
not started is rejected after withdrawal or retirement, and cannot execute in a
later episode even if its work domain is reused. Local work withdrawal also
closes new root admission. Already executing callbacks and their awaited results
still follow the existing completion protocol; this is not callback preemption.

The continuous native history now includes these actual owner records together
with control and publications. `owner_has_begin` proves that a retained owner
originated at a successful Begin. `owner_retained` proves that it cannot change
before that plugin's successful Unload. The owner changes accompany the existing
Begin/Unload control steps; admission checks and rejected invocations preserve
this observation. This strengthens the production projection without changing
the R1 interpretation or asserting a full-context correspondence.

Review the executable checks in
[`native_owner.rs`](../crates/cordis-kernel/src/native_owner.rs),
[`native_runtime.rs`](../crates/cordis-kernel/src/native_runtime.rs),
[`plugin_registration.rs`](../crates/cordis-kernel/src/plugin_registration.rs) and
[`native_host.rs`](../crates/cordis-kernel/src/native_host.rs), and the induction
in [`native_history.rs`](../crates/cordis-kernel/src/native_history.rs).
The `native_host` and `native_runtime` integration tests exercise delayed calls,
retirement, reused work domains, foreign executions and successful release.
Named negative controls remove the corresponding guards and owner updates.

Reproduce the focused runtime cases with the pinned toolchain:

```sh
cargo test -p cordis-kernel --test native_host --test native_runtime --offline
```

The shared `Arc<Mutex<Episode>>` still belongs to the ordinary adapter. These
checks authenticate its submitted numeric identity against the live registry;
they do not prove mutex scheduling, opaque argument semantics or allocation
identity when independent raw hosts deliberately reuse **all** identity numbers.
The ordinary unique-domain allocator remains a boundary. Arbitrary function
fields, slot interiors and the Node/native joint context still need their R1
interpretation, so R2 remains in progress.

## Begin provenance through publication and release

Every native episode now carries an immutable, erased `Capture`: the actual
control state, declarations, committed bindings, provider generations and
published slots observed when Begin captured its imports. `Capture::wf` proves
both directions of capture: an import exists exactly when a committed binding
had an available slot in that source table, and it contains that actual slot.
The snapshot comes from the production constructor, with no caller-supplied
expected values.

`Execution::capture_correspondence` connects this Begin observation to the
current work and native value owner. Its executable mutations preserve the
same capture, including Child/effect admission, poll landing, cancellation,
cleanup, retry and reversible value programs. While the episode remains open,
its imports equal the original captured imports. Finish carries that same
capture into the actual publication and hence the native joint history. Unload
returns exactly the originally captured imports and empties the closed owner;
it does not recapture today's targets during cleanup.

The value owner also stores its actual cleanup/work domain. Publication and
release compare it with the supplied work queue before changing either state.
A different work queue is rejected even when raw embeddings deliberately reuse
the same lifecycle domain, plugin ID and generation. This closes the work-domain
substitution gap; it does not make numeric domains allocation-identity tokens.
The ordinary host's unique domain allocator and shared episode mutex remain
explicit boundaries. The complete R1 interpretation still needs to join those
shared owners, function meanings and Node publication versions.

The snapshots are ghost data: they add no runtime table copies, historical
allocations or extra `Arc` owners. A cross-thread regression retains an escaped
context through provider withdrawal, cleanup failure and retry, then checks
replacement and a fresh episode. It also checks exact `Arc` counts and rejects
use of the closed old context. A second regression exercises the work-domain
substitution guard at both Finish and Unload.

Review path: `native_capture.rs::Capture` →
`LifecycleState::capture_native_values` → `NativeEpisode::wf` →
`Execution::capture_correspondence` → `NativeRuntime::{begin_managed_execution,
finish_managed_execution,release_managed_execution}`. This strengthens the
implementation of committed dependencies and the native publication view in
(46), while preserving the original R2 exit criteria. Negative controls remove
the work-domain check, forget Begin's sources or replace the publication's Begin
control snapshot with the Finish state. Each must compile and fail its named
contract; scoped checks do not establish full negative-regression acceptance.

## Joint native registry and publication history

The production Rust `Runtime` now owns `NativeRuntime<R, H, V>` through
`NativeDriver`. Its registration graph and `NativeServices` live inside one
verified owner; callers no longer pass an independent store to Begin, Finish,
lookup or Unload. The actual entry points preserve one joint invariant:

- Every Active registration has a complete publication of its declared user
  ports, with its current episode generation and real shared value slots.
- Every retained publication belongs to a registered Active or Unloading
  provider. Retirement alone preserves it. Withdrawal hides it from new lookup
  while retaining its values for committed consumers and restoration.
- Finish checks the actual episode declarations against the stored recipe before
  publishing. Release removes only its own table after the real work and cleanup
  guards pass. Failures, retry, compaction, recipe updates and shared Child
  transitions preserve unrelated publications.

`NativeEpisode::matches_provisions` rejects even a supplied owner with colliding
numeric origins and a different declaration sequence. This is a concrete guard,
not a precondition placed on the ordinary Rust caller. The ordinary host's global
domain allocator remains responsible for separating runtime instances.

`NativeRuntime::history_correspondence` now proves a continuous joint history
of the **actual control state and retained publication tables**, starting empty
and ending at the current observation. The independent relation in
`native_history::step` adds exactly one provider's table at Finish, removes
exactly that table at Unload, and preserves every table in other control steps.
Observation-preserving calls retain the same history. Explicit Restart remains
an extension; a history without Restart has the strict paper-control projection.
The ghost history is erased from Cargo builds.

This joins the native implementation of the publication view in equation (46)
with L-Finish, L-Leave and L-Unload at the registry/slot boundary. It still does
not interpret `Arc` interiors, arbitrary callback bodies, the shared episode
mutex state or Node's publication versions as one complete R1 context. The
remaining R2 criteria are unchanged.

Review path: `native_runtime.rs::{linked,wf,finish_managed_execution,
release_managed_execution,history_correspondence}` → `native_history.rs::step`
→ `cordis-driver/src/native.rs` → `Runtime::poll_settle`.
Aggregate regressions cover complete publication, colliding declarations,
provider/consumer failure and retry, unrelated values, stale/foreign episodes,
recipe/bookkeeping updates, retirement, compaction and a shared Child with an empty publication. Three negative controls
remove the declaration guard, discard unrelated publications or omit a joint
history transition; each requires a compiling mutant rejected by the named
contract.


## What now runs under a contract

| User-visible behavior | Executable contract | Production caller |
| --- | --- | --- |
| A publication owns the value actually supplied by its owner | `PublicationStore::publish_checked` checks the real lifecycle domain, generation and admission, then stores the actual generic payload | `Driver::publish` → `LifecycleDriver::publish_value` |
| Replacement keeps publication identity and returns the real previous value | `replace_checked` and `ValueCell::replace`; rejected operations return the new input intact | `Driver::set`, Rust `ServiceSlot::replace` |
| An old cleanup lease continues to read its own retained value | `leased_value` derives both publication identity and payload from the actual lease record | `Driver::read` |
| Release moves the real values only after lifecycle and full resource-manifest validation | `finish_resources` composes the existing receipt/lease protocol with actual payload transfer; rejection preserves all three states | `LifecycleDriver::finish_cleanup_values` |
| A factory is invoked with the actual argument before its Future is polled | `RegisteredPlugin::call` invokes the stored native `FnMut`; `invoke_future` retains the actual returned cleanup Future | Rust `Runtime::start`, `initialize_cleanup` |
| Async cleanup consumes the result its Future actually returned | `Awaiting::complete` / `await_completion` pair a captured origin with the native Verus `Future` output; `complete_future` derives success/failure/drain from that output | Rust `initialize_cleanup`, `Runtime::finish_reply`, `StaticCleanupFuture::complete_reply` |
| A landed inverse is retained before the continuation is selected | `CleanupQueue::land_result` allocates the token itself, stores the actual inverse and derives continuation from the result and cancellation state | `Runtime::poll_groups` |
| One empty group cannot authorize closing an episode with other work | `CleanupGroups` owns every cleanup queue; `remove` and `seal` check pending stages, issued receipts, retained failures and real payloads, then close registration | `Runtime::poll_groups`, `Runtime::poll_settle`, `StaticCleanupFuture::poll` |
| Bulk retry does not partially advance a set containing a nonretryable failure | `retry_execution` preflights the bound work and all queues, then advances the lifecycle and inverse attempts together | `Runtime::retry_cleanup` |
| Only the admitted native episode can finish or release its lifecycle | `begin_execution` constructs both bound owners; `finish_execution` and `release_execution` check their original ticket and current generation | `Runtime::start`, `Runtime::poll_settle` |
| Removing a group cannot turn consumed failure into successful restoration | `CleanupGroups` retains its accepted `Drained` summary; `release_execution` derives the final outcome from that summary | `Runtime::finish_reply`, `Runtime::poll_settle` |
| A Child retains its parent's actual dependencies across realm isolation | `register_plugin` resolves declared keys and inherits both original and child-realm ports, excluding the child's own provisions | `Runtime::mount_inner` |
| A hot update cannot substitute a new recipe for an already admitted call | `admit_registered_root` binds the actual work to the registration; `call` checks its domain, owner and recipe revision before invoking the stored `FnMut` | `Runtime::start` |
| A native Child inverse cannot retire the same numeric ID in another runtime | `ChildIdentity` comes from real registration; `retire_child_slot` reads that identity from its actual slot | `Runtime::poll_cleanup` |
| A late Child request cannot allocate after its pending inverse was consumed | `ChildSlot` is assigned once by `register_child_slot`; `retire_child_slot` closes a pending slot and allocation checks the original parent generation | `Runtime::mount_inner`, `Runtime::poll_cleanup` |
| An effect request cannot refer to a separately allocated or foreign group | `enqueue_effect` creates the real queue and binds the actual iterator; `activate` checks lifecycle origin and queue domain | `AsyncSetup::effect`, `Runtime::drain_requests` |
| A poll reply cannot be accepted for another group or current attempt | `EffectRun::admit/call/land` preserve the actual payload, argument and result with a private poll identity | `Runtime::poll_groups` |
| Recorded cancellation rejects new Child/effect acquisition while retaining landed inverses | `accepts_acquisition` reads the actual stage state; actual Ready inverses still land before continuation stops | `AsyncSetup::ensure_active`, `mount_request`, `effect` |

Native Rust service values additionally use `begin_native_execution`,
`NativeEpisode::provide/read`, `finish_native_execution` and
`release_native_execution` through `Runtime::poll_settle`, `AsyncSetup` and
`NativeDriver`; see the native service section below.

The Node store's payload is its actual `u64` JavaScript value handle. The Rust
value cell holds its actual `Arc<dyn Any + Send + Sync>`. Neither contract
interprets mutable JavaScript object fields or a Rust value's interior mutation.
Payloads need no `Clone`, `Copy`, `Debug` or equality implementation. A lease pins
a publication identity, not an immutable snapshot: replacing that publication
changes the value its leases read; a newer publication has a separate identity.

The cleanup adapter preserves the existing policies. A failed retryable factory
remains retained. Ordinary Rust may report a consumed, nonretryable failure as
`Drained`; the static host uses `RetainFailure` and remains blocked. Neither is
silently reported as successful restoration. Discarded factories and rejected
payloads leave the bookkeeping mutex before destruction, so user `Drop` can
reenter the host.

## Relation to the paper

`publication_projection.rs` interprets the actual store as a key/value lookup
table. `publish`, `replace` and `revoke` call its proofs in their own bodies:

- Publication inserts the supplied value at a previously absent visible key.
- Replacement updates that key and returns its actual previous value.
- Revocation removes only that publication's visibility. Repeating it cannot
  hide a newer publication of the same key.
- Lease metadata changes and reclaiming an already revoked value preserve
  current lookup. The retained lease observation is separate and can change.

This is the registry's visibility projection. Host phase, dependency and
availability checks impose additional conditions on service lookup; this table
alone is not the complete host observation.

These are concrete instances of the key-local updates in §3.4, represented by
`coeffects::put`. They are not equality between a multi-version host registry
and R1's entire reified context. Restoring the returned old value recovers a
single replacement; this does not by itself establish a plugin's complete
inverse law under interference.

`LifecycleState` now propagates actual parent/dependency/provision arguments
through insertion, committed bindings through Begin, and the existing control
step relations through Finish, Retire, Remove and Unload. Compaction preserves
the control observation. Explicit restart and dynamic interface changes retain
their separately specified extension contracts.

`land_result` proves the accumulator projection of Iter, Finish or delayed
diversion together with the real payload update. That projection does not
interpret an opaque inverse function's external effects. A failure or explicit
group cancellation is still a host extension where the original paper does not
provide the corresponding guard.

## Async proof boundary

For the Future passed to `await_completion`, Verus proves that a returned
completion contains that Future's actual output and the origin supplied when it
was wrapped. This proof is conditional on returning; it proves neither eventual
completion nor scheduler fairness. A constructor-free `Completion` prevents a
receiver from replacing its fields, but it is not an authenticity token for
external I/O: a caller can wrap an immediately ready Future.

`invoke` establishes `callback.ensures((actual_argument,), actual_result)` by
calling that callback. `invoke_future` invokes the factory immediately and keeps
its returned Future; it does not delay factory side effects or panic handling to
the first poll. The native setup entry now uses the stored `FnMut` directly through
`RegisteredPlugin::call`; cleanup factories use `invoke_future`. The iterator
entry now uses `EffectRun::call` and its private poll reply, as detailed below.
No expected result is supplied by the adapter. The checked
`witnessed_invocation` and `witnessed_completion` callers instantiate the data
flow with executable code.

A checked caller must establish the callback's `requires`, and a checked plugin
must prove its own effect law. Ordinary Rust/JavaScript plugin bodies remain
outside that proof. Native
registration and invocation are now connected as described below. This does not
establish a plugin's inverse law, the complete host interpretation, or arbitrary
external I/O truth.

## Composition now owned by the kernel

`CleanupGroups<T>` replaces the host's mutable map of individually verified
queues. Its fields are private and it exposes no mutable queue reference. A
mutation preserves all other groups. Removed queues leave the active map; only
monotonic identity counters survive, so storage and drain scans follow live
groups instead of the number of groups ever created. Live and removed group identities cannot
be substituted by reusing a domain. Sealing inspects all queues, so an empty root
cannot hide another group's pending stage or issued cleanup. A cancelled stage
must land before its group can be removed; any returned inverse remains owned.
A failed bulk-retry preflight changes no group. Successful sealing proves that
no owned queue retains a payload, issued callback or pending stage, and closes
all subsequent registration in that container.

This composition is used by both the polled Rust runtime and the static adapter.
The SetupWork protocol below further connects root dispatch and actual queued
requests. Native lifecycle admission and release are now composed with those
owners as described below. Native values now join Begin/Finish/Unload as described
below. Shared native Child request/inverse handles now have the checked pairing and
synchronization described below. A joint invariant for the complete host observation
remains open; these local compositions do not discharge that whole-state obligation.

## Setup and requests participate in drain

`SetupWork<C, G>` owns actual Child/group requests and tracks root setup plus
requests already dispatched to a host. `WorkItem`, `PendingWork` and `WorkReceipt`
have private payload and identity fields. `run` produces a receipt by actually
calling the operation on the owned request. `start` immediately calls the
factory and retains its returned Future; completing that Future produces the
actual result. An empty dispatch queue cannot hide a request still being
executed. The FIFO uses VecDeque, avoiding movement of remaining requests on
each dispatch; completed receipts leave the active map.

`enqueue_native_child` constructs both ends of a native Child request; the generic
`enqueue_owned_child` also retains externally supplied request/inverse pairs
atomically, returning both unchanged on rejection for disposal outside the host
mutex. Final `seal` checks root setup, queued/dispatched requests and every
cleanup queue, including their common cleanup domain. Rust Runtime and the
static host use this guard. The polled Runtime's initialization completion also
uses the same actual state.

An unpolled root Future may be cancelled after withdrawal. A started Future
must return or remain explicitly abandoned and blocking; it cannot take the
unpolled cancellation path. Async completion preserves the actual Result, and
failure cannot authorize successful initialization. The checked normalization below now preserves actual poll results and maps caught
panics only to failure; performing the poll and catching the panic remain ordinary Rust. The invocation relation also does not replace a plugin's effect laws or the
full semantic relationship between Child request, shared handle and inverse.

## Registered recipes and native Child operations

`NativeHost::register` and `register_child` call `LifecycleState::register_plugin`
and `register_child_slot` from `Runtime::mount_inner`, including actual dynamic
Child allocation. It consumes the actual `PluginDefinition`,
reads the parent's authoritative kernel declarations, resolves keys in the
supplied realm map, and performs the real insertion. The returned
`RegisteredPlugin` owns the actual callback, resolved interface and reserved
anchor. `NativeHost` retains it together with the actual `Mounted` payload;
ordinary host code no longer performs a second registration-map insertion.

Its contract proves both the exact success domain and the resulting interface.
An inherited dependency keeps its original port and its child-realm port,
without introducing duplicates or an inherited dependency on the child's own
provision. Duplicate declared keys and conflicting reservations are rejected.
Registration does not require dependencies to be available: that remains a
Begin condition. Failure preserves the lifecycle state and returns the original
definition and callback. The stricter parent policy, realm mapping and synthetic
anchor are explicit host conventions around the paper's Insert control rule.

`admit_registered_root` checks the real pending setup action, current generation,
registration domain and owner, then issues a private invocation containing the
actual argument and recipe revision. `RegisteredPlugin::call` checks that
identity and directly calls the stored `FnMut`. It accepts neither a replacement
callback nor an expected result. Its native Verus call contract relates the
registered function and actual argument to the returned `WorkReceipt`.

`WorkReceipt::dispatch` distinguishes the factory's actual `Ready` result from
its actual `Pending` Future, preserving the issued root identity in both cases.
The factory still runs immediately; only the returned Future is deferred.
Synchronous completion and conditional async completion reach the existing
root/drain protocol. A caught panic uses the failure-only entry. The native
Runtime uses this path, while the static adapter uses the same result dispatch
with its existing external registration boundary.

Recipe replacement retains plugin identity and advances a checked revision.
A call admitted before replacement is rejected without invoking either recipe.
Already-started Futures retain their original completion identity. Batch recipe
updates preflight all required revision increments before changing a recipe;
old captured values are dropped after installation.

A successful child registration also produces a private `ChildIdentity` carrying
its actual runtime domain, parent and allocated ID. Native cleanup stores this
identity and calls `retire_child`, which proves a Retire control step for that
child. Repeating it after removal is a state-preserving operation; it cannot
retire a later replacement or a foreign runtime's equal numeric ID. Retirement
is a request to withdraw the child, not proof that its resources have finished
restoring. The existing cleanup and removal guards remain necessary.

The shared native handle now contains a private `ChildSlot`, constructed from
its actual `SetupWork` lifecycle origin. `register_child_slot` checks the runtime
domain, parent generation, live parent phase and pending state, executes registration, and writes
exactly the returned child's identity. It accepts no separately reported
successful ID. A duplicate, failed, cancelled or obsolete request allocates
nothing and returns the original recipe. A failed allocation leaves the slot
pending until the host records the actual failure through `reject`; that
failure-only entry cannot overwrite a successful assignment.

`retire_child_slot` reads the assigned identity itself. If the inverse is
consumed before allocation, it marks the slot cancelled: a later request cannot
create an unowned child. Failed and cancelled slots have no child to retire.
Repeated retirement of an assigned slot keeps its identity, including after
removal. The native Runtime now calls these operations through `SharedChild`,
whose synchronization and pairing are checked below. Rejected recipe captures
and subsequent host retirement callbacks run after releasing its lock. The static
adapter keeps its explicit external allocation-acknowledgement protocol.

These contracts connect real allocation and registered function invocation.
The shared Child protocol below removes another ordinary-host assumption, but
publication/context observations, callback/panic adaptation and concrete plugin
effect/inverse laws still need their complete semantic composition. Registration
storage and lifecycle membership have the joint invariant described later.
Global uniqueness of domain and service-key allocators remains a host boundary.

## One shared Child for its actual request and inverse

[`shared_child.rs`](../crates/cordis-kernel/src/shared_child.rs) closes the native
request/inverse aliasing and synchronization gap:

- `enqueue_native_child` receives only the real request payload. It constructs
  one `SharedChild` from the actual setup action, puts that same handle in the
  queued `NativeChildRequest` and the retained `ChildCleanup::Native`, and returns
  an observer for it. Admission has an exact success condition; rejection returns
  the original payload and changes neither queue. No caller-selected inverse
  handle participates in this native entry point.
- The private `vstd::rwlock::RwLock` owns the actual `ChildSlot<()>`. Its invariant
  binds the slot to the runtime, parent and episode. Registration, failure and
  retirement acquire exclusive access; observations acquire shared access.
  `register_shared_child` states success **if and only if** the state observed
  under that lock and the real registry satisfy the allocation guard.
- Each terminal decision carries a persistent `GhostMapAuth`/points-to witness.
  The witness is tied to the actual slot mutation, not a separate expected log.
  `ChildSnapshot::terminal_agrees` proves that two terminal observations of this
  shared slot cannot disagree. `cancellation_precludes_assignment` combines a
  real Cancelled observation with any later observation: it cannot be Assigned.
  Together with the actual registration result contract, a completed pending
  inverse excludes a later successful allocation, even across lock acquisitions.
- Each operation returns its actual before/after observations and releases the
  lock before returning. The Runtime uses this entry point for dynamic children;
  already registered native children enter through `from_identity`, retaining
  their actual identity. Retire remains distinct from Remove and resource drain.

This connects the paper's Child allocation/Retire inverse and the control-step
projection of Definitions 58/63 to the real queue payload and shared state. It
is not a new paper rule or the complete R1 Child interpretation. No claim is made
that arbitrary plugin effects, the complete host observation or Theorem 64 have
therefore been proved.

The synchronization proof uses the pinned vstd lock/resource contracts and the
standard `Arc` clone contract. The kernel check does not reverify vstd or Rust's
standard library. The lock uses spinning and does not establish fairness,
starvation freedom or global deadlock freedom. Critical sections invoke no user
callback. Only scalar lifecycle data lives in the lock; vstd's lock has explicit
release and no automatic payload destructor, so error strings and captures stay
outside it. Host diagnostics, panic adaptation and the other Runtime locks remain
outside this shared-slot proof. No dependency or toolchain version was added.

## Lifecycle admission through actual release

`LifecycleState::begin_execution` performs the real Begin and constructs both
`SetupWork` and `CleanupGroups` with that setup action's domain, owner,
generation and action identity. Their origin fields are private and immutable.
An unbound owner with the same numeric cleanup domain cannot substitute for the
admitted queues. The ordinary `LifecycleDriver` still allocates globally unique
domains; uniqueness of that atomic allocator is a host boundary.

The native Rust Runtime uses these checked operations throughout its episode:

- `settle_execution` waits for the real root, dispatched Child/group requests
  and pending stages before acknowledging the original setup action.
- `finish_execution` also checks the actual current target and all groups before
  the real Finish transition. A failed Finish may acknowledge completed setup;
  it cannot change the kernel state or publish an Active service.
- `fail_execution` requires a retained queue failure and no admitted work or
  issued cleanup still in flight. It retains the lifecycle obligation and
  committed dependencies.
- `retry_execution` preflights all queues before changing the lifecycle attempt,
  then advances their retry tickets together. A rejected retry changes neither.
- `release_execution` checks the bound origin, current generation, restoration
  phase, outstanding lifecycle action, root/requests and every cleanup queue.
  It derives `Succeeded` or `Drained`, consumes the action, seals both owners and
  performs the real Unload. Rejection preserves all three states. Success proves
  the owner's committed dependencies have been released and it is Inactive.

The host no longer chooses an aggregate success flag or maintains a separate
`cleanup_drained` Boolean. The checked group owner records accepted consumed
failures and preserves that fact through removal, retries and sealing. A new
episode starts with a new origin and an empty failure summary. Synchronous Child
results use `complete_result` and the same checked outcome policy as Futures;
Child allocation/retirement and the slot transitions now have the contracts above,
including the shared native request/inverse pairing and slot synchronization.
The ordinary callback/panic adapter and full host observation still need their
semantic correspondence proofs. Low-level APIs accepting explicit reports
remain available for external-host protocols; a report is not proof of an
external effect.

The Begin, Finish and Unload contracts relate these calls to the existing paper
**control projection**. They do not yet prove the full R1 value/code/continuation
interpretation, complete Child effect or production trace. Static/Node
bridges retain their own external completion boundary; this native composition
is not automatically a proof of every adapter.

## Native service values join admission, Finish and Unload

`native_values.rs` now owns the native Runtime's actual publication registry and
its episode-local service slots. `begin_native_execution` performs the real
Begin and creates the bound `SetupWork`, `CleanupGroups` and `NativeEpisode`
together. There is no public constructor that recaptures a second value owner
from an existing work ticket. Domain checks and a stale publication check run
before Begin; rejection leaves control unchanged.

The private capture reads the kernel's actual committed bindings and clones the
actual stored `Arc<ServiceSlot>` for each available binding. Its contract proves
both directions: every retained import belongs to a committed provider of the
current generation, and every available committed slot is retained. Unrelated
services acquire no implicit owner. Realm and provider identity remain part of
the lookup key. The snapshot preserves slot referents; it is not an immutable
copy of the contents of an interior-mutable service.

`NativeEpisode::provide` accepts a declared, absent key and stores the actual
input. Rejection returns that input intact. Its `owned_table` projection proves
the same key-local `coeffects::put` update as §3.4, while preserving imports and
other keys. This is the episode's local table, not the whole R1 context.
`read` selects only an owned provision or an actual captured binding. The global
`visible` lookup additionally resolves the current Active provider and checks
its generation. Withdrawal can therefore hide a publication from new calls
while existing cleanup still reads its original committed slot.

`finish_native_execution` requires all declared service values, the same
originating work and groups, and the real Finish guard. It commits Active and
publishes the actual owned slots in one checked call. Runtime no longer copies
all published slots on every Active scheduler pass. In-place `set` continues to
update the shared `ValueCell`; this change makes no benchmark claim.

`release_native_execution` checks the matching value/work/publication origins,
then runs the actual drain and Unload protocol. A rejection preserves lifecycle,
work, groups, registry and episode values. Success removes exactly that owner's
publication, closes further episode reads and writes, and returns its actual
owned, imported and published slots. The host drops them after releasing its
bookkeeping mutex, including for cancelled partial setup. Retained cleanup
failure cannot take this path; a retry must satisfy the existing fresh-ticket
protocol. Already returned user `Arc`s remain ordinary references, not revocable
leases.

The proof uses Verus's standard `Arc` referent and cloning contracts. It does not
prove mutex synchronization, reference-count implementation, mutable service
contents, or arbitrary availability callbacks. Static/Node embeddings keep their
explicit external-host contracts. Low-level lifecycle APIs remain available and
do not themselves maintain this native composition. The production native adapter
now uses `NativeHost`, which exposes no mutable lifecycle or registration map.
Shared Child handles, the meanings of host bookkeeping fields, and the complete
host interpretation still need the global semantic invariant.

## Registration and lifecycle have one owner

`NativeHost<R, H>` owns the real `LifecycleState` and the actual map of
`RegisteredPlugin<R>`/host-payload pairs. It replaces Runtime's separate
`BTreeMap<PluginId, Mounted>`. Its `wf` contract establishes, for every entry:

- Map membership is exactly the paper control projection's registered set.
- The stored recipe has that map key and the actual lifecycle domain.
- Its parent and resolved dependencies/provisions match the actual kernel
  declarations, including the reserved anchor.

`register` performs real Insert and stores the supplied callback and host object
before returning. `register_child` also writes the real assigned Child slot in
that operation. Failure returns both input payloads unchanged. `remove` first
passes the existing lifecycle Remove guard, then returns that exact entry for
destruction outside bookkeeping locks. Unload retains the registered recipe;
Remove is a separate operation. Surviving entries are unchanged.

`host_mut` lends only `H`; its contract proves registration and control are
unchanged for any mutation through that borrow. No mutable registration or
lifecycle reference escapes. `replace`, `admit_root`, and `call` select the actual
stored registration by ID, retain the other entries, and enforce its revision
and invocation identity. All exposed lifecycle transitions, native value
composition, Child retirement and compaction preserve `wf`. The native adapter
reads pending tickets directly from this state instead of maintaining a second
action-view map. Live-ID enumeration is exact and duplicate-free; it scans
live entries rather than historical identity tombstones.

This connects the registration/interface portions of Definitions 49–50 and the
control projection of Definitions 58/63 to actual production storage. It is a
preservation result for this projection, **not the whole Theorem 64** or a complete
R1 context interpretation. `H` remains opaque: its Future state, shared handles,
lock synchronization, availability semantics and panic adaptation are not proved
by the container's membership invariant. External/static adapters retain their
existing registration boundary.

## Effect requests and actual poll receipts

`effect_work.rs` joins the effect iterator path to the existing cleanup owner.
`SetupWork::enqueue_effect` preflights the actual work owner, lifecycle origin,
source group's cancellation state, receipt capacity and fresh cleanup domain.
It allocates the real iterator queue and enqueues the supplied iterator payload
with that exact identity in one checked operation. Rejection returns the original
payload and binding vector and changes neither owner. Dispatch cannot activate
it against a foreign lifecycle or another queue with the same numeric group ID.

`EffectRun` owns the actual iterator payload. A successful `admit` reserves a
monotonically increasing poll identity; a second admission or call cannot replace
an outstanding result. `call` passes the stored payload and actual argument to
the adapter and constructs a private reply from its actual return. `land` checks
the lifecycle/group/domain and current poll identity before accepting it. A
Pending reply keeps the real stage pending. A Ready reply feeds its actual inverse
or error into `CleanupGroups::land_result`; cancellation determines continuation,
and an inverse yielded after cancellation is retained before iteration ends.
Wrong replies return intact without changing the runner or any cleanup group.
Poll identity exhaustion rejects admission without wrapping or reusing identities.

Runtime uses these methods for `AsyncSetup::effect`, dispatch and `poll_groups`.
Its separate `cancelled_groups` set has been removed. `ensure_active`, nested
Child/effect acquisition and cancellation queries read the same stage cancellation
state used for inverse landing. `EffectHandle::cancel` remains a cooperative
request; this guard takes effect when the driver records it in the stage protocol.
Native and external Child queue admission also
consult this checked guard. In-flight work may still register its inverse after
cancellation; new Child/effect acquisition cannot use that allowance.

This connects the actual iterator/control path to the existing accumulator
interpretation of L-Iter, L-Finish and L-Divert. It proves result provenance,
queue ownership and continuation selection, conditional on the supplied callback
contract. The conversion from the supplied `Poll`/panic result to `EffectOutput` now has
the checked contract below. Arbitrary iterator and inverse effects, custom
destructors, host mutex scheduling and the meaning of opaque mutable payload
fields remain boundaries. It is not a complete
production trace interpretation or a fairness/termination theorem.

## One production execution owner

`Execution<V, C, G, I>` now owns the actual `SetupWork`, every cleanup queue,
the live `EffectRun<G>` map, checked-out runner identities, native service values
and initialization state. Runtime no longer holds a separate work owner, phase
field or iterator map. The static adapter uses the same owner for work, cleanup
and phase, with its external lifecycle/value boundary unchanged.

The invariant connects lifecycle origins, cleanup domains and live group
membership; it also requires closed work, cleanup and native values to agree.
`begin_managed_execution` constructs this state. `finish_managed_execution`
publishes the actual values and makes the episode Active in one checked call.
`release_managed_execution` checks full drain and returns the actual values while
closing the episode. Direct Runtime retirement and restart withdrawal use
`withdraw_managed_execution` to close acquisition together with the control
transition, preserving in-flight work and values. Child-triggered retirement
still calls the existing shared-Child protocol before host notifications.

`take_effect` leaves a checkout record. `put_effect` checks the originating
live queue and cannot overwrite a stored runner. `retire_effect` consumes the
actual runner only after that queue drains, returning its payload for destruction
outside the mutex. A borrowed or abandoned runner prevents removal and release,
even when the iterator map is empty. This is a safety guard; abandoning a runner
does not imply eventual recovery. Cancellation still permits an admitted stage
to land its inverse.

These are actual production state and transition contracts. They do not yet
supply the semantic interpretation of opaque callback effects, mutable value
contents, all host bookkeeping, or the whole host's correspondence to R1.

## Actual Poll normalization

`normalize_poll` preserves actual Pending/Ready results and converts a caught
panic only to failure. `normalize_effect_poll` distinguishes Pending, iterator
end, returned error, yielded inverse and caught panic. It maps the actual inverse
once, with no expected result supplied by the caller. Runtime uses these checked
functions for root, iterator and cleanup polls; the static host shares the root
and cleanup helpers.

The standard `Poll` type specification describes the real enum's variants. It
adds no assumed `poll`, `catch_unwind` or callback implementation. The proof starts
from the result handed to normalization; it does not prove panic capture, the
polling implementation, arbitrary callback effects, or eventual completion.

## Actual reversible service values and finite programs

[`ReversibleValue`](cases/reversible-values.md) adds a concrete production path
for the three semantic links. Plugins use `Setup::update_reversible` or
`run_value_program`; the normal Runtime and static host call the same checked
implementation. A private inverse holds the real target and captured pre/post
value states. `Execution` registers it before returning; `CleanupQueue::dispatch`
selects, executes and acknowledges the actual queued object without a host
success flag. Interference retains that exact inverse for explicit retry.

`operation` and `primitive_theory` establish actual partial inverse laws for
replacement, checked addition, XOR and compare/exchange. The observed state
includes the value and nesting depth, so a same-value later write cannot be
mistaken for an unchanged state. `Program::component` proves roots and every
outcome-selected continuation belong to R1's full finite strict carrier.
Programs are supplied by plugins; their validated code and actual comparison
results control execution. No expected result or transcript is an argument.

The actual value lock carries a ghost history. `history_interpretation`
classifies every write, successful inverse and rejected attempt.
`ProgramReport::source_execution` constructs a continuous dependent-grammar
trace for the complete run or failed prefix, framing other table keys.
All successful-prefix inverses enter the existing cleanup owner in execution
order. The history is erased from Cargo builds.

This closes those links **for this primitive/program path**, not the whole
host context. Ordinary callbacks, Node object state and the global joint
interpretation remain within the existing R2 acceptance work below.
See the [English case](cases/reversible-values.md) or
[中文案例](cases/reversible-values.zh-CN.md) for code, constraints, failure
reproduction and negative controls.

## Continuous production control history

`LifecycleState` now maintains a ghost `History` alongside its actual kernel and
action protocol. Every base control mutation records its actual before/after
control observations. The invariant starts at the empty registry, retains the
previous prefix, and ends at the current real control state. `record_control`
cannot replace that state with a caller-supplied transcript.

`control_history_correspondence` proves that the whole recorded sequence is
continuous and each step satisfies the paper control rule, an observation-
preserving internal step, or an explicit extension in `control_history.rs`.
Ordinary incoherent withdrawal is L-Divert or L-Leave. Forced coherent withdrawal
remains Restart. Dynamic provision insertion/removal and pending dependency
configuration have exact interface frames; provision removal additionally
requires absence of retained commitments to that port. Rejected calls and
compaction preserve the control observation. If a history contains no extensions,
`strict_paper_trace` derives the finite strict paper-control execution and its
reachability result from the recorded history.

Both the native and Node drivers use this lifecycle owner, including dynamic
Child insertion and managed resource release. The history is erased from Cargo
builds. This is the complete history of this **control projection**, not the
whole R1 context: service object contents, callback/function fields, publication
versions and the value/cleanup trace must still be composed into one semantic
observation. Protocol-only changes are internal steps in this projection; their
existing receipt and cleanup contracts continue to govern those changes.

## Remaining R2 acceptance

1. Establish the argument → executed operation → outcome → continuation →
   actual inverse relation at extensible production plugin entry points, with
   concrete primitive laws. Native registration and direct `FnMut` invocation
   now establish the recipe/argument/result prefix of that relation. Reversible
   value programs additionally establish concrete effect/inverse laws and
   outcome-selected code, while ordinary plugin bodies remain open. Do not
   substitute a caller-supplied expected result
   or assume arbitrary callback correctness.
2. Own and compose all concurrent groups, dynamic children, publications,
   admitted work and drain/release decisions in one checked production state.
   All cleanup queues now share a verified owner, and payload release composes
   with receipt/lease validation. Root setup and dispatch now participate in
   lifecycle admission, failure, retry and release.
   Real Child allocation/retirement and one-shot shared-slot transitions now have
   contracts. Native publication and committed-value owners now compose with
   Begin/Finish/Unload. NativeHost now also preserves the actual registry,
   callback and lifecycle interface correspondence. Shared native Child pairing,
   synchronization and persistent terminal decisions now have checked contracts.
   `Execution` now jointly owns actual work, native values, phase, live runners
   and their checkouts, with composed publication, withdrawal and release. The
   semantics of other shared host bookkeeping and complete host observation
   still need a joint invariant; result normalization is now checked separately.
3. Prove the complete production trace's classification and its relation to
   the R1 interpretation, including the stated multi-version and dynamic
   interface extensions. Actual reversible value histories and complete finite
   programs now have source traces, and the real lifecycle owner retains a continuous
   classified control history for both adapters. Their complete joint native/Node
   history remains open.
   A list of classified methods is not this theorem.

These are the existing R2 exit criteria, not new conditions added to reduce the
scope of the milestone. Original paper items and the four integration audit
outcomes have not been promoted by this increment.

## Review and reproduction

```sh
cargo test -p cordis-kernel --test publication_values --test async_completion --test cleanup_queue --test cleanup_groups --test setup_work --test execution_lifecycle --test plugin_registration --test child_slot --test native_values --test native_host --test shared_child --test effect_work --test execution --test poll_result --offline
python3 scripts/record-development.py --offline
```

Eight execution-owner tests cover atomic publication/phase, foreign withdrawal,
release and closed contexts, failure/retry, wrong runner return, late inverse
landing, dispatched work and abandoned root/runner blocking. Three poll tests
cover all result branches and preservation of the actual noncopy inverse.

Seven effect-work tests cover atomic allocation, exact payload/binding transport,
Pending/Ready receipts, cancellation and retained inverses, wrong-group and
foreign replies, rejection ownership and calls after cancellation. A Runtime
regression checks an escaped cancelled context, late inverse registration and
landing, suppressed subsequent stages, and owner survival. Four negative controls
misbind the queued group, bypass source cancellation, accept a wrong poll identity,
or discard the actual returned inverse.

Eight shared-Child tests cover FIFO/LIFO pairing, inverse-before-dispatch,
terminal failure/assignment, foreign and obsolete admissions, rejected payloads,
concurrent observers/rejections, registered-identity construction and destructor
reentry after rejection. Two Runtime regressions check cloned failure diagnostics
and identity observation while the actual child is removed.

Six native-host tests cover rejected allocation without losing either actual
input, host mutation and recipe updates across multiple owners, wrong/foreign/
obsolete invocations, dynamic Child assignment/removal, retained cleanup failure
through retry and Unload, and live entry enumeration after churn/compaction.

Seven native-value tests cover exact committed imports, real slot aliasing,
realm isolation, duplicate and foreign Begin, incomplete Finish, failed cleanup
and retry, stale publications, old closed contexts, and deferred destruction of
noncopy values. Existing Runtime regressions cover shared updates, cancelled
setup and destructors reentering contexts.

Child-slot tests cover duplicate assignment, the inverse-before-allocation ordering,
retained allocation failure, foreign runtimes, obsolete episodes and retirement
after replacement. Four additional negative controls remove one-shot admission,
the generation/live-parent guards, or pending cancellation; each must fail the exact contract.

The targeted tests exercise noncopy payloads, old/new publications, stale
generations, foreign domains, exact cleanup manifests, reverse Future completion
order, factory invocation timing, failed retries, destructor ownership, late
cancelled landings, foreign/unbound lifecycle owners, retained provider
commitments, atomic retry, consumed failure after group removal, and sealing
with non-root work still outstanding. Registration tests add realm isolation,
current parent declarations, rejected noncopy payloads, wrong/foreign owners,
stale recipe revisions, direct factory invocation, actual async failures and
Child retirement after removal. The normal development checks additionally rebuild and test the Rust and Node hosts.

Forty-nine R2 negative controls change actual payloads or identities, forge cleanup
success, continue after cancellation, omit outstanding work, or substitute an
unbound cleanup owner. They also erase an isolated realm or registered
dependencies, omit the recipe revision check, or bypass the Child runtime check.
Five of these native-value controls omit committed imports, bypass a generation
check, finish without complete values, substitute the published map, or release
a different episode. Three native-host controls hide a registration, lend another
owner's bookkeeping, or replace another owner's recipe. Three shared-Child
controls substitute a separate request handle, reject an otherwise valid allocation
or report retirement without changing the actual slot. Six execution/poll controls
omit a checkout, accept a foreign runner, omit Active, retire a live queue, turn
Pending into completion, or discard the returned inverse.
Five value/program controls ignore the actual result or depth, omit an inverse,
forge restoration success or skip a continuation. Two control-history cases omit
a real step or attribute a declaration at another port to the supplied call.
Each scoped experiment needs a fresh positive proof,
a compiled mutant and rejection of the named contract. A scoped result does not
mean the full 184-case negative regression ran; see [validation](validation.md).

The source-bound development report records the full positive check separately
from release acceptance and paper completion. No Node dependency is added for
Rust users, and no temporal-logic library is required for these contracts.
