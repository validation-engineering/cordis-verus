# R2: production execution contracts

[简体中文](r2-execution.zh-CN.md) · [Paper milestones](paper-refinement-roadmap.md)

R2 connects the paper's constraints to production managed calls. **R2 remains
in progress.** The contracts below run in the Rust and Node adapters; they close
payload, registration and result-transfer gaps, but do not yet establish whole-host semantic
refinement or Component membership for arbitrary plugin callbacks.

## What now runs under a contract

| User-visible behavior | Executable contract | Production caller |
| --- | --- | --- |
| A publication owns the value actually supplied by its owner | `PublicationStore::publish_checked` checks the real lifecycle domain, generation and admission, then stores the actual generic payload | `Driver::publish` → `LifecycleDriver::publish_value` |
| Replacement keeps publication identity and returns the real previous value | `replace_checked` and `ValueCell::replace`; rejected operations return the new input intact | `Driver::set`, Rust `ServiceSlot::replace` |
| An old cleanup lease continues to read its own retained value | `leased_value` derives both publication identity and payload from the actual lease record | `Driver::read` |
| Release moves the real values only after lifecycle and full resource-manifest validation | `finish_resources` composes the existing receipt/lease protocol with actual payload transfer; rejection preserves all three states | `LifecycleDriver::finish_cleanup_values` |
| A factory is invoked with the actual argument before its Future is polled | `RegisteredPlugin::call` invokes the stored native `FnMut`; `invoke_future` retains the actual returned cleanup Future | Rust `Runtime::start`, `initialize_cleanup`, `Runtime::poll_groups` |
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
`RegisteredPlugin::call`; iterator and cleanup entries use these generic helpers.
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
owners as described below. Publication values, Child request/inverse handles and the
complete host observation still need a joint semantic invariant; the local
composition does not discharge that whole-state obligation.

## Setup and requests participate in drain

`SetupWork<C, G>` owns actual Child/group requests and tracks root setup plus
requests already dispatched to a host. `WorkItem`, `PendingWork` and `WorkReceipt`
have private payload and identity fields. `run` produces a receipt by actually
calling the operation on the owned request. `start` immediately calls the
factory and retains its returned Future; completing that Future produces the
actual result. An empty dispatch queue cannot hide a request still being
executed. The FIFO uses VecDeque, avoiding movement of remaining requests on
each dispatch; completed receipts leave the active map.

`enqueue_owned_child` admits the actual Child request and retains its inverse
atomically, returning both unchanged on rejection for disposal outside the host
mutex. Final `seal` checks root setup, queued/dispatched requests and every
cleanup queue, including their common cleanup domain. Rust Runtime and the
static host use this guard. The polled Runtime's initialization completion also
uses the same actual state.

An unpolled root Future may be cancelled after withdrawal. A started Future
must return or remain explicitly abandoned and blocking; it cannot take the
unpolled cancellation path. Async completion preserves the actual Result, and
failure cannot authorize successful initialization. Ordinary Rust still reports
caught panics through a failure-only entry; Verus has not proved the adapter's
poll/panic correspondence. The invocation relation also does not replace a plugin's effect laws or the
full semantic relationship between Child request, shared handle and inverse.

## Registered recipes and native Child operations

`LifecycleState::register_plugin` now runs in `Runtime::mount_inner`, including
actual dynamic Child allocation. It consumes the actual `PluginDefinition`,
reads the parent's authoritative kernel declarations, resolves keys in the
supplied realm map, and performs the real insertion. The returned
`RegisteredPlugin` owns the actual callback, resolved interface and reserved
anchor; `Mounted` no longer keeps independent copies of those fields.

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
removal. The native Runtime calls these operations under its existing mutex;
rejected recipe captures and subsequent host retirement callbacks are handled
after releasing that mutex. The static adapter keeps its explicit external
allocation-acknowledgement protocol.

These contracts connect real allocation and registered function invocation.
They do not yet prove the complete R1 Child effect: ordinary Rust still moves
the registration into `Mounted`, clones the shared slot handle between the queued request and
its inverse, synchronizes access, adapts panics, and maintains publication/context observations.
A joint invariant for those operations and concrete plugin effect/inverse laws
are still required. Global uniqueness of domain and service-key allocators also
remains an explicit host boundary.

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
while shared-handle aliasing, synchronization and the ordinary callback/panic adapter still need their
semantic correspondence proofs. Low-level APIs accepting explicit reports
remain available for external-host protocols; a report is not proof of an
external effect.

The Begin, Finish and Unload contracts relate these calls to the existing paper
**control projection**. They do not yet prove the full R1 value/code/continuation
interpretation, complete Child effect or production trace. Static/Node
bridges retain their own external completion boundary; this native composition
is not automatically a proof of every adapter.

## Remaining R2 acceptance

1. Establish the argument → executed operation → outcome → continuation →
   actual inverse relation at extensible production plugin entry points, with
   concrete primitive laws. Native registration and direct `FnMut` invocation
   now establish the recipe/argument/result prefix of that relation. Do not
   substitute a caller-supplied expected result
   or assume arbitrary callback correctness.
2. Own and compose all concurrent groups, dynamic children, publications,
   admitted work and drain/release decisions in one checked production state.
   All cleanup queues now share a verified owner, and payload release composes
   with receipt/lease validation. Root setup and dispatch now participate in
   lifecycle admission, failure, retry and release.
   Real Child allocation/retirement and one-shot shared-slot transitions now have
   contracts. Shared Child handle aliasing/synchronization, poll/panic adaptation, publication values and complete
   host observation still need semantic composition.
3. Prove the complete production trace's classification and its relation to
   the R1 interpretation, including the stated multi-version and dynamic
   interface extensions. A list of classified methods is not this theorem.

These are the existing R2 exit criteria, not new conditions added to reduce the
scope of the milestone. Original paper items and the four integration audit
outcomes have not been promoted by this increment.

## Review and reproduction

```sh
cargo test -p cordis-kernel --test publication_values --test async_completion --test cleanup_queue --test cleanup_groups --test setup_work --test execution_lifecycle --test plugin_registration --test child_slot --offline
python3 scripts/record-development.py --offline
```

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

Eighteen negative controls change actual payloads or identities, forge cleanup
success, continue after cancellation, omit outstanding work, or substitute an
unbound cleanup owner. They also erase an isolated realm or registered
dependencies, omit the recipe revision check, or bypass the Child runtime check.
Each scoped experiment needs a fresh positive proof,
a compiled mutant and rejection of the named contract. A scoped result does not
mean the full 150-case negative regression ran; see [validation](validation.md).

The source-bound development report records the full positive check separately
from release acceptance and paper completion. No Node dependency is added for
Rust users, and no temporal-logic library is required for these contracts.
