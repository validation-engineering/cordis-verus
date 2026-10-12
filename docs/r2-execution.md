# R2: production execution contracts

[简体中文](r2-execution.zh-CN.md) · [Paper milestones](paper-refinement-roadmap.md)

R2 connects the paper's constraints to production managed calls. **R2 remains
in progress.** The contracts below run in the Rust and Node adapters; they close
payload and result-transfer gaps, but do not yet establish whole-host semantic
refinement or Component membership for arbitrary plugin callbacks.

## What now runs under a contract

| User-visible behavior | Executable contract | Production caller |
| --- | --- | --- |
| A publication owns the value actually supplied by its owner | `PublicationStore::publish_checked` checks the real lifecycle domain, generation and admission, then stores the actual generic payload | `Driver::publish` → `LifecycleDriver::publish_value` |
| Replacement keeps publication identity and returns the real previous value | `replace_checked` and `ValueCell::replace`; rejected operations return the new input intact | `Driver::set`, Rust `ServiceSlot::replace` |
| An old cleanup lease continues to read its own retained value | `leased_value` derives both publication identity and payload from the actual lease record | `Driver::read` |
| Release moves the real values only after lifecycle and full resource-manifest validation | `finish_resources` composes the existing receipt/lease protocol with actual payload transfer; rejection preserves all three states | `LifecycleDriver::finish_cleanup_values` |
| A factory is invoked with the actual argument before its Future is polled | `invoke` uses native Verus `FnOnce` contracts; `invoke_future` retains the actual returned Future, then `Awaiting::complete` awaits that value | Rust `initialize_callback`, `initialize_cleanup`, `Runtime::poll_groups` |
| Async cleanup consumes the result its Future actually returned | `Awaiting::complete` / `await_completion` pair a captured origin with the native Verus `Future` output; `complete_future` derives success/failure/drain from that output | Rust `initialize_cleanup`, `Runtime::finish_reply`, `StaticCleanupFuture::complete_reply` |
| A landed inverse is retained before the continuation is selected | `CleanupQueue::land_result` allocates the token itself, stores the actual inverse and derives continuation from the result and cancellation state | `Runtime::poll_groups` |
| One empty group cannot authorize closing an episode with other work | `CleanupGroups` owns every cleanup queue; `remove` and `seal` check pending stages, issued receipts, retained failures and real payloads, then close registration | `Runtime::poll_groups`, `Runtime::poll_settle`, `StaticCleanupFuture::poll` |
| Bulk retry does not partially advance a set containing a nonretryable failure | `can_retry_all` / `retry_all` preflight every owned queue, preserve other groups and issue fresh attempt identities | `Runtime::retry_cleanup` |

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
the first poll. These helpers now run at production setup, iterator and cleanup
entry points. No expected result is supplied by the adapter. The checked
`witnessed_invocation` and `witnessed_completion` callers instantiate the data
flow with executable code.

A checked caller must establish the callback's `requires`, and a checked plugin
must prove its own effect law. Ordinary Rust/JavaScript plugin bodies and host
registration remain outside that proof. The generic call relation and small
witnesses do not establish a plugin's inverse law, the complete relationship
between a registered plugin and its invocation, or arbitrary external I/O truth.

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
requests. Lifecycle and publication still need a joint semantic invariant with
these protocols; the local composition does not discharge that whole-state
obligation.

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
poll/panic correspondence. The invocation relation also does not replace the
semantic proof of actual Child allocation or a plugin's effect laws.

## Remaining R2 acceptance

1. Establish the argument → executed operation → outcome → continuation →
   actual inverse relation at extensible production plugin entry points, with
   concrete primitive laws. Do not substitute a caller-supplied expected result
   or assume arbitrary callback correctness.
2. Own and compose all concurrent groups, dynamic children, publications,
   admitted work and drain/release decisions in one checked production state.
   All cleanup queues now share a verified owner, and payload release composes
   with receipt/lease validation. Root and request receipts now participate in
   drain checks. Actual Child allocation, poll/panic adaptation and the joint
   lifecycle/publication state still need semantic composition.
3. Prove the complete production trace's classification and its relation to
   the R1 interpretation, including the stated multi-version and dynamic
   interface extensions. A list of classified methods is not this theorem.

These are the existing R2 exit criteria, not new conditions added to reduce the
scope of the milestone. Original paper items and the four integration audit
outcomes have not been promoted by this increment.

## Review and reproduction

```sh
cargo test -p cordis-kernel --test publication_values --test async_completion --test cleanup_queue --test cleanup_groups --test setup_work --offline
python3 scripts/record-development.py --offline
```

The targeted tests exercise noncopy payloads, old/new publications, stale
generations, foreign domains, exact cleanup manifests, reverse Future completion
order, factory invocation timing, failed retries, destructor ownership, late
cancelled landings and sealing with non-root work still outstanding. The
normal development checks additionally rebuild and test the Rust and Node hosts.

Eight negative controls replace a real value with `None`, substitute a lease's
publication identity, turn an awaited error into success, keep a cancelled
continuation alive, omit non-root groups from the drain check, or alter the
argument in a checked `invoke` caller, omit dispatched requests, or discard an already running root. Each scoped experiment needs a fresh positive proof, a
compiled mutant and rejection of the named contract. A scoped result does not
mean the full 140-case negative regression ran; see [validation](validation.md).

The source-bound development report records the full positive check separately
from release acceptance and paper completion. No Node dependency is added for
Rust users, and no temporal-logic library is required for these contracts.
