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
| Async cleanup consumes the result its Future actually returned | `await_completion` pairs a captured origin with the native Verus `Future` output; `complete_future` derives success/failure/drain from that output | Rust `initialize_cleanup`, `Runtime::finish_reply`, `StaticCleanupFuture::complete_reply` |
| A landed inverse is retained before the continuation is selected | `CleanupQueue::land_result` allocates the token itself, stores the actual inverse and derives continuation from the result and cancellation state | `Runtime::poll_groups` |

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

The association from plugin argument to callback factory, the factory's produced
Future, and the returned inverse's effect still needs a checked implementation
contract. The ordinary Rust adapters that invoke arbitrary closures are outside
the verified crate. Their tests and the small `witnessed_completion` caller are
not a proof that every production callback satisfies those obligations.

## Remaining R2 acceptance

1. Establish the argument → executed operation → outcome → continuation →
   actual inverse relation at extensible production plugin entry points, with
   concrete primitive laws. Do not substitute a caller-supplied expected result
   or assume arbitrary callback correctness.
2. Own and compose all concurrent groups, dynamic children, publications,
   admitted work and drain/release decisions in one checked production state.
   The current composition of payload release with receipt/lease validation is
   narrower than that whole-host invariant.
3. Prove the complete production trace's classification and its relation to
   the R1 interpretation, including the stated multi-version and dynamic
   interface extensions. A list of classified methods is not this theorem.

These are the existing R2 exit criteria, not new conditions added to reduce the
scope of the milestone. Original paper items and the four integration audit
outcomes have not been promoted by this increment.

## Review and reproduction

```sh
cargo test -p cordis-kernel --test publication_values --test async_completion --test cleanup_queue --offline
python3 scripts/record-development.py --offline
```

The targeted tests exercise noncopy payloads, old/new publications, stale
generations, foreign domains, exact cleanup manifests, reverse Future completion
order, failed retries, destructor ownership and late cancelled landings. The
normal development checks additionally rebuild and test the Rust and Node hosts.

Four negative controls replace a real value with `None`, substitute a lease's
publication identity, turn an awaited error into success, or keep a cancelled
continuation alive. Each scoped experiment needs a fresh positive proof, a
compiled mutant and rejection of the named contract. A scoped result does not
mean the full 136-case negative regression ran; see [validation](validation.md).

The source-bound development report records the full positive check separately
from release acceptance and paper completion. No Node dependency is added for
Rust users, and no temporal-logic library is required for these contracts.
