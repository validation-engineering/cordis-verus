# Cleanup acknowledgements and dependency release

English · [简体中文](cleanup-protocol.zh-CN.md)

This guide follows one contract: an executor must account for an admitted cleanup
before the shared lifecycle API can release that episode's committed dependencies.
It connects the production `LifecycleActions` protocol to the kernel guard and
the actual Node and Rust completion paths. It is a bounded step in
[A07 / F1](adoption-plan.md), not a complete proof of either host or a newly
confirmed upstream/runtime defect. The [paper ledger](paper-obligations.json)
still has **18 partial items and four open integration obligations**.

## Paper clause to executable protocol

The paper's §4.2.2, Definition 54 and L-Unload (pp.36–37) separate two duties:
retain the consumer's committed view while applying its accumulator, and defer a
provider's restoration while that provider is still relied upon. The prose on
p.37 makes discarding the committed view the last act of L-Unload.

| Review clause | Executable connection | Boundary |
| --- | --- | --- |
| **BindingPersistence** | `Kernel::begin_cleanup` retains committed bindings; `Kernel::finish_cleanup` releases them. `LifecycleActions` checks the matching cleanup acknowledgement before calling finish. | The protocol matches the report to an exact outstanding ticket; it does not prove that an arbitrary inverse succeeded. |
| **RestorationGuard** | Cleanup admission calls the real kernel guard, which rejects a provider still named by a live committed consumer. An owner's outstanding action also blocks that owner's cleanup admission through the shared API. | Dependency ordering is not parent/child lifetime ordering or a scheduler theorem. |
| **Inverse before release** | A cleanup action must become an explicit outcome before finish can release the commitment. A failed outcome remains blocking until explicit retry. | Rust's `Drained` policy acknowledges consumed work, not successful restoration; it must not be substituted for the paper's inverse law. |

The bold labels are project review names, not new paper propositions. See
[PR-01](paper-review-guide.md#pr-01-an-episode-keeps-the-provider-identity-it-committed-to)
and [progress contracts](progress-contracts.md) for the underlying projections and
separate concrete inverse-execution results. This milestone does not complete a
paper item or establish Corollary 69 for arbitrary callbacks.

## Read the actual call chain

1. [LifecycleActions](../crates/cordis-kernel/src/lifecycle_actions.rs) composes
   setup/cleanup admission, [ActionLedger](../crates/cordis-kernel/src/action_ledger.rs)
   ticket consumption, outcome receipts and guarded finish. These are executable
   Rust functions in the Verus-checked kernel source, not a parallel model of a
   different dispatcher.
2. [shared::LifecycleDriver](../crates/cordis-driver/src/shared.rs) calls that
   protocol. `pending_views` is a serialization view; it does not authorize
   transitions. The API provides no mutable kernel reference that bypasses the
   protocol. That ordinary owner also maintains the pairing of this Kernel with
   this protocol instance. The public core module does not prove correctness of
   arbitrary cross-instance combinations; pairing and host routing remain
   integration obligations.
3. [Driver::complete](../crates/cordis-driver/src/lib.rs) separates setup from
   cleanup completion. For Node cleanup it records `Succeeded` or `Failed`.
   Failure returns before `finish_cleanup` and before the resource/publication
   release loops. Success calls the guarded finish, then releases dependency
   leases and reclaims its publications. Those ordinary Rust loops remain a
   host boundary, even though their publication primitives have their own proofs.
4. [Domain.dispatch / Fiber._cleanup](../packages/compat-cordis/runtime.js)
   runs the actual callbacks and sends the completion report. The separate Rust
   [Runtime::poll_settle](../crates/cordis/src/runtime.rs) reports `Drained`
   after its cleanup work has been consumed.

Cleanup admission preallocates a Pending receipt. Completion updates that receipt
in place; it does not allocate a new receipt after consuming the action. Setup
completion cannot stand in for cleanup completion. Tickets identify the
exact domain, owner, generation, action and kind; a duplicate, wrong-kind or stale
completion cannot authorize a new attempt. Cancellation does not silently discard
an outstanding setup ticket: its result may still carry an inverse to collect.

## Three outcomes, two host policies

| Outcome | Protocol meaning | Host policy |
| --- | --- | --- |
| `Succeeded` | Updates the receipt to authorize matching-generation finish. | Node reports it only when its managed cleanup pass has no reported errors. Truth of that report remains a host obligation. |
| `Failed` | Keeps a blocking receipt; finish/removal through the shared API remain unavailable. Explicit retry replaces its state and ticket with a fresh action. | Node keeps failed inverse registrations and dependency leases. Successful inverses are removed and are not replayed on retry. |
| `Drained` | Updates the receipt to acknowledge consumed work and permit matching-generation finish. | Ordinary Rust consumes `FnOnce` inverses, records their errors and continues draining. This is neither a successful-recovery assertion nor a retryable inverse queue. |

A rejected finish preserves the Kernel state and committed bindings. Successful
finish consumes the receipt. Retry is permitted only from `Failed`
and updates the existing receipt with a fresh ticket; the previous attempt's
ticket stays consumed. A
caller cannot convert a retained `Failed` receipt into `Succeeded` by replaying
completion; it must perform the explicit retry protocol. None of these outcomes
makes a callback idempotent or reverses partial external work.

Resources registered before the first episode use the **generation-zero
reservation** path. Admission and finish are tracked separately while the kernel
remains Inactive; this is a host extension, not a paper L-Unload transition.
The same receipt representation is used; phase and generation checks distinguish
reservation cleanup from an installed episode. This is not a separate receipt type.

## Evidence and remaining assumptions

Use the [source-bound evidence guide](evidence-guide.md) and the actual verification
reports for accepted runs; this page supplies no new proof or release counts.
Review a successful cleanup, failure with retained dependencies, explicit retry,
and rejected replay against both the protocol and the real host tests. The
[cleanup case](cases/lifecycle-cleanup.md) and
[Node disposal-failure regressions](../tests/node-compat/disposal-failure.test.mjs)
exercise real callbacks; the [Rust runtime regressions](../crates/cordis/tests/runtime.rs)
cover its separate draining policy. These focused commands run behavioral tests;
they do not replace Verus verification or the full development/release gates.

```sh
cargo test --offline -p cordis-driver --test shared_lifecycle --test cleanup_outcomes
cargo test --offline -p cordis-driver --test episode_failure --test reservation_effects
```

The proof boundary includes protocol state and the specified kernel calls. It
excludes callback truthfulness, arbitrary inverse effects, publication-release
routing as a whole, JavaScript, N-API/FFI, OS/file/network behavior, scheduling and
termination of arbitrary futures. In particular, a pending callback may never
return; safe retention is not eventual cleanup. The file case independently
checks write callbacks and resulting contents, and does not make disposal a
file-durability guarantee.

The engineering gain is that cleanup authorization and its kernel transition can
be reviewed and checked together in the code the shared API executes. A passing
protocol proof does not promote the surrounding runtime to an end-to-end theorem,
and an API/proof composition gap is not evidence of an observed upstream bug.
