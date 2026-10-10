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
2. [shared::LifecycleDriver](../crates/cordis-driver/src/shared.rs) owns a
   [LifecycleState](../crates/cordis-kernel/src/lifecycle_state.rs). This verified
   type constructs and retains its Kernel and action protocol together; its
   public mutations preserve both invariants. Hosts receive only an immutable
   Kernel view and cannot pass a replacement Kernel to its cleanup methods.
   `pending_views` remains a serialization view, not transition authority.
3. [Driver::complete](../crates/cordis-driver/src/lib.rs) records `Succeeded` or
   `Failed` for Node cleanup. Failure returns without releasing resources.
   Success calls the shared state's `finish_cleanup_resources`, implemented in
   [cleanup_release.rs](../crates/cordis-kernel/src/cleanup_release.rs). It checks
   the exact current cleanup receipt and registry domain, validates and executes
   the complete resource batch, then calls the actual guarded Kernel finish.
   The ordinary adapter subsequently removes the returned opaque value slots
   and updates its host bookkeeping.
4. [Domain.dispatch / Fiber._cleanup](../packages/compat-cordis/runtime.js)
   runs the actual callbacks and sends the completion report. The separate Rust
   [Runtime::poll_settle](../crates/cordis/src/runtime.rs) uses the checked
   `CleanupJournal` for actual inverses. Retained failures report `Failed`; an
   exhausted journal reports `Succeeded`, or `Drained` if a consumed `FnOnce`
   inverse failed.

Cleanup admission preallocates a Pending receipt. Completion updates that receipt
in place; it does not allocate a new receipt after consuming the action. Setup
completion cannot stand in for cleanup completion. Tickets identify the
exact domain, owner, generation, action and kind; a duplicate, wrong-kind or stale
completion cannot authorize a new attempt. Cancellation does not silently discard
an outstanding setup ticket: its result may still carry an inverse to collect.

## The actual resource batch is checked before commitment release

Managed acquisitions record the consumer owner and generation in the real lease;
the real Driver allocates these leases for the next admitted episode. Its
`PublicationRegistry` carries the Driver domain. Unscoped legacy leases cannot
be consumed by managed cleanup, and a registry carrying a different domain is rejected even when its local
publication and lease IDs happen to match. The domain number is checked here;
unique domain allocation remains the real Driver's host responsibility.

[`PublicationRegistry::cleanup_batch`](../crates/cordis-kernel/src/publication_cleanup.rs)
checks every selected lease's consumer, every publication's owner/generation,
revoked/retained state, uniqueness and all remaining holders. It also checks
**completeness** against the registry: no lease of this consumer episode or
retained publication of this owner/generation may be omitted. The manifest is
therefore checked at execution time, not assumed correct by a caller.

Only after the complete preflight does it release leases and reclaim publications.
Its executable contract states exact acceptance, unchanged registry on rejection,
exact returned publication/slot pairs, preservation of unselected resources and
`episode_resources_cleared`. The composed finish then releases commitments and
proves the actual L-Unload step; the generation-zero reservation branch keeps
its separate, unchanged Kernel state. Rejected batches preserve the Kernel,
protocol receipt and entire registry as they were **on entry to finish**. An
already recorded successful callback report stays recorded; the theorem does
not roll back the earlier completion or any callback effects.

[Regression cases](../crates/cordis-driver/tests/cleanup_resources.rs) exercise
failure/retry, stale replies, omitted/duplicate/foreign resources, a foreign
registry with matching local IDs, remaining external holders and reservation
cleanup. The canonical negative controls additionally remove the lease-owner
check and move commitment release before batch validation. Local selected-proof
experiments do not substitute for the full release negative-control gate.

This closes a concrete release-orchestration gap. Global domain allocation,
lease-acquisition routing, serialization views, opaque value-handle removal,
JS/FFI execution and callback-report truth remain host boundaries. The Rust
callback journal below adds explicit retry without proving arbitrary inverse effects.

## Retryable Rust inverses use the checked journal

[`CleanupJournal`](../crates/cordis-kernel/src/cleanup_journal.rs) wraps the real
`StageProtocol` stack used by both Rust Runtime and static typed episodes. Its
executable contracts check that restoration selects the last waiting token,
keeps that token selected on failure, and resumes it with a fresh attempt number
only on explicit retry. A failed or pending selection makes the journal nonempty.
Duplicate, old-attempt and foreign-domain reports cannot clear it. Late
registrations remain behind the selected operation and run before older waiting
operations after it succeeds.

[`CleanupQueue<T>`](../crates/cordis-kernel/src/cleanup_queue.rs) owns that journal
and the real `Vec<Option<T>>` of callback payloads. Both hosts use this executable
container, with no `Clone` or `Debug` requirement on the payload. Registration
allocates its token and stores its exact payload together. Selection moves the
payload out of that token's slot once per attempt. A matching failed completion
stores exactly the supplied retry payload back in that slot; stale, foreign,
duplicate or otherwise rejected completions preserve the queue and return the
supplied payload unchanged. Retry requires a retained payload, so a consumed
failure cannot admit an empty retry. Every stored payload belongs to a waiting
or selected token; an empty queue therefore has no stored payload or issued work.
The host no longer maintains a separate unchecked token-to-payload vector.

Use `Setup::on_cleanup_retryable` / `on_cleanup_retryable_async`, or
`Inverse::retryable` / `retryable_async` inside an effect. The same registration
methods are available on `AsyncSetup` and `Runtime`. These accept `FnMut`
factories; each attempt constructs a new future, while the current pending future
stays owned by Runtime if a caller drops `Settle` or `Join`.

```rust
let mut attempts = 0;
setup.on_cleanup_retryable(move || {
    attempts += 1;
    if attempts == 1 { Err("temporary cleanup failure".into()) }
    else { Ok(()) }
});
```

After a reported failure, inspect `Runtime::cleanup_failure(id)` or the
`CleanupFailed` snapshot blocker. Calling `settle` or `shutdown` again does not
retry. Once all callbacks from the current attempt have settled, the caller can
admit and drive another attempt:

```rust
runtime.retry_cleanup(id)?;
runtime.settle().await?;
```

The real Runtime first obtains a fresh `LifecycleActions` cleanup attempt, then
retries each failed journal. It retains the committed providers and payloads;
already successful operations are not replayed. Independent effect groups can
finish their current work while another group is blocked, but earlier operations
in that failed group wait. A failed effect's explicit disposal withdraws its
owning episode so that dependency retention also covers its retry. Historical
errors remain available through `take_cleanup_errors` and effect handles.

`StaticEpisode::retry_cleanup` provides the same retained-factory behavior for
externally driven typed plugins. The external host must admit the fresh action
and retain dependency leases. The Node typed bridge uses this entrypoint only
when its backend is asked to run another cleanup attempt. A consumed static
`FnOnce` failure or an abandoned static cleanup future remains blocked and cannot
be retried through this API. Ordinary Runtime preserves its existing policy of
draining failed `FnOnce` inverses.

The factory author must make another attempt safe after partial external work;
`FnMut` does not imply idempotence. Verus checks token/receipt transitions and
the actual payload storage and movement, treating each payload as an opaque
value. The executor's choice of which factory to return after invocation,
closure captures, domain allocation, panic handling and the truth of callback
results remain host obligations. In particular, storing exactly the supplied
retry value does not prove that an arbitrary executor returned the original
factory. The [container regressions](../crates/cordis-kernel/tests/cleanup_queue.rs)
check object identity and destruction; [Rust host regressions](../crates/cordis/tests/retry_cleanup.rs)
check distinct effect-group factories and successful retry, alongside the
[typed backend regression](../crates/cordis-node/tests/plugin_runtime.rs).
The canonical `cleanup-journal-discards-failed-inverse` and
`cleanup-queue-discards-retained-payload` mutations exercise selected-token and
actual-payload retention respectively. Local selected-proof experiments remain
separate from full release acceptance.

## Cleanup outcomes and host policies

| Outcome | Protocol meaning | Host policy |
| --- | --- | --- |
| `Succeeded` | Updates the receipt to authorize matching-generation finish. | Node and Rust report it after exhausting cleanup without consumed failures. Truth of the callback results remains a host obligation. |
| `Failed` | Keeps a blocking receipt; finish/removal through the shared API remain unavailable. Explicit retry replaces its state and ticket with a fresh action. | Node and retryable Rust inverses retain failed work and dependencies. Successful inverses are not replayed. Consumed static typed `FnOnce` failures remain blocked without a retry factory. |
| `Drained` | Updates the receipt to acknowledge consumed work and permit matching-generation finish. | Ordinary Rust records consumed `FnOnce` errors and continues draining; retained retryable failures still block. `Drained` is not a successful-recovery assertion. |

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
cargo test --offline -p cordis-driver --test shared_lifecycle --test cleanup_outcomes --test cleanup_resources
cargo test --offline -p cordis-driver --test episode_failure --test reservation_effects
cargo test --offline -p cordis-kernel --test cleanup_journal --test cleanup_queue
cargo test --offline -p cordis --test retry_cleanup
cargo test --offline -p cordis-node --test plugin_runtime typed_retryable_cleanup_recovers_only_on_a_new_host_attempt -- --exact
```

The proof boundary includes protocol state and the specified kernel calls. It
excludes callback truthfulness, arbitrary inverse effects, opaque value-handle
destruction and host routing, JavaScript, N-API/FFI, OS/file/network behavior, scheduling and
termination of arbitrary futures. In particular, a pending callback may never
return; safe retention is not eventual cleanup. The file case independently
checks write callbacks and resulting contents, and does not make disposal a
file-durability guarantee.

The engineering gain is that cleanup authorization and its kernel transition can
be reviewed and checked together in the code the shared API executes. A passing
protocol proof does not promote the surrounding runtime to an end-to-end theorem,
and an API/proof composition gap is not evidence of an observed upstream bug.
