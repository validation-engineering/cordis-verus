# Updating a provider while Child cleanup fails

[简体中文](update-recovery.zh-CN.md) · [Paper review](../paper-review-guide.md) · [Original R01 obligations](../r01-prewrite-replay.md)

This case updates one provider used by a consumer that owns one Child. An actual
reversible write prevents the Child's inverse from restoring its expected state.
The runtime retains the consumer and provider until explicit retry succeeds,
restores the old data, then activates the updated provider and a fresh Child.
It runs without Node.js, a network service, or arbitrary asynchronous callbacks.

The deliverable is `provider-consumer-one-child/v1`. Its claims combine verified
kernel contracts with an integration test of the ordinary Rust host. This is not
a proof of the entire host scheduler, R01, Equation (55), or the whole paper.
Existing R01 closure criteria and all original-paper audit/refutation statuses
remain unchanged; general recovery, global termination and confluence are deferred.

## Reproduce

From the repository root with the pinned toolchain and cached dependencies:

```sh
# One end-user example; prints checked events and a JSON result.
cargo run -p cordis-verus --example update_recovery --locked --offline

# Native owner/ticket case + real Runtime case + action-ticket regressions.
python3 -B scripts/reproduce-update-recovery.py --offline

# The same reproduction plus fresh selected kernel proofs.
python3 -B scripts/reproduce-update-recovery.py --offline --proof

# Five strict mutations of production implementations.
python3 -B scripts/check-profile-controls.py update-recovery
```

Omit `--offline` on the Cargo/reproduction commands if dependencies need fetching.
Prepare Verus with `./scripts/install-verus.sh` before requesting proof checks.
`target/update-recovery/report.json` records source hashes, exact commands, raw
logs, observed data and whether proofs actually ran. A run without `--proof`
records `not_run`; it never imports old proof counts. The mutation report is
`target/update-recovery-controls/report.json`. Whole-kernel development acceptance
is recorded separately by `python3 -B scripts/record-development.py --offline`.
These commands do not perform release/platform acceptance or full negative regression.

## What happens

The provider supplies a reversible counter. The consumer explicitly requires it
and provides a marker. The Child explicitly requires both services. Thus the
Child has real committed service dependencies; parentage alone is not used as a
release-ordering premise.

| Stage | Old counter `(value, inverse depth)` | Expected result |
| --- | --- | --- |
| Provider setup | `(10, 0)` | Service published |
| Consumer and Child each write | `(13, 2)` | Both real inverses retained |
| Inject an explicit interfering write | `(17, 3)` | Fault has its own inverse |
| Request provider update | `(17, 3)` | Child restore fails; consumer/provider cannot clean up |
| Poll again without retry | `(17, 3)` | Failure remains; no implicit retry |
| Restore the injected write | `(13, 2)` | Original Child inverse becomes applicable |
| Explicit Child retry | `(11, 1)`, then `(10, 0)` | Child, consumer, then old provider release |
| Updated provider and fresh Child | New counter `(23, 2)` | New data starts at `20`; both plugins run again |
| Final shutdown | New counter `(20, 0)` | All three plugins removed |

The injected write is deliberate use of a raw resource handle, outside the
plugins' managed operations. The guarantee is checked interference rejection and
retention, not exclusion of all external writes or automatic rollback. The native
case additionally attempts a forged successful acknowledgement for a managed
inverse, checks old and duplicate replies, verifies fresh action/restore attempts,
and verifies that an old episode reply cannot change the new owner's queue.

## Paper → contract → executable path → evidence

The paper references use the pinned version in `upstream.lock.json`. Definition
54 / L-Unload are on pages 36–37; PR-01 in the paper review guide records their
precise interpretation. Strict inverse domains are the explicit R1-DOMAIN
revision of the component/inverse constraints, not a claim that every original
operation is a total function.

| Guarantee | Executable contract and proof | Actual caller / evidence |
| --- | --- | --- |
| Preserve committed providers during recovery (Definition 54, L-Unload) | `Kernel::begin_cleanup` / `finish_cleanup`; `LifecycleState::binding_protects_provider`; `cleanup::update::failed_child_keeps_chain` derives protection for both levels over arbitrary finite cleanup-command histories without a new accepted Child authorization | Shared/native lifecycle adapters; both scenarios inspect actual committed providers and reject premature cleanup |
| Failure retains a real inverse (strict component/inverse interpretation) | `Inverse::restore_following` checks value **and depth**; `CleanupQueue::restore_value` retains the same inverse after rejection; `NativeRuntime::fail_managed_execution` derives its failed lifecycle receipt from actual failed queues | `Setup::update_reversible` and native registered root; the counter remains `(17, 3)` after rejection |
| A host success flag cannot replace managed restoration | `RecordedExecution::complete_result` rejects acknowledgements for managed slots; data restoration uses `dispatch` and the original inverse implementation | Native case attempts forged success before and after retry; both are rejected |
| A retry is a new attempt, old replies cannot release (implementation protocol enforcing L-Unload order) | `retry_execution`, `consumed_ticket_never_returns`, exact `CleanupQueue::complete_result` ticket/issued checks | Native case checks action and restore-attempt freshness; `cleanup_protocol` regressions exercise stale action reports, including new episodes |
| Child request and inverse refer to the same owned Child | `SetupWork::enqueue_native_child` creates the pair atomically; `register_shared_child` binds the parent episode; `retire_shared_child` produces the actual retirement; native `release` records Child Unload separately | Native case consumes the actual queued request and inverse; ordinary host uses `Setup::mount`; Child retirement is never advertised as its completed Unload |
| Restore before provider release, then activate the update | `release_execution` derives the completion outcome from drained work/queues and performs actual L-Unload; `begin_managed_execution` supplies the next episode | Runtime case uses `update_plugin`, `retry_cleanup`, `settle`, and `dispose_all`; it asserts release/setup event order and old/new values |

The chain theorem requires **actual committed bindings** and a failed receipt.
Begin constructs bindings; the strengthened failure contracts propagate the
queue failure through `LifecycleState`, `NativeHost` and `NativeRuntime`. It does
not assume that cleanup succeeded. For the finite history theorem, every step
must satisfy the production `cleanup_step` relation; `execute_cleanup` and
`run_cleanup` provide that relation. Normal retry success is established by the
actual inverse; no theorem asserts that an arbitrary interfering environment
will eventually restore the required state.

Sources: [chain proof](../../crates/cordis-kernel/src/lifecycle_state/cleanup/update.rs),
[cleanup protocol](../../crates/cordis-kernel/src/lifecycle_state/cleanup.rs),
[real work/queue release](../../crates/cordis-kernel/src/lifecycle_state/execution.rs),
[managed acknowledgement boundary](../../crates/cordis-kernel/src/managed_lifecycle_callbacks.rs),
[native scenario](../../crates/cordis-kernel/examples/support/update_recovery.rs),
[Runtime scenario](../../crates/cordis/examples/support/update_recovery.rs).
Each scenario is shared by its runnable example and integration test.

## Acceptance and limits

The five negative controls change real implementations: promote a failed report
to success; bypass the release receipt; discard a retained payload; ignore inverse
depth; split the Child request from its inverse. Each requires a fresh selected
positive proof, successful whole-mutant compilation, and rejection at the named
contract. A timeout, parse error, or unrelated failure does not count.

No arbitrary callback, destructor, JavaScript, external I/O, operating-system
persistence or scheduler fairness theorem is claimed. The host closures and
update routing are integration-tested. Protocol safety and the selected data
operations are verified in the kernel source also compiled by Cargo. Existing
plain `FnOnce` failure/`Drained` behavior is not used as successful restoration
in this case. Full parent-function equivalence, arbitrary multi-owner recovery,
Node recovery, and all-schedule confluence remain in the original backlog.
