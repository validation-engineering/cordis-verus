# Generated lifecycle evidence

English · [简体中文](generated-lifecycle.zh-CN.md) · [Original update/recovery case](update-recovery.md)

The `provider-consumer-one-child/v1` profile connects five useful guarantees to
real execution, executable Verus contracts and deliberately broken implementations.
It extends the fixed example with generated histories; it does not close R01 or
the whole-paper obligations. See the [ownership and review map](../review-map.md).

## Reproduce

Use the repository's pinned tools and installed offline dependencies. The Native
campaign and replay need Rust and Python. The comparison additionally needs Node,
the locked Cordis checkout and npm dependencies. Verus is needed for paired proof
controls; it is not a user application runtime dependency.

```sh
python3 -B scripts/check-lifecycle-campaign.py native --offline --seed 260824 --cases 96
python3 -B scripts/check-lifecycle-campaign.py compare --offline --build --seed 260824 --cases 48
python3 -B scripts/check-lifecycle-campaign.py controls --offline --seed 260824 --cases 12
```

For integrated acceptance, finish source changes first, run the development
recorder once, then the three commands above, the existing exact comparison, and
the audit. The `--build` comparison option can be omitted after a fresh development
run has built the same sources.

```sh
python3 scripts/record-development.py --offline
# Run native, compare and controls as above on these unchanged sources.
node scripts/check-node-compat.mjs
python3 -B scripts/check-lifecycle-campaign.py accept
```

Results, complete inputs, raw stdout/stderr, commands, versions and hashes are
under `target/lifecycle-campaign/`. `acceptance/report.json` binds the final source
to development, generated execution, comparison, reduction and strict proof
records. The audit checks evidence; it does not execute a new proof. Reports in
`target` are local artifacts, not automatically published GitHub assets.

## What actually executes

| Profile | Real executor | Observations and limits |
| --- | --- | --- |
| `native-managed/v1` | [`lifecycle_scenario`](../../crates/cordis/examples/lifecycle_scenario.rs) calls `NativeRuntime`, recorded root/Child execution and actual inverse dispatch | Values **and depth**, target/committed IDs, owner/Episode/action/restore identities, original Child handles, publication visibility, retained inverse slots and every intermediate state. The observer intentionally holds value handles to inspect their final state; this is not an allocator reclamation test. |
| `plugin-lifecycle/v1` | [One shared JS fixture](../../tests/compat/lifecycle-scenario.mjs), bundled against either the native facade or locked original Cordis | Actual public plugin setup, publications, callback attempts, errors, resource identities, owner/Episode relationships and callback order. Native diagnostics additionally check committed-provider retention. JS callback effects are not thereby proved. |

The Native generator varies registration order, bounded scalar parameters,
failure at the Child or consumer, same-value interfering writes, repeated failed
retries, obsolete/duplicate replies and successful updates after recovery. Every
full Native case must successfully execute multiple root/Child episodes and
restore all values to their initial value/depth at shutdown. Admitted, invalid
command and interference strata must all occur. Rejecting everything cannot pass.

The generator's small arithmetic oracle chooses inputs and checks snapshots. It
does not supply the executor with ghost journals, histories, receipts or expected
results. [`scenarios.py`](../../scripts/lifecycle/scenarios.py) and
[`oracle.py`](../../scripts/lifecycle/oracle.py) are ordinary test code, not an
additional implementation or a formal proof of the generator.

These are finite seeded scenarios with deterministic coverage strata, not a
uniform sample of arbitrary plugins. Native receipt operations have no matching
public original-Cordis API. They remain Native tests and are explicitly
unsupported in the plugin comparison. Arbitrary async schedules, general alias
transport, opaque `Arc<T>` effects and global termination remain outside this
profile.

## Compare without hiding differences

The report records attempts, completed processes, supported cases and four
outcomes: `matched`, `intentional_difference`, `unsupported`, and
`unexplained`/`inconclusive`. An unexplained result, crash or timeout blocks
acceptance. There is no headline “compatibility percentage”. A successful process
may still report an unsupported operation.

The only ID projection is a checked bijection between real registration IDs and
observed births. It preserves parents, distinct Child births, Episodes and
resource bindings. Raw IDs, errors, snapshots and the complete ordered event list
remain in the evidence. No callback events are sorted to make results equal.
Native-only diagnostics are retained separately, because the original public API
does not expose that state. The original fixed differential fixture still uses
its existing exact comparison with **no normalization**.

Two differences are reviewed for this precise fixture and locked revision:

| Policy | Native facade | Locked original Cordis | Acceptance condition |
| --- | --- | --- | --- |
| `dependency-cleanup-order/v1` | Child, consumer, then provider callbacks | For this update fixture: provider, consumer, Child; for consumer-first shutdown: consumer, Child, provider | Check each full event list against the corresponding exact order and identities; require all other public states/outcomes to match in the no-fault cases. This is not a claim about all upstream schedules. |
| `cleanup-failure-retention/v1` | A throwing cleanup blocks the update, retains old dependencies and stops release of the dependent providers | `_unload` catches/logs the callback error, consumes that disposable and continues the update | Check the injected error, exact failed actor, retained resources, complete intermediate state and both ordered traces. An arbitrary mismatch is not covered by this policy. |

The upstream rationale is in the immutable checkout's
`packages/core/src/fiber.ts`, `_unload`; the lock and source bytes are bound in the
bundle record. The Native cleanup policy is linked to
[`LifecycleState`](../../crates/cordis-kernel/src/lifecycle_state/cleanup.rs)
through the shared Driver. A public API test of that bridge is empirical evidence,
not a proof of JavaScript or the FFI.

The retry extension explicitly observes `settle_fault` after the failed update,
then repairs the fault and calls `retryCleanup`. The domain can still have an
unobserved error queued after an update promise rejects; the scenario records
that second diagnostic rather than discarding it. Original Cordis has no matching
public `retryCleanup`, so this whole extension is reported as unsupported while
the Native recovery, another update and shutdown are checked independently.

## Test the same broken implementations

[`negative-controls.update-recovery.json`](../../scripts/negative-controls.update-recovery.json)
is the existing canonical five-control selection. The paired runner copies the
actual workspace, changes exactly that implementation expression, compiles it,
then uses both real behavioral callers and the unchanged strict proof harness.

| Mutation | Behavioral caller |
| --- | --- |
| Promote failure to success | Actual `execute_cleanup` command loop and its repeated-failure test |
| Bypass the successful cleanup receipt | The same real dispatcher test, including rejected release and provider retention |
| Drop the retained payload | Queue test with an owned payload, address and destructor counter; generated resource traces where applicable |
| Ignore inverse depth | Same-value interference test and generated Native histories |
| Split Child request from its inverse | Original-handle/actual-registration test and generated Child observations |

The Native generator calls managed primitives directly, so it does not cover
mutations solely in `execute_cleanup`. The dedicated dispatcher caller covers
those mutations. `generated` and `targeted` behavioral results are kept separate
as detected, not detected or inconclusive, with the applicability boundary.
A test counts as detected only when the designated test executes and fails at its
reviewed assertion. Compile failures, an empty selection and unrelated panics do
not count. Proof rejection requires a fresh selected positive, whole-mutant
compilation and exactly the designated contract diagnostics. Full negative
regression and release qualification remain separate and are labelled `not_run`.

The inverse-depth control is also reduced. Every candidate must pass against the
unmodified binary and fail against the mutated binary with the **same guarantee,
operation and actor**. The reducer deletes commands, then checks that no single
remaining command can be deleted under this predicate. It claims one-deletion
minimality, not a globally shortest program. It saves original/reduced complete
commands, all trial logs, binary hashes and a replay command in the reduction
report. For example:

```sh
python3 -B scripts/check-lifecycle-campaign.py replay --offline --input target/lifecycle-campaign/native/scenarios.json
```

The reduction report's `replay` command selects its saved mutant and expected
failure. A reduced prefix is evidence of that failure, not a full successful
shutdown scenario. `controls --behavior-only` is an integration pilot and cannot
satisfy paired or integrated acceptance.
