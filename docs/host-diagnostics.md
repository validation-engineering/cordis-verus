# Explain lifecycle waits

English · [简体中文](host-diagnostics.zh-CN.md)

The Node host exposes the actual shared Driver state through `ctx.snapshot()`.
Use it to explain a missing dependency, a provider waiting for consumers, a failed
cleanup action, or an old episode rejection. Reading a snapshot does not drive
transitions, run `Service.check`, retry cleanup, or read service payloads.

```js
import { Context } from '@cordis-verus/compat-cordis';
const ctx = new Context();
try {
  const worker = await ctx.inject(['storage'], () => {});
  const entry = ctx.snapshot().plugins.find(node => node.id === worker.id);
  console.log(entry.blockers); // MissingProvider, port.service === 'storage'
} finally {
  await ctx.dispose();
}
```

Internal scheduler and native-plugin observations use a separate lightweight state
projection; full dependency graphs and diagnostic histories are built only for an
explicit snapshot request.

Both Cordis and Harness profiles expose the same diagnostic types. This is a host
observation interface, not another scheduler or a new proof of asynchronous callbacks.

## Dependencies and cleanup barriers

The snapshot retains `abi: 1` and adds `diagnosticsSchema: 'cordis.driver/v1'`.
IDs are decimal strings. Each plugin includes `dependencies`, `committed`,
`target`, `blockers`, and Node `host` observations in addition to its existing state.
Ports retain native key/realm IDs; `service` and `realmLabel`, where available, come
from names already interned by the host. No service lookup is performed for display.

| Reason | Meaning |
| --- | --- |
| `MissingProvider` | No matching provider declaration or retained publication was found. |
| `RealmMismatch` | The service was observed in other realms; this does not mean those providers are ready. |
| `ProviderUnavailable` / `PublicationMissing` | A provider exists but cannot currently satisfy this port. |
| `CheckNotEvaluated` / `CheckPending` | Availability has no usable cached result or has an outstanding check. |
| `CheckRejected` / `CheckError` / `CheckInvalidated` | The cached check returned false, threw, or lost its original input identity. |
| `CommittedConsumers` | These consumer episodes still retain this provider. |
| `PendingAction` | A real setup/cleanup ticket has not completed. |
| `RetiringChildren` | Retained children prevent the inactive owner from proceeding or being removed. |
| `CleanupFailed` | Cleanup failed and still requires explicit retry; successful inverses are not replayed. |
| `Failed` / `TargetChanged` / `Unsealed` | Setup failure, a current/committed dependency difference, or incomplete registration. |

Several reasons can coexist. A new availability check is not a blocker when the
Driver can still use its previously accepted cached result. Missing setup
dependencies are not reported as cleanup blockers. A cleanup retry already in
flight is `PendingAction`; a historical error string alone does not make it failed.

`committed` describes the publication and provider generation retained by the
current episode. `target` projects the kernel's current bindings. During replacement,
a binding can name an old provider with `publication: null` while root lookup already
sees another provider. Diagnostics preserve that transient instead of replacing the
kernel target with a root service lookup. Target mismatch is not automatically a bug.

## Labeled inverse observations

Name effects at registration to make cleanup actionable:

```js
ctx.effect(() => async () => { await flushBufferedWrites(); }, 'flush buffered writes');
const snapshot = ctx.snapshot({ includeTiming: true });
```

`host.action` includes the actual native ticket and current cleanup stage, such as
`draining-tasks`, `inverses`, `draining-calls`, or `closing-objects`. `host.inverses`
lists retained registrations: `id`, `parent`, `owner`, `generation`,
`registeredGeneration`, `label`, `state`, `attempts`, and an error when available.
States are `registered`, `waiting` for an effect initializer, `running`, or `failed`.
Raw plugin-returned inverses receive the label `plugin cleanup`. Nested effects and
each registration of a repeated function have distinct identities.

Prepared generation-zero resources retain `registeredGeneration: '0'`; their
`generation` changes only when an actual setup ticket adopts them. Cancellation
before setup keeps generation zero. Successful inverses are removed, while failures
retain their IDs across explicit `retryCleanup()`. Nested failed wrappers also retry;
a successful sibling is not replayed. This is a view of retained work, not an
unbounded audit history. Native Rust stream/object/session close failures are
reflected by the action stage and Driver error; this list does not invent JS inverse
IDs for operations inside a native library.

Default snapshots omit clocks, so repeated reads of unchanged state compare equal.
`includeTiming` adds `elapsedMs` to a running action and running/waiting inverse
attempts. It measures elapsed host time since that action/attempt began, including
waiting; it is not CPU time, deadlock detection, or a completion guarantee. It does
not assign a timer to every dependency blocker.

## Old episode errors and boundaries

`CordisError` preserves its code/message and can carry immutable `details`:
`owner`, `requestedGeneration`, `currentGeneration`, `removed`, and `operation`.
Managed continuation and Rust handle rejections use actual host identities. Equal
generations can still be rejected for a closed or replaced handle; generation
comparison alone does not determine admission. Missing native error fields are not
inferred by parsing a message. Reading or copying an error grants no authority.

Snapshot objects are copies and do not invoke effect metadata getters. Errors and
labels are application-provided text, so this is not automatic redaction. Service
values, callback objects and configuration payloads are not deliberately exported.

The ordinary Rust `Runtime::snapshot()` remains a separate
[diagnostic interface](diagnostics.md). In that host, a failed `FnOnce` inverse is
reported and cleanup continues; it is not the Node Driver's retained retry queue.
See [semantics](semantics.md). Neither diagnostic interface expands kernel proof
scope or closes the paper's host-boundary obligation.

Regression entry points: [Driver observations](../crates/cordis-driver/tests/driver_diagnostics.rs),
[Node observations](../tests/node-compat/diagnostics.test.mjs), and
[Rust object admission](../tests/node-compat/rust-objects.test.mjs).
