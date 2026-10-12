# Rejecting lifecycle waits that retain their own caller

English | [简体中文](reentrant-wait.zh-CN.md)

A managed callback can keep a provider alive while asking to dispose that provider
or its owner. Waiting for that disposal would keep the callback open, while the
provider must wait for the callback's consumer to finish. Cordis Verus rejects
this request with `REENTRANT_MUTATION` and identifies the retained provider.

This case covers a specific lifecycle wait policy. It does not claim that arbitrary
Promises, Rust futures, locks or cross-process RPC calls cannot deadlock.

## Reproduce

From a prepared checkout with Node and the pinned Rust toolchain:

```sh
npm ci --ignore-scripts
npm run build:native
node --test --test-timeout=30000 tests/node-compat/wait-admission.test.mjs tests/node-compat/invocation-ledger.test.mjs tests/node-loader/rust-module-reverse.test.mjs
```

Both Cordis and Harness compatibility profiles are exercised. The dynamic module
suite loads real Rust libraries; it does not replace the bridge with a mock.
The source-bound [development record](../development-report.json) identifies the
complete verification run. These individual commands are behavioral tests.

## What happens

The test creates `consumer -> relay -> provider` committed service dependencies.
A separate `branch` owns the provider; the consumer is outside that subtree.

1. During consumer setup, waiting for either `provider.dispose()` or
   `branch.dispose()` is rejected. The error identifies the consumer, generation,
   target and actual retained provider. No retirement occurs during this check.
2. The same guard runs during consumer cleanup. The first cleanup deliberately
   fails; the provider and relay remain readable.
3. An explicit cleanup retry repeats the guard and succeeds. Ordinary external
   disposal can then release the relay and provider.
4. Separate tests admit unrelated and foreign-domain disposal, and two concurrent
   roots successfully complete nested `JS -> Rust -> JS -> Rust` calls.

An error response therefore explains a dependency that the callback currently
retains. It is not a timeout or a claim that the whole application is stuck.

## Requests that outlive a Rust future

A Rust plugin may send two JS requests, drop their futures and return. The real
transport records both before handing them to JS. Cancellation leaves those
records outstanding. An out-of-order reply consumes only its exact request;
the job cannot finish until the second reply arrives as well.

Each `RequestTicket` records the domain, owner, generation, session, job, request
and restoration permission. A receipt must match an outstanding ticket in every
field; mismatching, duplicate and foreign-domain receipts leave all records intact. All numeric identities cross JSON as decimal
strings. Request IDs never wrap or repeat within a domain; completed entries are
reclaimed. Native lifecycle wait admission checks this record instead of accepting
a JS `holding` flag. An expired receipt reports `StaleAuthority`.

The dynamic module regression runs two concurrent roots with matching numeric
session/job/request IDs and different domains. It rejects cross-domain and altered
replies, keeps both callbacks pending, accepts their actual replies and checks
that replay is rejected and module resource counters return to zero. The backend
regression additionally drops two futures from one job, cancels the job and sends
out-of-order success/failure receipts:

```sh
# Use the pinned toolchain through the repository environment.
bash -c 'source scripts/toolchain-env.sh; cargo test --offline --locked -p cordis-node --test plugin_runtime exact_receipts'
```

A failure reply confirms that the request ended; it does not confirm successful
resource cleanup. Stream/object failures stay in their resource journals for
retry. The receipt is an internal lifecycle identity, not an unforgeable security
credential. Plugin authors continue using the existing `ctx.call`, stream and
object APIs. Custom addons must advertise `requestProtocol: 1` in `rustInfo`; the
JS bridge rejects an older protocol before dispatch. The dynamic-library ABI is
unchanged.

## JS scopes and completed continuations

Setup, cleanup, owned tasks and effect initializers/inverses now register with the
native `InvocationLedger` before running callbacks. Registration checks the
current kernel generation. The returned `ScopeHandle` contains only domain and
scope identity; owner and generation stay in the native record. A callback's
success or failure ends its scope, while cancellation alone does not.

The actual wait path submits the local ALS scope handles to `check_scope_wait`.
Its checked scan admits the wait exactly when every supplied handle is known and
each still-live record has a current generation and no modeled conflict. A
completed nested scope cannot stop the scan before a live ancestor. A rejection
identifies the actual recorded owner and retained provider; JS supplies neither
owner metadata nor a `holding` override to this decision.

Completed records are reclaimed immediately. Their never-reused handles can
still identify inactive origins, allowing an ordinary detached continuation to
settle or close its domain after setup ends. Unknown or foreign-domain handles
are rejected, and duplicate completion cannot end another scope. Freshness of
completed continuations is still checked by the JS episode guard. This ledger
proves ownership bookkeeping and wait admission; it is not an independent cleanup
barrier or a proof that a callback has actually finished.

`invocation-ledger.test.mjs` observes real native commands, cancels two concurrent
tasks, settles them out of order (including rejection), and checks that only the
completed record disappears. Nested effects exercise the full supplied ancestor
scan. `snapshot().storage.invocationScopes` reports live JS records, not retained
effect resources. Custom addons must advertise `scopeProtocol: 1` in
`bindingInfo`; the public plugin API is unchanged.

## Paper, contract and runtime

| Obligation | Executable contract or evidence |
| --- | --- |
| Preserve the provider identities captured by this episode | `Kernel::committed_reaches` returns an answer exactly when the source generation is current; the answer equals the reflexive transitive closure of live committed edges. It does not use current target resolution. |
| Reject precisely the modeled wait conflict | `Kernel::check_wait` admits a current episode exactly when the invocation is not holding work open, or no member of its committed closure lies in the target's ownership subtree. A rejection contains a real retained member. |
| Connect dependency retention to cleanup ordering | `retained_dependency_blocks_cleanup` proves that a non-reflexive committed dependency path prevents the target's actual kernel cleanup guard from opening. |
| Call the checked implementation | `assertNotWaitingForAncestor` routes JS scopes through `check_scope_wait` and reverse Rust receipts through native `check_wait`; both compose ledger ownership with the same kernel method compiled by Cargo and checked by Verus. |
| Tie ownership to real native requests | `PluginContext::enqueue` calls `RequestLedger::issue`; `Backend::reply_request` calls `complete` under the same transport mutex; `Backend::poll` uses exact `job_drained`. Cancellation and future drop do not consume receipts. |
| Compose ownership with the wait decision | `RequestLedger::check_wait` requires a recorded complete receipt in the Driver's domain, then invokes the checked kernel policy with holding work open. `assertNotWaitingForAncestor` routes reverse callbacks through this path. |
| Record JS invocation ownership | `InvocationLedger::begin` records a current owner episode; `finish` removes exactly its live record and preserves all others. The monotonic identity counter prevents reuse without storing completed records. |
| Check every supplied ancestor | `InvocationLedger::check_wait` returns an allowed result exactly when every supplied scope is known and every live record is current and conflict-free; `any_live` checks the same records for domain settlement. |
| Detect incorrect implementations | Canonical negative mutations admit a retained provider, admit a stale episode, or reject an unrelated target. They target the real executable decision. Additional mutations accept altered request ownership, drain before reply, or discard live ownership in wait admission. Scope mutations discard live ownership or stop at a completed nested scope. Full negative regression remains separate from development validation. |

Read [wait_guard.rs](../../crates/cordis-kernel/src/wait_guard.rs), the
[request ledger](../../crates/cordis-kernel/src/request_ledger.rs),
[invocation ledger](../../crates/cordis-kernel/src/invocation_ledger.rs),
[transport](../../crates/cordis-node/src/plugin.rs),
[Driver](../../crates/cordis-driver/src/lib.rs), and the
[host guard](../../packages/compat-cordis/runtime.js). The graph specification is
independent of traversal: reachability is membership in every dependency-closed
set containing the caller. The implementation uses the existing kernel invariant
that live commitment positions decrease along dependency paths.

Definition 54, L-Unload and Theorem 70 of the
[locked paper](https://arxiv.org/pdf/2608.25512v1#page=36) constrain dependency
retention and release ordering. This wait-admission policy is an additional host
rule that helps implement those constraints. It does not complete Theorem 73's
progress obligations or change the paper coverage ledger.

## Verification boundary

The native request ledger proves exact issuance, receipt consumption, pending-job
queries and their composition with the wait guard. The JS invocation ledger also
proves registration, exact completion, record reclamation and the supplied scope
scan. Both Rust implementations are compiled by Cargo and checked by Verus.
Ordinary host code still captures
owner/session/job metadata at context creation, keeps payloads and wakers aligned
with records under the mutex, dispatches JS, reports the actual result, preserves
complete AsyncLocalStorage ancestry and raises the error. JS also chooses when to
register and report callback completion. These integration facts have tests, not
a whole-host refinement proof: the native scan cannot detect an ancestor omitted
by the host. Scope handles and request receipts are internal identities, not
security credentials against arbitrary code in the same process.

The decision observes one immutable kernel state and grants no reservation for a
later state. Callback termination, scheduler fairness, arbitrary callback effects,
domain mutation queues and general RPC wait cycles remain outside the contract.
A detached JS-only continuation can retain its episode without holding an action;
a detached reverse-call continuation cannot reuse a receipt after its reply.
Backend shutdown abandons the transport and reports failure; it is not a successful
resource-cleanup acknowledgment.

Next, include this case in the standalone Harness failure report and review the
remaining callback-result and ALS ancestry boundary. Existing cleanup
report, retry and stale-receipt guarantees are reviewed separately in the
[cleanup protocol](../cleanup-protocol.md).
