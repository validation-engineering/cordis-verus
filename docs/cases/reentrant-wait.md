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
node --test --test-timeout=30000 tests/node-compat/wait-admission.test.mjs tests/node-loader/rust-module-reverse.test.mjs
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

## Paper, contract and runtime

| Obligation | Executable contract or evidence |
| --- | --- |
| Preserve the provider identities captured by this episode | `Kernel::committed_reaches` returns an answer exactly when the source generation is current; the answer equals the reflexive transitive closure of live committed edges. It does not use current target resolution. |
| Reject precisely the modeled wait conflict | `Kernel::check_wait` admits a current episode exactly when the invocation is not holding work open, or no member of its committed closure lies in the target's ownership subtree. A rejection contains a real retained member. |
| Connect dependency retention to cleanup ordering | `retained_dependency_blocks_cleanup` proves that a non-reflexive committed dependency path prevents the target's actual kernel cleanup guard from opening. |
| Call the checked implementation | `assertNotWaitingForAncestor` sends `check_wait` through the real Driver; the Driver calls the same kernel method compiled by Cargo and checked by Verus. |
| Detect incorrect implementations | Canonical negative mutations admit a retained provider, admit a stale episode, or reject an unrelated target. They target the real executable decision. Full negative regression remains separate from development validation. |

Read [wait_guard.rs](../../crates/cordis-kernel/src/wait_guard.rs), the
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

The host still supplies invocation ownership, the live `holding` fact and complete
AsyncLocalStorage ancestry, selects the correct Driver domain, translates JSON and
actually raises the error. These facts and the JS/FFI connection have tests; they
are not made true by the kernel proof. The decision observes one immutable kernel
state and grants no reservation for a later state. Callback termination, scheduler
fairness, arbitrary callback effects, domain mutation queues and general RPC wait
cycles remain outside this contract. Completed continuations retain episode
identity but do not block a wait unless they still hold independent native work.

The next integration goal is to connect those invocation and transport facts to
checked request ownership, then add this case to the standalone Harness failure
report. Existing cleanup report, retry and stale-receipt guarantees are reviewed
separately in the [cleanup protocol](../cleanup-protocol.md).
