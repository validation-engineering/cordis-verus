# A03 compatibility iteration — 2026-10-08

This archive records a new run of the four compatibility comparisons after the
scoped provider/consumer update and cleanup-message changes. It retains the raw
runner reports separately from the [2026-10-06 baseline](../README.md); no older
failure, observation or input hash is replaced. These are finite behavior checks
against the snapshots in [`upstream.lock.json`](../../../upstream.lock.json).
They are not a proof of the JS coordinator, complete plugin migration acceptance
or the full release gate.

## Reports and reproduction

Restore the locked upstream checkouts and cached dependencies, then build the
native addon using the [preparation instructions](../../cases/lifecycle-cleanup.md#reproduce).
Run each command separately from the repository root so that a failed comparison
does not hide the remaining results. The [manifest](manifest.json) records the
commands, process exit codes, archive SHA-256 values and input verification.

| Report | Command | Result and scope |
| --- | --- | --- |
| [upstream-core.json](upstream-core.json) | `node scripts/check-upstream-core.mjs --backend=all` | **Failed, exit 1:** upstream 87/87, native 85/87, across the same 12 unchanged upstream behavioral suites; type-only tests remain outside this runner. |
| [node-compat.json](node-compat.json) | `node scripts/check-node-compat.mjs` | Passed, exit 0: six shared fixtures, including the upstream Timer plugin; exact upstream/native observations. |
| [node-profiles.json](node-profiles.json) | `node scripts/check-node-profiles.mjs` | Passed, exit 0: Cordis and Harness profiles, each compared against its own fixed upstream. |
| [harness-compat.json](harness-compat.json) | `node scripts/check-harness-compat.mjs` | Passed, exit 0: real Harness modules in global and scoped scenarios; this does not run the companion application's complete default workflow. |

The full core suite still reports failure: upstream passes 87/87 and native
passes 85/87. The remaining failed assertions are `Fiber inertia lock 2` and
`Fiber dispose error`. They retain the explicit committed-publication and cleanup-failure
contracts described in the [compatibility guide](../../node-compatibility.md#两个-profile).
They are not skipped, normalized or relabeled as conformance passes. Passing the
other comparisons does not override the full core result.

## What changed and what remains

`Fiber update config while injected service reloads` now passes for the scoped
direct update path. Coordination starts from an idle mutation queue, only for
external callers with no managed invocation origin in the Cordis profile. A
provider update may coordinate with updates of direct committed consumers made
in the same synchronous stack; a path through an intermediate node excludes the
case. Custom `Config` or `internal/update` hooks also exclude it. The shared
barrier waits for asynchronous cleanup/setup, while each returned Promise retains
its own result and failure.

Repeated updates of the same Fiber, transactions, restart/dispose, queued updates,
later microtasks, multi-hop graphs, custom configuration/hooks and the Harness
profile retain independent FIFO revisions. Managed callbacks and their completed
continuations do not gain external coordination authority. The full scope is in
the [update contract](../../node-compatibility.md#同栈-providerconsumer-更新).

`Plugin inactive context` now passes because cleanup-time resource-registration
errors contain the expected text. Registration remains forbidden. The
`CLEANUP_BLOCKED` code and the priority of `STALE_EPISODE` checks are retained.

These changes complete the implementation for the two accidental gaps in this
fixed suite. A03 still requires a real migration record, edits and rollback steps;
A04's diagnostics tasks and the host-to-paper refinement remain open. Upstream
versions, Node/platform, source inputs and native artifact identity are recorded
in the raw reports. Results do not extend automatically to another version or
platform.
