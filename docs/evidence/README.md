# Compatibility evidence

These are complete, byte-for-byte copies of locally generated JSON reports from
2026-10-06, using Node 22.22.0 on macOS arm64. They record finite behavioral
comparisons against the exact upstream snapshots in
[`upstream.lock.json`](../../upstream.lock.json). They are not Verus proofs,
full third-party plugin compatibility, or cross-platform release acceptance.

The complete upstream core run **failed**: the original implementation passed
87/87 tests; the native implementation passed 83/87, with four failures and no
pending tests. This failure is retained in the report and the command exited 1.
Passing selected scenarios below does not override this result.

## Reports and reproduction

Prepare the locked runtime checkouts, dependencies, and native addon using the
[lifecycle case's preparation commands](../cases/lifecycle-cleanup.md#reproduce).
See the [contributor instructions](../../CONTRIBUTING.md) for the broader workflow.
Use `node scripts/build-node.mjs --offline` when the native dependencies are cached.
Run the commands separately so a nonzero result remains visible and does not
prevent collecting the other reports.

| Archived report | Command from repository root | Result and scope | Original output |
| --- | --- | --- | --- |
| [upstream-core.json](upstream-core.json) | `node scripts/check-upstream-core.mjs --backend=all` | **Failed, exit 1:** 12 unchanged upstream behavioral suites; upstream 87/87, native 83/87. Type-only tests are excluded. | `target/upstream-core/all.json` |
| [node-compat.json](node-compat.json) | `node scripts/check-node-compat.mjs` | Passed, exit 0: six selected shared fixtures, exact native/upstream observation equality, no trace normalization. | `target/node-compat/differential.json` |
| [node-profiles.json](node-profiles.json) | `node scripts/check-node-profiles.mjs` | Passed, exit 0: separate Cordis and Harness profile fixtures, each run against its own upstream and native backend. | `target/node-compat/profiles.json` |
| [harness-compat.json](harness-compat.json) | `node scripts/check-harness-compat.mjs` | Passed, exit 0: real Harness modules in global and scoped scenarios, both backends, exact observation equality. | `target/harness-compat/all.json` |

The separate [lifecycle-cases.json](lifecycle-cases.json) archive, described in
[the lifecycle case](../cases/lifecycle-cleanup.md), comes from
`node scripts/reproduce-lifecycle-cases.mjs` and its local output
`target/lifecycle-cases/report.json`. Its successful status means the four real
executions reproduced their declared observations: the two pinned upstreams lose
the consumer's final log write, while both native profiles preserve it. It is
**observed-as-declared**, not a statement that all four runtimes conform to the
desired lifecycle condition. It also demonstrates the distinct cleanup-error and
retry contracts; see the case page for raw-trace interpretation and boundaries.

The six shared fixtures cover core lifecycle, the upstream Timer plugin, events,
child readiness, realms, and shadow realms. The Harness module comparison is
separate from the companion application's complete default Web/standard and
headless acceptance workflows. These reports do not establish that every
original Cordis or Harness plugin works unchanged.

The locked Cordis snapshot is `f8ea3cd50f1a5724e8e715995bcde131c9c12b2c`
(`cordis` 4.0.0-rc.10). The locked DeepSeek Harness snapshot is
`da00f7f5358f2949383b35c14f548bc20187d80c` (its vendored Cordis package is
`@deepseek-ai/cordis` 4.0.4). They are distinct compatibility targets, not an
assertion about the latest upstream release at reading time.

## Four observed core differences

The following names are copied from the failed assertions in
[upstream-core.json](upstream-core.json). They describe compatibility differences;
none is presented here as a confirmed upstream defect.

| Upstream test | What the run observed | Interpretation and review boundary |
| --- | --- | --- |
| `Fiber inertia lock 2` | At the fixture's 1,200 ms fake-timer checkpoint, upstream expects `ACTIVE` (2); native reports `UNLOADING` (5). | Removing and re-providing a root service during setup does not cancel the native episode's already-started withdrawal. Upstream's provider-fiber epoch can return to the same identity in this fixture; native retains the withdrawn publication identity through cleanup. This is an observable lifecycle difference. |
| `Fiber dispose error` | Upstream expects disposal to resolve after an inverse throws. Native rejects with an aggregate cleanup error. | Native reports failed cleanup and retains the resources needed for retry. This is an explicit cleanup-error contract difference, not a passing compatibility case. |
| `Fiber update config while injected service reloads` | The expected activation trace is `[[1,"old"],[2,"new"]]`. Native produces `[[1,"old"],[2,"old"],[2,"new"]]`, with the final consumer active on the new configuration. | Separate external updates run through the native host's mutation queue. The consumer can reactivate between the provider update and its own queued update. This is a reproducible update-coalescing compatibility gap; it must not be dismissed as benchmark noise or a harmless assertion-text mismatch. |
| `Plugin inactive context` | The test expects cleanup-time plugin/effect/event registration to throw a message containing `inactive context`. Native rejects those operations with `CLEANUP_BLOCKED`: `Recovery transactions cannot acquire new resources`; the assertion failure is then reported as a cleanup error. | Registration is rejected and the attempted child callback is not executed. The observed mismatch is the error contract/message, not permission to create new resources during cleanup. |

The two scheduling-related failures (`inertia lock 2` and configuration update)
were also rerun in isolation using the unchanged upstream tests and failed again.
That diagnostic selected only two tests; its 85 unselected cases are **not** a
second complete conformance run. Its unmodified [Vitest JSON](additional-differences.json) and
[process log](additional-differences.log) are archived separately. The exact
command, from repository root, was:

```sh
CORDIS_CORE_BACKEND=native node node_modules/vitest/vitest.mjs run \
  --config tests/upstream-core/vitest.config.mjs \
  --reporter=json \
  --outputFile=target/upstream-core/additional-differences.vitest.json \
  --testNamePattern='inertia lock 2|update config while injected service reloads' \
  > target/upstream-core/additional-differences.log 2>&1
```

It exited 1 with 0 passed, 2 failed and 85 unselected tests. Unlike the full
runner's JSON, this diagnostic Vitest output does not contain an independent
source-hash manifest. A separate local native diagnostic helped inspect the full
configuration trace and admission errors; its probe source is not an archived
reproduction entry point. The full report above remains the primary acceptance
result.

## Source and artifact binding

Each archived JSON preserves its original fields, observations, failure messages,
input hashes, and embedded `nativeBuild` evidence. The four reports have 319,
308, 327, and 464 `inputs` entries respectively, in table order. Every entry was
rehashed against the local files after all four commands completed; all matched.
No failed result, stack trace, or observation was rewritten during archiving.

The runners verify the locked upstream commit/tree and that its source checkout
is unchanged. Native reports bind the addon bytes to its build source hashes.
The full core, profile, and Harness runners additionally record an aggregate
hash of the installed test dependencies. The six-fixture differential records
its dependency lock and bundled inputs but does not have the same whole-installed-
dependency aggregate. A hash match establishes which inputs produced a record;
it does not establish correctness beyond the report's actual checks.

Archive SHA-256 values, measured directly from the unmodified original bytes:

| File | SHA-256 |
| --- | --- |
| `upstream-core.json` | `6aa0c29eb0acf9936e6c206c9a482f19684449f6fc483a1b9bb56d8bee9af95d` |
| `node-compat.json` | `63d77a19a9dbad8ce637412a08c9b71e87b11857174a7082b55f5f54c9af080c` |
| `node-profiles.json` | `30474cd7fd171c6b07e2da40be07cf90c98481cfebff269b237749ab2f9ecf33` |
| `harness-compat.json` | `b227a031b8ca9e2b7d4b63a02952d0fadb5bf67d68d58545c551c0f85d3a4ea2` |

The upstream-core runner's original process logs and detailed Vitest JSON remain
in `target/upstream-core/{upstream,native}.log` and
`target/upstream-core/{upstream,native}.vitest.json`. Copies prefixed with
`initial-` preserve the first complete run locally. The other three runners embed
their compared observations and, where captured, subprocess diagnostics in their
JSON; they do not each create a separate standalone process-log file. Bundles
remain under `target/node-compat/` and `target/harness-compat/bundles/`.

`target/`, upstream checkouts, dependencies, and native binaries are ignored local
artifacts. A fresh clone must restore/build these inputs before checking hashes
or rerunning the commands. Paths inside the raw JSON are preserved from the
machine that produced it. Rerunning on another checkout may produce different
bundle bytes or diagnostic paths; a new result should be archived as new evidence,
not used to edit these original observations into a passing result.
