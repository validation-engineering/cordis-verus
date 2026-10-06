# Cleanup ordering and explicit failure recovery

A delayed consumer cleanup writes its final log line after its provider has
closed the file in both locked upstream runtimes. The same plugin source, run
through either cordis-verus compatibility profile, writes both lines successfully.
A separate workload demonstrates our explicit cleanup error and retry contract.

These are **fixed-version observations** on the platform in the linked report.
They do not claim a new upstream discovery, a latest-upstream result, complete
compatibility, or a proof of arbitrary JavaScript and file I/O.

## Reproduce

From a prepared checkout (validated here with Node 22.22.0 and the pinned Rust toolchain):

```sh
npm ci --ignore-scripts
npm run build:native
node scripts/reproduce-lifecycle-cases.mjs
```

If the ignored upstream source caches are absent in a clean clone, prepare just
the two runtime repositories first:

```sh
git clone --no-checkout https://github.com/cordiverse/cordis.git upstream/cordis
git -C upstream/cordis checkout --detach f8ea3cd50f1a5724e8e715995bcde131c9c12b2c
git clone --no-checkout https://github.com/deepseek-ai/deepseek-harness.git upstream/deepseek-harness
git -C upstream/deepseek-harness checkout --detach da00f7f5358f2949383b35c14f548bc20187d80c
```

Install the pinned Rust toolchain using `./scripts/install-verus.sh` if needed.
The runner refuses an upstream revision/tree mismatch,
a dirty upstream checkout, and a stale native addon. It does not fetch current
upstream code or change `upstream.lock.json`.

Results appear in `target/lifecycle-cases/report.json`. Each runtime also gets its
own bundled fixture, stdout/stderr, and actual `logger.txt`. The report preserves
raw ordered traces, process status, runtime versions, module/source/artifact
SHA-256 hashes, installed dependency evidence, and the machine/tool versions.

The [recorded result](../evidence/lifecycle-cases.json) is a snapshot. Run the command
above for current evidence; do not infer freshness from a green historical report.
The runner exits successfully only if all four executions reproduce their declared
observations. That means the comparison worked, **not** that all four runtimes
satisfied the desired final-write condition. An upstream fix will fail the declared
observation check and require reviewing the expectation.

## Case 1: the final log write survives consumer cleanup

**Classification:** failure of the stated final-write condition in the two pinned
versions, matching the class of defect reported in [Cordis issue #26](https://github.com/cordiverse/cordis/issues/26).
[Upstream PR #110](https://github.com/cordiverse/cordis/pull/110) independently discusses
this ordering problem. Those discussions motivate the workload; the results below
come from executing the actual source snapshots.

The setup creates a parent plugin with a file-backed service and an injected
consumer. The consumer writes `start` during setup and `end` after an asynchronous
pause in its cleanup. Disposing the parent also disposes the provider. The desired
condition is concrete: the `end` write is requested before provider close, succeeds,
and the resulting file contains both lines.

| Runtime actually executed | Locked source | Final write | File | Parent `dispose()` |
|---|---|---|---|---|
| Cordis `4.0.0-rc.10` | `f8ea3cd50f1a5724e8e715995bcde131c9c12b2c` | `ERR_STREAM_WRITE_AFTER_END` | `start` only | Fulfills |
| Harness `@deepseek-ai/cordis` `4.0.4` | `da00f7f5358f2949383b35c14f548bc20187d80c` | `ERR_STREAM_WRITE_AFTER_END` | `start` only | Fulfills |
| `@cordis-verus/compat-cordis` `0.1.0` | Exact source/artifact hashes in report | Succeeds | `start`, `end` | Fulfills |
| `@cordis-verus/compat-harness` `0.1.0` | Exact source/artifact hashes in report | Succeeds | `start`, `end` | Fulfills |

The important observed event order is:

```text
Both pinned upstreams: consumer cleanup starts → provider closes → final write fails
Both native profiles:  consumer cleanup starts → final write requested → provider closes → final write succeeds
```

This display selects the relevant events; the JSON retains every event in its
original order without sorting or normalization. It is a correctness workload,
not a timing or throughput benchmark.

All four executions use the identical [fixture](../../tests/cases/lifecycle-fixture.mjs).
Only resolution of the `cordis` import changes. Both native profiles use their
actual package entry points, including the Harness-specific Context constructor.
The child processes explicitly load the recorded native addon and clear `NODE_OPTIONS`
to avoid inheriting a different preload. No upstream source is patched. Relative to the public issue's example, this
fixture explicitly:

- names the service `caseLogger`, leaving the framework's diagnostic logger alone;
- joins plugin readiness and the initial write instead of waiting a fixed second;
- waits 30 ms rather than three seconds in the consumer cleanup;
- captures write callbacks and stream closure, then reads the actual file.

These changes make a small repeatable observation of the same dependency/cleanup
pattern; the fixture is not presented as a byte-for-byte copy of the issue.

### Why this relates to the verified kernel

The paper's **Definition 54 (Reliance)** describes installed consumers retaining
committed providers. The model's `Unload` rule requires the provider to have no
remaining reliance. In our executable kernel:

1. [`restoration_guarded`](../../crates/cordis-kernel/src/lib.rs) requires no live
   committed link to the restoring provider.
2. `Kernel::begin_cleanup` ensures that condition on success; `update_node` returns
   `Error::Relied` while a committed consumer remains.
3. [`Driver::drive`](../../crates/cordis-driver/src/lib.rs) admits cleanup actions
   through ordinary [`shared::LifecycleDriver::begin_cleanup`](../../crates/cordis-driver/src/shared.rs), which checks the
   action ledger and calls the verified kernel guard. The Node boundary returns
   those actions.
4. The ordinary JS [`Domain.dispatch` / `Fiber._cleanup`](../../packages/compat-cordis/runtime.js)
   executes callbacks and reports successful or failed completion before further
   lifecycle work proceeds.

The exact host method names and calls are inspectable in those files. See the
[paper review guide](../paper-review-guide.md) and [obligation ledger](../paper-obligations.json), item 54, for the formal
statement's status. `begin_cleanup` is an implementation admission guard; it is
not itself a claim that every JS callback refines the complete paper calculus.

The Verus result establishes the kernel transition contract. This experiment
checks the path through the actual Node host and callbacks. N-API, JavaScript
scheduling, the correctness of completion acknowledgements, Node streams and the
OS remain outside the completed end-to-end proof. Here the cleanup requests its
write but does not await the write callback; the final file check independently
waits for that callback and closure. Parent disposal alone is not advertised as
a durable file-flush guarantee. The runtime also cannot stop a plugin from
closing a resource manually outside its managed lifecycle.

## Case 2: cleanup failure is explicit and retryable

**Classification:** intentional contract difference, not an upstream bug claim.
The pinned Cordis test `fiber.spec.ts` explicitly expects disposal to fulfill
when a disposer throws, with the error sent to its logger.

The common plugin registers one inverse that throws on its first attempt. Every
runtime executes this same inverse once. Only after observing the first disposal
result does the fixture probe for an explicit `retryCleanup()` API.

| Runtime | First disposal | Explicit retry API | Attempts after retry |
|---|---|---|---|
| Both pinned upstreams | Fulfills | Absent | 1 (no retry attempted) |
| Both native profiles | Rejects | Available; succeeds after the failure condition is removed | 2 |

The second phase is an extension demonstration, not an unchanged-API compatibility
claim. Our failed inverse remains available for explicit recovery rather than
being counted as successful cleanup. Applications must handle rejection, decide
when retry is appropriate, and make retryable inverses tolerate partial work.
These observations do not prove rollback of arbitrary external side effects or
safe automatic retry.

The broader host regression coverage is in
[`disposal-failure.test.mjs`](../../tests/node-compat/disposal-failure.test.mjs),
including a failed consumer retaining its committed provider until recovery.
Those tests are executable evidence; they do not replace a proof of the host.
