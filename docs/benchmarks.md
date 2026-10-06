# Local performance measurements

The benchmark is an independent measurement command, not a proof or release gate.
It performs no network requests or LLM calls. Measurements describe the current
machine, Node version, build profile and source snapshot. No absolute performance
budget or accepted multi-platform result is implied.

```sh
# Use the same Node version for build and measurement; the development baseline is 22.22.
node scripts/build-node.mjs --offline
node scripts/benchmark.mjs --output target/benchmarks/baseline.json
node --test tests/benchmarks/*.test.mjs
```

The last command tests statistics, report validation, baseline policy, and a small
native worker smoke case. The measurement CLI does not compile or verify Rust.
It rejects stale native source/build evidence and a stale Rust SDK fixture.
Independent-module scenarios also verify both dynamic-library paths and hashes. Reports
are local JSON, defaulting to `target/benchmarks/latest.json`.

Native bindings use Cargo's optimized release profile (optimization level 3).
Debug assertions and overflow checks remain enabled, and the build verifies
Cargo's reported profile before copying the artifact. This improves execution
without removing the runtime checks used during development.

## Method

Each scenario starts a fresh Node process. Module loading, process startup and
initial fixture setup are outside the timer. There are 5 warmup batches and 25
recorded batches by default, executed sequentially with concurrency one. Use
`--warmup`, `--samples`, `--scale`, `--fanout`, `--stream-items`, or repeat `--scenario`
to select another explicit workload. `--scale` multiplies the ordinary batch sizes;
provider withdrawal always measures one prepared group per sample.

| Scenario | Default operations per batch | Measured boundary |
| --- | --- | --- |
| `native.lifecycle` | 20 cycles | Rust shared driver via N-API and JSON: mount, setup completion, retire, cleanup completion and removal |
| `facade.syncService` | 500 calls | Committed JS service lookup and synchronous call |
| `facade.asyncService` | 100 calls | JS service lookup, resolved Promise and await |
| `rust.syncService` | 100 calls | JS to Rust JSON DTO service |
| `rust.asyncRoundTrip` | 10 calls | JS → Rust Future → async JS service → Rust → JS |
| `rust.pullStream` | 2 streams × 16 items | Rust stream open, sequential pulls, reverse record calls, EOF and close, amortized per item |
| `rust.checkpointReplace` | 10 replacements | Alternate two independent Rust libraries on one Harness Context, including consumer cleanup writes, logical checkpoint transfer and reactivation |
| `facade.mountDispose` | 5 cycles | Awaited plugin activation and journaled effect cleanup |
| `facade.providerWithdrawal` | 1 group with 16 consumers | Retire provider and drain dependent cleanup; preparation and final graph disposal are outside the timer |
| `facade.settledReadiness` | 1 sweep of 16 consumers, each with 8 providers | Harness-profile readiness reads on a settled graph; construction, activation and final cleanup are outside the timer |

The native lifecycle measurement includes JSON encoding/decoding, N-API and the
ordinary Rust driver. It is **not an isolated Rust kernel benchmark**. The stream
fixture intentionally calls back into JS when pulling/closing, as the existing
SDK integration fixture does; it is not a zero-callback stream implementation.
The suite asserts results, drained cleanup and provider/consumer ordering.

`performance.now()` measures each whole batch. The report retains every raw batch
time and CPU sample, derives nanoseconds per unit and uses nearest-rank p50/p95/p99.
These are **batch-amortized latency distributions**, not individually sampled
request-tail latencies. Throughput is total units divided by total batch time;
there is no empty-loop subtraction or claimed zero-cost instrumentation. Synchronous
loops do not introduce an await per call. Async workloads execute sequential awaits.

Each worker records RSS, V8 heap, external/ArrayBuffer memory and process high-water
RSS before warmup, after measured batches and after final cleanup. By default a
forced GC runs before warmup and after cleanup, never inside timed batches; use
`--no-gc` for natural collection. Retained deltas can be negative, and neither heap
nor RSS alone proves absence of native leaks. Event-loop delay is sampled at 1 ms
resolution across the measurement phase, including between-sample graph work.
It is observational; it is not exact native-boundary accounting or a hard maximum
main-thread work slice. Run on an otherwise quiet, thermally stable machine, repeat
runs, and inspect raw samples before adopting a budget.

## Source binding and comparison

JSON records include the full benchmark/core/native source hash map, harness digest,
native manifest, binary, build report and SDK fixture hashes, actual platform/CPU,
OS release, Node/Node-API/module ABI, driver ABI and compiler profile. Sources and
artifacts are checked again after measurement. Generated timestamps and manifest
provenance timestamps are not mistaken for changed benchmark methodology.

```sh
node scripts/benchmark.mjs --output target/benchmarks/candidate.json \
  --baseline target/benchmarks/baseline.json --max-regression 0.20 --metric p95
```

The threshold is explicit: `0.20` permits at most 20% increase in the selected
nanoseconds-per-unit metric (`p50`, `p95`, `p99`, or `mean`) for every scenario. There
is no default absolute or cross-platform budget. Exit codes are `0` for a passing
measurement/comparison, `2` for a complete measurement with performance regression,
and `1` for measurement, input, baseline or configuration failure. A failed run
replaces its output with `measurement-failed`; partial results do not become a
baseline. Invalid CLI options and aliases that would overwrite the baseline are
rejected before any report write. A timed-out worker is terminated and cleanup is explicitly unconfirmed.
The default per-scenario timeout is 60 seconds (`--timeout-ms`).

Baselines must have matching sampling method, harness code, environment, build
profile and scenario units. By default sources must also match. To compare a
reviewed older revision, explicitly pin its `inputs.sourceDigest`:

```sh
node scripts/benchmark.mjs --output target/benchmarks/candidate.json \
  --baseline /path/to/reviewed-baseline.json --max-regression 0.20 \
  --baseline-source <the-baseline-inputs.sourceDigest>
```

This override does not permit a different CPU, Node version, ABI, build profile or
measurement harness. A passing timestamp does not rescue tampered raw samples,
stale build inputs or incomplete results. Report hashes are local integrity links,
not signed publisher attestations. Baselines and comparisons require judgement
about machine load and noise; no statistical-significance claim is made.

Upstream performance comparisons, isolated kernel-only measurements, long-running
soak/leak tests, production workload profiles and accepted platform-specific budgets
remain separate work. Lifecycle correctness guards must not be disabled to improve
benchmark results.

## 2026-10-05 settled-readiness checkpoint

A local Apple M4 / macOS arm64 / Node 22.22.0 run compared the facade before and
after quiescent-pump reuse. Both runs used the same optimized native artifact,
with assertions and overflow checks enabled, the same harness, 128 consumers
with eight committed providers each, three warmup sweeps and 15 measured sweeps.

| Batch-amortized time per readiness read | Before reuse | After reuse |
| --- | ---: | ---: |
| p50 | 710.06 µs | 0.95 µs |
| p95 | 730.71 µs | 1.11 µs |

The [before report](performance/2026-10-05-readiness-before.json) and
[after report](performance/2026-10-05-readiness-after.json) retain raw samples,
source maps, artifact hashes and the explicit baseline comparison. This isolates
quiescent-pump reuse: the earlier native build-profile and phase-filtering changes
are present in both runs. It is not a claim that arbitrary workloads improve by
this ratio, and it establishes no cross-machine performance budget.

Quiescence is reused only after an explicitly empty native drive and stable state
synchronization. Commands that may change the graph, failures, Rust interop, state
observers and nested pumps invalidate it conservatively. Epoch validation,
committed-provider checks and the native transition decision remain authoritative.

```sh
node scripts/benchmark.mjs --scenario facade.settledReadiness \
  --fanout 128 --samples 15 --warmup 3 --timeout-ms 120000
```

## Resident lifecycle history

Two scenarios keep one Harness-profile Context and a fixed set of committed
consumers alive throughout all warmup and measured batches:

- `facade.residentRestart`: restart the same provider identity; consumers restore
  against the old committed value and rebind to the new episode.
- `facade.residentReplace`: dispose the provider, mount a fresh provider and rebind
  the same consumers; node identities grow with completed replacement cycles.

Each batch executes `10 * --scale` cycles. Construction and final graph disposal
remain outside timing; consumer cleanup, publication retirement and reactivation
are included. Assertions check the old committed value during every inverse,
consumer reactivation, and zero live resources after final disposal.

```sh
node scripts/benchmark.mjs \
  --scenario facade.residentRestart --scenario facade.residentReplace \
  --fanout 4 --samples 100 --warmup 0 --timeout-ms 300000 \
  --output target/benchmarks/resident.json
```

This example measures 1,000 cycles in each independent process. Every batch,
including warmup, has a `checkpoints` entry with cumulative cycles, native Driver
storage counters and process memory. Initial and final-cleanup checkpoints are
also retained. The report validator requires the complete sequence, monotonic
stable identity histories and zero live resources at the closed checkpoint.
Inspect the raw ordered samples to see latency changes as history accumulates;
the aggregate p95 alone loses that relationship.

Checkpoint snapshots and memory observations run outside timed batches. Forced GC
still runs only before the initial measurement and after final cleanup, so per-batch
heap movement includes ordinary GC noise. RSS includes V8 and native allocations,
while record counts separate stable history from live resources; neither establishes
an exact bytes-per-record cost. The retained Context intentionally remains reachable
at the final checkpoint. These finite churn measurements do not establish an
unbounded-run memory guarantee, absence of leaks or a production performance budget.

### 2026-10-06 history maintenance checkpoint

The shared Node Driver now invokes the already verified stable binding/declaration
filters after every 256 successful cleanup or removal changes. It does not reclaim
live commitments, reuse node identities, or renumber publication/lease records.
The failed-cleanup regression triggers maintenance through unrelated nodes while
an Unloading consumer still reads its retained provider value.

A local Apple M4 / macOS arm64 / Node 22.22.0 comparison used four consumers,
100 batches of ten cycles, no warmup, and the same benchmark harness, environment
and optimized/assertion-enabled build profile:

| After 1,000 cycles | Same provider restart | Fresh provider replacement |
| --- | ---: | ---: |
| Binding records before maintenance | 4,004 | 4,004 |
| Binding records with maintenance | 112 | 78 |
| Live bindings / leases, both runs | 4 / 4 | 4 / 4 |
| Batch-amortized p95 before | 665.34 microseconds | 777.71 microseconds |
| Batch-amortized p95 with maintenance | 478.82 microseconds | 648.16 microseconds |

The [before](performance/2026-10-06-resident-before.json) and
[after](performance/2026-10-06-resident-after.json) reports retain every ordered
batch, checkpoint and source/build hash. Their source maps differ only in the
shared Driver and its regression test. Both close with zero live resources.
Publication records still reach 1,001 and lease records 4,004; replacement also
retains 1,006 node identities. Those remaining histories are an explicit future
reclamation task. The timing observations are one local comparison, without a
statistical-significance or cross-platform throughput claim; RSS does not measure
the bytes reclaimed by the binding filter.


## Independent native checkpoint replacement

`rust.checkpointReplace` keeps one Harness-profile Context, its NativeDriver and
`--fanout` committed JS consumers alive while alternating v1 and v2 of the real
`native-checkpoint` SDK fixture. Both independent libraries load before the first
measurement. The report binds their distinct SHA-256 hashes to the native build
record and includes the module controller sources in its source map. The measured
reload still verifies the requested artifact through the normal controller path;
this is an end-to-end replacement measurement, not just checkpoint serialization.

```sh
node scripts/benchmark.mjs --scenario rust.checkpointReplace \
  --fanout 4 --samples 100 --warmup 0 --timeout-ms 300000 \
  --output target/benchmarks/native-checkpoint.json
```

This runs 1,000 replacements in one process, in 100 timed batches. Before each
replacement the business value increases by one. Each committed consumer adds one
more during cleanup, exercising the final writes before capture. The new native
instance must retain all of these writes and report the expected schema version;
its Fiber identity changes, while the Driver stays the same and old service handles
reject calls. Timed batches include these per-cycle correctness assertions,
controller snapshots and stale-handle exception checks; the result is not the
latency of the reload API alone. No growing event trace is retained by the fixture.

Each initial, batch and closed checkpoint records process memory, Driver storage,
module image count, native instance/job/stream/object/reverse-call counters and
migration receipt tokens/serialized bytes. The report validator requires exactly
two resident images, one live native instance and one armed migration receipt at
every active checkpoint, with no outstanding native jobs or resources. Final
cleanup must leave all live graph resources, native instance/resource counters and
checkpoint tokens/bytes at zero. The two code images remain mapped by design.
These observations are taken outside the timed batches, as in the resident JS
scenarios. Probe allocations can still affect later GC and memory observations.
The final logical value is the last active snapshot, before terminal
consumer cleanup, so it describes only the measured replacement cycles.

The fixture explicitly migrates one integer; it does not measure large payload
serialization, new-image loading per deployment, concurrent business traffic,
rollback storms or native threads outside the SDK. Increasing stable identity,
publication or lease histories remain visible and must not be interpreted as
live plugin resource leaks. Likewise, zero live resource counters do not imply
constant RSS or prove the absence of all leaks. Reclamation optimizations require
separate before/after evidence and must retain stale-handle invalidation.


### 2026-10-06 checkpoint replacement baseline

Three sequential, independent processes on Apple M4 / macOS arm64 / Node 22.22.0
used four consumers, 100 batches of ten replacements and no warmup. The optimized
native build retained assertions and overflow checks. All three completed 1,000
replacements with the same source digest and exact resource/history counts below.
The final migrated value was 5,000: 1,000 business increments and 4,000 consumer
cleanup increments. Each replacement checked the actual schema transition and
rejected its immediately retired service handle; every batch also rejected a
handle retained from the very first instance.

| Observation | Run 1 | Run 2 | Run 3 |
| --- | ---: | ---: | ---: |
| Batch-amortized p50, ms/replacement | 4.82 | 4.87 | 4.87 |
| Batch-amortized p95, ms/replacement | 5.29 | 5.27 | 5.35 |
| Initial RSS, MiB | 58.23 | 58.08 | 57.88 |
| RSS after final cleanup and GC, MiB | 106.78 | 106.77 | 106.33 |
| JS heap after final cleanup and GC, MiB | 5.96 | 5.95 | 5.96 |

| Counter | Initial | After 1,000 replacements | After final cleanup |
| --- | ---: | ---: | ---: |
| Resident code images | 2 | 2 | 2 |
| Native instances | 1 | 1 | 0 |
| Checkpoint tokens | 1 | 1 | 0 |
| Checkpoint serialized bytes | 209 | 215 | 0 |
| Live graph nodes | 7 | 7 | 0 |
| Live bindings / leases | 5 / 5 | 5 / 5 | 0 / 0 |
| Binding records | 5 | 45 | 45 |
| Node identity slots | 7 | 2,007 | 2,007 |
| Publication records | 3 | 2,003 | 2,003 |
| Lease records | 5 | 5,005 | 5,005 |

Every batch had zero outstanding jobs, streams, objects and reverse calls, including
all retained-failure counters. Migration receipt bytes grow slightly because their
session/node/generation metadata contains larger decimal identifiers; old receipts
do not accumulate. The checkpoint count stays one until final disposal.

The raw [run 1](performance/2026-10-06-native-checkpoint-run1.json),
[run 2](performance/2026-10-06-native-checkpoint-run2.json) and
[run 3](performance/2026-10-06-native-checkpoint-run3.json) reports preserve every
sample, cumulative checkpoint, source hash and both library hashes. This is a
baseline, not a measured speedup or an upstream Cordis comparison. RSS remains
higher after cleanup even though live counters are zero and the JS heap returns
near its initial 5.13 MiB; these observations do not identify the individual
allocator, V8 or native contributions. Stable identity/publication/lease histories
still grow, so subsequent reclamation work must preserve old-handle rejection and
be evaluated against this measured workload. No runtime optimization or reclamation
policy changed in this baseline step.
