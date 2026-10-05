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
It rejects stale native source/build evidence and a stale Rust SDK fixture. Reports
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
