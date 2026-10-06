# Comparing cordis-verus with Cordis

cordis-verus adds an executable Verus lifecycle kernel and explicit recovery
contracts to a Rust plugin runtime. Its Node adapters aim to run supported
original Cordis plugins. The tradeoff is a native build and integration boundary,
plus some deliberate differences in lifecycle behavior.

This comparison concerns the revisions in [upstream.lock.json](../upstream.lock.json):
Cordis `f8ea3cd50f1a5724e8e715995bcde131c9c12b2c` (`4.0.0-rc.10`) and
DeepSeek Harness `da00f7f5358f2949383b35c14f548bc20187d80c` (vendored Cordis
`4.0.4`). It does not describe every upstream release or every npm plugin.

## Capabilities and costs

| Area | Upstream Cordis / Harness | cordis-verus |
| --- | --- | --- |
| Plugin language | Original JavaScript/TypeScript ecosystem | Typed Rust plugins and supported original JS plugins through separate Cordis/Harness profiles; compile TS before loading |
| Lifecycle implementation | JavaScript/TypeScript runtime | Executable Rust kernel verified by Verus; ordinary Rust and JS hosts manage values, callbacks and scheduling |
| Cleanup dependencies | Behavior depends on the selected upstream implementation and plugin interactions | Committed provider identities survive consumer cleanup; provider teardown waits for those consumers under the kernel contract |
| Cleanup failure | Pinned Cordis tests expect disposal to fulfill after an inverse throws | Reject disposal, retain the failed inverse and provider resources, and expose explicit retry |
| Configuration and HMR | Official configuration and module APIs | Supported official configuration transactions and in-place JS HMR; Worker/process replacement and independent Rust `cdylib` instance replacement have explicit recovery contracts |
| Native code updates | No equivalent Rust plugin ABI in this comparison | Rebuild a compatible dynamic library, then replace its instance in-process; logical state transfer requires an opt-in checkpoint contract |
| Installation | JS dependencies and supported upstream tooling | Adds a platform-specific native addon, pinned Rust/Verus build inputs and artifact validation |
| Assurance | Upstream behavior and tests serve as compatibility evidence | Kernel contracts, counterexamples, host regressions and application acceptance are reported separately |

See [feature parity](upstream-parity.md) for the detailed Rust API mapping and
[Node compatibility](node-compatibility.md) for profile limits. A Rust `cdylib`
replacement does not rewrite running machine code or make arbitrary old function
pointers safe. Code remains loaded under the module lifetime/budget rules in the
[native module guide](native-rust-modules.md).

## A concrete lifecycle problem

A service owns a file stream. Its consumer waits during cleanup, then writes a
final record through that service. Closing the service before the consumer's
write loses that final record.

The [lifecycle case](cases/lifecycle-cleanup.md) uses the same fixture across four
real entries. It records behavior, exact source hashes and raw traces for two
pinned upstreams and the corresponding native profiles. The native contract
retains the committed provider until the consumer has completed cleanup.
A demonstrated fixed-version defect is distinct from an upstream maintainer's
confirmation, and neither is a claim about the current upstream head.

The cleanup-failure companion case makes a different point: preserving failed
cleanup and surfacing its error is a specification choice. Applications depending
on upstream's error-swallowing behavior must account for rejection and retry.
We do not call this JavaScript behavior Rust-style undefined behavior.

## Compatibility is measured without hiding differences

The [archived comparisons](evidence/README.md) include the unchanged upstream core
suite, strict profile traces, the smaller API fixture and real Harness service
scenarios. The full upstream core comparison retains native failures; matching
selected fixtures does not erase differences in that broader suite.

The current run passes **87/87 upstream tests** and **83/87 native tests**.
The `inertia lock 2` scenario and disposal after an inverse throws differ under
our committed-publication and cleanup-failure contracts. Two additional failures
are reproducible compatibility gaps: serialized provider/consumer updates cause
an extra activation with the old consumer configuration, and cleanup-time resource
registration is rejected with error text different from upstream. These are not
claimed safety improvements;
the [archive notes](evidence/README.md) record their investigation.
An expected failure is still a conformance failure.

The companion [Harness acceptance](https://github.com/validation-engineering/cordis-harness/blob/main/docs/official-validation-report.json)
adds official Web/standard and headless execution with original plugins, UI,
tools and session storage. Its scripted local model provider keeps acceptance
reproducible. It does not establish equivalence for every model, plugin or external
service, and browser-side Cordis is not replaced.

## Performance evidence and maintenance tradeoffs

There is no general speed advantage established over upstream Cordis.
The [2026-10-05 application measurements](https://github.com/validation-engineering/cordis-harness/blob/main/docs/performance.md)
recorded median full Web acceptance lifecycles of **1,857 ms upstream** and
**2,589 ms native** with the same JS extension workload on Apple M4 / macOS ARM64 /
Node 22.22.0. Native was about **39% slower** in that specific three-run observation.
The workflow includes tools, persistence, shutdown and a fixed cancellation wait;
it is neither isolated startup time nor throughput. These are historical results,
not a new benchmark of the current commit.

Our [2026-10-06 lease reclamation measurements](benchmarks.md) address a different
maintenance problem in our own implementation. After 1,000 native checkpoint
replacements, stored lease records fell from **5,005 to 5 while running, then 0
after close**; live leases had been 5 in both implementations. Three paired
batch-amortized p95 changes were +0.42%, −0.18% and −3.19%. This demonstrates
removal of released-record accumulation, not universal acceleration or constant
RSS. Lookup and stable deletion cost O(active leases); vector capacity may retain
its live high-water mark, and node/publication history remains a separate concern.

For maintainers, explicit contracts and source-bound records make certain changes
reviewable: a cleanup guard can be followed from the paper into executable code;
a weakened contract can be challenged by a proof or a specific regression.
The [paper review guide](paper-review-guide.md) provides those paths. This also
creates obligations: maintain Verus proofs, host tests, profiles, native packaging
and evidence freshness. We have not measured developer-hours saved.

## Choosing this project

Evaluate cordis-verus when you need Rust-native plugin composition, explicit
cleanup recovery, mixed JS/Rust lifecycles, or an inspectable example of formal
methods connected to running software. If your requirement is exact behavior for
all existing Cordis plugins, the known differences and native integration work
need evaluation first. See the [evidence guide](evidence-guide.md) for reproducible
entry points and the remaining publication work.
