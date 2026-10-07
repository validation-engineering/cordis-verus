# Comparing cordis-verus with Cordis

English · [简体中文](comparison.zh-CN.md)

cordis-verus connects formal methods to executable lifecycle code while aligning
with Cordis functionality. The same Rust kernel is verified by Verus and compiled
into the runtime. Original plugin interfaces, upstream tests and official Harness
workflows provide concrete targets for functional alignment.

The comparison below focuses on the lifecycle contracts you can inspect and the
plugin capabilities you can use. Supported behavior and known differences are
reported alongside their evidence.

This comparison concerns the revisions in [upstream.lock.json](../upstream.lock.json):
Cordis `f8ea3cd50f1a5724e8e715995bcde131c9c12b2c` (`4.0.0-rc.10`) and
DeepSeek Harness `da00f7f5358f2949383b35c14f548bc20187d80c` (vendored Cordis
`4.0.4`). It does not describe every upstream release or every npm plugin.

## From paper constraints to executable code

The [paper review guide](paper-review-guide.md) follows five paper clauses through
their assumptions, Verus contracts, executable call paths and named regressions.
This makes it possible to inspect which constraint governs a lifecycle decision
and where the ordinary Rust or JavaScript host takes over. The kernel's specified
contracts are proved; arbitrary plugin callbacks and external I/O remain outside
that proof boundary. The [paper ledger](paper-coverage.md) records the remaining
refinement work.

For maintainers, these paths give a concrete starting point for reviewing a change
to provider identity, cleanup or recovery. Proof checks, host regressions and
application acceptance check different parts of that change. Keeping those
connections current is part of maintaining the implementation.

## Functional alignment

| Area | Upstream Cordis / Harness | cordis-verus |
| --- | --- | --- |
| Plugin language | Original JavaScript/TypeScript ecosystem | Typed Rust plugins and supported original JS plugins through separate Cordis/Harness profiles; compile TS before loading |
| Lifecycle implementation | JavaScript/TypeScript runtime | Executable Rust kernel verified by Verus; ordinary Rust and JS hosts manage values, callbacks and scheduling |
| Cleanup dependencies | Behavior depends on the selected upstream implementation and plugin interactions | Committed provider identities survive consumer cleanup; provider teardown waits for those consumers under the kernel contract |
| Cleanup failure | Pinned Cordis tests expect disposal to fulfill after an inverse throws | Reject disposal, retain the failed inverse and provider resources, and expose explicit retry |
| Configuration and HMR | Official configuration and module APIs | Supported official configuration transactions and in-place JS HMR; Worker/process replacement and independent Rust `cdylib` instance replacement have explicit recovery contracts |
| Native code updates | No equivalent Rust plugin ABI in this comparison | Rebuild a compatible dynamic library, then replace its instance in the Node host; logical state transfer requires an opt-in checkpoint contract |
| Installation | JS dependencies and supported upstream tooling | Rust applications use Cargo with pinned Rust/Verus build inputs; optional Node compatibility adds a platform-specific native addon and artifact validation |
| Assurance | Upstream behavior and tests serve as compatibility evidence | Kernel contracts, counterexamples, host regressions and application acceptance are reported separately |

Node and npm are optional for Rust applications; see the [architecture overview](../README.md#architecture) for runtime and development requirements.

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

The [2026-10-08 comparisons](evidence/2026-10-08-a03/README.md) include the unchanged
upstream core suite, strict profile traces, the smaller API fixture and real
Harness service scenarios. The current full core run records **87/87 upstream
tests** and **85/87 native tests**. The other three comparisons pass; their
selected scenarios do not erase the two core failures.

The [2026-10-06 baseline](evidence/README.md) remains archived at 87/87 upstream
and 83/87 native, including all four original failures. The two accidental gaps
now pass: scoped coordination avoids an extra activation with the old consumer
configuration, and cleanup-time registration errors include the expected text.
Coordination covers same-stack direct provider/committed-consumer updates in the
Cordis profile under the [documented conditions](node-compatibility.md#同栈-providerconsumer-更新);
other cases retain FIFO scheduling. Resource registration remains forbidden
during cleanup, with structured failure codes and stale-episode checks preserved.

The remaining `inertia lock 2` scenario and disposal after an inverse throws differ
under our committed-publication and cleanup-failure contracts. Both assertions
remain in the suite, and the full comparison still exits with failure. An expected
failure is still a conformance failure. These fixes do not prove the JS coordinator
or establish compatibility for every application.

The companion [Harness acceptance](https://github.com/validation-engineering/cordis-harness/blob/main/docs/official-validation-report.json)
adds official Web/standard and headless execution with original plugins, UI,
tools and session storage. Its scripted local model provider keeps acceptance
reproducible. It does not establish equivalence for every model, plugin or external
service, and browser-side Cordis is not replaced.

## Choosing this project

Evaluate cordis-verus when you need Rust-native plugin composition, explicit
cleanup recovery, mixed JS/Rust lifecycles, or an inspectable example of formal
methods connected to running software. If your requirement is exact behavior for
all existing Cordis plugins, the known differences and native integration work
need evaluation first. See the [evidence guide](evidence-guide.md) for reproducible
entry points and the remaining publication work.

## Further measurements

Performance optimization remains ongoing. Historical [application measurements](https://github.com/validation-engineering/cordis-harness/blob/main/docs/performance.md)
and [runtime benchmarks](benchmarks.md) retain their methods, samples and scope
for engineering reference.
