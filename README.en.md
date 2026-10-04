# cordis-verus

[简体中文](README.md) · [Documentation](docs/README.md) · [Project status](docs/status.md) · [Contributing](CONTRIBUTING.md)

A Rust implementation of Cordis lifecycle and reversible effects, with executable contracts and proofs in [Verus](https://github.com/verus-lang/verus). The kernel uses the same source for Verus verification and Cargo compilation. A Rust runtime adds typed services, asynchronous plugins, events, timers, and configuration loading.

This is a separate project from the earlier TLA+ study. Its semantic reference is [arXiv:2608.25512v1](https://arxiv.org/abs/2608.25512v1), with pinned official Cordis and DeepSeek Harness snapshots as implementation references. It offers corresponding Rust interfaces; it does not execute TypeScript plugins or implement Harness's model APIs, permission system, or UI.

**This is the first private research/development snapshot: experimental version 0.1.0, not published on crates.io, and not through the complete release quality gate.** Public APIs and proof coverage are still evolving.

## Current progress

| Check | Frozen snapshot result |
| --- | --- |
| Whole-crate positive Verus verification | **2,227 verified / 0 errors**, with `--no-cheating --compile` |
| Rust behavior tests | **259 tests + 2 doctests** passed |
| All 81 numbered paper items | **42 formalized · 17 proved · 18 partial · 4 refuted** |
| Integration obligations | **4 open** |
| Negative controls and release evidence | **114 controls awaiting full calibration**; complete `quality.sh` has not passed |

These counts describe a frozen source snapshot, not a proof of the whole paper. `formalized` means a definition has been encoded; it does not certify every model or host implementation. The experimental scoped-negative checker produces selected-proof evidence only. **It does not replace canonical whole-crate negatives or constitute v3 release evidence.** See [status](docs/status.md) and [validation](docs/validation.md) for the evidence and reproduction procedure.

## Capabilities

- Lifecycle kernel: four-state transitions, actual provider identities, target and committed bindings, separate retirement/removal, and guarded recovery ordering.
- Verified closed programs: real service values, Provision, cross-provider operations, dynamic Child creation, actual LIFO inverse journals, pending admission, and Divert after target drift.
- Rust host: synchronous/asynchronous setup, typed services, realms, child plugins, cancellation and cleanup, events, and owner-scoped timers.
- Configuration and maintenance: JSON trees, Include, hot reload, explicit persistence, diagnostics, and shutdown.

The host is covered by behavior and integration tests. Arbitrary Rust callbacks, Futures, locks, and file I/O do not yet have a complete formal refinement. See [upstream parity](docs/upstream-parity.md) and [semantic boundaries](docs/semantics.md).

## Quick start

Install Git, Rustup, Python 3, and curl. The installer downloads and checks pinned Verus/Rust toolchains for macOS ARM/Intel or Linux x86_64 without changing Rustup's default toolchain. Initial setup needs network access and Cargo dependencies; later runs can use cached inputs.

```bash
git clone https://github.com/Stool233/cordis-verus.git
cd cordis-verus
./scripts/install-verus.sh
source scripts/toolchain-env.sh
cargo test --workspace --locked
cargo run --locked -p cordis --example basic
```

The repository is currently managed as a private project; cloning requires GitHub access. Examples use a std-based executor and require no model credentials or external services.

| Explore | Start here |
| --- | --- |
| Consumer/provider cleanup ordering | [basic.rs](crates/cordis/examples/basic.rs) |
| Async stages, children, and LIFO | [async_lifecycle.rs](crates/cordis/examples/async_lifecycle.rs) |
| Configuration reload and persistence | [config_reload.rs](crates/cordis/examples/config_reload.rs), [config_persistence.rs](crates/cordis/examples/config_persistence.rs) |
| Concrete verified program APIs | [Verified programs](docs/verified-programs.md) |

## Verification and paper scope

```bash
# Daily development: formatting, lints, docs, whole-crate positive proofs,
# tests, examples, and package checks
./scripts/check-development.sh --offline

# Positive kernel verification only
./scripts/verify.sh --num-threads 2 --triggers-mode silent

# Complete workflow: formatting, lints, docs, proofs, tests, examples,
# canonical whole-crate negatives, and package checks
./scripts/quality.sh --offline

# Inventory consistency; --require-complete is a separate gate that currently fails
python3 scripts/check-paper-coverage.py
```

Tools and inputs are pinned in [toolchain.lock.json](toolchain.lock.json), [Cargo.lock](Cargo.lock), and [upstream.lock.json](upstream.lock.json). A negative control must compile and then fail a real contract. Timeouts, exhausted solver resources, and compiler failures do not count. Default CI runs development checks and **excludes the full negative-control suite**. Canonical whole-crate negatives and complete release validation remain separate workflows. A checked-in CI configuration does not imply a successful remote matrix run.

Scoped results include actual nine-rule executions, provider ordering, observational recovery, guarded exchanges and suffix transport, and episode deletion with mixed foreign Table/Child journals and dynamic registry changes. Their contract premises remain essential; these are not general scheduling confluence or complete host proofs. See [architecture](docs/architecture.md), [refinement](docs/refinement.md), and the [paper ledger](docs/paper-coverage.md).

Unit-component witnesses refute the original statements of Lemmas 62, 75, and 77 and the unconditional completion clause of Theorem 71(2). Encoded Child exchange/deletion and literal-input examples still have original Component representation gaps; **they do not unconditionally refute original items 78/79/80**. See the [paper audit](docs/paper-audit.md).

## Contributing and licensing

The [roadmap](docs/roadmap.md) lists implementation and proof work with completion criteria. Follow [CONTRIBUTING.md](CONTRIBUTING.md) for changes, [SECURITY.md](SECURITY.md) for security reports, and the [release procedure](docs/releasing.md) for publishing.

Project Rust code is licensed under [MIT](LICENSE). Upstream code retains its own licenses. The paper and extracted text are outside this project's MIT license and are not distributed with the source; see [research inputs](reference/README.md).
