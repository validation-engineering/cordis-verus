# cordis-verus

**A Rust plugin runtime with a Verus-verified lifecycle kernel.**

[简体中文](README.zh-CN.md) · [Documentation](docs/README.md) · [Examples](crates/cordis/examples) · [Roadmap](docs/roadmap.md) · [Contributing](CONTRIBUTING.md)

cordis-verus implements [Cordis](https://github.com/cordiverse/cordis) plugin lifecycles and reversible effects in Rust. Plugins declare services and dependencies; the runtime coordinates activation, provider changes, and cleanup. The kernel is executable Rust: the same source is verified by [Verus](https://github.com/verus-lang/verus) and compiled by Cargo.

Use it to build Rust plugin systems, host supported Cordis JavaScript plugins through a native Node adapter, or compose Rust and JavaScript plugins in one lifecycle graph.

**Status:** Experimental, pre-1.0. APIs are evolving, and the crates and npm packages are not yet published. See [verification scope](#verification-scope) for the distinction between kernel proofs, runtime tests, and application compatibility.

## Features

- **Dependency-aware lifecycles.** Track provider identity and retain the services an active consumer needs until its cleanup completes. Failed cleanup remains visible and retains the resources needed for recovery.
- **Typed Rust plugins.** Compose services, asynchronous setup and cleanup, child plugins, events, and timers with explicit resource ownership.
- **Cordis on Node.** Run supported original JS plugins with Rust making lifecycle decisions. JavaScript objects, functions, and service values retain their identity in Node. Cordis and DeepSeek Harness have separate compatibility profiles.
- **Rust and JavaScript together.** Mount user-compiled Rust plugins in the Node graph through explicit service, stream, object, and callback adapters. Typed bindings preserve existing Rust service slots, with opt-in live values and consumer-specific availability checks.
- **Configuration and reload.** Load JSON plugin trees and coordinate official Harness configuration edits through one lifecycle queue. Inspect observed module dependencies before replacing a Worker from a captured artifact, with recovery after failed startup. External executable plugins use a separate JSON-RPC interface.

See [upstream parity](docs/upstream-parity.md) for supported behavior and deliberate differences, and [semantics](docs/semantics.md) for lifecycle contracts.

## Quick start

You need Git, Rustup, Python 3.9+, curl, and a native Rust build toolchain. The installer selects and checks the pinned Rust/Verus toolchain from [toolchain.lock.json](toolchain.lock.json); it does not change your default Rustup toolchain. Installer targets are macOS ARM64/x86_64 and Linux x86_64.

```sh
git clone https://github.com/Stool233/cordis-verus.git
cd cordis-verus
./scripts/install-verus.sh
bash -c 'source scripts/toolchain-env.sh && cargo run --locked -p cordis --example basic'
```

Repository access is currently required to clone. Initial setup downloads the toolchain and dependencies. The example needs no model credentials or external service.

The [basic example](crates/cordis/examples/basic.rs) mounts a consumer before its provider, then shuts them down:

```text
consumer: hello from verified Cordis
consumer cleanup still sees: hello from verified Cordis
provider cleanup follows the consumer
```

The consumer can still use its committed service during cleanup. The provider is released afterwards. The example includes a small executor; the Rust runtime itself does not select an async executor for your application.

### Node compatibility

With the Rust toolchain installed, use Node **22.22.0** and npm:

```sh
npm ci --ignore-scripts
npm run build:native
npm run example:node
```

The [Node example](examples/node/basic.mjs) imports `Context` from `cordis`, loads a service, and disposes its consumers. A preload hook routes that package name to the native adapter. For your own application, select the matching profile:

```sh
# Original Cordis plugins
node --import @cordis-verus/compat-cordis/register app.mjs

# DeepSeek Harness Cordis plugins
node --import @cordis-verus/compat-harness/register app.mjs
```

These commands require the corresponding local runtime packages. Compile TypeScript plugins to JavaScript before loading them. Use one profile per Node environment. Compatibility is validated for specific interfaces and applications; see the [Node guide](docs/node-compatibility.md) for loading rules, known differences, and platform limits.

### DeepSeek Harness

The companion [cordis-harness](https://github.com/Stool233/cordis-harness) project exercises this runtime in an application. It runs the pinned official **Web / standard** and **headless** compositions, preserving the official CLI, Loader, plugins, frontend, and JSONL session storage while replacing the **Node Cordis host**. Browser-side Cordis remains the official JavaScript implementation.

Follow its [build guide](https://github.com/Stool233/cordis-harness/blob/main/docs/build.md) to prepare the verified runtime artifacts. Then, from that repository:

```sh
npm run official:install -- --offline
npm run official
```

Use the install command without `--offline` when public dependencies are not cached. The [application acceptance record](https://github.com/Stool233/cordis-harness/blob/main/docs/official-validation-report.json) covers the default plugin roster, a real tool call, session recovery across processes, and shutdown. Model requests in acceptance tests use a local fixture; interactive use requires your own model configuration.

## Architecture

| Component | Responsibility |
| --- | --- |
| [`cordis-kernel`](crates/cordis-kernel) | Executable Verus specifications, lifecycle transitions, action ownership, and publication contracts |
| [`cordis-driver`](crates/cordis-driver) | Shared lifecycle control used by the Rust and Node hosts |
| [`cordis`](crates/cordis) | Typed services, plugin callbacks, async work, events, timers, and configuration loading |
| [`cordis-node`](crates/cordis-node) and [`packages/`](packages) | Node-API binding, JavaScript facades, compatibility profiles, and Rust plugin adapters |

The kernel governs lifecycle state. Each host manages its own values, callbacks, and resource journals. Read the [architecture guide](docs/architecture.md) for source navigation and trust boundaries.

## Verification scope

Formal guarantees apply to the kernel's specified contracts and their stated assumptions. Arbitrary Rust or JavaScript callbacks, asynchronous host execution, the FFI boundary, and file or network I/O are outside the completed proof scope. Behavior tests and upstream comparisons provide separate evidence for those layers.

The last recorded local development run includes:

| Check | Result |
| --- | ---: |
| Whole-kernel Verus verification, with `--no-cheating --compile` | 2,290 verified obligations; 0 errors |
| Rust workspace behavior tests | 403 passed |
| Rust documentation tests | 2 passed |
| Node behavior tests | 441 passed |
| Extracted crate builds and npm installation checks | Passed on macOS ARM64 / Node 22.22.0 |

The [development report](docs/development-report.json) binds results to source and artifact hashes. These are verification obligations and tests, not a count of proved paper theorems. Other platforms require their own execution evidence.

The semantic reference is [arXiv:2608.25512v1](https://arxiv.org/abs/2608.25512v1). Full host-to-paper refinement and the complete release gate remain open. The [paper ledger](docs/paper-coverage.md) records completed, partial, and refuted claims; the [paper audit](docs/paper-audit.md) explains their scope. A passing development run does not substitute for the release gate's full negative-control suite.

## Development

After installing the toolchain and Node dependencies:

```sh
# Proofs, formatting, lints, docs, tests, examples, and package checks
python3 scripts/record-development.py

# Check that recorded evidence still matches local sources and artifacts
python3 scripts/record-development.py --check
```

Add `--offline` to the first command when dependencies are cached. The second command checks freshness; it does not rerun proofs. Upstream differential tests and the complete release gate are separate checks described in [validation](docs/validation.md) and the [Node guide](docs/node-compatibility.md).

## Documentation and contributing

| Topic | Guide |
| --- | --- |
| Rust services and resource ownership | [Runtime](docs/runtime.md) · [Events](docs/events.md) |
| Configuration and external plugins | [Loader](docs/loader.md) · [Process plugins](docs/process-plugins.md) |
| Original JS plugins and native packages | [Node compatibility](docs/node-compatibility.md) · [Distribution](docs/native-distribution.md) |
| Rust plugins in a Node application | [Factory SDK](docs/rust-node-plugins.md) · [Typed bindings](docs/typed-rust-plugins.md) |
| Proofs, progress, and remaining work | [Refinement](docs/refinement.md) · [Status](docs/status.md) · [Roadmap](docs/roadmap.md) |

The [documentation index](docs/README.md) includes further examples and design notes. Detailed documentation is currently a mix of English and Chinese.

Bug reports, focused fixes, plugin compatibility cases, and proof contributions are welcome in either language. Read [CONTRIBUTING.md](CONTRIBUTING.md) for setup and review expectations, [SECURITY.md](SECURITY.md) for vulnerability reporting, and the [release procedure](docs/releasing.md) for publication requirements.

## License

[MIT](LICENSE). Upstream components retain their licenses and attribution in [NOTICE](NOTICE). cordis-verus is an independent implementation, not an official Cordis or DeepSeek release. The reference paper and extracted text are not distributed with this repository; see [research inputs](reference/README.md).
