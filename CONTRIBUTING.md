# Contributing

Chinese and English issues, documentation, and pull requests are welcome. This
is an experimental project; open a short design discussion before a large API
or semantic change. Small bug fixes can go directly to a pull request.

## Development setup

Install Rustup, Python 3.9 or newer, Git, curl and Node 22.22.0, then run:

```sh
./scripts/install-verus.sh
npm ci --ignore-scripts
./scripts/check-development.sh
```

The script runs formatting, Clippy with warnings denied, rustdoc, executable
whole-kernel Verus proofs, behavior tests, examples, and isolated
crate archive tests/release builds, a source-bound Node addon and self-contained
Node behavior tests. Optional upstream differential tests use `npm run test:compat`;
see [Node compatibility](docs/node-compatibility.md) for the locked-source prerequisite. After dependencies are cached,
`python3 scripts/package-check.py --offline` checks packaging without network.
Release acceptance requires a fresh `./scripts/quality.sh` record plus actual
asset installation on every selected platform. Full negative mutations run
independently through `negative-regression.yml` or `scripts/check-negative.py`. See [validation](docs/validation.md) for the
separate gates and the experimental scoped checker.
The primary CI targets are Linux x86_64 and macOS arm64/x86_64. Other platforms
are currently unvalidated. CI configuration is not evidence of a completed run.

### Toolchain availability

The installer selects the pinned Rust/Verus versions from
[toolchain.lock.json](toolchain.lock.json) without changing the default Rustup
toolchain. Installer targets are macOS ARM64/x86_64 and Linux x86_64.

The pinned rolling-release archive URLs returned HTTP 404 in the
[recorded CI run](https://github.com/validation-engineering/cordis-verus/actions/runs/37490393141).
The project now preserves those exact bytes in public, checksum-locked
[toolchain archives](docs/toolchains/README.md). The installer tries this archive
before the original upstream URL. Fresh source installations need no repository
access grant or GitHub token; cached archives remain usable offline.

## Changes and review

Keep each change focused. Include a minimal failing regression for behavioral
fixes, explain semantic changes, and run the relevant checks before the full
quality gate. Avoid timing-dependent tests: use manual timers or controlled
futures whenever possible. Do not silence a failing proof by changing the
implementation into an unchecked duplicate or adding `assume`, `admit`, or
`external_body`. Consult `AGENTS.md` and `docs/semantics.md`.

R2–R4 refinement work uses implementation batches: develop the connected runtime
code and proofs first, using compilation and targeted Verus checks as needed.
Record deferred regression and negative-control scenarios while interfaces are
changing, then implement the necessary cases and run the complete development
workflow at integration acceptance. A regression remains required before accepting
a behavioral fix, but need not interrupt every intermediate implementation step.
Existing tests and CI gates remain in place. See the
[batch workflow](docs/paper-refinement-roadmap.md#implementation-batches-and-acceptance).

Kernel code is both executable Rust and Verus input. Changes must preserve the
published contracts and be verified with the exact pinned toolchain. Host tests
are not a formal refinement proof. Report new assumptions and limits explicitly.
A Clippy exception should be narrowly scoped and explain the Verus constraint;
do not disable warnings across the host adapter.

Update `CHANGELOG.md` for user-visible behavior, APIs, and corrected proof
claims. Describe compatibility using a concrete observable behavior rather than
claiming complete upstream parity. Update research/toolchain locks only in an
intentional, reviewed change and rerun proofs, negative tests, and packaging.

## Source organization and removals

Follow the [current plan](docs/verification-plan.md) ([中文](docs/verification-plan.zh-CN.md)).
Work continues on `main`; the fixed pre-refactor branch is
`codex/archive-before-refactor-2026-10-24`. Group code by state ownership and
responsibility, keeping executable operations and contracts directly connected.
For a removal, record its purpose, remaining callers/proof references, replacement
or archive location, scope changes and checks. Update source links, selectors, CI
and package inputs together. Historical reports retain their original hashes;
moving files does not refresh proof evidence.

## Evidence and paper reviews

Start with the [evidence guide](docs/evidence-guide.md) and the five
[paper review paths](docs/paper-review-guide.md). A claim should identify its
paper version or runtime revision, premises, executable call path and observable
result. Keep a reproduced defect distinct from an upstream acknowledgment or a
deliberate contract difference. Preserve failed differential results.

When changing a referenced contract or test, update
`docs/paper-review-cases.json` and run `python3 scripts/check-paper-review.py`.
This index check runs in the development workflow; it detects missing references,
not an invalid mathematical correspondence. Record exact commands and outputs for
independent reproductions.

## Version and support policy

The workspace crate versions are declared in `Cargo.toml` and developed together.
Prioritize Cordis behavior and explicit paper contracts; update callers and
documentation together when experimental APIs change. Do not add aliases solely
to preserve an obsolete development layout. Published API removals or semantic
changes need a 0.x minor version and migration notes; patch releases aim to fix
behavior without intentional API removal. Before 1.0, pin versions when
reproducibility matters. Maintenance targets the latest development revision and
the latest released 0.x version; there is no LTS commitment.

The supported Rust compiler is the pinned Rust 1.98.1, also declared as the
minimum package version. Raising it requires a documented toolchain update and
the complete verification gate. The source repository is [validation-engineering/cordis-verus](https://github.com/validation-engineering/cordis-verus),
now public. GitHub Releases distribute precompiled runtime previews; registry
publication remains separate. See `docs/releasing.md` before distribution.

By submitting a contribution, you license it under the project's MIT license.
Preserve upstream attribution and keep the reference paper out of source/crate
distributions. No CLA or transfer of copyright is required.

Full negative regression has its own runner and source-bound evidence; see
[full negative validation](docs/full-negative-validation.md) for concurrency,
timeouts and CI shards. Release recording does not implicitly run that suite.
Preserve its exact mutation manifest and rejection criteria; a timeout, compiler
failure or missing case is not a successful negative result.

For archive transport, private-fork authentication and original toolchain provenance, see
[toolchain archives](docs/toolchains/README.md).
