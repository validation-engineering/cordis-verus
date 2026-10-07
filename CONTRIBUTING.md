# Contributing

Chinese and English issues, documentation, and pull requests are welcome. This
is an experimental 0.1 project; open a short design discussion before a large API
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
Full release acceptance additionally requires `./scripts/quality.sh`, including
all full-crate negative mutations. See [validation](docs/validation.md) for the
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

Kernel code is both executable Rust and Verus input. Changes must preserve the
published contracts and be verified with the exact pinned toolchain. Host tests
are not a formal refinement proof. Report new assumptions and limits explicitly.
A Clippy exception should be narrowly scoped and explain the Verus constraint;
do not disable warnings across the host adapter.

Update `CHANGELOG.md` for user-visible behavior, APIs, and corrected proof
claims. Describe compatibility using a concrete observable behavior rather than
claiming complete upstream parity. Update research/toolchain locks only in an
intentional, reviewed change and rerun proofs, negative tests, and packaging.

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

The five workspace Rust crates currently share unreleased version 0.1.0 and are developed together.
During this unpublished development stage, prioritize Cordis behavior and paper
semantics; update callers and documentation directly when an API changes rather
than adding compatibility shims for earlier development snapshots. After publication, patch
releases aim to fix behavior without intentional public API removal. Breaking
API or documented semantic changes require a 0.x minor release with migration
notes. Before 1.0, downstream users should expect changes and pin versions when
reproducibility matters. Only the latest development revision and, once
published, the latest 0.x release receive maintenance; no LTS commitment exists.

The supported Rust compiler is the pinned Rust 1.98.1, also declared as the
minimum package version. Raising it requires a documented toolchain update and
the complete verification gate. The source repository is [validation-engineering/cordis-verus](https://github.com/validation-engineering/cordis-verus),
now public. No runtime release or registry namespace is configured; see `docs/releasing.md` before distribution.

By submitting a contribution, you license it under the project's MIT license.
Preserve upstream attribution and keep the reference paper out of source/crate
distributions. No CLA or transfer of copyright is required.


Independent negative controls can run concurrently with
`CORDIS_NEGATIVE_JOBS=2 python3 scripts/record-verification.py --offline`.
The default remains one worker. Each worker gets an isolated kernel source tree;
the default total Verus thread budget is nine, divided across workers. The
subprocess wall-clock timeout defaults to 600 seconds. Set
`CORDIS_NEGATIVE_TIMEOUT` (or use `check-negative.py --timeout`) when a slower
machine needs more time. This wall-clock allowance does not change SMT resource
limits. Partial timeout output is retained for diagnosis.
These settings are recorded in the evidence. They do not change proof contracts,
solver resource limits, or the acceptance rule: every mutation must compile,
verify the entire crate, and fail a concrete contract. A timeout, frontend error,
partial verification or solver exhaustion alone is always inconclusive.
The quality command also runs the Python evidence-gate regression tests.

Release evidence must include every name in `check-negative.py::mutation_manifest`, in the canonical order. A minimum mutation count is insufficient: missing, duplicated, additional or reordered entries invalidate the record, as do incomplete positive or negative whole-crate statistics. The evidence-gate unit tests cover these cases.

For archive transport, private-fork authentication and original toolchain provenance, see
[toolchain archives](docs/toolchains/README.md).
