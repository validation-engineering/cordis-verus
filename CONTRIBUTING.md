# Contributing

Chinese and English issues, documentation, and pull requests are welcome. This
is an experimental 0.1 project; open a short design discussion before a large API
or semantic change. Small bug fixes can go directly to a pull request.

Install Rustup, Python 3.9 or newer, Git, and curl, then run:

```sh
./scripts/install-verus.sh
./scripts/check-development.sh
```

The script runs formatting, Clippy with warnings denied, rustdoc, executable
whole-kernel Verus proofs, behavior tests, examples, and isolated
crate archive tests/release builds. After dependencies are cached,
`python3 scripts/package-check.py --offline` checks packaging without network.
Full release acceptance additionally requires `./scripts/quality.sh`, including
all full-crate negative mutations. See [validation](docs/validation.md) for the
separate gates and the experimental scoped checker.
The primary CI targets are Linux x86_64 and macOS arm64/x86_64. Other platforms
are currently unvalidated. CI configuration is not evidence of a completed run.

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

## Version and support policy

The two crates currently share version 0.1.0 and are developed together. Patch
releases aim to fix behavior without intentional public API removal. Breaking
API or documented semantic changes require a 0.x minor release with migration
notes. Before 1.0, downstream users should expect changes and pin versions when
reproducibility matters. Only the latest development revision and, once
published, the latest 0.x release receive maintenance; no LTS commitment exists.

The supported Rust compiler is the pinned Rust 1.98.1, also declared as the
minimum package version. Raising it requires a documented toolchain update and
the complete verification gate. The source repository is [Stool233/cordis-verus](https://github.com/Stool233/cordis-verus),
initially private. No public release or registry namespace is configured; see `docs/releasing.md` before distribution.

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
