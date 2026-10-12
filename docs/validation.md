# Validation and evidence

All verification uses committed toolchain locks. Behavior tests, Verus proofs,
mutation checks and paper coverage answer different questions.

| Gate | Command | Establishes |
| --- | --- | --- |
| Development | `./scripts/check-development.sh` | Ledger/Python checks, fmt/Clippy/rustdoc, full positive kernel proof and compilation, Rust/Node tests, examples, isolated crate and npm package checks |
| Development record | `python3 scripts/record-development.py --offline` | Fresh development checks and source hashes; not release acceptance |
| Release quality | `./scripts/quality.sh` | The same complete proof and runtime checks, executed once, with release recording handled separately |
| Release record | `python3 scripts/record-verification.py --offline` | Fresh release-quality checks and `verification/v4` evidence; full negatives explicitly `not_run` |
| Full negative regression | `python3 scripts/check-negative.py` | The unchanged baseline passes; all 138 compilable mutations produce concrete whole-crate contract rejections |
| Whole paper | `python3 scripts/check-paper-coverage.py --require-complete` | Whole-paper ledger conditions; currently fails because obligations remain open and original claims are refuted |

## Release policy

The project's primary evidence is the connection from paper constraints to
contracts on executable Rust, checked by Verus. Every release still verifies and
compiles the **complete unchanged kernel** with `--no-cheating --compile`.
No proof obligation, contract or solver resource limit is removed by this policy.

Mutation tests ask a different question: whether the selected deliberate changes
are detected by the contracts. They help maintain specifications and review
regressions, but repeatedly verifying 138 modified copies is not an additional
proof of the released program. Full mutation regression is therefore independent
of the normal release path. Run it when reviewing changes to contracts, mutation
selectors, proof tooling or the toolchain, or as a periodic maintainer audit.
It is not automatically scheduled by this change.

Default push/PR CI runs development checks on Linux x86_64 and macOS Apple Silicon.
A manual development run can add Intel with `include_macos_intel=true`.

The manual **Release validation** workflow requires Linux x64, macOS Apple
Silicon / Intel, and Windows x64. Linux runs the complete positive proof and
quality gate. The other hosts run Rust, Node and extracted-package acceptance,
without executing Verus. The collector requires the same commit and source
fingerprints before joining proof and host records. All four platforms install
the exact assembled runtime, run its example, and repeat after offline `npm ci`.
No platform can inherit another host's runtime pass. Negative controls remain
independent of this release gate.

A draft runtime prerelease can be created only after **all selected platforms**
pass, using assets from the same commit and workflow attempt. Source hashes,
toolchain fingerprints, native provenance and package bytes must agree. A clean
source commit is required for packaging. Drafts are never published automatically.
Green development CI or a local quality record alone is not a completed
cross-platform release.

The manual **Full negative regression** workflow defaults to **Linux only**;
`include_macos=true` and `include_macos_intel=true` independently add platforms.
It retains baseline preflight, complete mutation coverage, process cleanup,
current-attempt artifact binding and optional `diagnostic_keep_going`. It has no
release job or publication permission. Its failures remain failures; they do not
block an independent release workflow. See [negative execution and collection](full-negative-validation.md)
([简体中文](full-negative-validation.zh-CN.md)).

## Evidence and reproduction

Install Rustup, Python 3.9+, Git, curl and the documented Node/npm prerequisites:

```sh
./scripts/install-verus.sh
npm ci --ignore-scripts
python3 scripts/record-development.py
# After dependencies are cached:
python3 scripts/record-verification.py --offline
python3 scripts/record-verification.py --check
# Independent, expensive specification regression:
python3 scripts/check-negative.py --jobs 1 --threads 2 --timeout 2400
```

Recorders serialize local proof work with a Unix advisory lock and two Verus
threads. `--check` checks freshness, not new verification. Failed runs invalidate
the relevant record; changed sources prevent success. Generated development and
release reports are excluded from source fingerprints so refreshing one does not
invalidate the other. Both reports still bind their check scripts and source inputs.

`target/positive-proof/` contains raw Verus JSON, stderr and a compiled-artifact
fingerprint. The release recorder checks the fixed whole-crate invocation,
successful statistics, pinned Verus identity, actual compiled artifact and unchanged
source/tool fingerprints. It also validates runtime test sections and fresh native
build/npm installation evidence. `verification/v4` records full negatives as
`{ "status": "not_run", "requiredForRelease": false, ... }`; it never copies an old
negative pass into a new release. The runtime manifest is `runtime-release/v2`.
The packager and installer reject legacy or incomplete evidence rather than
interpreting an old schema under the new policy.

The Node suites use four concurrent test files, a 30-second timeout and the
complete test set. Native checkpoint and child tests have separate Cordis/Harness
profile files with shared test bodies. No cases or assertions are skipped.

## Experimental scoped-negative calibration

`scripts/check-negative-scoped.py` and
`scripts/negative-controls.scoped.candidate.json` remain an opt-in experiment.
The candidate map is not a passed report. Calibration requires a fresh whole
positive proof, then each selected positive proof, complete mutant compilation
and a rejection at the reviewed function/anchor. Unexpected diagnostics, empty
selections and resource/frontend failures reject the evidence.

```sh
python3 scripts/check-negative-scoped.py \
  --negative-mode scoped-negative --action calibrate \
  --project-root "$PWD" \
  --manifest scripts/negative-controls.scoped.candidate.json \
  --report-dir /tmp/cordis-scoped-calibration-new \
  --threads 2 --timeout 1200
```

Use a new directory outside the project. Calibration would establish detection
by the designated proofs, not full verification of every mutated crate. The
independent full regression retains its complete-crate acceptance rule. Neither
kind of mutation evidence establishes paper-wide completion.
