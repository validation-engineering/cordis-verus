# Validation and evidence

All verification uses committed toolchain locks. Behavior tests, Verus proofs,
mutation checks and paper coverage answer different questions.

| Gate | Command | Establishes |
| --- | --- | --- |
| Development | `./scripts/check-development.sh` | Ledger/Python checks, fmt/Clippy/rustdoc, full positive kernel proof and compilation, tests, examples, isolated package tests/builds |
| Development record | `python3 scripts/record-development.py --offline` | Fresh development checks and source hashes |
| Full release | `./scripts/quality.sh` | Development checks plus all canonical full-crate negative controls |
| Release record | `python3 scripts/record-verification.py --offline` | Fresh full gate and verification/v3 evidence |
| Whole paper | `python3 scripts/check-paper-coverage.py --require-complete` | Whole-paper ledger conditions; currently fails because obligations remain open and original claims are refuted |

Default push/PR CI runs **development** checks on Linux x86_64 and macOS
ARM64/Intel. The separate **Full release validation** workflow is manually
dispatched and runs `quality.sh` on the same matrix. Green development CI does
not mean full release acceptance. No workflow publishes packages.
Both retain logs and artifacts; full validation also retains negative reports.

## Reproduce locally

Install Rustup, Python 3.9+, Git and curl:

```sh
./scripts/install-verus.sh
python3 scripts/record-development.py
# After dependencies are cached:
python3 scripts/record-development.py --offline
python3 scripts/record-development.py --check
```

The recorder serializes local proof work with a Unix advisory lock and two
Verus threads. A hash-only `--check` confirms freshness, not new verification.
Failed runs invalidate the relevant record. Changed sources prevent a passed
record. Raw logs and package artifacts are generated under ignored `target/`.

For release verification:

```sh
python3 scripts/record-verification.py --offline
# Add --upstream only when immutable research inputs are available.
```

Full negative runs can take hours. Each mutation must compile, then produce a
concrete contract rejection during whole-crate verification. Timeouts, solver
resource limits, frontend errors and crashes fail the gate. The full release
gate has not passed for this checkpoint; [status](status.md) records this
without weakening the acceptance criteria.

## Experimental scoped-negative calibration

`scripts/check-negative-scoped.py` is a separate opt-in experiment.
`scripts/negative-controls.scoped.candidate.json` is a **candidate mapping**,
not a passed report. Its `scoped-negative-report/v2` schema is not accepted by
the existing release recorder.

Calibration requires a fresh whole positive, then for every canonical mutation:
a positive proof at the selected function, a complete mutant compilation, and
a rejected proof at the reviewed function/anchor. Source, tool and harness
hashes bind the result. All canonical controls must appear in order.
Unexpected diagnostics, empty selections and resource/frontend failures reject
the evidence.

```sh
python3 scripts/check-negative-scoped.py \
  --negative-mode scoped-negative --action calibrate \
  --project-root "$PWD" \
  --manifest scripts/negative-controls.scoped.candidate.json \
  --report-dir /tmp/cordis-scoped-calibration-new \
  --threads 2 --timeout 1200
```

Use a new directory outside the project. A successful calibration establishes
detection by the designated proofs, not full verification of every mutated
crate. Accepting this different evidence for release needs an explicit reviewed
schema/policy change and completed calibration. Neither is claimed here.
