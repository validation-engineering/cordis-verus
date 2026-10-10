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
Apple Silicon (ARM64). A manual development run can add macOS Intel with
`include_macos_intel=true`.

The separate **Full release validation** workflow is manually dispatched and uses
the same two default platforms; `include_macos_intel=true` adds Intel to that run.
It first runs one baseline preflight per selected platform, then all 120 complete-crate
negative controls on each platform in a platform-specific partition using strictly
bound shared baseline evidence. The [execution plan](full-negative-validation.md)
keeps preflight and shard deadlines consistent and reserves time for cleanup within
each job. Each selected platform collects its results within `quality.sh`.
Green development CI does not mean full release acceptance. The release workflow
can create a draft runtime prerelease after every selected platform passes the
complete gate; its assets and evidence must match that selection exactly. A default
run neither validates Intel nor produces Intel assets. It does not publish the draft
automatically. Both workflows retain logs and artifacts; full validation also retains
negative reports.

The development/release Node suites and `npm run test:node` use four concurrent
test files, with the same 30-second timeout and complete test set. This bounds
competition between independent native-library fixtures on machines with many
logical CPUs; it does not skip tests or increase their timeout.
Native checkpoint and child tests use separate Cordis/Harness profile entrypoints
with shared test bodies. Each profile has its own file deadline; all original
cases, assertions and individual timeouts remain in the suite.

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
without weakening the acceptance criteria. See [complete negative execution and
collection](full-negative-validation.md) ([简体中文](full-negative-validation.zh-CN.md))
for process cleanup, CPU budgets and the unchanged whole-crate acceptance rule.

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
