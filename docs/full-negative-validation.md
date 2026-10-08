# Complete negative validation

English · [简体中文](full-negative-validation.zh-CN.md)

Release validation deliberately changes kernel operations, guards or specifications
and requires the proofs to reject each change. Every one of the 114 canonical mutations must first
compile and then produce a concrete contract failure while verifying the entire
crate. The unchanged kernel must also pass. A timeout, resource limit, frontend
error or partial result does not satisfy this requirement.

## Execution and cleanup

The runner defaults to one worker and a total budget of at most two available
CPUs. It respects process affinity and Linux cgroup quotas. The unchanged baseline
uses the same thread count as a mutation worker; it no longer silently starts nine
threads. Explicit settings are recorded with the actual effective budget:

```sh
CORDIS_NEGATIVE_JOBS=1 CORDIS_NEGATIVE_THREADS=2 CORDIS_NEGATIVE_TIMEOUT=2400 \
  python3 scripts/record-verification.py --offline
```

`CORDIS_NEGATIVE_CPU_BUDGET` can raise the default budget within the detected CPU
limit. More concurrency is not automatically faster: each Verus thread can own an
SMT solver. Timeout changes affect wall time, not solver resource limits or proof
contracts. Ordinary local release validation still executes all controls afresh.

Each verifier invocation owns a process group. Timeout, cancellation and termination
stop its Verus and solver descendants; failed workers stop further dispatch and
cancel active siblings. Standard output, diagnostics and `.meta.json` stage records
are retained, including elapsed time, command, exit status, source fingerprint and
cancellation state. The queue contains only the active worker budget, rather than
all 114 already-submitted tasks.

Termination is requested once per process group. The supervisor observes leader
exit without reaping it until group cleanup finishes, so the process-group identity
remains reserved. The supervisor uses `waitid(WNOWAIT)` where Python exposes it, with
`kqueue(NOTE_EXIT)` as the macOS fallback. The actual method is recorded per stage.
Stage records retain process-group snapshots, signals and any cleanup error. A
cleanup failure cannot turn a timeout or cancellation into accepted proof evidence.
CI steps use `exec` so cancellation reaches the supervisor. A forced kill can still
leave incomplete stage files; collection rejects them.

## Parallel CI without reducing proof scope

The release workflow defaults to Linux x64 and macOS Apple Silicon (ARM64).
Set `include_macos_intel=true` when dispatching it to include macOS Intel. It first
verifies the unchanged whole crate once on each selected platform. Preflight retains
`--trace --time` diagnostics and must pass on all selected platforms before any
negative shards start. This prevents one failing baseline from being repeated across
the entire matrix.

Each mutation still compiles and verifies the **entire mutated crate**, with one
worker, two Verus threads and a 300-second compilation deadline. A single platform
plan supplies both the preflight and shard proof deadlines:

| Platform | Proof deadline | Shards | Maximum controls per shard | Compile + proof budget | Job headroom |
| --- | ---: | ---: | ---: | ---: | ---: |
| Linux x64 | 40 min | 18 | 7 | 315 min | 45 min |
| macOS ARM64 | 60 min | 24 | 5 | 325 min | 35 min |
| macOS Intel (opt-in) | 90 min | 38 | 3 | 285 min | 75 min |

The planner checks complete mutation coverage and reserves at least 30 minutes
within each six-hour shard job for installation, evidence checks,
cleanup and upload. Preflight jobs reserve another 15 minutes beyond the proof
deadline. The workflow permits at most twelve concurrent negative jobs. These
limits are execution budgets, not measured proof durations; they do not raise
solver resource limits or change proof contracts.

Shards reuse the platform's successful preflight baseline from the **same workflow
run and attempt**. The raw baseline output, metadata and hashes travel with the
shard evidence. This is not a cache across commits or workflow runs. Standalone
local shards execute a fresh baseline; shared preflight reuse requires the complete
CI run and attempt identity.

`scripts/negative-shards.py collect` accepts only the exact complete partition and
rechecks original stdout, stderr and invocation metadata, including the shared
baseline. It binds evidence to complete source input hashes, canonical mutations,
verifier/solver/proof-library bytes, platform, thread settings, and GitHub run and
attempt. Scoped flags, changed sources, missing/duplicate controls, altered
summaries, cancellation, cleanup failures and resource errors fail collection.
The final mutation list retains canonical order.

Each platform's quality job collects its complete planned partition within the ordinary gate,
alongside positive proof, tests, examples, package builds and installation checks.
Only the complete collected report can enter `verification/v3`; a green preflight
or one green shard cannot. Every selected platform must pass all 114 full-crate
negative controls and the entire quality gate before runtime draft creation.
The draft contains exactly the selected platforms' assets and evidence. Excluding
Intel makes no claim about Intel validation or artifact availability.

Artifacts have platform, attempt and shard identifiers in their names. Rerun the
**whole workflow** after a failure: rerunning only failed jobs would mix attempts
and is intentionally rejected. The collector does not authenticate arbitrary local
JSON; it trusts the checked execution environment and GitHub artifact transport,
then checks internal consistency and exact input binding.

For local distributed execution, run all indices against the same unchanged source
snapshot and platform into new directories, then pass their parent directory with
`record-verification.py --negative-shards <directory>`. A single shard is useful for
diagnosis but is not accepted as a release result. CI records bind their run/attempt
and are not interchangeable with locally generated records.

## Proof stability

`Kernel::release_provision` uses `#[verifier::spinoff_prover]` to give its proof an
independent solver context. This avoids interference from earlier failed queries
in a mutated crate. Its executable body, preconditions, postconditions and resource
limits are unchanged. The complete positive and negative checks remain responsible
for validating this proof organization; an isolated diagnostic check alone is not
release evidence.

The composition proofs `causal_normalization::adjacent_swap`,
`fresh_semantics::configuration_preservation`, and `rewrite_confluence::swap_frame`
hide the body of `primitive_theory` inside their proofs and use the contracts of
proved component lemmas. This avoids unnecessary expansion of a quantified theory.
The concrete insertion example calls its existing operation lemma explicitly before
composition. Public contracts, executable behavior, mutation definitions and solver
resource limits remain unchanged. Targeted negative checks must still find concrete
failures in the complete mutated crate, without resource errors.

The concrete foreign-child examples separate restoration and registry values,
terminal transport, and target execution into proved helper lemmas. Composition
uses their contracts instead of unfolding all states and quantified theories in
one query. The existing public postconditions, executable code and mutation list
remain unchanged. Scoped timing guides this organization; the complete positive
proof and full-crate negative controls still determine acceptance.

The deletion induction obtains each landing guard through the proved
`fragment_landing_guard` lemma. A removed dependency exclusion therefore exposes
a small, explicit contract obligation instead of leaving the solver to search the
entire induction context. The concrete prefix proof reuses its fragment contract
without re-proving a stronger condition. These changes preserve the public
contracts and resource limits; a resource failure still rejects negative evidence.

See [validation gates](validation.md), the [release procedure](releasing.md), and
the [runner](../scripts/check-negative.py) / [collector](../scripts/negative-shards.py)
regressions in `scripts/tests/`.
