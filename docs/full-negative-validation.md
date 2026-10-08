# Complete negative validation

English · [简体中文](full-negative-validation.zh-CN.md)

Release validation deliberately changes executable kernel code and requires the
proofs to reject each change. Every one of the 114 canonical mutations must first
compile and then produce a concrete contract failure while verifying the entire
crate. The unchanged kernel must also pass. A timeout, resource limit, frontend
error or partial result does not satisfy this requirement.

## Execution and cleanup

The runner defaults to one worker and a total budget of at most two available
CPUs. It respects process affinity and Linux cgroup quotas. The unchanged baseline
uses the same thread count as a mutation worker; it no longer silently starts nine
threads. Explicit settings are recorded with the actual effective budget:

```sh
CORDIS_NEGATIVE_JOBS=1 CORDIS_NEGATIVE_THREADS=2 CORDIS_NEGATIVE_TIMEOUT=1200 \
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

Termination is requested once per process group so repeated cancellation cannot
reenter a child's cleanup handler. The grace period and final group kill remain.
CI steps use `exec` to deliver runner cancellation directly to the Python supervisor.
A forced kill can still leave incomplete stage files; collection rejects them.

## Parallel CI without reducing proof scope

The release workflow runs twelve independent shards per platform. Each shard has
nine or ten mutations, one unchanged whole-crate baseline, one worker and two Verus
threads. It compiles and verifies each assigned **entire mutated crate**. This is
different from the experimental function-scoped checker.

`scripts/negative-shards.py collect` accepts only the exact complete partition and
rechecks original stdout, stderr and invocation metadata. It binds the evidence to
the complete source input hashes, canonical mutation contents, verifier/solver/proof
library bytes, platform, and GitHub run and attempt. Scoped flags, changed mutant
sources, missing/duplicate controls, mismatched summaries, cancellation and resource
errors fail collection. The final mutation list retains canonical order.

Each platform's quality job collects its twelve shards within the ordinary gate,
alongside the positive proof, tests, examples, package builds and installation checks. Only the
complete collected report can enter `verification/v3`; one green shard cannot.
Runtime draft creation still requires all three platforms to pass.

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

See [validation gates](validation.md), the [release procedure](releasing.md), and
the [runner](../scripts/check-negative.py) / [collector](../scripts/negative-shards.py)
regressions in `scripts/tests/`.
