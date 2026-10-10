# Complete negative validation

English · [简体中文](full-negative-validation.zh-CN.md)

Release validation deliberately changes kernel operations, guards or specifications
and requires the proofs to reject each change. Every one of the 121 canonical mutations must first
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
stop its Verus and solver descendants; by default, failed workers stop further
dispatch and cancel active siblings. Standard output, diagnostics and `.meta.json` stage records
are retained, including elapsed time, command, exit status, source fingerprint and
cancellation state. The queue contains only the active worker budget, rather than
all 121 already-submitted tasks.

Termination is requested once per process group. The supervisor observes leader
exit without reaping it until group cleanup finishes, so the process-group identity
remains reserved. The supervisor uses `waitid(WNOWAIT)` where Python exposes it, with
`kqueue(NOTE_EXIT)` as the macOS fallback. The actual method is recorded per stage.
Stage records retain process-group snapshots, signals and any cleanup error. A
cleanup failure cannot turn a timeout or cancellation into accepted proof evidence.
CI steps use `exec` so cancellation reaches the supervisor. A forced kill can still
leave incomplete stage files; collection rejects them.

## Continue collecting after failures

Use `--keep-going` to diagnose all mutations in a run or shard, even when an
individual mutation fails the negative acceptance checks. For example, a resource
limit, a timeout whose processes were successfully cleaned up, or a mutant that
unexpectedly verifies remains a failure, but no longer hides later controls.
The unchanged baseline must still pass first. Cancellation, cleanup failures and
infrastructure errors still stop execution; this mode does not promise complete
results after an interrupted run.

In GitHub Actions, choose **Full release validation → Run workflow** and enable
`diagnostic_keep_going`. Leave `create_draft` disabled. The equivalent CLI request is:

```sh
gh workflow run release-validation.yml \
  --repo validation-engineering/cordis-verus --ref main \
  -f diagnostic_keep_going=true -f create_draft=false \
  -f include_macos_intel=false
```

This is opt-in; ordinary release runs retain the default stop-on-failure behavior
inside each shard. Diagnostic runs keep the same full-crate checks, resource limits
and process cleanup. They retain raw artifacts even on failure and do not use
`continue-on-error`. A shard still exits unsuccessfully if any control fails.
Before artifact upload, both preflight and shard jobs print a compact JSON summary
and append the same reported results to the Actions job summary. This includes the
source commit, run/attempt, baseline result, per-control outcomes and diagnostic
coverage. A failed upload therefore need not hide which controls ran. Missing,
interrupted or malformed reports remain explicitly incomplete. This display does
not reconstruct missing raw evidence and is never accepted by the release collector.
Verification and upload failures retain their original job status.

The quality and draft-release jobs are skipped for diagnostic runs, even if every
control passes. Requesting both diagnostic mode and a draft release is rejected in
the planning job before verification starts.

For a local diagnostic run of all controls:

```sh
python3 scripts/check-negative.py --keep-going --jobs 1 --threads 2 --timeout 2400
```

For one local shard, use a new output directory and repeat with other indices as
needed (a single shard covers only its assigned controls):

```sh
python3 scripts/negative-shards.py run \
  --shard-index 0 --shard-count 18 --output target/negative-diagnostics/shard-0 \
  --jobs 1 --threads 2 --timeout 2400 --compile-timeout 300 --keep-going
```

`diagnostic.json` records outcomes in canonical order, with an error type and message
for each failed control. Its counts distinguish selected, attempted, passed, failed
and unexecuted controls. `complete: true` means all selected controls were attempted;
it can coexist with failures. The report is written to `target/proof-negative/` for the monolithic runner
and the chosen output directory for a shard, alongside the raw stdout, stderr and
stage metadata. A completed diagnostic shard has `shard.json` status
`diagnostic-passed` if all its controls pass, or `failed` otherwise, and always
`releaseAcceptance: false`. Check the report for unexecuted controls before
calling collection complete.

Diagnostic evidence cannot enter release validation: the collector explicitly
rejects it, including an all-passing diagnostic run. After fixing the reported
problems, run the ordinary full gate again on one final source snapshot, with
`diagnostic_keep_going=false` (or without `--keep-going` locally). Complete diagnostic
coverage helps plan the fixes; release acceptance still requires fresh ordinary
validation of every selected platform.

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
| macOS ARM64 | 60 min | 25 | 5 | 325 min | 35 min |
| macOS Intel (opt-in) | 90 min | 41 | 3 | 285 min | 75 min |

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
or one green shard cannot. Every selected platform must pass all 121 full-crate
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

Baseline and mutant invocations both use `--multiple-errors 0`. In the
[pinned Verus implementation](https://github.com/verus-lang/verus/blob/168759867f8c4ba0be848f5a3e438c75cee3e6e3/source/rust_verify/src/verifier.rs#L806),
this stops additional diagnostic queries after the first `Invalid` result for a
`CheckValid`; it does not skip its initial query, other functions, or any primary
obligation in a successful baseline. The default additional-error search can itself
exhaust resources after a concrete contract failure. This setting controls that
search, without selecting fewer proofs or raising resource limits. A primary
query returning resource `unknown` remains a failure, and any reported resource
error still invalidates the negative result. Invocation metadata and the collector
require the same fixed setting for the baseline and every mutant.

The pinned verifier also prints “not all errors may have been reported” for
successful queries when the additional diagnostic budget is zero. This note alone
does not indicate a skipped proof; acceptance still depends on the verification
summary and the complete error log.

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

Token exclusion, provision-inverse restriction and the single-step loading target
are exposed through the proved `removal_excludes_retained_token`,
`provision_receipt_action` and `loading_step_target` lemmas. Transport, recovery and
interval proofs use those contracts without repeating broad quantified searches.
The observational journal invariant composes a checked single-entry proof,
`provided_journal_entry`, rather than repeating the lifecycle reasoning inside its
quantifier. Owner-deletion recovery hides child undo when existing projection
contracts supply the required facts. `invocation_record_metadata` and
`retained_invocation_prior_landing` separate receipt metadata from the history
argument used to locate its original landing. The helpers are checked as part of
the same whole crate; they add no assumptions.
A mutated guard or projection must still produce a concrete contract failure, and
any resource failure still invalidates the complete negative result.

See [validation gates](validation.md), the [release procedure](releasing.md), and
the [runner](../scripts/check-negative.py) / [collector](../scripts/negative-shards.py)
regressions in `scripts/tests/`.

Constructor equations and per-entry facts are checked separately before larger
composition proofs consume them. `swap_construction` fixes the transported suffix,
`last_mapped_token` fixes the compressed journal position, and
`landing_catalogue_equation` fixes the captured owner. Ordering, insertion,
retention and Fresh landing proofs similarly separate their local facts from the
quantified execution argument. `FreshDriver::step` consumes
`instruction_receipt_metadata` for receipt identity and the actor control frame.
The old-unload example consumes `related_table_entry` for table-domain and value
relations. These facts are established in small proofs before the wrapper combines
them. The existing public preconditions and
postconditions remain unchanged. A mutation can therefore fail in a smaller
helper instead of exhausting a downstream composition query. Every helper must
still pass the unchanged whole-crate baseline; its conclusion is never added as
an unproved assumption. Selected-proof probes are debugging tools only, and the
full-crate negative acceptance criteria remain unchanged.

`program_trace::allocation_monotone` hides the event relation `ack` and consumes
`acknowledgement_frame`'s proved contract during sequence induction. Allocation
monotonicity no longer expands every event's registration and history conditions.
The historical-name mutation must still fail the original non-reuse contract.
`Kernel::compact_bindings` separates the retained-position extension and final
graph/binding preservation into private proved helpers. The loop consumes their
contracts; the executable filter and its public postconditions remain unchanged.
An inverted live-record condition must fail a checked premise, and any additional
resource error still rejects the whole negative result.

`mixed_grammar::restore_retires` consumes a separately checked single-child inverse
contract while keeping `undo` opaque during journal induction. The orchestration
swap frame composes the existing swap and suffix contracts without reopening the
transition, transport or crossing-guard definitions. The concrete shared recovery
example separates forward target facts from the general deletion theorem and
uses its proved projection equality to obtain the terminal value. Existing public
requirements and guarantees are preserved. The example trace additionally exposes
its actual owner and foreign journal tokens and provider ownership, and the forward
example checks the surviving call against its committed provider. Fresh
terminal recovery keeps the episode replay predicates opaque when composing
the checked episode and terminal contracts. No executable transition,
mutation definition or solver resource limit is changed.

Child-inverse transport checks its concrete retirement-state equation in
`child_inverse_state` before composing the existing contracts. The active-child
example uses `restore_retires` directly; the underlying child inverse remains
responsible for the retirement bit in the same whole-crate verification.
