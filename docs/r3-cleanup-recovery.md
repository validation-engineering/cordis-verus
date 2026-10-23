# R3: recovery through the production cleanup dispatcher

[简体中文](r3-cleanup-recovery.zh-CN.md) · [Production recovery](r3-production-recovery.md) · [Milestones](paper-refinement-roadmap.md)

The production mixed cleanup dispatcher now connects actual scalar and typed
restoration attempts to the inverse suffix retained by a registered function.
The finite composition derives successful restoration and recovery of Begin
values under explicit conditions on the observed execution. This advances the
production correspondence with Equation (55); **R3 remains in progress**.

## Actual execution and retained evidence

The Rust host calls `Cleanups::pop`, which calls
`Execution::dispatch_payload_cleanup`. The same verified queue implementation
selects the actual action, performs the guarded restoration, acknowledges its
actual result, and returns the completion. Ordinary callbacks and Child cleanup
remain distinct branches.

Each managed completion now carries erased snapshots of the actual queue before
and after dispatch. `Dispatch::authentic` and `finished` are postconditions of
that production entry point. They connect these snapshots to the selected slot,
ticket, actual attempt and acknowledgement. The scalar branch exports the same
complete queue transition as the typed branch.

The value observation comes from the scalar commit or the typed attempt's locked
read. `recorded` decodes it at the actual Journal cut; a typed successful output
uses the restored owner's authenticated history and recorded revision. A retired
typed allocation is absent, rather than being assigned a fabricated value.
The evidence uses `Ghost` data: it adds no runtime history buffer, payload clone,
or additional lock.

## Contracts established by real returns

| Guarantee | Actual source and proof |
| --- | --- |
| Success is exactly the strict inverse domain | `Dispatch::recovery`, `strict_step`: the real observed value equals the selected inverse's captured output |
| Success restores the captured input and consumes only this slot | Actual scalar/typed write, acknowledgement and `finished` queue transition |
| Failure preserves the exact inverse and selected slot | The real returned queue; `progress` preserves the optional remaining recovery result and the local attempted value |
| Retry keeps that inverse and uses a newer attempt | `Execution::retry` exports slot/waiting preservation, same token and increasing attempt; `resumed_inverse` composes two actual completions |
| A completed ticket stays closed | `completed_attempt_stays_closed` uses either branch's authoritative Journal receipt, including after subsequent retries |

The strict domain concerns `(Journal, allocation)`, not a service name. Aliases
therefore refer to the same inverse domain. The observed value includes the
reversible semantic state; equal payload contents alone do not enable a retry.
Failure preserves the state at the actual attempt, not necessarily the value
that existed before an interfering writer ran. The whole issue/read/write/ack
interval is not claimed to be atomic.

## From the retained suffix to a finite cleanup sequence

`managed_cleanup_path` consumes actual emitted dispatch results. Their retained
boundaries supply the before/after queues; callers do not supply replacement
queue snapshots. `values_at` constructs the value trajectory from their real
outputs. `pending` interprets remaining inverses while skipping `None` slots
left by successful cleanup.

`linked` is a sufficient, explicit source condition:

- the results belong to the same attached queue and their Journal prefixes are
  ordered, with strictly increasing attempt identities;
- successive actual slot vectors agree, and each selection is the last occupied
  slot of the invocation's retained suffix;
- each actual read agrees with the value trajectory constructed so far.

`RegisteredReport::cleanup_progress` starts with the already established actual
Begin/return recovery contract. It proves that each finite prefix preserves the
remaining recovery obligation. `cleanup_attempts_succeed` derives success of
each attempted inverse from those source conditions. If the suffix is fully
consumed, `cleanup_recovers_begin` proves its constructed value result equals
the actual Begin values. Neither a desired result heap nor inverse success is
an extra premise.

These conditions exclude a conflicting failed read from this particular continuous
trajectory. The [interleaved recovery proof](r3-interleaved-recovery.md) now
includes actual foreign managed writes, blocked attempts, foreign restoration
and later cleanup in one finite history. It derives exhaustion from matching
actual successful restores and connects the resulting values to a real native
Unload when the endpoint's source conditions hold.

The projection remains limited to the allocations touched by the invocation.
Publication, dynamically created Child effects, pending registrations and general
legal lifecycle deletion still need composition. Scheduler fairness and eventual
retry remain separate obligations.

## Review and validation

- [cleanup_recovery.rs](../crates/cordis-kernel/src/cleanup_recovery.rs): actual
  observations, strict domains, remaining-stack preservation and retry composition.
- [payload_cleanup.rs](../crates/cordis-kernel/src/payload_cleanup.rs) and
  [cleanup_queue/completion.rs](../crates/cordis-kernel/src/cleanup_queue/completion.rs):
  real dispatch, erased boundary retention and propagated postconditions.
- [managed_cleanup_path.rs](../crates/cordis-kernel/src/managed_cleanup_path.rs):
  finite composition from real results back to registered Begin values.
- [execution.rs](../crates/cordis-kernel/src/execution.rs): production retry
  postconditions; [runtime.rs](../crates/cordis/src/runtime.rs): host caller.

Current integrated proof, compilation and regression evidence is recorded in
[interleaved recovery](r3-interleaved-recovery.md#review-and-validation). The
preceding cleanup-only results do not certify subsequent source changes.

New acceptance scenarios to add at integrated acceptance:

- mixed scalar/typed suffixes with aliases, a pre-existing queue prefix and holes
  left by earlier successes;
- actual failure, retained inverse, admitted retry and rejection of the old reply;
- rejected chain assembly for unrelated queue domains, reused attempts, changed
  slot vectors and reads that do not continue the recorded trajectory;
- contract mutations that substitute a boundary snapshot, discard a failed
  inverse, skip a live slot or accept a value outside the strict inverse domain.

The complete development recorder and new negative-control acceptance remain
pending. Earlier verification reports do not certify changed sources; full
negative regression and calibration remain `not_run`. This document does not
promote original paper items 68/69 or mark R3 complete.
