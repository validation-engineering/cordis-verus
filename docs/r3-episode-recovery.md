# R3: recovery throughout a real episode

[简体中文](r3-episode-recovery.zh-CN.md) · [Milestones](paper-refinement-roadmap.md) · [Source map](paper-refinement-map.md)

The first R3 batch connects Equations (55) and (56) to **every episode cut in
one actual Mixed/Fresh script execution**. Recovery no longer requires the
script's last successful command to be the selected owner's Unload. The real
`run_inspected` entry point carries the same contract. R3 remains in progress;
this batch covers the concrete synchronous Unit/Child/Provision/Xor language,
not the entire managed-production/v1 effect carrier.

## The guarantee

For any successful Begin and a later cut before the same owner's next Unload:

```text
apply the owner's retained inverse word to the current table observation
    =
apply the actual foreign value maps to the observation immediately after Begin
```

This is the concrete table-value specialization of Theorem 68, Equation (55).
The foreign maps include other actors' captured inverse journals when they
Unload, even when those receipts predate the selected episode. Fresh uses the
allocation choice recorded by each actual Child landing.

At a cut that is followed by the owner's actual Unload, its post-state has that
same value observation and the owner's table is empty: Corollary 69, Equation
(56). Later successful commands do not invalidate this historical conclusion.
A subsequent Begin supplies a new snapshot and a separate recovery interval.

For an episode still open in the **returned machine**, the contract additionally
connects the value equation to `restore_receipts` on the actual stored journal
and actual tables. Its result is `Some` and its projection equals the foreign
replay. Definedness comes from the existing history-derived journal theorem;
callers do not assume restoration succeeds. This is a contract about the same
receipt interpreter used by executable Unload, not a new recovery implementation.
It does not permit Unload before the normal lifecycle cleanup guard holds.

A checked error leaves these guarantees on the successfully executed prefix.
A request that was rejected, and commands after it, add no source transitions.

## Paper-to-code review

| Paper constraint | Contract and implementation |
| --- | --- |
| Definition 51: observe registered tables, including Loading values | `projection::project`; `equal_payload` transfers the observation using unique ownership, without equating unrelated execution metadata |
| Lemma 59: an episode stays installed between Begin and Unload | `terminal_episode::{mixed_open_interval,fresh_open_interval}` derives the interval from the actual transition sequence |
| Theorem 68 / (55): recovery at an arbitrary episode cut | `episode_replay::recover_cut` and `fresh_episode_replay::recover_cut`; the real Xor library proves its scalar commutation laws |
| Corollary 69 / (56): recovery on the closing Unload | `recovered_at` connects every closing cut to its actual next source state and empty owner table |
| Real receipts, not a caller-provided recovery model | `MixedDriver::{source_journal,source_restoration,restored_observation_from_source}`; Fresh delegates through its actual inner driver |
| One actual source execution for all queries | `ScriptReport::recovery_history_witness`; `establish_recovery_history` is called by the actual Mixed/Fresh `run_script` establishment path |
| Values, functions and recovery at the public inspection entry point | `run_inspected` propagates `recovery_history` alongside its R1 interpretation certificate |

The implementation is in [episode_replay.rs](../crates/cordis-kernel/src/episode_replay.rs),
[fresh_episode_replay.rs](../crates/cordis-kernel/src/fresh_episode_replay.rs), and
[inspected_run.rs](../crates/cordis-kernel/src/inspected_run.rs). `recovery_source`
extracts the shared source witness. `current_recovery` returns that witness and
the current actual-journal equation. All these histories and queries are ghost
proof data; the batch adds no runtime history buffer or user dependency.

## Why this is not legal lifecycle deletion

The paper itself distinguishes the two readings on page 46 of the locked v1
snapshot: Equation (55) compares table values, with control outside the relation.
Interpreting it as the execution that would have occurred without the owner
requires further conditions, including that an owner-created fiber takes no step.

For example, an owner can publish a service and create a Child. A consumer then
uses that service, while the Child publishes a value of its own. Recovery removes
the owner's service but preserves the Child's value until the Child cleans up.
Without the owner, that Child would not exist and that consumer's Begin might be
illegal. The equal table observation does not construct a legal surviving trace.
In this value algebra a scalar operation on an absent key is identity; the actual
strict interpreter still rejects a missing value.

A separate [conditional deletion certificate](r3-script-deletion.md) now connects
the actual Mixed report to a constructed legal execution for a private table owner,
including foreign Child lifecycles. It uses the same source witness and relates
the target's table projection to this recovery equation. Owner-created Children
and private consumers are outside that certificate. The value theorem itself
does not erase children, rewind the allocator, restore arbitrary external I/O,
prove global termination, or change the original paper ledger's partial/refuted
outcomes. Standalone mutators and bootstrap have not acquired this new
all-episode report contract. Theorem 68 and Corollary 69 remain `partial` for the
original unrestricted target.

## Reproduction

The [runtime cases](../crates/cordis-kernel/tests/episode_replay.rs) use real
`run_script` / `run_inspected` calls. They check:

- a consumer prevents owner cleanup, preserving the actual Child receipt,
  published values and provider inverse;
- two episodes use different provider snapshots and allocate different children;
- both owner Unloads occur inside the same successful history, followed by a
  further successful transition and a rejected command;
- the consumer's operations and inverses cancel, while the Child's values remain
  until its own cleanup.

With the pinned toolchain and cached dependencies:

```sh
source scripts/toolchain-env.sh
cargo test -p cordis-kernel --test episode_replay --locked --offline
python3 scripts/check-r3-episode-controls.py
python3 scripts/record-development.py --offline
```

The two selected **semantic** mutations discard foreign history or substitute
an empty journal for the actual stored receipts in the recovery observation.
They must compile as a whole crate and fail the designated recovery contract.
The existing strict harness rejects timeouts, resource exhaustion, compilation
errors and unrelated diagnostics as evidence. Logs, copied source trees and
hashes are retained under `target/r3-episode-controls/`; its report labels full
negative regression and calibration `not_run`. It is separate from the whole
proof/runtime/package [development record](development-report.json), and neither
is release or paper-wide acceptance. Old R2 acceptance artifacts remain bound to
their original source; they are not refreshed by changing hashes.

The next [production recovery batch](r3-production-recovery.md) establishes
authentic mixed history links, strict inverse words and actual typed attempt
domains. The episode-level composition below remains open.

## Remaining R3 work

1. Connect recovery intervals to R2's actual managed scalar/typed replacements,
   shared aliases, pending inverse attempts and joint production histories.
   Derive the required admissible-interference conditions from those histories;
   the concrete Xor equation is not automatically a theorem for these effects.
2. Extend constructive deletion to its explicitly admissible Child/consumer
   cases. Construct the surviving execution, preserve real allocation and
   admission, and state when deletion is impossible. Table equality alone cannot
   discharge this criterion.
3. Compose the applicable results across the audited component carrier and
   repeated production episodes, then perform the combined R3 semantic review
   and acceptance against its unchanged exit criteria.
