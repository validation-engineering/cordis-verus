# R3: final recovery at an actual native snapshot

[简体中文](r3-final-recovery.zh-CN.md) · [Source continuity](r3-source-continuity.md) · [Milestones](paper-refinement-roadmap.md)

This completes the first remaining R3 package: combine the automatically
captured producer interval, actual native Unload, foreign restoration and
original Child obligations at one real snapshot. **R3 remains in progress.**
The result connects the managed-value recovery expression around Equations
(55)/(56) to running storage and lifecycle code; it does not establish the
paper's unrestricted recovery or legal deletion theorem.

## The guarantee

`RecordedExecution::capture_release_census` takes the actual successful release
result, registered invocation report and scalar/typed handles in that invocation's
declared object scope. It reads the real native snapshot and producer histories;
callers do not supply a list of successful restores or an expected final value.

Its erased `FinalCensus` reports either a concrete source obstruction or all of
these facts at that **same snapshot**:

- The invocation's touched scalar/typed values equal their authentic Begin values.
- Every original native Child obligation has a matching completion, with the
  Child's owner and publications absent. Later registry removal preserves this.
- The invocation's forward writes have no pending inverse-registration entries.
- The actual invocation Begin and its actual native Unload occur in the retained
  Journal prefix.

The proof query returns `None` exactly when the invocation boundary is clear,
all interval forwards have matching later restores and all original native Child
obligations have matching collected resolutions. Parent Unload alone does not
establish either foreign closure or Child completion.

```rust,ignore
// After the actual owner.release(...) returned a successful ReleaseOutcome:
let recovery = owner.capture_release_census(
    &world, &report, group, offset, &release, &scalars, &payloads,
);
```

This is a verification-facing API. A verified caller also establishes the report's
retained ownership, registration and same-Journal source-order contracts. The
production methods preserve that evidence. `RecoveryCapture::evidence` is
`Ghost`: ordinary Rust cannot inspect it as a runtime recovery status. Capture
observes completed work; it does not schedule cleanup or perform rollback.
Explicit capture reads existing storage/Journal locks, with no retained runtime
history or extra user payload Arc.

## Where each conclusion comes from

| Obligation | Actual source and proof |
| --- | --- |
| Local restoration | Authentic inverse registration, retained dispatch history and the real Unload guard force a successful matching acknowledgement; `restoration_before_unload` identifies its actual write. |
| Complete interval | Storage ownership certificates produce every relevant committed mutation, including raw callers outside the recorded facade. `includes_restore` matches actual cleanup to that independent projection using source identity, creation position and typed history agreement. |
| Foreign closure | `unload_census` checks every actual interval forward. The nonempty client also derives closure from a second registered report's authentic terminal queue and Unload, without an observed-success coverage premise. |
| Child completion | The original native inverse inventory is matched against real shared-slot birth, retirement and Child Unload sources. The native ledger transfers terminal state to the same later snapshot. |
| Endpoint value | Source coverage and unique consumption derive the remaining inverse word; local and foreign completion exhaust it. The actual snapshot decodes to Begin values. |

The interval continues through the common snapshot, including writes after the
local owner's Unload. There is no assumed quiet suffix between Unload and capture.
Source boundaries remain explicit:

| Obstruction | Meaning |
| --- | --- |
| `Boundary(Change)` | A real changed frame, such as destructive replacement or retirement, has no reversible projection. |
| `Boundary(Earlier)` | A successful restore crosses the invocation boundary and is outside its retained inverse word. |
| `Foreign` | An actual interval creating write has no matching later restore by this cut. |
| `Child` | An original Child inverse has no matching collected completion at this cut. |

## Nonempty composition and runtime reproduction

`nonempty_unload_client` composes two nonempty actual registered reports, a
nonempty foreign-forward interval and one assigned native Child. Its source
profile identifies the creating report for every interval forward and the actual
Child birth/retirement/Unload. It derives foreign closure and Child completeness;
only a real invocation-boundary obstruction can remain. A clear boundary therefore
implies the complete endpoint guarantee. This finite profile allows failures and
retries; it does not assume successful restoration or the desired endpoint values.

The executable regression
`final_recovery_capture_spans_foreign_retry_and_a_later_child_unload` exercises:

1. A parent and a foreign writer changing the same scalar and typed allocation;
   the writer also consumes a publication of the parent's assigned Child.
2. Real Child retirement and parent cleanup failure caused by the foreign write.
3. Foreign restoration/Unload followed by parent retry with a fresh ticket and
   successful parent Unload, while the Child is still Active.
4. A later Child Unload, repeated capture after Child Remove, and unchanged Arc
   counts.
5. A raw write after local Unload, its restoration, and a destructive replacement;
   capture observes these operations without changing the actual values.

Runtime assertions check concrete state, values, tickets and ownership. They do
not assert erased `Obstruction` variants or instantiate every source-profile
premise of the proof client. Verus checks those contracts separately.

## Review and validation

| Entry | Role |
| --- | --- |
| [reversible_value/managed/interleaving/release.rs](../crates/cordis-kernel/src/reversible_value/managed/interleaving/release.rs) | The real Unload guard identifies the local restore. |
| [reversible_value/managed/interleaving/sources/matching.rs](../crates/cordis-kernel/src/reversible_value/managed/interleaving/sources/matching.rs) | Match actual scalar/typed restores to the complete producer projection. |
| [reversible_value/managed/interleaving/history/lifecycle/unload_census.rs](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/unload_census.rs) | Total source query, concrete obstructions and same-snapshot recovery theorem. |
| [reversible_value/managed/interleaving/history/lifecycle/unload_capture.rs](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/unload_capture.rs) | Executable capture from actual release results, snapshots and storage. |
| [reversible_value/managed/interleaving/history/lifecycle/unload_client.rs](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/unload_client.rs) | Nonempty foreign-owner/Child composition. |
| [reversible_value/managed.rs](../crates/cordis-kernel/tests/managed_function.rs) | Reachable failure/retry and later-Child runtime case. |

Reproduce the integrated checks with the pinned toolchain:

```bash
python3 scripts/record-development.py --offline
python3 scripts/check-profile-controls.py final-cut
```

The [development record](development-report.json) binds whole-kernel proof,
runtime, documentation and package checks to exact source hashes. Use
`python3 scripts/record-development.py --check` to detect stale evidence; this
hash check performs no new proofs. Earlier scoped counts in the source-continuity
page are historical and do not certify changed sources.

The two selected controls deliberately skip foreign closure or Child completion.
The strict runner requires a fresh positive baseline, successful compilation of
each mutant and rejection at the named recovery contract; unrelated diagnostics
or solver limits do not count. Its local report is
`target/r3-final-cut-controls/report.json`. Full negative regression and scoped
calibration remain **not_run** by these commands. Development checks are separate
from release acceptance and paper-wide completion.

## What remains in R3

[Package 2](r3-observation-recovery.md) now supplies complete native intermediate
publication/owner/pending observations and a separate proof query in this same-cut
capture. [Package 3](r3-host-recovery.md) now connects ordinary Rust host mutations to the recorded owner. Recovery of Node's separate protocol and legal surviving production executions still require further work.
Declared object scope, actual report ownership and matching source identities
remain inputs. This package proves neither arbitrary callback/external I/O truth
nor scheduler fairness, eventual cleanup, global termination or confluence.
