# R3: publication and pending recovery at intermediate cuts

[简体中文](r3-observation-recovery.zh-CN.md) · [Final value/Child recovery](r3-final-recovery.md) · [Milestones](paper-refinement-roadmap.md)

This completes the second remaining R3 package for the native production
observation: exact typed publications, Episode owners and managed writes awaiting
inverse registration. Every intermediate cut comes from the actual shared Journal,
including cuts during loading, failed cleanup and retry. **R3 remains in progress.**
[Package 3](r3-host-recovery.md) completes ordinary Rust host ownership migration; legal surviving production execution remains separate work.

## The guarantee

`NativeRuntime::recovery_snapshot` captures after an earlier real Journal snapshot
and constructs its recovery evidence from the runtime's complete typed history.
It needs neither expected final tables nor a caller's list of successful cleanups.

```rust,ignore
let before = world.publication_snapshot();
// Run actual root/Child functions, publication, cleanup and retry.
let recovery = world.recovery_snapshot(before.joint());
```

The captured interval explains **every** cut between the earlier read and the new
read. Its three observations are reconstructed as follows:

| Observation | Retained part | Newly created part |
| --- | --- | --- |
| Typed publication | Earlier publication, with its exact payload references, imports and Begin capture, until that provider's Unload | Actual Finish whose publication has not subsequently been consumed by Unload |
| Episode owner | Earlier owner until its Unload | Actual Begin whose owner has not subsequently been consumed by Unload |
| Pending inverse registration | Earlier managed write until its actual RegisterInverse commit | Actual managed forward that has not yet been registered |

These are source-derived normal forms, not tables calculated from assumed target
values. Native state indices are derived from actual raw Journal records; value,
work and cleanup commits between native transitions remain in the interval.
Each current publication/owner has a unique unconsumed opening. The source index
distinguishes repeated Episodes of one provider, even if they publish the same Arc.
A pending entry identifies its actual creating write and object; registration
consumes it exactly once and it cannot reappear at later cuts.

The capture also runs the complete observation query. Its proof-only result is
`None` exactly when all source effects in this observation balance. That result
implies exact equality of the earlier and current publication, owner and pending
tables. Otherwise the result identifies a concrete source obstruction:

| Observation | Diagnosis |
| --- | --- |
| Publication / owner | `Removed`: the first actual Unload consuming an entry present at the earlier cut. `Introduced`: an actual Finish / Begin still unconsumed at the new cut. |
| Pending | `SettledInitial`: an actual registration consumed an earlier pending obligation. `Outstanding`: an actual new managed forward still awaits registration. |

These diagnoses concern recovery relative to a selected cut, **not runtime errors**.
Registering an earlier pending inverse is useful progress, but it changes that
cut's pending table. Similarly, republishing equal data in a new Episode does not
restore the old creation identity. Source balance is stronger than accidental
endpoint value equality.

## Composition with value and Child recovery

The existing `RecordedExecution::capture_release_census` now includes
`observations` and `observation_issue`. Their source is the **same native snapshot**
as the value/Child census, and their start is the authentic pre-Begin cut. Thus
publication and pending changes during the call are included, rather than starting
only at the call's return. Both results must be considered: value recovery alone
does not imply restoration of the publication/owner/pending observation, and
inverse registration does not imply that the inverse has run successfully.

`Interval::completed_lifetimes` is a nonempty proof client over this actual source.
It takes an interval containing a Begin and a managed forward, preserves initial
resources, and identifies actual later Unload and registration commits for all new
lifetimes and writes. It derives source balance and the three recovered tables;
final table equality is not a premise. Multiple providers, repeated Episodes and
failed intermediate attempts may interleave.

`registration_microsteps` examines an actual successful registration. Every cut
after its creating write and before insertion contains the corresponding pending
entry; every later cut excludes it. No other registration can consume that write.
This also covers the microsteps hidden by a function-return-only observation.

## Production boundary and cost

These are verification-facing APIs. Callers establish the earlier snapshot's same
Journal/native source; the runtime's read lock establishes chronological extension.
Historical typed observations come from the current native owner's maintained
complete history. The query does not compare independently supplied typed histories.

`interval`, `issue`, `observations` and `observation_issue` are `Ghost` evidence,
erased from ordinary Rust. They are not runtime recovery status fields. Capture
reads the existing Journal lock and retains no payload Arc or runtime event log.
It observes execution; it does not perform rollback or schedule cleanup.

The restored projection here is the native publication/owner tables and the
Journal's managed inverse-registration table. It does not assert equality of all
control/heap/configuration records, restore arbitrary callback interiors, prove
external I/O truth, or cover Node's separate versioned-publication protocol.
The value/Child guarantees and their declared object scope remain separately
specified. The ordinary Rust host now uses [recorded ownership](r3-host-recovery.md); general legal deletion, fairness, termination
and confluence are not discharged by this package.

## Review and reproduction

| Entry | What to inspect |
| --- | --- |
| [lifecycle_state/native/runtime/history/registry_recovery.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/history/registry_recovery.rs) | Unique opening source, first consuming Unload, exact normalization and recovery query. |
| [reversible_value/joint/pending_recovery.rs](../crates/cordis-kernel/src/reversible_value/joint/pending_recovery.rs) | Intermediate pending census, real registration source and unique consumption. |
| [lifecycle_state/native/runtime/history/recovery.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/history/recovery.rs) | Raw-cut indexing, complete source scope and combined observation recovery. |
| [lifecycle_state/native/runtime.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime.rs) | Executable ordered snapshot and recovery capture. |
| [reversible_value/managed/interleaving/history/lifecycle/unload_capture.rs](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/unload_capture.rs) | Same-cut composition with registered invocation value/Child recovery. |
| [lifecycle_state/native/runtime/history/recovery/client.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/history/recovery/client.rs) | Nonempty completed lifetimes and registration microsteps. |
| [native_runtime.rs tests](../crates/cordis-kernel/tests/native_runtime.rs) | Failure, retry, blocked provider release, same-Arc republication and payload reclamation while snapshots survive. |

The runtime scenario checks actual states, payload ownership and fresh Episode
identity. It cannot inspect erased diagnoses and is not an instantiation of every
proof-client premise. The managed value/Child regression also exercises the joined
capture with real scalar/typed writes and retained inverse registrations.

```bash
python3 scripts/record-development.py --offline
python3 scripts/check-profile-controls.py observation
```

The [development record](development-report.json) is authoritative for the exact
source-bound proof, runtime and package results. `--check` checks its hashes and
performs no new verification. The two selected controls deliberately omit the
publication or pending query. Both must compile, pass a fresh matching positive
baseline and fail the specified source-balance contract; timeouts, solver limits
and unrelated diagnostics do not count. Their local report is
`target/r3-observation-controls/report.json`.

Full negative regression and scoped calibration remain **not_run** by these
commands. Development acceptance is separate from release and paper completion.
The original numbered-paper audit outcomes are unchanged: this package extends
the production observation used alongside Equations (55)/(56); pending inverse
registration remains an explicit implementation refinement, not an atomic paper
rule or proof of the unrestricted original recovery theorem.
