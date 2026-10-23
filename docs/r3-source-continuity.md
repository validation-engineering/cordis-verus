# R3: recovery from authenticated value sources

[简体中文](r3-source-continuity.zh-CN.md) · [Observed recovery](r3-observed-recovery.md) · [Common recovery cut](r3-common-recovery-cut.md)

Complete native intermediate publication/owner/pending observation recovery is now covered by [package 2](r3-observation-recovery.md). Related boundaries below describe this earlier entry point; ordinary-host migration and general legal deletion remain open.

The recorded production path now derives value continuity from the actual
Journal and payload history resources. Its recovery entry points no longer
require the caller to supply equality between each event's observed value and
the recovery interpreter's reconstructed heap.

**R3 is still in progress.** The admitted synchronous Fresh deletion/replay
result is described [separately](r3-closed-region-deletion.md). The [final recovery composition](r3-final-recovery.md) now consumes complete
producer intervals at an actual native cut. Broader observations and ordinary-host
migration remain open.

## What the running code retains

`Inverse::restore_following` captures an authenticated payload history while
holding the real storage lock. A successful restoration records the resulting
history; an interference failure records the history it actually read. A closed
payload has an authentic retirement observation and no live value history.

`Sources` keeps the longest authenticated prefix for each payload source. Merging
two sources uses persistent Verus resource agreement. A matching numeric key or
revision alone cannot establish agreement. Histories retain the complete semantic
state, including payload identity, head and depth; a restored head at a newer
revision is therefore distinguished from a fresh replacement with equal contents.

`RecordedExecution` owns this evidence alongside its real cleanup queues:

- `run_recorded_root` retains the actual root/Child function's typed histories.
- `run_function` retains successful steps, including a prefix followed by failure.
- `dispatch` retains successful, failed and closed typed cleanup observations.
- The cross-owner observed methods merge the actual source evidence.
- `apply_scalar_observed` and `apply_payload_observed` execute raw reversible
  forwards and retain their actual sources automatically.
- `restore_scalar_observed` and `restore_payload_observed` execute raw restores
  and record both success and failure. Scalar failure returns the same linear
  inverse; typed failure retains the actual locked observation.
- `observe_payload_restore` remains available for explicitly importing a tracked
  result produced by the raw restore API.
- All supported lifecycle changes preserve the accumulated evidence.

Its invariant states that every retained event's typed decoder is covered by
these sources. The proof-only `observe_foreign` entry requires that coverage;
an arbitrary payload history cannot be inserted as an observation. These data,
including merges and history traversals, are erased. They add no runtime log,
lock, allocation or user dependency.

## From storage ownership to complete producer sources

`scalar_source_snapshot` and `payload_source_snapshot` now return a
`Producer::certified` proof through the actual `RecordedExecution` read paths.
For each captured allocation, the certificate derives three facts:

1. Every real same-allocation Journal frame has a source position, including
   operations performed through raw handles outside the recorded facade.
2. Every successful restoration names an earlier actual creating operation
   with the same address, before/after values and origin position.
3. A creating position is successfully consumed at most once.

These are postconditions of the storage/host code, without a caller-supplied
complete-coverage or unique-consumption premise. Scalar storage maintains an
erased linear inverse lease: ordinary operations, computed effects, cursors and
batch execution mint it at the real write; failed restoration returns it;
successful restoration consumes it. The actual restore event names that origin.
A second operation reaching identical scalar value/depth states has a different
lease. The Journal's separate linear last-write frontier prevents an owner from
skipping same-allocation commits, even when their records are equal.

For typed storage, successful restoration now proves that it returns to the
actual creating operation's predecessor. The semantic history reconstructs the
live head stack; restoring a head removes it permanently, and later fresh
revisions cannot revive it. This proves unique success despite the borrowed
`restore(&self)` API. Replacement and retirement stay in the complete census as
explicit non-reversible barriers. Terminal evidence survives retirement in an
owner-independent erased record, so source collection remains available after
`capture()` returns `None`.

The certificate covers the captured lifetime of one allocation. It neither
freezes future mutations nor certifies arbitrary mutable data inside a payload.
The proof resources and terminal histories erase; explicit source collection
reads existing storage locks and does not clone user payload Arcs.

## From source guards to recovery

`run_recorded_root` establishes `source_order` at the real function return.
Subsequent managed calls, dispatch, the four observed raw operations, and
same-Journal cross-owner observation export `source_order_extends`. Work, Child,
registration, callback acknowledgement, retry and release preserve that evidence.
A verified client can compose these public postconditions instead of supplying
chronology again after every call. Different Journals retain independent clocks;
manual proof-only imports do not automatically establish chronological order.

`capture_invocation_census` now captures an authentic common endpoint, reads
all actual scalar/typed owners in the declared invocation scope, retains typed
source witnesses, constructs the interval and calls `recorded_census`. It is an
executable `RecordedExecution` method; the same registered-report contract serves
root and Child calls. The lower-level `capture_recovery_interval` accepts actual
start/end receipts when an existing lifecycle endpoint is needed.

`Interval::new` scans the actual Journal positions in order. Each reversible
mutation produces one source-backed `Event::Produced`; raw operations outside the
recorded facade are included. Aliases use the actual `(Journal, allocation)` key,
and a single commit cannot appear twice. Persistent receipt-prefix extraction
keeps historical cuts authenticated. Typed capture now reads a common Journal
cut under the real storage lock, including retired owners, instead of ending at
the owner's last mutation.

`Interval::initial` derives the creating writes which were not consumed before
the start cut. `Interval::origin` proves that every successful interval restore
either names one of these pre-interval obligations or a prior creating event in
the same interval. Unique physical consumption and the one-event-per-commit
projection derive the absence of duplicate successful observations. The derived
inventory is a source census: it does not transfer ownership of executable
inverses or assert that an arbitrary historical inverse word is executable.

`recorded_census` no longer takes `coverage::complete`, `origins::admitted`,
chronology, read gaps or quiet tails as caller premises. It constructs those
facts, then recovers the registered invocation's Begin values from the actual
endpoint using the remaining inverse word, **or returns a concrete proof-only
obstruction**:

- `Change` identifies a changed Journal frame outside the reversible projection,
  including destructive payload replacement or retirement.
- `Earlier` identifies an actual successful restore whose creating position is
  before the interval but whose inverse is outside this invocation's retained
  word. A foreign restoration can legitimately cross Begin; that cannot be
  advertised as restoring this invocation's Begin.

The actual declared object scope, valid registered report and its retained
cleanup relation remain inputs. The producer certificate does not discover
arbitrary JavaScript objects or prove external callbacks. The returned interval
and diagnosis erase; this API does not implement automatic rollback or a runtime
status indicator. Explicit collection takes real storage/Journal read locks but
retains no executable log or additional user payload Arc. The earlier manually
observed route remains available as `observer_census` and
`recover_observer_censused_prefix`; its source guards remain explicit.

`recover_recorded_prefix` composes these results with the actual registered
invocation's retained inverses. At any admitted prefix, the constructed remaining
strict inverse word is defined and recovers that invocation's Begin values.
Foreign writes and failed cleanup attempts may still be present. This is a
managed value specialization of Equation (55), including the inverses of admitted
foreign forwards; it does not assert that the local owner can consume another
owner's resources.

`unload_recovers_from_source_history` additionally composes the existing terminal
foreign-owner evidence, actual native Unload, original Child resolutions and
settled forward registrations. It proves recovered values and Child terminal
state at one actual native snapshot. Its pre-existing Child completeness,
foreign observation coverage and quiet-tail conditions remain explicit.

The new [capture_release_census](r3-final-recovery.md) route uses the complete
producer interval through the actual native snapshot. It derives local closure
from Unload, checks every foreign creation and original Child obligation, and
returns a same-cut recovery result or a concrete obstruction. The nonempty
terminal-owner/Child client derives closure without an observer coverage or
post-Unload quiet-tail premise.

| Review step | Source |
| --- | --- |
| Actual locked restore capture | [payload_inverse.rs](../crates/cordis-kernel/src/payload_inverse.rs), [payload_attempt.rs](../crates/cordis-kernel/src/payload_attempt.rs) |
| Persistent prefix merge and agreement | [shared_value_sources.rs](../crates/cordis-kernel/src/shared_value_sources.rs) |
| Report/dispatch evidence and decoding | [managed_value_sources.rs](../crates/cordis-kernel/src/managed_value_sources.rs), [cleanup_recovery.rs](../crates/cordis-kernel/src/cleanup_recovery.rs) |
| Executed raw forward/restore capture | [managed_lifecycle_values.rs](../crates/cordis-kernel/src/managed_lifecycle_values.rs) |
| Maintained production chronology | [managed_source_order.rs](../crates/cordis-kernel/src/managed_source_order.rs), [managed_lifecycle_order.rs](../crates/cordis-kernel/src/managed_lifecycle_order.rs) |
| Linear last-write ownership and complete allocation projection | [joint_owner_history.rs](../crates/cordis-kernel/src/joint_owner_history.rs), [joint_execution.rs](../crates/cordis-kernel/src/joint_execution.rs) |
| Actual scalar inverse leases, creation and unique consumption | [scalar_ownership.rs](../crates/cordis-kernel/src/scalar_ownership.rs), [reversible_value.rs](../crates/cordis-kernel/src/reversible_value.rs) |
| Typed predecessor, unique restoration and retained terminal sources | [payload_semantic_history.rs](../crates/cordis-kernel/src/payload_semantic_history.rs), [payload_source_history.rs](../crates/cordis-kernel/src/payload_source_history.rs) |
| Unified producer certificate returned by the host | [managed_producer_sources.rs](../crates/cordis-kernel/src/managed_producer_sources.rs), [managed_lifecycle_values.rs](../crates/cordis-kernel/src/managed_lifecycle_values.rs) |
| Full Journal census and derived read/tail gaps | [managed_source_coverage.rs](../crates/cordis-kernel/src/managed_source_coverage.rs) |
| Source-to-value continuity | [managed_source_link.rs](../crates/cordis-kernel/src/managed_source_link.rs) |
| Source-to-outstanding-inverse membership | [managed_source_obligations.rs](../crates/cordis-kernel/src/managed_source_obligations.rs) |
| Owned history invariant and public recovery entry | [managed_lifecycle_history.rs](../crates/cordis-kernel/src/managed_lifecycle_history.rs), [managed_lifecycle_sources.rs](../crates/cordis-kernel/src/managed_lifecycle_sources.rs) |
| Automatic interval and pre-interval obligations | [managed_producer_interval.rs](../crates/cordis-kernel/src/managed_producer_interval.rs), [managed_producer_event.rs](../crates/cordis-kernel/src/managed_producer_event.rs) |
| Actual host capture and registered root/Child recovery | [managed_producer_capture.rs](../crates/cordis-kernel/src/managed_producer_capture.rs), [managed_producer_recovery.rs](../crates/cordis-kernel/src/managed_producer_recovery.rs) |
| Actual common native cut | [managed_recovery_cut.rs](../crates/cordis-kernel/src/managed_recovery_cut.rs) |

## Historical interval validation and remaining boundaries

The following results belong to the preceding producer-interval batch. Current
final-composition validation is described in [final recovery](r3-final-recovery.md);
the development record detects changes since its last complete run.

The producer-interval batch passed scoped validation on 2026-10-19 with pinned
Verus `0.2026.10.04.1687598`: **541 verified, 0 errors**. This checks the affected
history, Journal, typed-source and managed-recovery modules, not the entire crate:

```bash
source scripts/toolchain-env.sh
./scripts/verify.sh \
  --verify-only-module reversible_value::history \
  --verify-module reversible_value::joint \
  --verify-only-module reversible_value::payload \
  --verify-module reversible_value::payload::source \
  --verify-module reversible_value::payload::semantic_history \
  --verify-module reversible_value::payload::restoration \
  --verify-module reversible_value::managed \
  --num-threads 2 --triggers-mode silent --output-json
```

The four kernel suites `managed_function`, `native_runtime`,
`registered_value_function` and `reversible_value` passed **69 tests**. Kernel
Clippy (`--all-targets --all-features -- -D warnings`), formatting and the paper
coverage, review and refinement checks also passed. Cargo checks used
`--locked --offline`. Whole-kernel development acceptance and full negative
controls for this batch: **not_run**.

Two nonempty registered-root regressions exercise the new executable capture:
`invocation_census_collects_raw_aliases_without_retaining_payloads` covers raw
writes, duplicate handle aliases, cleanup interference, restoration and native
retry, while checking values, depths and user Arc counts. The second,
`invocation_census_reads_destructive_and_retired_producers`, checks collection
after destructive replacement and repeated collection after retirement. The
interval and `Issue` values erase; runtime assertions do not validate these proof
objects. Verus checks their provenance, recovery implication and obstruction
contracts.

The added regression `producer_snapshots_cover_raw_calls_repeated_states_and_retirement`
in [managed_function.rs](../crates/cordis-kernel/tests/managed_function.rs)
executes raw calls outside the facade, failed scalar restoration and retry,
repeated scalar states, repeated typed contents, old typed inverse rejection,
replacement, retirement and repeated terminal source collection. It also checks
that source collection does not retain extra user Arc references. Runtime
assertions do not test erased provenance; that guarantee is checked by Verus.

The existing nonempty cross-owner regression exercises scalar and typed writes,
a failed function prefix, cleanup interference, foreign restoration, native retry
and successful release through these modified production methods. It remains a
runtime regression, not an instantiation of every premise of the common-cut
proof. The [development record](development-report.json) is the authoritative
whole-workflow acceptance record; scoped checks do not replace it.

Deferred controls for this interface must reject a restore witness copied from
an old inverse instead of the locked current cell, a discarded observer source,
an omitted conflicting write, an unknown inverse origin and a duplicate success
observation. Full negative regression and scoped calibration must retain their
own explicit status; a successful development run does not execute them.
Additional deferred controls must reject a skipped owner frontier update, a
scalar restore without its creating lease, a lease reused after consumption, a
typed restore to an unrelated older head, and discarded retirement history.
For the automatic interval, also reject an omitted or duplicated mutation,
a forged receipt prefix, a hidden pre-interval restoration obligation, and a
silently ignored destructive barrier.

This result does not construct a legal lifecycle with an owner removed, extend
the value observation to all publications/pending effects at intermediate cuts,
prove arbitrary callback effects, or prove scheduling/termination. Those claims
are not consequences of Equation (55)'s value equality. The original paper
outcomes and R3 exit criteria are unchanged.
