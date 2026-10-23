# R3: recovery from observed execution owners

[简体中文](r3-observed-recovery.zh-CN.md) · [Common checkpoint](r3-common-recovery-cut.md) · [Interleaved recovery](r3-interleaved-recovery.md)

Complete native intermediate publication/owner/pending observation recovery is now covered by [package 2](r3-observation-recovery.md). Related boundaries below describe this earlier entry point; ordinary-host migration and general legal deletion remain open.

An execution can fail to restore a value because another execution still owns a
later write. The recovery proof now derives that later write's restoration from
its actual registered inverse, recorded cleanup and drained queue. It does not
require the caller to assume that the foreign restoration succeeded. **R3 remains
in progress; complete source coverage and the value trajectory remain explicit.**

## Running path and proof

| Running source | Established contract |
| --- | --- |
| `RecordedExecution::run_function` | Every successful step belongs to its actual original queue/token and registration, including the prefix before a later failure |
| `run_function_observed` | Executes that interpreter and appends all returned forward observations to both owners' histories |
| `dispatch_observed` | Executes the real mixed dispatcher and appends the same managed success or failure observation to both owners |
| Successful group removal or native Unload | Retains the actual terminal queue with its drain guard established |
| `drained_forward` | Slot conservation forces an authentic successful managed restoration of each covered original inverse |
| `unload_recovers_from_observed_owners` | Combines source-derived foreign closure with the existing common-checkpoint value, Child and pending-registration theorem |

`owns_forward` binds a real report step to the original action, exact group,
queue, token and inverse registration. Removal does not discard the original
slot. A queue cannot drain by losing its managed inverse or replacing its
restoration with an ordinary callback's `Drained` result.

The observer can retain histories for several groups. `observations_extend`
proves that existing dispatch coverage is maintained when either observed entry
appends its actual outputs. This composes over finite sequences of calls,
failures and retries. It cannot repair coverage that was already missing.
`retain_forward_source` carries registration evidence through extensions of the
same original slot history. Early group removal is sufficient for that group's
already restored writes; the entire foreign execution need not have unloaded.

## Causal boundaries and cost

Before either observed entry runs, the source owner joins its retained boundary
with the observer's authentic receipt, when they share a Journal. Writes and
cleanup therefore follow the relevant preceding observations. Afterward, the
observer retains the source's actual completion or cleanup boundary. An earlier
receipt remains covered without being substituted for the actual predecessor.

These joins compare persistent proof witnesses. They add no runtime lock, value
clone or history buffer. Managed calls retain their existing return-time Journal
read. The observed entry points borrow the two real owners; their ordinary
execution still goes through the existing interpreter and mixed dispatcher.
Independent Journals keep separate boundaries.

## Coverage and remaining boundary

`foreign::covered` requires every relevant foreign forward in the target history
to name an actual registered step in a supplied recorded owner, that step's
terminal group, and the corresponding dispatch observations after the forward.
It checks coverage of actual dispatches, including failures. It does not ask
which dispatch succeeded. `closed_from_owners` derives successful closure using
the real drain boundary. A map of owners supports multiple sources and historical
groups; a missing source or an undrained group does not satisfy this contract.

The executable observed entries preserve coverage when used throughout the
observed interval. They do not intercept arbitrary raw writes, opaque callbacks,
unobserved dispatches or other hosts. The common-cut theorem still requires
authentic value continuity and order, complete Child endpoints, and unchanged
value tails. Neither local nor foreign release proves scheduler fairness or
eventual recovery. General publication/pending recovery, ordinary-host migration,
and legal surviving execution construction remain open.

## Review and validation

- [managed_lifecycle_observer.rs](../crates/cordis-kernel/src/managed_lifecycle_observer.rs): executable observed calls/dispatches and receipt joins.
- [managed_lifecycle_function.rs](../crates/cordis-kernel/src/managed_lifecycle_function.rs): source ownership from the actual returned prefix.
- [managed_foreign_closure.rs](../crates/cordis-kernel/src/managed_foreign_closure.rs): observation preservation, terminal-slot restoration and closure over recorded owners.
- [managed_recovery_cut.rs](../crates/cordis-kernel/src/managed_recovery_cut.rs): the composed recovery entry.
- [managed_function.rs](../crates/cordis-kernel/tests/managed_function.rs): `observed_foreign_owner_restores_failed_prefix_before_native_retry` exercises two actual owners, a failed call prefix, same-value typed interference, rejected release, foreign cleanup and native retry.

Current scoped results and reproduction commands are in the [interleaved recovery
guide](r3-interleaved-recovery.md#review-and-validation). The runtime case does not
establish every premise of the composed proof. Integrated acceptance still needs
a nonempty proof client and mutations that omit a dispatch, substitute a
queue/token or owner, discard a failed prefix, treat a retained failure as drain,
or claim cross-Journal order. Full development acceptance and new mutation
controls remain pending; full negative regression/calibration remain `not_run`.

The [source-continuity composition](r3-source-continuity.md) now retains actual typed history resources across these methods and derives value continuity from real Journal gaps. Source creation/uniqueness guards derive outstanding-inverse membership. The complete observation and lifecycle-deletion boundaries remain explicit.
