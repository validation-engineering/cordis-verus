# R3: recovery ownership in the ordinary Rust host

[简体中文](r3-host-recovery.zh-CN.md) · [Final recovery](r3-final-recovery.md) · [Intermediate observations](r3-observation-recovery.md)

This completes the third remaining R3 package: route the ordinary Rust host's
actual mutations through `RecordedExecution`. R3 as a whole remains in progress;
legal surviving production executions and Node's separate protocol recovery are
still open.

## What changed

`Runtime` and the static host now keep the same recorded owner from attachment
through cleanup and release. `Plugin::native_function` attaches it at the actual
registered root return, retaining that call's queue prefix. The same entry runs
a mounted Child. Other root bodies attach at Begin and keep their existing
callback/value/service behavior. Post-return writes through `owner_context`,
resumable programs, effect groups and later Child registration extend the owner.

The owner exposes immutable `Execution` inspection through a verified `Deref`.
It has no `DerefMut` or public mutable-core accessor. The host therefore cannot
accidentally call the lower-level queue mutators: such a call fails Rust type
checking until it uses a history-maintaining entry.

| Actual operation | Maintained contract |
| --- | --- |
| Scalar writes, typed replacement, value/service programs | The old queue prefix, token identity and issued host action are preserved; new inverse slots extend the same original obligations. |
| Root work, effect handles, admission and publication | Unrelated queue histories and invocation baseline remain unchanged. |
| Managed cleanup dispatch | The actual read, inverse attempt and acknowledgement enter the recorded history, including failure. |
| Host callback/Future completion | Only the issued host action can be acknowledged; a callback cannot consume a managed inverse. Rejection returns the original result. |
| Controlled retry | The control/episode identity is checked, failed payloads and obligations remain, and fresh tickets are issued before failure flags clear. |
| Controlled Unload, effect retirement and static seal | Real drained queues become terminal evidence before executable storage is removed. |

`terminal_history` proves that every managed inverse in a terminal queue has a
matching actual successful dispatch; a Journal-bound queue also retains that
dispatch's matching acknowledgement. `release_controlled` exports this guarantee
for the actual call used by `Runtime`, covering both the initial prefix and later
registrations. This is not inferred from an empty Vec alone.

The new append contracts are proved on the existing executable mutators and
their loops. They are not extra assumptions placed on ordinary callbacks.
`NativeDriver` also exposes recorded root execution, observed controlled release
and the package-2 native recovery snapshot for verification-facing clients.

## Paper connection and boundary

The migration connects the real adapter to the maintained inverse history used
by the production refinement of Equations (55)/(56). It does not change those
equations, the source/closure conditions of the recovery queries, or the original
paper audit outcomes. Raw shared-value handles can still cause interference;
complete producer capture, rather than a host callback list, supplies external
source coverage. Appending an inverse is not proof that foreign interference
has finished or that all observations have returned to their initial values.

Histories, payload observations and terminal queues are `Ghost`/`Tracked` data
erased from executable builds. The migration stores no extra runtime action log
or historical payload Arc. An authentic root report can still be used by the
kernel's explicit common-cut capture APIs; `Runtime` does not retain all full
reports or provide a runtime "recovery proved" flag.

The Rust adapter and arbitrary callback bodies remain outside Verus verification.
The verified owner constrains the operations it calls, not external I/O truth,
scheduler fairness, eventual Future completion or arbitrary payload interiors.
The static host shares the ownership protocol but does not acquire native
publication semantics. Node's independent multi-version publication protocol,
general legal deletion, global termination and confluence remain separate.

## Review and reproduction

| Source | Review |
| --- | --- |
| [reversible_value/managed/interleaving/history/lifecycle/host.rs](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/host.rs) | Read-only core access, append-only host mutations, terminal consumption theorem. |
| [reversible_value/managed/interleaving/history/lifecycle/callbacks.rs](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/callbacks.rs) | Guarded host/Future acknowledgement and unchanged rejected result. |
| [reversible_value/managed/interleaving/history/lifecycle/native.rs](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/native.rs) | Recorded root return, controlled retry and terminal release. |
| [poll_control.rs](../crates/cordis-kernel/src/poll_control.rs) | The actual control identity checks and observed Unload. |
| [native.rs](../crates/cordis-driver/src/shared/native.rs) | Ordinary driver delegation to those same owners. |
| [runtime.rs](../crates/cordis/src/runtime.rs) | Root/Child attachment, real cleanup dispatcher and scheduler calls. |
| [reversible_value/managed.rs](../crates/cordis/tests/managed_function.rs) | Late scalar/payload writes, Child, failed callback, retained prefix, successful retry and stale-context rejection. |

Existing scalar/service programs, asynchronous callback, effect/handle, static
host and plugin suites exercise the migrated paths. The new regression checks
observable values and cleanup behavior; it cannot inspect erased proof data.

```sh
python3 scripts/record-development.py --offline
python3 scripts/check-profile-controls.py host
```

The [development record](development-report.json) binds the full development
result to exact sources. `--check` only validates hashes, not proofs. The two
selected controls omit appended history or terminal queues and must compile,
pass a fresh positive baseline, and fail the designated assertion. Their local
report is `target/r3-host-controls/report.json`. Full negative regression and
scoped calibration are **not_run** unless separately executed. Development
acceptance is not release acceptance or paper-wide completion.

[Package 4](r3-native-deletion.md) adds source-bound native interior deletion; complete effect-trajectory replay remains open.
