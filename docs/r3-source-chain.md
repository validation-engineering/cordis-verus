# R3: automatic production source association

[中文](r3-source-chain.zh-CN.md) · [Control replay](r3-control-replay.md) · [Full Journal deletion](r3-effect-deletion.md) · [Recovery cut](r3-final-recovery.md)

A recorded `NativeRuntime` now derives replay commands at its actual successful transition boundary. A captured source binds those commands to the exact native history, allocation bound and complete shared Journal snapshot. Callers no longer maintain a parallel command list or prove that it describes the snapshot.

This closes **automatic control-source association**, and connects it to real managed cleanup and recovery. **R3 remains open:** replay still executes the Kernel control projection. A legal remaining Journal relation is not yet an execution of every retained effect on newly created host resources.

## One source chain

1. Successful root and Child registration record resolved dependency/provision sets, parent and private anchor from the stored `RegisteredPlugin`. Other successful native transitions record their actual actor and rule. Failed operations do not add commands.
2. The production invariant proves that every recorded command matches its native successor and label. The snapshot supplies the allocation bound; no caller-provided bound is needed.
3. `Source::command_at` and `command_for` link commands in both directions to actual Journal positions. Typed `Finish` publications keep their original values, capture, action origin, work domain and committed providers. Other interleaved records retain the complete Journal's existing contracts.
4. The runtime now maintains **complete Unload-source coverage**. Every native Unload has an authentic successful release witness in the source ledger. `Source::unload_at` derives it from a command index, including its cleanup source and covered Journal prefix. Same-Journal cleanup checkpoints precede the Unload. Existing queue/token completion proofs can then follow that witness; no cleanup success is invented from a control label.
5. `Source::inverse_source` uses the same Journal to identify the managed forward behind an inverse registration and prove unique consumption. Scalar operations, typed payload operations, work/cleanup attempts, host/control records and publication metadata remain in that shared source carrier.
6. `capture_release_census` / `capture_unload_census` bind the commands to their **existing recovery cut**. `with_deletion`, `with_effects` and `replay_control` compose value/Child recovery, legal Journal deletion and real Kernel replay at this cut. When full Journal deletion succeeds, the actual replay endpoint is proved equal to its native control endpoint under the same name permutation. Binding adds no second Journal read, callback execution or payload clone.

The source certificate has private fields. A certificate from another cut cannot satisfy the verified replay contract. Shared aliases and later writes are not made invisible: their existing source-continuity and effect-selection obligations remain.

## Bounded recording

`NativeRuntime::new` and `NativeDriver::new` keep recording disabled. Their histories remain erased proof state. Use `new_recorded` for a finite review or recovery scenario:

```rust,ignore
let mut runtime = NativeRuntime::new_recorded(domain, 4096);
// Register plugins and run the ordinary lifecycle / managed effect methods.
let captured = runtime.control_source_snapshot()?;
let replay = captured.source.replay(&captured.cut, &keep, Ghost(window))?;
```

The explicit limit bounds the number of retained commands. Commands contain control declarations, not service payload references. The first excess successful transition marks recording `Exhausted`; it does **not** reject that lifecycle operation. `Disabled` and `Exhausted` return explicit capture errors, so a truncated transcript cannot certify a complete source. There is no mid-execution reset that pretends to start from the empty state. Previously captured sources stay independent of later runtime changes.

The window and its deletion mask still require source admissibility. This API is not a serialization of the erased Journal, a general event-log debugger or an automatic choice of which effects to delete.

## Review and validation

| Obligation | Entry |
| --- | --- |
| Bounded source recording and immutable cut binding | [native_control_source.rs](../crates/cordis-kernel/src/native_control_source.rs): `Recorder::append`, `bind_control_source`, `Source::replay` |
| Every actual transition participates | [native_runtime.rs](../crates/cordis-kernel/src/native_runtime.rs): `transition`, `wf` |
| Every Unload has its authentic cleanup source | [native_source_cleanup.rs](../crates/cordis-kernel/src/native_source_cleanup.rs): `complete`, `unload_collected`, `Source::unload_at` |
| Commands, typed publications and inverse origins share the Journal | [native_source_chain.rs](../crates/cordis-kernel/src/native_source_chain.rs) |
| Reuse the real managed recovery cut | [managed_unload_capture.rs](../crates/cordis-kernel/src/managed_unload_capture.rs), [managed_deletion_capture.rs](../crates/cordis-kernel/src/managed_deletion_capture.rs) |
| Ordinary Rust driver entry | [native.rs](../crates/cordis-driver/src/shared/native.rs): `NativeDriver::new_recorded` |

Runtime regressions use automatic commands for the 24→13 control replay, resolved inherited declarations and anchors, disabled/zero/full capacity, failed-operation accounting and detached snapshots. The existing scalar/typed interference, failed cleanup, new retry ticket and later Child release scenario now replays controls from the same real recovery captures and checks that collection does not retain additional payload references.

Run `python3 scripts/check-r3-source-chain-controls.py` for strict controls that omit command recording or Unload-source collection. Matching positives, whole-mutant compilation and designated semantic rejection are required. Full negative regression remains separately labelled `not_run`. See [development evidence](development-report.json) for source-bound integration results; neither scoped checks nor development acceptance claim release readiness or paper completion.

## Remaining R3 work

The source side is linked; the full target execution is still separate. It must construct and relate target Journal references, action/work/cleanup tickets, inverse producers and typed payloads through the real remaining host execution. Complete effect selection from Episode ownership, broader shared/revision-changing effects, admitted asynchronous paths and the separate Node protocol also remain open. Original paper audit outcomes, Equation (55), global termination and confluence are not upgraded by this source certificate.

[Real managed target execution](r3-target-execution.md) adds executable input retention and target invocation to this source chain. Full-Journal target scheduling and cross-invocation correspondence remain open.
