# R3: executable native control replay

[中文](r3-control-replay.zh-CN.md) · [Native deletion](r3-native-deletion.md) · [Full Journal deletion](r3-effect-deletion.md) · [Milestones](paper-refinement-roadmap.md)

An admitted native Episode window now produces a surviving **control execution through the production `Kernel` methods**. The result records every actual intermediate control state. It is no longer only a sequence satisfying an abstract transition relation.

This closes the registry allocation and Kernel generation part of the replay gap. **Full production Journal replay and R3 remain incomplete.** Service values, action-ledger tickets, work domains and Node protocol events are outside this control result.

## Source-to-execution contract

`Snapshot::replay_control_window` connects a certified production snapshot to:

1. The existing native window theorem, which derives a legal surviving control history from source closure.
2. An executable finite name permutation. Retained insertions receive consecutive IDs in their original order; parents and committed provider identities use the same permutation.
3. The existing `Kernel::insert`, `begin`, `check_iteration`, `finish`, `leave`, `retire`, `begin_cleanup`, `finish_cleanup` and `remove` implementations. No function installs a proposed target state or counter.
4. A proof that every resulting intermediate state equals the renamed surviving source state. Kernel generations equal the number of retained `Begin` calls since each retained insertion. The finite source length bounds counter growth.

The preferred entry is now [automatic production source association](r3-source-chain.md). `NativeRuntime::new_recorded` records successful transitions and actual resolved declarations, including inherited dependencies and the private reservation anchor. `control_source_snapshot` derives the command/snapshot association and allocation bound. The lower-level `Snapshot::replay_control_window` remains available with its explicit source premises.

```rust,ignore
let captured = runtime.control_source_snapshot()?;
let replay = captured.source.replay(&captured.cut, &keep, Ghost(window))?;
let retained_kernel = replay.execution.kernel();
```

Normal runtimes keep recording disabled. An explicitly bounded recorder reports exhaustion instead of certifying a truncated source. Full Journal history and typed payload evidence remain erased; commands are the finite executable review input. Window and effect-selection conditions remain explicit.

Preparation rejects mismatched mask lengths, out-of-bound births and repeated allocation identities, including repeats in discarded input. Replay calls retain their normal executable error handling. The new result owns a separate Kernel; no source instance is modified. This opt-in review API stores its finite command plan; intermediate proof states and source certificates are erased.

## Concrete regression

`tests/native_control_replay.rs` creates a real native runtime with earlier, selected and later episodes of the same owner. The selected episode creates a Child that is unloaded, retired and removed. A later allocation and its consumer survive.

| Observation | Source | Executed remainder |
| --- | --- | --- |
| Control steps | 24 | 13 |
| Allocated registry slots | 4 | 3 |
| Later provider ID | 2 | 1 |
| Consumer ID / parent | 3 / 2 | 2 / 1 |
| Consumer's committed provider | 2 | 1 |
| Original owner's generation | 3 | 2 |

Commands now come automatically from successful production transitions and the actual stored `RegisteredPlugin`. The regression also checks that replay leaves the source runtime intact. It demonstrates the adapter path; the universal guarantee is supplied by the Verus contracts, under the stated source conditions.

## Review and validation

| Obligation | Executable/proof entry |
| --- | --- |
| Source window implies a runnable plan | [lifecycle_state/native/runtime/history/deletion/replay.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/history/deletion/replay.rs): `executable_step`, `executable_path`, `replay_control_window` |
| Preserve real insertion arguments | [kernel_replay.rs](../crates/cordis-kernel/src/kernel_replay.rs): `Command::from_registration` |
| Consecutive allocations and consistent name transport | [kernel_replay_names.rs](../crates/cordis-kernel/src/kernel_replay_names.rs): `compact`, `prepare`; [allocation_names.rs](../crates/cordis-kernel/src/allocation_names.rs): `prefix_pairing` |
| Source rules enable actual methods; actual successors are exact | [kernel_replay.rs](../crates/cordis-kernel/src/kernel_replay.rs): `replay_admission`, `unique`, `replay_one`, `execute` |
| Actual generation accounting | [kernel_replay.rs](../crates/cordis-kernel/src/kernel_replay.rs): `generations`, `represented_generations` |

Run `python3 scripts/check-profile-controls.py control-replay` for two strict controls: leaving an allocation in its source slot and omitting the actual `Kernel::begin` call. Each requires a matching positive, a compiling mutant and rejection at the designated contract. Full negative regression remains a separate check.

## Remaining boundary

`Kernel::finish_cleanup` here realizes the already-admitted **control** Unload. It does not acknowledge a real plugin destructor, consume a managed inverse, or invoke `NativeRuntime::release_managed_execution`. Existing production cleanup guards and ownership certificates continue to protect those operations.

Journal allocation keys are erased proof identities; concrete registry IDs and Kernel generations are different quantities. This result transports the latter. The full Journal theorem still needs its own reference/source conversion, typed inverse and work identities, publication payload correspondence, asynchronous landing and Node protocol recovery. Earlier and later control states agree under renaming; old action tickets or opaque payload identities are not thereby reusable. No general whole-effect Equation (55), R3 completion, global termination or release acceptance is claimed.
