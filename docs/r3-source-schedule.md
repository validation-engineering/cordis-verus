# R3: source ordering and typed continuation

[简体中文](r3-source-schedule.zh-CN.md) · [Shared target execution](r3-shared-target-batch.md) · [Remaining work](r3-remaining-work.md)

The finite native batch now derives call order from real invocation completions.
Typed operations also have producer-derived input continuity and an atomic
captured-input landing path. These are executable R3 building blocks;
**the general surviving-execution theorem is still open**.

## Actual source order

The production recipe ledger maintains a checked executable revision alongside
its erased history. `run_replayable_root` captures that revision and the actual
recipe allocation identity after the original root completes. Its contract ties
the number to that precise `Recipes::Call` receipt. Exhaustion becomes `None`;
the counter never wraps and ordinary host execution remains available.

`order::plan` checks that retained calls belong to the same actual recipe stream,
then sorts their original slice indices. It proves a complete permutation,
strictly increasing positions and chronological receipt inclusion. It rejects
unavailable names, exhausted positions, different streams and duplicates before
any target provider is created. Comparisons retain the existing common naming
namespace requirement; they do not use lifecycle domain numbers as identity.

`batch::run` uses this plan both when selecting first operands and when invoking
the original registered root executor. `Batch::order` maps returned call order
to source indices. Failure diagnostics use the original source index. Reversing
the input slice is now supported; omitting an earlier operation whose scalar
inverse is still outstanding remains an explicit error. This orders the selected
calls, not all Begin/publication/Child/cleanup/Unload events.

## Typed input and landing

`Input::continues_payload` compares actual allocation names and executable source
heads. When they match, two persistent witnesses from the actual inverse owners
establish that the complete preceding output equals the next input, including
value and depth. No `T: Eq`, pointer cast, live source reread or caller-supplied
value equality is needed. Cleanup or retirement cannot rewrite retained history.
A mismatching head is rejected; this helper does not synthesize intervening
restores or replacements.

`payload::Capture::apply` rechecks the target's anti-stale revision **under the
same write lock as the mutation**. A successful write produces its next capture
before unlocking. Its value, semantic head, revision and commit correspond to
the actual resulting inverse. Stale, capacity and retired failures carry the
actual rejection observation and return the attempted payload. A successful
restore still advances the anti-stale revision, so old captures stay stale even
when the semantic value returns to its previous state.

`capture_native_payload` and `native_payload::Capture::land` connect this path to
the real selected service handle and cleanup owner. Landing checks owner/work/
queue admission again and registers the actual inverse through the existing
cleanup implementation. Success returns the next capture; failure adds no
inverse. The ordinary typed interpreter shares the same write and registration
implementation. Payload contents with interior mutability keep their existing
explicit boundary; an `Arc<T>` is not a deep snapshot of arbitrary user state.

## Audit path

| Obligation | Executable implementation and contract |
| --- | --- |
| Actual position, no invented ordinal | [`recipe_history.rs`](../crates/cordis-kernel/src/recipe_history.rs), [`managed_replay.rs`](../crates/cordis-kernel/src/managed_replay.rs): `Ledger::revision`, `Source::wf`, `run_replayable_root` |
| Same stream, complete chronological permutation | [`managed_replay_order.rs`](../crates/cordis-kernel/src/managed_replay_order.rs): `plan`, `prefix`, `chronological` |
| Plan drives real calls | [`managed_replay_batch.rs`](../crates/cordis-kernel/src/managed_replay_batch.rs): `run`, `actual_prefix` |
| Typed source continuity | [`managed_replay_payload_history.rs`](../crates/cordis-kernel/src/managed_replay_payload_history.rs): `continues_payload` |
| Atomic input guard and real inverse | [`payload_inverse.rs`](../crates/cordis-kernel/src/payload_inverse.rs): `apply_captured_following` |
| Actual selection and cleanup ownership | [`native_payload.rs`](../crates/cordis-kernel/src/native_payload.rs), [`payload_cleanup.rs`](../crates/cordis-kernel/src/payload_cleanup.rs): `land`, `apply_payload_captured_following` |

These support the existing recovery work package for paper items 68, 69 and 79;
they do not change the audited Equation (55) interpretation or its exit criteria.
The batch does not yet automatically compose the typed continuity and captured
landing interfaces into the full surviving lifecycle scheduler. Cross-call
scalar/typed state simulation, dynamic bindings, owner publications, Child and
interior Unload remain required. The [effect boundary case](r3-effect-boundary.md)
exposes an additional interface decision needed for general replay success.

## Reproduction and evidence

```sh
cargo test -p cordis-kernel --test managed_replay --test replay_effect_boundary --locked --offline
python3 -B scripts/check-r3-source-schedule-controls.py
bash scripts/check-r3-effect-boundary.sh
```

The selected negative controls require a matching positive proof, a compiling
mutant and rejection at the designated source-position or typed-input assertion.
A timeout or unrelated diagnostic is not a passing control. Runtime cases cover
reordered source input, mixed-stream rejection, a real slot rebind, typed
history after cleanup, two successful typed landings and actual reverse cleanup,
wrong owners, intervening replacement, retirement and semantic restoration with
an advanced revision. Scoped evidence is not whole-R3 or release acceptance.
