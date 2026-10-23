# R3: source-derived scalar landing

[简体中文](r3-scalar-landing.zh-CN.md) · [Shared target execution](r3-shared-target-batch.md) · [Remaining R3 work](r3-remaining-work.md)

A retained successful source operation can now drive a checked scalar operation
in a real target Episode. Its definedness comes from the actual source report.
The target captures a declared service, reads its current value and inverse
depth, invokes the preserved computation, and lands through the same native
effect path used by the managed interpreter.

**This closes a primitive-level success obligation, not the entire R3-A
simulation.** The batch scheduler must still derive the corresponding inputs
and permitted interference from its production history.

## Execution and contracts

```rust,ignore
let prepared = source.prepare_scalar(step_index, &target_owner, group_id)?;
let target_step = prepared.land(&mut target_owner, group_id)?;
```

`step_index` selects an operation in the source's actually executed successful
prefix. It is not a desired target result or an arbitrary instruction index.

| Stage | Executed code and verified guarantee |
| --- | --- |
| Source | `Source::wf` binds the stored body, port list, operand and retained inverse to the actual registered report. It now includes the body/port length invariant. |
| Target read | `Source::prepare_scalar` captures the preserved port through the real target owner. `Capture::prepare_at` checks both the value and inverse depth before computing. An `InputMismatch` retains the actual selected binding, certified snapshot and read receipt as erased evidence. |
| Computation | The original `ScalarEffect` runs outside the service/value locks. Source success and the checked input prove that its semantic operation is defined. |
| Landing | `PreparedStep::land` calls the existing `apply_native_effect`. With that prepared input, the result is either a corresponding actual `Step`, `Closed`, or `Interference`. `Capacity` and `Rejected` are excluded by the proof. |
| Success | The actual before/after values, outcome and branch equal the source step. The new inverse is in the target owner's actual queue, with its actual registration receipt; no source inverse is reused. |
| Failure | Wrong/closed admission performs no landing. Interference has an authentic rejection receipt; the rejection preserves the joint state and outstanding obligations at that commit and does not add an inverse to the owner. |

For an admitted landing the contract establishes:

```text
landing succeeds ⇔ actual state at landing = captured source input
```

This is a statement about the actual landing receipt, including failed attempts.
It does not require a successful target step as an input to the proof.
`quiet_input` also gives a sufficient condition: between the actual target read
and landing, no frame changes that target allocation's state. `unchanged` derives
the landing input from those real Journal frames, and the executable `land`
method invokes that proof. Other allocations may change, and rejected attempts
may occur. A change followed by restoration can also satisfy the exact state
test; the quiet condition is sufficient, not necessary.

## The uncertainty this exposes

`ScalarEffect::compute` proves a return-value law. It does not prove that the
implementation leaves all shared state untouched. Even a verified computation
may perform additional operations; another actor may also change the captured
object before landing. Copying an effect does not remap references hidden in
its implementation.

Consequently, successful source execution alone cannot establish successful
target execution for arbitrary host behavior. The existing interference check
is necessary. R3 still needs to derive target input correspondence and the
appropriate scheduling/effect-frame conditions from ownership and the captured
history. Effects outside the mediated scalar/typed scope need their own source
and frame contracts. Neither a silent purity assumption nor a new
“target succeeds” caller premise closes that obligation.

The new entry executes one scalar operation. It does not schedule a registered
root/Child, settle its work, implement typed replacement, or finish an Episode.
`batch::run` still uses the original registered interpreter and retains its
current scope; it has not been switched to a second replay interpreter.
Matching a port and input here is also not a replacement for the batch's
allocation/alias correspondence.

## Paper-to-code review

The primitive domain, result, continuation and strict inverse use the same
`managed::semantics` interpretation as R1/R2. This supplies part of the
constructive surviving-execution obligation under R3's recovery items
68, 69 and 79 in the [paper plan](paper-refinement-map.md).
It is not yet the general recovery conclusion of Equation (55).

Read [the executable source bridge](../crates/cordis-kernel/src/managed_replay_scalar.rs),
[the native capture/landing path](../crates/cordis-kernel/src/native_effect.rs),
and [the scalar computation contract](../crates/cordis-kernel/src/scalar_effect.rs)
together. The source operands are retained by replay opt-in; the new read,
Journal and inverse correspondence evidence erases in ordinary builds.

The runtime cases in
[managed_replay.rs](../crates/cordis-kernel/tests/managed_replay.rs) cover real
branch/depth progression and cleanup, a same-value/different-depth rejection,
interference followed by actual restoration and retry, unrelated writes, and
wrong or withdrawn owners. The strict
`scripts/check-r3-scalar-landing-controls.py` control removes the depth check:
the mutant must compile and fail at the designated input-equality assertion.
Scoped evidence does not replace full development, full negative regression
or release acceptance.
