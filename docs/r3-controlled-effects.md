# Controlled effects: paper operations executed by the kernel

[简体中文](r3-controlled-effects.zh-CN.md) · [Counterexample](r3-effect-boundary.md) · [Remaining R3 work](r3-remaining-work.md)

**The selected architecture routes state relevant to the paper's recovery claims
through controlled kernel operations.** A plugin describes an operation; the
same verified Rust implementation performs its real read, calculation, write,
inverse creation and history recording in both source execution and replay.
An arbitrary callback's return-value law cannot establish that boundary.

## Implemented execution path

```text
ManagedInstruction::scalar / Effect::Kernel
  -> original registered root or Child function interpreter
  -> declared service and execution-owner capture
  -> closed Instruction evaluated under the value write lock
  -> shared commit_calculation: actual write + Journal receipt + inverse
  -> original execution owner registers the inverse in its cleanup queue
```

`Instruction` is a closed, data-only enum: built-in value operations and checked
multiply/add. It cannot contain a closure, trait object or shared service handle.
Its executor only calculates from the locked value and instruction arguments.
Function branches still select from the actual result. Typed replacement remains
in the same heterogeneous function, with its original payload and inverse path.
The ordinary Rust host's `ManagedInstruction::scalar` uses this path by default.

The controlled and extensible paths share the real scalar commit routine and
inverse registration. `Effect::Scalar` continues to invoke an extensible
`ScalarEffect` outside the value lock and then check its captured input. It keeps
its return-value and interference contracts; it does not acquire a purity claim.
No arbitrary callback executes under the controlled path's value lock.

## What is proved and where

| Paper-to-code obligation | Actual implementation and contract |
| --- | --- |
| The primitive operates on its real input | [`Instruction::evaluate` and `commit_calculation`](../crates/cordis-kernel/src/scalar_effect.rs) evaluate the closed instruction against the state acquired under the same write lock. Controlled success is equivalent to the primitive being defined at that actual state; callback interference is excluded. |
| Declared selection, alias frame, real inverse ownership | [`apply_native_controlled`](../crates/cordis-kernel/src/native_effect.rs) rechecks the execution owner and admission, joins real prior receipts, and exports the existing service/alias interpretation. [`apply_controlled_effect`](../crates/cordis-kernel/src/controlled_effect.rs) registers the returned inverse in the original cleanup queue. |
| Dependent function membership and actual execution | [`managed_function.rs`](../crates/cordis-kernel/src/managed_function.rs) and [`managed_semantics.rs`](../crates/cordis-kernel/src/managed_semantics.rs) include controlled instructions in the same function semantics and successful-prefix report. `controlled_execution` derives absence of scalar interference from that actual report. This uses the existing R1 function interpretation and the original executable interpreter. |
| Preserve the complete source body during target execution | [`Source::instantiate_controlled`](../crates/cordis-kernel/src/managed_replay.rs) checks every instruction, including unvisited branches, before target registration. [`batch::run_controlled`](../crates/cordis-kernel/src/managed_replay_batch.rs) checks every source before allocating providers, then uses the original shared-object batch and authentic source order. |

For paper navigation, operations and the mediated grammar are Definitions 29/30,
components are Definition 48, and confinement is Definition 55 in the
[paper ledger](paper-coverage.md). The contracts above strengthen their runtime
premises under the audited R1 interpretation. General recovery is Theorem 68 /
Corollary 69, with the recovery expression in Equation (55); those results are
not completed by this controlled primitive/function path.

The checks are executable and verified: a source containing `Effect::Scalar`
is rejected without changing the target runtime. Successful acceptance establishes
that its retained body is controlled, not that every subsequent lifecycle action
must succeed. In particular, undefined arithmetic still fails and retains the
real successful prefix for cleanup.

## Reproduce and review

```sh
cargo test -p cordis-kernel --test managed_replay --test replay_effect_boundary --locked --offline
bash scripts/check-r3-effect-boundary.sh
python3 -B scripts/check-r3-controlled-effects-controls.py
```

The cases cover mixed scalar/payload calls, out-of-order source input, real target
cleanup back to the initial values, overflow after a successful prefix, and an
unvisited callback branch. The same verified callback counterexample is refused
by the controlled entry; the extensible entry still reproduces its interference.
Strict selected controls mutate the admission check and the actual calculation
input. They require matching positive proofs, compiling mutants and designated
contract failures; timeouts are not accepted.

Check the source-bound [development record](development-report.json) for the
integrated result. These cases and selected controls are not full negative
regression, release acceptance or R3 completion.

## Remaining boundary

This is the first concrete implementation of the chosen architecture, not an
exclusive-access capability system for every plugin resource. Other owners can
still access shared values through existing APIs. The complete scheduler must
construct target states and derive the required interleaving/ownership conditions
from production histories. `Arc<T>` payloads model retained value identity and
replacement; arbitrary mutation inside `T`, callbacks, destructors and external
I/O do not inherit a deep-state proof.

Extending the instruction set requires a verified implementation, a declared
state footprint and integration with actual history and inverse ownership. It
cannot be accomplished by attaching a "pure" marker to arbitrary callbacks.
The native lifecycle scheduler, general ownership closure, remaining execution
profiles and final Equation (55) composition remain the fixed R3-A/B/C/D work.
