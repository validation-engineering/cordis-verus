# R3: a verified return law is not a complete effect contract

[简体中文](r3-effect-boundary.zh-CN.md) · [Source ordering](r3-source-schedule.md) · [Remaining work](r3-remaining-work.md)

**A real counterexample prevents deriving general target success from the current
`ScalarEffect` return law alone.** This is an interface/proof obligation, not a
solver limitation or a reason to assume the desired target success.

The shared [fixture](../crates/cordis-kernel/tests/support/replay_effect_boundary.rs)
implements `ScalarEffect` and proves its exact `Add(1)` return law. It also holds
a real identity issuer and a reference to the target value. On the second call,
it performs an additional `Add(0)` write to that shared value before returning.
`Add(0)` preserves the numeric value but increments outstanding inverse depth.
Nothing in the current trait's return-value postcondition prohibits this write.

The [runtime case](../crates/cordis-kernel/tests/replay_effect_boundary.rs) uses
the original registered root interpreter and `Source::instantiate`:

1. Source and target start with scalar state `(value = 5, depth = 0)`.
2. The source call returns the modeled result and successfully writes `(6, 1)`.
   The target is still `(5, 0)` before replay.
3. The target runs the same retained function. Its computation performs the
   extra target write, producing `(5, 1)` before normal landing.
4. The normal landing rejects interference. Its managed queue receives no
   inverse for the rejected operation. The hidden write is not automatically
   registered or recovered by the modeled operation.

No concurrent thread or unverified implementation of the fixture is needed.
The script verifies the exact fixture compiled by Cargo, then runs the case:

```sh
bash scripts/check-r3-effect-boundary.sh
```

The positive proof establishes the implemented return law; the runtime test
reproduces this particular source/target pair. It does not claim to prove the
entire runtime scenario symbolically. Existing rejection and inverse-ownership
contracts continue to apply and prevent false successful acknowledgements.

## Consequence for paper-to-code refinement

The paper recovery interpretation requires the operation's accounted-for state
changes and reads to correspond to those of the executable implementation.
A pure result model plus a correct managed write is insufficient if the callback
can perform additional shared writes or retain references that are not relocated
with the target. Observing a complete source history alone cannot establish the
absence of new effects when that callback executes again.

The selected architecture establishes a [controlled effect boundary](r3-controlled-effects.md):
all state relevant to the recovery theorem must be accessed through the audited
operation interface, with declared reads/writes, identity transport and actual
history/owner provenance. The implementation direction is to constrain plugin access within the paper's
scope. Its first step connects closed data instructions to the original
interpreter, atomic commit and cleanup queue, and rejects callback instructions
at controlled replay admission. General plugin callbacks retain their explicit
environment contracts; built-in operations do not prove arbitrary extensions
have the same footprint.

This finding does **not** reduce the R3 exit criteria, declare arbitrary callbacks
verified, or close R3-A/B. The complete lifecycle scheduler and final Equation
(55) composition remain required after the effect boundary is resolved.
