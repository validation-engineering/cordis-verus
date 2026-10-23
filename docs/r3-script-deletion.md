# R3: legal deletion from a real script

[简体中文](r3-script-deletion.zh-CN.md) · [Episode value recovery](r3-episode-recovery.md) · [Production recovery](r3-production-recovery.md)

The actual Mixed `run_script` report now carries a conditional **legal surviving
execution**, alongside its episode value-recovery equation. The target is
constructed from the report's source history; callers do not supply a successful
target execution, expected heap or successful inverse.

A separate [closed-region construction](r3-closed-region-deletion.md) now handles owner-created Child and actual consumers together, for both Mixed and Fresh. The private-episode certificate described on this page retains its own narrower guards and shared-effect result.

## Admitted source interval

The selected interval starts at an actual owner Begin and ends at that episode's
actual Unload. It may occur inside a longer script, including a script returning
a checked error after the interval. The extra conditions inspect that same source:

- The owner executes table operations. It does not create a Child in this interval.
- Other registered interfaces avoid the owner's private provisions at Begin.
- Foreign Insert and Child creation retain their real source identities and
  satisfy the same exclusion for their new dependencies. The owner is not inserted
  or removed inside the interval.

Foreign table operations, foreign Child lifecycles, dynamic registry changes and
old foreign inverse journals are supported within these guards. Shared dependency
keys are allowed: the real Xor library proves strict forward/inverse commutation
and raw-outcome stability over every input. A consumer of the deleted owner's
private publication does not meet the declaration condition.

## Result and execution link

The constructor omits the owner's activation and cleanup steps while retaining
external retirement. The owner remains registered and inactive. Foreign calls
are reinterpreted in the target, and their inverse tokens are mapped to the
constructed target history. The proof establishes:

1. Every retained transition is legal, starting from the actual pre-Begin state.
2. The resulting control and table observation agree with the actual post-Unload
   state. Journal token numbers need not be equal.
3. The target's table projection equals the foreign value replay already proved
   for that same source episode.

`ScriptReport::recovery_history_witness` includes the deletion certificate for
every admitted closed interval. Its establishment is called by the real script's
successful and checked-error returns. `delete_private_episode` retrieves the
constructed target using that same witness.

| Review step | Source |
| --- | --- |
| Actual script witness and establishment | [episode_replay.rs](../crates/cordis-kernel/src/episode_replay.rs) |
| Source guards, target constructor and report query | [script_deletion.rs](../crates/cordis-kernel/src/script_deletion.rs) |
| Actual Xor library's strict interface | [xor_recovery_algebra.rs](../crates/cordis-kernel/src/xor_recovery_algebra.rs): `strict_interface` |
| Guard and inverse transport for the constructed execution | [foreign_child_deletion.rs](../crates/cordis-kernel/src/foreign_child_deletion.rs): `closed_deletion` |

## Scoped verification

The final combined check of native Begin, managed/payload recovery, Mixed/Fresh
script entry points and the Xor interface passed: **401 verified, 0 errors**.
Kernel all-target, all-feature Clippy and paper-map consistency checks passed.
These results are scoped development evidence, not whole-paper or release acceptance.

```sh
source scripts/toolchain-env.sh
./scripts/verify.sh --verify-module mixed_driver --verify-module xor_recovery_algebra \
  --verify-module reversible_value::managed --verify-module reversible_value::payload \
  --verify-module lifecycle_state::native::runtime::episode \
  --num-threads 2 --triggers-mode silent --output-json --time
```

## Boundary and pending acceptance

This certificate currently applies to Mixed scripts. It is separate from the
Fresh value-recovery result and from production native/Node lifecycle deletion.
The separate closed-region result handles selected Child/consumer families.
Combining them with this single-episode shared-effect profile still requires
birth/name/parent and consumer-admission transport; table equality alone is
insufficient. The original
paper counterexamples and R3 exit criteria remain unchanged.

Pending integrated acceptance covers a nonempty shared-dependency episode with
foreign Child creation and Unload, repeated interior episodes, checked-error
prefixes, and rejection of private consumers or owner-created Children. Negative
controls must reject dropped foreign births, incorrect retained labels or a
target with fabricated receipt provenance. Full development and negative-control
acceptance remain separate from the scoped proof checks.
