# R3: transport the complete native Journal carrier

[简体中文](r3-effect-deletion.zh-CN.md) · [Native window](r3-native-deletion.md) · [Milestones](paper-refinement-roadmap.md)

Package 5 connects an interior native episode window to **a legal surviving
Journal trajectory**, including the other retained record kinds, actual guard
reads, slot references and pending inverse registrations. The source is the
same certified production snapshot used by the earlier recovery captures.
**R3 remains in progress.** This is constructive transport of the R2 Journal
relation, not yet executable replay through the production allocator or arbitrary
Rust/Node callbacks.

## What is guaranteed

A caller selects a native window and a proof-only mask over the actual Journal
frames. Native selection comes from the window; the mask selects other effects.
There is no caller-supplied initial state, desired target trace or successful
inverse. `Snapshot::delete_effect_window` either returns a source obstruction or
constructs the surviving frames and proves:

- Every retained step satisfies the actual `joint::step` relation and R2 record
  classification, including Work, Cleanup, Groups, Host, Control, configuration,
  scalar operations, slot replacement and payload-version transitions.
- Ordinary steps keep their source operation and exact local input. The reads
  used by cross-record guards agree with the corresponding source reads. Native
  guards compare the referenced actor's registration and owner; an unrelated
  native revision is not treated as a dependency.
- Local slot references still point to retained Object records. Foreign Journal
  identities remain external references, with no invented local value.
- Inverse registration points to the retained creating forward after event
  indices are compressed. A retained pending write and its settlement cannot be
  split. Outstanding pending entries are the exact renamed source entries.
- Scalar Restore origins are also compressed, identify the original retained
  forward and inverse values, and are consumed at most once in the target.
- The final native control, publications and Episode owners equal the original
  endpoint. Its revision counts retained native commits. Other records are not
  silently declared equal merely because lifecycle observations agree.

The native window keeps its earlier/later Episodes, source closure and actual
Child removal requirements from package 4. An arbitrary effect mask can be
rejected; this package does not automatically infer the effects of every selected
Episode.

## Source checks and reported obstructions

| Check | Meaning of a rejection |
| --- | --- |
| Window | The earlier native closure, boundary, consumer or Child condition fails |
| MaskLength | The selection does not cover this exact source prefix |
| Local | A retained step lost its exact local predecessor state |
| Read | A retained guard lost its source configuration, queue, owner or registration observation |
| Reference | A retained local slot lost its source object |
| Cause | A registration/settlement or scalar inverse lost its creating write or unique-consumption condition |

These are equalities and source obligations over the selected source records.
Target guard success is derived from the source step and preserved reads. The
internal `Plan::construct` transport combinator has a step-transport obligation;
the public snapshot query discharges it from the native-window theorem and the
checks above, rather than asking the caller to prove a successful target.

## Same executable path and recovery cut

The new APIs are in the kernel compiled by both Verus and Cargo:

```rust,ignore
let capture = runtime.publication_snapshot()
    .with_effect_deletion(Ghost(window), Ghost(effect_mask));
// In a verified client, capture.result exposes the erased construction/obstruction.
```

`RecoveryCapture::with_deletion(...).with_effects(...)` retains the existing
value/Child/native recovery results and adds this construction at **the same
snapshot**. It does not perform another Journal read, callback invocation or
cleanup. The mask, historical records and result are erased; no unbounded runtime
history is introduced. The constructed trace is proof data, never a fabricated
authenticated receipt or a second physical Journal.

## Nonempty case and validation

The proof client derives the legality of **17 source commits** containing two
interleaved managed writes, their registrations, a failed cleanup, a newer retry,
successful restoration, a local slot and a later outstanding forward. Deleting
one object's/queue's effects leaves **7 legal commits**. The retained registration
moves from source write index 5 to target index 2; the remaining pending obligation
moves from source index 15 to target index 5. The original partial restoration
domain is preserved. A retained queued inverse is not mistaken for a drained queue.

Two strict selected negative controls reject ignoring guard reads and retaining
a stale registration index. Run `python3 scripts/check-r3-effect-deletion-controls.py`.
The combined [development record](development-report.json) binds the source to
whole-kernel proofs, existing real cleanup/failure/retry tests and package checks.
Full negative regression is separate and remains `not_run` unless explicitly run.

## Review path and remaining work

| Connection | Source |
| --- | --- |
| Actual snapshot, source checks, obstruction, native transport | [native_joint_deletion.rs](../crates/cordis-kernel/src/native_joint_deletion.rs): `Selection::check`, `edge`, `endpoint`, `Snapshot::delete_effect_window` |
| Event positions, pending conservation, inverse provenance | [joint_erasure.rs](../crates/cordis-kernel/src/joint_erasure.rs): `pending_edge`, `construct`, `restoration_sources` |
| Exact reads of the production guards | [joint_erasure_reads.rs](../crates/cordis-kernel/src/joint_erasure_reads.rs): `same`, `transport` |
| Nonempty source and surviving execution | [joint_erasure_client.rs](../crates/cordis-kernel/src/joint_erasure_client.rs): `source_valid`, `nonempty` |
| Same-cut value/Child composition | [managed_deletion_capture.rs](../crates/cordis-kernel/src/managed_deletion_capture.rs): `with_effects` |

Retained Journal allocation keys are erased proof identities. Concrete registry
IDs, Kernel generations, action tickets, work domains and opaque payload identities
need distinct transport contracts. [Native control replay](r3-control-replay.md)
now compacts registry IDs and regenerates Kernel generations through actual
Kernel calls. It does not execute this full Journal relation. That composition
still needs complete producer-specific interpretation, typed inverse payload
sources and reference/ticket transport. Exact predecessor/read checks
conservatively reject some recoverable shared-write histories and revision-changing
payload/slot paths. Full heap recovery, Mixed/Fresh episode-specific replay,
asynchronous landing transport and Node protocol recovery remain separate work.
Combining certificates at a cut does not remove those obligations.

This advances the constructive surviving-execution part of Lemma 79 for the
admitted carrier. It does not upgrade the original Theorem 68/Corollary 69/Lemma 79
audit outcomes, prove general Equation (55) for every effect, or claim whole-paper,
release, scheduler-fairness or global-termination acceptance.
