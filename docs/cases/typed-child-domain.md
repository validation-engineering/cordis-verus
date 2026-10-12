# A typed Child can be valid while its insertion is blocked

[简体中文](typed-child-domain.zh-CN.md) · [Refinement milestones](../paper-refinement-roadmap.md)

A plugin may have a valid component definition and still be unable to create a
child because another registered plugin reserves the child's provision. An
empty service table does not mean the corresponding declaration is available.
Retirement also does not release the reservation; removal does.

This case connects Definitions 48 and 52 to a precise insertion-domain boundary
relevant to items 55–57. Their existing ledger statuses are unchanged.

## The formal inputs

[`paper_instantiation`](../../crates/cordis-kernel/src/paper_instantiation.rs)
supplies a concrete `SmallState` carrier and editors with proved insertion,
retirement, background-preservation and faithful-readback laws. Its child is a
Unit iterator with dependency `true` and provision `false`. Every key's value
fiber is `int`; the interpretation covers every input in that carrier.
The child satisfies the full Component predicate, not just grammar membership.
It declares a provision without installing a value; Definition 48 does not
require eventual publication of every declaration.

[`equal_observations_different_domains`](../../crates/cordis-kernel/src/typed_child_domain.rs)
compares the same typed child and fresh name 2 in two concrete inputs:

| Observation | Before | After reserving a different child, name 1 |
| --- | --- | --- |
| Parent's visible binding | `true → 7` | `true → 7` |
| All-table projection | Unchanged | Unchanged |
| Parent component and phase | Unchanged | Unchanged |
| Name 2 | Fresh | Fresh |
| Provision `false` | Available | Reserved by inactive child 1, whose table is empty |
| Actual typed instantiation | `Some`, capturing inverse for child 2 | `None` |

The successful result includes the actual child name, its name-dependent
continuation and captured retirement. Immediate retirement is defined and
preserves the table observation while leaving the child registered.

## Connection to executable code

`kernel_domain` proves that this typed primitive's acceptance equals
`Kernel::insert_enabled` for the corresponding registration domain, under
explicit capacity and fresh-name conditions. `registration_matches` relates
registered names and the conflicting provision. It deliberately says nothing
about runtime service values, phase or callback interpretation.

`check_instantiation` calls the production `Kernel::check_insert`; its ghost
arguments are erased and cannot provide the runtime answer. The checked
`exercise_domain_gap` constructs the registration relation from actual empty
Kernel, insert and check calls. It proves acceptance before the reservation and
rejection afterward. A runtime regression also checks the actual `Conflict`
classification, retention after retirement and acceptance after removal.
The native allocator chooses the inserted identity. A successful preflight
does not allocate or reserve a later identity or provision.

```sh
cargo test --offline -p cordis-kernel --test typed_child_domain
./scripts/verify.sh --verify-module typed_child_domain --triggers-mode silent
```

The second command is a scoped development check. Whole-kernel verification and
all normal development checks are recorded separately in
[the source-bound development report](../development-report.json).

The canonical mutation `typed-child-check-accepts-reserved-provision` replaces the
production check in this client with unconditional success. Its scoped selector
is `typed_child_domain::check_instantiation`; a compiled mutant must fail that
function's exact-domain postcondition. A selected experiment is not a full negative
regression or completed canonical selector calibration.

## Remaining obligation

The child-input witness does not establish the spawning parent's original
full-context witness or construct recursive Gamma. The native example connects
registration domains; it does not implement `SmallState`'s value-bearing context.
Consequently this is not an unconditional refutation of original 57, 73 or 80,
nor a completed Component-to-production refinement.

The [completed R1 strict interpretation](../r1-semantics.md) now supplies a
separate full-carrier parent/continuation/child contract and actual value/code/
inverse representation. It also proves the single recovery/admission relation
obstruction using this case. The original total-function witness and production
callback/value refinement remain separate; the scope of this registration-only
example is unchanged.
