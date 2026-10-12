# R1: a context interpretation connected to executable code

[简体中文](r1-semantics.zh-CN.md) · [Paper milestones](paper-refinement-roadmap.md)

R1 establishes an explicit **finite, strict context interpretation** for the
verified synchronous interpreter. A parent that creates children, its
continuations, its service values and its captured inverses now have a common
semantic contract connected to executable Rust. This completes R1 under that
interpretation; it is not a proof that the original paper's unrestricted total
function interpretation is equivalent to the runtime.

The original paper ledger remains separate. In particular, items 28, 47, 55,
56 and 57 retain their original audit status. The changes below are named
revisions, not silently strengthened premises for those original statements.

## The interpretation

The carrier contains every finite, typed, well-formed registry of the specified
interface, including states that are not on a selected execution history.
Operations return `Option<Landed>`: missing bindings, conflicting provisions and
invalid Child choices remain undefined. Native APIs preserve their checked
`Result` errors. The native allocation bound and duplicate declaration checks
are explicit parts of the representation.

The executable `FreshDriver` language contains Unit, Provide, Xor and dynamically
allocated Child instructions. Its code bank is validated before registration.
Its finite dependency graph of blueprints supports nested children; continuations
preserve the original program indices. The generic semantic contract supports
typed primitive libraries with proved scalar inverse laws. The executable u64/Xor
library supplies those laws in `library_theory`; they are not caller assumptions.

The reified context reads actual storage:

| Field | Representation and interpretation |
| --- | --- |
| Registry | Identities, parent, retirement, phase, declarations and committed providers |
| Services | Every registered owner's actual key/value table, including non-Active tables |
| Root and current iterator | Validated blueprint and program counter, interpreted by the same fresh-name grammar |
| Accumulator | Actual retained inverse receipts, interpreted in reverse order as a strict partial function |
| Allocation | Monotonic next identity, including the finite-machine capacity limit |

There is no self-referential store of all mathematical functions. Function
fields are represented by finite code and receipt data. The interpretation
compares their behavior on **every test context**, including inverse failures;
it does not infer function equality merely from matching journal numbers.
The representation is ghost code and adds no runtime dependency or Node.js
requirement. `inverse_at` provides read-only inspection of an actual receipt.

## Explicit revisions

| Revision | Original clauses | Resolution |
| --- | --- | --- |
| R1-CONTEXT | Definition 28; function fields of Definitions 48–50 | Use finite reified code and journals. Do not assert the printed unrestricted `μΓ. Γ × (Γ → Γ) × Σ` equation. The existing diagonal obstruction remains in the audit. |
| R1-DOMAIN | Definitions 29–30, 48, 52, 55–56; Lemma 57 | Use an indexed strict Component contract. Admission observes control and declared service values; recovery compares service observations. Keep failure explicit and prove the actual returned inverse. |
| R1-FIELDS | Equation (54), iterator and accumulator fields | Interpret root/current code and retained journals as strict partial functions on arbitrary inputs. Prove equality between executable storage and its source interpretation. This is not a classification of arbitrary callbacks or all observationally equivalent programs. |

Separating admission from recovery is necessary. A successful Child creation
followed by its actual inverse leaves a retired, empty, registered child. Service
observations recover, but the child's provision still blocks a second creation
at a **different fresh name**. `no_single_recovery_and_admission_relation` proves
that no relation can both count this as recovery and preserve that strict Child
domain. Simply adding control fields to table equality cannot repair both claims.

## What is proved

`guarded_components::member_is_component` derives a semantic contract from the
least constructor grammar and scalar primitive laws. It quantifies every legal
input of the declared carrier, rather than assuming a successful trace. It covers:

- Exact success/failure transport. Unrelated service values may differ: declared
  inputs alone determine value reads, outcomes, continuations and receipts once
  admission control agrees.
- Forward write confinement, typed finite outputs, and service recovery by the
  actual returned inverse.
- Preservation and inverse write confinement on every legal input where that
  captured inverse is defined.
- Semantic membership of the actual continuation and dynamically spawned root.

`MixedDriver::root_component` establishes this contract for every installed
native root, including the spawning parent. `reified_representation` relates the
actual store to the source configuration. `function_correspondence` compares
root/current calls and accumulated inverses on arbitrary input states.
`reified_insertion_domain` includes the real allocator limit, validation,
declaration uniqueness and registry conflict guard.

`run_inspected` connects these results in an executable caller. It accepts a code
bank and commands, constructs the source history from an empty machine, and
returns the observed value and actual receipt. No ghost source state, successful
execution or inverse-definedness assumption is supplied by its caller. A failing
command returns its original error with the certified successful prefix.

## Reproduce the case

```sh
cargo run -p cordis-kernel --example semantic_context --offline
```

The example runs a provider and a parent that changes the provider value,
creates a child and publishes its own service. It checks:

1. The parent's own service is 42 and its captured Child inverse names child 2.
2. Parent cleanup restores the provider value to 7 and retires child 2.
3. A new parent can register, but its Child instruction fails with `Conflict`
   because the retired child's provision is still reserved. The failed call
   creates no success result or inverse; earlier successful effects remain logged.

The example runs in the normal development checks. Integration tests also inspect
the actual provider identity and XOR mask and reject reads outside a live table
or retained journal. Negative controls replace a real service read with `None`
and fabricate a Unit inverse; the corresponding executable postconditions must
reject these changes after mutant compilation succeeds.

## Review and verification

| Obligation | Review entry |
| --- | --- |
| Complete stated carrier, parent and continuation contracts | [guarded_components.rs](../crates/cordis-kernel/src/guarded_components.rs) |
| Actual values, code, all-input inverse denotation and machine limits | [reified_context.rs](../crates/cordis-kernel/src/reified_context.rs) |
| Executable caller constructing its own evidence | [inspected_run.rs](../crates/cordis-kernel/src/inspected_run.rs) |
| Why the single recovery/admission relation cannot suffice | [typed_child_domain.rs](../crates/cordis-kernel/src/typed_child_domain.rs) |
| Runtime fault case | [semantic_context.rs](../crates/cordis-kernel/tests/semantic_context.rs) |

Run `python3 scripts/record-development.py --offline` to verify the whole kernel,
run runtime checks and bind the development evidence to source files. Scoped
negative experiments are separate from the complete negative regression; consult
the [validation levels](validation.md) before treating either as release evidence.

## What remains after R1

R2 connects production managed plugin calls, arbitrary host values and host
protocol composition to an applicable effect contract. These are not covered by
the closed synchronous interpreter's u64 value theory. R3 generalizes recovery
across interference and episodes. R4 handles global scheduling, termination and
applicable confluence. Neither strict Component membership nor a successful
prefix implies that every future call succeeds, every inverse remains enabled
after arbitrary interference, or an asynchronous callback eventually completes.

The original total-function Component witness, unrestricted recursive equation
and original paper-wide completion remain independent audit targets. R1 does not
change `check-paper-coverage.py --require-complete` or promote those claims.
