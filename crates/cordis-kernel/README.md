# cordis-kernel

Executable Rust contracts for Cordis lifecycle and managed resources, checked
with [Verus](https://github.com/verus-lang/verus). Cargo compiles the same
implementation; specification and proof code is erased from ordinary builds.
This is an independent, experimental implementation, not an official Cordis package.

The main review case is a provider update with a consumer and one Child: failed
managed cleanup retains dependencies and recovery data, explicit retry uses a
fresh attempt, and release requires the checked protocol. The
[case study](../../docs/cases/update-recovery.md) connects the paper clauses,
actual callers, proofs and reproduction. Ordinary host callbacks remain a
separate integration boundary.

## Source entry points

These are current review domains. The
[structure and verification plan](../../docs/verification-plan.md) tracks their
physical reorganization; it does not change theorem or acceptance scopes.

| Domain | Start here | Responsibility |
| --- | --- | --- |
| Lifecycle authority | [Kernel](src/lib.rs), [LifecycleState](src/lifecycle_state.rs) | Registry, committed providers, generations, checked transitions and action protocol |
| Cleanup | [Protocol](src/cleanup_protocol.rs), [update chain](src/cleanup_update.rs), [queue](src/cleanup_queue.rs) | Requests, retained payloads, failure/retry receipts and release guards |
| Managed effects | [Reversible values](src/reversible_value.rs), [execution](src/execution.rs) | Actual mutations, captured inverses and owned execution histories |
| Host state owners | [NativeRuntime](src/native_runtime.rs), [NodeRuntime](src/node_runtime.rs) | Host-specific state and its connection to common lifecycle contracts |
| Paper interpretation | [Refinement](src/refinement.rs), [semantics](src/semantics.rs), [foundations](src/foundations.rs) | Explicit models, effect laws and implementation bridges |

Read complete `requires` and `ensures`, then follow the real caller. A mathematical
helper, a bounded interpreter theorem and a production-path guarantee have
different premises. The [paper inventory](../../docs/paper-mapping-inventory.md)
retains those distinctions and the remaining whole-paper obligations.

## Checks and boundaries

Use the repository's pinned Rust, `vstd` and Verus versions. `scripts/verify.sh`
checks the executable kernel with `--no-cheating --compile`; `cargo test` alone
does not check proofs. Full development and release gates are described in
[validation](../../docs/validation.md).

This crate does not prove arbitrary callback effects, JavaScript, FFI, external
I/O, scheduler fairness or whole-system termination. Native and Node owners
share protocol machinery, but need their own interpretation contracts. Pure Rust
runtime use requires no Node runtime. Original paper refutations and corrected
claims remain separate in the [paper audit](../../docs/paper-audit.md); general
recovery and confluence are not declared complete.

Licensed under MIT; see `LICENSE` and `NOTICE` in this package.
