# Ownership and review map

English · [简体中文](review-map.zh-CN.md) · [Plan](verification-plan.md) · [Generated evidence](cases/generated-lifecycle.md)

Start with the state an operation owns. The production function and its Verus
contract remain together. The tables classify responsibilities and review paths;
they do not declare every function in a directory to be a production caller.

## Five guarantees, five review paths

| Guarantee / paper basis | State owner and mutation entry | Real caller and observation | Evidence / boundary |
| --- | --- | --- | --- |
| Unresolved dependents protect their provider; definitions 53–54 and L-Unload | `Kernel` owns registered identities, phases and committed bindings. [`LifecycleState`](../crates/cordis-kernel/src/lifecycle_state/cleanup.rs) owns action receipts and `execute_cleanup`; managed release uses the same `cleanup_step`. | Shared Driver calls the dispatcher; Native `RecordedExecution::release` calls managed release. Observe target **and** committed IDs through failure and retry. | `failed_child_keeps_chain` in [`cleanup/update.rs`](../crates/cordis-kernel/src/lifecycle_state/cleanup/update.rs), strict dispatcher controls, generated histories. A parent relation alone is not a service dependency. |
| Failed restore retains the inverse and payload; witnessed effects with explicit R1-DOMAIN interpretation | [`Inverse::restore_following`](../crates/cordis-kernel/src/reversible_value.rs) owns the actual shared value/depth under its lock; [`CleanupQueue`](../crates/cordis-kernel/src/cleanup_queue.rs) owns occupied payload slots and restore journal. | Actual `RecordedExecution::dispatch`, real shared values and destructor-observed payload tests. | Inspect strict inverse-domain and payload-retention contracts together. A consumed ordinary `FnOnce` failure is not managed recovery. |
| Old/duplicate replies cannot finish a new attempt; implementation mechanism | [`ActionLedger`](../crates/cordis-kernel/src/action_ledger.rs), [`CleanupJournal`](../crates/cordis-kernel/src/cleanup_journal.rs), queue completion and retry. | Actual `ActionTicket` and `RestoreTicket`, refreshed attempt, unchanged rejected state, old replies against a new Episode. | Existing receipt tests plus generated failure/retry histories. No assumption that an arbitrary asynchronous callback eventually replies. |
| A Child inverse retires its own Child; definitions 52 and 54 | [`shared_child`](../crates/cordis-kernel/src/lifecycle_state/registration/shared_child.rs) atomically creates request/inverse ownership; Native registration associates the real identity. | Original returned `SharedChild`, actual request dispatch, parent Episode and explicit provider/consumer bindings. | Exact handle/registration checks, split-handle mutation and its contract rejection. Ownership and dependency remain distinct. |
| Supported updates recover after the cause is removed; scoped evidence toward theorems 68–70 | [`NativeRuntime`](../crates/cordis-kernel/src/lifecycle_state/native/runtime.rs) owns registration, publications and actual recorded execution; the owner retains cleanup state until release. | Real roots, Child requests, interfering writes, restored causes, explicit retry, another update and complete shutdown. | Existing fixed case plus generated admitted/adverse strata. This is not general recovery equivalence, confluence or global liveness. |

The [paper inventory](paper-mapping-inventory.md) remains authoritative for open
generality obligations. A test model checks observations; it never supplies the
production history or substitutes for a refinement proof.

## Source organization and dependency direction

| Area | Ownership / purpose | Review classification |
| --- | --- | --- |
| [`lifecycle_state/`](../crates/cordis-kernel/src/lifecycle_state/), [`lifecycle_actions/`](../crates/cordis-kernel/src/lifecycle_actions/), action/cleanup ledgers | Shared lifecycle authority and committed-provider protection | Production state with attached contracts and trace composition |
| [`reversible_value/`](../crates/cordis-kernel/src/reversible_value/), [`cleanup_queue/`](../crates/cordis-kernel/src/cleanup_queue/), [`cleanup_groups/`](../crates/cordis-kernel/src/cleanup_groups/) | Managed operations, retained inverses, actual execution origins and histories | Production primitives plus interpretation/transport proofs; generality limits remain explicit |
| [`lifecycle_state/native/`](../crates/cordis-kernel/src/lifecycle_state/native/), [`node_runtime/`](../crates/cordis-kernel/src/node_runtime/) | Separate Native and Node state owners establish their own premises for the shared protocol | Production connections. Node records publications/handles/scopes; it does not prove JS object interiors. |
| [`refinement.rs`](../crates/cordis-kernel/src/refinement.rs), [`dependent_grammar.rs`](../crates/cordis-kernel/src/dependent_grammar.rs), grammar/history/recovery modules and [`mixed_driver/`](../crates/cordis-kernel/src/mixed_driver/) | Paper semantics, conditional theorems, reference executors and bridges from actual histories | Specification and proof support, including executable research drivers; being erased or not called by a host does not make it redundant |
| [`paper_counterexamples.rs`](../crates/cordis-kernel/src/paper_counterexamples.rs), recovery/mixed examples, scoped controls and frozen evidence | Counterexamples, repaired interpretations, admitted examples and falsification | Retained research evidence; separate navigation, same active verification targets |
| [`cordis-driver/src/shared/`](../crates/cordis-driver/src/shared/), [`cordis-driver/src/node.rs`](../crates/cordis-driver/src/node.rs) | Shared scheduling policy, command decoding and host state adapters | Ordinary Rust bridge, not an additional verified scheduler theorem |
| [`runtime/setup.rs`](../crates/cordis/src/runtime/setup.rs), [`services.rs`](../crates/cordis/src/runtime/services.rs), [`cleanup.rs`](../crates/cordis/src/runtime/cleanup.rs), [`poll.rs`](../crates/cordis/src/runtime/poll.rs) | Episode-bound API, service handle access, cleanup receipts and cooperative polling | Ordinary Rust host. Struct ownership and lifecycle entry points remain in [`runtime.rs`](../crates/cordis/src/runtime.rs); module splits preserve lock/drop order. |
| Optional Node facade / N-API / process / cdylib adapters | Language semantics, callback execution, transport and external I/O | Tested host boundary. Rust applications do not require Node; Harness stays a separate application. |

The dependency direction remains host → shared Driver → verified state owners →
shared lifecycle and resource protocols. Mathematical support supplies theorems
to attached contracts. It is not a runtime dependency on Node or a second copy of
the implementation. The [architecture guide](architecture.md) explains toolchain,
library, compiler, verifier and FFI trust assumptions.

## Disposition of accumulated material

| Material before refactoring | Disposition and rationale | Check |
| --- | --- | --- |
| 253 flat files connected by `#[path]` | Moved to their **existing logical module paths**: 41 lifecycle files, then 212 remaining files. All 255 path attributes removed, including two redundant attributes. No public module identity changed. | Exact body/contract comparison after path directives and source-reference updates; compile, full Verus, packaging and canonical mutation-anchor checks |
| 5,195-line ordinary `runtime.rs` | Cleanup extracted first; setup, service handle methods and poll loop extracted next. Root now 3,139 lines before future edits. Public types/exports remain stable; only necessary internal method visibility changes. | Method-body comparison, Cargo/lints, original host regressions and extracted package builds |
| 15 wrappers around the same strict control runner | Replaced by `check-profile-controls.py PROFILE` | The same canonical selections, fresh positives, full mutant compile and exact rejection diagnostics; unique full/R2 runners retained |
| Repeated entry-point lists | One task-based documentation index, this ownership map and one campaign CLI | Links, source bindings and bilingual review entry points |
| General models, conditional recovery branches, unique failures and frozen reports | Retained under research navigation and their existing verification targets | No obligation is closed by moving a file; historical reports keep their original source binding |

The fixed archive is `codex/archive-before-refactor-2026-10-24` at `60bdd89`.
The layout before the second batch is also preserved at `c47d111`. Neither branch
history nor the upstream lock is rewritten. This iteration has **no approved
semantic deletion**: more removal requires comparing premises/results, callers,
proof dependencies and unique counterexamples. The archive alone is not a reason
to delete a theorem still used by a current claim.
