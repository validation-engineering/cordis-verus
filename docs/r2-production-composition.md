# R2 package 4: production trace composition

Current R2 status is defined by [package 5 acceptance](r2-acceptance.md): managed-production/v1 is complete. Earlier checkpoints below retain their original evidence and scope.

[简体中文](r2-production-composition.zh-CN.md) · [R2 contracts](r2-execution.md) · [State inventory](r2-state-inventory.md)

This package connects the **actual production checkpoints** to complete step
classification over their checked state. It combines the finite managed function,
host-reference and configuration packages. [Package 5](r2-acceptance.md) now provides combined acceptance of this stated carrier; this is not whole-paper completion.

## What the guarantee means

A lifecycle projection can remain unchanged while a service value, revision,
cleanup obligation, callback claim or configuration changes. Such a step cannot
be called an internal stutter of the complete recorded observation.

For every actual native Journal commit, the production interpretation retains
all thirteen record variants and outstanding inverse registrations. It derives
one continuous control trajectory, including the initial empty graph and every
interleaving. Each step is a paper control rule, explicit Restart, exact
whole-record stutter, or an extension with the corresponding checked record law.
An Iter with unchanged control still retains its observable native revision.
Paper labels here describe the control projection; managed function/effect laws
come from [package 1](r2-function-semantics.md), not from erasing value changes.

The Node interpretation similarly covers the complete protocol observation:
lifecycle actions, publication values/revisions/leases, checks, policy, Episodes,
callback scopes, restoration selections, released handles and dynamic interfaces.
It constructs a continuous control history from these actual steps. Dynamic
interfaces and Restart remain explicit extensions. Only an extension-free
control projection enters the strict paper closure.

## How the actual owners are joined

| Production path | Composition and evidence |
| --- | --- |
| `Runtime::execution_snapshot` / `plugin_execution_snapshot` → checked native snapshots | Typed publications, scalar/payload owners, work, cleanup and scope certificates retain the same Journal epoch. `Snapshot::new` and `into_joint` establish the production interpretation; callers do not supply an expected trajectory. |
| Node driver diagnostics → `Driver::execution_snapshot` → `NodeRuntime::snapshot` | The producer establishes `production::interpreted` on its exact protocol history. JSON formatting remains adapter code. |
| Node bridge → `Bridge::{issue, bind_fiber, unbind_fiber, begin_call, finish_call, remove}` | Every successful reference-table mutation appends its exact transition to an erased history. Rejections preserve the owner. Node-dependent guards retain the actual protocol cut they read. |
| `Bridge::snapshot` / `HostSnapshot::production_trace` | Check complete retained-publication/Fiber coverage, pair actual references with the current protocol, and derive real object issuance and pending-ticket claim origins. |
| `Loader::execution_snapshot` → native `configuration_snapshot` | Native, typed configuration and source histories share one captured Journal. Their keys are distinct; every mutation of each key has an indexed typed observation. Every source action resolves to its exact earlier accepted configuration, including same-version refresh/recovery. |
| Real Loader mount/reconstruction → `configuration_allocation` → `Tree::ready` | Every enabled root/group/Child allocation names an actual native Insert with its original parent. Readiness derives complete parent-correct, distinct allocation elaboration. A stale current allocation is still rejected by the existing runtime checks. |

The built-in native group uses the checked empty service program. Its descendants
are real owned registrations with separate Insert/Begin/function/Finish steps.
The planner's complete preorder and parent-returned scope determine their
structure. This is the documented administrative elaboration of groups and
includes; it does not invent one atomic paper effect for the whole Loader
transaction or give arbitrary factory bodies a Component proof.

A bridge operation's protocol cut is the actual NodeRuntime argument read by
that operation. The production driver retains its bridge/core association.
Reference-history order and protocol-history order are preserved separately;
these certificates do not invent a total order across independently created
owners or infer that equal numeric domain IDs prove object identity.

## Paper-to-code review

| Paper connection | Review entry |
| --- | --- |
| Definitions 58/63, complete execution/control steps | [native_production.rs](../crates/cordis-kernel/src/native_production.rs): `production_step`, `production_trace`; [node_production.rs](../crates/cordis-kernel/src/node_production.rs): the same entry points |
| Definition 29 / equation (31), real values and inverse domains | Existing [managed function](r2-function-semantics.md) and typed/scalar operation proofs remain attached to actual receipts; full-record classification retains their pending obligations. |
| Begin, callback dispatch and retained references | [node_bridge_history.rs](../crates/cordis-kernel/src/node_bridge_history.rs): `step`, `object_origin`, `claim_origin`; [node_bridge.rs](../crates/cordis-kernel/src/node_bridge.rs): actual mutators and snapshot |
| Definition 81 and group/Child elaboration | [configuration_runtime.rs](../crates/cordis-kernel/src/configuration_runtime.rs): actual allocation; [native_history.rs](../crates/cordis-kernel/src/native_history.rs): `insertion_origin`; [configuration_tree.rs](../crates/cordis-kernel/src/configuration_tree.rs): `elaboration` |
| Configuration/source transaction composition | [native_configuration.rs](../crates/cordis-kernel/src/native_configuration.rs): `production_trace`, `covered`, `source_reviewed`; [package 3](r2-configuration-semantics.md): actual data, module and source semantics |

## Reproduce and check the boundary

Run the pinned, offline development acceptance once:

```sh
python3 scripts/record-development.py --offline
python3 scripts/record-development.py --check
```

The [development record](development-report.json) binds whole-kernel proof,
Rust/Node regressions, examples and extracted packages to source hashes. A
changed source invalidates the old record. Four added canonical negative controls
check a native/control stutter confusion, the analogous Node error, completion
of a still-pending callback claim, and substitution of an allocation's Insert
origin. Selected negative checks require fresh positives, full mutant compilation
and the exact named failure; they are not the full mutation regression.

Histories and interpretation proofs erase from production Rust. No runtime event
log, old payload retention, callback replay or Verus-TLA dependency is introduced.
The small Node Episode update now has a separate local payload contract, composed
with the full protocol contract, to verify within the existing solver limits.

The verified carrier does **not** contain arbitrary JS/Rust object interiors,
callback computation or user destructors. JSON/URL/IEEE adapters, Node-API/JS/ALS,
ordinary Arc/Mutex execution, wakeups and error-report aggregation, external I/O
and static embedding lease truth retain their explicit boundaries. Their
observable effects are not certified as stutters by this package. Conflicting
named-port aliases retain the documented semantic condition. General recovery,
fair scheduling, global termination and confluence belong to later milestones.

[Package 5](r2-acceptance.md) now freezes and reviews this scope, with real failure/retry paths and strict selected rejection evidence. Its acceptance remains distinct from release and whole-paper completion.
