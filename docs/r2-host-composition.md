# R2 package 2: host and Node composition

Current R2 status is defined by [package 5 acceptance](r2-acceptance.md): managed-production/v1 is complete. Earlier checkpoints below retain their original evidence and scope.

[Package 4](r2-production-composition.md) now adds actual reference-table histories and production protocol classification. The boundary discussion below remains applicable.

[简体中文](r2-host-composition.zh-CN.md) · [R2 contracts](r2-execution.md) · [Paper milestones](paper-refinement-roadmap.md)

This package connects verified lifecycle and service identities to the **actual
references used by the hosts**: Node objects, Fibers and selected callbacks;
Rust shared Episodes; and static typed imports. The executable kernel owns the
reference tables and checks their associations. The production adapters call
those same functions.

The package closes this reference and dispatch association scope. **R2 remains
in progress**: complete configuration semantics, whole-production-step
refinement and final R2 acceptance are separate packages. It does not prove
arbitrary JavaScript or Rust callback bodies.

## What changes for users

- Service reads return the exact object selected by the real committed binding,
  including an invisible publication retained for failed cleanup. A live
  publication, Fiber or callback claim prevents early removal of its reference.
- Setup and cleanup use a retained claim for the real pending lifecycle ticket.
  A different Fiber, stale ticket or duplicate completion cannot finish that
  invocation. An in-flight setup retains its selected callback and configuration
  reference; a later restart selects the new callback.
- Typed Rust imports carry a sealed result from the actual Node lookup. The
  adapter checks runtime, consumer, generation and port before resolving the
  provider's original typed slot. Static assembly checks the complete declared
  and inherited port set and retains the supplied `Arc` values.
- Every ordinary Rust shared-Episode access checks that the locked execution has
  the identity issued with its immutable context. A substituted execution is
  rejected before access.

No user-facing plugin API change is required. The JS facade requires addon
`hostProtocol: 1`; build or install the matching native addon with the package.
Node remains an optional compatibility host for the native Rust library.

## The production connection

| Owner | Real path | Contract |
| --- | --- | --- |
| `Bridge<WeakReference<NativeObject>>` | JS `HostBridge` → Node-API bridge → `issue`, `publish`, `replace`, `resolve`, `remove` | Non-reused IDs within the owner, exact originally issued reference, domain checks and retention checks against the actual publication table. |
| Fiber map and callback claims | `_activate` / `_cleanup` → `beginAction` → `Bridge::begin_call`; `completeAction` → real driver completion → `finish_call` | The bound Fiber and retained recipe share the pending ticket's domain. A claim is retired only after that exact ticket is no longer pending. |
| `HostSnapshot` | `validateHostSnapshot` → `Bridge::snapshot` | Check every retained publication and registered Fiber for a corresponding reference. The paired observation interprets an authentic `Selected` read as a lookup in this actual reference heap. |
| `Selected` | typed request start → `NodeRuntime::select` → `ResolvedImport` → `typed_instance` | The private credential records a real read event and its exact domain, consumer, generation, port, publication and provider. It replaces reconstruction from JSON owner/publication numbers. |
| `static_values::Values<ServiceSlot>` | `StaticPlugin::begin` → `from_definition`; setup read/provide → checked values | Resolve actual realms and inherited ports; reject missing, duplicate or extra imports; preserve exact supplied slots and declaration-bound writes. |
| `host_context::Association` | native/static creation → `SharedEpisode::checked_lock` | Context and execution share the real lifecycle origin and work domain. The runtime checks this relation after acquiring the actual mutex. |

The bridge stores the adapter's real weak Node-API references as its generic
payload; there is no parallel integer-only object model. The small
[JS adapter](../packages/compat-cordis/host-bridge.js) attaches each payload once
to its native box in a private `WeakMap`, and retains live boxes in a private
root map. A native lookup returns the same box. Payload getters and callbacks
are not invoked by table operations. Weak native references avoid a new native
strong-reference cycle through the JS Domain.

`Object.freeze` fixes the recipe's callback/configuration **references**, not
the interiors of user configuration or callback closures. HMR may change the
next selected callback without rewriting the retained recipe of an already
running invocation. This is a dispatch identity guarantee, not a proof of
module loading, arbitrary callback effects or eventual return.

A snapshot is an explicit audit operation. It rejects incomplete coverage rather
than assuming all JS objects exist. It does not introduce a runtime proof log,
run a full table scan on every service read. Package 4 adds inductive histories
for the actual reference mutations and complete checked protocol classification;
arbitrary adapter computation remains outside those histories.

## Paper-to-code review

| Paper obligation | Connection established here | Explicit limit |
| --- | --- | --- |
| Definition 29 / equation (31), service selection | Existing `reads::result` and read-lift contracts select the actual publication. `Selected::interpretation` proves the credential came from that read; `HostSnapshot::selected` connects it to the retained foreign-reference heap. | Reference identity does not interpret mutable JS object interiors. |
| Definition 30, actual function interpretation | The real setup dispatch retains its chosen Fiber, callback and argument reference. Package 1 supplies function/effect laws for supported managed Rust bodies. | General JS callbacks need their own semantic contracts; retaining a function reference does not establish Component membership. |
| Begin / Finish / Unload and committed dependencies | Claims validate the real pending ledger ticket. Completion calls the existing checked lifecycle protocol; retained publications prevent reference removal during blocked or failed cleanup. | JS scheduling, invocation truth and eventual cleanup are not proved by identity checks. |
| Context, declarations and reads/writes | Static assembly resolves the actual definition and imports; native/shared context checks use the execution's real issued identity. | An external static embedding must still supply truthful provider/lease authority. The Node embedding obtains its selection from the checked graph. |

Dynamic interfaces, callback dispatch and HMR remain explicit implementation
extensions. This package does not label them observation-preserving paper steps
merely because lifecycle projection is unchanged. See the
[paper map](paper-refinement-map.md) for the still-partial composition obligation.

Review the executable contracts in
[`node_bridge.rs`](../crates/cordis-kernel/src/node_bridge.rs),
[`node_reads.rs`](../crates/cordis-kernel/src/node_reads.rs),
[`static_values.rs`](../crates/cordis-kernel/src/static_values.rs) and
[`host_context.rs`](../crates/cordis-kernel/src/host_context.rs).
Their callers are the
[driver bridge](../crates/cordis-driver/src/objects.rs),
[Node-API bridge](../crates/cordis-node/src/bridge.rs),
[typed adapter](../crates/cordis-node/src/typed.rs) and
[static host](../crates/cordis/src/runtime/static_host.rs).

## Acceptance and boundaries

[Development evidence](development-report.json) binds the complete unchanged
kernel proof, Rust/Node regressions and package checks to source hashes. Verify
its freshness with `python3 scripts/record-development.py --check`. The runtime
cases cover reference identity, ABA replacement, withdrawal and cleanup retry,
wrong/old dispatches, an actual yielded setup followed by callback replacement,
static realm resolution, and substituted shared executions.

Five canonical negative controls target object substitution, accepting a
non-pending dispatch, releasing a retained object, writing for a foreign static
owner and ignoring the shared execution's domain. A selected check requires a
fresh matching positive, whole-mutant compilation and the exact named contract
failure. Such evidence is distinct from full mutation regression, release
validation and paper-wide completion.

Reproduce the focused runtime scenarios after building the matching addon:

```sh
source scripts/toolchain-env.sh
cargo test --locked --offline -p cordis-kernel --test host_bridge --test static_values
cargo test --locked --offline -p cordis-node --test plugin_runtime
cargo test --locked --offline -p cordis-verus association_tests
node scripts/build-node.mjs --offline
node --test --test-timeout=30000 tests/node-compat/host-bridge.test.mjs
```

For complete development acceptance, run
`python3 scripts/record-development.py --offline` instead of manually repeating
its underlying workflow. Full negative regression runs independently with
`python3 scripts/check-negative.py`.

The audited/trusted boundary still includes Node-API reference dereferencing,
the JS engine and private box adapter, standard `Arc`/`Mutex` semantics,
TypeId/namespace translation, opaque callback and payload interiors, panic/I/O
truth, scheduling and external static-host leases. Native assembly and the
runtime association check reduce the ordinary adapter's obligations; they do
not verify those external runtimes. Independent native Journals and Node
instances retain independent histories.
