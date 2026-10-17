# R2 production-execution acceptance

[简体中文](r2-acceptance.zh-CN.md) · [Milestones](paper-refinement-roadmap.md) · [Source map](paper-refinement-map.md)

R2 is complete for **managed-production/v1**: the stated executable managed
function carrier and the native, Node reference/protocol, and configuration
extensions. Package 5 assembles the semantic review and reproducible acceptance
of packages 1–4. It does not change any of R2's three original exit criteria or
the original paper audit. The completion scope is explicit, as it is for R1.

## What has been accepted

| Original R2 criterion | Execution and proof | Concrete acceptance |
| --- | --- | --- |
| Actual argument, outcome, continuation and inverse provenance at managed entry points | `Plugin::native_function` → `NativeRuntime::run_managed_root` → `Execution::run_function`; `Step::interpretation`, `Report::interpret_queue`, registered `execution_interval` | A schema default becomes the actual Child argument; mixed scalar/typed effects execute, their real result selects the continuation, a later conflict blocks the retained inverse, and recovery restores the original input. Mutations omit real return witnesses and discard the selected continuation. |
| Compose admission, invocation, concurrent landing, drain and release without expected-result inputs | Native owner/Journal and `configuration_snapshot`; NodeRuntime and actual Bridge claims with `HostSnapshot::production_trace`; existing issue/read/restore/acknowledge contracts | Loader failure and recovery preserve the committed tree, stale Episode access rejects, provider release waits for the consumer, and retry/reconstruction produces new identities. Node failure retains the actual replacement object and dependencies, then rejects the old completion while a fresh retry is pending. |
| Every implementation step has its appropriate relation | `native_production::classified` and `production_trace`; `node_production::classified` and `production_trace`; bridge exact transitions and configuration/source projections | Every accepted snapshot comes from the real production owner. Mutations confuse a control stutter with full-observation equality, finish a still-pending claim, or replace an authentic Insert position. Exact contract rejection is required. |

The [machine-readable review](paper-refinement-plan.json) assigns each of the six
R2 work items to exactly one original criterion and names the executable/proof
entry points. The inventory checker checks references and scope consistency;
it is **not** a substitute for Verus or a semantic audit. No new theorem count
is manufactured by this acceptance package: it consumes the established
production contracts and adds executable integration evidence.

## Two real execution paths

The [native example](../crates/cordis/examples/r2_production.rs) runs one real
Loader/Runtime with a source file, a group and a managed Child. Its eight checked
stages are load, blocked cleanup, retained provider, drained inverse, reconstructed
configuration, changed argument, saved source, and final release. It captures the
actual joint production snapshot at each stage. A second writer creates a real
typed conflict; it is explicitly retired because a service dependency is not an
ownership relation. Failure prevents saving a pending configuration. Recovery
reconstructs fresh root/Child registrations; a later update changes the scalar
result from 13 to 15, and final cleanup restores 10. The source save is read back
and a second save is unchanged. There is no mock state machine or manufactured
expected execution passed into the kernel.

```sh
cargo run -p cordis-verus --example r2_production --locked --offline
```

The [Node case](../tests/node-compat/r2-acceptance.test.mjs) uses the real addon,
Driver and HostBridge. It creates a dynamically published JS object, binds a real
Child consumer, replaces the object, fails consumer cleanup and keeps the actual
replacement available. A fresh retry rejects the previous completion without
changing the current snapshot. Only successful consumer completion permits
provider cleanup. Reference/protocol snapshots are validated throughout. This
path tests the adapter and proves the kernel contracts it calls; it does not
prove what an arbitrary JavaScript callback computes.

```sh
node scripts/build-node.mjs --offline
node --test --test-timeout=30000 tests/node-compat/r2-acceptance.test.mjs
```

## Reproduce the combined evidence

Use the pinned toolchain and cached dependencies:

```sh
python3 scripts/check-r2-acceptance.py --offline
python3 scripts/check-r2-acceptance.py --check
```

The first command starts with 12 fixed canonical negative controls covering all
three criteria, so stale diagnostic expectations surface before the expensive
integration workflow. Each uses a fresh matching positive, a complete mutant
compilation, and the precise named failing function/diagnostic/source anchor.
It then runs `record-development.py --offline` exactly once: whole-kernel proof,
Rust/Node tests, all examples and extracted/installed packages, including both
production scenarios in the actual log. Acceptance requires both stages on the
same unchanged source. Timeouts, resource exhaustion and compilation errors are
failures of the check, not successful negative evidence. Premature cleanup
acknowledgement must reject in both success and failure branches; a failed branch
is not silently omitted because the solver happened to report another first.

The report is `target/r2-acceptance/report.json`. Fresh baselines, mutants,
compilation artifacts and raw verifier logs remain in a unique evidence directory
under `target/r2-acceptance/`, including on failure. It binds all source inputs,
the development record/log, tool artifacts, selected cases and outputs. `--check`
revalidates them without running proofs; it cannot refresh stale evidence.
The tracked [development record](development-report.json) is the complementary
source-bound evidence. A clean checkout must run the command to create its local
R2 report; the milestone label alone is not a passing report.

These are selected checks, **not** the complete 318-case negative regression or
its calibration. Reports explicitly retain `fullNegativeControls: not_run`,
`scopedCalibration: not_run`, `releaseAcceptance: false` and `paperCompletion: false`.

## Semantic boundaries and the next milestones

The full carrier here includes finite stored root/Child functions, verified scalar
effects and typed replacement, all native Journal records/pending inverses, exact
owner/Episode/work and cleanup protocols, typed configuration/source histories,
Node protocol state and actual bridge reference identity. Ghost histories erase;
acceptance adds no runtime logging or user dependency.

- Arbitrary callback computation, mutable `T`/JS interiors and unverified effect
  implementations have no effect-correctness theorem. They must supply their own
  verified laws before joining the managed interpreter. Their ambient effects
  are not called observation-preserving internal steps.
- Allocation semantics includes shared aliases. The literal named-port Component
  specialization needs its explicit footprint/singleton-alias conditions. Dynamic
  resolution is not assumed constant and conflicting aliases are not independent.
- Restart, multiversion publication, dynamic interfaces and configuration are
  explicitly specified extensions. Strict paper control closure is conditional
  on the relevant projection containing only paper/internal labels. Function
  effects and their inverse interpretation remain separately linked to actual
  calls and receipts; a control projection alone does not prove them.
- Owners with one actual Journal share its order. Independent Journals and Node
  reference/protocol histories keep their own order and real guard cuts. Numeric
  domain equality is not a proof of shared instance identity.
- Ordinary adapter synchronization, Node-API/JS/ALS and weak-reference truth,
  JSON/URL/IEEE conversion, error aggregation, scheduler behavior, external static
  leases and filesystem durability retain explicit environment/implementation
  boundaries. Runtime demonstrations exercise them without promoting them to
  formal proofs. Group/include elaboration is a sequence of owned registrations,
  not an atomic paper Component or a theorem about arbitrary factory bodies.

These boundaries are the existing R1 and packages 1–4 conditions, not newly
assumed missing inverse laws or an assumed correct execution history. The actual
managed interpreter, exact mutations, producer histories and provenance laws are
proved. General recovery over arbitrary allowed interleavings belongs to R3;
maximal progress, scheduling assumptions, termination and confluence belong to
R4. R5 still requires the original whole-paper audit and release/platform review.
Original refutations and all four integration audit statuses remain unchanged.
