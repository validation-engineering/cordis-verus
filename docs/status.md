# Current status — 2026-10-08

This is an experimental development checkpoint for the public
[validation-engineering/cordis-verus](https://github.com/validation-engineering/cordis-verus) repository.
It is not a published crate, a production-readiness claim, or a completed
refinement of the entire paper.

## Verified checkpoint

The [development report](development-report.json) records the current whole-kernel
verification count and workspace test counts, bound to their exact source hashes.
The workflow uses `--no-cheating --compile` on the official Verus rolling release
`0.2026.10.04.1687598` and Rust `1.98.1`, and checks formatting and Clippy.
These are verification obligations and tests, not a count of paper theorems.
The behavior tests include 8,232 bounded lifecycle traces.

The source-bound [development report](development-report.json) records the fresh
checks for the prepared repository, including isolated package tests and builds.
Its schema differs from the [full release report](verification-report.json).
`python3 scripts/record-development.py --check` checks freshness, not new proofs.
Raw development logs and crate artifacts stay in `target/`.

The toolchain was checked against official release metadata on 2026-10-04.
This rolling release is pinned to `168759867f8c4ba0be848f5a3e438c75cee3e6e3`,
including a matching source checkout and three platform archive checksums.
The observed main branch was ahead at `fc7d32e1d9917d31dda119e5742286b10c0ffcd6`;
the project uses the published binary identified above. Cordis main still matched
the locked `f8ea3cd50f1a5724e8e715995bcde131c9c12b2c` revision.

The maintenance changes represent driver transitions and root setup ownership
with enums, unregister cancelled effect-join waiters, and share polling and
loader bookkeeping helpers. Started setup/effect futures remain owned by the
runtime until landing, and inverses are collected before cancellation cleanup.
Host regression tests cover these behaviors; they are not new async proofs.

The host compatibility work adds dynamic service child providers with explicit
owner lifetime dependencies, shared provider payload slots and consumer-specific
availability checks. Loader supports opt-in reversible configuration updates;
external executable plugins use bounded JSON-RPC with code snapshots for rollback.
These are host behavior changes, not new kernel theorems or TypeScript plugin
compatibility. See [runtime](runtime.md), [loader](loader.md), and
[process plugins](process-plugins.md) for the operational boundaries.

## Local performance checkpoint

Native distribution builds now use optimization level 3 while retaining debug
assertions and overflow checks. The driver filters impossible phases before
resolving readiness, and the facade reuses a confirmed quiescent pump until any
potential mutation or failure. Repeated settled reads no longer scan the whole
graph. Source-bound local measurements and their limited scope are documented in
[benchmarks](benchmarks.md); lifecycle correctness and paper completion claims
remain unchanged.

The shared Node Driver also performs periodic verified binding/declaration history
filtering. The finite 1,000-cycle resident measurements record live resources,
identity/publication/lease histories, memory and latency before and after this
change. Released lease records are now removed while their logical IDs remain monotonic;
node and publication histories still grow. Three paired 1,000-cycle native
checkpoint measurements reduced physically stored lease records from 5,005 to 5,
then zero at shutdown, with p95 around 5.5 ms on both builds. See the
[lease reclamation evidence](benchmarks.md#2026-10-06-lease-record-reclamation).
These are record counts, not a constant memory claim or long-running production
acceptance.

## Native Node compatibility slice

The new `cordis-driver`, Node-API binding and JS facade run a tested subset of
original Cordis plugins. Service values remain in JavaScript; Rust selects
lifecycle actions. A verified PublicationRegistry tracks revocation and cleanup
leases independently of logical provider identity. Rust Runtime and Node now share LifecycleDriver control and a verified action ledger;
backend values and journals remain separate. Service checks, two profiles, JSON
Incremental Loader transactions, owned tasks and Worker artifact recovery have executable
regressions. A shared domain mutation queue now orders multiple JSON Loaders, direct Fiber revisions and final
Context shutdown. Scoped lifecycle steps cannot escape into plugin continuations, failed cleanup
blocks new revisions, and accepted work drains before close. An opt-in official Loader adapter now coordinates create/update/remove, old/new
Fibers and actual Include persistence queues, with stale-owner generation checks.
The official host installer now wraps ConfigEditor admission before file locking,
write/reconcile/rollback, Include refresh and the HMR operation queue. The
companion Harness boot installs these bridges for its default UI. Ordinary event
callbacks cannot borrow transaction steps, and readiness reports a retained native
cleanup failure instead of waiting forever. The [official module adapter](official-config-transactions.md) coordinates supported
in-place replacements with real cleanup before cache changes and explicit recovery
after candidate failure. [Observed module graphs](module-graph-reloads.md) also
support full Worker replacement and retained-artifact recovery.
`ProcessDomain` supplies a real OS-process boundary for application native addons,
with accepted-call drain, cleanup acknowledgement plus normal exit, and restoration
from retained artifacts after candidate failure. The companion Harness provides
an opt-in Web/standard supervisor and file-change polling. Existing paper
completion counts are unchanged.

The [Rust factory SDK](rust-node-plugins.md) adds same-graph JSON services,
pull streams, explicit opaque object/callback adapters and event-driven Futures
through user-compiled addons. Objects and callbacks are acquired through declared
factory methods; arguments and results remain JSON. They are not arbitrary handles
or closures embedded in DTOs.

The [native module SDK](native-rust-modules.md) adds independent Rust `cdylib` plugins to the resident Node Driver through C ABI v1. Immutable factory references, synchronous/asynchronous JSON services, cooperative cancellation, actual cleanup barriers and candidate-failure recovery support same-process code replacement. The ABI also supports declared reverse JS JSON calls, streams and object interfaces in both directions, and explicit JS callbacks, with action-scoped acquisition, real operation drain and retryable close. It retains code images and exposes resource diagnostics and a per-addon image limit. Owned children and dynamically published factories use the same lifecycle graph; arbitrary Rust typed slots are not shared across the ABI. Opt-in versioned JSON checkpoints migrate declared logical state after drain and support recovery through consumer acceptance. This does not physically unload images or prove native callbacks.

The [typed adapter](typed-rust-plugins.md) executes real `cordis::Plugin` definitions
in the Node graph. It retains original slots and per-Fiber FnMut state, with
explicit opt-in for `provide_checked`, `set` and `refresh` on declared services.
Availability uses real pending CheckTickets and consumer injection configuration.
Fixed-per-factory `requires_with_config` declarations now apply while Pending and
are checked against the original Plugin before setup, including explicit JSON null.
An explicit dynamic service catalog also enables original publication handles
and owned child plugins in the same native graph, preserving owner anchors,
exact inherited dependency ports and original slots. Effect groups, configuration
update hooks and other remaining typed Runtime operations are still outside this adapter.
Explicit `FnMut` cleanup factories now retain failed work for a fresh host attempt;
Runtime and static typed episodes use the verified `CleanupJournal` to reject stale
receipts and retain selected tokens. Legacy static `FnOnce` cleanup failure stays
permanent instead of accepting an empty retry. The verified `CleanupQueue<T>` now
owns the actual callback payload vector with that journal, proving exact slot
movement, single issuance, retention of supplied retry values, unchanged rejected
inputs and absence of stored or issued work when empty. Executor factory choice
and callback effects remain tested host integration; these changes do not complete
the paper proof.

Borrowed object release drops an adapter reference; owned release waits for its
explicit cleanup and retains failed work for retry. Ordinary JS inverses must all
succeed before the consumer's object LIFO phase and its own Rust session teardown.
This preserves handles and instances for failed-inverse retry. Reverse `JsObject`,
`JsCallback` and `JsStream` capabilities are action-scoped, including clones. Explicit
Rust close reports `ObjectBusy`/`StreamBusy` for pending method/pull work; automatic
journals still drain real completion, with stream return issued before joining next.
These ownership and reentrancy rules have host regression coverage, not new paper
completion claims.
Native manifests now bind the selected platform artifact to its bytes and build
inputs; local bundle assembly preserves actual host evidence. Declared platform
targets are not a claim that every remote build has passed.
See the [Node guide](node-compatibility.md) for commands and remaining M0–M7 work.
The source-bound development report separately records native build and Node
behavioral tests. Optional locked-upstream differential tests are separate evidence
in `target/node-compat/differential.json`; the default CI does not run that suite.
None of these records proves arbitrary JS callbacks or complete profile compatibility.

The [performance tools](benchmarks.md) provide source/build-bound measurements,
raw batch samples and explicit baseline comparison. Three independent local
1,000-cycle native checkpoint replacement runs establish a reproducible baseline
with actual migrated values and resource observations. The fixed two-image workload
does not establish production budgets, prolonged application stability or platform
acceptance; those require separate workloads and execution evidence.

Remaining integration work includes the other typed Runtime operations, broader
interface and ABI contracts, more Cordis/Harness ecosystem and module-boundary
coverage, broader supervisor/CLI coverage, actual platform acceptance and
host-to-paper refinement. The full long-term
architecture and release gate remain incomplete.

## Paper coverage

The machine-readable [ledger](paper-obligations.json) is the source of truth.
The generated [coverage table](paper-coverage.md) links each item to contracts.

| Status | Numbered items | Meaning |
| --- | ---: | --- |
| `formalized` | 42 | Definition encoded, sometimes under a supplied interpretation |
| `proved` | 17 | Claim proved within its recorded scope and contract |
| `partial` | 18 | Some cases or bridges remain open |
| `refuted` | 4 | An original claim has a mechanically checked counterexample |
| **Total** | **81** | Counts are not a paper-completion percentage |

Four integration obligations remain open: whole lifecycle, reconciliation of
original and corrected statements, executable simulation, and host behavior.
A conditional Component definition does not construct recursive Γ or establish
that every runtime callback implements it.

Original Lemmas 62, 75 and 77, and the unconditional completion clause of
Theorem 71, have counterexamples. Original Child-related 78/79/80 remain partial:
encoded-rule obstructions do not instantiate every original total-context and
Component premise. See the [paper audit](paper-audit.md).

## Latest proof additions

- Typed Component and instantiation interfaces preserve per-key fibers, actual
  fresh identity and the captured child's retirement inverse.
- Restricted deletion composes foreign Unit/Operation/Provision/Child landings,
  mixed Table/Child journals and dynamic Insert/Remove. It constructs surviving
  executions and terminal recovery. Owner Child, private-provision consumers
  and unrestricted schedules remain outside this theorem.
- Strict function-field refinement retains real `None`/`Some` domains and
  permits different continuation identities and receipt lengths on its legal
  comparison domain.
- Historical independence includes internal children, removed entries and
  reused names. The total interpretation/strict implementation bridge remains open.

## Validation still open

There are **118 canonical negative mutations**. A complete full-crate negative
run for this source has not passed. The earlier 1,927-obligation snapshot's
full quality run stopped on `mixed-removal-ignores-retention` after a timeout.
Partial contract diagnostics were not accepted as a passed result.

The opt-in scoped-negative checker and candidate selector manifest are
experimental. Unit tests and selected probes do not establish a completed
118-control calibration and do not replace the full release gate. The first
full candidate calibration accepted 11 controls, then rejected control 12
(`begin-reuses-episode-generation`) because its real assertion failure was
accompanied by an SMT resource-limit failure. The run is **failed**, not a
completed calibration; its partial results are not release evidence.
See [validation](validation.md) for commands and evidence boundaries.

The local environment is macOS ARM64. Hosted Linux/macOS results must be checked
on the repository's Actions page after the push; configuration alone is not
cross-platform evidence. No crates.io upload or public release is part of this
checkpoint. Unfinished proof experiments are excluded. Next work and acceptance
criteria are in the [roadmap](roadmap.md).
