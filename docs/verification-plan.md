# Paper-to-code verification plan

English · [简体中文](verification-plan.zh-CN.md) · [Update recovery case](cases/update-recovery.md) · [Remaining paper obligations](paper-mapping-inventory.md)

**Updated: 2026-10-24.** Work continues on `main`; the fixed pre-refactor archive
is `codex/archive-before-refactor-2026-10-24` at `60bdd89`. The bounded iteration's
code, ownership map, module layout, generator, reducer, upstream comparison and
paired-control runner are implemented. The final-source gate is
`python3 -B scripts/check-lifecycle-campaign.py accept`; only a passing record for
the current sources constitutes integrated acceptance. See the
[review map](review-map.md) and [reproduction guide](cases/generated-lifecycle.md).
The whole-paper target remains open.

The goal is to make paper constraints useful in running software: a plugin author
can update a provider, understand a blocked cleanup, retry safely and inspect the
contract behind that behavior. The first delivery remains
`provider-consumer-one-child/v1`: one provider, one consumer and one level of Child,
with managed reversible data, explicit dependencies and fallible cleanup.
R01 and the complete paper-to-code mapping remain long-term commitments.

## Two complementary checks

The [Anthropic article](https://www.anthropic.com/research/formal-verification)
reports a Rust/Verus Python interpreter and 99.95% agreement with CPython over
more than 1.7 million generated programs. Its
[technical appendix](https://www-cdn.anthropic.com/files/4zrzovbb/website/6867eadf760258fa8b42a504600cd3c036d16358.pdf)
distinguishes the proof against formal semantics from empirical CPython agreement;
the stated interpreter theorem concerns results when execution returns. It also
reports that all seven injected bugs broke proofs, while five survived the random
tests. These are reported experiments, not independently reproduced results here.

We adopt the separation of evidence, without importing their coverage numbers or
termination claims into this project:

```mermaid
flowchart TD
    Paper["Cordis paper and explicit corrections"] -->|"Interpretation review"| Spec["Formal definitions and contracts"]
    Code["Executable Verus kernel"] -->|"Machine-checked contracts and refinement"| Spec
    Host["Actual Rust / optional Node callers"] -->|"Checked protocol calls; opaque host boundary remains"| Code
    Host <-->|"Shared scenarios and declared observations"| Upstream["Pinned Cordis reference implementation"]
```

The diagram assigns evidence roles; each connection needs its own scoped evidence.
Verus checks the stated contracts of the kernel source also compiled by Cargo.
Review must still establish that our definitions represent the intended paper
clauses. Integration and differential tests check real callers and compatibility;
they do not prove arbitrary callbacks, FFI or external I/O. Compiler, verifier,
library and host assumptions remain in the [architecture boundary](architecture.md).

The paper, upstream implementation and revised failure policy can disagree.
Keep paper counterexamples and intentional implementation differences visible.
Agreement rates measure a specified generated distribution, not proof coverage
or the probability that an application is correct.

## Reuse the existing foundation

| Existing entry point | What it already supplies | Extension planned here |
| --- | --- | --- |
| [Update recovery case](cases/update-recovery.md) and [reproducer](../scripts/reproduce-update-recovery.py) | Actual native and ordinary Rust host paths, managed inverse failure, retained dependencies, explicit retry and source-bound proof selection | More generated histories around the same user guarantee |
| [Node differential runner](../scripts/check-node-compat.mjs) and [shared fixture](../tests/compat/differential-fixture.mjs) | Fixed scenarios against a pinned upstream, source/artifact hashes and exact observation comparison | A separate versioned scenario/observation format for generated cases; preserve existing exact fixtures |
| [Five update-recovery controls](../scripts/negative-controls.update-recovery.json) | Mutations of real implementations with strict proof rejection criteria | Execute the same mutations against relevant behavioral tests as well |
| [Admission contracts](progress-contracts.md) | Exact success conditions for selected real APIs | Check useful acceptance alongside rejection, so an always-reject implementation cannot pass the intended guarantee |
| [Paper inventory](paper-mapping-inventory.md) | Stable remaining obligations and their dependencies | Attach new evidence to existing units without declaring a bounded result to close a general obligation |

The new plan is the current bounded iteration under A07/A08/A13/A15 and F1/F4 in
the [adoption plan](adoption-plan.md). It does not introduce another R-series
milestone or replace the original ledger and its closure criteria.

## Guarantees to deliver and review

Each guarantee needs a paper clause or explicit implementation extension, an
actual call path, its complete contract and premises, fresh proof evidence, a
nonempty success/failure example and an appropriate negative control.

| User guarantee | Paper connection | Actual path and required evidence |
| --- | --- | --- |
| An old provider remains protected while its dependent cleanup is unresolved | Definition 54 and guarded L-Unload; current targets and episode-committed providers remain distinct under Definition 53 | `Kernel::begin_cleanup`, `LifecycleState` and `cleanup::update::failed_child_keeps_chain`; observe committed identities through failed cleanup and retry |
| Failed managed restoration retains the inverse and its payload | Witnessed effects and strict inverse domains; the domain restriction is the explicit R1-DOMAIN interpretation | `Inverse::restore_following`, `CleanupQueue` and `NativeRuntime::fail_managed_execution`; check both value and inverse depth, not an empty queue alone |
| Old or duplicate replies cannot finish a new cleanup attempt | Generation/ticket protocol is an implementation mechanism enforcing lifecycle order, not a separate numbered paper theorem | Actual action/restore tickets, `retry_execution` and receipt validation; cover retries and a new episode |
| A Child inverse retires its own Child and release follows real service dependencies | Definition 52 and Definition 54 | Atomic Child request/inverse creation, recorded parent episode, retirement and Unload; ownership alone does not establish a service dependency |
| A supported update can succeed after its failure cause is removed | Local admission and actual inverse contracts; scoped recovery evidence relevant to Theorems 68–70 | Real update, restore, retry and release calls; successful setup/release plus precise blocked outcomes, without claiming the complete recovery equation or global progress |

Failures caused by deliberately interfering raw resource access belong in a
separate test category. They check detection and retention, not the exclusion of
all environmental interference. Ordinary consumed `FnOnce` cleanup with `Drained`
must not be counted as successfully restored managed data.

Termination is a separate conclusion. Theorem 73 concerns its finite/bounded,
lifecycle-only model under its stated hypotheses. A host timeout is not a proof
that the abstract rules deadlock, and a successful finite test does not prove
that every Future, JavaScript callback or scheduler eventually completes.

## Architecture direction

Keep a shared verified lifecycle protocol and give each host a precise bridge.
`NativeRuntime` and `NodeRuntime` are verified Rust state owners; their names do
not mean that the kernel contains two language engines. Their different data,
publication and invocation responsibilities still require separate contracts.

| Layer | Responsibility and maintenance direction |
| --- | --- |
| Shared verified protocol | Keep committed bindings, generations, cleanup receipts, failure retention and release authority together. Reuse common contracts and preservation lemmas where their premises really coincide. |
| Native verified owner | Own managed values, retained inverse payloads and root/Child histories; establish the Native premises of the shared protocol from actual mutations. |
| Node verified owner | Own the represented publication, handle and invocation state; establish the Node premises separately. JS object contents and callback effects remain explicit boundaries. |
| Ordinary host and compatibility code | Execute callbacks, Futures and I/O, maintain transport/FFI associations and exercise real error handling. Tests validate these paths; forwarding to a proved function is not itself a proof of the wrapper. |
| Harness application | Own official workflow and application-specific Loader/HMR integration; consume runtime APIs without becoming a kernel dependency. |

Current source paths are Rust `Runtime` → shared `NativeDriver` → `NativeRuntime`
and Node facade → N-API adapter → `Driver` / `NodeDriver` → `NodeRuntime`.
Both connect to the shared lifecycle state. See the
[native owner](../crates/cordis-kernel/src/lifecycle_state/native/runtime.rs),
[Node owner](../crates/cordis-kernel/src/node_runtime.rs) and
[shared lifecycle state](../crates/cordis-kernel/src/lifecycle_state.rs).
Pure Rust use continues to require no Node runtime. Structural work should first
improve ownership and navigation within the existing crates; adding crates,
hosts or a temporal library is not a prerequisite for this iteration.

## Structure and removal are part of the delivery

The project should express one clear chain: useful behavior → actual implementation
→ explicit contract → proof and reproducible evidence. Accumulated experiments,
repeated wrappers and chronological progress notes should not obscure that chain.
Reorganization starts before the next feature expansion, rather than waiting for
the final acceptance step. The existing case and regressions provide the initial
behavioral baseline; generated campaigns add coverage afterward.

The archived kernel has 446 source files, all directly under `src/`. The ordinary
Rust host's `runtime.rs` has 5,195 lines. These counts include contracts, proofs,
comments and tests; they identify navigation problems, not proof redundancy.

### Target organization

Keep the current crate boundaries initially. Within each crate, group files by
state ownership and responsibility rather than the iteration that introduced them.
The table describes the target; the completed structural batches below identify
which parts are already in place:

| Area | Intended organization | Review question |
| --- | --- | --- |
| `cordis-kernel` lifecycle | Control state, committed bindings, actions and cleanup in one discoverable domain | Who may advance or release this episode, and which checked call enforces it? |
| `cordis-kernel` effects | Managed values, inverse payloads, journals and resource ownership | Which actual mutation produced this inverse, and what survives failure? |
| `cordis-kernel` host state | Separate Native and Node state-owner domains using shared protocol contracts | Which host-specific premise is established here rather than assumed? |
| `cordis-kernel` semantics and refinement | Paper definitions, actual implementation bridges and reusable lemmas with clear direction of dependency | Is this an original statement, revised contract, conditional theorem or connected production guarantee? |
| `cordis-driver` | Shared scheduling policy and Native/Node adapters with matching physical and logical module paths | Where does ordinary Rust enter the verified owner? |
| `cordis::runtime` | Separate service access, setup, cleanup and polling responsibilities; keep public exports deliberate | Can a reviewer trace one update without reading an unrelated subsystem? |
| Node and optional plugin integration | Keep FFI, transport, compatibility policy and application adapters outside shared kernel authority | What requires Node, a foreign process or an application-specific policy? |
| Documentation and checks | Short task-based entry points; current contracts/cases first, detailed research separately; one authoritative command for each acceptance scope | Which source, proof and reproduction support this advertised claim? |

Executable functions retain their directly attached contracts. Moving a proof to
a different domain must not create an unchecked implementation copy or an assumed
bridge. General paper proofs needed by production contracts stay in the dependency
closure. A research-only crate/directory is an option only after that closure is
known and its explicit verification entry point is preserved. Merely being ghost
code or lacking a runtime caller is not a reason to remove a proof.

### Keep, consolidate, separate or remove

| Material | Default decision | Evidence required before removal from `main` |
| --- | --- | --- |
| Production state, guards and direct proof bridges | Keep; clarify ownership and API | An equivalent replacement and migrated callers, with the same required guarantees |
| Repeated wrappers, state projections and helper lemmas | Consolidate around one implementation/contract | Compare premises, outcomes and state frames; migrate runtime, proof and test callers |
| Exploratory models and superseded replay variants | Classify separately; retain useful research | Check dependency closure, ledger references and unique counterexamples; retain an active verification target for still-claimed results |
| Chronological progress prose and repeated module lists | Replace with current contracts and a focused research index | Preserve unique conclusions, unresolved obligations, paper corrections and source-bound evidence links |
| Duplicate scripts, fixtures and obsolete experimental API aliases | Merge or remove when their role is covered | Preserve distinct failure cases, observation semantics and strict acceptance; update commands, CI and package inputs |
| Frozen reports, refutations and unfavorable comparisons | Preserve as evidence with their original scope | Never rewrite a historical pass to match a new tree or delete a failure to improve apparent coverage |

For each removal, the change description records the old path, its purpose,
remaining callers/references, replacement or archive location, any supported-scope
change and the checks run. Search references and inspect semantic differences;
unused-code output alone is insufficient. We do not retain experimental aliases
solely to preserve the old layout. Public feature changes require updated support
and migration documentation. No deletion may silently turn an open paper obligation
into a completed one or weaken a current guarantee.

### Completed structural batches

| Previous organization / purpose | Current location or replacement | Scope and review |
| --- | --- | --- |
| Driver `src/native.rs`, the existing shared Native adapter | `crates/cordis-driver/src/shared/native.rs` | Same `shared::native` API and implementation; no compatibility shim |
| 41 flat kernel files reached through `#[path]`, including `native_runtime.rs`, `cleanup_protocol.rs` and `cleanup_completion.rs` | `src/lifecycle_state/`, `src/lifecycle_actions/` and `src/cleanup_queue/` under `cordis-kernel`; each file follows its existing logical module name | Module identities, executable/proof bodies and contracts preserved; source links, review bindings and strict negative diagnostic paths migrated |
| Seven cleanup/receipt/effect-poll methods in the ordinary host's `runtime.rs` | `crates/cordis/src/runtime/cleanup.rs` | Method bodies, lock/drop ordering and failure policy preserved; internal access only |
| 15 script entry points selecting the same strict negative runner | `python3 scripts/check-profile-controls.py PROFILE` | Same fixed profile selections, fresh positives, compiling mutants and exact proof rejection; full and R2 validation scopes remain separate |

`python3 scripts/check-profile-controls.py --help` lists the profiles.
`python3 scripts/check-profile-controls.py update-recovery --check` checks the
selection and current source anchors only; it does **not** run proofs or create a
passing evidence report. Omitting `--check` runs that profile's strict checks.
The [development record](development-report.json) identifies its own checked
source; moving a file does not refresh an old pass. The original files and
superseded wrappers remain in the fixed archive. No unique theorem, counterexample
or evidence record was removed, and no paper obligation was closed by these moves.

The second layout batch moves 212 further kernel files to their existing logical
module paths and removes the remaining 214 path attributes. Setup, service-handle
methods and polling now have separate ordinary-host modules; `runtime.rs` is
3,139 lines. Function bodies and contracts are preserved. The
[review map](review-map.md) records the ownership classification and disposition;
unique research results and frozen evidence remain retained.

The [generated lifecycle case](cases/generated-lifecycle.md) is the implementation
and reproduction entry for steps 3–6 below. It records intentional cleanup-policy
differences without calling them upstream agreement.

### Archive and branch discipline

The archive is a local Git branch at the frozen snapshot above. Keep it fixed;
continue new commits on `main` without rewriting the archived history. It includes
tracked source and the prior plan, not ignored toolchains, upstream checkouts or
`target` artifacts. Those inputs retain their locks and reproduction instructions.
Branch creation does not publish a release or refresh verification evidence.

Review old paths with `git show codex/archive-before-refactor-2026-10-24:<path>`.
After committing a batch, compare it with the archive using
`git diff codex/archive-before-refactor-2026-10-24..main`.
Remote synchronization is separate from this local archive.

## Work sequence and exit criteria

The bounded deliverables below have implementation and review entry points. Acceptance
is source-bound: the final audit requires fresh development, scenario, comparison
and paired-control records together. Dependencies do not require full-suite runs
after each edit; these items do not introduce another paper milestone taxonomy.

| Order / state | Deliverable | Dependency | Exit criterion |
| --- | --- | --- | --- |
| 0. Archive · complete | Frozen code and prior plan on the named branch; active work stays on `main` | Existing working tree | Archive resolves to `60bdd89`; tracked work is preserved and history is not rewritten |
| 1. Scope and ownership · implemented | Contract/evidence matrix plus production/proof/research inventory and candidate removal decisions | Archive and existing case | Every guarantee has a real caller, exact observation and premise; every proposed removal has an accountable replacement or disposition |
| 2. Structure and cleanup · implemented | Organize one domain at a time; consolidate repeated code and prose; separate research navigation | 1 for the affected domain; existing regressions | Clear ownership, no lost proof/negative anchors, migrated callers and packaging; preserved guarantees or an explicit scope change |
| 3. Generate and shrink · implemented | Seeded real Native lifecycle scenarios and reducer | 1 and the relevant stable interfaces from 2 | Existing failure/retry reproduced, required families covered and replayable reduced failures demonstrated with a known control |
| 4. Compare with Cordis · implemented | Node/native and pinned-upstream adapters for the supported common scenario subset | 1; reuse 3's format/reducer | Raw traces, complete outcome accounting and no unexplained difference accepted as compatibility |
| 5. Test/proof detection · implemented | Paired behavioral and proof results for the five existing implementation mutations | 3; 4 where a control exercises Node | Fresh baseline, valid mutant compilation, intended contract rejection and separately recorded behavioral result |
| 6. Integrated review · final-source gate | Final contract, source, scenario, mutation and architecture evidence | 1–5 | One final source passes the applicable concentrated acceptance; reviewers can reconstruct the full guarantee chain |

### Generated scenarios

Start with the existing provider/consumer/one-Child shape. Vary supported
registration/setup order, provider replacement, cleanup failure position,
interfering writes, explicit retry, stale/duplicate replies and final shutdown.
Include successful updates without failure and an update after recovery.
Add aliases and controlled asynchronous completion only after the corresponding
access and scheduling boundaries are explicit; these are extensions, not implicit
coverage of the first profile.

The runner must drive actual APIs and observe actual resources. A generator's
model may choose commands but must not manufacture the production history or
stand in for the executor. Separate well-formed admitted scenarios from deliberate
invalid-command/interference scenarios. Record rejection and unsupported cases
rather than silently filtering them out.

Store the seed, generator version, complete command sequence, input parameters,
explicit completion schedule where applicable, observation format and runtime
versions. Shrinking must preserve the failure predicate and necessary ownership,
dependency and fault setup. Save the reduced commands so reproduction does not
depend solely on an RNG seed or the latest generator version.

Required observations include API outcomes, target/committed provider identity,
owner/episode/attempt identity, publication visibility, cleanup/retry decisions,
retained resources and relevant causal ordering. Compare intermediate states as
well as endpoints. Reject a run that misses required scenario families or valid
successful operations, even if all generated rejections look safe.

### Compatibility accounting

The Node adapter is a separate host acceptance surface. It cannot inherit the
Native managed-data theorem merely by consuming the same scenario description.
Publish its supported subset and bridge premises. If an operation has no equivalent
public upstream API, record the limitation and keep its Native guarantee test.

Classify runs as matching, reviewed intentional difference, unsupported, or
unexplained mismatch/crash/timeout. Record attempted, supported and completed
counts and generation parameters; do not hide unsupported or timed-out runs in
an agreement percentage. Known differences need narrow predicates, rationale,
linked regression and review when their scope changes. Every unreviewed failure
blocks the corresponding compatibility claim.

Any mapping of runtime-local IDs must preserve creation, ownership, episode and
binding relationships. Keep raw traces and document permitted observational
projection. Do not sort away meaningful order, discard errors or merge generations
to obtain equality. Existing fixed differential fixtures keep their exact
comparison. Harness workflow acceptance remains separately recorded in the
companion application.

### Negative controls and maintainability

Reuse the five existing errors: failed report promoted to success, release receipt
bypassed, retained payload discarded, inverse depth ignored, and Child request
separated from its inverse. A proof rejection counts only after a fresh matching
positive proof and complete mutant compilation, at the intended contract.
Timeouts, resource limits and unrelated compiler/solver failures are inconclusive.
Behavioral results are recorded independently as detected, survived, not applicable
or inconclusive, with reasons. A proof-detected mutation surviving tests is useful
evidence of different coverage; it does not justify weakening either check.

Factor repeated lemmas only where the actual preconditions and state ownership
match. Keep executable operations and their contracts discoverable together;
separate common protocol reasoning from host-specific interpretation. Review
proof-check cost and change impact, not proof line counts as a success metric.
No `assume`, `admit`, `external_body`, removed guard or weakened observation may
substitute for a difficult proof or failing comparison.

## Acceptance and reporting

Implement related production changes and proofs first. Use compilation and
selected checks to resolve blockers, then finish the related scenario and mutation
support. At the integration boundary run
`python3 scripts/record-development.py --offline` once on the final source;
do not also run its underlying full workflow. Execute the new generated campaign
and paired mutation checks with their own source-bound records. Follow
[validation policy](validation.md) for repairs and refreshed evidence.

Every acceptance record must identify the scope, source/tool/upstream/artifact
hashes, exact commands, raw logs, supported scenarios, observed differences,
proof result, mutation result and remaining boundary. A seed alone is insufficient.
Changed sources do not inherit an earlier pass. New documentation alone does not
refresh proof or release evidence.

Track delivered guarantees, covered operation/failure families, reproducible
minimal failures, unresolved differences, mutation detection and independent
reproduction. A maintainer-run clean installation is not external review or
adoption. Proof obligation counts, random sample counts and compatibility ratios
must not be combined into a paper-completion percentage.

The iteration is complete when all remaining work items satisfy their exit
criteria for the declared scope and a reviewer can follow one continuous chain:
paper clause → real API → executable contract → checked proof → failing and
successful reproduction → rejected erroneous implementation. Release/platform
qualification and the full negative suite retain their separate gates/statuses.

## Retained long-term obligations

General shared-heap replay and function correspondence (R01/P01/P03/S03), complete
recovery at every cut (R08), legal episode deletion (R09), independence (G02),
global progress (G04), confluence (G07) and configuration convergence (C01) remain
in the [fixed inventory](paper-mapping-inventory.md). Closed verifiable values are
the selected route for strong generic value/effect guarantees; arbitrary `Arc<T>`
remains on an explicitly bounded ordinary path.

Node recovery (R07), opaque external resources and scheduler liveness retain
their own obligations. The bounded Native delivery does not require all of them
to be solved first, and cannot discharge them by omission. Extend one supported
effect/host surface at a time when its user value and premises are clear.
