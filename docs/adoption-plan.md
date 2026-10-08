# Adoption and formal-methods plan

English · [简体中文](adoption-plan.zh-CN.md)

The project aims to make existing Cordis applications practical to maintain while
connecting lifecycle guarantees to running code. Adoption must be earned through
installation, compatibility, diagnostics and reliable updates. Formal methods
support those tasks with inspectable contracts and evidence; proof counts alone
do not establish usefulness or adoption.

This plan turns those goals into work items with acceptance criteria. The
[technical roadmap](roadmap.md) retains the detailed proof dependencies and host
work. [Status](status.md), the [paper ledger](paper-obligations.json), and
[source-bound reports](evidence-guide.md) remain the sources of current results.
This document does not change their statuses or the [release gate](releasing.md).

## Who the first milestone serves

The first users are Cordis/Harness plugin maintainers and application developers
who need understandable service replacement, cancellation and cleanup. The
companion [cordis-harness](https://github.com/validation-engineering/cordis-harness)
is the main application entry point; a small pure Rust example provides the
Node-free path. Node is optional compatibility infrastructure, not a requirement
of the Rust kernel. See [architecture](architecture.md) for the separate runtime,
plugin-build and proof-development dependencies.

A successful first evaluation answers three questions: can I run my task, can I
maintain its plugins, and can I check the guarantee I am relying on? An independent
project that continues using the runtime after a real change or failure is the
main adoption signal. Our own repositories and examples do not count as external
adoption. No external adoption is claimed by this plan.

## Work items

P0 identifies prerequisites for independent evaluation. P1 is the main product
and research work; P2 requires demonstrated demand. These are priorities, not
delivery dates. Each item needs the acceptance record described below.

| ID | User outcome | Deliverable and acceptance | Formal connection |
| --- | --- | --- | --- |
| **A01 · P0** | Rebuild the evidence for a version | Durable pinned toolchain archives with the original hashes; clean CI on each claimed platform; complete canonical negative controls and package checks on one frozen revision. Timeouts and compiler/solver failures are inconclusive. | F0; existing full release gate remains mandatory. |
| **A02 · P0** | Run an application without first learning Verus | Qualified runtime artifacts and installation guidance; independent installation runs the official Harness workflow and a pure Rust example. No hidden sibling checkout, workspace link or preinstalled verifier; compiler requirements remain explicit where compilation is needed. | Artifact release depends on A01. Proof reproduction has a separate entry point. |
| **A03 · P0** | Know whether an existing plugin can migrate | Resolve the two unintentional gaps in the archived baseline; preserve the two deliberate contract differences. Rerun the unchanged pinned suite, official workflow and actual plugin cases; record edits and rollback steps. | Compatibility, intentional differences and uncovered behavior remain distinct; F1/F3 explain the contracts. |
| **A04 · P1** | Explain blocked startup or disposal | Expose dependency blockers, owner/episode identity, labeled effects, waiting time and structured failures through the existing diagnostics. A diagnostic read must not execute user callbacks or export service payloads. | An observed state projection, not a proof of all executions; follows F1. |
| **A05 · P1** | Maintain JS/Rust interfaces once | Versioned interface representation and generated client/adapter for one DTO + async service first. Compile generated code and test values, cancellation and replacement; name unsupported members rather than silently emitting `any`. | Reuse the existing protocol; stronger claims wait for the relevant F1/F2 theorem. State the generator trust boundary. |
| **A06 · P1** | Keep dependencies and setup inputs consistent | One declaration produces admission requirements and typed setup inputs; prepare configuration before retiring the old instance. Compile-fail mismatch checks and existing lifecycle traces establish the intended behavior. | Translate to kernel declarations and committed leases; preparation gains no lifecycle authority. |
| **A07 · P1** | Extend guarantees through the actual host | Start with consumer cleanup before provider release in the shared Driver/ActionLedger. Mechanize the mapping and preservation obligations for actual transitions, then extend to cancellation, stale generations and concurrent actions. | F1; tests and a mapping document alone cannot complete refinement. |
| **A08 · P1** | Recover predictably from failed updates | Specify preflight, drain, checkpoint, rollback failure and explicit retry across the existing Loader/HMR paths. Reproduce failed recovery without losing its error or retained recovery source. | Uses A07. Checkpoints cover declared state, not arbitrary external I/O rollback. |
| **A09 · P1** | Load the same native plugin from Rust or Node | Extract a shared native loader/controller; one independent library passes dependency replacement, cancellation, failure retention and checkpoint/retry scenarios in both hosts. Provide a buildable template. | One ABI and journal, with A07's protocol. Logical cleanup does not imply safe physical library unloading. |
| **A10 · P1** | Keep repeated updates affordable | Source-bound application baselines for latency, retained resources, tombstones and loaded images; document budgets by platform/workload and rerun failures after optimization. | Reclamation preserves committed identities, stale-handle rejection and failure retention. No advance speed claim. |
| **A11 · P1** | Audit the complete paper and explicit corrections | Follow the representation, lifecycle and scheduling dependencies in the technical roadmap. Give every ledger item a final audit disposition; preserve counterexamples and separately state corrected results. | F3; close each of the four overall obligations on its own terms. |
| **A12 · P1** | Use a bounded, composable plugin contract | Define a managed profile with explicit dependencies, actions, owned resources and fallible cleanup; ship its SDK, examples and checks. | F2/F4; arbitrary plugin computation, original JS callbacks and I/O do not become proved automatically. |
| **A13 · P0 → P1** | Reproduce why a contract matters | Versioned cleanup ordering, failure retention, late-result rejection and failed-update cases: short demonstration, runnable reproduction, then contract/proof review. Comparisons use equivalent observations and retain unfavorable outcomes. | Evidence follows the actual layer tested; an in-memory probe does not establish file/network behavior. |
| **A14 · P1** | Validate usefulness in an independent project | Capture a real task, installation cost, required edits and blocking reasons; after integration, revisit one real change, upgrade or failure. Record continued use or departure voluntarily. | User failures inform contracts and negative controls. First trials need bounded claims, not a completed general paper proof. |
| **A15 · P0 → P1** | Contribute without depending on one author | Separate compatibility, ordinary-host and proof contribution paths; keep fast feedback and full acceptance distinct. Record semantic decisions, support scope and migration notes; grow independent review. | Contract changes update implementation, proof premises and regressions together. |
| **A16 · P2** | Add a language or deployment boundary when useful | Python, remote RPC or WASM work requires a real task, evidence existing paths are insufficient, a maintenance owner and separate acceptance. Extend one boundary at a time. | Each adds an environment and failure model; existing kernel proofs do not certify a new host. |

The compatibility starting point remains the [archived 87/87 upstream and 83/87
native run](evidence/README.md). A new run of the unchanged pinned suite in the
[second iteration](evidence/2026-10-08-a03/README.md) gives 87/87 upstream and
85/87 native. It fixes the tested provider/consumer update case and cleanup-time
registration message; committed
publication and cleanup-failure retention remain intentional differences. The
historical report is retained. These counts do not establish compatibility with
every upstream version or complete A03's real migration acceptance.

## Formal work alongside the product

F0–F4 are related work areas, not certification levels or a correctness score.
Useful SDK changes can ship with the existing guarantee boundary while the next
proof bridge is being developed. They cannot acquire stronger claims through
tests alone.

| Track | Connection to establish | Completion evidence |
| --- | --- | --- |
| **F0 · Rebuildable evidence** | Source → pinned tools → proofs, negative controls and tests → artifacts | Existing full gates pass at a frozen revision; another environment reproduces the bound evidence. |
| **F1 · Actual host protocol** | Admission → invocation → landing → drain → cleanup → removal | Machine-checked refinement for the specified actual transitions and public calling paths, with explicit premises, nonempty traces and negative controls. |
| **F2 · Constrained standard integration** | Typed/generated interfaces → the shared owner/generation/resource protocol | Dependency/method consistency, correct translation and invalid-capability rejection; external language and generator assumptions are stated. |
| **F3 · Lifecycle and paper audit** | Component/Child representation → general recovery → scheduling/progress → original and corrected specifications | Final dispositions for all 81 entries and completion of the four overall obligations: whole-lifecycle, corrected-specification, executable-simulation and host-boundary. Refuted original claims stay visible. |
| **F4 · Scoped system guarantee** | Published API → shared Driver → execution histories → the applicable lifecycle specification | Every bridge required by the selected managed profile is complete and independently reviewable; plugin, I/O, scheduler and toolchain assumptions are listed. |

A restricted F4 profile may finish before the general F3 result. Its smaller scope
does not close the existing paper-wide obligations. Finite-prefix safety does not
establish eventual cleanup; progress claims must state termination and scheduling
premises. The goal is an honest complete audit, not making refuted original
statements true. The [paper review guide](paper-review-guide.md) shows how to
inspect the connections already present.

## Milestones and exit criteria

| Milestone | Product and research work | Required exit evidence |
| --- | --- | --- |
| **M0 · Independent evaluation** | A01–A04/A13/A15 foundations; F0 and the first F1 contract/mapping | An independent evaluator follows the installation and reproduction record and explains its boundary. Published artifacts separately require the complete release gate. |
| **M1 · Maintainable plugins** | A04–A06; relevant F1/F2 slices; continued paper representation work | An independent author integrates a plugin and changes its interface using the documented tests and diagnostics, without maintainer edits to low-level protocol code. |
| **M2 · Continued operation** | A08–A10, limited external trials; concurrent actions/recovery and resource profiles | A real external workflow survives a relevant modification, upgrade or failure; the same native library passes the claimed hosts/platforms. |
| **M3 · Sustainable adoption** | Clear API/support policy, external contributions and authorized case studies; applicable F4 plus continued F3 | Independent maintainers can sustain a key module or reuse the contracts/method; all advertised guarantees refer to actual APIs and versions. |

These stages overlap. Keep one real user task, its related protocol/proof gap and
necessary reproducibility work active together. Paper-wide research remains a
separately tracked commitment. More host languages do not compensate for a broken
first installation.

## First implementation iteration

This iteration establishes the foundation rather than declaring M0 complete:

| Work package | Present scope | Completion record |
| --- | --- | --- |
| Toolchain and CI (A01) | Restore checksum-matched pinned archives, test installer failures, run actual platform jobs | Archive provenance/hashes, fresh-install commands and job results. Remaining release failures stay open. |
| Comparable cleanup case (A13) | Extend the existing fixed-version research with equivalent provider/consumer observations across implementations | Adapter inputs, exact versions, ordered traces and assertions; distinguish memory-only observations from the existing real-file case. |
| Adoption intake (A14/A15) | Bilingual plan and a [real-task intake form](../.github/ISSUE_TEMPLATE/adoption.yml) | The form is available; no invitation, independent evaluation or sustained adoption is counted until it occurs. |

## Second iteration: the two baseline compatibility gaps

A03 now has a scoped runtime implementation for both accidental gaps. In the
Cordis profile, an external direct provider update can coordinate with updates of
its direct committed consumers in the same synchronous stack, starting from an
idle mutation queue and without a managed invocation origin. A `consumer → intermediate → provider`
dependency path, custom `Config` or an `internal/update` hook excludes the case. The requests share a lifecycle barrier, await asynchronous
cleanup/setup and retain their own failure outcomes. Repeated Fiber updates,
transactions, restart/dispose, queued or later-microtask updates, multi-hop graphs,
custom configuration/hooks and the Harness profile retain ordinary FIFO behavior.
See the [compatibility contract](node-compatibility.md#同栈-providerconsumer-更新).

Cleanup-time registration errors now contain `inactive context`; the
`CLEANUP_BLOCKED` code and prior `STALE_EPISODE` rejection remain intact. These
changes do not prove the JS coordinator or arbitrary callbacks, and do not close
the paper's host-boundary obligation.

A03 still needs a real plugin migration record, including edits and rollback steps.
The four A04 diagnostic tasks now have the bounded implementation below. A05's
DTO + async generator and its related A07 host slice should start from a real
service. Recorded external blockers can change the order without dropping proof
dependencies.

## Third iteration: diagnostics and runtime delivery

A04 now exposes shared Driver dependency reasons, actual target/committed bindings,
consumer/child barriers and pending action tickets. Node adds labeled retained
inverse identities, attempts, failures and optional elapsed time, together with
structured old-episode rejection details. Snapshot reads neither execute callbacks
nor retry or release resources. Regression cases also fix explicit retry through
nested effects and preserve the failed registration when the same raw callback was
registered more than once. See [host diagnostics](host-diagnostics.md) for the scope,
including the different ordinary Rust cleanup contract. An external troubleshooting
record and host refinement remain separate work.

A01/A02 delivery support now includes platform-specific precompiled npm assets, a
standalone new-project installer and optional GitHub draft prerelease creation.
The workflow requires every selected platform to pass the complete quality gate
and install/reinstall the built assets first. Linux x64 and macOS Apple Silicon are
the defaults; macOS Intel is opt-in with `include_macos_intel=true`. Assets and
validation claims cover only the selected platforms. Runtime use needs Node/npm and GitHub
access, not Rust, Verus or a source checkout. This is the Node compatibility runtime,
not a prebundled Harness application or a pure Rust application binary. No runtime
release is available yet; [distribution instructions](native-distribution.md) explain
how the prepared path will work and how maintainers qualify a release.

## Independent installation acceptance

Before claiming M0 or a usable distribution, retain a record from outside the
maintainer's checkout and build cache:

1. Identify the source revision, artifact hashes, OS/architecture and runtime or
   compiler versions. Mark a source trial separately from an artifact install.
2. Start with a clean user environment: no sibling repository, workspace symlink,
   custom addon override or hidden preinstalled verifier. Runtime artifact use
   must not require Verus; source builds must list every actual prerequisite.
3. Follow only the documented path. Run the supported official Harness default
   workflow with the explicit offline scripted model provider, and the documented
   pure Rust example. Confirm that the Rust path needs no Node installation.
4. Remove and reinstall the delivered artifacts, rerun the task and record missing
   or unsupported-target errors. Keep commands, outputs, elapsed time and any
   maintainer intervention; report cold versus warm cache conditions.
5. Record the evaluator's result and unresolved blockers. A maintainer-only local
   package check or a configured CI matrix does not complete independent adoption
   acceptance. Platform claims require actual runs on each claimed target.

This is an acceptance requirement, not a statement that qualified artifacts are
already available. Public experimental source and runtime package publication are
different milestones; neither removes the existing security or release policy.

## Intake, contribution and measures

Use the adoption form for a real migration or maintenance task. A minimal public
reproducer can replace proprietary code; do not post credentials or private
prompts. Record the current approach, desired behavior, environment, baseline
steps, and what would make the evaluator stop or continue. No automatic telemetry
is required. An issue supplies task evidence, not permission to use a person's
name or project in promotional material.

Route a small behavior mismatch to the [bug form](../.github/ISSUE_TEMPLATE/bug_report.yml),
a contract or paper gap to the [proof form](../.github/ISSUE_TEMPLATE/proof.yml),
and a proposed new boundary to the [feature form](../.github/ISSUE_TEMPLATE/feature.yml).
Use [CONTRIBUTING](../CONTRIBUTING.md) for checks. Focused checks provide development
feedback; release acceptance still runs the complete gate.

Each work item or semantic change should retain:

1. **Task and contract:** who needs what, the observable success/failure behavior,
   and what remains retained after failure.
2. **Scope and connection:** profile, versions, platforms and assumptions; actual
   API/Driver/kernel paths; relevant proof and unverified boundaries.
3. **Evidence:** nonempty successful execution, failure/negative control,
   compatibility outcome and source-bound results from the real application path.
4. **Adoption and ownership:** installation/change/debugging cost, evaluator
   feedback, support responsibility and the next unresolved condition.

Track first-run attempts and successes by platform, required migration edits,
maintainer interventions, and continued use after a real change. Also track
independent contract reviews, reproduced counterexamples and reuse of the method
in other projects. Stars and downloads are context, not substitutes for those
observations. Record the actual sample and reasons for choosing another solution;
do not infer a market ranking or a growth target from unobserved competitor usage.
