# R2: production execution contracts

[简体中文](r2-execution.zh-CN.md) · [Paper milestones](paper-refinement-roadmap.md)

R2 connects the paper's constraints to production managed calls. **R2 remains
in progress.** The contracts below run in the Rust and Node adapters; they close
payload, registration and result-transfer gaps, but do not yet establish whole-host semantic
refinement or Component membership for arbitrary plugin callbacks.

## Current closure status

The first function package connects a complete stored **mixed scalar/typed
root or Child body** to full-carrier operation/continuation/inverse laws, actual
declared reads and writes, failure provenance, mixed cleanup and the real
invocation return. It includes `Plugin::native_function`, a runnable conflict
and retry example, kernel/host acceptance cases and four new canonical mutations.
See [the delivery scope and review path](cases/managed-functions.md).

Current-source development acceptance is recorded in
[development-report.json](development-report.json), with source fingerprints;
selected negative checks do not imply full-negative or release acceptance.
The three partial R2 items remain partial: this package does not supply arbitrary
callback semantics, unconditional independence for aliases, complete Node and
configuration meaning, or whole-host paper-step grouping.

The batch descriptions and counts below are historical checkpoints. Their
pending checks and past passes do not override the current source-bound record.

The preceding batch connects actual typed cleanup issue, read/restore and acknowledgement
through every intervening recorded state. See [typed cleanup intervals](#typed-cleanup-issue-read-and-acknowledgement).

The preceding batch adds reversible typed payload replacement and actual cleanup queue composition.
See [typed restoration](#reversible-typed-payload-replacement).

The preceding batch connects actual non-scalar shared payload storage, replacement
and availability checks to the same native execution. See [shared typed payloads](#shared-typed-payloads-in-the-actual-execution).

The preceding batch classifies every commit of the actual recorded native carrier,
including outstanding inverse obligations, and joins the classification to real
snapshots and root/Child returns. See the [complete recorded-carrier classification](#complete-classification-of-the-recorded-native-carrier).

The preceding batch connects the status binding across 61 real mutation methods and
authenticates the complete shared-status history from its actual creation. See
[status continuity](#status-continuity-across-real-calls-and-interleavings).

The preceding batch makes the effect status part of the actual `Execution` ownership
invariant, removing the caller-supplied conditional Journal premise from initialization
and retirement. See [shared effect status](#execution-owned-shared-effect-status).
The three partial R2 work items and original exit criteria remain unchanged.

The preceding native identity batch passed **9 scoped Verus checks, 89 Rust
regressions, 805 Node/Loader regressions and 2 strict negative controls**, plus
formatting and strict workspace Clippy across all targets/features. All **299
canonical anchors** passed preflight. See [checked issuance](#verified-native-identity-issuance).
Previous slice counts are historical, not passes carried forward to changed sources.

The preceding Node captured-ancestry slice passed **179 scoped Verus checks,
29 Rust regressions, 805 Node/Loader regressions and 2 strict negative controls**,
plus formatting and strict workspace Clippy across all targets. The actual JS
callback holds an opaque native path. Its checked constructor preserves the exact
selected parent prefix; wait queries consume the complete captured path, including
completed callbacks with still-live ancestors. See the
[ancestry contract](r2-node-execution.md#captured-callback-ancestry).

Each negative requires a fresh matching positive, whole-mutant compilation and
exact function/diagnostic/source-anchor rejection. All **297 canonical anchors**
passed preflight. An earlier concurrent run had five timeout cancellations; the
final full Node suite passed with the same assertions, concurrency and timeouts,
after builds and proofs completed. This local rerun does not establish the cause
of those delays. Full development, whole-kernel proof, full negative regression,
release and R2 semantic acceptance remain pending.

The preceding Loader/native ownership slice's **86/77/2/8**
(proofs/Rust regressions/doctests/negatives) is historical evidence, not a new pass
on this source. Its configuration factory, RuntimeAccess ownership and joint
snapshot remain in place; see the
[ownership contract](r2-configuration-execution.md#loader-runtime-ownership-and-joint-observation).

The preceding source/configuration batch's **244/60/6** proof/regression/negative
counts and the earlier configuration-Journal **171/56** counts are historical;
they are not additional current-source acceptance.

The preceding source-checkpoint batch passed **68 scoped Verus checks, 55 Rust
regressions and 4 strict negative controls**, formatting and strict workspace
Clippy (all targets). The actual Loader now owns source checkpoints in checked
code, derives updates from processed save documents and retains the original
review stamp throughout I/O. See the [source contract](r2-configuration-execution.md#source-checkpoints-derived-from-the-actual-save).
Negatives require fresh matching positives, whole-mutant compilation and exact
named contract failures. These are scoped results, not full development, full
negatives, release or R2 semantic acceptance. The earlier Node-policy source's
152/81/20/3 and function-return source's 592/139/5 results remain historical.

Actual finite Value/Service returns now authenticate their real write,
inverse-registration and failure witnesses in the same Journal commit as the
returned Call. Each local witness strictly precedes the return; foreign
histories retain their identity. See the [function return contract](r2-function-semantics.md#effects-joined-to-the-actual-invocation-return).
The previous recipe-history batch's 282/128/2 figures describe that earlier
source only.

Actual registered recipes now share the value/work/cleanup Journal. Exact typed
registration, replacement, removal and callback/Value/Service-root return records
bind each returned invocation to its installed revision and actual native Episode. Complete projection
and installed-version origin proofs accompany the real runtime paths. See the
[recipe-history contract](r2-configuration-execution.md#registered-recipes-in-the-common-execution-history).
This advances native function/history composition; arbitrary Component meaning
and the complete native/Node/configuration interpretation remain open.

Actual configuration adoption now uses a checked native batch: complete
preflight, exact new/previous bodies and actual metadata results, with unchanged
live episodes/publications and no partial mutation on rejection. See the
[adoption contract](r2-configuration-execution.md#complete-adoption-of-actual-registered-recipes).
General Component membership remains open; the recipe records now join the Journal as described above.

The source-to-plan traversal now also runs in the checked kernel. The actual
Loader consumes its complete parent-before-child result, using each parent's
real returned context and preserving exact callback/failure provenance. See the
[planning contract](r2-configuration-execution.md#complete-source-to-plan-traversal).
Schema/module/context meaning and full Component composition remain open.
The preceding adoption source passed 169 scoped configuration checks plus 2 dependency contracts, 81 Rust regressions and strict workspace Clippy. Full development, R2 semantic acceptance and this batch's negative-control verification remain pending.

The actual configuration tree, native allocations, ordered structural phases and
recovery extraction now run through checked production owners. Actual save documents,
I/O phase results and accepted-revision/domain stamps are also checked; see the
[configuration review path](r2-configuration-execution.md#structural-reconciliation-and-native-allocation-evidence).
The current configuration identity/removal/reconstruction batch has scoped proof
and compilation/lint evidence; its new runtime/negative cases and full acceptance
are pending. See [the exact contract scope](r2-configuration-execution.md#parent-local-identity-and-complete-structural-dispatch).
The preceding [development record](development-report.json) describes its recorded
source hashes, not the subsequent changed checkout. The 961/226/5 figures below describe the preceding source batch and must
not be carried to changed sources. Historical percentages are effort estimates,
not a prediction of remaining time or paper-proof coverage.

Actual recursive group/include expansion now has a complete payload/order and
read-source derivation, used by both file loading and save preflight. Acyclic
ancestry and the total nesting bound are checked; actual parsed checkpoints are
retained before commit. See the [source expansion contract](r2-configuration-execution.md#source-backed-group-and-include-expansion).
This does not close the grouped component or source-save semantics.

Three substantive obligations remain: full-carrier interpretation of general
functions/effects beyond the checked scalar/typed finite bodies; the complete Node object/Fiber/HMR interpretation and its
connection to the native/configuration trajectory; and group/include and source projection/merge correspondence with configuration
semantics. Passing development checks does not discharge these obligations. R2's
exit criteria and the four integration obligations remain unchanged.

The production Node protocol now has its own continuous checked history joining
lifecycle, publication handles/versions, leases and availability. Actual request,
replacement and reply sequences prove ABA rejection; retained admissions, actual
status/error payloads and rejected replies now share that history. Interval proofs
connect retained ownership and release to the actual Begin. Dynamic control changes
retain their explicit classification. See the [Node review path](r2-node-execution.md).
Actual callback scopes, their wait results and withdrawn-publication selections
now share that history. Release manifests are constructed from the real registry;
finite-history proofs establish publication/scope origins and scope non-reuse.
The actual release queue and delivery filter also share that history. Write and
retirement origins, complete enqueueing and current-slot exclusion are proved for
the returned batch; JS map deletion is still external.
Actual Node reads now also enter that history. Their retained leases are derived
from execution; committed and cleanup views have real Begin/capture origins, and
the returned handles have a read-only context interpretation. This does not
interpret operations inside JS objects.
Actual parent/interface state and dynamic declaration ownership now share this history.
Publication admission and the complete provider-handoff loop use checked real
arguments/results, including blocked releases and partial failures. See the
[interface review path](r2-node-execution.md#actual-interfaces-and-dynamic-provider-handoff).
This code/proof batch has scoped verification; the preceding development record
does not cover these changed sources. New runtime/negative evidence and full
integration acceptance remain pending.
The remaining Node work is JS object/Fiber/function/HMR, callback
dispatch/ancestry and its connection to native/configuration histories.

## Remaining delivery packages

These packages refine the existing three open execution obligations and the
`configuration` work package in `paper-refinement-plan.json`. They do not replace
the six recorded R2 work-item statuses or change the milestone's exit criteria.
They describe outstanding integration work, not completed proofs.

| Package | Implementation and proof deliverable | Closure criterion |
| --- | --- | --- |
| R2-A · Extensible effects | Actual arguments, read/write footprint, outcome and returned inverse at the managed effect boundary | A new primitive supplies checked effect/inverse laws used by its real invocation, without caller-provided expected outcomes |
| R2-B · Function fields | Interpret stored roots, actual continuations, Child bodies and accumulated inverses | The actual code and receipts have the required meaning on every input in the stated carrier, including failure domains |
| R2-C · Shared production state | Inventory fields, owners and mutation entry points; compose runtime, execution, shared episode, service slots, Child and cleanup | Every relevant observation has an interpretation and every mutation preserves the common invariant, including escaped handles and late replies |
| R2-D · Host integration | Compose native/static policies, Node value handles, publication versions, leases, HMR and dynamic interfaces | Each actual boundary uses the common interpretation or an explicit extension, with argument/result and version provenance |
| R2-E · Step correspondence | Cover success, rejection, cancellation, failure and retry at each managed entry | Each transition refines a paper step, preserves the complete relevant observation, or satisfies an explicit extension rule |
| R2-F · Joint execution history | Compose control, value, function, Child, cleanup and version histories across interleavings | Actual execution constructs one continuous source trace from the real initial state, including failed prefixes |
| R2-G · Runtime and negative evidence | Record cases during implementation; implement the necessary integrated regressions and contract mutations afterwards | Fault cases exercise the real callers, and selected compilable mutations are rejected by the named contracts |
| R2-I · Configuration workflow | Connect parent-local entry identity, groups/includes, module/configuration processing, revisions, recovery and persistence results to lifecycle actions | Accepted configuration changes act on the exact registered components; failure/cancellation retain real recovery inputs and partial work is not reported as committed |
| R2-H · Integration acceptance | Run and record complete development checks after the related implementation and evidence are assembled | The existing R2 obligations and configuration integration are closed with matching source-bound evidence |

The configuration package is already assigned to R2 in the plan. Definition 81's
six-field record is formalized, but `Entry::as_paper_entry` only projects resolved
named leaves. It rejects groups, includes and child-bearing entries; that local
projection does not prove the whole loader transaction. Parsing, module execution
and external persistence results retain explicit boundary contracts.

Use the [implementation-batch workflow](paper-refinement-roadmap.md#implementation-batches-and-acceptance).
Start with C's state inventory and E's entry-point inventory, integrate A/B/C and
the native E/F path, then D/I and their step/history correspondence. R3/R4 can
consume established contracts while G/H are pending. Track necessary deferred
cases with their caller, guarantee and intended failure; add tests and fault
demonstrations at integration, then run the complete checks. Required acceptance
evidence is deferred, not discarded. G/H remain pending until actually completed.

The [production state inventory](r2-state-inventory.md) now records the native
owners, mutation entries, remaining semantic boundaries and deferred integration
cases. The first A/B implementation adds extensible scalar computations to the
real managed value path; see below. These are implementation advances, not R2
integration acceptance.

## Historical delivery estimate — 2026-10-16

**The earlier engineering estimate was 82% (planning range: 78–88%).
It is retained as planning history, not the current completion measure.**
The exit audit still has three partial work items; no new percentage is inferred
from passing more checks. The previous weighted estimate was 80%; this is not a
percentage of proved paper statements. It does not change the six canonical
work-item statuses, the four open integration obligations, or R2's exit criteria.
Credits below are reviewer judgement about delivered work; proof counts do not
determine them. Code/proof packages contribute 90 points and acceptance 10.

| Package | Weight | Current credit | Main remaining deliverable |
| --- | ---: | ---: | --- |
| A · Extensible effects | 10 | 9 | General effects and declared object footprints beyond the scalar carrier |
| B · Function fields | 15 | 14 | General callback/heterogeneous-effect bodies and full original-carrier Component composition |
| C · Shared state | 15 | 14 | Static context inputs, Arc/Weak/mutex association, opaque slot interiors and remaining host observations |
| D · Host integration | 10 | 7 | JS object/version association, dynamic interfaces and HMR in the common interpretation |
| E · Step correspondence | 15 | 14 | Full-observation classification of every remaining managed entry and failure branch |
| F · Joint history | 15 | 14 | One continuous trace joining function, Child, value, control, cleanup and version histories |
| I · Configuration | 10 | 6 | Entry expansion, structural lifecycle actions, reconstructed snapshots, persistence and the joint configuration history |
| G · Runtime/negative evidence | 5 | 4 | Recorded new scenarios and named compiling mutants on the integrated interfaces |
| H · Integration acceptance | 5 | 0 | Final source-bound development record after all obligations close |
| **Total** | **100** | **82** | **R2 remains in progress** |

The previous publication/owner batch joined the common trajectory with complete
typed indexing and same-epoch observation (+1 in C). The slot batch connected actual
managed publication/import slots and capture commits. The subsequent handle/control, context and scope batches share actual
status and immutable Begin metadata and connect registered realms and callback scopes.
The declared-access batch joins actual scalar calls and finite function instructions
to the production object carrier (+1 in B); the remaining packages have not closed.
The multi-service batch adds whole-body declaration checks, actual cross-service continuations and failure-prefix histories (+1 in B).
The alias/effect batch connects native declared preparation and actual input-to-commit causality and establishes the conditional paper lift (+1 in A).
The stored-function batch connects registered multi-service root/Child dispatch,
complete finite dynamic-resolution interpretation and the actual inverse queue
(+2 in B). The configuration batch adds actual owned update/Future sequencing, native target guards and commit/recovery gates (+2 in I). The implementation/proof subtotal is **78/90 (about 87%)**.
Twelve implementation points remain, primarily general function/effect
composition and Node/configuration integration. Acceptance is separate. Earlier
day budgets were provisional planning estimates; calendar duration needs
re-estimation against those remaining integration paths.
The largest remaining risks are heterogeneous callback/effect interpretation,
Node object/version semantics and configuration identity-to-action correspondence.
Further native scalar leaf contracts alone must not be counted as closing these
packages. Full-observation host composition and general paper-step grouping
still require implementation and final acceptance.


## Actual configuration update and recovery protocol

The Loader now stores its real update plans in the checked `Configuration` and
`Batch`, while `ConfigUpdatePlan` stores the actual forward/inverse Futures in
checked `Reversible`. A native target binds runtime domain, component ID,
activation generation and recipe revision. The actual returned poll result drives
forward progress and reverse recovery; commit/recovery cannot bypass outstanding
work. See the [paper-to-code review and remaining boundaries](r2-configuration-execution.md).

The preceding source batch passed **961 selected Verus checks, 0 errors**, with whole-kernel
crate compilation, and **226 Rust tests**, including five new configuration/target
cases. Workspace all-target/all-feature Clippy, Rustdoc with warnings denied,
formatting and diff checks pass. Five strict controls each pass a matching positive
and whole-mutant compilation, then fail the exact named runtime contract. All
**259** canonical mutation/diagnostic anchors pass preflight; 49 negative-harness
tests and the paper allocation/review/coverage checks pass.

At that preceding checkpoint, whole-kernel proof, full development/R2 acceptance,
complete negative regression/calibration, Node tests and release/platform checks
were **not run**. The current development record supersedes those scoped results
for workspace validation; semantic R2 acceptance remains separate.

R2-I remains partial: entry
expansion, structural lifecycle actions, reconstruction semantics, persistence
and the common configuration/Node history still require composition. This does
not close the four integration obligations or authorize whole-paper claims.

## Stored multi-service functions and complete finite-body interpretation

`Plugin::native_service_program` stores the complete body in `Body::Services`.
The checked native root/Child dispatcher obtains the actual recipe revision,
checks all registered keys before root issuance, and settles from the actual
result. Every operation captures its then-current Begin-bound slot.
`service_composition` proves grammar membership for every resolution schedule
and interprets the actual complete success/failure prefix, using Journal-qualified
allocation addresses. `service_stack` connects the strict reverse stack to the
real retained queue. See the [paper-to-code review and limits](r2-function-semantics.md).

The finite registered path now closes this body-level composition. General
callbacks, heterogeneous effects, the full original-carrier Component result,
remaining Node observations and configuration workflow are still open.
The canonical R2 statuses and four integration obligations remain unchanged.

Historical stored-function-batch verification passed **921 Verus checks, 0 errors**, with
whole-crate compilation, and **166 Rust regressions** (including five new
integration cases). The interleaved example, workspace Clippy/Rustdoc,
formatting and diff checks pass. Five strict controls each have a fresh
same-selector positive, complete mutant compilation and the exact named
contract rejection: stored-operation substitution, lost Journal identity,
interpreted inverse order, actual cleanup-stack FIFO and discarded final failure.
All **254** canonical mutation/diagnostic anchors pass preflight; that is not a
full negative-verification result.

The actual waiting queue now appends exactly the recorded instruction tokens.
Cleanup dispatch exports LIFO selection for a new restore and preservation of an
already-selected retry ticket; `next_queued_inverse` composes that real dispatch
with the last retained prefix inverse. Failure-result transfer is extracted into
the actually called `Report::failed`, so its negative control rejects loss of the
real failure without expanding unrelated trace invariants.

Whole-kernel verification, full development/R2 acceptance, the complete negative
suite/calibration, Node runtime, benchmarks and release/platform checks were
**not run**. Earlier sections describe historical batches; their counts are not
automatically evidence for later source changes. The current configuration-batch evidence is recorded above.

## Native extensible effects and the alias-aware paper mapping

The native `update_reversible_with` path now uses
`capture_native_effect → Capture::prepare → apply_native_effect`. The first entry
resolves the actual Begin declaration and retains its provider/slot/object and
root or effect-group identity. Calculation runs outside the host and value locks.
Landing rechecks the lifecycle/work/queue identity, admission and captured
value/depth, then retains the real inverse before returning. The ordinary host
still supplies the association with its exact shared Episode allocation; numeric
identities alone do not authenticate independently constructed host instances.

The private prepared value now carries evidence of its **actual input read**.
Every committed or rejected calculation follows that checkpoint; a local read
also includes the captured slot-selection commit. Overflow, rejected computation
and stale-input rejection preserve the entire recorded Journal state and pending
inverse obligations at the rejection event. Other writers may still interleave.
Replacing a slot during calculation does not redirect the calculation or its
inverse: both retain the original allocation.

| Paper constraint | Checked contract | Production connection |
| --- | --- | --- |
| Definition 8: returned inverse restores the input | `effect::operation`, `managed_step` | Actual computed result, before/after states and queue-owned inverse |
| Definition 29, equation (31): one binding operation | `single_key_refinement`, `single_key_effect` | Actual write checkpoint, provided the selected name still denotes this allocation and has no other current alias in the observed map |
| Definition 30: outcome-selected operation stage | `terminal_member`, `general_semantics` | Built-in and extensible writes share one allocation-key library, including the real continuation and strict inverse |
| Strict R1 independence interpretation associated with Theorem 47 | `allocation_independence`, `Write::disjoint_from` | Distinct actual allocations in the same Journal; covers generated forward/inverse words and outcome/continuation stability |

`targets` is extracted from real local managed slots; `production_value` updates
**all current aliases**, and `production_replace` accounts for the separate
resolution change. Opaque and foreign entries remain explicit in the complete
service projection, outside this local scalar map. `operation_agrees` connects
the fixed operation enum to the same general `ScalarEffect` model.

There is a real compatibility boundary: equation (31) leaves every other key
unchanged. `other_alias_changes` proves why a second alias of a successful managed
write violates that literal single-key interpretation. The alias-aware projection
is an explicit extension; `single_key_refinement` recovers the paper step, including
failure and the inverse on every coherent recovery input, under its stated
condition. No runtime alias ban or false independence premise has been added.
This is a property of the implementation's interpretation, not a refutation of
the paper under its own assumptions.

This closes the native declaration/prepare/commit mapping for the supported
extensible scalar family. Arbitrary effectful callbacks, other mutable value
carriers, whole root/Child continuation membership, dynamic multi-call grouping,
and Node/configuration integration remain R2 obligations. In particular, two
operations on the same allocation still require their own independence witness.

Current-source scoped validation: **890 selected Verus checks**, zero errors,
whole-crate compilation, **161 Rust regressions**, the interleaved example,
workspace Clippy/Rustdoc with warnings denied, and format/diff checks passed.
Three new integrated regressions cover retained targets across replacement,
wrong-owner/stale/closed rejection, and actual Child aliases, both conditional
branches, same-host reentry, overflow, panic and inverse cleanup.
**Five strict negative controls** pass same-source positive proof, whole-mutant
compilation and exact named-contract rejection: alias singleton closure, input-read
causality, owner admission, stale-error classification and discarded inverse.
The alias/cause controls modify proof evidence; the other three modify runtime
behavior. All **251** canonical mutation/diagnostic anchors and **49** harness
regressions pass. Whole-kernel verification, full development/R2 acceptance,
full negative regression/calibration, Node runtime, benchmarks and release/platform
acceptance were **not run**. Prior batch results below are historical.

Review: [`native_effect.rs`](../crates/cordis-kernel/src/native_effect.rs),
[`value_alias.rs`](../crates/cordis-kernel/src/value_alias.rs),
[`scalar_effect.rs`](../crates/cordis-kernel/src/scalar_effect.rs),
[`value_access.rs`](../crates/cordis-kernel/src/value_access.rs).

## Multi-service native bodies and dynamic footprints

`Setup` and `AsyncSetup::run_service_program` execute a finite body with a typed
service key, scalar operation and outcome-selected continuation per instruction.
The host resolves keys through its actual context; the checked executor validates
**all** body declarations against the real Begin owner before the first write,
including branches that this run will not select. Backward or out-of-range
continuations are rejected. Ordinary root/Child callbacks and dynamic effect
groups use the same `Execution::run_service_program` entry.

Each instruction resolves its current slot, applies the actual operation and
retains its inverse in the actual receiving queue before advancing. A later
overflow or service-read failure returns the real program counter and preserves
every successful prefix inverse, with consecutive tokens and the original queue
prefix unchanged. Computation rejection carries erased evidence for the actual
selected object and rejected operation. Cleanup continues to target captured
objects after slot replacement.

Same-Journal calls carry the preceding completion receipt, including inverse
registration when that registration uses the value's Journal. `join_causes`
checks both that receipt and the current slot-selection receipt against the
actual Journal under its read lock. `source_trace` and `failed_trace` then place
successful calls and a rejected final computation in a real continuous history.
Allocation, slot replacement, other writers and lifecycle events between calls
remain in that history. A rejection preserves the recorded state and pending
obligations. These are erased proofs, not runtime audit logs. The causal join
adds a Journal read-lock acquisition; no performance improvement is claimed.
Foreign-Journal services remain supported, with separate histories rather than
an invented total order across domains.

`Report::production` derives each step's meaning on the actual allocation map.
`successful_footprint` records captured slot/object reads and successful object
writes; a rejected computation has its separate capture/receipt witness.
`affected` derives the union of **all current aliases at each actual write**;
`frame` proves that this body's writes preserve other service observations.
It is not a whole-interval frame against unrelated concurrent writers.
The effective alias set is a proof projection, not a new runtime permission.

The hard boundary is now explicit: declared service names authorize calls, but
an alias may expose their effects under another name. The executor does not
reject existing aliasing plugins or silently assert that their declared names
are independent. `Program::component` proves the finite body on the existing R1 finite scalar carrier
with independent ports; `interpreted` proves real calls on allocation state.
The alias/effect section above now supplies the explicit extension and conditional
single-key lift. Full multi-call/root composition, arbitrary callbacks/Futures,
other value carriers, opaque values and Node/configuration composition remain open.
The new multi-service API is native-only; existing single-service APIs retain
their static-host path. Stored single-service root bodies remain available;
this new finite sub-body is invoked by actual ordinary callbacks.

Review: [`service_program.rs`](../crates/cordis-kernel/src/service_program.rs),
[`value_access.rs`](../crates/cordis-kernel/src/value_access.rs),
[effects](paper-refinement-map.md#effects),
[components](paper-refinement-map.md#components). The B package advances from
11/15 to 12/15. No canonical integration obligation is closed.

Historical multi-service batch evidence (before the alias/effect changes): **832 selected Verus checks**, zero errors,
whole-crate compilation, **158 targeted Rust regressions**, the interleaved
example, workspace Clippy/Rustdoc with warnings denied, and format/diff checks
passed. Four new integrated cases cover cross-provider branches and overflow,
unselected declarations/realms, actual effect-group queues, and Child aliases,
slot replacement, foreign Journals and retained failed-prefix cleanup.
**Five strict compiling mutants** passed matching-positive, whole-mutant
compilation and named-contract-rejection checks: four new declaration/prefix/
causality/aggregate-frame controls and the existing continuation control with
its outdated function attribution corrected. The cause and aggregate-frame
mutants change erased proof instrumentation, not runtime behavior. All **248**
canonical mutation/diagnostic anchors and **49** harness regressions passed.
Whole-kernel verification, full development/R2 acceptance, full negative
regression/calibration, Node runtime, benchmarks and release/platform acceptance
were **not run**. That batch estimated R2 at **77% (73–83%)**; this did not
change the canonical paper or integration statuses.

## Declared native calls and production function steps

The native paths of `AsyncSetup`/`Setup::update_reversible` and
`run_value_program` now call `Execution::apply_native_value` and
`run_native_value_program`. The kernel reads the actual Begin-owned/imported
service, checks its declared port and retains the actual selected object.
Ordinary root/Child callbacks and dynamic effect groups use these same entries;
registered finite root/Child dispatch also delegates to the program entry.
The new `observe_reversible` reads the declared service through this checked
selection and returns its real scalar snapshot and Journal checkpoint.

`access::Footprint` separates the selected slot read, retained object read and
object write. Cordis declarations authorize service access; this does not invent
a separate read-only permission system. The selected object, actual forward
event, returned result and queued inverse are linked by `access::Write`.
Successful finite instructions have the same correspondence through
`Report::production_steps`, including the retained successful prefix of a
failed program and its actual receiving cleanup group.

The source state is `access::objects` of the **actual journal records** at each
write position. `interpret` derives the dependent-grammar operation on that
whole local object map; no caller-supplied coherent initial table is required.
`primitive_theory` establishes the operation/inverse law on its complete scalar
allocation carrier. `project_value_step` lifts each write to the actual owned
and imported service maps: all current aliases of its allocation change, and
other observations are framed. Intervening writes, replacements and lifecycle
events stay in the common history; the entire callback interval is not claimed
to be atomic or free of interference.

An erased selection receipt is passed through actual snapshot acquisition and
managed writes. Same-domain reads include the captured slot commit; successful
writes occur strictly after it and preserve its authenticated history prefix.
Program instructions retain this causal link before their actual inverse
registrations. A replacement may make the current slot select a new object;
the captured object and its inverse keep their original identity. Foreign
Journal references retain their explicit boundary, without a fictitious shared
causal order. These receipts/history fields are erased from ordinary builds.

**Boundary retained by the multi-service work above:** a declaration on one port does not prove that another
port is unaffected when both alias the same object. `declared_frame` requires
the actual alias closure to be included in the proposed port write set. That
condition is explicit, not derived automatically from plugin declarations.
The multi-service executor above derives its effective alias footprint at each write.
Lifting it to a fixed declared-port carrier still needs this condition and dynamic-resolution semantics.
The native `update_reversible_with` path now composes declaration capture,
actual-input preparation and checked landing as described above. Complete
function composition and other effect/value carriers remain separate work. Arbitrary callback/Future bodies, opaque payload interiors, static host
inputs and ordinary host pointer/mutex association are not proved by these calls.

Review links: [effects](paper-refinement-map.md#effects),
[observations](paper-refinement-map.md#observations),
[components](paper-refinement-map.md#components);
[`value_access.rs`](../crates/cordis-kernel/src/value_access.rs),
[`value_function.rs`](../crates/cordis-kernel/src/value_function.rs),
[`native_slot_observation.rs`](../crates/cordis-kernel/src/native_slot_observation.rs).
That earlier batch advanced the function-field package from 10/15 to 11/15; it closes no
canonical integration obligation. Its historical R2 estimate was **76% (72–82%)**.

Historical declared-access scoped evidence: **796 selected Verus checks**, zero errors,
complete crate compilation, **154 targeted Rust regressions**, the interleaved
example, workspace Clippy/Rustdoc with warnings denied, and format/diff checks
passed. Three new integrated cases cover declared reads/rejections and a failed
program prefix, the actual dynamic cleanup group, and an ordinary Child using
aliases, replacement and old-object restoration. **Eight strict compiling mutants**
passed fresh-positive/whole-mutant-compilation/named-contract-rejection checks:
three new access/causality/alias controls and five migrated implementation controls.
The causal-receipt mutation changes erased proof instrumentation, not runtime
behavior. All **244** canonical mutation/diagnostic anchors pass preflight.
Whole-kernel proofs, full development acceptance, full negative regression and
calibration, Node runtime, benchmarks and release/platform acceptance were
**not run**. Historical evidence below belongs to its stated earlier sources.

## Local object references and actual service observations

The common trace now establishes a stronger invariant: every recorded slot
selecting a local object has a corresponding object record in that same state.
This is derived from actual allocation/replacement commits, not supplied as a
coherent-heap premise by the caller. `Snapshot::trajectory` exports the invariant
at every prefix, starting from the empty map, including concurrent writes,
replacements, lifecycle changes and cleanup/retry.

`ReversibleValue::reference` obtains a persistent receipt under its real read
lock. `Slot::new` and `Slot::replace` submit that exact target receipt to the
Journal. The authority checks its provenance, and `object_retained` proves that
later steps preserve the allocation's identity and record type. Domain identity
is the authoritative history's resource identity; it is not a host-assigned
integer. All other allocation/update entries preserve the same invariant.
Replacement takes a short object read before the slot write; that read is
released before acquiring the slot or Journal. No object/slot lock or callback
is entered while holding the Journal lock. Receipts and histories are erased;
retaining historical records in the proof does not retain runtime allocations.

The actual publication and Episode maps now have complete service observations
at the production checkpoint. Every actual map key is represented as opaque
payload, foreign slot, foreign object selection, or local object state. A local
slot collected before a concurrent replacement resolves its **current** object
at the later shared epoch. Foreign states are not guessed; opaque payloads do
not acquire scalar semantics. `service_snapshot`, `service_episode_snapshot`
and the controlled/scoped variants export this composition alongside lifecycle,
work, cleanup, context and polling state.

`aliases` and `value_observation_step` prove that actual writes and restores
affect every local slot selecting that allocation, while other selections are
framed. `Capture::execution_snapshot` also proves the captured old local object
still resolves after replacement; it does not retarget the capture or inverse.
These are implementation premises for the paper's value observations and frame
reasoning ([review path](paper-refinement-map.md#observations)), advancing
R2-C/E/F. They do not establish declared footprints for arbitrary functions,
the complete R1 carrier, or independence merely because two ports differ.

Historical slot/reference-batch evidence: **774 selected Verus checks**, zero errors, complete
crate compilation, **151 targeted Rust regressions**, the interleaved example
and workspace Clippy/Rustdoc with warnings denied passed. Three new scenarios
exercise cross-thread replacement with alias/old-object cleanup, foreign target
round trips, and mixed publication/import observations; the existing concurrent
production checkpoint regression also passes. **Seven strict compiling mutants**
were rejected at their named contracts, including three new reference controls.
The replacement-substitution control requires both its success and rejection-
payload diagnostics. All **241** canonical mutation/diagnostic anchors pass
preflight. Whole-kernel proofs, full development acceptance, full negative
regression/calibration, Node runtime, benchmarks and release/platform acceptance
were **not run**. Evidence below belongs to its stated historical sources.

At that batch the estimate was **75% (71–81%)**. Local reference closure and actual service
projection are now established; general function/Child interpretation, ordinary
host pointer/mutex association, Node/configuration composition and whole-R2
acceptance remain open. Proof counts do not determine the completion estimate.

Review: [`value_references.rs`](../crates/cordis-kernel/src/value_references.rs),
[`joint_execution.rs`](../crates/cordis-kernel/src/joint_execution.rs),
[`value_slot.rs`](../crates/cordis-kernel/src/value_slot.rs),
[`native_slot_observation.rs`](../crates/cordis-kernel/src/native_slot_observation.rs)
and [`native_slot_runtime.rs`](../crates/cordis-kernel/src/native_slot_runtime.rs).

## From the actual write to the actual inverse registration

Each `Inverse` now carries an erased, persistent `joint::Receipt` captured from
the value's real journal commit before releasing its lock. `Inverse::recorded`
binds it to that object's identity, exact forward event and before/after states.
The receipt is created by the authoritative member; an event index supplied by
a caller is insufficient.

The private typed `Execution::register_inverse` bridge uses the receipt from
the **same inverse payload** it inserts. Under the cleanup queue's actual journal
lock, `Member::update_following` authenticates the earlier prefix. If both owners
use the same Journal, the trajectory records `Change::RegisterInverse { write }`.
`joint::valid` requires that index to name a real earlier successful forward
operation. The registration event still performs the exact cleanup transition:
append one occupied slot and its waiting token. Other entries are framed.

| Production path | Evidence exported by its contract |
| --- | --- |
| `Execution::apply_value` | `ValueAdmission::registration` connects the returned result, actual queued inverse, queue identity/domain and token. |
| `Execution::apply_prepared_effect` | The same connection uses the actual checked computation's event and captured input. Rejected or stale preparations add no inverse. |
| `Execution::run_value_program` | `ProgramReport::registered` and `registrations` connect every successful prefix instruction to its own write position and actual queue slot, including a later failing instruction. |
| `Execution::advance_value_program` | The cursor retains the last successful registration and its exact checkpoint position; rejection or exhaustion preserves the prior certificate. |
| Stored finite root/Child | `Function::run`, `Report::appended` and `RegisteredReport::certified` export those same certificates through the real registered dispatcher. |

`Evidence::microsteps` produces the continuous journal prefix containing both
endpoints and any intervening operations. `Evidence::paper_write` interprets
the forward endpoint and its strict inverse through the existing dependent
grammar, under the stated scalar carrier and key-table premise. These are
properties of the actual managed call, not an independently supplied log.
Receipts, positions and edges are erased. This change adds no runtime event
log, event counter, Journal clone or additional lock acquisition.

Independent objects and standalone executions remain supported. A foreign
Journal gets its local write evidence and the owner's real insertion evidence,
but **no same-domain edge or order theorem**. An unlinked queue has no joint
insertion receipt. The contracts distinguish all three cases rather than
equating unrelated numeric positions.

**The two operations remain separately observable.** The forward commit now
also creates an erased `joint::Pending` capability and an entry in the same
Journal's authoritative pending map. `Applied::pending` owns that capability;
the finite interpreter retains each one in its actual `Batch::items`, including
the successful prefix of a failing program. Admission selects this contract
only when the actual cleanup queue and value share a Journal.

The typed registration bridge moves the actual inverse into the queue and
consumes its capability in the **same journal commit** that records the queue
append. `Evidence::pending_interval` proves that every intervening trace state
retains the obligation for that exact write and object, and that registration
removes it. A consumed capability cannot be duplicated or used for a second
transfer. `Snapshot::pending` and `pending_trajectory` expose this projection
alongside the object/work/cleanup trajectory. The map and capabilities erase;
they add no runtime counter, log, lock acquisition or heap allocation.

This establishes the pending interval for **calls with certified registration
evidence** on the four managed scalar paths above, including finite registered
root/Child results and failed program prefixes. It does not turn the pair into
an atomic paper step or prove a census of arbitrary Rust values. Raw
`ReversibleValue::apply`, foreign-domain values and unlinked queues do not
create this managed obligation.

### Producer-authenticated return contracts

A previous audit found that `Execution::apply_value` could discard a successful
`Applied` and return `Overflow` while its selected proof still passed. Owner-field
equality did not describe the interior shared write, and tracked resources can
be discarded. The production implementation did not contain that branch.
**The same compiling mutation is now rejected by the actual return contract.**

`Execution::attempts` retains an erased `attempt::Ledger`. The scalar producer
appends the authentic receipt from its real value commit while still holding
the value lock. Prepared effects do the same for computation, stale-input and
rejection events. The owner is passed mutably into that producer; the caller
does not supply an expected outcome. An admitted call must extend the previous
receipt sequence by exactly one entry. Success binds that entry to the actual
queued inverse and registration; an error must match the actual rejected event
and its error classification. Closed admission retains the entire owner.
Other errors retain all runtime owner fields while adding the erased receipt.
Work, cleanup, native lifecycle and finite root/Child contracts frame this history.

| Managed entry | Return obligation |
| --- | --- |
| `apply_value` | Overflow or capacity must come from the real rejected input; a successful write must have the actual queued inverse and registration. |
| `apply_prepared_effect` | Distinguish stale input, exhausted depth and rejected computation using the actual receipt and prepared input/code. Success registers the matching inverse. |
| `advance_value_program` | A non-admission error must be the rejected instruction in the cursor's real checkpoint. Exhaustion retains the owner and last registration. |
| `run_value_program` | Only closed admission returns outer `Err`. An admitted failing program returns its certified report after registering every successful-prefix inverse. |

`Ledger::rejection_step` proves that the authentic rejection commit preserves
the **whole joint state map and pending-obligation map in the receipt's Journal**,
with no new pending
write or settlement. This is a stuttering implementation step at that commit;
other callers may still interleave before or after it. It does not claim that
the entire duration of a call freezes the shared state. The ledger adds no
runtime history, allocation or lock acquisition.

The preceding producer-return batch rejected the discard-success/return-error
mutation. Those producer contracts remain in the selected positive scope.
They cover the four managed scalar entries; raw writes, external callback side
effects, panic/abort recovery and global termination remain outside the guarantee.
Current batch evidence and the remaining cleanup obligations are listed below.

Review: [`value_attempt.rs`](../crates/cordis-kernel/src/value_attempt.rs),
[`value_registration.rs`](../crates/cordis-kernel/src/value_registration.rs),
[`joint_execution.rs`](../crates/cordis-kernel/src/joint_execution.rs),
[`value_program.rs`](../crates/cordis-kernel/src/value_program.rs),
[`value_function.rs`](../crates/cordis-kernel/src/value_function.rs).
The [mixed native episode regression](../crates/cordis-kernel/tests/registered_value_function.rs)
combines a stored root, direct write, checked computation, cursor, foreign
object and failed program prefix, then restores both actual objects in cleanup
order. `r2-register-inverse-omits-edge` checks the erased causal instrumentation;
the retained inverse-loss controls change actual runtime ownership.
`r2-managed-write-omits-pending` and
`r2-registration-drops-pending-capability` check missing production proof
instrumentation against named contracts; they are not runtime fault claims. Full R2
and full negative-regression acceptance remain open.

## From issued inverse to actual restoration and acknowledgement

The production `CleanupQueue::dispatch` now returns erased
`restoration::Evidence` with every scalar completion. It takes the inverse from
the actual selected slot, executes its guarded restore, and acknowledges that
result inside the verified typed path. `CleanupGroups::dispatch` and
`Execution::dispatch_cleanup` expose the same identity and trace contracts.
Both [`Runtime::poll_cleanup`](../crates/cordis/src/runtime.rs) and the
[static host](../crates/cordis/src/runtime/static_host.rs) consume this dispatch;
the scalar inverse executes inside that verified call. Ordinary host diagnostic
flags and external callbacks still require their own interpretation.

| Actual boundary | Required evidence |
| --- | --- |
| Queue `pop` | An authentic issue receipt names the selected ticket and the now-empty slot. The dispatched inverse equals the original stored payload. |
| `Inverse::restore_following` | The receipt comes from the real locked `Restore` or `Blocked` commit and names the exact object, inverse and state. A successful snapshot has that source and history position; failure returns the same inverse. |
| Typed acknowledgement | The receipt names the same ticket and actual outcome. Success empties the slot; failure retains exactly the original inverse and selects a failed attempt. |
| `dispatch_cleanup` return | A value report carries those receipts; an error or no-action result preserves the live queue and its trace. Other queues remain framed. |

For a queue and object in the same Journal, `Evidence::microsteps` proves
`issue < restore/block < acknowledgement` in one authentic continuous history,
including intervening commits. `Evidence::paper_attempt` interprets the actual
restore as the strict inverse of the scalar operation; a blocked attempt leaves
the interpreted service table unchanged. Existing `retry` contracts preserve
the payload and advance its attempt; a later dispatch obtains fresh receipts.
The evidence is erased and uses existing journal locks, with no runtime log or
additional lock acquisition.

The typed scalar path now also requires the interval guarantee below. A
whole-host resource census, shared host fields
and general paper-step grouping remain open. Foreign-domain objects retain
separate authentic histories; unlinked queues have no joint queue interval.
Generic host callbacks, Node/configuration composition and global termination
remain explicit boundaries.

## Registered realms and callback scopes

The actual `Context` uses the checked immutable `RealmContext`. Resolution uses
the registered key-to-realm map (default realm zero); `with_realm` changes one
entry and `share` selects the source context's realm without changing other keys.
Clones share the immutable map. `RegisteredPlugin` retains that map alongside its
anchor, and registration/Child/Begin contracts propagate both to `Capture` and
`NativeContext`. Native `Runtime::start` builds its context and anchor from this
Begin owner, so mutable `Mounted` bookkeeping cannot select a different map.
The existing publication projection now includes realm/anchor metadata; its
retention theorem therefore preserves them across interleavings until Unload.

`AsyncSetup` carries a checked `SetupScope` instead of a host-filled group number.
`root_scope` identifies the actual root queue. `admit_scoped_effect` admits the
real iterator and issues its origin/work/group/queue identity together;
`EffectRun::call_scoped` checks the iterator identity before delivering the scope
and actual payload to the adapter closure. An incorrect scope returns the runner,
argument and closure without invoking them. The host checks the scope against
the current Execution before registering resources. The scope remains usable
while its queue is live, including during permitted cleanup registration; its
historical queue record does not authorize use after removal.

The production `plugin_execution_snapshot` now uses
`scoped_service_episode_snapshot`. `SetupScope::observed` proves that this actual
scope selects a live membership entry and queue in the same read epoch as control,
work and service slots. It reuses the existing Journal read. Callbacks still run
after releasing the host mutex and outside the Journal lock.

A failed poll admission is **not** a blanket no-change operation: when its target
bindings disappear or change, the checked protocol may cancel/settle the queue.
The rejected iterator is unchanged and no callback scope is issued. Admission of
an effect request (`enqueue_native_effect`) retains its separate exact rejection
contract. Keeping these cases distinct preserves the runtime's cancellation
semantics in the proof.

These are executable connections for the existing context, committed-dependency
and group-scoped effect obligations. The five production identity allocators are now
[checked](#verified-native-identity-issuance); other namespaces and the ordinary
Arc/Weak/Mutex bridge remain host premises. Static embedding inputs,
arbitrary callbacks and slot interiors, the remaining Node/configuration
interpretation and general paper-step grouping remain open. Numeric scopes do
not authenticate independently constructed hosts with colliding identities.
At that batch the engineering estimate stayed **75% (71–81%)**: it reduced uncertainty in C/E/F
without claiming that their remaining obligations or R2 acceptance have closed.

Historical evidence for the preceding realm/scope sources: **755 selected Verus checks**, zero errors,
complete crate compilation, **134 targeted Rust regressions**, the interleaved
example and workspace Clippy/Rustdoc with warnings denied passed. Four integrated
scenarios cover registered maps/anchors through input changes and replacement,
actual host Begin despite changed bookkeeping, foreign same-number group scopes,
and retirement invalidation. **Seven strict compiling mutants** were rejected at
their named contracts, including four new realm/anchor/scope controls and three
affected registration/capture controls. All **238** canonical mutation/diagnostic
anchors pass preflight. Whole-kernel proofs, full development acceptance, full
negative regression/calibration, Node runtime, benchmarks and release/platform
acceptance were **not run**. Earlier evidence below is historical, not a substitute
for checks on these sources.

Review: [`realm_context.rs`](../crates/cordis-kernel/src/realm_context.rs),
[`plugin_registration.rs`](../crates/cordis-kernel/src/plugin_registration.rs),
[`native_values.rs`](../crates/cordis-kernel/src/native_values.rs),
[`setup_context.rs`](../crates/cordis-kernel/src/setup_context.rs),
[`effect_work.rs`](../crates/cordis-kernel/src/effect_work.rs),
[`native_slot_runtime.rs`](../crates/cordis-kernel/src/native_slot_runtime.rs),
[`runtime.rs`](../crates/cordis/src/runtime.rs).

## Shared Begin context and effect admission

`NativeEpisode` now owns an `Arc<NativeContext>` containing its actual Begin
ticket, work domain, provision ports and committed bindings (with registered
realms and anchor added by the batch above). The verified
`setup_context` / `native_context` entries return that immutable metadata with
an exact correspondence to the existing `Capture`; it contains no slot or user
payload references. Closing an Episode releases its slots while escaped metadata
continues to describe the old Begin, including after a replacement provider appears.
Metadata is not permission to acquire resources: the real Execution still checks
its phase and the source group's admission state.

The production `AsyncSetup` holds its scope (previously a group number) and an `Arc<SharedEpisode>`.
That allocation contains the immutable host context and the mutex-protected
execution together. Cloning and creating an effect scope share it, instead of
copying realm maps, owner IDs, bindings and declarations into every handle.
Native ownership/declarations come from the kernel-issued context; static
embeddings retain their explicitly supplied `External` metadata.

`AsyncSetup::effect` calls `Execution::enqueue_native_effect` on the native path.
The caller supplies the source group, fresh queue domain and iterator payload;
the kernel reads the **Begin bindings** itself. Its success contract identifies
the actual new queue and exact payload, preserves every existing queue and sets
the new queue's committed bindings to the capture. Rejection returns the original
payload and execution unchanged. The general `enqueue_effect` API remains for
callers supplying their own binding contract; it is not the native adapter path.

The existing production service checkpoints now export `context_observed`.
`context_correspondence` connects the captured Begin/work identity to actual
work and cleanup membership in that same certified epoch.
`effect_context_correspondence` connects an admitted queue's committed providers
to its real history record; `committed_between` proves that subsequent queue,
value, failure and retry interleavings preserve those providers. Historical queue
records do not imply that a retired group is still live. These links refine the
existing committed-dependency and iterator contracts of Definitions 58/63;
they do not replace general paper-step grouping.

The actual `retry_controlled_execution` wrapper also exports that success enables
the returned lifecycle cleanup reply and leaves no failed cleanup queues.
Rejection preserves the actual execution and lifecycle state as well as control.
These guarantees are propagated from the existing checked retry implementation.

The batch above now connects registered realm/anchor metadata and callback
scoping. Remaining context boundaries include ordinary host allocation/Mutex/Weak
association, diagnostics, other identity namespaces and static embedding inputs. Co-location
removes independently copied context fields; it is not a new pointer-identity
axiom or a proof of arbitrary callback execution. At that batch R2 remained **75% (71–81%)** as
an engineering estimate; no canonical obligation is closed by this batch alone.

Historical evidence for that preceding source revision: **735 selected Verus checks**, zero errors, complete
crate compilation, **87 targeted Rust regressions**, the interleaved example and
workspace Clippy/Rustdoc with warnings denied passed. Coverage includes native
Begin/replacement, nested and escaped setup, retry cleanup, static embedding,
waiters and reversible effects. Two scenarios were added and the existing full
failure/retry/replacement scenario was extended to retain metadata through slot
release. Seven strict compiling mutants were rejected at their exact contracts,
including wrong context owner, substituted effect bindings and the affected
capture/publication/retry boundaries; all **234** canonical anchors pass preflight.
An earlier 684-test kernel/driver/host run passed before the final lint-only
annotation; it is retained separately, not reused as final-source acceptance.
Whole-kernel proofs, full development acceptance, the complete final-source Rust
suite, full negative regression/calibration, Node runtime and release/platform
acceptance were **not run**.

Review: [`native_values.rs`](../crates/cordis-kernel/src/native_values.rs),
[`setup_context.rs`](../crates/cordis-kernel/src/setup_context.rs),
[`cleanup_interval.rs`](../crates/cordis-kernel/src/cleanup_interval.rs),
[`native_slot_runtime.rs`](../crates/cordis-kernel/src/native_slot_runtime.rs),
[`runtime.rs`](../crates/cordis/src/runtime.rs).

## Episode association and actual polling control

`Mounted` no longer stores independent `failed`, `cleanup_failure` and `restart`
fields. Its `PollControl<CallbackError>` owns the actual first error payloads,
restart intent and current Begin identity. Changes produce `Control` events in
the same Journal as values, slots, native lifecycle, work and cleanup. The driver
uses `poll_flags()` from this owner; availability remains a separate host input.

The production adapter calls the composed kernel entries:

| Entry | Guarantee on the actual execution |
| --- | --- |
| `begin_controlled_execution` | Reject failed, already-bound or wrong-plugin controls; bind the returned Begin ticket, work domain and real cleanup membership. The shared guard checks the native owner and membership records in the same epoch. |
| `request_restart` | Check the real registered phase and retirement state; clear setup failure but preserve cleanup failure, current Episode and retained payloads. Restart is intent, not cleanup completion. |
| `retry_controlled_execution` | First admit the actual cleanup retry. Rejection retains the entire control; success clears only cleanup failure and returns the new ticket, whose action is the actual prior allocator counter. |
| `release_controlled_execution` | First release the matching actual Episode. Only successful Unload unbinds it and clears restart; failure retains the control and its errors. |

`control::begin_binds_actual_members` derives the native/cleanup association from
a certified trajectory. `Runtime::plugin_execution_snapshot` now certifies the
actual control alongside the native owner, work, cleanup and managed slots in
one read epoch. These implementation events connect to the existing lifecycle
rules and Definitions 58/63; they do not add paper axioms or prove general step
grouping. Error reporting retains opaque callback results, not a proof that the
callback or external resource behaved correctly.

Each native handle also carries its actual Begin/work identity. The checked
initialization and retirement entries reject a foreign origin without assuming
that origin belongs to the Episode. At that batch, matching numeric identities still left the exact
Journal/membership association as a conditional API premise. The
[Execution-owned status](#execution-owned-shared-effect-status) now removes that
premise at the actual effect initialization and retirement entries. The ordinary
host effect-polling path additionally keeps a **Weak reference to the exact shared Episode allocation**
and rejects a mismatch before polling, cancellation or error forwarding. A clone
keeps that association; an escaped old handle cannot bind a new allocation. Weak
ownership neither retains the Episode payload nor creates a cycle through a
group's handle. The tests independently corrupt the origin and the shared
allocation to exercise both checks.

This separates a remaining uncertainty precisely: the pinned Verus library does
not specify `Arc`/`Weak` pointer identity comparison. The host identity gate is
real Rust code with regressions, **not a Verus proof of arbitrary mutex aliasing**.
No unchecked identity axiom was added. The constructors, immutable provenance,
checked transitions and current-state projection are verified under their stated
premises. Complete `AsyncSetup` context interpretation, generic payload/slot
interiors, callback semantics, scheduling, and the Node/configuration composition
remain open. At that batch R2 stayed at **75% (planning range 71–81%)**; this is engineering
progress within C/E/F, not closure of another work package or paper-proof coverage.

In the preceding Episode/control batch, **723 selected Verus checks** passed with zero errors and
complete crate compilation. **682 Rust unit/integration/doc tests** passed across
the kernel, driver and Rust host with all features; five scenarios were added.
The interleaved example, workspace Clippy/Rustdoc with warnings denied and format
checks passed. Four strict compiling mutants were rejected at named contracts:
clearing cleanup failure on restart, binding another cleanup member, clearing
failure on rejected retry, and accepting a foreign handle origin. All **232**
canonical mutation/diagnostic anchors pass preflight. Whole-kernel verification,
full negative regression/calibration, complete development acceptance, Node
runtime and release/platform acceptance were **not run**. These are historical
results for that batch's source; current context-batch evidence is above.

Review: [`poll_control.rs`](../crates/cordis-kernel/src/poll_control.rs),
[`control_execution.rs`](../crates/cordis-kernel/src/control_execution.rs),
[`host_status.rs`](../crates/cordis-kernel/src/host_status.rs),
[`native_slot_runtime.rs`](../crates/cordis-kernel/src/native_slot_runtime.rs),
[`runtime.rs`](../crates/cordis/src/runtime.rs).

## Actual shared handle status in the execution trajectory

`EffectHandle` and `ServiceHandle` now read their **actual semantic fields**
from `host_status::HostStatus<CallbackError>`. A shared checked cell holds progress
flags; the exclusive payload owner holds the actual error vector, first terminal
error and external Child identity. Erased linear permissions connect them. Each accepted change commits a `Host` record to the
native episode's existing Journal. No second status table mirrors these fields.
The common record projects error count/terminal presence; the typed owner proves
exact error append and retention, without interpreting an external error's truth.

`Execution::effect_status` binds the handle to an existing live effect queue.
The ordinary host installs it under the Episode mutex before returning the handle.
Cancellation records a request; the scheduler still has to cancel the actual queue.
It cannot declare initialization or completion. `initialize_effect_status` checks
the real queue is settled and has no pending poll. `retire_observed_effect` consumes
the actual checked-out runner through `retire_with_status`, shared with raw
`retire_effect`, then commits completion.
Pending work, retained inverse failure and mismatched group/domain leave both the
runner and status unchanged. Its success contract includes an earlier removal of
that exact group in the same history; `host::checked_completion` also proves the
retired group stays absent through later interleaved events.

Completion means retirement under the queue's cleanup policy. `RetainFailure`
blocks retirement until resolution; `DrainConsumed` can retire a consumed failed
callback while retaining its error, so `finished()` does not imply a successful
`join()` or prove an external resource was released. This connects handle
observations to the existing iterator/cleanup control projection of Definitions
58/63. The new host-status events are implementation extensions, not additional
paper axioms: effect initialization is not the owner's L-Finish, effect retirement
is not the owner's L-Unload, and general paper-step grouping remains open.

Service-child initialization/removal and terminal errors remain explicitly named
**host reports**, distinct from checked effect completion. A terminal report
does not set `finished`, preserves the first terminal error and rejects a later
service-finished report. Reporting service completion cannot finish an effect.
`EffectHandle::execution_snapshot` and `ServiceHandle::execution_snapshot` certify
the real status in its domain. Static/external service statuses have a separate
domain; native statuses share object, slot, lifecycle, work and cleanup history.
The history is erased rather than retained as an executable audit log.

Lock order is Episode mutex → status mutex → checked cell → Journal for compound effect steps;
handle-only operations take status → checked cell → Journal. Neither path acquires a host lock
while holding Journal. Waker invocation, user callbacks and rejected error
destruction occur after unlocking. Waiter IDs/wakers, driver/notify callbacks,
ordinary `Arc<Mutex<_>>` association, remaining host fields and arbitrary
root/Child bodies retain the boundaries described in the Episode/control section
above. The Execution invariant now supplies exact effect-status Journal/membership
association; the whole Episode's ordinary shared-allocation relation and scheduler
fairness remain open.

The integrated scenarios cover an in-flight cancelled effect and late inverse,
concurrent cloned-handle observations, wrong-group rejection, a retained failed
inverse with stale/fresh replies, actual scalar interference followed by retry,
and terminal service failure. The **previous handle-status batch**, on its own
source snapshot, passed **699 selected Verus checks**,
zero errors and full crate compilation; **198 runtime regressions** (four added
in this batch); the interleaved example; workspace Clippy/Rustdoc with warnings
denied; and formatting. Two strict controls reject cancellation that sets
completion and completion that skips real retirement. Each has a fresh matching
positive, complete mutant compilation and a named contract rejection. All **228**
canonical mutation/diagnostic anchors pass preflight. Whole-kernel verification,
full negative regression, full development acceptance and release/platform
acceptance were **not run**. Earlier counts describe their original sources.
At that batch R2 remained **75% (planning range 71–81%)**, with no additional work package closed.

Review: [`host_status.rs`](../crates/cordis-kernel/src/host_status.rs),
[`host_execution.rs`](../crates/cordis-kernel/src/host_execution.rs),
[`runtime.rs`](../crates/cordis/src/runtime.rs),
[`static_host.rs`](../crates/cordis/src/runtime/static_host.rs).

## Actual publication slots and captured commits

The typed service path now connects **the actual publication/import map, its
slot, the selected revision and the selected object** to the common execution
history. `Cell::capture` obtains a receipt from its real Journal member while
holding the slot lock. `Capture::wf` requires the receipt's slot key, source,
revision and object to match the actual captured `Arc`. A genuine receipt from
another slot cannot satisfy the contract.

`Capture::execution_snapshot` includes that exact selection commit in an
authentic Journal prefix. It uses the slot's domain, even after selecting a
foreign object. `slot::retained` proves source identity and monotonic revision
at every intervening event. Refresh or equal-object republication cannot rewrite
an old capture. Begin fixes a shared slot reference, not every later slot value.

`NativeServices::collect_slots` traverses every retained publication, including
ones hidden during restoration. The episode operation traverses actual owned
values and imports. Coverage follows from these real maps, not a caller's list.
`read_reversible` also exports the captured provider origin and source slot.
`NativeRuntime::service_snapshot` and `service_episode_snapshot` collect erased
receipts first, then certify them with native history, work and cleanup in one
Journal read epoch. Both production `Runtime` snapshot entries use them.

Each slot lock is released before the Journal read; that epoch never waits for
a slot lock. This preserves the writer's slot-then-Journal order. Aliases use
the same slot record; the final Journal determines its current revision.
Evidence creates no executable shadow map or payload owners. A checkpoint does
traverse actual tables and acquire short slot read locks; this is inspection
work, not work added to every plugin read/write. No callback or opaque payload
destructor executes inside these lock scopes.

The preceding slot batch passed **672 selected Verus checks**, zero errors and full crate
compilation, **194 runtime regressions**, the interleaved example, workspace
Clippy/Rustdoc with warnings denied and formatting. Three strict controls pass:
borrow another slot's commit, omit a published slot's evidence, or omit Begin
imports from collection. Each has a fresh matching positive, a completely
compiled mutant and rejection at its named contract. All **226** canonical
mutation/diagnostic anchors pass preflight. The integrated runtime scenarios
cover aliases, foreign slots and replacements, opaque payload lifetime, hidden
publications, failure/retry/stale replies and concurrent host checkpoints.
Whole-kernel proofs, full negative regression, R2 development acceptance and
release/platform acceptance were **not run**. Earlier counts below are historical
and are not reused as current-source acceptance.

The claim covers same-domain managed slots. Foreign slots remain explicit
references; a local slot selecting a foreign object does not prove that object's
writes in this domain. Opaque `Any` payloads, general effect/footprint semantics,
remaining host flags/escaped-handle association, Node/configuration composition,
and general paper-step grouping remain open. This does not establish scheduler
fairness. At that batch the engineering estimate stayed at **75% (71–81%)** because the remaining
R2 packages have not closed.

Review: [`value_slot.rs`](../crates/cordis-kernel/src/value_slot.rs),
[`native_slot_observation.rs`](../crates/cordis-kernel/src/native_slot_observation.rs),
[`native_slot_runtime.rs`](../crates/cordis-kernel/src/native_slot_runtime.rs),
[`joint_execution.rs`](../crates/cordis-kernel/src/joint_execution.rs).

## Native publication and complete typed history

`NativeRuntime::transition` now commits a single `Record::Native` containing
the real control state, episode owners, published port sets, Begin work domains,
captured bindings/import keys and provider origins. Begin adds exactly its
owner; Finish adds exactly its publication; Unload removes both. Other rules,
including Restart and Retire, preserve them. These changes share the same
Journal order as actual object writes, slot replacements, work and cleanup.

The generic `History<V>` still records the exact `NativePublication<V>`, including
its actual `Arc<V>` values and full Begin capture. Erased positions associate
each typed observation with its real joint commit. `project_step` checks the
projection; `History::interval` excludes an omitted native transition between
positions. An erased revision advances on every native transition, including
control stuttering. `Snapshot::complete_projection` proves that **every event
for this native member** is indexed, including the initial allocation and the
tail of the checkpoint. No caller supplies an expected history or publication.

`publication_has_finish` traces each retained typed publication to an actual
successful Finish. `publication_retained` preserves that exact table and capture
until its provider's successful Unload. `native::retained` proves the corresponding
owner/port/provenance retention across all intervening journal events, including
other objects' writes, cleanup failures and retries. Hidden during restoration
continues to mean retained; it does not mean released.

`NativeRuntime::publication_snapshot` exports this typed evidence.
`episode_snapshot` certifies the real native member, actual work owner and every
live cleanup group in **one Journal read epoch**. It checks the current episode
owner; its domain premise follows from native Begin and managed frame contracts.
The ordinary host now uses the slot-aware producer described above.
`Runtime::plugin_execution_snapshot(id)` uses the current
mounted episode while holding its existing mutex, and returns `None` before
Begin or after Unload. `Runtime::execution_snapshot` also uses the strengthened
publication checkpoint. No callback, destructor or value/slot lock runs inside
the Journal read epoch.

Typed histories, positions, revisions and old Arc references are erased. They
do not create a runtime event log or retain old service values. The native
checkpoint regression keeps all snapshots alive after Unload and confirms the
last service Arc can still be destroyed. The host regression observes actual
cleanup failure, retained dependency, retry and final removal through the new
entry. This batch's source-bound check results are recorded below.

The preceding publication/owner batch passed **648 selected Verus checks**, zero errors and full crate
compilation, **192 runtime regressions**, the interleaved example, workspace
Clippy/Rustdoc with warnings denied and formatting. Three strict development
controls passed: omit the native commit, record a false joint position, or omit
actual episode cleanup observation. Each requires a fresh matching positive,
complete mutant compilation and rejection by the named contract; resource
failures are not accepted. All **223** canonical mutation/diagnostic anchors
passed preflight on that batch's source. Whole-kernel verification, full negative
regression, complete R2 development acceptance and release/platform acceptance
were **not run** in that batch. Earlier counts below describe their original batches, not fresh
acceptance of this source.

This closes the native publication/owner history join, not the complete host
interpretation. The common record projects generic payloads; their exact typed
references remain in the indexed history. It does not interpret arbitrary Arc
interiors. The specialized managed-slot connection is described above. Shared host flags,
ordinary mutex association, arbitrary callbacks, Node versions/dynamic interfaces,
configuration transactions and general paper-step grouping remain separate
obligations. Finish/Unload preconditions still come from their existing checked
execution protocol; the new read checkpoint is not a new global drain protocol.

Review: [`native_execution.rs`](../crates/cordis-kernel/src/native_execution.rs),
[`native_history.rs`](../crates/cordis-kernel/src/native_history.rs),
[`native_runtime.rs`](../crates/cordis-kernel/src/native_runtime.rs),
[`execution.rs`](../crates/cordis-kernel/src/execution.rs).

## Live cleanup membership and guarded retirement

`CleanupGroups` now owns a private Journal member in addition to the members of
its queues. Its record contains the actual lifecycle origin, live group IDs and
queue keys/domains, the allocation high-water marks, sealed state and sticky
consumed-failure flag. The map is derived from the real `entries`; callers cannot
supply a smaller manifest. `Execution::observe_execution` certifies this record,
work and every live queue under the same read guard. Their keys are distinct.

The actual `add_iterator`, `remove`, `seal` and consumed-failure updates maintain
that record. A private queue checkout does not remove membership: `take` retains
the authoritative record and `put` must restore the same queue identity. This
also covers scalar dispatch, asynchronous completion, retry and iterator calls.

Removal and sealing use a bounded Journal write epoch. The actual held queues
are certified against the authority before the membership commit. Its transition
guard requires empty waiting work, no selected or issued action, no pending
stage, a settled continuation and no occupied payload slot. Seal checks **every
live group**. It cannot rely on a host-reported drain flag or a stale snapshot.
The lock is explicitly released before queue/runner payloads can be destroyed;
no plugin callback or nested value/slot lock runs under it.

`groups::checked_removal` and `checked_seal` extract these guards from an actual
certified history. Removed IDs remain absent throughout every later state of
that history; a sealed owner stays sealed and empty. Queue records remain as
history, so their presence no longer implies live ownership. Sticky consumed
failure survives removal and sealing. This connects the existing production
drain/release conditions to the common trajectory; it is not a new paper rule
or proof that arbitrary callbacks implement reversible effects.

The earlier membership batch passed 616 selected Verus checks with zero errors and whole
crate compilation, 165 runtime regressions, the interleaved native example,
workspace Clippy/Rustdoc with warnings denied and formatting. The new native
case exercises cancellation with an admitted stage, blocked removal, failed
cleanup, fresh retry, successful or consumed completion, group retirement and
final publication release, observing the same Journal between these steps.
At that source revision, all 221 canonical mutation/diagnostic anchors passed preflight; this is not a
fresh negative-verification run. Deferred controls should omit a membership
commit, omit a live queue from sealing, or reuse a retired ID. Whole-kernel,
full negative, R2 integration and release acceptance remain pending.

Membership evidence is erased, but this change does add a Journal reference
and write epochs on membership/failure changes, plus a metadata traversal at
seal. It makes no performance claim. Native publication/owner history now joins
this map as described above; remaining work includes shared host flags, general
callback/footprint interpretation, Node and configuration composition.

Review: [`group_execution.rs`](../crates/cordis-kernel/src/group_execution.rs),
[`cleanup_groups.rs`](../crates/cordis-kernel/src/cleanup_groups.rs),
[`joint_execution.rs`](../crates/cordis-kernel/src/joint_execution.rs),
[`execution.rs`](../crates/cordis-kernel/src/execution.rs).

## Issued responsibility at every intervening state

The actual `restore_value` producer calls `Evidence::establish_interval` before
returning. Its existing result contract now includes `interval::holds`, and this
contract reaches `Execution::dispatch_cleanup`. It proves, from the state just
after the real issue commit through the state just before acknowledgement:

- The same queue domain, selected ticket and already allocated attempt remain
  active and issued; the selected payload slot stays vacant.
- No intervening commit dispatches, retries or completes that queue's selected
  action. Other objects and independent queue fields may still change.
- The acknowledgement is the first completion of this issued action. Failure
  puts the exact original inverse back into its selected slot.

The payload identity comes from the real `pop` and typed result contracts. The
interval describes its outstanding **cleanup responsibility**. On successful
restore the Rust inverse is consumed before acknowledgement; the theorem does
not pretend that this Rust value stays alive afterwards.

`completed_attempt_stays_closed` then checks any later certified snapshot that
extends the actual acknowledgement history. The completed attempt stays inactive
at every later state and cannot receive a second accepted completion, including
after retry of the same slot. `interval::retired_at` exposes a particular state
or commit from this universal result. A failed attempt is also closed; retry
keeps the payload but must allocate a new attempt identity.

These proofs use the production `cleanup_step` rules and the real monotone
`CleanupJournal::next` counter. The existing commit checks connect those rules to
the executable queue. No second queue, runtime history, allocation or lock is
added. `Snapshot::valid_history` exports the closed snapshot invariant needed
for composition across modules. The result covers finite authentic histories of
arbitrary length; it does not promise that a callback will terminate or that a
scheduler will eventually retry.

The preceding scalar-interval batch recorded 597 selected Verus proofs with zero errors, 164 existing
runtime regressions, the interleaved native example, workspace Clippy and Rustdoc
with warnings denied, formatting and 96 negative-harness tests. Seven selected
controls require matching positive proofs, whole-mutant compilation and exact
named failures: three new interval/freshness controls and four retained producer, write and
no-action controls. The new controls acknowledge success before
running the inverse, reuse an attempt in the executable retry, and allow
old-ticket revival in the shared protocol relation. The last case checks a
specification change; it is not a claim of an existing runtime bug. All 221
canonical mutation/diagnostic anchors passed preflight. Those negative records
are not reused as current-source evidence after membership changes. Whole-kernel, full
negative-regression, R2 integration and release acceptance were not run.

Review: [`cleanup_interval.rs`](../crates/cordis-kernel/src/cleanup_interval.rs),
[`value_restoration.rs`](../crates/cordis-kernel/src/value_restoration.rs),
[`cleanup_completion.rs`](../crates/cordis-kernel/src/cleanup_completion.rs),
[`cleanup_journal.rs`](../crates/cordis-kernel/src/cleanup_journal.rs),
[`joint_execution.rs`](../crates/cordis-kernel/src/joint_execution.rs).

## Work and cleanup in the same trajectory

Native Begin attaches the actual `SetupWork` and root cleanup queue to the
runtime's Journal before returning the execution. Every later iterator queue
inherits that same Journal. Their private members must match their actual
fields after every checked mutation; missing the joint commit breaks `wf`.

`WorkState` records the lifecycle origin, domain, admission counter, root status
and failure, queued Child/group tickets, outstanding requests, and acquisition
and closure flags. `CleanupState` records committed bindings, pending/settled/
cancelled stages, the waiting stack, selected ticket and attempt counter,
failure, in-flight ownership and actual slot occupancy. `work_step` and
`cleanup_step` classify exact changes; payload identity and effect meaning
continue to use the existing typed contracts. A failed inverse retains its
original slot; retry advances the attempt; stale or duplicate confirmations
cannot complete the current action.

`Execution::observe_execution` holds **one journal read lock** while certifying
the work entry and every live queue, then releases it before returning.
`observe_execution_after` also proves extension of an earlier same-domain
program/value snapshot. `observation_ownership` proves distinct entries for work
and each live cleanup group. No caller assembles a supposedly coherent snapshot.
Standalone/static executions remain explicitly unlinked and return `None`.

Live cleanup membership/removal and native publication/owner projection now
have the joint contracts above. Exact captures remain in the indexed typed
history; arbitrary runner payload meaning and shared host flags remain open. The work/cleanup rules are implementation rules;
guard composition with the complete paper context remains open. In particular,
a value write and its queue registration are two ordered microsteps, not yet a
proved single paper step under every concurrent observation. The map retains
historical records after removal and does not prove physical resource release.
Snapshots do not prove arbitrary callbacks terminate or scheduling is fair.

Review: [`episode_execution.rs`](../crates/cordis-kernel/src/episode_execution.rs),
[`setup_work.rs`](../crates/cordis-kernel/src/setup_work.rs),
[`cleanup_queue.rs`](../crates/cordis-kernel/src/cleanup_queue.rs),
[`execution.rs`](../crates/cordis-kernel/src/execution.rs).
The [integrated regression](../crates/cordis-kernel/tests/registered_value_function.rs)
joins dynamic iterator allocation/retirement, real inverse interference,
retention, fresh retry, stale reply rejection and successful restoration.
`r2-joint-work-omits-commit` and `r2-joint-cleanup-omits-commit` test the two
recording obligations with compilable mutations. Full R2 acceptance remains open.

## One native execution domain

`Runtime::reversible_value(initial)` allocates an actual checked object in the
same execution domain as that runtime's lifecycle. Typed slots inherit their
initial object's domain. Object writes and inverses, successful slot swaps,
and native lifecycle transitions now commit through one `Journal`. The real
lock supplies their order; erased maps and persistent witnesses supply the
proof. `Snapshot::trajectory` starts with an empty map and constructs the
continuous classified trajectory without a caller-provided coherent heap.

| Actual mutation | Joint observation and interpretation |
| --- | --- |
| `Cell::record` | The exact operation/result/branch, rejected attempt, strict inverse or blocked restore updates its original object entry; other entries are framed. |
| `Slot::replace` | The same slot advances one revision and selects the supplied object's domain/key; retained captures and inverses keep their old object. |
| `NativeRuntime::transition` | Control, episode owner and publication projection take one checked native transition. Exact typed history is completely indexed; `Restart` remains an explicit extension. |

The common state is a **projection**, not a second mutable service store.
Logical member records remain after Rust handles drop; this map is not an
inventory of live allocations or a proof of memory reclamation.
Authoritative member tokens connect entries to the actual locked fields.
Value snapshots now carry a joint snapshot whose heap entry equals their real
value/depth. Cursor advancement and observation preserve both local and joint
history prefixes. Program reports carry that actual object's joint snapshot.
`Runtime::execution_snapshot` observes the real native publication/control entry in the same
domain. Snapshot refresh retains its actual Journal reference; equality of a
domain number alone is not used to substitute another history authority.

`Plugin::native_value_program(name, key, program)` stores `Body::Value(Function)`
directly in the real registration, for both roots and Children. It no longer
uses an opaque closure to associate that finite code with its plugin identity.
`NativeRuntime::run_value_root` reads the stored body and revision, revalidates
its finite code, selects the first matching **registered dependency port**,
authenticates the Begin-issued owner, and admits the real root ticket. Explicit
dependencies precede inherited aliases, so an isolated Child uses its own realm.
No caller supplies a replacement body, expected result or invocation-time port.

`Function::run` reads the episode's committed typed slot and registers each
successful prefix inverse in group zero. The checked dispatcher settles the
root from the computed result; overflow cannot be acknowledged as success.
`RegisteredReport` binds that result to the actual lifecycle/work ticket,
registration revision, code and port. Component membership at the root follows
over the existing finite scalar carrier and the actual registered declarations.
Opaque callbacks keep separate, version-checked dispatch.

`Member` now retains persistent evidence for its last real joint commit.
`Snapshot::projection` maps every local object event to an ordered position in
that same domain history. `ProgramReport::joint_steps` connects each executed
instruction, outcome and continuation to those exact positions;
`joint_rejection` covers the actual failed instruction. `Cursor::joint_steps`
does the same across interleavings. Combined with the registered report, this
connects **registered actor/body → real operation/result/inverse → joint trace**.
The positions and witnesses are erased, with no runtime event counter or log.

This does not establish arbitrary Rust/JS callback membership, a complete
host/resource interpretation in the joint map, or the paper's declared
object-footprint/frame theorem for every aliased port. Returned invocation
reports identify their own steps; not every joint event yet has a proved
registered actor. Numeric domain allocation and shared host mutex association
retain their existing boundary contracts.

The [interleaved example](../crates/cordis/examples/interleaved_program.rs) now
uses this factory and finite root/Child bodies. It still demonstrates slot
replacement, an old-object cleanup failure, dependency retention and retry.
Regressions exercise failed root prefixes, concurrent objects/slots/lifecycle,
wrong and repeated owners, stale recipe versions, isolated Child selection,
finite-body hot updates, and explicit rejection by the static host.

**Remaining uncertainty:** interpret shared Episode flags, generic slot interiors
and host resource ownership; then compose Node versions/dynamic interfaces and
loader transactions. The current joint map contains native control/owners/
publication projection, objects, slot selections, work tickets/status, live
cleanup membership and cleanup queue observations. Exact generic captures are
linked by the typed history, while the remaining host fields are not yet included. `Cursor::object_trace` remains the earlier
retained-view theorem, with its original coherent-view premise.

Standalone `ReversibleValue::new` creates an independent domain. A slot may
still accept an object from another domain; the joint observation retains the
foreign reference, and `resolve` returns `None` instead of inventing its state.
Calling the new factory is therefore necessary for this connected domain
scope; it does not migrate existing objects or include another runtime's
lifecycle automatically. Static and Node hosts are not covered by the new
native root constructor.

The journal adds real synchronization. Lock order is object/slot then journal;
the journal never acquires an object/slot lock or invokes a plugin callback.
History and proof tokens are erased, so it does not retain a runtime audit log.
Throughput, contention, scheduler fairness and termination are not established
by this proof batch. Selected checks are not whole-kernel, whole-R2 or release
acceptance.

Review: [`joint_execution.rs`](../crates/cordis-kernel/src/joint_execution.rs)
→ [`native_runtime.rs`](../crates/cordis-kernel/src/native_runtime.rs)
→ [`value_function.rs`](../crates/cordis-kernel/src/value_function.rs)
→ `Plugin::native_value_program` / `Runtime::reversible_value` in
[`runtime.rs`](../crates/cordis/src/runtime.rs).

The focused regression source is
[`registered_value_function.rs`](../crates/cordis-kernel/tests/registered_value_function.rs)
and [`reversible_runtime.rs`](../crates/cordis/tests/reversible_runtime.rs).
Selected negative controls substitute the stored finite body, falsely confirm
a failed run, misattribute a joint position, or omit an object/control commit.
Each selected probe requires a fresh positive, a compiling mutant and rejection
at its named contract. Full negative regression and R2 acceptance are separate.



## Risk-first connection: interleaved continuations and recovery

The highest-risk question is whether separately verified calls can describe
one actual execution when other plugins run between them. A snapshot with a
valid local history alone does not establish that another snapshot extends it.
The production `ReversibleValue` lock now retains an authoritative, append-only
ghost history. Each snapshot carries persistent evidence from that same
allocation. Acquiring the lock with a previous checkpoint proves prefix
extension; neither a second value with the same contents nor a fabricated
history can supply that evidence. All history and resource tokens are erased
from ordinary Rust execution.

`ValueProgramCursor`, created through the real `Setup`/`AsyncSetup` API, retains
the actual validated code, target, next instruction and episode/group identity.
`advance_value_program` authenticates that owner and current acquisition before
executing one stored instruction. Its actual result selects the continuation;
its actual inverse enters the same episode's cleanup queue before return.
Overflow leaves the instruction available for explicit retry. Foreign or closed
owners cannot advance it. Dropping a cursor does not discard previously queued
inverses. `observe` can include subsequent cleanup attempts without authorizing
new writes.

`Cursor::component` derives full-carrier membership from the actual stored
finite program. `Cursor::interpreted_trace` constructs a continuous scalar-table
trace containing all observed events, including other callers' writes, rejected
operations, blocked restoration and successful restoration. The cursor's own
steps occur at strictly increasing indices in that same trace, with the actual
outcome-selected continuation. It does not concatenate unrelated local logs or
assume that adjacent cursor calls were atomic.

Run the connected production probe:

```sh
cargo run -p cordis-verus --example interleaved_program --offline
```

The example mounts a real parent and Child. The Child's program runs one step,
another plugin writes, and the next comparison selects its unmatched branch.
Child cleanup restores the later steps, blocks at the earlier inverse, retains
the provider, then succeeds after the other writer restores and cleanup is
retried. It also rejects a foreign owner and a withdrawn owner. This is a
runtime witness for Child/control integration, **not a proof of arbitrary
Child callbacks or the entire host's joint trace**.

The aliasing gap exposed by this probe is addressed by the typed slot/object
connection below. The single-port scalar theorem remains only that projection;
it is not a full-observation frame theorem for aliased ports.

Review: [`shared_value_history.rs`](../crates/cordis-kernel/src/shared_value_history.rs)
→ `Snapshot::extends` / `ReversibleValue::snapshot_after` →
[`value_cursor.rs`](../crates/cordis-kernel/src/value_cursor.rs) →
`AsyncSetup::{start_value_program, advance_value_program}` →
[`interleaved_program.rs`](../crates/cordis/examples/interleaved_program.rs).
The canonical negative controls remove owner authentication, skip the stored
continuation or drop its registered inverse. Development probes require each
mutant to compile and fail its named contract; this is separate from full
negative-regression acceptance.

## Actual slot versions and shared object identity

The production native service table now stores the checked `ServiceSlot` sum.
Its `ReversibleValue` variant owns the actual typed slot under a verified lock;
non-scalar payloads now use the [checked shared owner](#shared-typed-payloads-in-the-actual-execution). The `Any` downcast in the Rust
adapter chooses the variant from the actual payload once. There is no shadow
object table, duplicated mutable value or extra runtime identity counter. That
downcast and the ordinary episode mutex remain host boundaries.

`NativeEpisode::read_reversible` reads the actual committed provider and slot.
`Execution::begin_native_value_program` composes this read with the same owner's
acquisition check and binds the actual code, port, provider, slot version and
object to the cursor. Callers cannot supply an expected provider or version to
that entry. Each advance still registers the inverse of that captured object.
`Setup`/`AsyncSetup::capture_reversible` exposes the same retained selection;
its version is diagnostic/provenance information, not a new lifecycle lease.

The slot's erased authoritative history records actual payload replacements.
`Capture::refresh` uses its own slot and proves prefix extension; earlier
versions keep their original object. `check_result` accepts a callback result
only if the observed current revision still matches the captured revision.
Replacing A with B and then A again does not make an old callback fresh.
Slot revisions track replacement, not writes inside the selected object;
predicate truth and arbitrary side effects remain external obligations.
Ordinary reads, dynamic `ServiceHandle` replacement and static typed slots all
use these checked stores. User predicates and arbitrary payload destructors run
outside their storage locks; replacing a payload returns the displaced Arc.

`value_heap.rs` separates port selections from allocation-keyed heap values.
Its interpretation is derived from a certified production snapshot, with the
allocation identity supplied by that snapshot. A write or restoration affects
every port selecting that object and frames the other objects. Slot replacement
advances every current selection of that same slot; a different slot may still
select the old object. Earlier captures, cursor targets and inverses stay fixed.
`alias_changes` explicitly proves why distinct port names are insufficient for
the old port-local frame when both expose the changed object.

This is an alias-aware **retained-view trace**, not yet one live observation of
the entire host. `Cursor::object_trace` takes a coherent binding/heap observation
as a premise. It does not combine reads taken at different times into an atomic snapshot.
The new native domain trajectory above joins actual object/slot/control commits
through its own common lock; it does not change this older theorem's premise. Consequently the port-keyed R1 Component/noninterference
theorems cannot simply be reused for arbitrary aliased ports. The common R2
interpretation must connect declared ports to actual object footprints and
derive those bindings from the full execution. Arbitrary root/Child bodies,
opaque/JS interiors and the shared episode remain additional open obligations.

The connected example now replaces the live slot with value 1000 while the
Child cursor and another port retain the old object. The cursor reaches 23,
cleanup blocks at 22, and retry restores 10 at depth 0; the replacement stays
1000 throughout. Dynamic publication replacement and equal-object
republication have separate integration regressions. New canonical negative
controls accept a stale capture, substitute the replacement payload, or read
the wrong realm. Selected development probes require a fresh positive, a
compiling mutant and rejection at the named contract; full regression and
whole-R2 acceptance are separate.

Review: [`value_slot.rs`](../crates/cordis-kernel/src/value_slot.rs)
→ `NativeEpisode::read_reversible` → `Execution::begin_native_value_program`
in [`value_cursor.rs`](../crates/cordis-kernel/src/value_cursor.rs)
→ [`value_heap.rs`](../crates/cordis-kernel/src/value_heap.rs)
→ [`interleaved_program.rs`](../crates/cordis/examples/interleaved_program.rs).

## Node admission through retained cleanup resources

The real `Driver::ready` and `NodeDriver::begin_checked` now call
[`node_admission.rs`](../crates/cordis-kernel/src/node_admission.rs). The checked
operation reads the actual lifecycle target, provider generations, publication
identities and accepted check cache. Its readiness contract is an equivalence;
it cannot satisfy the contract by always reporting unavailable. Begin also has
an exact success condition including actual target size and capacity.

Lease capacity is checked before Begin. After Begin succeeds, allocation of the
selected publication leases is proved to succeed. Rejection preserves control,
action ownership, payloads, revisions and the publication/lease registry; it
does not leave a partially acquired lease batch. Success creates an `Admission`
whose private manifest has precisely the providers committed by this actual
Begin and live leases tagged with the returned setup ticket's owner/generation.
Its erased capture retains the real source values, versions and selection facts.

`NodeRuntime` now retains this owner in its private admission map. The real driver
reads its resource slice; managed release derives the lease list and checks the
original domain/generation before consuming it. Rejection preserves resources,
and only successful release removes the retained owner. The same history now
includes preparation, seal, failure, restart, accepted completion and retry flags,
with actual error strings. It proves Begin provenance, retention until release,
and preservation under rejected replies. See the [Node review path](r2-node-execution.md).

The control projection proves L-Begin/L-Unload. Generation-zero preparation and
adoption, checked markers and dynamic interfaces are recorded explicit extensions.
JS predicate truth, object interiors, Fiber/function/HMR effects, remaining adapter
caches and cross-runtime interpretation still prevent whole-Node refinement.
Cached acceptance retains the existing explicit-notify policy; admission does not
claim the predicate is still true after a value change.

Review: `Kernel::{target, complete_target_facts}` →
`Availability::{ready, begin_setup}` → `Admission::{wf, value_provenance, finish}`
→ the real `Driver::{drive, complete}`. Historical control records are proof data;
neither this capture nor its source values add runtime history copies.

## Issued episode ownership and delayed root calls

The production `NativeRuntime` now records the setup ticket and work domain
actually issued at Begin. Its invariant gives every Loading, Active or
Unloading plugin exactly one current owner; Inactive and removed plugins have
none. A publication must belong to that owner. Root admission and invocation,
Finish, withdrawal, settlement, failure, retry and Unload check the supplied
execution or invocation against this retained record. Editing opaque host
bookkeeping cannot replace it. Successful Unload removes it; failures and
retries retain it.

`RegisteredInvocation` also retains the admitted lifecycle ticket. Immediately
before invoking the stored callback, `NativeHost::call` rechecks the pending
setup action, current generation, Loading phase and retirement flag, in addition
to the existing owner/domain/recipe revision checks. A root whose invocation has
not started is rejected after withdrawal or retirement, and cannot execute in a
later episode even if its work domain is reused. Local work withdrawal also
closes new root admission. Already executing callbacks and their awaited results
still follow the existing completion protocol; this is not callback preemption.

The continuous native history now includes these actual owner records together
with control and publications. `owner_has_begin` proves that a retained owner
originated at a successful Begin. `owner_retained` proves that it cannot change
before that plugin's successful Unload. The owner changes accompany the existing
Begin/Unload control steps; admission checks and rejected invocations preserve
this observation. This strengthens the production projection without changing
the R1 interpretation or asserting a full-context correspondence.

Review the executable checks in
[`native_owner.rs`](../crates/cordis-kernel/src/native_owner.rs),
[`native_runtime.rs`](../crates/cordis-kernel/src/native_runtime.rs),
[`plugin_registration.rs`](../crates/cordis-kernel/src/plugin_registration.rs) and
[`native_host.rs`](../crates/cordis-kernel/src/native_host.rs), and the induction
in [`native_history.rs`](../crates/cordis-kernel/src/native_history.rs).
The `native_host` and `native_runtime` integration tests exercise delayed calls,
retirement, reused work domains, foreign executions and successful release.
Named negative controls remove the corresponding guards and owner updates.

Reproduce the focused runtime cases with the pinned toolchain:

```sh
cargo test -p cordis-kernel --test native_host --test native_runtime --offline
```

The shared `Arc<Mutex<Episode>>` still belongs to the ordinary adapter. These
checks authenticate its submitted numeric identity against the live registry;
they do not prove mutex scheduling, opaque argument semantics or allocation
identity when independent raw hosts deliberately reuse **all** identity numbers.
The shared driver now uses checked per-issuer allocation; choosing the common
namespace and ordinary shared ownership still require the host bridge. Arbitrary function
fields, slot interiors and the Node/native joint context still need their R1
interpretation, so R2 remains in progress.

## Begin provenance through publication and release

Every native episode now carries an immutable, erased `Capture`: the actual
control state, declarations, committed bindings, provider generations and
published slots observed when Begin captured its imports. `Capture::wf` proves
both directions of capture: an import exists exactly when a committed binding
had an available slot in that source table, and it contains that actual slot.
The snapshot comes from the production constructor, with no caller-supplied
expected values.

`Execution::capture_correspondence` connects this Begin observation to the
current work and native value owner. Its executable mutations preserve the
same capture, including Child/effect admission, poll landing, cancellation,
cleanup, retry and reversible value programs. While the episode remains open,
its imports equal the original captured imports. Finish carries that same
capture into the actual publication and hence the native joint history. Unload
returns exactly the originally captured imports and empties the closed owner;
it does not recapture today's targets during cleanup.

The value owner also stores its actual cleanup/work domain. Publication and
release compare it with the supplied work queue before changing either state.
A different work queue is rejected even when raw embeddings deliberately reuse
the same lifecycle domain, plugin ID and generation. This closes the work-domain
substitution gap; it does not make numeric domains allocation-identity tokens.
The shared driver and native cleanup domains now use checked allocation.
Shared episode mutex association and independent namespaces remain boundaries.
The complete R1 interpretation still needs to join those
shared owners, function meanings and Node publication versions.

The snapshots are ghost data: they add no runtime table copies, historical
allocations or extra `Arc` owners. A cross-thread regression retains an escaped
context through provider withdrawal, cleanup failure and retry, then checks
replacement and a fresh episode. It also checks exact `Arc` counts and rejects
use of the closed old context. A second regression exercises the work-domain
substitution guard at both Finish and Unload.

Review path: `native_capture.rs::Capture` →
`LifecycleState::capture_native_values` → `NativeEpisode::wf` →
`Execution::capture_correspondence` → `NativeRuntime::{begin_managed_execution,
finish_managed_execution,release_managed_execution}`. This strengthens the
implementation of committed dependencies and the native publication view in
(46), while preserving the original R2 exit criteria. Negative controls remove
the work-domain check, forget Begin's sources or replace the publication's Begin
control snapshot with the Finish state. Each must compile and fail its named
contract; scoped checks do not establish full negative-regression acceptance.

## Joint native registry and publication history

The production Rust `Runtime` now owns `NativeRuntime<R, H, V>` through
`NativeDriver`. Its registration graph and `NativeServices` live inside one
verified owner; callers no longer pass an independent store to Begin, Finish,
lookup or Unload. The actual entry points preserve one joint invariant:

- Every Active registration has a complete publication of its declared user
  ports, with its current episode generation and real shared value slots.
- Every retained publication belongs to a registered Active or Unloading
  provider. Retirement alone preserves it. Withdrawal hides it from new lookup
  while retaining its values for committed consumers and restoration.
- Finish checks the actual episode declarations against the stored recipe before
  publishing. Release removes only its own table after the real work and cleanup
  guards pass. Failures, retry, compaction, recipe updates and shared Child
  transitions preserve unrelated publications.

`NativeEpisode::matches_provisions` rejects even a supplied owner with colliding
numeric origins and a different declaration sequence. This is a concrete guard,
not a precondition placed on the ordinary Rust caller. The ordinary host's global
domain allocator remains responsible for separating runtime instances.

`NativeRuntime::history_correspondence` now proves a continuous joint history
of the **actual control state and retained publication tables**, starting empty
and ending at the current observation. The independent relation in
`native_history::step` adds exactly one provider's table at Finish, removes
exactly that table at Unload, and preserves every table in other control steps.
Observation-preserving calls retain the same history. Explicit Restart remains
an extension; a history without Restart has the strict paper-control projection.
The ghost history is erased from Cargo builds.

This joins the native implementation of the publication view in equation (46)
with L-Finish, L-Leave and L-Unload at the registry/slot boundary. It still does
not interpret `Arc` interiors, arbitrary callback bodies, the shared episode
mutex state or Node's publication versions as one complete R1 context. The
remaining R2 criteria are unchanged.

Review path: `native_runtime.rs::{linked,wf,finish_managed_execution,
release_managed_execution,history_correspondence}` → `native_history.rs::step`
→ `cordis-driver/src/native.rs` → `Runtime::poll_settle`.
Aggregate regressions cover complete publication, colliding declarations,
provider/consumer failure and retry, unrelated values, stale/foreign episodes,
recipe/bookkeeping updates, retirement, compaction and a shared Child with an empty publication. Three negative controls
remove the declaration guard, discard unrelated publications or omit a joint
history transition; each requires a compiling mutant rejected by the named
contract.


## What now runs under a contract

| User-visible behavior | Executable contract | Production caller |
| --- | --- | --- |
| A publication owns the value actually supplied by its owner | `PublicationStore::publish_checked` checks the real lifecycle domain, generation and admission, then stores the actual generic payload | `Driver::publish` → `LifecycleDriver::publish_value` |
| Replacement keeps publication identity and returns the real previous value | `replace_checked` and `ValueCell::replace`; rejected operations return the new input intact | `Driver::set`, Rust `ServiceSlot::replace` |
| An old cleanup lease continues to read its own retained value | `leased_value` derives both publication identity and payload from the actual lease record | `Driver::read` |
| Release moves the real values only after lifecycle and full resource-manifest validation | `finish_resources` composes the existing receipt/lease protocol with actual payload transfer; rejection preserves all three states | `LifecycleDriver::finish_cleanup_values` |
| A factory is invoked with the actual argument before its Future is polled | `RegisteredPlugin::call` invokes the stored native `FnMut`; `invoke_future` retains the actual returned cleanup Future | Rust `Runtime::start`, `initialize_cleanup` |
| Async cleanup consumes the result its Future actually returned | `Awaiting::complete` / `await_completion` pair a captured origin with the native Verus `Future` output; `complete_future` derives success/failure/drain from that output | Rust `initialize_cleanup`, `Runtime::finish_reply`, `StaticCleanupFuture::complete_reply` |
| A landed inverse is retained before the continuation is selected | `CleanupQueue::land_result` allocates the token itself, stores the actual inverse and derives continuation from the result and cancellation state | `Runtime::poll_groups` |
| One empty group cannot authorize closing an episode with other work | `CleanupGroups` owns every cleanup queue; `remove` and `seal` check pending stages, issued receipts, retained failures and real payloads, then close registration | `Runtime::poll_groups`, `Runtime::poll_settle`, `StaticCleanupFuture::poll` |
| Bulk retry does not partially advance a set containing a nonretryable failure | `retry_execution` preflights the bound work and all queues, then advances the lifecycle and inverse attempts together | `Runtime::retry_cleanup` |
| Only the admitted native episode can finish or release its lifecycle | `begin_execution` constructs both bound owners; `finish_execution` and `release_execution` check their original ticket and current generation | `Runtime::start`, `Runtime::poll_settle` |
| Removing a group cannot turn consumed failure into successful restoration | `CleanupGroups` retains its accepted `Drained` summary; `release_execution` derives the final outcome from that summary | `Runtime::finish_reply`, `Runtime::poll_settle` |
| A Child retains its parent's actual dependencies across realm isolation | `register_plugin` resolves declared keys and inherits both original and child-realm ports, excluding the child's own provisions | `Runtime::mount_inner` |
| A hot update cannot substitute a new recipe for an already admitted call | `admit_registered_root` binds the actual work to the registration; `call` checks its domain, owner and recipe revision before invoking the stored `FnMut` | `Runtime::start` |
| A native Child inverse cannot retire the same numeric ID in another runtime | `ChildIdentity` comes from real registration; `retire_child_slot` reads that identity from its actual slot | `Runtime::poll_cleanup` |
| A late Child request cannot allocate after its pending inverse was consumed | `ChildSlot` is assigned once by `register_child_slot`; `retire_child_slot` closes a pending slot and allocation checks the original parent generation | `Runtime::mount_inner`, `Runtime::poll_cleanup` |
| An effect request cannot refer to a separately allocated or foreign group | `enqueue_effect` creates the real queue and binds the actual iterator; `activate` checks lifecycle origin and queue domain | `AsyncSetup::effect`, `Runtime::drain_requests` |
| A poll reply cannot be accepted for another group or current attempt | `EffectRun::admit/call/land` preserve the actual payload, argument and result with a private poll identity | `Runtime::poll_groups` |
| Recorded cancellation rejects new Child/effect acquisition while retaining landed inverses | `accepts_acquisition` reads the actual stage state; actual Ready inverses still land before continuation stops | `AsyncSetup::ensure_active`, `mount_request`, `effect` |

Native Rust service values additionally use `begin_native_execution`,
`NativeEpisode::provide/read`, `finish_native_execution` and
`release_native_execution` through `Runtime::poll_settle`, `AsyncSetup` and
`NativeDriver`; see the native service section below.

The Node store's payload is its actual `u64` JavaScript value handle. The Rust
value cell holds its actual `Arc<dyn Any + Send + Sync>`. Neither contract
interprets mutable JavaScript object fields or a Rust value's interior mutation.
Payloads need no `Clone`, `Copy`, `Debug` or equality implementation. A lease pins
a publication identity, not an immutable snapshot: replacing that publication
changes the value its leases read; a newer publication has a separate identity.

The cleanup adapter preserves the existing policies. A failed retryable factory
remains retained. Ordinary Rust may report a consumed, nonretryable failure as
`Drained`; the static host uses `RetainFailure` and remains blocked. Neither is
silently reported as successful restoration. Discarded factories and rejected
payloads leave the bookkeeping mutex before destruction, so user `Drop` can
reenter the host.

## Relation to the paper

`publication_projection.rs` interprets the actual store as a key/value lookup
table. `publish`, `replace` and `revoke` call its proofs in their own bodies:

- Publication inserts the supplied value at a previously absent visible key.
- Replacement updates that key and returns its actual previous value.
- Revocation removes only that publication's visibility. Repeating it cannot
  hide a newer publication of the same key.
- Lease metadata changes and reclaiming an already revoked value preserve
  current lookup. The retained lease observation is separate and can change.

This is the registry's visibility projection. Host phase, dependency and
availability checks impose additional conditions on service lookup; this table
alone is not the complete host observation.

These are concrete instances of the key-local updates in §3.4, represented by
`coeffects::put`. They are not equality between a multi-version host registry
and R1's entire reified context. Restoring the returned old value recovers a
single replacement; this does not by itself establish a plugin's complete
inverse law under interference.

`LifecycleState` now propagates actual parent/dependency/provision arguments
through insertion, committed bindings through Begin, and the existing control
step relations through Finish, Retire, Remove and Unload. Compaction preserves
the control observation. Explicit restart and dynamic interface changes retain
their separately specified extension contracts.

`land_result` proves the accumulator projection of Iter, Finish or delayed
diversion together with the real payload update. That projection does not
interpret an opaque inverse function's external effects. A failure or explicit
group cancellation is still a host extension where the original paper does not
provide the corresponding guard.

## Async proof boundary

For the Future passed to `await_completion`, Verus proves that a returned
completion contains that Future's actual output and the origin supplied when it
was wrapped. This proof is conditional on returning; it proves neither eventual
completion nor scheduler fairness. A constructor-free `Completion` prevents a
receiver from replacing its fields, but it is not an authenticity token for
external I/O: a caller can wrap an immediately ready Future.

`invoke` establishes `callback.ensures((actual_argument,), actual_result)` by
calling that callback. `invoke_future` invokes the factory immediately and keeps
its returned Future; it does not delay factory side effects or panic handling to
the first poll. The native setup entry now uses the stored `FnMut` directly through
`RegisteredPlugin::call`; cleanup factories use `invoke_future`. The iterator
entry now uses `EffectRun::call` and its private poll reply, as detailed below.
No expected result is supplied by the adapter. The checked
`witnessed_invocation` and `witnessed_completion` callers instantiate the data
flow with executable code.

A checked caller must establish the callback's `requires`, and a checked plugin
must prove its own effect law. Ordinary Rust/JavaScript plugin bodies remain
outside that proof. Native
registration and invocation are now connected as described below. This does not
establish a plugin's inverse law, the complete host interpretation, or arbitrary
external I/O truth.

## Composition now owned by the kernel

`CleanupGroups<T>` replaces the host's mutable map of individually verified
queues. Its fields are private and it exposes no mutable queue reference. A
mutation preserves all other groups. Removed queues leave the active map; only
monotonic identity counters survive, so storage and drain scans follow live
groups instead of the number of groups ever created. Live and removed group identities cannot
be substituted by reusing a domain. Sealing inspects all queues, so an empty root
cannot hide another group's pending stage or issued cleanup. A cancelled stage
must land before its group can be removed; any returned inverse remains owned.
A failed bulk-retry preflight changes no group. Successful sealing proves that
no owned queue retains a payload, issued callback or pending stage, and closes
all subsequent registration in that container.

This composition is used by both the polled Rust runtime and the static adapter.
The SetupWork protocol below further connects root dispatch and actual queued
requests. Native lifecycle admission and release are now composed with those
owners as described below. Native values now join Begin/Finish/Unload as described
below. Shared native Child request/inverse handles now have the checked pairing and
synchronization described below. A joint invariant for the complete host observation
remains open; these local compositions do not discharge that whole-state obligation.

## Setup and requests participate in drain

`SetupWork<C, G>` owns actual Child/group requests and tracks root setup plus
requests already dispatched to a host. `WorkItem`, `PendingWork` and `WorkReceipt`
have private payload and identity fields. `run` produces a receipt by actually
calling the operation on the owned request. `start` immediately calls the
factory and retains its returned Future; completing that Future produces the
actual result. An empty dispatch queue cannot hide a request still being
executed. The FIFO uses VecDeque, avoiding movement of remaining requests on
each dispatch; completed receipts leave the active map.

`enqueue_native_child` constructs both ends of a native Child request; the generic
`enqueue_owned_child` also retains externally supplied request/inverse pairs
atomically, returning both unchanged on rejection for disposal outside the host
mutex. Final `seal` checks root setup, queued/dispatched requests and every
cleanup queue, including their common cleanup domain. Rust Runtime and the
static host use this guard. The polled Runtime's initialization completion also
uses the same actual state.

An unpolled root Future may be cancelled after withdrawal. A started Future
must return or remain explicitly abandoned and blocking; it cannot take the
unpolled cancellation path. Async completion preserves the actual Result, and
failure cannot authorize successful initialization. The checked normalization below now preserves actual poll results and maps caught
panics only to failure; performing the poll and catching the panic remain ordinary Rust. The invocation relation also does not replace a plugin's effect laws or the
full semantic relationship between Child request, shared handle and inverse.

## Registered recipes and native Child operations

`NativeHost::register` and `register_child` call `LifecycleState::register_plugin`
and `register_child_slot` from `Runtime::mount_inner`, including actual dynamic
Child allocation. It consumes the actual `PluginDefinition`,
reads the parent's authoritative kernel declarations, resolves keys in the
supplied realm map, and performs the real insertion. The returned
`RegisteredPlugin` owns the actual callback, resolved interface and reserved
anchor. `NativeHost` retains it together with the actual `Mounted` payload;
ordinary host code no longer performs a second registration-map insertion.

Its contract proves both the exact success domain and the resulting interface.
An inherited dependency keeps its original port and its child-realm port,
without introducing duplicates or an inherited dependency on the child's own
provision. Duplicate declared keys and conflicting reservations are rejected.
Registration does not require dependencies to be available: that remains a
Begin condition. Failure preserves the lifecycle state and returns the original
definition and callback. The stricter parent policy, realm mapping and synthetic
anchor are explicit host conventions around the paper's Insert control rule.

`admit_registered_root` checks the real pending setup action, current generation,
registration domain and owner, then issues a private invocation containing the
actual argument and recipe revision. `RegisteredPlugin::call` checks that
identity and directly calls the stored `FnMut`. It accepts neither a replacement
callback nor an expected result. Its native Verus call contract relates the
registered function and actual argument to the returned `WorkReceipt`.

`WorkReceipt::dispatch` distinguishes the factory's actual `Ready` result from
its actual `Pending` Future, preserving the issued root identity in both cases.
The factory still runs immediately; only the returned Future is deferred.
Synchronous completion and conditional async completion reach the existing
root/drain protocol. A caught panic uses the failure-only entry. The native
Runtime uses this path, while the static adapter uses the same result dispatch
with its existing external registration boundary.

Recipe replacement retains plugin identity and advances a checked revision.
A call admitted before replacement is rejected without invoking either recipe.
Already-started Futures retain their original completion identity. Batch recipe
updates preflight all required revision increments before changing a recipe;
old captured values are dropped after installation.

A successful child registration also produces a private `ChildIdentity` carrying
its actual runtime domain, parent and allocated ID. Native cleanup stores this
identity and calls `retire_child`, which proves a Retire control step for that
child. Repeating it after removal is a state-preserving operation; it cannot
retire a later replacement or a foreign runtime's equal numeric ID. Retirement
is a request to withdraw the child, not proof that its resources have finished
restoring. The existing cleanup and removal guards remain necessary.

The shared native handle now contains a private `ChildSlot`, constructed from
its actual `SetupWork` lifecycle origin. `register_child_slot` checks the runtime
domain, parent generation, live parent phase and pending state, executes registration, and writes
exactly the returned child's identity. It accepts no separately reported
successful ID. A duplicate, failed, cancelled or obsolete request allocates
nothing and returns the original recipe. A failed allocation leaves the slot
pending until the host records the actual failure through `reject`; that
failure-only entry cannot overwrite a successful assignment.

`retire_child_slot` reads the assigned identity itself. If the inverse is
consumed before allocation, it marks the slot cancelled: a later request cannot
create an unowned child. Failed and cancelled slots have no child to retire.
Repeated retirement of an assigned slot keeps its identity, including after
removal. The native Runtime now calls these operations through `SharedChild`,
whose synchronization and pairing are checked below. Rejected recipe captures
and subsequent host retirement callbacks run after releasing its lock. The static
adapter keeps its explicit external allocation-acknowledgement protocol.

These contracts connect real allocation and registered function invocation.
The shared Child protocol below removes another ordinary-host assumption, but
publication/context observations, callback/panic adaptation and concrete plugin
effect/inverse laws still need their complete semantic composition. Registration
storage and lifecycle membership have the joint invariant described later.
Global uniqueness of domain and service-key allocators remains a host boundary.

## One shared Child for its actual request and inverse

[`shared_child.rs`](../crates/cordis-kernel/src/shared_child.rs) closes the native
request/inverse aliasing and synchronization gap:

- `enqueue_native_child` receives only the real request payload. It constructs
  one `SharedChild` from the actual setup action, puts that same handle in the
  queued `NativeChildRequest` and the retained `ChildCleanup::Native`, and returns
  an observer for it. Admission has an exact success condition; rejection returns
  the original payload and changes neither queue. No caller-selected inverse
  handle participates in this native entry point.
- The private `vstd::rwlock::RwLock` owns the actual `ChildSlot<()>`. Its invariant
  binds the slot to the runtime, parent and episode. Registration, failure and
  retirement acquire exclusive access; observations acquire shared access.
  `register_shared_child` states success **if and only if** the state observed
  under that lock and the real registry satisfy the allocation guard.
- Each terminal decision carries a persistent `GhostMapAuth`/points-to witness.
  The witness is tied to the actual slot mutation, not a separate expected log.
  `ChildSnapshot::terminal_agrees` proves that two terminal observations of this
  shared slot cannot disagree. `cancellation_precludes_assignment` combines a
  real Cancelled observation with any later observation: it cannot be Assigned.
  Together with the actual registration result contract, a completed pending
  inverse excludes a later successful allocation, even across lock acquisitions.
- Each operation returns its actual before/after observations and releases the
  lock before returning. The Runtime uses this entry point for dynamic children;
  already registered native children enter through `from_identity`, retaining
  their actual identity. Retire remains distinct from Remove and resource drain.

This connects the paper's Child allocation/Retire inverse and the control-step
projection of Definitions 58/63 to the real queue payload and shared state. It
is not a new paper rule or the complete R1 Child interpretation. No claim is made
that arbitrary plugin effects, the complete host observation or Theorem 64 have
therefore been proved.

The synchronization proof uses the pinned vstd lock/resource contracts and the
standard `Arc` clone contract. The kernel check does not reverify vstd or Rust's
standard library. The lock uses spinning and does not establish fairness,
starvation freedom or global deadlock freedom. Critical sections invoke no user
callback. Only scalar lifecycle data lives in the lock; vstd's lock has explicit
release and no automatic payload destructor, so error strings and captures stay
outside it. Host diagnostics, panic adaptation and the other Runtime locks remain
outside this shared-slot proof. No dependency or toolchain version was added.

## Lifecycle admission through actual release

`LifecycleState::begin_execution` performs the real Begin and constructs both
`SetupWork` and `CleanupGroups` with that setup action's domain, owner,
generation and action identity. Their origin fields are private and immutable.
An unbound owner with the same numeric cleanup domain cannot substitute for the
admitted queues. The ordinary `LifecycleDriver` still allocates globally unique
domains; uniqueness of that atomic allocator is a host boundary.

The native Rust Runtime uses these checked operations throughout its episode:

- `settle_execution` waits for the real root, dispatched Child/group requests
  and pending stages before acknowledging the original setup action.
- `finish_execution` also checks the actual current target and all groups before
  the real Finish transition. A failed Finish may acknowledge completed setup;
  it cannot change the kernel state or publish an Active service.
- `fail_execution` requires a retained queue failure and no admitted work or
  issued cleanup still in flight. It retains the lifecycle obligation and
  committed dependencies.
- `retry_execution` preflights all queues before changing the lifecycle attempt,
  then advances their retry tickets together. A rejected retry changes neither.
- `release_execution` checks the bound origin, current generation, restoration
  phase, outstanding lifecycle action, root/requests and every cleanup queue.
  It derives `Succeeded` or `Drained`, consumes the action, seals both owners and
  performs the real Unload. Rejection preserves all three states. Success proves
  the owner's committed dependencies have been released and it is Inactive.

The host no longer chooses an aggregate success flag or maintains a separate
`cleanup_drained` Boolean. The checked group owner records accepted consumed
failures and preserves that fact through removal, retries and sealing. A new
episode starts with a new origin and an empty failure summary. Synchronous Child
results use `complete_result` and the same checked outcome policy as Futures;
Child allocation/retirement and the slot transitions now have the contracts above,
including the shared native request/inverse pairing and slot synchronization.
The ordinary callback/panic adapter and full host observation still need their
semantic correspondence proofs. Low-level APIs accepting explicit reports
remain available for external-host protocols; a report is not proof of an
external effect.

The Begin, Finish and Unload contracts relate these calls to the existing paper
**control projection**. They do not yet prove the full R1 value/code/continuation
interpretation, complete Child effect or production trace. Static/Node
bridges retain their own external completion boundary; this native composition
is not automatically a proof of every adapter.

## Native service values join admission, Finish and Unload

`native_values.rs` now owns the native Runtime's actual publication registry and
its episode-local service slots. `begin_native_execution` performs the real
Begin and creates the bound `SetupWork`, `CleanupGroups` and `NativeEpisode`
together. There is no public constructor that recaptures a second value owner
from an existing work ticket. Domain checks and a stale publication check run
before Begin; rejection leaves control unchanged.

The private capture reads the kernel's actual committed bindings and clones the
actual stored `Arc<ServiceSlot>` for each available binding. Its contract proves
both directions: every retained import belongs to a committed provider of the
current generation, and every available committed slot is retained. Unrelated
services acquire no implicit owner. Realm and provider identity remain part of
the lookup key. The snapshot preserves slot referents; it is not an immutable
copy of the contents of an interior-mutable service.

`NativeEpisode::provide` accepts a declared, absent key and stores the actual
input. Rejection returns that input intact. Its `owned_table` projection proves
the same key-local `coeffects::put` update as §3.4, while preserving imports and
other keys. This is the episode's local table, not the whole R1 context.
`read` selects only an owned provision or an actual captured binding. The global
`visible` lookup additionally resolves the current Active provider and checks
its generation. Withdrawal can therefore hide a publication from new calls
while existing cleanup still reads its original committed slot.

`finish_native_execution` requires all declared service values, the same
originating work and groups, and the real Finish guard. It commits Active and
publishes the actual owned slots in one checked call. Runtime no longer copies
all published slots on every Active scheduler pass. In-place `set` continues to
update the shared `ValueCell`; this change makes no benchmark claim.

`release_native_execution` checks the matching value/work/publication origins,
then runs the actual drain and Unload protocol. A rejection preserves lifecycle,
work, groups, registry and episode values. Success removes exactly that owner's
publication, closes further episode reads and writes, and returns its actual
owned, imported and published slots. The host drops them after releasing its
bookkeeping mutex, including for cancelled partial setup. Retained cleanup
failure cannot take this path; a retry must satisfy the existing fresh-ticket
protocol. Already returned user `Arc`s remain ordinary references, not revocable
leases.

The proof uses Verus's standard `Arc` referent and cloning contracts. It does not
prove mutex synchronization, reference-count implementation, mutable service
contents, or arbitrary availability callbacks. Static/Node embeddings keep their
explicit external-host contracts. Low-level lifecycle APIs remain available and
do not themselves maintain this native composition. The production native adapter
now uses `NativeHost`, which exposes no mutable lifecycle or registration map.
Shared Child handles, the meanings of host bookkeeping fields, and the complete
host interpretation still need the global semantic invariant.

## Registration and lifecycle have one owner

`NativeHost<R, H>` owns the real `LifecycleState` and the actual map of
`RegisteredPlugin<R>`/host-payload pairs. It replaces Runtime's separate
`BTreeMap<PluginId, Mounted>`. Its `wf` contract establishes, for every entry:

- Map membership is exactly the paper control projection's registered set.
- The stored recipe has that map key and the actual lifecycle domain.
- Its parent and resolved dependencies/provisions match the actual kernel
  declarations, including the reserved anchor.

`register` performs real Insert and stores the supplied callback and host object
before returning. `register_child` also writes the real assigned Child slot in
that operation. Failure returns both input payloads unchanged. `remove` first
passes the existing lifecycle Remove guard, then returns that exact entry for
destruction outside bookkeeping locks. Unload retains the registered recipe;
Remove is a separate operation. Surviving entries are unchanged.

`host_mut` lends only `H`; its contract proves registration and control are
unchanged for any mutation through that borrow. No mutable registration or
lifecycle reference escapes. `replace`, `admit_root`, and `call` select the actual
stored registration by ID, retain the other entries, and enforce its revision
and invocation identity. All exposed lifecycle transitions, native value
composition, Child retirement and compaction preserve `wf`. The native adapter
reads pending tickets directly from this state instead of maintaining a second
action-view map. Live-ID enumeration is exact and duplicate-free; it scans
live entries rather than historical identity tombstones.

This connects the registration/interface portions of Definitions 49–50 and the
control projection of Definitions 58/63 to actual production storage. It is a
preservation result for this projection, **not the whole Theorem 64** or a complete
R1 context interpretation. `H` remains opaque: its Future state, shared handles,
lock synchronization, availability semantics and panic adaptation are not proved
by the container's membership invariant. External/static adapters retain their
existing registration boundary.

## Effect requests and actual poll receipts

`effect_work.rs` joins the effect iterator path to the existing cleanup owner.
`SetupWork::enqueue_effect` preflights the actual work owner, lifecycle origin,
source group's cancellation state, receipt capacity and fresh cleanup domain.
It allocates the real iterator queue and enqueues the supplied iterator payload
with that exact identity in one checked operation. Rejection returns the original
payload and binding vector and changes neither owner. Dispatch cannot activate
it against a foreign lifecycle or another queue with the same numeric group ID.

`EffectRun` owns the actual iterator payload. A successful `admit` reserves a
monotonically increasing poll identity; a second admission or call cannot replace
an outstanding result. `call` passes the stored payload and actual argument to
the adapter and constructs a private reply from its actual return. `land` checks
the lifecycle/group/domain and current poll identity before accepting it. A
Pending reply keeps the real stage pending. A Ready reply feeds its actual inverse
or error into `CleanupGroups::land_result`; cancellation determines continuation,
and an inverse yielded after cancellation is retained before iteration ends.
Wrong replies return intact without changing the runner or any cleanup group.
Poll identity exhaustion rejects admission without wrapping or reusing identities.

Runtime uses these methods for `AsyncSetup::effect`, dispatch and `poll_groups`.
Its separate `cancelled_groups` set has been removed. `ensure_active`, nested
Child/effect acquisition and cancellation queries read the same stage cancellation
state used for inverse landing. `EffectHandle::cancel` remains a cooperative
request; this guard takes effect when the driver records it in the stage protocol.
Native and external Child queue admission also
consult this checked guard. In-flight work may still register its inverse after
cancellation; new Child/effect acquisition cannot use that allowance.

This connects the actual iterator/control path to the existing accumulator
interpretation of L-Iter, L-Finish and L-Divert. It proves result provenance,
queue ownership and continuation selection, conditional on the supplied callback
contract. The conversion from the supplied `Poll`/panic result to `EffectOutput` now has
the checked contract below. Arbitrary iterator and inverse effects, custom
destructors, host mutex scheduling and the meaning of opaque mutable payload
fields remain boundaries. It is not a complete
production trace interpretation or a fairness/termination theorem.

## One production execution owner

`Execution<V, C, G, I>` now owns the actual `SetupWork`, every cleanup queue,
the live `EffectRun<G>` map, checked-out runner identities, native service values
and initialization state. Runtime no longer holds a separate work owner, phase
field or iterator map. The static adapter uses the same owner for work, cleanup
and phase, with its external lifecycle/value boundary unchanged.

The invariant connects lifecycle origins, cleanup domains and live group
membership; it also requires closed work, cleanup and native values to agree.
`begin_managed_execution` constructs this state. `finish_managed_execution`
publishes the actual values and makes the episode Active in one checked call.
`release_managed_execution` checks full drain and returns the actual values while
closing the episode. Direct Runtime retirement and restart withdrawal use
`withdraw_managed_execution` to close acquisition together with the control
transition, preserving in-flight work and values. Child-triggered retirement
still calls the existing shared-Child protocol before host notifications.

`take_effect` leaves a checkout record. `put_effect` checks the originating
live queue and cannot overwrite a stored runner. `retire_effect` consumes the
actual runner only after that queue drains, returning its payload for destruction
outside the mutex. A borrowed or abandoned runner prevents removal and release,
even when the iterator map is empty. This is a safety guard; abandoning a runner
does not imply eventual recovery. Cancellation still permits an admitted stage
to land its inverse.

These are actual production state and transition contracts. They do not yet
supply the semantic interpretation of opaque callback effects, mutable value
contents, all host bookkeeping, or the whole host's correspondence to R1.

## Actual Poll normalization

`normalize_poll` preserves actual Pending/Ready results and converts a caught
panic only to failure. `normalize_effect_poll` distinguishes Pending, iterator
end, returned error, yielded inverse and caught panic. It maps the actual inverse
once, with no expected result supplied by the caller. Runtime uses these checked
functions for root, iterator and cleanup polls; the static host shares the root
and cleanup helpers.

The standard `Poll` type specification describes the real enum's variants. It
adds no assumed `poll`, `catch_unwind` or callback implementation. The proof starts
from the result handed to normalization; it does not prove panic capture, the
polling implementation, arbitrary callback effects, or eventual completion.

## Actual reversible service values and finite programs

[`ReversibleValue`](cases/reversible-values.md) adds a concrete production path
for the three semantic links. Plugins use `Setup::update_reversible` or
`run_value_program`; the normal Runtime and static host call the same checked
implementation. A private inverse holds the real target and captured pre/post
value states. `Execution` registers it before returning; `CleanupQueue::dispatch`
selects, executes and acknowledges the actual queued object without a host
success flag. Interference retains that exact inverse for explicit retry.

`operation` and `primitive_theory` establish actual partial inverse laws for
replacement, checked addition, XOR and compare/exchange. The observed state
includes the value and nesting depth, so a same-value later write cannot be
mistaken for an unchanged state. `Program::component` proves roots and every
outcome-selected continuation belong to R1's full finite strict carrier.
Programs are supplied by plugins; their validated code and actual comparison
results control execution. No expected result or transcript is an argument.

The actual value lock carries a ghost history. `history_interpretation`
classifies every write, successful inverse and rejected attempt.
`ProgramReport::source_execution` constructs a continuous dependent-grammar
trace for the complete run or failed prefix, framing other table keys.
All successful-prefix inverses enter the existing cleanup owner in execution
order. The history is erased from Cargo builds.

This closes those links **for this primitive/program path**, not the whole
host context. Ordinary callbacks, Node object state and the global joint
interpretation remain within the existing R2 acceptance work below.
See the [English case](cases/reversible-values.md) or
[中文案例](cases/reversible-values.zh-CN.md) for code, constraints, failure
reproduction and negative controls.

## Extensible scalar effects and managed commit

`ScalarEffect` supplies a Verus model and a real `compute` method whose result
must equal that model. `ScaleAdd` adds checked multiplication/addition without
extending the fixed `ValueOperation` enum. `ThenScalar` and `ChooseScalar` prove
composition using actual returned values and the actual predicate result. They
compose local calculations into **one shared-value write and one inverse**;
intermediate results are not separate published effects.

`Setup::update_reversible_with` / `AsyncSetup::update_reversible_with` now use the
native capture/prepare/landing path described above. The static-host path uses
`ReversibleValue::prepare_effect` and `Execution::apply_prepared_effect`. Preparation
captures value/depth, releases the value lock, executes the implementation and
retains the actual target, input, result and erased model in a private receipt.
The adapter then locks the episode and invokes `Execution::apply_prepared_effect`.
That method rechecks acquisition before committing under the value lock. A
changed value/depth rejects the result; exact restoration to the captured state
permits commit. Cancellation or withdrawal cannot authorize a later managed
write through a prepared result. The adapter catches computation panics outside
these locks and preserves their structured panic error kind.

On success, the checked owner constructs the inverse from the actual before and
after states and appends it to the real cleanup queue before returning. The
contract preserves the original queue prefix, unrelated cleanup groups, running
effects, checkouts, captured imports and phase. Existing inverse dispatch handles
restoration and retains interference failures for retry. The plugin supplies
neither a claimed outcome nor an inverse that could target another value.

The scalar lock history now includes actual computed operations and rejected
preparations. `forward_interpretation` connects success to the key-local source
operation and its strict inverse on every test table; `history_interpretation`
classifies rejected commits as scalar-observation-preserving steps. The
`terminal_component` theorem establishes full-carrier membership for this
terminal scalar operation, using `primitive_theory`'s derived inverse laws.
This is a concrete route from the paper's witnessed effects (8) and Component
constraint (48) to real code. It is not yet the combined control/value/function/
Child/cleanup trace or a proof of an arbitrary outer continuation.
The older table theorem interprets a chosen scalar at one key. `value_alias` now
provides the actual alias-aware projection and the conditional single-key lift;
the whole callback and multi-call context interpretation remains open.

Review path: [`scalar_effect.rs`](../crates/cordis-kernel/src/scalar_effect.rs)
(`ScalarEffect`, `primitive_theory`, `prepare_effect`, `apply_prepared_effect`,
`forward_interpretation`, `terminal_component`) →
[`runtime.rs`](../crates/cordis/src/runtime.rs) (`update_reversible_with`).
See the [unreleased API usage](rust-api.md#extensible-reversible-values-unreleased).
Both native and static setup use this entry. Ordinary Rust implementations do
not inherit a proof merely by implementing the trait; their model law must be
verified. External side effects and arbitrary mutable service payloads are
outside the scalar contract. The alias/effect section above records this batch's
selected runtime/negative evidence; [remaining integration scenarios](r2-state-inventory.md#deferred-integration-evidence)
are kept separate.

## Versioned values and accepted availability replies

The actual native `ServiceSlot` now stores `VersionedValue<Value>`. Its immutable
observation pairs the real payload with its revision; replacement advances that
revision even when the new payload compares equal. Capacity rejection returns
the supplied value and preserves the cell. A predicate runs outside the slot
lock, and its result is accepted only if that observed revision still matches.
The captured payload is also dropped outside the slot lock. This does not prove
the predicate body, arbitrary interior mutation, or mutex scheduling.

Node publications now retain their replacement revisions inside
`PublicationStore`, beside the actual payloads. The host no longer maintains a
separate revision counter. `observation` and `leased_observation` obtain values
and revisions from the same owner, including a revoked publication retained by
an old lease. Replacing a value neither changes publication identity nor retargets
an existing lease.

The real Driver calls the checked `availability::Availability` ledger for
request, notification, validation, completion and consumer removal. A request
reads the actual lifecycle domain, declared dependency, active provider and
visible publication, then issues its actual payload/version. Completion checks
that same lifecycle and store, the complete pending ticket, actual payload and
revision, current notification and dirty flag. There is no caller-selected
current revision or claimed freshness argument. Unknown/duplicate replies
preserve the ledger; a known invalidated reply consumes its own pending action
once. An older notification cannot overwrite the newer row. Removing a consumer
removes its rows while retaining outstanding replies for acknowledgement.
Diagnostic text remains in the adapter and cannot grant availability.

This is an explicit host availability extension. It preserves existing policy:
notifications dirty matching rows without clearing accepted availability, and
`set` alone does not request a new check. The proof establishes freshness when
accepting a callback; it does not assert that a cached predicate result describes
every later object state. JavaScript object contents, predicate truth and wire
translation still need their separate host contracts.

Review: [`versioned_value.rs`](../crates/cordis-kernel/src/versioned_value.rs),
[`publication_values.rs`](../crates/cordis-kernel/src/publication_values.rs),
[`availability.rs`](../crates/cordis-kernel/src/availability.rs) →
[`Driver adapter`](../crates/cordis-driver/src/availability.rs),
[`Runtime slot`](../crates/cordis/src/runtime.rs).

## Owned configuration transactions

`Loader` now stores the actual accepted snapshot, revision, candidate snapshot
and recovery payload in checked `Configuration<Snapshot, Transaction>`.
`check_begin` rejects exhausted revisions before plugin construction and update
planning. `begin` atomically stores the actual candidate/recovery pair; lending
pending work cannot change the accepted snapshot or revision. `commit` consumes
that stored candidate and returns the actual displaced snapshot and recovery
payload. It accepts no replacement snapshot argument. Recovery installs its
actual reconstructed snapshot, returns the abandoned candidate, and preserves
the accepted revision. Refreshing an unchanged effective configuration is a
separate metadata transition, not a claim of full-observation stuttering.

The ordinary async loader borrows its pending transaction across awaits. Dropping
apply or recovery therefore retains that work, including candidate IDs, captured
factories, started update inverses and recovery progress. The capacity check no
longer occurs after changing the accepted configuration.

These are snapshot/revision/ownership contracts, not a complete configuration
refinement. `recover` receives the reconstructed snapshot from ordinary host
code; it does not prove that those new IDs denote the original component
semantics. Tree flattening, module execution, group/include interpretation,
update-body effects, lifecycle action correspondence and persistence results
still need the joint R2-I argument. Definition 81 is not promoted by this change.

Review: [`configuration_transaction.rs`](../crates/cordis-kernel/src/configuration_transaction.rs)
→ [`Loader::apply_prepared` / `recover`](../crates/cordis/src/loader.rs).

## Continuous production control history

`LifecycleState` now maintains a ghost `History` alongside its actual kernel and
action protocol. Every base control mutation records its actual before/after
control observations. The invariant starts at the empty registry, retains the
previous prefix, and ends at the current real control state. `record_control`
cannot replace that state with a caller-supplied transcript.

`control_history_correspondence` proves that the whole recorded sequence is
continuous and each step satisfies the paper control rule, an observation-
preserving internal step, or an explicit extension in `control_history.rs`.
Ordinary incoherent withdrawal is L-Divert or L-Leave. Forced coherent withdrawal
remains Restart. Dynamic provision insertion/removal and pending dependency
configuration have exact interface frames; provision removal additionally
requires absence of retained commitments to that port. Rejected calls and
compaction preserve the control observation. If a history contains no extensions,
`strict_paper_trace` derives the finite strict paper-control execution and its
reachability result from the recorded history.

Both the native and Node drivers use this lifecycle owner, including dynamic
Child insertion and managed resource release. The history is erased from Cargo
builds. This is the complete history of this **control projection**, not the
whole R1 context: service object contents, callback/function fields, publication
versions and the value/cleanup trace must still be composed into one semantic
observation. Protocol-only changes are internal steps in this projection; their
existing receipt and cleanup contracts continue to govern those changes.

## Remaining R2 acceptance

1. Establish the argument → executed operation → outcome → continuation →
   actual inverse relation at extensible production plugin entry points, with
   concrete primitive laws. Native registration and direct `FnMut` invocation
   now establish the recipe/argument/result prefix of that relation. Reversible
   value programs additionally establish concrete effect/inverse laws and
   outcome-selected code, while ordinary plugin bodies remain open. Do not
   substitute a caller-supplied expected result
   or assume arbitrary callback correctness.
2. Own and compose all concurrent groups, dynamic children, publications,
   admitted work and drain/release decisions in one checked production state.
   All cleanup queues now share a verified owner, and payload release composes
   with receipt/lease validation. Root setup and dispatch now participate in
   lifecycle admission, failure, retry and release.
   Real Child allocation/retirement and one-shot shared-slot transitions now have
   contracts. Native publication and committed-value owners now compose with
   Begin/Finish/Unload. NativeHost now also preserves the actual registry,
   callback and lifecycle interface correspondence. Shared native Child pairing,
   synchronization and persistent terminal decisions now have checked contracts.
   `Execution` now jointly owns actual work, native values, phase, live runners
   and their checkouts, with composed publication, withdrawal and release. The
   semantics of other shared host bookkeeping and complete host observation
   still need a joint invariant; result normalization is now checked separately.
3. Prove the complete production trace's classification and its relation to
   the R1 interpretation, including the stated multi-version and dynamic
   interface extensions. Actual reversible value histories and complete finite
   programs now have source traces, and the real lifecycle owner retains a continuous
   classified control history for both adapters. Their complete joint native/Node
   history remains open.
   A list of classified methods is not this theorem.

These are the existing R2 exit criteria, not new conditions added to reduce the
scope of the milestone. Original paper items and the four integration audit
outcomes have not been promoted by this increment.

## Review and reproduction

```sh
cargo test -p cordis-kernel --test publication_values --test async_completion --test cleanup_queue --test cleanup_groups --test setup_work --test execution_lifecycle --test plugin_registration --test child_slot --test native_values --test native_host --test shared_child --test effect_work --test execution --test poll_result --offline
python3 scripts/record-development.py --offline
```

Eight execution-owner tests cover atomic publication/phase, foreign withdrawal,
release and closed contexts, failure/retry, wrong runner return, late inverse
landing, dispatched work and abandoned root/runner blocking. Three poll tests
cover all result branches and preservation of the actual noncopy inverse.

Seven effect-work tests cover atomic allocation, exact payload/binding transport,
Pending/Ready receipts, cancellation and retained inverses, wrong-group and
foreign replies, rejection ownership and calls after cancellation. A Runtime
regression checks an escaped cancelled context, late inverse registration and
landing, suppressed subsequent stages, and owner survival. Four negative controls
misbind the queued group, bypass source cancellation, accept a wrong poll identity,
or discard the actual returned inverse.

Eight shared-Child tests cover FIFO/LIFO pairing, inverse-before-dispatch,
terminal failure/assignment, foreign and obsolete admissions, rejected payloads,
concurrent observers/rejections, registered-identity construction and destructor
reentry after rejection. Two Runtime regressions check cloned failure diagnostics
and identity observation while the actual child is removed.

Six native-host tests cover rejected allocation without losing either actual
input, host mutation and recipe updates across multiple owners, wrong/foreign/
obsolete invocations, dynamic Child assignment/removal, retained cleanup failure
through retry and Unload, and live entry enumeration after churn/compaction.

Seven native-value tests cover exact committed imports, real slot aliasing,
realm isolation, duplicate and foreign Begin, incomplete Finish, failed cleanup
and retry, stale publications, old closed contexts, and deferred destruction of
noncopy values. Existing Runtime regressions cover shared updates, cancelled
setup and destructors reentering contexts.

Child-slot tests cover duplicate assignment, the inverse-before-allocation ordering,
retained allocation failure, foreign runtimes, obsolete episodes and retirement
after replacement. Four additional negative controls remove one-shot admission,
the generation/live-parent guards, or pending cancellation; each must fail the exact contract.

The targeted tests exercise noncopy payloads, old/new publications, stale
generations, foreign domains, exact cleanup manifests, reverse Future completion
order, factory invocation timing, failed retries, destructor ownership, late
cancelled landings, foreign/unbound lifecycle owners, retained provider
commitments, atomic retry, consumed failure after group removal, and sealing
with non-root work still outstanding. Registration tests add realm isolation,
current parent declarations, rejected noncopy payloads, wrong/foreign owners,
stale recipe revisions, direct factory invocation, actual async failures and
Child retirement after removal. The normal development checks additionally rebuild and test the Rust and Node hosts.

Forty-nine R2 negative controls change actual payloads or identities, forge cleanup
success, continue after cancellation, omit outstanding work, or substitute an
unbound cleanup owner. They also erase an isolated realm or registered
dependencies, omit the recipe revision check, or bypass the Child runtime check.
Five of these native-value controls omit committed imports, bypass a generation
check, finish without complete values, substitute the published map, or release
a different episode. Three native-host controls hide a registration, lend another
owner's bookkeeping, or replace another owner's recipe. Three shared-Child
controls substitute a separate request handle, reject an otherwise valid allocation
or report retirement without changing the actual slot. Six execution/poll controls
omit a checkout, accept a foreign runner, omit Active, retire a live queue, turn
Pending into completion, or discard the returned inverse.
Five value/program controls ignore the actual result or depth, omit an inverse,
forge restoration success or skip a continuation. Two control-history cases omit
a real step or attribute a declaration at another port to the supplied call.
Each scoped experiment needs a fresh positive proof,
a compiled mutant and rejection of the named contract. A scoped result does not
mean the full 184-case negative regression ran; see [validation](validation.md).

The source-bound development report records the full positive check separately
from release acceptance and paper completion. No Node dependency is added for
Rust users, and no temporal-logic library is required for these contracts.

## Verified native identity issuance

The host's four allocators (`NEXT_KEY`, `NEXT_REALM`, `NEXT_EPISODE`,
`NEXT_CLEANUP`) and the Rust/Node shared driver's `NEXT_DOMAIN` now use
[`IdentityIssuer`](../crates/cordis-kernel/src/identity_issuer.rs).
Service keys, realm isolation, shared Episode generations, and root/effect cleanup
domains and shared-driver domains therefore execute the checked CAS loop rather
than an adapter-local
`AtomicU64::fetch_update` closure. This strengthens the freshness needed by
Begin/work/group checks; it does not authenticate arbitrary equal integers.

`issue` linearizes a successful allocation at its strong compare-and-exchange.
Its erased authority issues a linear permission for the exact returned integer.
`Identity::distinct_from` proves that two such permissions from the same issuer
cannot name the same integer. Dropping a receipt does not return its number to the
allocator. A persistent progress witness makes every failed CAS observation
strictly larger, giving the retry loop a finite numeric variant. This concerns the
allocator's executed steps, not scheduler fairness or user Future termination.

Zero is reserved and `u64::MAX` is the exhausted sentinel. An exhausted result
carries evidence for that actual frontier; `remains_exhausted` certifies a later
load, and no path resets or wraps the counter. The native host retains its existing
panic-on-exhaustion policy; the shared driver
continues to report a `Capacity` error. The runtime stores one sequentially consistent atomic
counter per namespace; the permission map and progress history are erased.

Independent issuers may return equal integers. `starting_at` creates a fresh,
independent tail namespace, not a resumption token. Ordinary `Arc`/`Weak`/mutex
association, static-supplied metadata and namespaces outside these five production
allocators remain explicit boundaries. In particular, the Weak check before
polling is retained, and the conditional Journal ownership premise in
`HostStatus` has **not** been discharged by this allocator proof. A complete joint
host interpretation and paper-step classification remain open.

This source batch passed 9 selected Verus checks, 89 Rust regressions, 805
Node/Loader regressions, strict all-target/all-feature Clippy and formatting.
Two strict negative controls compiled and failed their exact issuance/exhaustion
postconditions after fresh matching positives. The 299 canonical controls passed
anchor preflight; full negative execution/calibration, whole-kernel proof, full
development/release and R2 acceptance were not run. Runtime coverage includes
concurrent issuance, dropped receipts, exhaustion, crosswired handles and cleanup
retry. No solver, assertion or timeout limits were relaxed.


## Execution-owned shared effect status

`Execution::effect_status(&mut self, id)` now installs exactly one private shared
link for a live group and returns the payload-owning `HostStatus`. The execution
invariant binds that exact link to its Journal, cleanup membership, Begin/work
identity and group domain. `initialize_effect_status(id)` and
`retire_observed_effect(run)` select the stored link themselves; neither accepts
a caller-selected status or assumes that equal numeric identities imply a shared
Journal. Two independent runtimes may have identical numbers and still advance
only their own status.

Initialization authenticates the real settled, non-pending queue in the Journal
write epoch. Retirement first removes the actual drained group and checkout,
then records `EffectFinished` for its stored link. The returned `Observation`
contains actual flags and an erased authentic receipt whose history includes the
earlier group removal. Failed retirement preserves the entire execution. Raw
`retire_effect` uses the same implementation; `remove` and release cannot silently
abandon an installed status. The link is removed on successful retirement, while
an escaped handle can continue observing completion.

The checked cell holds only progress, immutable provenance and the Journal member.
Error values, terminal errors and Child results stay in their exclusive
`HostStatus`; an erased linear permission ties their metadata to this same cell.
Retaining the execution's link does not retain these user payloads. `observe()`
returns an authentic member-local prefix, not a claim that unrelated members
still have their older values. `execution_snapshot()` captures the full Journal
under a read epoch. `last_observed()` explicitly denotes the payload owner's last
observation, which may precede progress made by the execution.

This closes the earlier **conditional effect-status Journal association** at the
real initialization/retirement entries. It strengthens the executable connection
to Definitions 58/63 and the existing lifecycle/cleanup guards; it adds no paper
axiom or unchecked pointer-identity specification. Ordinary `Arc`/`Weak`/mutex
association for the whole shared Episode, static context inputs, arbitrary
callbacks and Node/configuration Component meaning remain separate obligations.
Locks follow Episode → adapter status → checked cell → Journal; callbacks and
wakers run after releasing them.

The affected proof closure passed **870 scoped Verus checks, zero errors**, with
full kernel compilation. **882 workspace Rust unit/integration/doc tests** and
**four affected strict negative controls** passed. Each negative requires a fresh
matching positive, whole-mutant compilation and exact named diagnostic rejection.
All **299 canonical anchors**, formatting, strict all-target/all-feature workspace
Clippy and the paper index checks passed. Three new regressions cover identical
numeric identities in different Journals, unique status creation/raw retirement,
and releasing observer error payloads while the execution retains its link.
The initial skip-removal control was rejected at the actual retirement
postcondition, earlier than its old diagnostic anchor; it passed a fresh strict
run after that anchor was relocated. No solver limits or validation criteria
were relaxed. Whole-kernel proof, full negatives/calibration, Node runtime,
full development, release and R2 semantic acceptance were **not run**.


## Status continuity across real calls and interleavings

The actual status created for a group now remains identifiable through the
composed execution APIs. **61 methods** explicitly preserve `status_links`, or
remove only the retiring runner's entry. These contracts cover root admission and
completion, Child/effect enqueueing, checkout/return, scalar and service programs,
inverse registration, cleanup failure/retry, publication and release. Both finite
program loops preserve the exact links at every iteration. A fresh status factory
has an exact success condition and proves `HostStatus::owned_by(execution, id)`;
it cannot replace an existing group's link.

This is stronger than re-establishing `Execution::wf()`: an empty status map could
satisfy that invariant while losing an escaped handle. The new frame contracts
keep the same actual shared allocation across the real call chain. They frame the
link, not concurrently mutable progress flags; the flags have their own history.

Every returned `Observation` now contains an erased index of its **actual
constructor commit**. The checked cell and lock invariant retain this index.
The receipt authenticates the initial owner, Begin/work identity and kind, with
false progress flags, zero errors and no Child. `Observation::lifetime` derives
the complete interval from that creation to the actual latest member receipt.
For every intervening Journal step, `classified_step` establishes either the
same complete Host record or its exact guarded Host transition. `progress_between`
proves immutable provenance, monotone cancellation/initialization/completion and
terminal presence, nondecreasing error count, and a stable assigned Child.
No adjacent-commit, selected-interleaving or scheduler premise is required.

These are native shared-status safety contracts connected to the real producer.
They do not classify the full runtime observation or give arbitrary callbacks,
Node objects/HMR, configuration groups or source merging their Component meaning.
They do not prove eventual completion. The runtime stores no new history log;
creation indices, interval derivations and witnesses erase.

This source passed **878 scoped Verus checks, zero errors**, with full kernel
compilation, **87 focused Rust regressions**, and **two new strict negative
controls**. Each control required a fresh matching positive, whole-mutant
compilation and the exact named rejection. The mutations discard the actual
status association during runner checkout or invent an observation's allocation
index. All **301 canonical control anchors**, formatting, strict workspace
Clippy (all targets/features), paper indexes and changed-document local links
were checked; the preceding 299 control definitions were preserved. The earlier
870/882/4 results belong to their previous source. Whole-kernel proof, full Rust
and Node suites, full negatives/calibration, development, release and whole-R2
semantic acceptance were **not run** for this source.


## Complete classification of the recorded native carrier

The actual Journal observation now has one classifier over **all thirteen Record
variants and the outstanding managed-inverse map**. `interpreted_trajectory`
constructs its full sequence from the authenticated snapshot: the initial maps
are empty, the last maps equal that snapshot, and every original commit appears.
Neither an expected initial state nor a filtered list of calls is an input.

| Actual step | Established interpretation |
| --- | --- |
| Built-in or extensible scalar write | R1 dependent operation on the actual allocation; exact outcome, selected continuation and strict inverse on every recovery heap |
| Restore or rejected/stale/blocked attempt | Exact partial inverse or operation domain; every rejected value attempt preserves both complete maps |
| Native lifecycle rule | Existing R1 control step, with Restart identified separately as an extension; actual ownership and publication records remain present |
| Slot/payload replacement, payload retirement or allocation | Exact selected record and revision/freshness change, preserving every other record |
| Work, cleanup, groups, Host, poll control, recipes, configuration or sources | Their actual checked transition and guard over the same full input map; these are explicit implementation/host transitions |
| Managed inverse registration | The actual earlier forward write, exact queue transition and outstanding obligation removal; a foreign-domain registration cannot manufacture a local write order |

Framing preserves both the value and presence of every unrelated record. A whole
recorded-state stutter is equivalent to equality of the selected record **and**
the pending map, rather than equality of one projection. Successful writes remain
observable even when the scalar contents are unchanged, because depth changes.
Slot/payload/native revision changes, payload retirement, fresh allocation and inverse registration also
cannot be labelled whole-state stutters.

This classification is exported by the real `Journal::snapshot`,
`NativeRuntime::execution_snapshot` and `HostStatus::execution_snapshot` producers.
`record_recipes_following` authenticates it for the actual return commit;
registered Value/Service root and Child reports include it in `completed()` and
join it to their existing effect-before-return theorem. The indices and complete
observations erase; no runtime history or extra callback execution is added.

The same real return contract now proves `local_inverses_registered`: every
successful-prefix write whose managed inverse belongs to the return's Journal
has already settled its registration obligation. `Evidence::settled_through`
retains that fact through every later interleaving in the actual return prefix,
and `unique_settlement` excludes a second consumption. Failed function returns
retain this guarantee for their successful prefix. Other writers may still have
pending obligations; registration is not eventual inverse execution or success.

Review [joint_classification.rs](../crates/cordis-kernel/src/joint_classification.rs),
[the Journal producer](../crates/cordis-kernel/src/joint_execution.rs),
[the native return producer](../crates/cordis-kernel/src/native_runtime.rs) and
[Value](../crates/cordis-kernel/src/value_function.rs)/[Service](../crates/cordis-kernel/src/service_function.rs)
reports. `classify_step` composes separate value, owner, framing, rejection and
inverse-origin lemmas; it uses the existing solver limits.

**Recorded native carrier is not the complete host observation.** Opaque payload
interiors, JS object/Fiber/HMR and ALS behavior, ordinary Arc/Weak/mutex association,
and grouped/source-merge Component meaning remain open. An explicit configuration
or recipe transition proves that transition, not arbitrary callback effects.
The original named-port interpretation still requires its alias condition.
Foreign Journals remain separate; no fairness, eventual completion, whole-R2 or
paper-wide theorem follows from this classifier. The three partial R2 work items
and original exit criteria are unchanged.

The preceding classifier batch, after its Cargo import repair, passed **894 scoped Verus checks,
zero errors**, including full kernel compilation, and strict workspace Clippy
with all targets/features. Formatting, all **301 existing canonical anchors**,
paper indexes and changed-document local links were checked. No assumptions,
unchecked bodies, higher solver limits or relaxed negative criteria were added.
Runtime tests, new/full negatives, calibration, whole-kernel proof, development,
release and whole-R2 acceptance were **not run** for that source. The earlier
878/87/two-negative results describe the preceding source. New runtime
and negative scenarios are deferred to the related acceptance batch: interleave
all record kinds around failed cleanup/retry; preserve other writers' pending
obligations while proving the returning function's own local inverses registered;
reject a classifier that treats registration as a stutter or drops the pending
projection, and an attempted second settlement. Existing tests and all 301 strict
negative definitions are unchanged.

## Shared typed payloads in the actual execution

The native host now stores non-scalar services in
[`SharedPayload<T>`](../crates/cordis-kernel/src/shared_payload.rs), including its
actual `Arc<dyn Any + Send + Sync>` payload. This replaces the ordinary host
`Mutex<VersionedValue<Value>>`. The checked owner holds the real payload, version,
private lock, authoritative typed history and Journal member; the history and
correspondence evidence erase from Cargo output.

`Execution::new_payload` selects the actual Episode Journal. Production `provide`
and dynamic `publish` use this factory; standalone/static storage creates an
explicit independent domain. Reads, `set`, `ServiceHandle::set` and availability
checks use that same owner. Captures retain their original owner and value.
`check_result` rereads that owner and accepts exactly when the actual supplied
callback result is true, the owner is live and its captured revision is still current. Equal-value
replacement still advances the revision; numeric versions from different cells
cannot be substituted for the retained owner.

The common carrier now includes `Payload { source, revision }` and the terminal
`RetiredPayload` record, with exact `PayloadReplace` and `PayloadRetire` steps. `payload_execution::indexed` and
`Snapshot::complete_projection` connect every actual typed version, from initial
allocation, to its position in the complete interleaved Journal. No mutation of
that owner is omitted. `SharedPayload::execution_snapshot` holds its own read lock
while reading the Journal, tying a live owner's actual current typed value to
that epoch; retirement returns `None` instead of fabricating a live value.
The common Journal stores identity/version; it does not serialize arbitrary `T`.

The real Runtime checkpoints call
[`payload_service_snapshot` and `scoped_payload_service_episode_snapshot`](../crates/cordis-kernel/src/native_payload_runtime.rs).
They collect payload and scalar slot receipts before the Journal read, then
certify actual retained publications, Episode-owned values, captured imports,
control, work, cleanup and setup scope together. The complete
[`payloads::projection`](../crates/cordis-kernel/src/native_payload_observation.rs)
retains every service-map key and distinguishes scalar resolution, local payload
identity/version, retired payloads and foreign owners. `project_replacement` and the real
`Replacement::production_aliases` frame all unrelated service observations;
every current alias of the replaced owner sees the new revision. Foreign domains
remain explicit and do not acquire a fabricated common history.

Replacement returns the displaced executable `Arc` intact. Its audit observations
are erased, so the result does not retain an extra executable copy of the new
payload that could run a user destructor under an outer host lock. Existing host
callers release their bookkeeping locks before dropping old or rejected values.
Predicates run outside payload locks. This preserves the existing reentrancy
design; it is not a proof of arbitrary user destructors or host mutex scheduling.

Existing release regressions exposed an integration requirement in the pinned
vstd lock: dropping it does not destroy its stored value. `SharedPayload::retire`
now records a terminal step, empties the real storage and returns the payload
after releasing the lock. Repeated retirement returns no payload; replacement
rejects with `Closed`, capture/refresh return `None`, and earlier predicate results
are rejected. The Journal's `payload::retained` proof prevents resurrection.
The native host retains a `PayloadLifetime` guard in actual slot metadata; its
ordinary Rust destructor invokes this checked retirement when the last service
slot reference is released. Retained read Arcs can still keep their original
payload alive. Direct low-level kernel users must explicitly retire the owner;
this is not a claim that Verus proves arbitrary destructor execution. The four
existing release/reentrancy regressions were preserved and rerun after this fix.

For the paper-to-code review, this strengthens the concrete observation inputs
for Definition 29's operations/outcomes, Definition 48's Components and
Definition 58's execution observations. It does **not** establish arbitrary `T` interior mutation, general
heterogeneous effect/inverse laws, or original named-port Component membership.
Ordinary Episode Arc/Weak/mutex association, static context inputs, complete
JS/Fiber/HMR/ALS behavior and configuration group/source-merge meaning remain
open. The three partial R2 items and original exit criteria stay unchanged.

Review: actual [`runtime.rs`](../crates/cordis/src/runtime.rs) storage and factories
→ [`Execution::new_payload`](../crates/cordis-kernel/src/execution.rs)
→ [`shared_payload.rs`](../crates/cordis-kernel/src/shared_payload.rs)
→ [`payload_execution.rs`](../crates/cordis-kernel/src/payload_execution.rs)
→ combined service projections and Runtime checkpoints above.

The final source passed **955 scoped Verus checks, zero errors**, full kernel
compilation, **102 existing Rust regressions** across native services, static
hosting, reversible programs and configuration, and strict workspace Clippy for
all targets/features. Formatting, all **301 unchanged canonical anchors**, paper
indexes and **526 changed-document local links** passed. Source hashes are bound
to these checks. The initial four payload-release failures were repaired by the
explicit retirement protocol; their assertions were not weakened. No new runtime
tests, Node acceptance, new/full negatives, calibration, whole-kernel proof,
full development, release or whole-R2 acceptance ran in this batch. The preceding
894-check classifier result remains historical. Deferred new acceptance scenarios: concurrent replacements
and alias captures; same numeric revisions from different owners; replacement
between predicate evaluation and reply; payload destructor reentry after outer
locks; version-capacity rejection; mixed local/foreign values around failed
cleanup and retry. Existing tests and strict negative criteria are preserved.

## Reversible typed payload replacement

`Setup::replace_service` and `AsyncSetup::replace_service` now replace a declared
native service's actual payload and register its actual inverse before returning.
The same entry is available to root and Child callbacks:

```rust,ignore
setup.replace_service(greeting, String::from("updated"))?;
```

This operation uses the Begin-bound provider and retains the exact service slot.
It supports non-scalar Rust payloads, including the production erased `Any`
carrier. `ReversibleValue` keeps its existing scalar API; static storage is
explicitly rejected by this native service entry. An ordinary callback's
surrounding computation does not acquire a proof from calling this operation.

The implementation separates two kinds of state:

| State | Forward replacement | Successful inverse |
| --- | --- | --- |
| Actual Arc and semantic head/depth | Fresh head; depth increases | Restore the exact previous Arc, head and depth |
| Read revision | Increases | Also increases; old predicate results remain stale |
| Cleanup obligation | Register the actual inverse and retained slot | Remove only after actual guarded restoration succeeds |

The cell invariant reserves enough revision capacity for every outstanding
managed depth. A forward write reserves two increments (itself and its inverse);
a successful restore spends one increment while reducing depth. Therefore a
matching live inverse cannot fail because the revision counter is exhausted.
The inverse's checked type invariant authenticates its original state history.
A later managed write blocks an earlier inverse until the later one is restored;
repeating an already completed inverse cannot overwrite the current state.
An ordinary untracked `set` starts a new semantic head and invalidates earlier
inverses; retry is not promised to repair such an external conflict.

The actual cleanup queue owns a dedicated typed-inverse variant. Its dispatcher
selects the original queue slot and ticket, executes the checked inverse, and
derives success/failure from that result. A failure preserves the exact inverse
and retention guard and blocks earlier cleanup in that group. Existing explicit
retry issues a new ticket. Successful cleanup returns displaced values and
retention guards to the adapter for destruction after the Episode lock is
released. User destructors are not executed inside the verified payload lock.

`PayloadApply` and `PayloadRestore` are explicit non-stutter Journal changes.
Same-Journal writes acquire a linear pending obligation; the real queue insertion
consumes it. `Admission::pending_interval` proves it stays pending through all
intervening recorded steps. Foreign Journals retain separate identities. The
existing complete typed history, alias projection and native classification
include both new mutation kinds. Rejected restoration preserves the payload;
it does not fabricate a successful write or inverse.

The paper review path is Definition 29/equation (31) →
[`operation`, `primitive_law`, `Inverse::interpretation` and `roundtrip`](../crates/cordis-kernel/src/payload_inverse.rs)
→ [`apply_native_payload`, `apply_payload` and `dispatch_payload_cleanup`](../crates/cordis-kernel/src/payload_cleanup.rs)
→ the actual host API in [runtime.rs](../crates/cordis/src/runtime.rs).
The operation law covers every input in the typed semantic carrier. The fresh
head selected by the real owner is an explicit operation argument. `roundtrip`
derives inverse success for a composing stack; it does not assume each inverse
succeeds. The monotonically increasing read revision is an implementation
extension, not part of the state claimed to return to its old value.

This is a new concrete non-scalar primitive and production queue composition.
It does **not** establish arbitrary interior mutations of `T`, automatic progress,
general outcome-selected heterogeneous callback functions, original named-port
Component membership under aliases, or a complete joint Node/configuration
interpretation. General function-return grouping still needs further composition.
The typed restore issue/observation/acknowledgement interval is now connected
[below](#typed-cleanup-issue-read-and-acknowledgement).
The original R2 exit criteria and its three partial work items remain unchanged.

The preceding typed-inverse source passed **941 scoped Verus checks, zero errors**, full kernel
compilation, **102 existing Rust regressions** across five host suites, strict
workspace Clippy for all targets/features, formatting, paper index/review checks
and all **301 unchanged canonical negative anchors**. Proof scope:
`reversible_value`, `cleanup_groups`, `cleanup_queue`, `execution` and
`lifecycle_state`. Source hashes and logs are recorded locally in
`/tmp/cordis-r2-payload-inverse/checks.json`. The earlier 955/102 result belongs to
the preceding source and is not carried forward. New typed-path runtime cases,
new/full negative controls, Node acceptance, whole-kernel proof, full development,
release and whole-R2 acceptance were **not run**. Existing regressions are not
runtime acceptance for the new typed API. No assumptions, unchecked bodies or
solver limits were added.
Deferred new integration scenarios: nested typed replacements; two consumers
restoring in the wrong order then retrying; stale predicate replies after an
exact value restoration; ordinary replacement and retirement conflicts; retained
slot/destructor reentry; capacity reservation; and mutations that discard the
inverse, reuse a head, fail to advance the read revision, or acknowledge a
blocked restore. Existing tests and strict negative controls remain intact.


## Typed cleanup issue, read and acknowledgement

The actual typed cleanup dispatcher now returns an erased, authenticated
`Evidence<T>` for its own request, payload observation and acknowledgement.
It is constructed by `dispatch_payload_cleanup`, including the queue, exact
inverse, ticket and real restoration result; the adapter cannot supply a success
flag in place of the checked result.

| Actual result | Evidence | Queue completion |
| --- | --- | --- |
| Restored | Locked live-state read followed by the actual `PayloadRestore` commit | Successful acknowledgement removes the original inverse |
| Interference | Locked live-state read whose semantic state rejects this inverse | Failed acknowledgement retains the exact inverse and slot guard |
| Closed | Read of the owner's authenticated terminal `RetiredPayload` state | Failed acknowledgement retains the obligation |

A read has a prefix length in the real history; it need not append an event.
The read may immediately follow issue. Only successful restoration has a write
index. The inverse retains its actual Journal so a retired payload still admits
an authenticated read. Receipt maps, histories and result witnesses erase from
the executable; retaining this Journal handle does not store old payload values.

For a shared Journal, the read covers issue, an actual restore follows the read,
and acknowledgement follows the attempt endpoint. `custody_interval` proves the
same ticket remains outstanding through every intervening recorded state, with
its admission-time committed providers preserved. `microsteps` retains all
interleaved commits in the classified trajectory. After either completion result,
`completed_attempt_stays_closed` excludes that old ticket from every authentic
extension, including a retry with a fresh attempt number. Foreign Journals remain
separate; there is no inferred cross-domain total order.

Review the actual read/restore in
[`payload_attempt.rs`](../crates/cordis-kernel/src/payload_attempt.rs) and
[`payload_inverse.rs`](../crates/cordis-kernel/src/payload_inverse.rs), the queue
composition in [`payload_cleanup.rs`](../crates/cordis-kernel/src/payload_cleanup.rs),
and the interval/extension theorems in
[`payload_restoration.rs`](../crates/cordis-kernel/src/payload_restoration.rs) and
[`cleanup_interval.rs`](../crates/cordis-kernel/src/cleanup_interval.rs).
This connects the concrete inverse law of Definition 29/equation (31) to actual
cleanup execution and the existing control projection of Definitions 58/63.
It closes this typed protocol interval; it does not prove arbitrary callbacks,
interior mutations of `T`, scheduling progress, or the remaining general
function, Node and configuration semantics. R2 remains in progress.

This source passed **964 scoped Verus checks, zero errors**, full kernel
compilation, **102 unchanged Rust regressions** across five host suites, strict
workspace Clippy across all targets/features, formatting, paper index/review
checks and **301 unchanged canonical negative anchors**. Proof scope:
`reversible_value`, `cleanup_groups`, `cleanup_queue`, `execution` and
`lifecycle_state`. Local source-bound evidence:
`/tmp/cordis-r2-payload-interval/checks.json`. Earlier slice counts are historical.
New typed-path runtime cases, new/full negatives, Node acceptance, whole-kernel
proof, full development, release and whole-R2 acceptance were **not run**.
No assumptions, unchecked bodies or increased solver limits were introduced.

Deferred integration cases additionally cover: interference followed by an
intervening successful inverse and explicit retry; retirement before dispatch;
a read with no intervening write; unrelated commits between boundaries; fresh
retry versus duplicate old acknowledgement; and mutations that substitute the
issue, omit the actual read cause, or report success for a blocked/closed owner.
Existing tests and strict negative-control criteria are unchanged.
