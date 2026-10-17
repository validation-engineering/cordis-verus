# Paper refinement work map

[Milestones](paper-refinement-roadmap.md) · [里程碑（中文）](paper-refinement-roadmap.zh-CN.md)

Generated from `paper-refinement-plan.json` and the original `paper-obligations.json`.
This inventory checks allocation and source symbols. It does not establish a semantic bridge, prove a caller precondition, or certify paper completion.

Original-paper audit: formalized 42, partial 18, proved 17, refuted 4.

## Milestones

| ID | Goal | Status | Depends on |
| --- | --- | --- | --- |
| R0 | Whole-paper acceptance baseline | complete | — |
| R1 | A consistent semantics and implementation representation | complete | R0 |
| R2 | Refinement of production execution | in_progress | R1 |
| R3 | General lifecycle recovery | in_progress | R1 |
| R4 | Global lifecycle properties | in_progress | R2, R3 |
| R5 | Whole-chain review and delivery | planned | R4 |

R1 completion scope: Finite strict context and indexed Component interpretation implemented by FreshDriver. Explicit revisions are recorded in r1Interpretation; original paper claims are not promoted.

[R1 interpretation and reproduction](r1-semantics.md) · [中文](r1-semantics.zh-CN.md)

Carrier: Every finite, typed, well-formed registry with the stated component interface; not only states reached by one successful trace.

Executable profile: Validated finite FreshDriver code banks: Unit, Provide, u64 Xor and fresh Child, with actual values, continuations, inverse receipts and allocator limits.

Explicit revisions:

- R1-CONTEXT: Interpret finite code and retained receipts instead of the unrestricted recursive set/function equation.
- R1-DOMAIN: Separate strict admission/control and declared-value observations from service recovery. Preserve real failures; prove a semantic contract for parents, continuations and children on the complete stated carrier.
- R1-FIELDS: Interpret executable root/current fields and retained journals as strict functions on arbitrary test states, including undefined inverse calls; do not substitute token equality or assert original Equation (54).

Remaining boundary: Original unrestricted Gamma and total-function witnesses stay separate. Production callback/value contracts belong to R2; general interference recovery to R3; global termination and confluence to R4.

## R2 execution progress

Source-linked progress for the existing R2 exit criteria; local payload/result contracts are not whole-host refinement.

[Execution contracts and boundaries](r2-execution.md) · [执行合同与边界（中文）](r2-execution.zh-CN.md)

| Work item | Status | Scope | Remaining boundary |
| --- | --- | --- | --- |
| managed-payloads | complete | Actual generic payload ownership, key-local visible lookup, checked owner/generation/domain, lease-derived identity and atomic managed payload release. | JS object contents and Rust interior mutation are not interpreted by payload identity. |
| awaited-results | complete | Native async output/origin pairing and completion from the actual returned Result, retaining both host failure policies. | Native Future/result transport and actual Poll normalization do not prove external I/O truth, polling/panic capture or eventual return. Native registered FnMut provenance is checked separately. |
| landed-continuation | complete | Actual inverse payload landing and continuation selection from result/cancellation, with the accumulator-step projection. | The opaque inverse function effect is not interpreted by a token/payload accumulator. |
| invocation-effect-origin | partial | Managed native entry points bind real arguments, declarations, provider/slot selection, lifecycle/work/group identity, actual call/Poll results, continuation and retained inverse. Extensible scalar effects run computation outside locks, retain authentic read-to-commit causality and reject stale computations. Body::Value and Body::Services are actual stored root/Child bodies; multi-service binding checks every registered key and preserves real recipe code/revision. Whole finite dynamic execution and exact inverse-queue semantics are connected to the actual returns. Actual native recipe registration, SharedChild insertion, replacement, removal and callback/Value/Service-root returns now construct a typed history indexed in the common value/work/cleanup Journal. Exact before/after RegisteredPlugin values, installed-version origins, complete projection and same-epoch native Episode guards are checked. Rejected calls preserve recipe history; snapshot evidence erases old captures. Arbitrary function/effect meaning and complete native/Node/configuration semantic composition remain open. Actual finite Value/Service returns now authenticate their real write, inverse-registration and failure witnesses against the same Journal commit as the returned Call. Local effects strictly precede that return; foreign histories retain their identity, including locally registered inverses of foreign writes. All retained witnesses erase. Production Loader configuration now uses Recorded, with its exact protocol/candidate/recovery/update states indexed in the same Journal as native lifecycle, recipes, values and cleanup. Actual forward/inverse/structural poll returns, including Pending and failures, retain callback argument/payload/result provenance across composition. Complete typed projection and accepted-state/commit-input origins are proved; callbacks execute outside the Journal lock. Loaded-source/checkpoint history now shares that owner and Journal; full source/Component meaning and Node semantic composition remain open. The same Recorded owner now holds actual sources and source history; production load/clear/save cannot pair it with a different configuration. Source records authenticate that exact configuration and no-pending status in one Journal write epoch, including its execution index for same-version recovery/refresh. A single read captures both typed histories; complete projection and checkpoint-origin proofs resolve retained bases to actual loads/processed saves and earlier accepted configuration states. JSON/merge/group Component meaning remains separate. Actual registered Value/Service root and Child returns now also prove that every successful-prefix managed write local to the return Journal has its inverse registration obligation settled. The actual insertion remains settled across every later interleaving and cannot be consumed twice. Failure returns retain their successful-prefix guarantee; foreign Journals and eventual inverse success remain separate. Native typed payload replacement now separates the reversible Arc/head/depth state from a monotone read revision, reserves inverse capacity, and authenticates the real inverse with a checked type invariant. The real Setup/AsyncSetup entry resolves the Begin-bound service and registers its inverse plus exact retained slot in the actual cleanup queue. Checked dispatch derives completion from guarded restoration and preserves failed inverses. PayloadApply/PayloadRestore are explicit non-stutter Journal steps; same-domain inverse registration settles the actual linear pending obligation. Full-carrier primitive and composing-stack laws do not establish arbitrary callback or original-carrier Component composition. Actual typed cleanup now returns authenticated issue/read/optional-write/acknowledgement evidence. Reads are real Journal cuts, including terminal retired payloads; only successful restoration adds a write. Same-domain interval proofs preserve issued-ticket responsibility and admission-time committed providers through all interleavings, and any later authentic history keeps completed tickets inactive. These checked producers strengthen the concrete primitive connection, without closing general function, Node/configuration semantics or whole-R2 acceptance. Actual Body::Managed registrations now store complete finite heterogeneous root/Child functions. Their checked interpreter executes extensible verified scalar effects and typed replacement, binds all declared keys and current recipe arguments, selects real continuations and explains actual rejection. Full-carrier dependent grammar and parameterized named-port Component laws compose with the actual successful-prefix mixed inverse queue. Authentic same-Journal order includes all earlier local effects across foreign-Journal interruptions, and the real root return joins their witnesses. Alias projection retains an explicit singleton condition; arbitrary callback interiors and new effect families remain separate. | Arbitrary callbacks and effect families beyond the verified scalar/typed sum need explicit effect/inverse laws and execution connections. Parameterized full-carrier Component membership and singleton-alias projection do not establish unconditional named-port independence for conflicting aliases. Extra callback side effects, unverified Rust trait implementations, panic capture, external I/O truth and eventual Future return remain outside these contracts. |
| production-composition | partial | One native Journal records actual objects, slot replacements, lifecycle/publication owners, Begin captures, work, live cleanup queues/groups, host status, control, realms and setup scopes. Same-domain receipts join actual finite calls, rejected attempts, inverse registration and cleanup; producer snapshots retain the authoritative source history. Registered multi-service root/Child reports carry the actual selected function and qualified allocation interpretation; the retained queue has the same strict reverse-stack meaning. The actual Loader now uses a checked update Batch/Future owner and native target identity; accepted revision/recovery gates depend on its real results. Its phase and source observations now join the native Journal through Recorded; complete Component meaning remains open. Configuration now uses the real ordered Tree, native allocation snapshots, owned structural phase prefixes and actual recovery-payload extraction. These establish allocation/parent/protocol provenance; the complete configuration interpretation remains open. The real file-save owner now checks ordered I/O acknowledgements and partial reports, while configuration stamps reject revision ABA and foreign-runtime save plans. The complete source/Component interpretation remains open. The production NodeRuntime now owns lifecycle, actual publication handles/revisions/leases, checks and checked selection under one domain invariant and continuous erased history. Actual request/replacement/reply order proves version-ABA rejection; dynamic interfaces and managed release use the same owner. The same Node owner now stores actual admissions and episode status/error payloads; Begin origin and retention until successful release follow from its continuous history. Actual pending action tickets are derived directly from the ledger. Actual Node callback receipts and wait results now enter that same history; the core owns withdrawn-publication selections and derives release manifests from its real registry. Finite-history proofs establish publication/callback origin, scope retention/non-reuse and complete batch withdrawal. JS callback dispatch/ancestry and object/Fiber/HMR interpretation remain explicit boundaries. The actual Node release-candidate queue and returned batch now share this history: successful retirement queues real payloads, current retention filters delivery, and finite-history proofs trace writes and retirement while preserving candidates until drain. JSON transfer and JS deletion remain host boundaries. Actual Node reads now select retained Begin/own/cleanup/root publications in that same history. Retained admissions have live leases derived from execution, committed reads preserve the original slot across withdrawal and retry, and returned payloads have real write provenance. The caller-relative read-only lift connects the actual lookup outcome to Definition 29/equation (31); arbitrary JS object methods and whole Component functions remain outside this interpretation. Actual Node interface descriptors and dynamic ownership now share the same history, with derived control correspondence and mount/declaration origins. Actual publication branches and complete provider reconciliation retain exact successful or failed call prefixes; transfer requires drained old commitments and a visible eligible successor. New integrated runtime/negative acceptance remains pending. The actual Loader now uses checked parent-local key construction and inherited enabled status, rejecting duplicate allocation ownership. Exact old/candidate retirement selection and complete retirement/reconstruction loops carry actual callback arguments, host states, results and failed prefixes. Reconstruction preserves saved recipes and parent-local structure; success visits all enabled nodes with correct current parents. Group/include/factory meaning and complete native/Node semantic composition remain open; integrated acceptance for those paths is pending. Actual recursive group/include expansion now uses the checked Expander in file loading and save preflight. Complete derivations preserve actual payloads and child order, bind every included forest to its real read result, and cover the entire contiguous read interval. File ancestry is acyclic and total tree depth is bounded across include boundaries. The host retains actual parsed checkpoints before commit. Parsing/conversion, filesystem truth, grouped-component effect functions and source-save semantics remain explicit boundaries. Actual source-to-plan traversal now runs in configuration_planning. The checked preorder covers every structured input; child callbacks receive their actual parent-returned context, and accepted nodes store the exact returned recipe/allocation. Complete success and failed prefixes retain real input, callback and state provenance; failed plans expose no acceptable runtime tree. Source conversion, schema/module/context meaning and full Component composition remain explicit obligations. Production configuration adoption now calls the checked native batch. Whole-batch preflight exactly checks current targets, duplicate owners and revision capacity before mutation. Successful adoption installs each real setup body and actual metadata result in input order, advances each version once and returns the original payloads, while retaining declarations, lifecycle, publications and active episodes. Rejection returns the entire input and unchanged native owner. General body/metadata effect laws, destructors, Plugin conversion and full recipe Journal interpretation remain open. Actual native recipe registration, SharedChild insertion, replacement, removal and callback/Value/Service-root returns now construct a typed history indexed in the common value/work/cleanup Journal. Exact before/after RegisteredPlugin values, installed-version origins, complete projection and same-epoch native Episode guards are checked. Rejected calls preserve recipe history; snapshot evidence erases old captures. Arbitrary function/effect meaning and complete native/Node/configuration semantic composition remain open. Actual finite Value/Service returns now authenticate their real write, inverse-registration and failure witnesses against the same Journal commit as the returned Call. Local effects strictly precede that return; foreign histories retain their identity, including locally registered inverses of foreign writes. All retained witnesses erase. Actual Node profile configuration, mount/seal admission and Harness notification selection now execute in the checked owner. Permanent freezing follows from history; exact finite command traces preserve failed prefixes, and notification selects the full real dependency intersection without clearing failed cleanup or unrelated episodes. These are explicit host extensions, not whole-observation stutters. Actual Loader sources now use a checked owner for loaded root/text/resolutions and combined logical checkpoint/pending-sync records. A Save owns its original review stamp before I/O and preserves it across every step. Accepted configuration guards consume that actual cursor; unreviewed/stale/foreign-domain or pending-recovery saves return unchanged without source mutation. Actual processed phases, not report paths, determine updates; origin/frame proofs cover partial failure and duplicate keys. These source transitions are explicit persistence extensions. JSON/source projection/merge meaning, grouped Components and the complete shared Journal remain open. Production Loader configuration now uses Recorded, with its exact protocol/candidate/recovery/update states indexed in the same Journal as native lifecycle, recipes, values and cleanup. Actual forward/inverse/structural poll returns, including Pending and failures, retain callback argument/payload/result provenance across composition. Complete typed projection and accepted-state/commit-input origins are proved; callbacks execute outside the Journal lock. Loaded-source/checkpoint history now shares that owner and Journal; full source/Component meaning and Node semantic composition remain open. The same Recorded owner now holds actual sources and source history; production load/clear/save cannot pair it with a different configuration. Source records authenticate that exact configuration and no-pending status in one Journal write epoch, including its execution index for same-version recovery/refresh. A single read captures both typed histories; complete projection and checkpoint-origin proofs resolve retained bases to actual loads/processed saves and earlier accepted configuration states. JSON/merge/group Component meaning remains separate. NativeRuntime now constructs the actual configuration from its Journal. Loader retains that runtime behind a mutation-only RuntimeAccess view, preventing replacement through its public mutable accessor. One checked read authenticates the actual native member, configuration and sources; the combined snapshot proves complete typed projections in the same captured sequence. This preserves the ordinary adapter ownership premise; it is not whole-Loader semantic verification. Production Node callbacks now carry an opaque native Path captured once from the complete selected parent prefix. Checked issuance, completion and full-path wait queries share the Node history; known_scope_origin includes completed handles without ledger tombstones. JS ALS parent selection and arbitrary callback/HMR semantics remain outside this preservation guarantee. The four native allocators and the actual Rust/Node shared driver domain allocator now execute a verified strong-CAS issuer: returned IDs have linear allocation permissions, failed retries strictly advance, and exhaustion never wraps. This narrows native freshness assumptions but does not discharge Arc/Weak/Mutex-to-Journal association or unify independent namespaces. Actual Execution now installs and retains exactly one checked shared effect-status link per live group. Owner-selected initialization and retirement derive Journal, Begin/work and group association from its invariant, removing the old conditional status-Journal premise. Raw retirement shares the completion commit; erased linear payload permissions and authenticated observations preserve exclusive payload ownership without retaining user errors in the execution. Exact shared-status link frames now compose across 61 real execution/root/Child/value/cleanup/lifecycle methods and both finite program loops. The actual returned Observation authenticates its constructor index and complete member history; no caller-selected initial state is used. Native/Host snapshots and actual recipe return commits now export complete recorded-carrier classification, with both full records and pending inverse obligations. Registered Value/Service reports compose that prefix with actual write/inverse/failure-before-return evidence. Actual non-scalar service storage now uses verified SharedPayload<T: ?Sized>, including Arc<dyn Any + Send + Sync>. Native provide/publish allocate from the real Execution Journal; reads, replacements and version-checked predicate replies retain that owner. Complete typed history projection and production publication/owned/imported service observations join the scalar, work, cleanup, control and scope checkpoint. Payload replacement frames every unrelated scalar/payload observation and updates actual aliases. This closes the inner storage lock boundary, not arbitrary T interiors, outer Episode association or heterogeneous effect/inverse semantics. Explicit checked retirement now empties the storage and returns the real payload, with a terminal Journal record and no resurrection; the host final-slot guard invokes it. Retained read Arcs preserve their own lifetime. Ordinary destructor execution remains an adapter boundary. Native typed payload replacement now separates the reversible Arc/head/depth state from a monotone read revision, reserves inverse capacity, and authenticates the real inverse with a checked type invariant. The real Setup/AsyncSetup entry resolves the Begin-bound service and registers its inverse plus exact retained slot in the actual cleanup queue. Checked dispatch derives completion from guarded restoration and preserves failed inverses. PayloadApply/PayloadRestore are explicit non-stutter Journal steps; same-domain inverse registration settles the actual linear pending obligation. Full-carrier primitive and composing-stack laws do not establish arbitrary callback or original-carrier Component composition. Actual typed cleanup now returns authenticated issue/read/optional-write/acknowledgement evidence. Reads are real Journal cuts, including terminal retired payloads; only successful restoration adds a write. Same-domain interval proofs preserve issued-ticket responsibility and admission-time committed providers through all interleavings, and any later authentic history keeps completed tickets inactive. These checked producers strengthen the concrete primitive connection, without closing general function, Node/configuration semantics or whole-R2 acceptance. Actual Body::Managed registrations now store complete finite heterogeneous root/Child functions. Their checked interpreter executes extensible verified scalar effects and typed replacement, binds all declared keys and current recipe arguments, selects real continuations and explains actual rejection. Full-carrier dependent grammar and parameterized named-port Component laws compose with the actual successful-prefix mixed inverse queue. Authentic same-Journal order includes all earlier local effects across foreign-Journal interruptions, and the real root return joins their witnesses. Alias projection retains an explicit singleton condition; arbitrary callback interiors and new effect families remain separate. | Complete remaining resource/function observations, ordinary Arc/Weak/mutex-to-Episode association and static context inputs remain to be connected. Node object/Fiber/function/HMR semantics, remaining driver dispatch/diagnostics, JS causal ancestry/ALS parent selection and the full Loader workflow are not yet composed with the native interpretation. Finite scalar/typed bodies now compose with their real mixed cleanup queues and invocation returns. Foreign-Journal objects retain separate histories; no global snapshot/order is inferred. |
| complete-step-classification | partial | Native managed success, rejection, cancellation, cleanup failure/retry and old-reply rejection have checked local transitions and retained ownership. Finite registered roots/Child bodies now bind the real recipe, classify the actual rejected final instruction as a strict operation failure/full-recorded-state stutter, and connect complete successful prefixes to their real inverse queue. Slot selection, write, inverse registration and lifecycle completion remain distinct implementation steps. Actual configuration update/recovery polling, forward landing, failed inverse retention and native identity rejection have local contracts; actual structural and file-save phases now have ordered prefix/result contracts. Their full Component/source interpretation remains open; protocol and source transitions now share the native Journal. Node history now classifies each actual protocol mutation, preserves unaffected owners and connects its control projection to paper rules or explicit dynamic-interface/restart extensions; this does not classify arbitrary JS effects as stutters. Node failed completion, preparation, restart and retry now update the same actual status payloads; rejected replies preserve both status and retained admissions, and successful release is linked to its real Begin origin. Actual Node callback receipts and wait results now enter that same history; the core owns withdrawn-publication selections and derives release manifests from its real registry. Finite-history proofs establish publication/callback origin, scope retention/non-reuse and complete batch withdrawal. JS callback dispatch/ancestry and object/Fiber/HMR interpretation remain explicit boundaries. The actual Node release-candidate queue and returned batch now share this history: successful retirement queues real payloads, current retention filters delivery, and finite-history proofs trace writes and retirement while preserving candidates until drain. JSON transfer and JS deletion remain host boundaries. Actual Node reads now select retained Begin/own/cleanup/root publications in that same history. Retained admissions have live leases derived from execution, committed reads preserve the original slot across withdrawal and retry, and returned payloads have real write provenance. The caller-relative read-only lift connects the actual lookup outcome to Definition 29/equation (31); arbitrary JS object methods and whole Component functions remain outside this interpretation. Actual Node interface descriptors and dynamic ownership now share the same history, with derived control correspondence and mount/declaration origins. Actual publication branches and complete provider reconciliation retain exact successful or failed call prefixes; transfer requires drained old commitments and a visible eligible successor. New integrated runtime/negative acceptance remains pending. The actual Loader now uses checked parent-local key construction and inherited enabled status, rejecting duplicate allocation ownership. Exact old/candidate retirement selection and complete retirement/reconstruction loops carry actual callback arguments, host states, results and failed prefixes. Reconstruction preserves saved recipes and parent-local structure; success visits all enabled nodes with correct current parents. Group/include/factory meaning and complete native/Node semantic composition remain open; integrated acceptance for those paths is pending. Actual recursive group/include expansion now uses the checked Expander in file loading and save preflight. Complete derivations preserve actual payloads and child order, bind every included forest to its real read result, and cover the entire contiguous read interval. File ancestry is acyclic and total tree depth is bounded across include boundaries. The host retains actual parsed checkpoints before commit. Parsing/conversion, filesystem truth, grouped-component effect functions and source-save semantics remain explicit boundaries. Actual source-to-plan traversal now runs in configuration_planning. The checked preorder covers every structured input; child callbacks receive their actual parent-returned context, and accepted nodes store the exact returned recipe/allocation. Complete success and failed prefixes retain real input, callback and state provenance; failed plans expose no acceptable runtime tree. Source conversion, schema/module/context meaning and full Component composition remain explicit obligations. Production configuration adoption now calls the checked native batch. Whole-batch preflight exactly checks current targets, duplicate owners and revision capacity before mutation. Successful adoption installs each real setup body and actual metadata result in input order, advances each version once and returns the original payloads, while retaining declarations, lifecycle, publications and active episodes. Rejection returns the entire input and unchanged native owner. General body/metadata effect laws, destructors, Plugin conversion and full recipe Journal interpretation remain open. Actual native recipe registration, SharedChild insertion, replacement, removal and callback/Value/Service-root returns now construct a typed history indexed in the common value/work/cleanup Journal. Exact before/after RegisteredPlugin values, installed-version origins, complete projection and same-epoch native Episode guards are checked. Rejected calls preserve recipe history; snapshot evidence erases old captures. Arbitrary function/effect meaning and complete native/Node/configuration semantic composition remain open. Actual Node profile configuration, mount/seal admission and Harness notification selection now execute in the checked owner. Permanent freezing follows from history; exact finite command traces preserve failed prefixes, and notification selects the full real dependency intersection without clearing failed cleanup or unrelated episodes. These are explicit host extensions, not whole-observation stutters. Actual Loader sources now use a checked owner for loaded root/text/resolutions and combined logical checkpoint/pending-sync records. A Save owns its original review stamp before I/O and preserves it across every step. Accepted configuration guards consume that actual cursor; unreviewed/stale/foreign-domain or pending-recovery saves return unchanged without source mutation. Actual processed phases, not report paths, determine updates; origin/frame proofs cover partial failure and duplicate keys. These source transitions are explicit persistence extensions. JSON/source projection/merge meaning, grouped Components and the complete shared Journal remain open. Production Loader configuration now uses Recorded, with its exact protocol/candidate/recovery/update states indexed in the same Journal as native lifecycle, recipes, values and cleanup. Actual forward/inverse/structural poll returns, including Pending and failures, retain callback argument/payload/result provenance across composition. Complete typed projection and accepted-state/commit-input origins are proved; callbacks execute outside the Journal lock. Loaded-source/checkpoint history now shares that owner and Journal; full source/Component meaning and Node semantic composition remain open. The same Recorded owner now holds actual sources and source history; production load/clear/save cannot pair it with a different configuration. Source records authenticate that exact configuration and no-pending status in one Journal write epoch, including its execution index for same-version recovery/refresh. A single read captures both typed histories; complete projection and checkpoint-origin proofs resolve retained bases to actual loads/processed saves and earlier accepted configuration states. JSON/merge/group Component meaning remains separate. NativeRuntime now constructs the actual configuration from its Journal. Loader retains that runtime behind a mutation-only RuntimeAccess view, preventing replacement through its public mutable accessor. One checked read authenticates the actual native member, configuration and sources; the combined snapshot proves complete typed projections in the same captured sequence. This preserves the ordinary adapter ownership premise; it is not whole-Loader semantic verification. Production Node callbacks now carry an opaque native Path captured once from the complete selected parent prefix. Checked issuance, completion and full-path wait queries share the Node history; known_scope_origin includes completed handles without ledger tombstones. JS ALS parent selection and arbitrary callback/HMR semantics remain outside this preservation guarantee. For the actual shared Host record, complete receipt intervals now classify every intervening step as exact full-record preservation or the corresponding guarded Host transition. Creation comes from the actual allocation commit; provenance, progress flags, error count and assigned Child satisfy a proved interval invariant. This is a Host projection, not full-observation classification. A single classifier now covers every actual Journal commit over all thirteen native Record variants and outstanding managed-inverse obligations. Exact whole-record framing, value operation/strict inverse laws, native R1 rules versus Restart, host/configuration guards and inverse-write causality compose in the complete snapshot trajectory. Real snapshots and registered root/Child return producers export the classification. It covers the recorded native carrier, not opaque payload interiors or the complete host observation. Actual typed Payload replacements now have their own exact same-source increasing-version rule and non-stutter class in that common carrier; this does not infer an arbitrary payload inverse law. Payload retirement is an explicit terminal non-stutter step preserving pending inverse obligations; the retired record never becomes live again. Native typed payload replacement now separates the reversible Arc/head/depth state from a monotone read revision, reserves inverse capacity, and authenticates the real inverse with a checked type invariant. The real Setup/AsyncSetup entry resolves the Begin-bound service and registers its inverse plus exact retained slot in the actual cleanup queue. Checked dispatch derives completion from guarded restoration and preserves failed inverses. PayloadApply/PayloadRestore are explicit non-stutter Journal steps; same-domain inverse registration settles the actual linear pending obligation. Full-carrier primitive and composing-stack laws do not establish arbitrary callback or original-carrier Component composition. Actual typed cleanup now returns authenticated issue/read/optional-write/acknowledgement evidence. Reads are real Journal cuts, including terminal retired payloads; only successful restoration adds a write. Same-domain interval proofs preserve issued-ticket responsibility and admission-time committed providers through all interleavings, and any later authentic history keeps completed tickets inactive. These checked producers strengthen the concrete primitive connection, without closing general function, Node/configuration semantics or whole-R2 acceptance. Actual Body::Managed registrations now store complete finite heterogeneous root/Child functions. Their checked interpreter executes extensible verified scalar effects and typed replacement, binds all declared keys and current recipe arguments, selects real continuations and explains actual rejection. Full-carrier dependent grammar and parameterized named-port Component laws compose with the actual successful-prefix mixed inverse queue. Authentic same-Journal order includes all earlier local effects across foreign-Journal interruptions, and the real root return joins their witnesses. Alias projection retains an explicit singleton condition; arbitrary callback interiors and new effect families remain separate. | A complete classification and paper-step grouping over all remaining host/Node/configuration observations is still open. The scalar/typed finite function package connects its actual steps and return, but current receipts do not turn opaque callback work into a paper stutter. Unconditional original-carrier laws for conflicting aliases and final whole-R2 source-bound acceptance remain required. |

## Work packages

### effects

Effects, tracking and recovery — R1, R2, R3

**Current coverage:** Generic effect laws are encoded and proved; executable resource and fixed-program drivers recover concrete journals. R2 now preserves actual generic payloads, native awaited outputs, retry factories and landed continuation decisions in production adapters. Native finite multi-service calls now retain actual failed prefixes and their inverse registrations, including authenticated computation-rejection receipts. Native extensible scalar effects now bind actual Begin declarations and owner identity, preserve the real input-read checkpoint through computation, and recheck scope/state before registering the exact inverse. Rejected attempts stutter the complete recorded state and pending obligations.

**Open gap:** Production plugin callbacks do not yet instantiate every algebraic premise; opaque cleanup reports do not prove external restoration.

**Next action:** Generalize supported value carriers and extra callback effects, and compose admitted scalar calls with whole root/Child continuations.

**Premises to discharge or identify:**

- Each admitted primitive must establish its stated recovery law and observation relation.
- The caller-to-effect association must come from the executed call, not an expected result supplied by the caller.

**Acceptance:**

- A public executable path instantiates the laws using its actual journal.
- Failure retains the real recovery payload; a mutation that substitutes the inverse is rejected by the relevant contract.

**Review path** (source roles, not a proof of calling relationships):

- contract: [recover](../crates/cordis-kernel/src/foundations.rs)
- execution: [execute_and_recover](../crates/cordis-kernel/src/program.rs)
- execution: [complete](../crates/cordis-kernel/src/cleanup_queue.rs)
- execution: [await_completion](../crates/cordis-kernel/src/async_completion.rs)
- execution: [complete_future](../crates/cordis-kernel/src/cleanup_completion.rs)
- execution: [land_result](../crates/cordis-kernel/src/stage_landing.rs)
- execution: [apply_native_value](../crates/cordis-kernel/src/value_access.rs)
- proof: [primitive_theory](../crates/cordis-kernel/src/value_access.rs)
- proof: [production](../crates/cordis-kernel/src/service_program.rs)
- proof: [frame](../crates/cordis-kernel/src/service_program.rs)
- proof: [source_trace](../crates/cordis-kernel/src/service_program.rs)
- proof: [failed_trace](../crates/cordis-kernel/src/service_program.rs)
- execution: [capture_native_effect](../crates/cordis-kernel/src/native_effect.rs)
- execution: [apply_native_effect](../crates/cordis-kernel/src/native_effect.rs)
- execution: [prepare_observed](../crates/cordis-kernel/src/scalar_effect.rs)
- execution: [commit_calculated](../crates/cordis-kernel/src/scalar_effect.rs)

### context

Coeffects and recursive context — R1

**Current coverage:** R1 completes an explicit finite reified interpretation, with a nontrivial inhabitant, actual control/value/code/journal fields, exact insertion domains and source correspondence.

**Open gap:** Original Definition 28 remains partial: the unrestricted recursive set/function equation is not claimed by the explicit R1-CONTEXT revision.

**Next action:** Use the frozen strict interpretation in R2/R3; continue the original recursive-context audit separately.

**Premises to discharge or identify:**

- Existence of the required context is a proof obligation, not an assumed type equation.
- All values and function fields in the stated carrier need an interpretation.

**Acceptance:**

- Provide an inhabited, nontrivial model with checked observation and editor laws.
- Explain any departure from Definition 28 explicitly and keep its original status independent.

**Review path** (source roles, not a proof of calling relationships):

- contract: [projection_typed](../crates/cordis-kernel/src/paper_typed_context.rs)
- proof: [small_editors_satisfy_laws](../crates/cordis-kernel/src/paper_instantiation.rs)
- proof: [unrestricted_accumulator_obstruction](../crates/cordis-kernel/src/recursive_context.rs)
- proof: [nontrivial_carrier](../crates/cordis-kernel/src/reified_context.rs)
- proof: [reified_representation](../crates/cordis-kernel/src/reified_context.rs)
- proof: [reified_insertion_domain](../crates/cordis-kernel/src/reified_context.rs)

### observations

Operations, observations and independence — R1, R3, R4

**Current coverage:** Least iterator grammars, dependent outcomes and strict partial independence have substantial proofs. R1 adds all-input exact failure transport and declared-interface reads with arbitrary unrelated service values, plus separate admission and recovery relations. R2 derives cumulative alias effects from real service maps at each recorded multi-service write, rather than treating distinct port names as independent. The allocation-key library now unifies built-in and extensible scalar writes. Actual slot/object records derive all alias observations; single_key_refinement proves equation (31), including strict inverse domains, under current singleton resolution. other_alias_changes demonstrates why the unconditional single-key interpretation fails for another alias. allocation_independence instantiates the existing strict theorem for distinct real allocations.

**Open gap:** The explicit R1-DOMAIN revision resolves executable strict domains; original total-domain independence and its general recovery/scheduling consequences remain separate R3/R4 audit work.

**Next action:** Compose actual receipt/continuation transport through the general R3/R4 execution and reordering obligations.

**Premises to discharge or identify:**

- Shared-key value independence must be derived from concrete primitive laws.
- An equal observation must justify any claimed equality of operation domains.
- The alias-aware implementation projection is an explicit semantic extension. The original single-binding lift requires current singleton resolution in the observed map; this is not inferred from service names or imposed as a runtime alias ban.

**Acceptance:**

- Instantiate independence for the actual supported effect family, including nonempty shared-provider executions.
- Preserve real outcomes and returned inverses through every exchange.

**Review path** (source roles, not a proof of calling relationships):

- contract: [operations_independent](../crates/cordis-kernel/src/paper_trace_independence.rs)
- contract: [component_core](../crates/cordis-kernel/src/paper_components.rs)
- proof: [declared_transport](../crates/cordis-kernel/src/guarded_components.rs)
- proof: [no_single_recovery_and_admission_relation](../crates/cordis-kernel/src/typed_child_domain.rs)
- contract: [footprint](../crates/cordis-kernel/src/value_access.rs)
- proof: [project_value_step](../crates/cordis-kernel/src/native_slot_observation.rs)
- proof: [declared_frame](../crates/cordis-kernel/src/native_slot_observation.rs)
- proof: [production](../crates/cordis-kernel/src/service_program.rs)
- proof: [frame](../crates/cordis-kernel/src/service_program.rs)
- proof: [source_trace](../crates/cordis-kernel/src/service_program.rs)
- proof: [failed_trace](../crates/cordis-kernel/src/service_program.rs)
- proof: [single_key_refinement](../crates/cordis-kernel/src/value_alias.rs)
- proof: [other_alias_changes](../crates/cordis-kernel/src/value_alias.rs)
- proof: [allocation_independence](../crates/cordis-kernel/src/value_alias.rs)
- proof: [production_replace](../crates/cordis-kernel/src/value_alias.rs)
- proof: [operation_agrees](../crates/cordis-kernel/src/value_alias.rs)
- proof: [address_origin](../crates/cordis-kernel/src/service_composition.rs)
- proof: [interpret_failure](../crates/cordis-kernel/src/service_composition.rs)

### components

Components, Child and lifting — R1, R2

**Current coverage:** R1 completes semantic parent/continuation/child membership on the full finite strict carrier, actual value/code/journal interpretation, and an executable run_inspected client that constructs its evidence from empty. Original total Component membership is not conflated with this revision. R2 adds real publication/value lookup projection and propagates insertion arguments through LifecycleState. Finite multi-service sub-bodies invoked by ordinary root/Child/group callbacks check the entire Begin declaration range, interpret actual branch outcomes on allocation state and construct source histories for successful and failed prefixes. Stored Body::Services functions now dispatch as actual native roots and Child bodies, bind the current registered recipe, and settle from the real result. All finite resolution schedules inhabit the allocation grammar; actual success and rejected-final-instruction reports instantiate it using Journal-qualified addresses. The strict accumulated inverse equals the actual retained queue suffix.

**Open gap:** General callback and heterogeneous-effect function laws, full original-carrier Component composition and multi-version host values remain open. Complete finite multi-service bodies now have a parameterized allocation interpretation; this does not make dynamic aliases satisfy the original named-port single-key rule. Original unrestricted Gamma and total Component witnesses remain independent.

**Next action:** Extend the established finite-body contracts to heterogeneous checked effects and general continuation interfaces, and connect the remaining Node/configuration observations. Preserve the explicit dynamic-resolution input and conditional named-port interpretation.

**Premises to discharge or identify:**

- Child membership quantifies every input of its stated carrier.
- Kernel correspondence includes explicit identity capacity and fresh-name conditions.
- Full parent membership cannot be inferred from the supplied child witness or successful-prefix grammar membership.

**Acceptance:**

- Prove the typed primitive result and exact failure domain using real component inputs and editor laws.
- Connect the runtime representation and actual captured inverse without assuming insertion succeeded.
- Keep items 28, 55, 56 and 57 open until their complete obligations are met.

**Review path** (source roles, not a proof of calling relationships):

- contract: [typed_instantiate](../crates/cordis-kernel/src/paper_instantiation.rs)
- proof: [equal_observations_different_domains](../crates/cordis-kernel/src/typed_child_domain.rs)
- proof: [kernel_domain](../crates/cordis-kernel/src/typed_child_domain.rs)
- execution: [exercise_domain_gap](../crates/cordis-kernel/src/typed_child_domain.rs)
- execution: [check_insert](../crates/cordis-kernel/src/lib.rs)
- execution: [land_child](../crates/cordis-kernel/src/ownership.rs)
- proof: [member_is_component](../crates/cordis-kernel/src/guarded_components.rs)
- proof: [root_component](../crates/cordis-kernel/src/reified_context.rs)
- proof: [function_correspondence](../crates/cordis-kernel/src/reified_context.rs)
- execution: [run_inspected](../crates/cordis-kernel/src/inspected_run.rs)
- execution: [publish_checked](../crates/cordis-kernel/src/publication_values.rs)
- proof: [appended_value](../crates/cordis-kernel/src/publication_projection.rs)
- host: [publish](../crates/cordis-driver/src/lib.rs)
- execution: [run_native_value_program](../crates/cordis-kernel/src/value_function.rs)
- proof: [production](../crates/cordis-kernel/src/value_function.rs)
- proof: [component](../crates/cordis-kernel/src/service_program.rs)
- execution: [run_service_program](../crates/cordis-kernel/src/service_program.rs)
- proof: [production](../crates/cordis-kernel/src/service_program.rs)
- proof: [frame](../crates/cordis-kernel/src/service_program.rs)
- proof: [source_trace](../crates/cordis-kernel/src/service_program.rs)
- proof: [failed_trace](../crates/cordis-kernel/src/service_program.rs)
- execution: [apply_native_value_chained](../crates/cordis-kernel/src/value_access.rs)
- execution: [join_causes](../crates/cordis-kernel/src/joint_execution.rs)
- proof: [terminal_member](../crates/cordis-kernel/src/value_alias.rs)
- proof: [general_semantics](../crates/cordis-kernel/src/value_access.rs)
- proof: [single_key_effect](../crates/cordis-kernel/src/native_effect.rs)
- execution: [bind](../crates/cordis-kernel/src/service_function.rs)
- execution: [run_service_root](../crates/cordis-kernel/src/service_function.rs)
- proof: [resolved_member](../crates/cordis-kernel/src/service_composition.rs)
- proof: [interpret_dynamic](../crates/cordis-kernel/src/service_composition.rs)
- proof: [interpret_queue](../crates/cordis-kernel/src/service_stack.rs)

### transitions

State observations and lifecycle transitions — R1, R2, R4

**Current coverage:** Kernel transitions, finite checked cleanup histories and several execution/observation bridges are present.

**Open gap:** Whole-context preservation, unrestricted callback provenance, multiple pending admissions and host composition remain open.

**Next action:** Compose actual invocation and request completion with landing and resource release under the common representation.

**Premises to discharge or identify:**

- Target identity and committed provider identity remain distinct.
- External callback result truth and complete invocation ancestry need explicit sources.
- A host extension must have its own specification and a proved relationship to applicable paper constraints.

**Acceptance:**

- Every managed mutation has a proved transition and established caller premises.
- Prove retention and stale-result rejection across concurrent finite histories.
- Replay actual update, cleanup failure and retry through the public runtime.

**Review path** (source roles, not a proof of calling relationships):

- execution: [execute_cleanup](../crates/cordis-kernel/src/cleanup_protocol.rs)
- host: [complete](../crates/cordis-driver/src/lib.rs)
- contract: [related](../crates/cordis-kernel/src/paper_observations.rs)

### recovery

Recovery and episode deletion — R3

**Current coverage:** Concrete journals derive inverse definedness; restricted deletion constructs surviving traces; actual Mixed/Fresh scripts establish terminal value replay.

**Open gap:** Owner-created Child, consumers of owner provisions, interior owner Unload and the general Equation (55) correspondence remain open.

**Next action:** Extend constructive deletion first to an owner that creates a Child, then consumers and multiple episodes.

**Premises to discharge or identify:**

- Source histories must be generated by actual execution.
- Target legality, inverse success and replay equality are conclusions to prove, not supplied premises.

**Acceptance:**

- Cover each newly allowed interaction with a reachable nonempty example.
- Prove general recovery and legal surviving execution for the audited component class.

**Review path** (source roles, not a proof of calling relationships):

- execution: [run_script](../crates/cordis-kernel/src/mixed_driver.rs)
- execution: [run_script](../crates/cordis-kernel/src/fresh_driver.rs)
- proof: [recoverable](../crates/cordis-kernel/src/service_stack.rs)
- proof: [next_queued_inverse](../crates/cordis-kernel/src/service_stack.rs)
- contract: [selected_from](../crates/cordis-kernel/src/cleanup_completion.rs)

### global

Progress, support and canonical form — R1, R4

**Current coverage:** Fixed-registry bounds, a real single-actor finite loop and scoped trace normalization exist; original support and unconditional completion counterexamples are retained.

**Open gap:** General dynamic-registry progress and arbitrary-schedule canonical/confluence results are open.

**Next action:** Transport real names, inputs and receipts through legal reorderings; connect the selected semantics to maximal lifecycle execution.

**Premises to discharge or identify:**

- Pure lifecycle maximality differs from host fairness and unrelated host work.
- Termination and finite-name/step conditions must have code or environment sources.
- Original refutations of 71, 75 and 77 are not silently replaced by corrected claims.

**Acceptance:**

- Construct a legal reordered execution and prove its applicable endpoint relation.
- Derive progress under stated conditions without assuming the desired final state or reverse-step legality.

**Review path** (source roles, not a proof of calling relationships):

- execution: [run_until_blocked](../crates/cordis-kernel/src/fresh_run.rs)
- proof: [finite_execution_refines](../crates/cordis-kernel/src/refinement.rs)

### configuration

Configuration entries and host interpretation — R2

**Current coverage:** The actual Loader owns accepted/candidate snapshots, recovery inputs and a checked Batch of real keyed ConfigUpdatePlans. Reversible owns their actual forward/inverse Futures and prevents inverse construction before forward landing. Batch admits an actual success prefix and retains failed/pending inverses in reverse order. Native Target checks domain, ID, activation and recipe revision at update/adoption; commit requires successful updates and recovery requires inverse drain without a revision increment. Definition 81 still has the executable six-field record and explicit resolved-leaf projection. The actual ordered Tree now owns immutable recipes and checked names/parent indices. Mount identities come from private native Allocation records with certified native snapshots; actual callback results select identity changes and readiness checks parent ownership. Structural forward/recovery phases gate actual Loader work; erased prefix traces establish every successful phase before commit/recovery. Production recover_with extracts from the retained recovery payload after reconstruction, rather than accepting a caller-selected snapshot. Actual Save owns immutable document inputs and orders Check/Prepare/Recheck/Replace/Sync from real callback results. The returned progress distinguishes replacement from durability, retains failed prefixes and stops later dispatch. Production save plans retain checked accepted-revision/domain stamps, rejecting revision ABA and foreign-runtime reuse before I/O. The actual Loader now uses checked parent-local key construction and inherited enabled status, rejecting duplicate allocation ownership. Exact old/candidate retirement selection and complete retirement/reconstruction loops carry actual callback arguments, host states, results and failed prefixes. Reconstruction preserves saved recipes and parent-local structure; success visits all enabled nodes with correct current parents. Group/include/factory meaning and the common configuration/native/Node Journal remain open; new integrated runtime/negative acceptance is pending. Actual recursive group/include expansion now uses the checked Expander in file loading and save preflight. Complete derivations preserve actual payloads and child order, bind every included forest to its real read result, and cover the entire contiguous read interval. File ancestry is acyclic and total tree depth is bounded across include boundaries. The host retains actual parsed checkpoints before commit. Parsing/conversion, filesystem truth, grouped-component effect functions and source-save semantics remain explicit boundaries. Actual source-to-plan traversal now runs in configuration_planning. The checked preorder covers every structured input; child callbacks receive their actual parent-returned context, and accepted nodes store the exact returned recipe/allocation. Complete success and failed prefixes retain real input, callback and state provenance; failed plans expose no acceptable runtime tree. Source conversion, schema/module/context meaning and full Component composition remain explicit obligations. Production configuration adoption now calls the checked native batch. Whole-batch preflight exactly checks current targets, duplicate owners and revision capacity before mutation. Successful adoption installs each real setup body and actual metadata result in input order, advances each version once and returns the original payloads, while retaining declarations, lifecycle, publications and active episodes. Rejection returns the entire input and unchanged native owner. General body/metadata effect laws, destructors, Plugin conversion and full recipe Journal interpretation remain open. Actual native recipe registration, SharedChild insertion, replacement, removal and callback/Value/Service-root returns now construct a typed history indexed in the common value/work/cleanup Journal. Exact before/after RegisteredPlugin values, installed-version origins, complete projection and same-epoch native Episode guards are checked. Rejected calls preserve recipe history; snapshot evidence erases old captures. Arbitrary function/effect meaning and complete native/Node/configuration semantic composition remain open.

**Open gap:** Complete group/include Component semantics, module/schema/context meaning, configuration-to-Component interpretation, source-checkpoint semantics and complete composition with native/Node observations remain open. Ordered tree/update/save protocols and actual result provenance are checked; arbitrary callback inverse laws, external filesystem truth and convergence remain explicit premises.

**Next action:** Compose group/include Component meaning, native allocations and source checkpoints with the complete configuration/native/Node observation. Preserve explicit external I/O and liveness premises.

**Premises to discharge or identify:**

- URL resolution and plugin configuration validation are external adapter operations.
- Whole-tree reconciliation is not implied by correctness of a single record.

**Acceptance:**

- Trace accepted configuration changes to exact registered components and their cleanup/update actions.
- Retain failures and recovery inputs in a real configuration workflow.

**Review path** (source roles, not a proof of calling relationships):

- contract: [bound_effect](../crates/cordis-kernel/src/configuration_entry.rs)
- host: [as_paper_entry](../crates/cordis/src/loader.rs)
- execution: [commit](../crates/cordis-kernel/src/configuration_transaction.rs)
- host: [apply_prepared](../crates/cordis/src/loader.rs)
- execution: [poll_apply](../crates/cordis-kernel/src/configuration_batch.rs)
- execution: [poll_rollback](../crates/cordis-kernel/src/configuration_batch.rs)
- contract: [restored_from](../crates/cordis-kernel/src/configuration_future.rs)
- execution: [configuration_target_is_current](../crates/cordis-kernel/src/configuration_runtime.rs)
- host: [poll_rollback](../crates/cordis/src/config.rs)
- execution: [mount](../crates/cordis-kernel/src/configuration_tree.rs)
- execution: [ready](../crates/cordis-kernel/src/configuration_tree.rs)
- execution: [configuration_allocation](../crates/cordis-kernel/src/configuration_runtime.rs)
- execution: [poll_structure](../crates/cordis-kernel/src/configuration_transaction.rs)
- execution: [recover_with](../crates/cordis-kernel/src/configuration_transaction.rs)
- execution: [step](../crates/cordis-kernel/src/configuration_save.rs)
- execution: [progress](../crates/cordis-kernel/src/configuration_save.rs)
- execution: [accepts_save](../crates/cordis-kernel/src/configuration_transaction.rs)
- host: [commit_with](../crates/cordis/src/persistence.rs)
- execution: [prepare_entry](../crates/cordis-kernel/src/configuration_identity.rs)
- proof: [qualified_key_identity](../crates/cordis-kernel/src/configuration_identity.rs)
- execution: [insert_entry](../crates/cordis-kernel/src/configuration_identity.rs)
- execution: [retire_into](../crates/cordis-kernel/src/configuration_selection.rs)
- execution: [reconstruct](../crates/cordis-kernel/src/configuration_reconstruction.rs)
- contract: [chain](../crates/cordis-kernel/src/configuration_reconstruction.rs)
- execution: [expand](../crates/cordis-kernel/src/configuration_expansion.rs)
- contract: [valid_for](../crates/cordis-kernel/src/configuration_expansion.rs)
- contract: [valid](../crates/cordis-kernel/src/configuration_expansion.rs)
- contract: [read_call](../crates/cordis-kernel/src/configuration_expansion.rs)
- contract: [valid_error](../crates/cordis-kernel/src/configuration_expansion.rs)
- host: [read_tree_cached](../crates/cordis/src/loader.rs)
- contract: [failure_from](../crates/cordis-kernel/src/configuration_expansion.rs)
- execution: [plan](../crates/cordis-kernel/src/configuration_planning.rs)
- contract: [preorder](../crates/cordis-kernel/src/configuration_planning.rs)
- contract: [prefix](../crates/cordis-kernel/src/configuration_planning.rs)
- contract: [chain](../crates/cordis-kernel/src/configuration_planning.rs)
- contract: [matches_input](../crates/cordis-kernel/src/configuration_planning.rs)
- contract: [node_from_call](../crates/cordis-kernel/src/configuration_planning.rs)
- host: [prepare](../crates/cordis/src/loader.rs)
- execution: [preflight_configurations](../crates/cordis-kernel/src/configuration_adoption.rs)
- execution: [adopt_configurations](../crates/cordis-kernel/src/configuration_adoption.rs)
- contract: [ready](../crates/cordis-kernel/src/configuration_adoption.rs)
- contract: [rejected](../crates/cordis-kernel/src/configuration_adoption.rs)
- contract: [metadata_call](../crates/cordis-kernel/src/configuration_adoption.rs)
- contract: [adopted](../crates/cordis-kernel/src/configuration_adoption.rs)
- contract: [prefix](../crates/cordis-kernel/src/configuration_adoption.rs)
- contract: [framed](../crates/cordis-kernel/src/configuration_adoption.rs)
- execution: [replace](../crates/cordis-kernel/src/native_runtime.rs)
- proof: [with_host_properties](../crates/cordis-kernel/src/native_host.rs)
- host: [adopt_config_recipes](../crates/cordis/src/runtime.rs)
- proof: [installed_origin](../crates/cordis-kernel/src/recipe_history.rs)
- proof: [complete_projection](../crates/cordis-kernel/src/recipe_history.rs)
- proof: [invocation_origin](../crates/cordis-kernel/src/recipe_history.rs)
- execution: [advance](../crates/cordis-kernel/src/recipe_history.rs)
- execution: [snapshot](../crates/cordis-kernel/src/recipe_history.rs)
- contract: [native_guard](../crates/cordis-kernel/src/recipe_execution.rs)
- execution: [record_recipes](../crates/cordis-kernel/src/native_runtime.rs)
- execution: [recipe_snapshot](../crates/cordis-kernel/src/native_runtime.rs)
- execution: [run_value_root](../crates/cordis-kernel/src/value_function.rs)
- execution: [run_service_root](../crates/cordis-kernel/src/service_function.rs)

## Every numbered item

| Paper item | Original status | Primary work package | Milestones |
| --- | --- | --- | --- |
| Definition 1: Twisted composition | formalized | [effects](#effects) | R1, R2, R3 |
| Definition 2: Effect context | formalized | [effects](#effects) | R1, R2, R3 |
| Definition 3: Tracking | formalized | [effects](#effects) | R1, R2, R3 |
| Theorem 4: Tracking projection | proved | [effects](#effects) | R1, R2, R3 |
| Theorem 5: Tracking monoid homomorphism | proved | [effects](#effects) | R1, R2, R3 |
| Definition 6: Recovery | formalized | [effects](#effects) | R1, R2, R3 |
| Theorem 7: Tracking preserves recovery | proved | [effects](#effects) | R1, R2, R3 |
| Definition 8: Witnessed effect | formalized | [effects](#effects) | R1, R2, R3 |
| Definition 9: Effect composition | formalized | [effects](#effects) | R1, R2, R3 |
| Theorem 10: Effect monoid | proved | [effects](#effects) | R1, R2, R3 |
| Theorem 11: Witness composition | proved | [effects](#effects) | R1, R2, R3 |
| Definition 12: Effect lifting | formalized | [effects](#effects) | R1, R2, R3 |
| Theorem 13: Lift preserves composition | proved | [effects](#effects) | R1, R2, R3 |
| Theorem 14: Lifted forward projection | proved | [effects](#effects) | R1, R2, R3 |
| Theorem 15: Lifted recovery | proved | [effects](#effects) | R1, R2, R3 |
| Theorem 16: Finite local temporal composability | proved | [effects](#effects) | R1, R2, R3 |
| Definition 17: Witnessed iterators | formalized | [effects](#effects) | R1, R2, R3 |
| Definition 18: Iterator lifting | formalized | [effects](#effects) | R1, R2, R3 |
| Definition 19: Dependent coeffect context | formalized | [context](#context) | R1 |
| Definition 20: Get and set | formalized | [context](#context) | R1 |
| Definition 21: Coeffect specification | formalized | [context](#context) | R1 |
| Definition 22: Coeffect satisfaction | formalized | [context](#context) | R1 |
| Definition 23: Effect realizations | formalized | [context](#context) | R1 |
| Definition 24: Isolated coeffect context | formalized | [context](#context) | R1 |
| Definition 25: Get, set and isolate | formalized | [context](#context) | R1 |
| Definition 26: Interception context | formalized | [context](#context) | R1 |
| Definition 27: Get, set and intercept | formalized | [context](#context) | R1 |
| Definition 28: Combined recursive context | partial | [context](#context) | R1 |
| Definition 29: Operations and outcomes | formalized | [observations](#observations) | R1, R3, R4 |
| Definition 30: Context-mediated iterator grammar | formalized | [observations](#observations) | R1, R3, R4 |
| Definition 31: Observation tests | formalized | [observations](#observations) | R1, R3, R4 |
| Lemma 32: Coarsest observational equivalence | proved | [observations](#observations) | R1, R3, R4 |
| Definition 33: Context equivalence | formalized | [observations](#observations) | R1, R3, R4 |
| Definition 34: Lifting relations | formalized | [observations](#observations) | R1, R3, R4 |
| Lemma 35: Partial equivalence of maps and iterators | proved | [observations](#observations) | R1, R3, R4 |
| Definition 36: Observational effect witness | formalized | [observations](#observations) | R1, R3, R4 |
| Definition 37: Observational iterator witness | formalized | [observations](#observations) | R1, R3, R4 |
| Lemma 38: Transport of effect laws to observations | proved | [observations](#observations) | R1, R3, R4 |
| Lemma 39: Context-mediated admissibility | proved | [observations](#observations) | R1, R3, R4 |
| Definition 40: Reachable iterators and monoids | formalized | [observations](#observations) | R1, R3, R4 |
| Lemma 41: Generator closure laws | proved | [observations](#observations) | R1, R3, R4 |
| Definition 42: Iterator independence | formalized | [observations](#observations) | R1, R3, R4 |
| Theorem 43: Recovery in any inverse permutation | proved | [observations](#observations) | R1, R3, R4 |
| Definition 44: Operation independence | formalized | [observations](#observations) | R1, R3, R4 |
| Theorem 45: Distinct-key independence | proved | [observations](#observations) | R1, R3, R4 |
| Definition 46: Witnessed coeffect | formalized | [observations](#observations) | R1, R3, R4 |
| Theorem 47: Interface compatibility implies independence | partial | [observations](#observations) | R1, R3, R4 |
| Definition 48: Components | formalized | [components](#components) | R1, R2 |
| Definition 49: Fibers | formalized | [components](#components) | R1, R2 |
| Definition 50: Registry and publication | formalized | [components](#components) | R1, R2 |
| Definition 51: All-fiber key-restricted projection | formalized | [components](#components) | R1, R2 |
| Definition 52: Child creation inverse | formalized | [components](#components) | R1, R2 |
| Definition 53: Target and quiescence | formalized | [components](#components) | R1, R2 |
| Definition 54: Reliance | formalized | [components](#components) | R1, R2 |
| Definition 55: Confinement | partial | [components](#components) | R1, R2 |
| Definition 56: Context lift | partial | [components](#components) | R1, R2 |
| Lemma 57: Lifted admissibility | partial | [components](#components) | R1, R2 |
| Definition 58: Execution and episode observations | formalized | [transitions](#transitions) | R1, R2, R4 |
| Lemma 59: Rule frame facts | proved | [transitions](#transitions) | R1, R2, R4 |
| Lemma 60: Observational rule invariance | partial | [transitions](#transitions) | R1, R2, R4 |
| Lemma 61: Name equivariance | partial | [transitions](#transitions) | R1, R2, R4 |
| Lemma 62: Vestigial entries | refuted | [transitions](#transitions) | R1, R2, R4 |
| Definition 63: Well-formed registries | formalized | [transitions](#transitions) | R1, R2, R4 |
| Theorem 64: Preservation | partial | [transitions](#transitions) | R1, R2, R4 |
| Definition 65: Independence and entanglement | partial | [transitions](#transitions) | R1, R2, R4 |
| Lemma 66: Pairwise independence | partial | [transitions](#transitions) | R1, R2, R4 |
| Lemma 67: Entangled steps | partial | [transitions](#transitions) | R1, R2, R4 |
| Theorem 68: Global recovery exactness | partial | [recovery](#recovery) | R3 |
| Corollary 69: Terminal recovery | partial | [recovery](#recovery) | R3 |
| Theorem 70: Lifecycle ordering | partial | [transitions](#transitions) | R1, R2, R4 |
| Theorem 71: Resolution coherence | refuted | [global](#global) | R1, R4 |
| Definition 72: Provider precedence | formalized | [global](#global) | R1, R4 |
| Theorem 73: Progress and termination | partial | [global](#global) | R1, R4 |
| Definition 74: Support equation | formalized | [global](#global) | R1, R4 |
| Lemma 75: Support well-foundedness | refuted | [global](#global) | R1, R4 |
| Definition 76: Total provision | formalized | [global](#global) | R1, R4 |
| Lemma 77: Support at quiescence | refuted | [global](#global) | R1, R4 |
| Lemma 78: Transposition | partial | [global](#global) | R1, R4 |
| Lemma 79: Episode deletion | partial | [recovery](#recovery) | R3 |
| Theorem 80: Canonical form and confluence | partial | [global](#global) | R1, R4 |
| Definition 81: Configuration entries | formalized | [configuration](#configuration) | R2 |

## Integration obligations

| Obligation | Original status | Milestones |
| --- | --- | --- |
| whole-lifecycle | open | R1, R3, R4, R5 |
| corrected-specification | open | R1, R4, R5 |
| executable-simulation | open | R1, R2, R5 |
| host-boundary | open | R2, R4, R5 |

R0 completion means this planning baseline is recorded. R1–R5 require their own semantic and implementation evidence.
Original refutations remain refuted. The original `check-paper-coverage.py --require-complete` gate is unchanged.
