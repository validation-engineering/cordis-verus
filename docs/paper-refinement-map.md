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
| R2 | Refinement of production execution | complete | R1 |
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

R2 completion scope: Managed-production/v1: the executable finite managed-function carrier, native Journal/configuration composition and Node protocol/reference interpretation. Applicable R1 strict semantics, alias conditions and explicit extensions remain in force. Arbitrary callback interiors and external I/O are not semantically refined; the original paper ledger and integration obligations are unchanged. Source-bound acceptance is reproduced by scripts/check-r2-acceptance.py.

See [R2 acceptance](r2-acceptance.md) for all three criteria, explicit boundaries and reproducible evidence.


## R2 execution progress

Completed managed-production/v1 review against the three unchanged R2 exit criteria. Current evidence requires scripts/check-r2-acceptance.py on matching source; neither this inventory nor local payload contracts alone establish whole-host or original-paper equivalence.

[Execution contracts and boundaries](r2-execution.md) · [执行合同与边界（中文）](r2-execution.zh-CN.md)

| Work item | Status | Scope | Remaining boundary |
| --- | --- | --- | --- |
| managed-payloads | complete | Actual generic payload ownership, key-local visible lookup, checked owner/generation/domain, lease-derived identity and atomic managed payload release. | JS object contents and Rust interior mutation are not interpreted by payload identity. |
| awaited-results | complete | Native async output/origin pairing and completion from the actual returned Result, retaining both host failure policies. | Native Future/result transport and actual Poll normalization do not prove external I/O truth, polling/panic capture or eventual return. Native registered FnMut provenance is checked separately. |
| landed-continuation | complete | Actual inverse payload landing and continuation selection from result/cancellation, with the accumulator-step projection. | The opaque inverse function effect is not interpreted by a token/payload accumulator. |
| invocation-effect-origin | complete | Public native Value/Service/Managed root and Child entry points execute the actual stored finite body after binding authoritative keys, recipe arguments, version and owner/Episode. Verified scalar and typed replacement laws explain real inputs, results, continuation selection, rejection and the exact retained mixed inverse queue. Reports join all preceding same-Journal effect/inverse witnesses to the actual return; interleavings and foreign Journal identities are preserved. Full-carrier grammar and parameterized Component laws include both branches; the literal named-port projection retains explicit alias conditions. Ordinary callback argument/result transport is checked without asserting arbitrary callback effect laws. | Complete for the installed finite managed functions and their verified scalar/typed primitive sum, including actual argument/result/continuation/inverse provenance. Arbitrary callbacks and additional unverified effect families have no semantic theorem; new families must supply laws and execution connections. Named-port specialization retains the explicit singleton-alias condition. No external I/O truth or eventual Future return is inferred. |
| production-composition | complete | The actual native owner composes registration, recipe, lifecycle, typed publication, shared slots, work, polling, cleanup and retained inverse obligations through one checked Journal. Loader configuration/source projections use the same captured cut, complete indexed histories and real accepted-configuration/Insert origins. NodeRuntime composes complete protocol observations, dynamic interfaces, versioned publication/lease/check state, admissions, scopes and cleanup decisions. The actual Bridge owns reference identity, Fiber binding and pending callback claims, with exact transitions and real protocol guard cuts. Actual producer snapshots invoke their combination proofs; callers do not supply expected outcomes or traces. Independent owners retain their own order. | Within managed-production/v1 the producer, whole-history interpretation and acceptance review are complete. The explicit boundaries in r2Acceptance remain: arbitrary callback/object interiors, foreign codecs, Node-API/JS/ALS, ordinary synchronization, scheduling, filesystem truth and external static lease truth. These effects are not certified as stutters. Separate Journals retain separate orders; conflicting aliases retain their explicit interpretation conditions. General recovery, global termination and confluence belong to R3/R4. |
| complete-step-classification | complete | For every actual native Journal event, production_step preserves all thirteen record variants and pending obligations and proves a paper control step, exact full-record stutter, or separately specified extension. Node production_step retains the complete protocol relation and distinguishes full Observation::same from control-only equality. Production_trace derives continuous projections from each actual producer history; typed configuration/source and bridge reference histories retain exact transitions and provenance. Managed function/inverse semantics remain linked through the actual interpreter and receipts, rather than inferred from a control projection. Only appropriate extension-free projections enter strict paper closure. | Within managed-production/v1 the producer, whole-history interpretation and acceptance review are complete. The explicit boundaries in r2Acceptance remain: arbitrary callback/object interiors, foreign codecs, Node-API/JS/ALS, ordinary synchronization, scheduling, filesystem truth and external static lease truth. These effects are not certified as stutters. Separate Journals retain separate orders; conflicting aliases retain their explicit interpretation conditions. General recovery, global termination and confluence belong to R3/R4. |

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

**Current coverage:** The real native Loader combines the checked configuration transaction, update Future/batch, structural tree, include expansion, complete preorder, native recipe adoption and source/checkpoint histories. Package 3 adds actual module-table and scope binding ownership; Modules::prepare selects the retained Definition, applies interception, executes the stored structural schema and returns an immutable Prepared recipe whose raw/effective values satisfy the joint normalization contract. Mount, config updates and recovery use that recipe. Built-in group roots use the verified empty service program; their owned children use the existing structural insertion protocol. Recursive three-way merging covers every input key, complete keyed child ordering prevents dropped members, and source projection is accepted only after the actual proposed documents expand back to the entire requested tree. Save acknowledgement, revision ABA, partial progress and retry contracts remain in force. Package 4 now constructs total native and Node protocol step interpretations from actual producer checkpoints. Bridge mutations have continuous exact reference histories with real protocol guard cuts and issuance/claim origins. Configuration/native/source projections share one captured Journal with distinct keys, complete coverage and exact earlier accepted-source reviews. Ready configuration trees derive root/group/Child elaboration from real Insert events and original parents. Independent owners retain separate histories and ordinary adapter effects are explicit boundaries; see docs/r2-production-composition.md. Package 5 supplies a real Loader mixed-Child failure/recovery/source-save scenario and a Node dynamic-publication/failed-cleanup/stale-ticket scenario, with fixed-scope review and source-bound acceptance.

**Open gap:** The managed-production/v1 execution review is complete; arbitrary factory bodies, codec/filesystem truth and unconditional original total Component membership remain explicit interpretation boundaries. Original Definition 81 and whole-paper integration retain their existing audit outcomes; R3/R4 general recovery, termination and confluence remain open.

**Next action:** Use the accepted execution contracts in R3 recovery and R4 progress; preserve the original paper audit and rerun check-r2-acceptance.py when changing this production scope.

**Premises to discharge or identify:**

- JSON decoding/encoding, scalar classification and IEEE comparison encoding, URL/filesystem identity and external I/O are audited adapter boundaries; recursive schema/merge decisions execute in the kernel.
- Factory callbacks and arbitrary JS schema/module evaluation require their own function contracts; built-in native groups have a checked Unit root and structurally managed children.
- Whole-tree convergence does not follow from record normalization or a successful save round trip.

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
- execution: [prepare](../crates/cordis-kernel/src/configuration_module.rs)
- contract: [wf](../crates/cordis-kernel/src/configuration_module.rs)
- execution: [entry](../crates/cordis-kernel/src/configuration_module.rs)
- execution: [extend](../crates/cordis-kernel/src/configuration_binding.rs)
- execution: [validate](../crates/cordis-kernel/src/configuration_schema.rs)
- contract: [normalized](../crates/cordis-kernel/src/configuration_schema.rs)
- execution: [apply](../crates/cordis-kernel/src/configuration_data.rs)
- execution: [merge](../crates/cordis-kernel/src/configuration_data.rs)
- contract: [valid](../crates/cordis-kernel/src/configuration_data.rs)
- execution: [ordered](../crates/cordis-kernel/src/configuration_data.rs)
- execution: [check](../crates/cordis-kernel/src/configuration_data.rs)

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
