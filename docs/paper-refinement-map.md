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
- execution: [commit_calculation](../crates/cordis-kernel/src/scalar_effect.rs)

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

**Current coverage:** Concrete journals derive inverse definedness and restricted deletion constructs surviving traces. The actual Mixed/Fresh run_script and run_inspected now expose one empty-origin recovery_history witness for all episode cuts, including open current episodes, owner-created Child, consumers of owner services, repeated activation and interior owner Unload. Current stored-receipt restoration has a defined result whose table observation equals the foreign replay. This is the concrete synchronous Unit/Child/Provision/Xor specialization of Equations (55)/(56), not legal lifecycle deletion or the complete R2 effect carrier. The production run_function and registered root now establish authentic same-allocation scalar/typed history links. Quiet actual Journal gaps derive mixed replay and stored inverse-word definedness from per-allocation first observations, including shared aliases and failed prefixes. Real typed restore/cleanup attempts prove exact semantic-head domains and identify actual conflicting mutations or retirement. Registered root/Child dispatch now retains an authentic native Begin witness derived from the current owner history and proves same-Journal writes and invocation return follow that checkpoint, including empty functions and failed prefixes. Actual registered dispatch now establishes decoded Begin/return value recovery and the exact retained mixed queue inverse under same-Journal boundary/gap conditions. Typed interior gaps may return to an earlier semantic head at a newer revision; authenticated indexed histories prove the full state link and locate the actual intervening Restore. Real typed storage maintains the Apply/Replace/Restore history invariant, and successful cleanup attempts at newer revisions identify their preceding Restore. The actual Mixed script recovery witness now also constructs legal deletion for each admitted closed private-table episode, allowing foreign Child lifecycles, dynamic registry changes and old inverse journals. The real Xor library supplies strict partial commutation and raw-outcome stability; the constructed target table projection is linked to the same source episode foreign replay. The real mixed cleanup dispatcher now carries erased actual before/after queue boundaries, authentic scalar/typed read and restoration observations, exact slot consumption/retention and acknowledgement linkage. Execution retry exports preservation of the inverse and a strictly newer attempt; emitted completions compose retry and old-ticket closure. Finite source-linked cleanup results derive actual restoration success and recovery of registered Begin values for the retained suffix without assuming inverse success. Foreign managed forwards, blocked cleanup, raw restoration and later retry now compose in one finite source-linked value trajectory. Real semantic depth derives per-allocation inverse ordering and permits independent allocations to restore in different orders. A finite coverage condition on actual later successful restore events proves the constructed inverse record is exhausted, rather than assuming it is empty. The real native release path exports an erased Unload witness from its indexed host history with the exact preceding episode owner. Under matching native/episode identities, actual receipt prefixes and per-allocation quiet tails, the final common Unload observation equals the actual Begin values for the invocation's touched allocations. Actual release now retains the sealed cleanup membership receipt; in the same Journal, the actual native Unload commit follows that receipt. Historical groups, including those removed before final seal, have a source-derived drain cut; previously occupied registered tokens have an actual non-failed completion before that cut. Matching authentic managed acknowledgements then derive scalar/typed success, excluding callback Drained. The release-based value theorem derives local inverse closure from complete source acknowledgement coverage rather than a supplied local-success condition; foreign restoration remains explicit. Actual scalar/typed inverse insertion now certifies the owned group membership in the existing Journal write epoch, including the exact queue key, domain and token. The running interpreter and registered root/Child return export this source property for every retained prefix. Sealing cannot precede these authentic live-membership insertions, so unload_recovers_registered derives registration ordering and membership from the production postconditions; complete consuming-acknowledgement coverage remains explicit at that entry point. A tracked History collector now starts from actual retained slots; dispatch_recorded invokes the production mixed dispatcher and records authentic managed outputs, while retry_recorded preserves the actual inverse and newer attempt identity. The collector proves that every initially managed slot is retained or consumed by its authentic matching restoration. Persistent receipt comparison and token non-reuse derive complete local acknowledgement coverage at actual Unload from this continuous path and a matching drained terminal queue. unload_recovers_from_history composes that derived coverage with actual registration membership and the existing value endpoint, without a supplied cleanup_emitted or local-success premise. Ordinary cleanup removal now delegates to remove_observed and returns the exact drained queue only on success. The ordinary native release path emits one ReleaseObservation containing its actual result, authentic Unload and erased pre-release drained groups; rejection yields neither endpoint nor terminal groups. unload_recovers_from_release uses that source bundle directly rather than requiring callers to assemble a terminal queue or supply its drain status. RecordedExecution now owns the actual return-time Execution and per-group collectors, maintains live/terminal queue correspondence across mixed dispatch, single/native retry, Finish, withdrawal, early removal and actual Unload, and records managed dispatch observations across captured groups. Native retry proves preserved slots/queue identities and fresh lifecycle/per-queue tickets. run_recorded_root attaches the stored-function return directly; unload_recovers_from_owner consumes the retained source histories and actual terminal boundaries without caller-carried collectors or terminal snapshots.  History extension now appends every later actual registration without resetting earlier token identities or consumption receipts; release recovery accepts the preserved return-time prefix. RecordedExecution captures actual origins for subsequently allocated effect groups and keeps historical identities below the real monotone allocator across retry/seal. A maintained host-issued invariant and restricted HostAction retry type separate synchronous/awaited host acknowledgements from managed inverse consumption; actual Future output remains bound to its captured ticket. The recorded owner now delegates real work take/completion, effect activation/checkout/admission/landing/cancellation/retirement and atomic Child admission to their production methods. Actual poll output appends the returned inverse even after cancellation; rejected or pending replies cannot fabricate obligations. Native Child request, inverse and handle share the same actual allocation. Later run_function calls preserve the original baseline, extend the obligations for the complete successful prefix and automatically record each actual forward value event across all retained group histories. Recorded native root return now seeds an authentic same-Journal call boundary; later managed calls carry it to real writes and close with an actual read-epoch checkpoint certifying owner state and all local report receipts. Receipt coverage composes across failed prefixes, empty calls and finite call sequences without caller-supplied timestamps. The actual recorded dispatcher now passes the retained recovery boundary to the real Pop commit; scalar/typed attempts follow its actual issue, and the real success/failure acknowledgement becomes the next boundary. Same-Journal calls, cleanup and retries compose through authentic receipt coverage without extra cleanup locks. NativeRuntime::retire_shared_child now exports pending cancellation or the actual assigned Child Retire transition while preserving recipes, publications and episode owners. A real parent/Child/consumer regression permits parent Unload while the Child remains blocked by a consumer, including consumer cleanup failure/retry and separate Child Unload/Remove. Native retirement now retains the real shared-slot persistent decision and native receipt. Actual Unload exposes native/paper lifecycle pre/post projections. retire_and_release_child is an ordinary Rust callable client that performs retirement, checks the actual episode and composes guarded release; its native commit follows both the retirement receipt and sealed cleanup source. The resulting endpoint relation derives exact child owner/publication removal, the consumer guard and retired Inactive state; cancellation excludes later assignment. RecordedExecution source queries relate these witnesses to the creating episode and its retained native inverse. Runtime cases exercise blocked release, parent-execution substitution, successful Child release, repeated release, Begin at the retired endpoint and cancellation before late dispatch. NativeRuntime now automatically collects actual shared-slot Birth, Retirement and managed Unload sources in an erased append-only Ledger. Birth retains the actual Insert and parent EpisodeOwner, including action ticket and work domain. Every stored native receipt is covered by the same native member's committed Journal prefix; native operations preserve the collection. Retirement and the successful executable Child release derive the applicable collected resolution from these sources. RecordedExecution checks completeness against every original native inverse across all retained groups and extracts the authentic endpoint; parent drain does not imply Child completion. Actual registration and Begin wrappers now export the executable allocation bound; NativeRuntime maintains fresh insertions through all native transitions and certified snapshots. Collected assigned Child endpoints remain terminal at a later real checkpoint despite arbitrary native activity or separate Remove. unload_recovers_with_children combines this terminal state with restored invocation values and the absence of the invocation's actual forward positions from pending registration at that same checkpoint. The scalar/typed interpreter exports the actual settlement source. Child completeness, foreign closure and unchanged value tails remain explicit source conditions. Full publication/pending recovery across intermediate cuts, ordinary-host migration and complete external observation remain open. Observed-owner recovery now derives foreign restoration from actual report-step ownership, retained terminal groups and covered managed dispatches. Executable run_function_observed and dispatch_observed append the same actual observations to both owners, including failed prefixes and failed cleanup, and preserve existing source coverage. Same-Journal receipt joins carry preceding observations through real calls and cleanup without extra locks. unload_recovers_from_observed_owners combines this source-derived closure with the common-cut theorem; it does not infer complete external observation or value continuity. Actual typed restore attempts now retain persistent payload-history witnesses from the locked storage, including interference failures and retirement observations. RecordedExecution owns an erased per-source prefix collection: actual root/Child functions, later managed calls, cleanup dispatch and cross-owner observers retain or merge real evidence, and every stored event decoder is covered by the owner invariant. Source Journal gaps derive value continuity; creating records and absence of duplicate successful observations derive outstanding-inverse membership. recover_recorded_prefix connects these results to the managed specialization of Equation (55); unload_recovers_from_source_history composes the same source-derived linkage with foreign terminal owners, original Child completions and settled registrations at one real native snapshot. Source-closed region deletion now constructs legal surviving Mixed and Fresh executions from actual script recovery witnesses for owner-created Child and actual publication consumers selected together. The guards inspect original parent references, surviving dependency declarations and captured receipt footprints; retained partial inverses and history indices are transported constructively. Fresh retains each real allocation choice and binder continuation without a fixed-name whole-program encoding. A nonempty actual-library proof client includes a Child XOR consumer, an external consumer, blocked owner Unload and a surviving provider publication/Unload; incomplete consumer or birth selection is rejected. Fresh now records actual allocation growth and Insert parent/blueprint payloads in the script witness. Its executable compact method builds a finite bijective name map and source-ordered commands; closed-region guards derive retained-origin coverage and guarantee construction succeeds. Plan::source_execution transports the same installed Fresh program, original inverse receipts and closing table observations to the actual compacted records. A 39-to-25 transition regression replays through the public driver with shifted parents, later Child births, removed retained names and a checked source failure. The real Fresh dispatcher now exposes exact success domains for all seven commands. Its source witness retains complete Active tables, exact installed blueprint declarations, valid bank prefixes and duplicate-free declaration arrays; deletion and renaming preserve them. A maintained quiescent-journal invariant connects the all-row retained-Child scan to live source accumulators. source_command_admission derives concrete command admission from a represented source call and explicit finite allocation/generation and cleanup-idle conditions. Exact synchronous successors and plain Divert history are now derived from actual command results and preserved by closed-region deletion and renaming. Real Kernel generation/restoring fields establish a finite command-prefix bound and absence of leaked cleanup locks. The existing run_script now proves whole finite-script completeness for the admitted synchronous Fresh profile: it cannot return a checked error for a legal represented target and returns exactly its records and final state. Plan::replay_result connects this actual result to the constructed compacted trace and settled source service observation. A 26-to-21 regression covers retained Loading/Divert, original-provider restoration and repeated consumer activation with a new provider. The production source-coverage batch now executes raw scalar/typed forwards and restores through RecordedExecution with automatic authenticated capture, including failed restores and unchanged rejection results. Actual Step receipts explicitly match retained inverse origins. source_order is seeded at real root return and preserved through managed calls, dispatch, same-Journal cross-owner observation and lifecycle/work/Child changes. A full changed-frame Journal census derives all per-read gaps and the endpoint tail, and recover_observer_censused_prefix uses values decoded at the actual endpoint. Actual storage ownership now provides complete per-allocation producer certificates, including raw external scalar/typed operations. A linear Journal last-write frontier prevents skipped same-key commits. Scalar creation mints erased inverse leases in ordinary, computed, cursor and batch paths; successful restore consumes the lease and records its real origin. Typed semantic history now follows the actual creating predecessor and proves each head is successfully restored at most once. Owner-independent terminal evidence preserves typed replacement/retirement sources. The real RecordedExecution scalar_source_snapshot and payload_source_snapshot methods return Producer::certified, deriving whole captured-allocation coverage, earlier creation and unique consumption. The real capture_invocation_census method now captures a common endpoint, collects declared producers with persistent typed agreement and constructs a globally ordered, duplicate-free mutation projection. Initial unconsumed creating obligations and unique interval consumption are derived from actual producer histories. recorded_census now derives coverage and origin admission, and either recovers Begin from the actual endpoint or returns a concrete destructive-change/earlier-inverse proof obstruction. Declared object scope and retained report ownership remain explicit. The final recovery package now maps successful actual managed restores into the independent complete producer projection using exact creating identities and typed resource agreement. The actual capture_release_census entry reads one native snapshot, derives local success from real Unload, checks every foreign creating operation and every original native Child obligation, and returns a concrete boundary/foreign/Child obstruction or same-cut Begin value equality, Child terminal state and settled registration obligations. The interval includes post-Unload writes, without a quiet suffix assumption. A nonempty client composes two actual registered invocations and an assigned Child from their true source endpoints, deriving foreign closure and Child completeness; a clear invocation boundary suffices. A reachable runtime regression includes failure, foreign recovery, retry, parent release before Child Unload, later Remove and raw post-Unload writes. Two strict selected controls reject skipped foreign/Child completion. Whole-workflow evidence remains source-bound in development-report.json; full negative regression and paper-wide completion are separate. The second remaining R3 package derives complete native publication, Episode owner and pending-registration normal forms at every raw Journal cut. Actual openings have unique sources; first Unload consumption preserves exact typed publication identity until release. Pending entries derive their creating forward, actual registration and unique consumption. NativeRuntime::recovery_snapshot captures after an authentic earlier read and runs the complete source-balance query. capture_release_census includes this observation from the authentic pre-Begin cut at the same native snapshot as value/Child recovery. Source imbalance identifies a consumed initial entry or outstanding creation; balance derives exact table equality. A nonempty actual-source client derives closure from matching Unload/registration commits, and a runtime scenario covers failure/retry and same-Arc republication without retaining payloads. Development and selected negative-control evidence remain source-bound and distinct from paper-wide acceptance. Package 3 migrates Runtime and the static host to RecordedExecution with immutable-only core access. Actual callback/value/program/work/effect/Child mutations preserve queue histories; controlled retry and Unload retain source and terminal evidence. Successful controlled release derives a matching successful managed dispatch for every terminal inverse. Driver adapters expose the same recorded root and observed release. Package 4 now constructs a legal native lifecycle/publication/owner history for a source-closed interior episode window from an actual production Snapshot. Source boundary, parent, consumer and creating-parent birth guards imply target step legality, exact closing state and unchanged prefix/suffix episodes. Source allocation freshness and ordered native Journal origins survive. Authentic Begin locates the opening; the existing managed RecoveryCapture can attach this deletion result at its same actual cut without an additional read. A nonempty source-verified 27-to-11-step typed client covers repeated episodes, Child, consumers, failed-cleanup stutter and an independent provider. This is native observation-history deletion, not complete-Journal or executable callback replay. Package 5 transports the complete Journal relation from a certified native window and source effect mask, deriving retained-step legality from exact predecessor/guard reads, preserving local slot references and remapping registration and scalar inverse origins with pending conservation and unique scalar consumption. It composes with the existing recovery capture at the same cut; this is not physical allocator or callback replay. Native source windows now yield executable control replay through the production Kernel: finite allocation compaction transports registry IDs, parents and committed provider references; actual Begin calls regenerate Kernel generations, and every actual intermediate control state equals the renamed surviving source state. Concrete inputs can be captured from RegisteredPlugin, including its private reservation anchor. Opt-in bounded production recording now derives the control-command/snapshot association and allocation bound. Every actual Unload has an authentic cleanup source. Commands, exact typed publications and unique inverse origins share the full source Journal, and the existing managed recovery cut carries the same bound source into control replay. This still does not replay the full production Journal or ActionLedger. Opt-in replayable managed invocations now retain the real registered body and typed inputs, bind them to the full command/Journal source, and instantiate a real target Begin/interpreter/cleanup owner with separate ticket domains. Positive root-admission contracts rule out substituting an invented rejection. Local source/target effect transport derives corresponding outputs and inverses under explicit input correspondence. Explicit managed source capture now also retains every successful-prefix operand directly from its actual queued inverse, with program-counter, queue-token, allocation/write provenance and exact scalar state or typed value/head/depth. Individual fresh target resources can be constructed from those operands; outstanding scalar depth is rejected instead of invented, and the preserved instruction is proved defined at each supported seed with corresponding result and branch. This is not alias-graph construction or complete target scheduling. The actual Source::seed_input entry calls the primitive-domain proof and exports its initializes contract without caller-provided source/target input correspondence. An opt-in finite batch now assigns canonical executable allocation names, reuses one target object/slot per source allocation, publishes actual providers and runs retained root functions through the original executor. Returned calls are an authentic prefix in one target Journal; providers, failed prefixes and cleanup owners remain available. Common source naming namespace is explicit. The batch derives authentic source Call order; positive target-state simulation remains open. Source::prepare_scalar now checks the actual target service value/depth against a retained successful source operand and preserves authentic mismatch read evidence. PreparedStep::land executes the original native landing path, proves source-equivalent results and actual inverse retention, and excludes domain/capacity rejection. A quiet interval in the actual target Journal derives successful landing without assuming a successful target step; admission loss and interference remain explicit outcomes. Actual recipe ledger revisions and allocation identities now produce a checked chronological permutation used by the real finite batch. Different source streams are rejected at runtime. Retained typed inverse histories derive full input continuity; captured native typed landing checks revision under the write lock and registers the real inverse through the shared production path. A shared Verus/runtime fixture demonstrates that the extensible ScalarEffect return law admits hidden shared writes and cannot alone imply target success. The selected controlled-effect architecture now adds closed data instructions to the original root/Child interpreter and ordinary host default. Shared atomic commit proves success exactly on the real primitive domain, registers the actual inverse, and excludes callback interference. Controlled source/batch gates inspect every retained instruction before any target registration and derive absence of scalar interference from actual target reports.

**Open gap:** Full production executable replay is not established by the legal Journal relation or the new actual Kernel control replay. Remaining obligations are: transport Journal references and typed inverse/work producer identities, action-ledger tickets and publication payloads into one executable recovery interpretation; automatically derive the complete effect selection from production Episode ownership (control-command association is now derived at actual transitions); cover admitted shared writes, slot interiors and revision-changing payload paths beyond exact predecessor checks; connect Mixed/Fresh episode-specific selection, Mixed fixed-name code transport and admitted asynchronous landings; prove recovery for the separate Node protocol; and compose general recovery, including Equation (55), with the actual surviving execution. External effects outside the captured scalar/typed scope still need independent source/closure evidence. A host acknowledgement is not Child completion or external I/O truth. Original unrestricted/refuted paper outcomes remain unchanged. The complete selected Journal is not yet scheduled through these target invocations; cross-invocation input, reference, publication, ticket and inverse maps remain to be constructed. Runtime source operands are now retained, but they are not a replay heap: allocation identity, first-input selection and fixed-binding typed publications now compose in a finite executable batch. Automatic common-namespace derivation, general target allocation injectivity, dynamic bindings and target-current-state correspondence still need proof composition. See docs/r3-remaining-work.md for the fixed remaining acceptance packages. The scalar landing contract is a primitive result: the production scheduler must still derive its target input and interference conditions automatically. ScalarEffect's return-value law is not a shared-state effect-frame or hidden-reference remapping contract. The controlled scalar path resolves the demonstrated hidden-callback case for accepted programs. General shared-resource capability/ownership composition and target-state simulation remain required; arbitrary callbacks retain explicit effect/environment contracts. Typed continuity and captured landing still need composition into the full surviving scheduler.

**Next action:** Compose the controlled original executor with producer-derived order, scalar/typed source histories and actual target-state simulation; do not replace those obligations with a target-success assumption. Derive the common namespace for general production sources and integrate publications, Child, departure, cleanup/retry and Unload with actual action/work/inverse maps. The selected architecture routes paper-relevant state through controlled operations; arbitrary callback return laws do not confer recovery guarantees. Preserve R3-A through R3-D exit criteria.

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
- contract: [recovery_history_witness](../crates/cordis-kernel/src/episode_replay.rs)
- proof: [restored_observation_from_source](../crates/cordis-kernel/src/episode_replay.rs)
- proof: [establish_recovery_history](../crates/cordis-kernel/src/fresh_episode_replay.rs)
- proof: [fresh_open_interval](../crates/cordis-kernel/src/terminal_episode.rs)
- execution: [run_inspected](../crates/cordis-kernel/src/inspected_run.rs)
- execution: [run_function](../crates/cordis-kernel/src/managed_function.rs)
- proof: [establish_recovery](../crates/cordis-kernel/src/managed_recovery.rs)
- proof: [recover_retained](../crates/cordis-kernel/src/managed_recovery_word.rs)
- proof: [establish_recovery](../crates/cordis-kernel/src/payload_recovery.rs)
- proof: [prefix](../crates/cordis-kernel/src/shared_value_history.rs)
- proof: [current_begin](../crates/cordis-kernel/src/native_episode_origin.rs)
- contract: [after](../crates/cordis-kernel/src/managed_episode.rs)
- contract: [episode_interval](../crates/cordis-kernel/src/managed_root.rs)
- proof: [recover_observed](../crates/cordis-kernel/src/managed_endpoint.rs)
- contract: [endpoint_recovery](../crates/cordis-kernel/src/managed_root_recovery.rs)
- proof: [recover_begin](../crates/cordis-kernel/src/managed_root_recovery.rs)
- contract: [valid](../crates/cordis-kernel/src/payload_semantic_history.rs)
- proof: [append](../crates/cordis-kernel/src/payload_semantic_history.rs)
- proof: [between](../crates/cordis-kernel/src/managed_restored.rs)
- proof: [resumed_origin](../crates/cordis-kernel/src/payload_recovery.rs)
- contract: [admissible](../crates/cordis-kernel/src/script_deletion.rs)
- proof: [delete_private_episode](../crates/cordis-kernel/src/script_deletion.rs)
- proof: [strict_interface](../crates/cordis-kernel/src/xor_recovery_algebra.rs)
- proof: [establish_recovery](../crates/cordis-kernel/src/cleanup_recovery.rs)
- contract: [finished](../crates/cordis-kernel/src/cleanup_recovery.rs)
- proof: [resumed_inverse](../crates/cordis-kernel/src/cleanup_recovery.rs)
- proof: [cleanup_attempts_succeed](../crates/cordis-kernel/src/managed_cleanup_path.rs)
- proof: [cleanup_recovers_begin](../crates/cordis-kernel/src/managed_cleanup_path.rs)
- execution: [dispatch_payload_cleanup](../crates/cordis-kernel/src/payload_cleanup.rs)
- execution: [retry](../crates/cordis-kernel/src/execution.rs)
- proof: [enabled_is_last](../crates/cordis-kernel/src/recovery_obligations.rs)
- proof: [consume](../crates/cordis-kernel/src/recovery_obligations.rs)
- proof: [interleaved_progress](../crates/cordis-kernel/src/managed_interleaving.rs)
- proof: [drained](../crates/cordis-kernel/src/managed_interleaving_completion.rs)
- proof: [unload_recovers_begin](../crates/cordis-kernel/src/managed_interleaving_endpoint.rs)
- proof: [current_unload](../crates/cordis-kernel/src/native_episode_origin.rs)
- execution: [release_managed_execution_observed](../crates/cordis-kernel/src/native_runtime.rs)
- execution: [restore_observed](../crates/cordis-kernel/src/reversible_value.rs)
- execution: [restore_observed](../crates/cordis-kernel/src/payload_inverse.rs)
- proof: [membership_receipt](../crates/cordis-kernel/src/cleanup_groups.rs)
- proof: [drained_before_exit](../crates/cordis-kernel/src/group_release_history.rs)
- proof: [completed_before_drain](../crates/cordis-kernel/src/cleanup_release_history.rs)
- proof: [registered_token_completed](../crates/cordis-kernel/src/native_episode_origin.rs)
- proof: [acknowledgement_records](../crates/cordis-kernel/src/cleanup_recovery.rs)
- proof: [unload_recovers_from_cleanup](../crates/cordis-kernel/src/managed_release_path.rs)
- proof: [before_seal](../crates/cordis-kernel/src/managed_release_membership.rs)
- proof: [unload_recovers_registered](../crates/cordis-kernel/src/managed_release_membership.rs)
- proof: [registration_facts](../crates/cordis-kernel/src/payload_cleanup.rs)
- execution: [dispatch_recorded](../crates/cordis-kernel/src/managed_cleanup_history.rs)
- execution: [retry_recorded](../crates/cordis-kernel/src/managed_cleanup_history.rs)
- contract: [accounted](../crates/cordis-kernel/src/managed_cleanup_history.rs)
- proof: [emitted_from_history](../crates/cordis-kernel/src/managed_history_release.rs)
- proof: [unload_recovers_from_history](../crates/cordis-kernel/src/managed_history_release.rs)
- proof: [unique_consumption](../crates/cordis-kernel/src/cleanup_release_history.rs)
- proof: [compare](../crates/cordis-kernel/src/joint_execution.rs)
- contract: [queued_sources](../crates/cordis-kernel/src/managed_function.rs)
- execution: [remove_observed](../crates/cordis-kernel/src/execution.rs)
- execution: [remove_observed](../crates/cordis-kernel/src/cleanup_groups.rs)
- contract: [released](../crates/cordis-kernel/src/native_runtime.rs)
- proof: [unload_recovers_from_release](../crates/cordis-kernel/src/managed_history_release.rs)
- execution: [dispatch](../crates/cordis-kernel/src/managed_lifecycle_history.rs)
- execution: [run_recorded_root](../crates/cordis-kernel/src/managed_lifecycle_native.rs)
- execution: [retry_native](../crates/cordis-kernel/src/managed_lifecycle_native.rs)
- proof: [unload_recovers_from_owner](../crates/cordis-kernel/src/managed_owned_release.rs)
- proof: [extend](../crates/cordis-kernel/src/managed_cleanup_history.rs)
- contract: [host_turn](../crates/cordis-kernel/src/managed_cleanup_history.rs)
- execution: [enqueue_effect](../crates/cordis-kernel/src/managed_lifecycle_history.rs)
- execution: [register](../crates/cordis-kernel/src/managed_lifecycle_history.rs)
- execution: [complete_future](../crates/cordis-kernel/src/managed_lifecycle_callbacks.rs)
- execution: [complete_request](../crates/cordis-kernel/src/managed_lifecycle_work.rs)
- execution: [admit_scoped_effect](../crates/cordis-kernel/src/managed_lifecycle_work.rs)
- execution: [land_effect](../crates/cordis-kernel/src/managed_lifecycle_work.rs)
- execution: [retire_effect](../crates/cordis-kernel/src/managed_lifecycle_work.rs)
- execution: [enqueue_native_child](../crates/cordis-kernel/src/managed_lifecycle_children.rs)
- execution: [run_function](../crates/cordis-kernel/src/managed_lifecycle_function.rs)
- execution: [observe_execution_following](../crates/cordis-kernel/src/execution.rs)
- contract: [recovery_boundary_valid](../crates/cordis-kernel/src/managed_lifecycle_history.rs)
- execution: [close_call](../crates/cordis-kernel/src/managed_lifecycle_function.rs)
- contract: [covered_by](../crates/cordis-kernel/src/managed_lifecycle_function.rs)
- proof: [after_call_receipts](../crates/cordis-kernel/src/managed_lifecycle_function.rs)
- proof: [after_call](../crates/cordis-kernel/src/managed_lifecycle_function.rs)
- proof: [extend_boundary](../crates/cordis-kernel/src/managed_lifecycle_function.rs)
- execution: [pop_following](../crates/cordis-kernel/src/cleanup_queue.rs)
- execution: [dispatch_payload_cleanup_following](../crates/cordis-kernel/src/payload_cleanup.rs)
- contract: [follows_boundary](../crates/cordis-kernel/src/cleanup_recovery.rs)
- proof: [before_cleanup](../crates/cordis-kernel/src/managed_lifecycle_function.rs)
- execution: [retire_shared_child](../crates/cordis-kernel/src/native_runtime.rs)
- proof: [retain_decision](../crates/cordis-kernel/src/shared_child.rs)
- proof: [agrees](../crates/cordis-kernel/src/shared_child.rs)
- execution: [retire_shared_child_observed](../crates/cordis-kernel/src/native_runtime.rs)
- execution: [release_managed_execution_following](../crates/cordis-kernel/src/native_runtime.rs)
- contract: [belongs_to](../crates/cordis-kernel/src/native_child_recovery.rs)
- contract: [matches_unload](../crates/cordis-kernel/src/native_child_recovery.rs)
- execution: [release_retired_child](../crates/cordis-kernel/src/native_child_recovery.rs)
- execution: [retire_and_release_child](../crates/cordis-kernel/src/native_child_recovery.rs)
- proof: [from_release](../crates/cordis-kernel/src/native_child_recovery.rs)
- contract: [lifecycle_source](../crates/cordis-kernel/src/native_episode_origin.rs)
- contract: [owned_child_retirement](../crates/cordis-kernel/src/managed_lifecycle_children.rs)
- proof: [native_child_released](../crates/cordis-kernel/src/managed_lifecycle_children.rs)
- proof: [native_child_unassigned](../crates/cordis-kernel/src/managed_lifecycle_children.rs)
- proof: [child_birth](../crates/cordis-kernel/src/native_child_history.rs)
- proof: [child_history](../crates/cordis-kernel/src/native_child_history.rs)
- proof: [retirement_agrees](../crates/cordis-kernel/src/native_child_history.rs)
- contract: [covered](../crates/cordis-kernel/src/native_child_history.rs)
- proof: [extend_cut](../crates/cordis-kernel/src/native_child_history.rs)
- contract: [records](../crates/cordis-kernel/src/native_child_completion.rs)
- contract: [resolved](../crates/cordis-kernel/src/native_child_completion.rs)
- proof: [settle_retirement](../crates/cordis-kernel/src/native_child_completion.rs)
- proof: [settle_release](../crates/cordis-kernel/src/native_child_completion.rs)
- proof: [resolution_facts](../crates/cordis-kernel/src/native_child_completion.rs)
- contract: [native_children_resolved](../crates/cordis-kernel/src/managed_child_completion.rs)
- proof: [native_child_endpoint](../crates/cordis-kernel/src/managed_child_completion.rs)
- proof: [retain_native_child_endpoints](../crates/cordis-kernel/src/managed_child_completion.rs)
- contract: [allocated_below](../crates/cordis-kernel/src/native_lifetime.rs)
- contract: [fresh_insertions](../crates/cordis-kernel/src/native_lifetime.rs)
- proof: [append_allocation](../crates/cordis-kernel/src/native_lifetime.rs)
- proof: [terminal_retained](../crates/cordis-kernel/src/native_lifetime.rs)
- proof: [source_index](../crates/cordis-kernel/src/native_lifetime.rs)
- contract: [cut_source](../crates/cordis-kernel/src/native_child_cut.rs)
- proof: [resolution_at_cut](../crates/cordis-kernel/src/native_child_cut.rs)
- proof: [native_children_at_cut](../crates/cordis-kernel/src/managed_child_cut.rs)
- proof: [observe_later](../crates/cordis-kernel/src/managed_recovery_cut.rs)
- proof: [unload_recovers_with_children](../crates/cordis-kernel/src/managed_recovery_cut.rs)
- proof: [registered_pending_at_cut](../crates/cordis-kernel/src/managed_pending_cut.rs)
- execution: [run_function_observed](../crates/cordis-kernel/src/managed_lifecycle_observer.rs)
- execution: [dispatch_observed](../crates/cordis-kernel/src/managed_lifecycle_observer.rs)
- proof: [join_boundary](../crates/cordis-kernel/src/managed_lifecycle_observer.rs)
- contract: [owns_forward](../crates/cordis-kernel/src/managed_foreign_closure.rs)
- contract: [observations_extend](../crates/cordis-kernel/src/managed_foreign_closure.rs)
- proof: [extend_dispatch_coverage](../crates/cordis-kernel/src/managed_foreign_closure.rs)
- proof: [drained_forward](../crates/cordis-kernel/src/managed_foreign_closure.rs)
- proof: [closed_from_owners](../crates/cordis-kernel/src/managed_foreign_closure.rs)
- proof: [unload_recovers_from_observed_owners](../crates/cordis-kernel/src/managed_recovery_cut.rs)
- proof: [agreement](../crates/cordis-kernel/src/shared_value_sources.rs)
- proof: [retain_report](../crates/cordis-kernel/src/managed_value_sources.rs)
- proof: [retain_dispatch](../crates/cordis-kernel/src/managed_value_sources.rs)
- proof: [linked_from_sources](../crates/cordis-kernel/src/managed_source_link.rs)
- proof: [available](../crates/cordis-kernel/src/managed_source_obligations.rs)
- contract: [sources_for_history](../crates/cordis-kernel/src/managed_lifecycle_sources.rs)
- proof: [recover_recorded_prefix](../crates/cordis-kernel/src/managed_lifecycle_sources.rs)
- proof: [observe_payload_restore](../crates/cordis-kernel/src/managed_lifecycle_sources.rs)
- proof: [unload_recovers_from_source_history](../crates/cordis-kernel/src/managed_recovery_cut.rs)
- contract: [closed](../crates/cordis-kernel/src/closed_region_deletion.rs)
- proof: [restore](../crates/cordis-kernel/src/closed_region_deletion.rs)
- proof: [step](../crates/cordis-kernel/src/closed_region_execution.rs)
- proof: [from_source](../crates/cordis-kernel/src/closed_region_trace.rs)
- proof: [closing_observation](../crates/cordis-kernel/src/closed_region_trace.rs)
- proof: [from_source](../crates/cordis-kernel/src/closed_region_fresh_trace.rs)
- proof: [delete_closed_region](../crates/cordis-kernel/src/script_deletion.rs)
- proof: [delete_closed_region](../crates/cordis-kernel/src/fresh_region_deletion.rs)
- proof: [nonempty](../crates/cordis-kernel/src/closed_region_example.rs)
- proof: [source_guards](../crates/cordis-kernel/src/closed_region_example.rs)
- contract: [history](../crates/cordis-kernel/src/fresh_allocation_history.rs)
- contract: [payloads](../crates/cordis-kernel/src/fresh_allocation_history.rs)
- execution: [pair](../crates/cordis-kernel/src/allocation_names.rs)
- execution: [compact](../crates/cordis-kernel/src/fresh_compaction.rs)
- proof: [enabled](../crates/cordis-kernel/src/allocation_origins.rs)
- proof: [from_region](../crates/cordis-kernel/src/fresh_compaction_origins.rs)
- proof: [admission_complete](../crates/cordis-kernel/src/fresh_compaction_origins.rs)
- proof: [source_execution](../crates/cordis-kernel/src/fresh_compaction_source.rs)
- contract: [command_enabled](../crates/cordis-kernel/src/fresh_dispatch.rs)
- proof: [source_command_admission](../crates/cordis-kernel/src/fresh_dispatch_source.rs)
- proof: [source_step_admission](../crates/cordis-kernel/src/fresh_dispatch_step.rs)
- proof: [source_runtime_shape](../crates/cordis-kernel/src/fresh_execution_shape.rs)
- proof: [deleted_trace](../crates/cordis-kernel/src/fresh_execution_shape.rs)
- proof: [renamed_trace](../crates/cordis-kernel/src/fresh_execution_shape.rs)
- proof: [exact_successor](../crates/cordis-kernel/src/fresh_dispatch_exact.rs)
- proof: [deletion](../crates/cordis-kernel/src/fresh_synchronous_transport.rs)
- proof: [metadata_progress](../crates/cordis-kernel/src/fresh_runtime_metadata.rs)
- proof: [source_call_at](../crates/cordis-kernel/src/fresh_script_completeness.rs)
- contract: [replays](../crates/cordis-kernel/src/fresh_script_completeness.rs)
- proof: [replay_result](../crates/cordis-kernel/src/fresh_compaction_source.rs)
- contract: [recorded_values](../crates/cordis-kernel/src/managed_recovery.rs)
- execution: [apply_scalar_observed](../crates/cordis-kernel/src/managed_lifecycle_values.rs)
- execution: [apply_payload_observed](../crates/cordis-kernel/src/managed_lifecycle_values.rs)
- execution: [restore_scalar_observed](../crates/cordis-kernel/src/managed_lifecycle_values.rs)
- execution: [restore_payload_observed](../crates/cordis-kernel/src/managed_lifecycle_values.rs)
- contract: [source_order_extends](../crates/cordis-kernel/src/managed_lifecycle_order.rs)
- proof: [append](../crates/cordis-kernel/src/managed_source_order.rs)
- contract: [complete](../crates/cordis-kernel/src/managed_source_coverage.rs)
- proof: [gaps_from_census](../crates/cordis-kernel/src/managed_source_coverage.rs)
- proof: [tails_from_census](../crates/cordis-kernel/src/managed_source_coverage.rs)
- proof: [missing](../crates/cordis-kernel/src/managed_source_coverage.rs)
- proof: [recover_observer_censused_prefix](../crates/cordis-kernel/src/managed_lifecycle_sources.rs)
- proof: [unload_from_observer_census](../crates/cordis-kernel/src/managed_lifecycle_sources.rs)
- proof: [allocation](../crates/cordis-kernel/src/joint_owner_history.rs)
- execution: [update_observing](../crates/cordis-kernel/src/joint_execution.rs)
- proof: [restore_source](../crates/cordis-kernel/src/scalar_ownership.rs)
- contract: [valid](../crates/cordis-kernel/src/scalar_ownership.rs)
- proof: [unique_restore](../crates/cordis-kernel/src/payload_semantic_history.rs)
- execution: [source_snapshot](../crates/cordis-kernel/src/payload_source_history.rs)
- contract: [wf](../crates/cordis-kernel/src/payload_source_history.rs)
- proof: [consumption_source](../crates/cordis-kernel/src/managed_producer_sources.rs)
- proof: [certify](../crates/cordis-kernel/src/managed_producer_sources.rs)
- host: [scalar_source_snapshot](../crates/cordis-kernel/src/managed_lifecycle_values.rs)
- host: [payload_source_snapshot](../crates/cordis-kernel/src/managed_lifecycle_values.rs)
- contract: [initial](../crates/cordis-kernel/src/managed_producer_interval.rs)
- proof: [origin](../crates/cordis-kernel/src/managed_producer_interval.rs)
- proof: [check](../crates/cordis-kernel/src/managed_producer_interval.rs)
- proof: [facts](../crates/cordis-kernel/src/managed_producer_event.rs)
- execution: [capture_invocation_census](../crates/cordis-kernel/src/managed_producer_capture.rs)
- execution: [capture_recovery_interval](../crates/cordis-kernel/src/managed_producer_capture.rs)
- proof: [recorded_census](../crates/cordis-kernel/src/managed_producer_recovery.rs)
- proof: [take](../crates/cordis-kernel/src/shared_value_history.rs)
- proof: [includes_restore](../crates/cordis-kernel/src/managed_producer_matching.rs)
- proof: [restoration_before_unload](../crates/cordis-kernel/src/managed_release_path.rs)
- proof: [unload_census](../crates/cordis-kernel/src/managed_unload_census.rs)
- execution: [capture_release_census](../crates/cordis-kernel/src/managed_unload_capture.rs)
- proof: [nonempty_unload_client](../crates/cordis-kernel/src/managed_unload_client.rs)
- execution: [recovery_snapshot](../crates/cordis-kernel/src/native_runtime.rs)
- proof: [normalize](../crates/cordis-kernel/src/native_registry_recovery.rs)
- proof: [normalize](../crates/cordis-kernel/src/joint_pending_recovery.rs)
- proof: [check_all](../crates/cordis-kernel/src/native_observation_recovery.rs)
- proof: [completed_lifetimes](../crates/cordis-kernel/src/native_observation_client.rs)
- proof: [registration_microsteps](../crates/cordis-kernel/src/native_observation_client.rs)
- proof: [terminal_history](../crates/cordis-kernel/src/managed_host.rs)
- execution: [release_controlled](../crates/cordis-kernel/src/managed_lifecycle_native.rs)
- execution: [release_controlled_execution_observed](../crates/cordis-kernel/src/poll_control.rs)
- host: [run_recorded_root](../crates/cordis-driver/src/shared/native.rs)
- host: [start](../crates/cordis/src/runtime.rs)
- proof: [transport](../crates/cordis-kernel/src/native_episode_deletion.rs)
- contract: [admissible](../crates/cordis-kernel/src/native_deletion_trace.rs)
- proof: [delete](../crates/cordis-kernel/src/native_deletion_trace.rs)
- proof: [unchanged_outside](../crates/cordis-kernel/src/native_deletion_trace.rs)
- proof: [delete_since_begin](../crates/cordis-kernel/src/native_deletion_trace.rs)
- proof: [deletion_source](../crates/cordis-kernel/src/native_deletion_trace.rs)
- proof: [nonempty](../crates/cordis-kernel/src/native_deletion_client.rs)
- execution: [deletion_snapshot](../crates/cordis-kernel/src/native_runtime.rs)
- execution: [with_deletion](../crates/cordis-kernel/src/managed_deletion_capture.rs)
- contract: [births_closed](../crates/cordis-kernel/src/native_deletion_trace.rs)
- proof: [deletion_order](../crates/cordis-kernel/src/native_deletion_trace.rs)
- proof: [delete_effect_window](../crates/cordis-kernel/src/native_joint_deletion.rs)
- execution: [with_effect_deletion](../crates/cordis-kernel/src/native_joint_deletion.rs)
- proof: [endpoint](../crates/cordis-kernel/src/native_joint_deletion.rs)
- proof: [restoration_sources](../crates/cordis-kernel/src/joint_erasure.rs)
- proof: [pending_edge](../crates/cordis-kernel/src/joint_erasure.rs)
- proof: [transport](../crates/cordis-kernel/src/joint_erasure_reads.rs)
- proof: [nonempty](../crates/cordis-kernel/src/joint_erasure_client.rs)
- execution: [with_effects](../crates/cordis-kernel/src/managed_deletion_capture.rs)
- execution: [replay_control_window](../crates/cordis-kernel/src/native_deletion_replay.rs)
- proof: [executable_path](../crates/cordis-kernel/src/native_deletion_replay.rs)
- execution: [replay_one](../crates/cordis-kernel/src/kernel_replay.rs)
- contract: [represented_generations](../crates/cordis-kernel/src/kernel_replay.rs)
- execution: [compact](../crates/cordis-kernel/src/kernel_replay_names.rs)
- execution: [instantiate](../crates/cordis-kernel/src/managed_replay.rs)
- proof: [pair_step](../crates/cordis-kernel/src/managed_replay_transport.rs)
- contract: [managed_invocation_ready](../crates/cordis-kernel/src/managed_root.rs)
- execution: [capture](../crates/cordis-kernel/src/managed_replay_inputs.rs)
- contract: [captured](../crates/cordis-kernel/src/managed_replay_inputs.rs)
- execution: [seed](../crates/cordis-kernel/src/managed_replay_inputs.rs)
- proof: [seeded_operation](../crates/cordis-kernel/src/managed_replay_inputs.rs)
- execution: [seed_input](../crates/cordis-kernel/src/managed_replay.rs)
- contract: [initializes](../crates/cordis-kernel/src/managed_replay_inputs.rs)
- execution: [name](../crates/cordis-kernel/src/identity_issuer.rs)
- execution: [same](../crates/cordis-kernel/src/joint_identity.rs)
- execution: [bind](../crates/cordis-kernel/src/managed_replay_bank.rs)
- execution: [run](../crates/cordis-kernel/src/managed_replay_batch.rs)
- contract: [actual_prefix](../crates/cordis-kernel/src/managed_replay_batch.rs)
- contract: [supported_namespace](../crates/cordis-kernel/src/managed_replay_batch.rs)
- execution: [prepare_scalar](../crates/cordis-kernel/src/managed_replay_scalar.rs)
- execution: [land](../crates/cordis-kernel/src/managed_replay_scalar.rs)
- contract: [quiet_input](../crates/cordis-kernel/src/managed_replay_scalar.rs)
- proof: [unchanged](../crates/cordis-kernel/src/managed_replay_scalar.rs)
- proof: [read_witness](../crates/cordis-kernel/src/managed_replay_scalar.rs)
- execution: [prepare_at](../crates/cordis-kernel/src/native_effect.rs)
- execution: [revision](../crates/cordis-kernel/src/recipe_history.rs)
- execution: [plan](../crates/cordis-kernel/src/managed_replay_order.rs)
- contract: [chronological](../crates/cordis-kernel/src/managed_replay_order.rs)
- execution: [continues_payload](../crates/cordis-kernel/src/managed_replay_payload_history.rs)
- execution: [apply_captured_following](../crates/cordis-kernel/src/payload_inverse.rs)
- execution: [land](../crates/cordis-kernel/src/native_payload.rs)
- execution: [apply_payload_captured_following](../crates/cordis-kernel/src/payload_cleanup.rs)
- execution: [evaluate](../crates/cordis-kernel/src/scalar_effect.rs)
- execution: [commit_calculation](../crates/cordis-kernel/src/scalar_effect.rs)
- execution: [apply_controlled_effect](../crates/cordis-kernel/src/controlled_effect.rs)
- execution: [apply_native_controlled](../crates/cordis-kernel/src/native_effect.rs)
- proof: [controlled_execution](../crates/cordis-kernel/src/managed_function.rs)
- execution: [instantiate_controlled](../crates/cordis-kernel/src/managed_replay.rs)
- execution: [run_controlled](../crates/cordis-kernel/src/managed_replay_batch.rs)

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
