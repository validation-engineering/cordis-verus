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
| awaited-results | complete | Native async output/origin pairing and completion from the actual returned Result, retaining both host failure policies. | This does not prove factory-to-Future association, external I/O truth or eventual return. |
| landed-continuation | complete | Actual inverse payload landing and continuation selection from result/cancellation, with the accumulator-step projection. | The opaque inverse function effect is not interpreted by a token/payload accumulator. |
| invocation-effect-origin | partial | Establish actual argument, executed operation, result, continuation and inverse laws for extensible managed plugin entry points. | Native invoke/invoke_future now carry actual argument-to-call and factory-to-Future contracts in production. Complete registered-plugin provenance and primitive inverse laws remain open; generic FnOnce laws do not prove arbitrary plugin bodies. |
| production-composition | partial | One checked production invariant owns all concurrent groups, dynamic Child, admitted work, publications and drain/release decisions. | CleanupGroups now owns all Rust/static cleanup queues, preserves other groups, preflights every retry and seals from their actual state. Root setup, child requests and the joint lifecycle/publication invariant still use ordinary host orchestration. |
| complete-step-classification | partial | Classify the complete production trace against R1 and explicitly specified host extensions. | Control wrappers, visible payload updates and accumulator projections have local contracts; the unified trace correspondence and all extensions remain to be proved. |

## Work packages

### effects

Effects, tracking and recovery — R1, R2, R3

**Current coverage:** Generic effect laws are encoded and proved; executable resource and fixed-program drivers recover concrete journals. R2 now preserves actual generic payloads, native awaited outputs, retry factories and landed continuation decisions in production adapters.

**Open gap:** Production plugin callbacks do not yet instantiate every algebraic premise; opaque cleanup reports do not prove external restoration.

**Next action:** Carry actual operation inputs, outputs and returned inverses through a checked extensible effect boundary.

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

**Current coverage:** Least iterator grammars, dependent outcomes and strict partial independence have substantial proofs. R1 adds all-input exact failure transport and declared-interface reads with arbitrary unrelated service values, plus separate admission and recovery relations.

**Open gap:** The explicit R1-DOMAIN revision resolves executable strict domains; original total-domain independence and its general recovery/scheduling consequences remain separate R3/R4 audit work.

**Next action:** Compose actual receipt/continuation transport through the general R3/R4 execution and reordering obligations.

**Premises to discharge or identify:**

- Shared-key value independence must be derived from concrete primitive laws.
- An equal observation must justify any claimed equality of operation domains.

**Acceptance:**

- Instantiate independence for the actual supported effect family, including nonempty shared-provider executions.
- Preserve real outcomes and returned inverses through every exchange.

**Review path** (source roles, not a proof of calling relationships):

- contract: [operations_independent](../crates/cordis-kernel/src/paper_trace_independence.rs)
- contract: [component_core](../crates/cordis-kernel/src/paper_components.rs)
- proof: [declared_transport](../crates/cordis-kernel/src/guarded_components.rs)
- proof: [no_single_recovery_and_admission_relation](../crates/cordis-kernel/src/typed_child_domain.rs)

### components

Components, Child and lifting — R1, R2

**Current coverage:** R1 completes semantic parent/continuation/child membership on the full finite strict carrier, actual value/code/journal interpretation, and an executable run_inspected client that constructs its evidence from empty. Original total Component membership is not conflated with this revision. R2 adds real publication/value lookup projection and propagates insertion arguments through LifecycleState.

**Open gap:** Production callback effect laws, complete Child/continuation composition and the relation between multi-version host values and R1 remain open. Original unrestricted Gamma and total Component witnesses remain independent.

**Next action:** Connect the production publication/Child/cleanup path to an applicable value and effect contract, preserving the R1 representation and explicit error domains.

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

**Current coverage:** The six-field executable entry and an explicit host leaf projection are implemented.

**Open gap:** Parsing, module execution, tree reconciliation and persistence still have separate host obligations.

**Next action:** Connect the actual configuration transaction to the checked lifecycle protocol and describe non-leaf inputs explicitly.

**Premises to discharge or identify:**

- URL resolution and plugin configuration validation are external adapter operations.
- Whole-tree reconciliation is not implied by correctness of a single record.

**Acceptance:**

- Trace accepted configuration changes to exact registered components and their cleanup/update actions.
- Retain failures and recovery inputs in a real configuration workflow.

**Review path** (source roles, not a proof of calling relationships):

- contract: [bound_effect](../crates/cordis-kernel/src/configuration_entry.rs)
- host: [as_paper_entry](../crates/cordis/src/loader.rs)

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
