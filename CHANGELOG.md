# Changelog

Changes are recorded before release. There is no published release yet.

## Unreleased — 0.1.0

- Coordinate official Harness ConfigEditor file locks, reconciliation and rollback,
  Include refresh and the HMR operation queue with native domain admission. The
  companion application installs the bridge during default boot. Refuse official
  in-process module replacement before cache mutation.
- Isolate event and configuration observers from transaction-step authority;
  preserve scoped waterfall continuations. Reject unresolved native cleanup in
  readiness and rollback restart instead of waiting indefinitely. Keep host pumps
  in an explicit empty invocation scope so nested status observers cannot restore
  an already removed owner identity during shutdown.
- Expose observed ESM/CommonJS module graphs and reviewable Worker reload plans.
  Follow transitive changes, preserve retained-artifact recovery, and reject
  application native addons before retiring the active Worker.
- Add opt-in typed Rust `provide_checked`, `set` and `refresh` on declared services,
  with actual CheckTicket validation and generation-bound service notifications.
  Dynamic publication creation and removal remain outside this adapter.
- Add opt-in transactions for the unchanged official Harness Loader/Include.
  Coordinate create/update/remove with native lifecycle and actual write queues;
  reject stale owner episodes and normalize qualified nested removal. File
  failures remain explicit and do not claim rollback of running plugin effects.
- Capture synchronous adapter lifecycle operations while joining discarded
  Promises. Give update callbacks their own invocation origin so an asynchronous
  callback cannot reuse saved transaction steps after leaving its update frame.
  Keep host scheduling independent of observer episodes while preserving recovery
  admission, and reject retained update continuations after their revision ends.
  The host installer above extends this explicit API to official configuration entrypoints.

- Distinguish an active owned action from its later asynchronous continuations.
  Completed startup callbacks no longer block the official headless runner's
  shutdown; pending effects, inverses and owned tasks retain self-wait guards.
  Stale continuations may emit existing logger diagnostics, while service and
  resource access still requires their original, valid episode authority.

- Expose real per-Fiber lifecycle inertia for the unmodified upstream Loader.
  Startup and cleanup observers join native-admitted transitions, including
  restart and failed-setup cleanup, without waiting on their own parent domain.

- Keep native cleanup failures observable after settlement consumes transient errors.
  Disposal rejects on failed owned descendants or committed consumers, preserves
  the setup-error cause, and requires real explicit recovery before removal.

- Adapt real static `cordis::Plugin` definitions into the existing Node graph,
  using committed publication bindings and original shared typed slots.
  Preserve per-Fiber FnMut state across restart and reject implicit name/type
  conversions, unsupported dynamic operations and changed mount definitions.
- Share setup/cleanup execution helpers with the Rust Runtime. Keep failed
  legacy FnOnce cleanup permanently unconfirmed instead of accepting an empty
  retry; synchronize withdrawal with escaped AsyncSetup capabilities.
- Include the typed Runtime source closure in native build, npm installation
  and benchmark freshness checks.

- Add bidirectional explicit opaque object and callback adapters with fixed method
  interfaces, borrowed/owned leases and retryable asynchronous owned disposal.
  Acquire capabilities through declared factory methods; reject handles and
  callbacks embedded in ordinary JSON arguments or results.
- Retain objects and Rust sessions until ordinary JS inverses succeed, then
  release consumer objects in acquisition LIFO order before session teardown.
  Preserve failed cleanup dependencies, including nested effects and partial setup.
- Keep reverse `JsObject`/`JsCallback`/`JsStream` capabilities action-scoped. Explicit
  close rejects pending methods/pulls as Busy without changing admission; automatic
  journals still join completion and stream cancellation still issues return first.
  Reject observable ancestor-resource close cycles and stale request authority.
- Add source/build-bound performance measurement and explicit baseline comparison
  tools with raw batch samples and separate measurement-failure/regression outcomes.
  No performance numbers or accepted platform budgets are claimed by this entry.

- Add bidirectional Rust/JS pull streams with single-flight backpressure, idle
  resource ownership, real cancellation/return draining and retryable close.
  Bind restoration authority to individual pending requests; retain failed and
  malformed acquisitions through cleanup instead of treating drop as completion.
- Select and verify native artifacts by platform, architecture, libc and Node-API;
  record source-bound manifests and assemble existing host artifacts offline.
  Multi-platform execution and complete release acceptance remain separate.

- Add a user-extensible same-graph Rust factory SDK with explicit JSON service
  methods, event-driven Futures, reverse JS calls, caller-owned cancellation,
  cleanup retry and separately compiled addon acceptance.
- Preserve unchanged Loader fibers during configuration updates and accept
  prepared factory revisions through an explicit ModuleHost adapter; retain
  fresh-Worker restart for actual module-environment replacement.

- Share lifecycle control and the verified action ledger between Rust and Node.
- Add versioned Service.check, dynamic declaration transfer, reserve/seal ownership,
  callable logging, method decorators and separate Cordis/Harness profile policies.
- Add explicit owned-task draining, JSON Include/group loading, serialized update
  recovery and fresh-Worker artifact restart/rollback with abandoned-exit diagnosis.
- Execute all 87 unchanged upstream core tests, preserve known safety differences,
  and add strict profile differential evidence and extracted npm installation checks.

- Add an experimental native Node compatibility path: a value-independent Rust
  Driver, Node-API binding, JS object table and Cordis language facade. Original
  Timer source is exercised without modification in optional differential tests.
- Verify dynamic logical-provider declaration and a PublicationRegistry with
  exact cleanup leases, revocation, retained slots and reclamation guards.
- Retain action ownership across asynchronous cancellation and cleanup failure,
  reject stale/cross-domain completions, and allow explicit failed-inverse retry.
- Add native build fingerprints, Node behavioral evidence and a third extracted
  crate check. This is not complete Cordis/Harness compatibility or paper refinement.


- Pin Verus to the official `0.2026.10.04.1687598` rolling release, with platform
  archive checksums and the matching source revision in the upstream lock.
- Represent closed-driver transitions as operation-specific enums, carrying
  actual step outcomes and explicit Divert/Leave routing without inconsistent
  command/actor fields.
- Cancelled effect joins unregister their Wakers immediately. Keep setup futures
  in explicit lifecycle states and retain started stages until their inverses land.
- Share panic-aware Future polling and loader source-tracking reset/parent lookup,
  retaining all-settled events and recovery bookkeeping before suspension.
- Make lifecycle-frame, Begin-boundary, history-catalog and constructive-deletion
  proofs explicit under Verus's source-typed function encoding. Split source and
  target witnesses into small lemmas while preserving public contracts and
  existing per-function solver resource limits.

- Prepare the first private GitHub development snapshot with a bilingual entry point,
  architecture/module navigation, an explicit progress ledger and acceptance-based roadmap.
- Verify 2,227 whole-kernel obligations on the pinned toolchain; keep paper-wide
  completion and full mutation/release acceptance explicitly open.
- Compose foreign Child landings, mixed Table/Child journals and dynamic registry
  edits in the restricted constructive deletion theorem with real terminal recovery.
- Add conditional typed Component/instantiation interfaces and historically quantified
  independence definitions, preserving the recursive-context and strict-domain gaps.
- Separate daily development CI from the manual full release gate. Provide source-bound
  development evidence and an experimental, opt-in scoped-negative calibration tool.

- Strengthen the Lemma 75 well-foundedness counterexample to six external steps with directly proved total Unit components, independent of Child partiality.
- Derive strict batch recovery across old inverse maps without per-record reverse witnesses; retain the explicit lifecycle-crossing obligation.
- Verify owning single-admission sessions, drift landings and complete script histories with exact action/event provenance.
- Construct interface-separated providing-owner deletion with shared operations and actual foreign Unload; verify a from-empty token-compression example.
- Mechanize strict guarded Child definedness and core-progress boundaries; distinguish encoded-rule counterexamples from the original total-component premises.

- Add a verified FreshDriver with actual allocation, repeated activation and one immutable fresh-binder source program; preserve complete machine state on errors.
- Construct surviving shared-key lifecycle traces with authentic foreign Unload and compressed history tokens.
- Prove same-program natural equivariance for the full fresh-binder lifecycle and complete external input streams.
- Require release records to match the entire ordered negative-control manifest; regression-test missing and malformed evidence.

- Transport all nine-rule finite suffixes after an actual shared-provider Iter exchange, preserving strict observational receipts and swapped history tokens.
- Derive local reverse witnesses from authentic foreign Unload batches and prove strict terminal owner recovery for newly minted operational receipts.
- Formalize fixed fresh-child binders, historical allocation choices, complete name support and strict alpha transport.

- Add an executable owning MixedDriver and verified finite script runner, connecting actual cross-provider values, children, strict LIFO restoration and atomic failures to one mixed-grammar history.

- Derive shared-dependency surviving execution prefixes and strict terminal Unload, preserving nonempty initial history and real target receipts.
- Construct a real shared-provider Iter diamond with raw outcome and partial inverse stability.
- Derive Loading entangled-step identity and committed-provider pinning from empty-origin mixed traces.

- Add optional isolated parallel negative checks, preserving full-crate rejection criteria and recording worker settings; regression-test the evidence gate.

- Prove joinability and unique normal forms for guarded rewrite descendants of the same actual trace, preserving authentic receipt correspondence.

- Construct authentic isolated-owner episode deletion for every prefix, preserving foreign children and Unload through compressed history-token correspondence.
- Extend guarded constructive normalization to every lifecycle rule, including actual strict Unload and captured-child removal guards.
- Derive strict partial journal restoration and foreign replay domains from actual local inverse witnesses, with a verified forward-only counterexample.

- Generalize dependent primitives and the same mixed interpreter to
  observational recovery, preserving actual outcomes, strict partial inverse
  domains, all-prefix safety, original-index ordering and typed journals.
- Derive mixed Begin/Unload observational recovery from local witnesses and
  observational scalar commutation, without assuming a whole episode recovery
  equation or choosing quotient representatives.
- Construct Insert/Retire/Remove exchanges across every mixed grammar node,
  deriving reverse legality from original steps and precise name-read guards;
  preserve authentic receipts through arbitrary legal finite suffixes.
- Construct finite guarded local normalization with a strictly decreasing
  inversion count, preserving full external input payloads and actual trace
  legality while retaining unmovable name dependencies.
- Unify dependent operations and child creation under arbitrary continuation
  indices, deriving nine-rule safety, actual receipt history and child retention.
- Trace provider ordering and operation/inverse provenance through real mixed
  LIFO restores, including child retirement and earlier original-index landings.
- Derive actual dependent/mixed episode and terminal value recovery from empty
  traces, under an explicit exact scalar identity-extension interface. Preserve
  strict failures, real child control effects and the value-only replay boundary.
- Formalize Definition 42 with observational inverse comparison and greatest
  continuation bisimulation, and prove the equivalent generator criterion.
- Connect strict partial grammar independence to greatest continuation
  bisimulation and prove the failure-sink boundary of unguarded totalization.
- Construct a real mixed Child/O-Insert diamond with parent-name read guards
  and actual history correspondence; transport every legal finite suffix with
  the same labels while preserving distinct recorded historical inputs.
- Prove a diagonal obstruction to the nontrivial unrestricted set/function
  interpretation of Definition 28, without excluding restricted models.

- Construct one grammar Model from actual receipt history using stable tokens
  for repeated calls; derive successful-call agreement rather than assume it.
- Connect dependent grammar and arbitrary continuation indices to full-state
  successful traces, finite context projection and strict inverse domains.
- Prove historical episode/provider ordering, Loading coherence, actual
  operation/inverse provenance, and frozen state-map/edit factorization.
- Add an owning verified ChildDriver with real journal retention checks,
  atomic target-drift diversion, guarded child restoration and behavior tests.

- Executable Verus lifecycle kernel: four phases, provider identity, committed
  dependency bindings, restoration guards, and conditional progress proofs.
- Verified LIFO cleanup, reversible resource writes, and conditional recovery
  and effect commutation laws.
- Rust host APIs for synchronous/asynchronous setup, staged effects, dynamic
  child plugins, scoped typed services, failure handling, and explicit shutdown.
- Scoped synchronous/asynchronous events, timers, JSON configuration/schema,
  includes, factory revision reload, and failed-load recovery.
- Upstream provenance locks, negative proof mutations, integration examples,
  strict quality gate, cross-platform CI, and tests of extracted crate archives.

The 0.1 API is experimental. Complete asynchronous runtime refinement and
paper-wide liveness/confluence are not claimed. See `docs/semantics.md` for the
current scope of the proofs and `docs/upstream-parity.md` for functional gaps.

### Lifecycle and operational hardening

- Owner event admission/drain including callback/future destruction and escaped continuation leases.
- Explicit JSON save plans, Include-preserving three-way merge, atomic per-file replacement, conflict and durability retry reporting.
- Verus-proved stable compaction of obsolete bindings and removed declarations, plus automatic host maintenance.
- JSON/DOT lifecycle diagnostics and resumable shutdown with setup/cleanup error aggregation.
- Reproducible validation records, additional concurrency/failure regressions, and bilingual project entry points.

### Paper refinement

- Independent paper control-state model, concrete projection, per-operation
  simulation and frames, strict target-driven departure, error atomicity and
  compaction stuttering.
- Verified stage admission/landing protocol used by actual host effect groups.
- Store-owning witnessed Journal with exact partial/full rollback, independent
  history normalization and same-lane interleaving confluence.
- Executable ranked support with unique fixed point and conditional finite
  lifecycle step-count bound; explicit remaining whole-runtime obligations.
- Value-carrying lifecycle specification with actual iterator yields, child
  effects, inverse accumulators, and a landing-only conditional progress result.
- Owned resource Driver with actual provider guards, exact committed identities,
  resource-preserving reactivation and verified rollback before binding release.
- ChildEpisode witnesses for actual fresh children, LIFO retirement and guarded
  parent unload; explicit handling of externally removed children.
- Registry-level quiet control normal-form uniqueness using provider precedence
  alone, plus target-change predecessor attribution.
- Machine-checked counterexamples and corrections for paper v1 Lemmas 62 and 75;
  no claim that these counterexamples disprove Theorem 80.

### Algebra, dynamic execution and completion audit

- Effect tracking/lifting algebra with actual state-dependent witnesses;
  observational tests and coinductive iterator partial equivalence.
- Key-local coeffects, finite-word transformation monoids, and declaration-to-
  dynamic-schedule independence proofs.
- Full-rule primitive preservation, observational simulation, arbitrary name
  bijections, and matching of different fresh allocations.
- Dynamic schedule uniqueness, constructive serial completion and lawful
  deletion with the actual yielded inverses.
- Actual fixed-registry lifecycle counts, target-change attribution and a
  constructive full-rule execution reaching quiescence.
- Immutable Set/Copy/BranchWrite programs, owned provider-guarded execution,
  checked port layouts and complete-publication admission.
- An evidence-linked inventory of all 81 numbered paper items and a separate
  completion gate; passing ordinary quality checks is not paper completion.
- A four-step encoded full-rule counterexample to the exchange in Lemma 78(2), exposing
  the omitted dependency on a newly created insertion parent.
- Theorem 43 for arbitrary permutations of actual dynamically returned
  inverses, and Theorem 16 for every partial reverse prefix.
- Partial context-mediated operation grammar and exact all-fiber projections,
  including primitive full-state forward/inverse simulation.
- An eight-step total-on-provision, ranked, quiescent witness rules out the
  ordering in Theorem 80(1) within the encoded full-State rules. Original
  Definition 48/56 component instantiation remains open; this is not an
  unconditional refutation of either original Theorem 80 clause. A separate strict guarded fresh-binder counterexample exposes the literal named-input boundary; it does not supply the original globally total component witness.

### Contexts, child history and executable trace bridges

- Typed dependent coeffect maps and codecs, isolation, metadata monoids and
  interception, connected to the actual mediated operation/provision grammar.
- Partial-map reachable grammar independence, raw-outcome stability, generated
  monoid commutation and actual stage exchange; strict provision inverse domains.
- Child birth and creator-episode provenance from real full-rule traces and
  accumulators; lifecycle-born retirement closure and origin-aware quiet support.
- A five-step total, ranked, quiet counterexample to original Lemma 77, with a
  matching executable Kernel regression; external non-root insertion is retained.
- Atomic ProgramDriver landing and complete successful finite API trace
  simulation under a single model constructed from allocation/configuration
  history, including insertion and removal.
- Complete observational transport of Section 3.1, including the distinction
  between an actual-input witness and a uniform inverse for all accumulators.
- Dependent context-mediated grammar with operation-specific argument/outcome
  fibers, arbitrary continuation indices and least witnessed partial iterators.
- Partial full-State interpretation with captured-provider receipts, authentic
  inverse history and preservation for all nine successful lifecycle rules.
  The bridge to an existing total Model retains call-consistency premises.
- Nonreused per-fiber episode generations for checked ChildEpisode handles,
  preventing stale same-binding admission, child creation and parent cleanup.
