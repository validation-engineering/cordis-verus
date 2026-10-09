# Reviewing paper claims against executable Verus code

English · [简体中文](paper-review-guide.zh-CN.md)

This guide follows five claims from *A Programming Paradigm for Spatiotemporal
Composability*, [arXiv:2608.25512v1](https://arxiv.org/abs/2608.25512v1), to contracts,
executable calls and regression tests. It is a starting point for independent
review, not a claim that the entire paper or the asynchronous host is verified.

The authoritative inventory remains [paper-obligations.json](paper-obligations.json)
and its generated [coverage table](paper-coverage.md). These review cases do not
change an item's status. The selected definitions are `formalized`; Lemma 62 is
`refuted`; Theorem 80 is `partial`. A definition's encoding is not a theorem about
all consumers of that encoding.

## How to use this guide

1. Read the fixed paper version and the cited clause. Page numbers below are
   one-based PDF pages, matching the page markers in the local text extraction.
   Consult the PDF for mathematical layout. The PDF hash is in
   [upstream.lock.json](../upstream.lock.json); pinned toolchain versions are in
   [toolchain.lock.json](../toolchain.lock.json).
2. Read the function's **whole `requires` and `ensures`**, its invariants and
   projection. Follow the executable call into that function. A linked theorem
   alone does not establish that an application meets its premises.
3. Run the selected Cargo regression. It exercises executable behavior; it does
   not invoke Verus or prove that every schedule has that behavior.
4. Verify the source using `./scripts/verify.sh`. This runs the pinned verifier
   over the actual kernel source, with `--no-cheating`, and compiles it. Use
   [CONTRIBUTING.md](../CONTRIBUTING.md) for toolchain setup. The ordinary Rust host
   has a separate test boundary.
5. Record the commit (`git rev-parse HEAD`), command, toolchain and raw result when
   reporting a finding. GitHub's **y** shortcut turns a source page into a commit
   permalink. The relative links here intentionally follow the reviewed checkout.

Run commands below from the repository root. `--offline` assumes cached Cargo
inputs; omit it for an initial dependency download. `--exact` ensures a named
regression, rather than a substring match. Confirm the output reports one test.

The small [case index](paper-review-cases.json) records paper locations, ledger
statuses, source symbols and test names. Check it without building the project:

```sh
python3 scripts/check-paper-review.py
```

This is a documentation consistency check. It does not establish semantic
correspondence, run the tests or refresh proof evidence. If the ignored local
paper text is available, it also checks its locked hash and page/heading markers.
The full paper is not redistributed with this repository; see
[reference/README.md](../reference/README.md).

For Theorem 73, see [progress claims and executable contracts](progress-contracts.md):
exact acceptance conditions, their runtime callers, synchronous Mixed/Fresh
steps and the cross-call admitted landing domain. These implementation contracts
also inform Lemma 57. The real Fresh runner derives finite return for one actor
at a terminal result or its first error, and conditionally extends the source
represented by its input. `run_from_empty` establishes that input through the
actual setup script and proves one source execution from empty representing both
the prepared and returned machines, with well-formed, resource-safe states.
`SetupFailed` stops before autonomous execution and does not imply a blocked
actor. Insert/Begin/Step now have exact implementation acceptance domains through
`preparation_enabled`; a failed command in that profile is disabled at the actual
failure state, even after a prefix containing other commands. This does not
require all commands to be enabled initially. Retire/Depart/Unload/Remove remain
supported but outside the preparation profile. The actual Mixed/Fresh Unload
dispatcher branch now has its own exact cleanup-guard-plus-inverse domain. Real
source histories also establish inverse definedness for the complete concrete
Unit/Child/Provision/Xor journal, as reviewed in PR-02. The remaining command and dispatcher domains,
individual error variants, whole-system progress,
arbitrary Future completion and host scheduling remain
separate; these repairs do not require a temporal-logic dependency.

## PR-01: an episode keeps the provider identity it committed to

**Paper:** §4.2.2, Definition 53, p.35, equations (48) and (49); Definition 54,
p.36, equation (50); L-Begin, p.36, and L-Unload, p.37.

**Behavior:** changing the current dependency resolution does not silently
rewrite an installed consumer's committed provider. A provider's cleanup must
wait for consumers that still hold it in their committed view. An Active
consumer may temporarily disagree with its current target.

**Review chain:**

- [semantics.rs](../crates/cordis-kernel/src/semantics.rs): `target` and `quiet`
  encode the full-state definitions using actual published table domains.
- [refinement.rs](../crates/cordis-kernel/src/refinement.rs): `target`, `relied`
  and the `Begin`/`Unload` arms of `step` specify the control projection.
  This projection specializes publication to total declared provisions and
  erases payloads, iterators and accumulators. The same file explicitly separates
  host `Restart` from the paper's nine rules.
- [lib.rs](../crates/cordis-kernel/src/lib.rs): `Kernel::begin` requires `wf()`.
  On success it preserves `wf()`, establishes `committed_from(old(self), id)`
  and `refinement::step(..., Rule::Begin)`. Its executable loop records the
  bindings returned by the current target. `begin_cleanup` establishes
  `restoration_guarded(id)` while preserving bindings; `finish_cleanup`
  establishes `Rule::Unload` and clears that episode's committed view.
- [driver.rs](../crates/cordis-kernel/src/driver.rs): `Driver::unload` calls
  `begin_cleanup`, restores the real resource journal, then calls
  `finish_cleanup`. Its postcondition includes both the control rule and
  restoration of `resource(id)` to `initial(id)`.
- [mixed_driver.rs](../crates/cordis-kernel/src/mixed_driver.rs) and
  [fresh_driver.rs](../crates/cordis-kernel/src/fresh_driver.rs): public `unload`
  succeeds iff `unload_enabled`, combining Kernel cleanup permission with a
  defined `restore_receipts` over the actual journal. `undo_one` implements the
  corresponding strict inverse; the loop preserves restoring and decreases
  journal length. Public errors keep the complete machine, while an internal
  draft may already have restored a prefix. This connects the guard to actual
  finite cleanup; `!relied` alone does not establish arbitrary inverse validity.
  Its contribution to Lemma 57, Corollary 69 and Theorem 73 remains partial:
  defined restoration is separate from general foreign-replay equivalence or
  whole-system progress. PR-02 below derives the inverse condition for the
  complete concrete Unit/Child/Provision/Xor journal, without changing the guard.
- [lifecycle_actions.rs](../crates/cordis-kernel/src/lifecycle_actions.rs):
  `LifecycleActions` joins exact action tickets with cleanup outcomes and the
  actual `Kernel::finish_cleanup` call. A failed completion retains a blocking
  receipt; an explicit retry receives a new ticket. The shared Driver and Node
  path call this executable protocol. See the [cleanup protocol review](cleanup-protocol.md)
  for the contracts, reservation extension and the ordinary Rust host's distinct
  `Drained` policy. Host reports and external inverse effects remain outside the proof.
- [runtime.rs](../crates/cordis/src/runtime.rs): ordinary Rust
  `Runtime::poll_settle` calls the shared lifecycle Driver around
  host callback execution. This is an actual integration path, not a proof of
  arbitrary callback or Future behavior.

**Executable review:**

```sh
cargo test --offline -p cordis-kernel --test refinement strict_departure_preserves_committed_views_until_guarded_unload -- --exact
cargo test --offline -p cordis-kernel --test driver provider_resources_remain_live_until_consumer_recovery -- --exact
cargo test --offline -p cordis --test runtime provider_waits_for_async_consumer_cleanup -- --exact
cargo test --offline -p cordis-driver --test cleanup_outcomes failed_cleanup_retains_provider_until_an_exact_fresh_retry_succeeds -- --exact
```

The first test observes an unavailable current target while the consumer's old
committed bindings remain, and a rejected early provider cleanup. The second
runs actual resource recovery. The third exercises the asynchronous host and is
**test evidence**, not a proof that every host future terminates or preserves
its external resources. The fourth checks the production shared Driver: failed
cleanup retains dependencies until an exact fresh retry succeeds and finish is called.
Typed payload storage and escaped `Arc` values are
outside this control projection.

**Negative-control candidate:** `provider-lifetime-guard` removes the real
provider guard. Its presence in the mutation suite is not a current passed
negative-control result; see the evidence boundary below.

## PR-02: child retirement needs the referenced identity to remain registered

**Paper:** §4.2.1, Definition 52, p.35: a child-creating iteration returns the
created name and captures its retirement as the inverse. The discussion after
the definition appeals to the registered-name premise of O-Retire.

**Classification:** formalized primitive plus an **explicitly revised removal
policy**. Being retired does not imply that an outstanding inverse no longer
needs the identity. Unrestricted O-Remove can remove that identity too early.

**Review chain:**

- [paper_instantiation.rs](../crates/cordis-kernel/src/paper_instantiation.rs):
  `typed_instantiate` and `captured_retirement` state the conditional original
  primitive, given a context interpretation and editor laws. These premises
  must be inspected; the executable driver below does not automatically
  instantiate the paper's entire recursive context and Component model.
- [child_history.rs](../crates/cordis-kernel/src/child_history.rs): `retained`
  says that every child referenced by any actual accumulator remains registered.
  `remove_unreferenced` supplies the extra removal condition.
  `retained_recovery` proves restoration-domain/typing properties under the
  primitive inverse contracts; `retention_protocol_refines` proves execution,
  retained references and well-formedness for the revised protocol. It does not
  derive arbitrary table-value recovery from no premises.
- [child_driver.rs](../crates/cordis-kernel/src/child_driver.rs): `ChildDriver`
  privately owns its Kernel and episodes. `wf` includes registered references
  for every journal. `refines_retention` projects these **real journals**, rather
  than an unrelated ghost history, into `child_history::retained`.
- `land_child` calls the actual child episode and captures its inverse.
  `remove` first scans every journal through `has_reference`; success ensures
  `remove_unreferenced`, while `Retained` means a real reference exists.
  `unload` calls `ChildEpisode::finish_restore`; success ensures
  `ownership::child_unload` and an empty journal.
- [mixed_driver.rs](../crates/cordis-kernel/src/mixed_driver.rs) and
  [fresh_driver.rs](../crates/cordis-kernel/src/fresh_driver.rs):
  [`unit_child_recovery.rs`](../crates/cordis-kernel/src/unit_child_recovery.rs)
  connects a represented well-formed source's retained
  child identities to the actual receipts. `history_sound` alone only gives
  inverse definedness at the original landing; retention is the current-state
  fact. For a registered actor's `unit_child_journal`, Unit identity and Child
  retirement preserve registry membership, giving defined restoration of the
  complete real LIFO journal. Actual `run_script` outputs have this property;
  `run_from_empty` also establishes it at preparation and return. No runtime
  history buffer, alternate restore implementation or stronger `wf` is added.
- `unit_child_unload_domain` then equates `unload_enabled` with
  `cleanup_permitted` under that recovery property and journal classification.
  Public Unload and the actual `apply` branch connect this domain to execution.
  If a script stops on Unload with a Unit/Child journal, cleanup is not permitted
  at that stopping point. A retired child remains registered until legal Remove;
  parent ownership does not create a service dependency or force child cleanup
  before the parent's inverses. The source invariants below extend this result
  to Provision and Xor. This is a restricted bridge
  for Definition 52, Lemma 57 and Theorem 73, not Corollary 69's general
  foreign-replay recovery equation. Lemma 57 and Theorem 73 remain partial.

- [`provision_history.rs`](../crates/cordis-kernel/src/provision_history.rs) and
  [`provision_recovery.rs`](../crates/cordis-kernel/src/provision_recovery.rs)
  extend the actual-journal result to Unit/Child/Provision. Execution from empty
  derives `live_provisions`: each retained Provision has an occupied owner slot,
  with distinct provision keys within each live owner journal. Foreign Xor may
  change payloads while preserving those slots. The receipt bridge derives
  `provision_recovery`, and `provision_unload_domain` connects it to the same
  Kernel cleanup guard. Mixed/Fresh scripts and bootstrap outputs establish
  the property from real histories. The following stronger result also covers
  journals containing Xor.
- [`operation_history.rs`](../crates/cordis-kernel/src/operation_history.rs) and
  [`journal_recovery.rs`](../crates/cordis-kernel/src/journal_recovery.rs)
  establish `journal_recovery` for all four concrete receipt variants.
  `live_operations` derives current captured-provider resolution, provider/value
  retention and the order condition that a later Provision cannot remove an
  earlier operation's slot. Together with Provision uniqueness and child
  retention, `restore_all` proves defined restoration of the actual LIFO journal.
  The provider facts connect to Definitions 53/54 and the commitment guard in
  PR-01: retirement or target drift does not replace the provider captured by Xor.
  Actual script outputs and both bootstrap machines carry the stronger property;
  `journal_unload_domain` removes the receipt-profile restriction from the
  cleanup-guard equivalence. A script Unload failure means cleanup is not
  permitted at that stopping point. This is the concrete synchronous `u64`/Xor
  language, not arbitrary scalar effects, host callbacks, the general
  foreign-replay equation, an empty-owner-table theorem or global termination.

**Executable review:**

```sh
cargo test --offline -p cordis-kernel --test paper_vestige retiring_an_already_removed_child_requires_an_idempotent_extension -- --exact
cargo test --offline -p cordis-kernel --test child_driver retired_inactive_child_is_retained_until_real_inverse_is_consumed -- --exact
cargo test --offline -p cordis-kernel --test child_driver all_actual_journals_retain_their_children_through_nested_recovery -- --exact
cargo test --offline -p cordis-kernel --test unit_child_recovery fresh_history_retains_retired_children_until_parent_recovery -- --exact
cargo test --offline -p cordis-kernel --test unit_child_recovery mixed_history_retires_captured_children_without_running_their_journals -- --exact
cargo test --offline -p cordis-kernel --test unit_child_recovery failed_script_retained_removal_keeps_a_recoverable_actual_prefix -- --exact
cargo test --offline -p cordis-kernel --test unit_child_recovery bootstrap_terminal_publication_failure_keeps_a_recoverable_child_receipt -- --exact
cargo test --offline -p cordis-kernel --test provision_recovery mixed_history_recovers_distinct_provisions_and_only_its_captured_child -- --exact
cargo test --offline -p cordis-kernel --test provision_recovery foreign_xor_preserves_a_real_provision_until_dependency_cleanup_allows_recovery -- --exact
cargo test --offline -p cordis-kernel --test provision_recovery duplicate_provide_failure_keeps_the_actual_provision_and_child_prefix_recoverable -- --exact
cargo test --offline -p cordis-kernel --test provision_recovery bootstrap_missing_publication_still_recovers_committed_provision_and_child -- --exact
cargo test --offline -p cordis-kernel --test xor_recovery mixed_script_recovers_self_xors_before_removing_their_provisions -- --exact
cargo test --offline -p cordis-kernel --test xor_recovery retired_provider_stays_available_to_the_consumers_captured_xor_inverses -- --exact
cargo test --offline -p cordis-kernel --test xor_recovery interleaved_consumers_recover_only_their_xors_and_keep_the_provider_value -- --exact
cargo test --offline -p cordis-kernel --test xor_recovery bootstrap_failure_recovers_its_self_and_foreign_xors_from_the_real_prefix -- --exact
```

The first test exposes the missing-name failure on the public Kernel path.
The owning ChildDriver tests show the additional retention policy preventing
premature removal and consuming the captured retirement. The public Kernel's
original O-Remove was not silently tightened. Other adapters must establish their
own retention behavior; this case does not prove arbitrary JS child callbacks.

The new Unit/Child tests use public scripts to check retired identity retention,
parent recovery without running a child's journal, and recovery of the successful
prefix after a Retained error. An externally inserted child with the same parent,
but no captured receipt, is not retired by that recovery. These are behavior
regressions: Unit identity alone does not make inverse order observable in a
test; review the proof contracts for LIFO and definedness. The Xor cases make
that order observable: self Xor must recover before its Provision removes the
value. They also check consumer recovery after provider retirement, preservation
of a second consumer's interleaved effects, and successful-prefix recovery after
bootstrap publication fails. These tests construct public histories and do not
inject private journal state.

**Negative-control candidate:** `child-removal-ignores-retained-token` weakens
retention for a retired child. Acceptance evidence for this checkout remains a
separate requirement.

## PR-03: a vestigial entry can still affect parent guards

**Paper:** §4.3, Lemma 62, p.42, clauses (1) and (2).

**Classification:** a counterexample to the printed lemma, not a discovered
memory-safety defect in upstream Cordis. Empty service observations alone do not
make an entry invisible to all control rules.

**Review chain:**

- [semantics.rs](../crates/cordis-kernel/src/semantics.rs):
  `vestigial_parent_counterexample` establishes a retired, inactive, empty child
  for which deleting the child enables removal of its parent. This contradicts
  clause (2)'s claimed reverse applicability outside its listed exceptions.
  `vestigial_insert_counterexample` establishes that a new insertion may use a
  vestigial entry as its parent; erasing that parent blocks the same insertion
  and keeping it makes it cease to be childless, contradicting clause (1).
- `counterexample_reachable_full` proves the parent/child example is reachable
  in four full-rule steps from an empty state with the idle model. Read the
  actual `ensures` of these functions: they prove the counterexample's facts,
  not the false lemma.
- [paper_vestige.rs](../crates/cordis-kernel/tests/paper_vestige.rs) executes
  `Kernel::insert → retire → remove` on real Kernel values. The first regression
  obtains `Error::Children`, removes the vestigial child, then removes the parent.
  The second compares insertion under the retained and removed parent.
- [deletion.rs](../crates/cordis-kernel/src/deletion.rs): `full_step_bisimulation`
  and `suffix_deletion` are scoped corrections, with parent/freshness/provision
  exceptions and primitive erasure/retention assumptions. They are not the
  original unrestricted Lemma 62.

**Executable review:**

```sh
cargo test --offline -p cordis-kernel --test paper_vestige erasing_a_vestigial_child_changes_the_parent_removal_guard -- --exact
cargo test --offline -p cordis-kernel --test paper_vestige vestigial_parent_is_observable_to_new_child_insertion -- --exact
```

No host callback is needed to reproduce these control-rule observations. The
stronger claim that arbitrary external effects respect the corrected erasure
laws remains outside this example. See [paper-audit.md](paper-audit.md) for the
full argument and the distinction from the unresolved Child-based objections to
items 78–80.

**Negative-control candidate:** `erasure-drops-parent-read` targets the corrected
transport condition. This is distinct from the two positive proofs of
counterexamples: a counterexample proof is not a mutation-test result.

## PR-04: quiet confluence for a fixed executable program language

**Paper:** §4.3.5, Theorem 80, p.54: clause (1) requests a canonical ordering;
clause (2) compares quiet outcomes under the same orchestration inputs.

**Classification:** a proved restricted result relevant to clause (2).
The original item's status remains `partial`; this chain proves neither the
printed canonical ordering nor unrestricted dynamic-child confluence.

**Review chain:**

- [program.rs](../crates/cordis-kernel/src/program.rs): `ProgramDriver` fixes the
  code, initial private cells, owner, declarations and layout. The executable
  path is `insert → begin → admit → land → finish`, with retirement, departure,
  restoration and removal available between activations. `land` computes from
  that fixed code and lands target drift directly into Unloading. The caller
  cannot supply an arbitrary next value or continuation.
- [program_refinement.rs](../crates/cordis-kernel/src/program_refinement.rs):
  `wf` and `project` connect actual snapshots, program prefixes and journal depth
  to the full-state model. Depth counts actual instructions; phantom stages
  after the program terminates are excluded.
- [program_trace.rs](../crates/cordis-kernel/src/program_trace.rs):
  `raw_execution` describes successful API histories; `driver_trace_refinement`
  produces a full-rule execution under a model built from the actual history.
- [program_normal_form.rs](../crates/cordis-kernel/src/program_normal_form.rs):
  `trace_inputs` derives final configuration from extracted Insert/Retire/Remove
  inputs. `driver_quiet_confluence` requires two such histories, equal initial
  inputs, equal extracted orchestration, both final states quiet and a
  `precedence_ranking` of the first final control state. It ensures equal
  `project` results and full-rule reachability for both histories. Equal final
  payloads or identical intermediate schedules are not premises.

**Executable review:**

```sh
cargo test --offline -p cordis-kernel --test program_normal_form quiet_values_agree_after_different_schedules_and_provider_replacement -- --exact
```

This regression compares schedules including provider replacement and an
in-flight consumer diversion. Read the theorem to assess the universal claim;
the test supplies concrete executions only. The profile uses finite,
forward-moving instructions and private provision cells. Arbitrary payload
operations across providers, dynamic child instructions, all failed-call traces,
and arbitrary Rust/JS callbacks are outside this confluence theorem. The model
constructed for a trace does not automatically meet every original full-context
Component premise. [verified-programs.md](verified-programs.md) details the API.

**Negative-control candidate:** `normal-form-counts-phantom-stages` weakens the
actual-depth invariant. A fresh conclusive rejection is needed before presenting
it as accepted evidence for the reviewed source.

## PR-05: a configuration entry has six distinct fields

**Paper:** §5.2.1, Definition 81, p.65: the six bullets for `id`, `url`, `isolate`,
`intercept`, `config` and `disabled`.

**Classification:** executable encoding of the record and an ordinary-host leaf
projection. This does not prove the reconciliation claims in the following
paragraphs, which also rely on broader metatheory.

**Review chain:**

- [configuration_entry.rs](../crates/cordis-kernel/src/configuration_entry.rs):
  the generic `Entry` is the same executable type verified by Verus and compiled
  by Cargo. `new` preserves exactly its six inputs; `enabled` ensures the
  negation of `disabled`; `set_config` and `set_disabled` frame the other fields.
- `reconciliation_key` pairs the surrounding parent with the entry's `id`;
  the parent is not a seventh field. `sibling_keys` proves sibling key equality
  matches identifier equality. `bound_effect` denotes application of the
  selected module to this config; `binding_ignores_administration` holds when
  URL and config agree. This spec does not execute an arbitrary module callback.
- [loader.rs](../crates/cordis/src/loader.rs): `Entry::as_paper_entry` invokes an
  explicit caller-supplied module URL resolver, then calls the verified
  `configuration_entry::Entry::new`. It accepts named plugin leaves and rejects
  unresolved names, groups, includes and child-bearing entries. It preserves raw
  config before interception/schema normalization and the entry's own
  administrative bit, independent of its parent's effective enabled status.

**Executable review:**

```sh
cargo test --offline -p cordis --test loader paper_leaf_projection_requires_resolution_and_preserves_raw_configuration -- --exact
```

The test parses a disabled parent with an enabled child, verifies the child's
own bit, distinguishes raw config from interception metadata, and checks rejected
projections. The parser, URL resolver, host projection itself, module execution,
whole-tree reconciliation and persistence are ordinary Rust. Their behavior is
not established by verifying the six-field constructor.

**Negative-control candidate:** `configuration-enabled-polarity` changes the
executable boolean result while keeping its contract. Its declaration alone
is not proof that the mutation suite has passed.

## Evidence boundary and review contributions

All five named mutation candidates are defined in
[scripts/check-negative.py](../scripts/check-negative.py). Current accepted
release evidence must come from [verification-report.json](verification-report.json),
not from the presence of a candidate. At the introduction of this guide, that
report records **no successful complete release run**. A timeout, solver resource
failure, compiler error or a failed experimental scoped run is not a passed
negative control. Development verification is reported separately in
[development-report.json](development-report.json).

The release command is `./scripts/quality.sh --offline`; it includes the
full-crate negative controls. It is intentionally a broader and more expensive
check than the selected regressions above. A development pass does not substitute
for release acceptance or paper completion.

A useful review report identifies the case ID, commit and exact function,
then states whether the concern is an incorrect encoding, missing premise,
unconnected executable path, invalid evidence, or an application behavior gap.
Include a small trace or command when possible. Keep engineering-only additions,
such as native ABI limits and resource-accounting counters, labeled as engineering
contracts unless an actual paper correspondence is established.
