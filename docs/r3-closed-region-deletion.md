# R3: deleting Child and consumer episodes together

[简体中文](r3-closed-region-deletion.zh-CN.md) · [Private-episode deletion](r3-script-deletion.md) · [Refinement milestones](paper-refinement-roadmap.md)

Complete native intermediate publication/owner/pending observation recovery is now covered by [package 2](r3-observation-recovery.md). Related boundaries below describe this earlier entry point; ordinary-host migration is covered by package 3; full-effect legal deletion remains open.

Mixed and Fresh script reports now expose `delete_closed_region`: a proof query
that constructs a legal surviving execution from the **same actual source witness**
used by episode recovery. It admits an owner that creates Child and publishes to
active consumers when the affected episodes and names form a closed region.

This is a finite, conditional deletion result. R3 remains in progress.

## What the constructor does

A `Region` selects episode owners and names whose registrations are to disappear.
The latter set includes Child births being deleted and must be a subset of the
selected owners. For selected names that remain registered, the constructor keeps
Insert, Retire and Remove, while omitting activation and cleanup. Their projected
state is Inactive with an empty table and journal. All steps of erased names are
omitted. Unselected actors retain every step, in source order.

The source guards check:

| Source fact | Why it is required |
| --- | --- |
| Retained registrations do not name an erased parent | A surviving insertion must still have its parent |
| Unselected actors' dependency declarations avoid selected owners' provisions at every source state | A surviving Begin or coherence check must not lose its provider |
| Actual table-operation receipts stay on the same side of the region | Removing an internal operation cannot change an unselected callback's input |
| A selected owner's Child receipt captures an erased name; a retained owner's Child receipt does not | Removing the birth and retaining its inverse cannot be mixed |
| At the closing observation, selected registered owners are Inactive and erased registered names are retired | The same real provision history proves their tables empty |

These conditions refer to the original execution and captured receipts. They do
not require a successful target execution, a desired heap or a successful target
inverse. Internal consumers can read and modify their owner's publications; they
are included in the selected region.

## Connection to executable code

Both real script runners already retain an erased `recovery_history_witness`.
The new query uses that witness, constructs the target, and proves its steps legal.
A checked-error report can supply its actual successful prefix as well; endpoint
observation equality additionally requires the closing condition above.

Retained calls are interpreted on their own projected inputs. Their actual raw
outcomes, continuations and partial inverses agree. Original history indices are
compressed, and each retained inverse is related to the corresponding real source
entry. Successful restoration is derived from these primitive laws and source
restoration, rather than supplied as a target premise.

Fresh keeps **each retained source allocation choice** and the root/continuation
returned by its binder. The proof instantiates a node at that particular landing;
it does not encode all activations as one fixed-name Mixed program.

The semantic witnesses remain proof-only. The optional command-preparation API
below allocates a finite name map and a new command plan from the existing report;
it adds no Node dependency or alternative implementation of a verified primitive.

## Nonempty proof client

The client uses the actual Mixed driver's value library:

1. Owner 0 publishes a service and creates Child 2.
2. Independent provider 1 publishes a different service between the owner's steps.
3. Child 2 commits to owner 0 and performs a real XOR on its service. External
   consumer 3 also commits to owner 0 and becomes Active.
4. Owner 0 leaves. Its Unload is proved illegal while those consumers still rely
   on it. Both consumers unload; the Child's original inverse restores the value.
5. Owner 0 unloads, retiring the Child and removing its publication. Provider 1
   then unloads using its own original inverse, and Child 2 is removed.

The 23 source transitions produce **9 legal surviving transitions**. Five source
receipts become one retained receipt: source index 1 becomes target index 0.
The target retains provider 1's real publication and Unload. Omitting either
consumer from the selected episodes, or forgetting the deleted Child birth,
is formally rejected by the source guards.

## Executable allocation mapping

The Fresh report also provides `compact(keep)`. The mask selects successful
transition records in source order. The constructor returns a plan containing a
bidirectional name map, renamed transitions and the allocation bound. Its
`commands()` method emits commands for the existing `fresh::run_script`:

```rust,ignore
let source = fresh::run_script(blueprints(), &commands);
let plan = source.compact(&keep)?;
let replay = fresh::run_script(blueprints(), &plan.commands());
```

Use the same blueprint bank for source and replay. A mask derived from a `Region`
keeps its Insert/Retire/Remove rules as specified above; it is not simply a filter
on the selected actors. Only the successful prefix of a checked-error report is
compacted. The failed command is not silently retried.

The implementation and proofs connect these facts:

- Actual Insert and Child successes allocate the previous bound and increase it
  by one. Failed commands consume no name; Remove never resets the bound. The
  real script constructs this allocation history alongside its semantic witness.
- Every source Insert binds its actual parent and blueprint to that witness.
  A label alone does not carry those command arguments.
- An executable finite permutation pairs retained births with `0, 1, ...` in
  source order. It renames actors, inserted parents and Child outcomes together;
  removed retained names remain consumed. Outside the original allocation prefix
  it is the identity. Construction uses O(allocated names + transitions) work
  and space, with constant-time name lookup.
- A legal surviving execution supplies every command's earlier retained origin.
  The closed-region source guards therefore imply **the executable constructor
  succeeds**, without a caller-supplied target trace or extra origin assumption.
  Malformed birth records and references without retained origins return checked
  errors.
- `Plan::source_execution` constructs a legal execution for the **actual plan**,
  including Insert payloads, compacted Child choices and renamed original inverse
  receipts. The installed Fresh program family stays the same; service keys and
  values are unchanged. Settled endpoints retain the same table observation.

For an admitted closed region, the real `run_script` now completes the compacted
commands with exactly the planned records and the constructed successor states.
`Plan::replay_result` connects that executable result to the original source and,
at a settled cut, to the same service-table observation. A raw `compact` call
still checks allocation/reference consistency only: an arbitrary keep mask does
not acquire the semantic closed-region guarantee merely because it returns `Ok`.
This profile applies to the synchronous Fresh driver, whose Child instruction has
a binder; Mixed's fixed `expected` child literals still need code transport.

The executable regression includes owner/Child/consumer cleanup, retained
publication and Unload, a later Insert whose parent shifts, two later Child
allocations, removed retained names, and a final checked failure in the source.
Its **39 successful source transitions become 25 planned transitions**; replay
through the unchanged public driver matches every planned record and preserves
the live service value `99`. A second case rejects omitted origins, mismatched
mask length, repeated and out-of-range births, while preserving the source report.
These cases exercise the implementation; they do not replace the general proof.

## From a source rule to an executable command

The Fresh dispatcher now has an exact input domain for **all seven commands**.
`apply` succeeds if and only if `command_enabled` holds before the call. On a
checked failure, `run_script` returns the real successful prefix and a machine
in which that next command is disabled. The proof includes the existing rollback
behavior; it does not change the order of runtime checks.

The source witness now retains runtime facts that source legality alone does not
supply: complete Active service tables, the installed root blueprint and its exact
declarations, a validated code prefix, and declaration arrays without duplicates.
The real commands maintain these facts. Closed-region deletion and name renaming
preserve them in `Plan::source_execution`. This matters because the general paper
relation allows some partial-publication Finish steps that this executable profile
rejects.

`source_command_admission` connects a represented, legal source call to the actual
`apply` input domain:

| Command | Connection to the runtime check |
| --- | --- |
| Insert | Source parent/reservation guard and installed blueprint shape, with finite allocation capacity |
| Begin | Source target availability and empty Inactive journal, with generation capacity |
| Step | Actual Unit/Provide/Xor/Child evaluation; retained runtime shape supplies complete terminal publication and unique Child declarations |
| Retire / Depart | Registration, phase and target coherence guards |
| Unload | The same original inverse sequence, dependency guard and an idle cleanup transaction |
| Remove | Retirement, inactivity, empty table, no live ownership children and no retained Child inverse |

The Remove connection also uses a concrete invariant: Inactive and removed rows
have empty journals. `new`, each real command and the script loop maintain it.
Consequently, scanning historical rows cannot introduce a hidden reference beyond
the source's live inverse accumulators. Retirement and registry removal remain
distinct.

The single-command result now composes into **whole finite-script completeness**.
The premise is an empty-origin source execution with the installed runtime shape,
authentic Insert arguments, dense allocation history and synchronous departures.
The ordinary `run_script` establishes `ScriptReport::replays`: every such source
execution for the supplied commands has the same returned records and final
represented state, and the report contains no checked error.

Three connections make this stronger than a legal target trace alone:

- `exact_successor` establishes both the returned transition and its precise
  successor. Source `Divert` also allows an admitted in-flight landing; synchronous
  `Depart` keeps the journal/history unchanged. The real witness records this fact,
  and deletion and renaming preserve it. The separate admitted-landing API remains
  supported by its own contract.
- Kernel metadata contracts follow the actual stored generation and restoring
  fields through Insert, Begin, primitive evaluation and reverse cleanup. At
  command boundaries no cleanup lock is left behind, and every generation is
  bounded by the processed command count. Before the next command, the slice
  length supplies generation capacity and allocation capacity. No larger counter
  type or runtime counter is added.
- The existing runner maintains the exact target prefix in erased proof state.
  A legal next source call therefore cannot enter its checked-error branch.
  The proof does not assume an executable target succeeds and adds no replay
  interpreter or runtime trace storage.

A further runtime case retains a Loading/Divert departure, restores its original
provider effect, removes that provider, and reactivates the same consumer against
a new provider after Child compaction. Its **26 source transitions become 21**;
all records match, and the final service value remains `8`.

## Review path

| Obligation | Code |
| --- | --- |
| Source closure, primitive footprints, actual inverse transport | [closed_region_deletion.rs](../crates/cordis-kernel/src/closed_region_deletion.rs): `closed`, `local`, `run`, `restore` |
| Complete lifecycle step transport | [closed_region_execution.rs](../crates/cordis-kernel/src/closed_region_execution.rs): `step` |
| Constructed execution and closing observation | [closed_region_trace.rs](../crates/cordis-kernel/src/closed_region_trace.rs): `from_source`, `closing_observation` |
| Actual Fresh choices and trace construction | [closed_region_fresh.rs](../crates/cordis-kernel/src/closed_region_fresh.rs), [closed_region_fresh_trace.rs](../crates/cordis-kernel/src/closed_region_fresh_trace.rs) |
| Actual Mixed / Fresh report queries | [script_deletion.rs](../crates/cordis-kernel/src/script_deletion.rs), [fresh_region_deletion.rs](../crates/cordis-kernel/src/fresh_region_deletion.rs): `delete_closed_region` |
| Actual allocator history and Insert payloads | [fresh_allocation_history.rs](../crates/cordis-kernel/src/fresh_allocation_history.rs), [fresh_driver.rs](../crates/cordis-kernel/src/fresh_driver.rs): `run_script` |
| Executable name map and command preparation | [allocation_names.rs](../crates/cordis-kernel/src/allocation_names.rs): `pair`; [fresh_compaction.rs](../crates/cordis-kernel/src/fresh_compaction.rs): `compact`, `commands` |
| Source-derived origins and plan execution | [fresh_compaction_origins.rs](../crates/cordis-kernel/src/fresh_compaction_origins.rs): `from_region`; [fresh_compaction_source.rs](../crates/cordis-kernel/src/fresh_compaction_source.rs): `source_execution` |
| Exact real dispatcher and quiescent journals | [fresh_driver.rs](../crates/cordis-kernel/src/fresh_driver.rs): `apply`, `run_script`; [fresh_dispatch.rs](../crates/cordis-kernel/src/fresh_dispatch.rs): `command_enabled` |
| Source call to executable admission | [fresh_dispatch_source.rs](../crates/cordis-kernel/src/fresh_dispatch_source.rs): `source_command_admission`; [fresh_dispatch_step.rs](../crates/cordis-kernel/src/fresh_dispatch_step.rs) |
| Actual runtime shape and compaction preservation | [fresh_execution_shape.rs](../crates/cordis-kernel/src/fresh_execution_shape.rs): `source_runtime_shape`, `deleted_trace`, `renamed_trace` |
| Exact successors and synchronous branch transport | [fresh_dispatch_exact.rs](../crates/cordis-kernel/src/fresh_dispatch_exact.rs): `unique`, `exact_successor`; [fresh_synchronous_transport.rs](../crates/cordis-kernel/src/fresh_synchronous_transport.rs) |
| Actual finite-machine metadata | [lib.rs](../crates/cordis-kernel/src/lib.rs): `synchronous_metadata`; [fresh_runtime_metadata.rs](../crates/cordis-kernel/src/fresh_runtime_metadata.rs): `metadata_progress`, `metadata_admission` |
| Whole real-script completeness and plan result | [fresh_script_completeness.rs](../crates/cordis-kernel/src/fresh_script_completeness.rs): `source_call_at`, `unique_path`, `replays`; [fresh_compaction_source.rs](../crates/cordis-kernel/src/fresh_compaction_source.rs): `replay_result` |
| Executable replay regression | [fresh_compaction.rs](../crates/cordis-kernel/tests/fresh_compaction.rs) |
| Nonempty client and rejected incomplete regions | [closed_region_example.rs](../crates/cordis-kernel/src/closed_region_example.rs): `nonempty`, `source_guards` |

This is an admitted constructive case relevant to Lemma 79. The existing
single-episode value theorem remains the Equation (55)/(56) result. Deleting a
closed family is not an unrestricted single-owner deletion theorem, and does not
change the original paper's partial or refuted audit outcomes.

## Remaining boundaries and acceptance

- The selected owners are fixed over the supplied empty-origin history. Repeated
  episodes are supported as part of that region; selecting only one generation of
  a reused identity requires a finer episode-indexed construction.
- Writes across the region boundary are excluded. Shared external-table effects
  covered by private-episode deletion are not yet combined with this construction.
- Whole-trace executable replay is covered for the synchronous Fresh profile
  above. Mixed fixed-name code transport and admitted asynchronous landing
  transport remain open; no fairness or arbitrary callback guarantee is implied.
- Ordinary Runtime/Node integration, complete host-generated history coverage and
  general publication/pending recovery at intermediate cuts remain open.
- Runtime acceptance includes the three Fresh compaction cases above and repeated
  consumer activation. Deferred: broader Mixed/Fresh integration, complete fault
  demonstrations, and proof mutations that retain a consumer, drop a Child origin,
  substitute a retained inverse, allow a landed Divert in a plain command, or
  discard the generation/cleanup metadata connection.

The final source passed **382 scoped Verus checks, 0 errors**, covering the root
kernel, the Mixed driver module and the complete Fresh subtree. The pinned
verifier used `--no-cheating` and compiled the checked executable source; this is
not a whole-crate or paper-wide verification result.

The six selected runtime suites passed **60 tests**, including all three compacted
replays. Kernel all-target/all-feature Clippy with warnings denied, formatting,
paper mapping/coverage/review consistency and **563 local documentation links**
also passed. Whole-development acceptance and full negative controls remain
**not run**. R3 remains in progress under the boundaries above.

```sh
source scripts/toolchain-env.sh
./scripts/verify.sh --verify-root --verify-only-module mixed_driver --verify-module mixed_driver::fresh \
  --num-threads 2 --triggers-mode silent --output-json
CARGO_INCREMENTAL=0 cargo test -p cordis-kernel --test fresh_driver --test fresh_compaction \
  --test fresh_bootstrap --test mixed_driver --test lifecycle --test ownership --locked --offline
CARGO_INCREMENTAL=0 cargo clippy -p cordis-kernel --all-targets --all-features \
  --locked --offline -- -D warnings
python3 scripts/check-paper-refinement.py
```

[Native episode-window deletion](r3-native-deletion.md) now covers the actual native lifecycle/publication/owner projection with an exact interior splice. It is separate from this whole-region Mixed/Fresh theorem and does not close shared-effect or executable production transport.
