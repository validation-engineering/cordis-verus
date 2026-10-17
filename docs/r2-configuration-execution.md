# Configuration updates: from owned plans to accepted revisions

Current R2 status is defined by [package 5 acceptance](r2-acceptance.md): managed-production/v1 is complete. Earlier checkpoints below retain their original evidence and scope.

## Historical implementation and verification checkpoints

Package 3 now supplies the configuration-data and binding interpretation, including schema normalization and source round trips. The earlier checkpoints below document protocol increments; their open-boundary statements should be read with the current remaining-boundaries section and the [package 3 review](r2-configuration-semantics.md).

[中文](r2-configuration-execution.zh-CN.md)

The production Loader now uses checked owners for its actual update plans,
forward/inverse Futures, accepted snapshot and recovery inputs. An incomplete
update cannot authorize a configuration commit. A pending or failed inverse
cannot authorize completion of recovery. These are executable protocol
guarantees; they do not prove an arbitrary plugin's inverse undoes its I/O.

## Paper obligation and runtime path

Definition 81 identifies a configuration entry by its parent-local `id`, module,
context annotations, bound configuration and administrative status. The following
reconciliation discussion relies on correct instantiation/withdrawal and the
premises of the paper's recovery, termination and convergence results. This batch
connects one necessary part of that interpretation: an accepted in-place update
must belong to the intended registered component and must follow the actual
execution/recovery outcome. It does not close Theorems 73 or 80 or reinterpret
groups/includes as already proved leaf entries.

The actual call chain is:

1. `Loader::apply_transaction` captures a native `Target` for each update and
   stores an `Action<UpdateKey, ConfigUpdatePlan>` in `Configuration::begin_structural`.
   Its path and target stay separate from the mutable callback payload.
2. `Loader::apply_prepared` drives `Configuration::poll_update`.
   `Batch::poll_apply` selects the next stored action and lends its actual plan
   to the host. The host checks its captured target before polling it.
3. `ConfigUpdatePlan` owns a `Reversible` containing the actual pinned forward
   Future, inverse factory and any pending inverse Future. The checked owner
   caches the actual forward result and preserves pending Futures across caller
   cancellation. The host only polls and converts caught panics to errors.
4. Once all actions succeed, `Runtime::adopt_config_recipes` calls the checked
   `NativeRuntime::adopt_configurations`. The kernel preflights the whole owned
   batch and proves every target/body/metadata adoption before returning success.
5. `Configuration::commit` checks its own batch and consumes its own candidate.
   On failure or cancellation, `Loader::recover` instead drives the retained
   actions in reverse order before rebuilding the accepted tree.

## Structural reconciliation and native allocation evidence

The production Loader now enters `Configuration::begin_structural`. Its checked
phase owner requires removal, successful settlement, mounting and successful
settlement before any in-place update. Actual recipe adoption follows those
updates; only then may `commit` accept the candidate. Recovery drains inverses,
removes failed/new allocations, settles, reconstructs and settles again. A
pending or failed callback preserves its phase and the actual staged payload.
Resuming recovery does not repeat earlier successful reconstruction stages.
The erased `forward_steps` and `recovery_steps` sequences prove these ordered
prefixes; the public poll contract links each advancement to the real callback's
successful return, including its actual arguments and before/after payloads.

`configuration_tree::Tree` owns the actual node names, immutable recipe payloads,
enabled flags, parent indices and allocation records. The ordinary path index is
a cache: `Tree::get` checks the requested name against the stored node. Insertion
rejects duplicate names and invalid/disabled parents. Mounting selects the parent
from the tree itself and rejects a missing parent before calling the factory;
it cannot silently attach a child to the outer root. An actual failed call leaves
that node's recipe and identity available for retry.

`Runtime::mount_configuration` obtains a private `Allocation` from the real
`NativeRuntime`. The allocation contains domain, identity and parent evidence
from a certified native execution snapshot. Tree mounting accepts only the
expected domain and parent; a rejected allocation is returned by the kernel API.
Parent replacement may temporarily leave a retained child bound to the old
parent. `Tree::ready` rejects that state until the child has the correct parent.
This is an explicit reconciliation intermediate state, not an invariant that
would forbid valid updates. Snapshot and prefix evidence are erased by Cargo.

Production `recover_with` extracts the accepted snapshot through a callback on
the actual retained recovery payload after all recovery phases succeed. It takes
no caller-selected replacement snapshot. This establishes result provenance;
it does not by itself prove that arbitrary reconstruction callbacks restore the
paper's entire context.

Review `configuration_tree::{mount, ready}`, `configuration_runtime::configuration_allocation`,
`configuration_transaction::{poll_structure, commit, recover_with}` and the actual
`Loader::{apply_prepared, recover}` callers. Tests cover missing/incorrect parents,
foreign domains with colliding numeric IDs, stale path caches, intermediate
parent replacement and interruption at every structural phase. Strict negative
controls also reject skipping structural commit/recovery and accepting a wrong
cache entry.

Full development evidence is generated in [development-report.json](development-report.json)
by `python3 scripts/record-development.py --offline`. Its status and source hashes
must match the checkout; it remains distinct from whole-R2 semantic acceptance,
full negative regression and release/platform checks.

## Parent-local identity and complete structural dispatch

The production planner now calls `Tree::prepare_entry` with the actual entry ID,
parent index and administrative flag. The checked code constructs the path from
its stored parent and propagates disabled ancestry. `insert_entry` rechecks that
preparation against the current tree. The local-ID grammar permits Unicode,
requires a nonempty value and excludes `/` and `:`. The
`qualified_key_identity` and `local_key_correspondence` proofs establish that the
implemented path encodes the pair **(parent, local ID)** injectively: different
parents can use the same local ID; siblings cannot. This connects Definition 81's
reconciliation key to actual Loader inputs without interpreting every JSON field.

The tree also rejects assigning one native allocation to two different entries.
`Tree::retirements` compares the actual old and candidate trees and selects exactly
those old allocations not retained at the same path with the same identity. It
rejects a changed runtime domain/root for a nonempty old tree. The real remove
phase calls `retire_into`: its erased receipt records every actual `dispose`
callback, argument, host state and result. Success covers the complete selection;
failure records the first failed call and stops before later selections.

Both normal mounting and recovery now call the same checked `Tree::reconstruct`
loop. It uses the authoritative parent-before-child node order, skips disabled
entries and gives the callback the stored recipe and current parent identity.
The host re-reads the native allocation before retaining it. It invokes the saved
factory when replacement is required. The checked tree rejects a returned
allocation with the wrong domain, parent or a duplicate identity. A successful
pass has visited every enabled entry and satisfies `Tree::ready`; names, local-ID
origins, administrative status, parent indices and recipes remain unchanged.
Failure preserves the completed prefix and leaves the failed node and later
nodes unchanged; no later callback runs. Callback side effects before an error
are retained in the receipt, not assumed to have been undone.

`Rebuilt::visits`, `chain`, `complete_prefix` and `removal_prefix` are erased proof
evidence for these actual loops. The ordinary `Snapshot::order` list has been
removed. Allocation snapshots certify real native observations at capture time;
they do not promise continued liveness, quiescence or equivalence of arbitrary
factory effects. Source-backed structural expansion is connected below; complete
group/include Component meaning, module/configuration meaning and the common
native/Node/configuration Journal still need their own interpretation.

Review the executable [identity](../crates/cordis-kernel/src/configuration_identity.rs),
[selection and removal](../crates/cordis-kernel/src/configuration_selection.rs),
[reconstruction](../crates/cordis-kernel/src/configuration_reconstruction.rs),
and their [Loader callers](../crates/cordis/src/loader.rs).

Deferred integration evidence for this batch:

- Repeated Unicode IDs under different parents; duplicate siblings, invalid IDs,
  disabled ancestry and stale preparations.
- A real callback failure after a successful parent, followed by recovery retry;
  preserve the successful allocation and use the reconstructed parent for its child.
- A moved path, replaced ID, foreign domain and duplicate allocation; reject
  mutants that keep the wrong allocation, skip a node or continue after failure.

The identity/dispatch checkpoint is historical. Current source-bound scoped
validation is recorded with the planning contract below; preceding development
records must not be carried to changed sources.

## Source-backed group and include expansion

`read_tree_cached`, used by both file loading and save preflight, now executes
[`configuration_expansion::Expander`](../crates/cordis-kernel/src/configuration_expansion.rs).
Its input is an owned entry forest: each node contains its actual payload, inline
children and optional include request. The adapter moves these fields into the
expander and moves the expanded result back; no expected output tree is supplied.

The checked algorithm first expands inline children, then reads an include with
the current document's base and the node's actual request, recursively expands
that returned document and appends its roots below the requesting entry.
`Forest::valid` and `Branch::valid_for` describe the complete recursive result:
every input position has one output with the same payload, child order is exact,
and included roots cannot become siblings of their requesting entry. The erased
read intervals are contiguous and exhaustive, so the derivation cannot omit a
read or justify a child using a different successful read.

The expander owns the actual reader state. Its erased history connects each
request and returned document/error to the real callback's before/after state.
`failure_from` additionally requires a returned read error to be the exact error
from this expansion's last actual read; an earlier or fabricated error cannot
satisfy that contract. Successful derivations carry the actual file-identity ancestry; it is acyclic
and bounded. A reported cycle contains the traversed distinct prefix followed
by an identity already in that prefix. Native path bytes are used as identity
inputs; lossy Unicode conversion cannot merge two paths in this check. Path
canonicalization and the association between those bytes and filesystem objects
remain the adapter's responsibility.

The existing nesting limit is now checked across include boundaries during
expansion, before applying the new revision. This avoids resetting tree depth at
each file. Read/expansion failure returns no accepted output forest; the caller
retains its preceding accepted configuration and source records. Source
checkpoints retain the actual parsed records used for expansion, so `load_file`
no longer parses the same files again after the runtime revision commits.

JSON decoding and the small entry conversions remain ordinary Rust input/output
adapters. The proof begins at the structured forest. It does not prove filesystem
truth, URL/module/schema interpretation, the group component's complete effect
function, source-save round-trip semantics or the common native/Node/configuration
Journal. It also does not prove an external reader eventually returns.

Deferred integration evidence: nested inline/include order and payloads; a shared
include instantiated under two different parents; a failed nested read followed
by retry; native-byte path identity and actual cycles; the total nesting limit
across several files. Selected strict mutants should drop/reparent an included
root, substitute a read result or skip a cycle/depth guard. These are new evidence
items; existing Loader regressions are recorded separately.

## Complete source-to-plan traversal

The actual `Loader::prepare` now calls
[`configuration_planning::plan`](../crates/cordis-kernel/src/configuration_planning.rs).
The checked traversal linearizes the structured input in exact depth-first,
parent-before-child order. `preorder` includes every entry, including disabled
entries, and gives each child its real parent's position. The planner constructs
its own `Tree`; the host no longer supplies a completed candidate tree or drives
a separate recursive visitor.

Each callback receives the stored source payload, the checked parent-local
`PreparedEntry`, and the context returned for that exact parent. Root entries
receive the supplied root context. In production, that context holds scope,
inherited injection configuration and the parent's retention decision. The
callback performs the actual module/service lookup, schema normalization and
retention decision; the checked planner stores its returned recipe and allocation
before processing children. The ordinary path map is rebuilt from checked keys
and remains only a lookup cache.

`prefix` and `chain` connect the complete input order, actual callbacks, host
states, parent contexts and stored recipes. Success covers every source position
exactly once. A callback failure is the exact error of the last call, which is
still bound to its source entry and real parent context. Earlier accepted nodes
remain in the erased partial-plan evidence; no later callback runs. Structural
rejection also stops dispatch. A failed plan does not expose a runtime `Tree`
that the Loader could accept. Input depth/capacity rejection runs before any
planning callback. These logs and the partial-plan evidence are erased by Cargo.

This connects structured input traversal to the existing retirement/reconstruction
and transaction owners. The small `Entry::into_planning` conversion, schema and
module meaning, context transformation semantics, callback side effects and
whole-Component membership remain explicit adapter/semantic obligations. A real
callback result is not itself a proof of that callback's effect laws.

Deferred integrated evidence: nested groups/includes with multiple siblings;
disabled ancestors; different parent-specific scopes, injections and retention
decisions; failure after a successful parent followed by a fresh planning retry;
and duplicate keys or allocations rejected before later callbacks. Strict
mutants should skip an input, use a sibling's context, store another recipe,
continue after failure or return a failed partial tree as accepted.

The preceding planning-source checkpoint passed **158 scoped
Verus checks, 0 errors**, workspace/all-targets/all-features Clippy with warnings
denied, and **59 existing Rust regressions** (8 kernel configuration and 51
Loader/update/service-configuration/persistence cases). The proof command also
compiled the same kernel source. These are configuration-scoped checks, not
whole-kernel, whole-R2, full negative regression or release acceptance. New
integration cases above and the complete development record remain pending.

## Complete adoption of actual registered recipes

`Runtime::adopt_config_recipes` now calls the checked
[`NativeRuntime::adopt_configurations`](../crates/cordis-kernel/src/configuration_adoption.rs)
through the native driver. It supplies the owned batch of actual targets, setup
bodies and metadata. The ordinary host retains plugin/interface compatibility
checks; it no longer implements the distinct-target/capacity loop or relies on
an `expect` after that loop to justify successful replacement.

`preflight_configurations` checks every captured domain, active generation,
recipe revision, duplicate owner and revision capacity before changing any
registration or calling the metadata updater. Its result is equivalent to
`ready` for the whole batch. Rejection identifies an actual invalid target,
duplicate or exhausted revision and returns the complete original payload batch.
The rejected call leaves the native owner unchanged.

The checked adoption loop proves each remaining target stays current while
preceding distinct targets are replaced. A successful return covers every input
in its original order: the exact setup body is installed, its revision advances
once, the original body is returned, and `metadata_call` relates the actual
before/after host value and returned metadata to that same entry's updater.
Unselected entries are unchanged. Declarations, realms, parent identity,
lifecycle state, publication values and the active episode remain unchanged;
this is a configuration extension changing future function recipes, not a
stutter on the complete function-bearing state.

The production updater only swaps the name and the next-activation update hook.
It returns displaced values rather than dropping user captures between swaps;
old bodies and hooks are released after the complete batch returns. The live
episode retains its existing update hook. `Configuration::poll_structure` sees
the actual result, so only complete adoption can advance to configuration commit.

The contracts distinguish normal `Err` (no native mutation) from normal `Ok`
(complete adoption). They do not give rollback after an arbitrary metadata
updater panics, prove callback side effects or destructor semantics, or certify
an arbitrary replacement body as a Component. Interface compatibility, conversion
from `Plugin`, host-field meaning and complete native/Node/configuration semantics remain
explicit obligations; typed recipe records now join the common Journal below.

The [native runtime cases](../crates/cordis-kernel/tests/native_runtime.rs)
exercise a stale second target and a duplicate second owner without touching the
first entry, plus a successful reversed-order batch with distinct new bodies and
metadata. They also check exact old payloads, version changes, stable generations
and retained publication handles. Deferred strict mutants should skip duplicate
or capacity checks, store a different body, omit a returned previous payload or
update metadata on the wrong owner. Host destruction-order fault cases and
whole-R2 acceptance remain separate.

The preceding adoption-source checkpoint passed **169 scoped configuration Verus checks plus
2 separately selected dependency checks**, all with zero errors, and strict
workspace Clippy across all targets and features. **81 Rust regressions** passed:
30 kernel configuration/native-runtime cases and 51 Loader/update/persistence
cases, including the two new adoption cases. These results cover the source of
this adoption batch; they are not whole-kernel verification, complete R2
acceptance, negative-control verification or release/platform acceptance.

## Registered recipes in the common execution history

The production native owner now retains an erased
[`recipe_history::History<R>`](../crates/cordis-kernel/src/recipe_history.rs)
of the exact `RegisteredPlugin<R>` values. Its private ledger commits to the
same Journal as lifecycle, value writes, slots, work and cleanup. The common
[`Recipes` record](../crates/cordis-kernel/src/recipe_execution.rs) projects the
real domain, component, parent, anchor, realms, declarations and recipe revision;
it does not invent an interpretation for arbitrary callback bodies.

Ordinary and SharedChild registration record the installed body at revision zero.
Removal records the actual removed entry. Replacement records the new typed
body and the single revision increment while retaining the live Episode and
publications. `call` and `call_opaque` record the actual returned invocation;
`run_value_root` and `run_service_root` record their real registered program's
return, including a returned inner failure. The public contracts tie each event
to the actual before/after registry and returned result. Rejected admission or
invocation does not append a successful call event. An `FnMut` may change its
captured state without changing the installed recipe revision; the typed history
retains that real before/after value rather than pretending the body was constant.

A recipe call commit certifies the actual native owner under the held Journal
write lock: the lifecycle ticket, work domain, Loading phase and non-retired
status must agree. No callback runs while that lock is held. Lifecycle insertion
or removal and its recipe record are ordered internal steps; this is not a claim
that the pair is one atomic paper transition. `recipe_snapshot` observes the
recipe record and native owner together in one read epoch.

`Snapshot::complete_projection` proves that every recipe-record mutation in the
checkpoint has an indexed typed state. `History::installed_origin` derives an
actual earlier insertion/replacement for a retained version. Together with the
exact event indices and cross-record guard, `Snapshot::invocation_origin` relates
a call to that installed version and the actual retained native Episode. Real
value/cleanup operations may interleave between recipe events; they remain in
the common history.

Cargo erases the histories, old bodies and proof indices. A snapshot keeps a
shared Journal handle, not old plugin captures. The native regression exercises
replacement of an admitted recipe, rejection of the stale call, cancellation,
restart, a call of the new body, retirement/Leave and removal, while retaining
snapshots and checking that old captures are released.

A returned callback may only have constructed a Future. Its completion is still
tracked by the existing awaited-result/work contracts; this event does not prove
that Future termination, arbitrary external effects or whole-function Component
membership. The Node object/Fiber/HMR interpretation, complete configuration
meaning and cross-host semantic composition remain R2 work. Deferred strict
mutants should omit a recipe record, change its version/owner, associate a call
with a foreign native key, or drop a SharedChild insertion. Complete development
and R2 acceptance remain separate from the scoped evidence below.

## Configuration phases in the common execution history

The production `Loader` now uses
[`configuration_recorded::Recorded`](../crates/cordis-kernel/src/configuration_recorded.rs).
It owns the actual `Configuration` protocol and a typed ledger allocated in the
same Journal as its Runtime's native lifecycle, recipes, values and cleanup.
Its constructor receives the Runtime's real Journal. No mutable protocol owner
escapes the wrapper; the same owner now also holds the source state described below.

Successful begin, every forward/rollback/structural poll return, commit,
reconstruction and source-representation refresh record their exact before/after
protocol values. Actual `Pending` and error results are classified separately
from completion. Rejected begin/commit/recovery/refresh operations preserve the
whole owner, including its history. A refresh can change configuration payloads
without changing the lifecycle revision, so it is an explicit metadata transition.

[`configuration_batch::{apply_result, rollback_result}`](../crates/cordis-kernel/src/configuration_batch.rs)
and `configuration_transaction::{update_result, structure_result}` expose the
actual callback argument, before/after payload and returned-result relations
through the composition boundary. This includes partial changes on Pending or
failure, not only successful phase advancement. Recovery still obtains its
accepted result from the retained payload's actual reconstruction callback.

[`configuration_history::History`](../crates/cordis-kernel/src/configuration_history.rs)
keeps exact typed candidates, recovery payloads and update plans in erased
evidence. Its entries are indexed into the shared Journal's
[`Configuration` records](../crates/cordis-kernel/src/configuration_execution.rs).
`Snapshot::complete_projection` proves every change of that configuration record
in the captured common trace has its typed entry; unrelated records may interleave.
`History::commit_inputs` derives the complete owned success prefix and exact
candidate of a commit. `accepted_origin` traces accepted payloads to the actual
initial state or an explicit commit/reconstruction/refresh.

Callbacks execute outside the Journal lock. Their native/value/cleanup actions
can therefore precede the recorded poll return, with other owners interleaved.
The configuration event is a return boundary, not an atomic transaction around
the callback. The complete history and old plans/Futures erase; the wrapper keeps
the current protocol, sources and shared Journal handles at runtime.

This establishes actual configuration event ordering and typed provenance in the
native trajectory. Source/checkpoint transitions now join the same Journal as
described below. Group/include Component laws, JSON/merge meaning, arbitrary
callbacks/destructors and the full Node/Fiber/HMR interpretation remain R2
obligations; an event label alone does not discharge them.

Deferred integrated evidence: interleave real value writes and configuration
polls, inject a failed update and failed inverse, retain a checkpoint through
recovery, and check that old Future captures are released. Strict mutants should
omit a configuration record, alter its outcome or substitute the returned
recovery payload. The source/phase cases below close a subset of this evidence;
the broader scenarios remain pending.

## Loader runtime ownership and joint observation

`NativeRuntime::configuration` now constructs the actual `Recorded` owner from
its own Journal. `Loader::with_runtime` uses this checked producer through
`NativeDriver` and `Runtime`; it keeps both the runtime and configuration private.
The public `runtime_mut()` returns [`RuntimeAccess`](../crates/cordis/src/runtime/access.rs),
a view of mutable runtime operations with read-only `Deref`. It supports mount,
update, restart, cleanup/retry, settlement and shutdown, but cannot yield
`&mut Runtime` for replacing the host. This closes a concrete safe-Rust escape:
previously `mem::replace(loader.runtime_mut(), Runtime::new())` could leave the
configuration and source checkpoints attached to the old Journal.

Futures consume the operation view and retain its underlying exclusive borrow.
For example, `let pending = loader.runtime_mut().settle();` can be awaited later;
dropping it preserves the existing cancellation/recovery behavior. Code requiring
an unrestricted `&mut Runtime` must use an owned Runtime or accept the operation
view instead. This is an intentional unreleased API restriction.

`Loader::execution_snapshot()` reaches the checked
[`NativeRuntime::configuration_snapshot`](../crates/cordis-kernel/src/native_configuration.rs).
Under **one Journal read epoch**, it authenticates the actual native member,
configuration ledger and source ledger. The result binds the current native
control/publication/episode-ownership observation and both exact typed histories to the
same captured sequence. `Snapshot::complete_projection` proves that each native,
configuration and source record modification in that sequence has a corresponding
typed state, including changes interleaved between the owners' last writes.
Source checkpoint-origin and accepted-configuration proofs apply to this same
capture. A fresh Journal or omission of native-member authentication must fail
the corresponding constructor/snapshot contract.

Only one Journal handle is retained in the combined snapshot. Old payloads and
histories are erased; this API is proof evidence, not a persistent audit log.
No plugin callback or payload lock is entered while holding the Journal read.
The kernel's low-level snapshot still requires a configuration from the same
Journal. The ordinary Loader adapter preserves this premise through construction,
private fields and the restricted view; that Rust ownership argument does not
amount to verification of the complete Loader or arbitrary callbacks. Full
Component, Node and source-meaning obligations remain open.

## Source checkpoints in the configuration execution history

`Recorded<S, R, K, U, P, V>` now owns both the actual configuration and its
`sources::Source<P, V>`. Production `Loader` no longer stores an independently
mutable source object. `load_file`, `load_json`, disposal and `SavePlan::commit`
all use this composite owner. Read-only access supports projection and save
planning; neither the source nor the configuration can be replaced through a
mutable reference from the wrapper.

`load_sources` and `clear_sources` reject an outstanding update/recovery without
changing either history. Rejected loads return their actual inputs. Save
acceptance consumes the real cursor, validates its original domain/revision and
retains the existing processed-prefix and pending-sync rules. The save adapter
borrows the whole owner exclusively during I/O and acknowledgement; its report
cannot update a separate source object.

The source recorder is constructed from the actual configuration ledger. Its
[`Sources` transition](../crates/cordis-kernel/src/source_execution.rs) authenticates
that configuration record under the same held Journal write epoch, requiring no
pending transaction. The event contains the observed configuration state,
including its execution index as well as its accepted revision. Recovery and
refresh can retain the revision but still produce distinct indexed states.
Source changes use `Member::update_guarded`; the unguarded update APIs exclude
them. Actual payload changes and drops occur before taking this lock, and user
callbacks remain outside it.

[`configuration_source_history::Snapshot`](../crates/cordis-kernel/src/configuration_source_history.rs)
captures the typed source and configuration histories with one common Journal
read. `complete_projection` covers every change of this source record.
`accepted_configuration` resolves a load, clear or save to an exact earlier
typed configuration state in that trace. `checkpoint_origin` combines this with
the real load/processed-document history: every retained merge base has an actual
introducing event and an associated accepted configuration state. These facts
are derived from execution, not supplied as a pair of expected snapshots.
Histories, old configuration values and review states erase; current payloads
and Journal handles remain at runtime.

This closes source/configuration ownership and ordering. It does not prove that
arbitrary loaded JSON or three-way merge output denotes the accepted Component
tree. The real parser, include expansion, group meaning, filesystem truth and
full native/Node interpretation still need their respective refinement premises.
The existing adapter checks on tree, registry and source contents remain
necessary; a numeric revision alone does not establish equal payloads after a
same-revision refresh.

Two integrated cases exercise same-Journal callback interleaving, pending-source
rejection, structural failure/reconstruction, retained checkpoints, failed sync
and no-op sync retry, foreign domains and an old save after commit. The real
filesystem fault test now also uses the composite owner. New strict controls
remove load admission during recovery or wire the source recorder to a different
Journal. The broader value-write/Future-drop and full configuration-semantic
acceptance scenarios remain on the checklist above.

## Actual save execution and reviewed revision

`SavePlan` stores each actual document in
[`configuration_save::Document`](../crates/cordis-kernel/src/configuration_save.rs).
Its observed/output strings, immutable path/permission/configuration payload and
durability-retry flag are the inputs to the checked `Save` owner. `Save::step`
calls the host on that stored document in this order:

`Check → Prepare → Recheck → Replace → Sync → Done`.

The production callback checks source bytes/permissions and include targets,
prepares and synchronizes a sibling temporary file, rechecks the source, replaces
it and synchronizes the parent. Only the actual successful return advances the
phase. Failure halts the save, preserves every completed prefix and leaves later
files untouched by this protocol. Unchanged files skip preparation/replacement;
a pending durability retry still requires `Sync`. The erased per-file history
proves all required successful phases before a completed save. There is no
public operation for acknowledging an unexecuted phase.

The ordinary adapter builds `SaveReport` from checked progress. A completed
replacement followed by failed synchronization is **written and durability
uncertain**, and is excluded from the remaining-file suffix. A retry of an
unchanged file does not repeat its replacement. This models the actual result
of each I/O call; it does not prove the operating system's durability guarantee,
atomicity across files or exclusion of a concurrent external editor. The
replacement protocol is an explicit persistence extension to the paper's entry
description, not a paper theorem about filesystem crash recovery.

`Configuration::save_stamp` captures the real accepted revision when no update
or recovery is pending. `Loader::prepare_save` supplies the actual runtime domain;
`commit_save` uses `Configuration::accepts_save` with its current domain before
any file operation. This rejects an old plan even after configuration A changes
to B and back to A. Another runtime cannot accept the plan merely because its
tree and revision numbers coincide. Domain uniqueness remains the native
runtime allocator's boundary. Registry/source/include checks still apply.

The [direct protocol cases](../crates/cordis-kernel/tests/configuration_save.rs)
inject a failure at every save phase and exercise partial reports, unchanged
files, barrier retries and stopped dispatch. The
[actual file cases](../crates/cordis/tests/persistence.rs) cover revision ABA and
foreign-runtime plans alongside existing include, conflict and partial-save
cases. Selected strict mutants skip synchronization, hide durability uncertainty,
or discard revision/domain checks; they must fail the exact named contract after
successful compilation and a matching positive check.

This closes local save ordering, reporting and accepted-revision provenance.
Complete group/include and configuration-to-Component semantics, source
projection/merge meaning and complete native/Node semantic composition remain
open. Source checkpoint ownership and native Journal ordering are connected
above and below; a per-file save protocol does not discharge the remaining laws.

## Source checkpoints derived from the actual save

The real `Loader::configuration.sources` is
[`configuration_save::sources::Source`](../crates/cordis-kernel/src/configuration_source.rs).
It owns loaded root/text/include resolutions and a single checkpoint record per
path containing both the local configuration value and its pending-sync flag.
`load`, `clear` and accepted saves extend one erased history; clearing runtime
state does not erase its proof history. A load preserves outstanding sync for
retained checkpoint keys. Only read-only views are exposed to the JSON adapter.

The production save consumes its reviewed `SaveStamp` through `start` before
dispatching any I/O. The actual `Save` owns this stamp, and `step` preserves it.
There is no operation to re-stamp an already executed cursor.
`Configuration::accept_saved_sources` consumes that cursor and checks its stored
domain/revision against the actual configuration with no outstanding recovery.
Unreviewed, stale or foreign-domain saves are returned unchanged without changing
the source owner. The production adapter exclusively borrows `Recorded` throughout
the synchronous I/O and acceptance and uses its `accept_saved_sources` entry point;
the configuration cannot change between those checks.

Checkpoint updates consume the actual stored documents and phases; `SaveReport`
does not authorize them. Only `Sync` or `Done` advances a document's local merge
base. `Sync` retains pending durability, including after failed directory fsync;
successful retry reaches `Done` and clears it. Earlier failures leave that file's
checkpoint unchanged. `advance_origin` proves the last processed document wins,
including duplicate keys; `advance_frame` preserves every unprocessed key.
`History::checkpoint_origin` traces each retained base to an actual load or a
processed document. `Saved::acknowledgement` derives the successful Check and,
when needed, Replace/Sync calls from that document's real phase history.

The checkpoint is the saved **local intent**, not the merged disk text: external
fields can remain on disk without becoming runtime configuration. Saves preserve
loaded source text, root and include resolutions. The filesystem fault regression
now replans from the retained owner after a failed directory sync, instead of
constructing the expected checkpoint and pending flags in the test.

This closes source bookkeeping and review/result provenance as an explicit
persistence extension to Definition 81's configuration-entry interpretation.
It does not prove JSON decoding, source projection or three-way merge semantics,
filesystem/path canonicalization, grouped Component meaning or whole-tree
convergence. Ordered-map proofs require the standard lawful-key comparison
premise. Runtime domain uniqueness and complete native/Node semantic composition
remain separate obligations. The source/configuration Journal connection is
checked above. Histories and save-authority proof values erase; runtime storage
retains current records, Journal handles and the stamp needed for admission.

## Guarantees and review points

| Guarantee | Executable contract |
| --- | --- |
| A plan cannot silently move to another runtime, activation or recipe version | `configuration_runtime::{configuration_target, configuration_target_is_current, replace_configuration}` checks domain, component ID, generation and revision against the actual native owner. A successful replacement invalidates the old target. |
| Pending is not success; successful actions form the original ordered prefix | `configuration_batch::Batch::poll_apply` records the exact stored key, callback payload before/after and actual result. A failure closes forward execution. |
| Cancellation retains both forward and inverse work | `configuration_future::Reversible` owns the real Future values; a caller borrows them for polling. A completed forward Future is never polled again. |
| An inverse cannot start before its forward operation lands | `Reversible::poll_rollback` waits for the stored forward result before calling `prepare_inverse`; its result contract connects the actual stored factory/Future to the returned outcome. Forward failure still requires rollback of partial work. |
| Recovery cannot lose a failed inverse or skip to an earlier action | `Batch::poll_rollback` discards only unstarted plans, selects the last started action, and removes it only on actual inverse success. Pending/error retains the plan and its changed payload. |
| Accepted state and revision do not change while work is pending | `Configuration::{work, poll_update, poll_rollback}` frame the accepted snapshot and revision. `commit` requires the completed batch; `recover` requires an empty recovery stack and does not increment revision. |

The `Success` and `Landing` evidence is ghost data. The runtime stores the plans,
Futures and small counters that drive execution; it does not accumulate an
unbounded runtime proof log. The transaction does not expose a mutable batch or a
public “acknowledge success” operation.

Recovery intentionally uses the captured inverse even when its forward target
is no longer current. Resolving a new instance and applying an old inverse to it
would be wrong. A plugin must capture the resources it changed, undo partial
application, and make failed rollback safe to retry. Planning must remain free
of external mutations. These effect laws are separate from the verified ownership
and sequencing protocol.

## Remaining R2 boundaries

The [package 3 interpretation](r2-configuration-semantics.md) now checks module/scope
binding, recursive schema/default normalization, three-way merge, complete keyed
ordering and full source round trips. `Prepared::entry` complements the older
resolved-leaf projection; native groups execute a verified empty program with
structurally managed children.

- Package 4 still has to compose these exact typed observations with the complete
  native/Node production-step interpretation; package 5 provides combined R2
  acceptance. R2 remains `in_progress`.
- JSON/URL/IEEE codecs, external filesystem identity and I/O, service-key
  translation, arbitrary factory bodies and JavaScript schema callbacks remain
  explicit audited or foreign-system boundaries. The native schema and merge
  algorithms themselves are checked executable code.
- Captured targets authenticate the driver's unique domains, not independently
  constructed runtimes that deliberately reuse a domain. Actual recipe revisions
  and allocation/parent checks retain their existing contracts.
- Snapshot/recovery payloads contain the real immutable normalized recipes, but
  arbitrary factory effects and callback inverses do not acquire Component laws
  through configuration validation. Polling/panic truth and eventual callback
  return remain separate.
- Complete production-step refinement, general recovery, global termination and
  confluence are not established by a successful plan, source round trip or
  per-file save acknowledgement.

## Validation

The preceding ownership and joint-observation source checkpoint passed **86 scoped Verus checks,
77 Rust regressions (26 kernel and 51 Loader/persistence/service cases), 2 doctests
and 8 strict negative controls**, plus formatting and strict workspace Clippy
across all targets. The proof selects the native configuration composition,
native history, source history, configuration history and Recorded wrapper.
It does not rerun the whole Journal or every earlier configuration proof.

One new runtime case changes actual lifecycle state inside a configuration
callback and captures Pending, failed and recovered states with retained source
checkpoints. The production Loader failure/retry case also observes the joint
snapshot, restarts the retained runtime and awaits a saved `settle()` future.
The paired doctests exercise ordinary operations and reject replacing the
runtime through the view. This Rust ownership check is separate from the Verus
negative controls, whose mutants must compile.

The two new strict controls reject constructing a configuration in an unrelated
Journal and omitting native-member authentication from the shared snapshot.
Six existing source/save controls also passed at that checkpoint. Every case requires
its matching positive, whole-mutant compilation and exact named contract/anchor
rejection. All **295 canonical anchors** passed preflight. This is not full
negative regression, calibration, development or R2 acceptance. These counts
are historical for the later Node-path batch; see [current scope](r2-execution.md#current-closure-status).

```bash
source scripts/toolchain-env.sh
./scripts/verify.sh --verify-module lifecycle_state::native::runtime::configuration \
  --verify-module lifecycle_state::native::runtime::history \
  --verify-module configuration_source_history --verify-module configuration_history \
  --verify-module configuration_recorded --num-threads 2 --triggers-mode silent
CARGO_INCREMENTAL=0 cargo test --offline -p cordis-kernel \
  --test native_runtime --test configuration_recorded
CARGO_INCREMENTAL=0 cargo test --offline -p cordis-verus \
  --test loader --test loader_update --test persistence --test service_configuration
CARGO_INCREMENTAL=0 cargo test --offline -p cordis-verus --doc runtime::access
```

### Historical source/configuration composition evidence

The preceding source/configuration composition passed **244 scoped Verus checks,
60 Rust regressions (9 kernel and 51 actual Loader/persistence cases), and
6 strict negative controls**, plus formatting and strict workspace Clippy across
all targets. The proof covers the configuration, source, save and batch owners,
their typed histories and the entire shared Journal module, including its
existing native, recipe, value, work, cleanup, host and control projections.

The two new controls reject loading during pending recovery and wiring sources
to an unrelated Journal. Four existing controls reject unprocessed checkpoints,
discarded sync retries, stale reviews and loss of the original review during I/O.
Each has a matching current-source positive, whole-mutant compilation and exact
named function/diagnostic/source-anchor rejection. All **293 canonical anchors**
passed preflight. This is not full negative regression or calibration.

```bash
source scripts/toolchain-env.sh
./scripts/verify.sh --verify-module configuration_recorded \
  --verify-module configuration_source_history --verify-module configuration_history \
  --verify-module configuration_transaction --verify-module configuration_batch \
  --verify-module configuration_save --verify-module reversible_value::joint \
  --num-threads 2 --triggers-mode silent
CARGO_INCREMENTAL=0 cargo test --offline -p cordis-kernel \
  --test configuration --test configuration_save --test configuration_recorded
CARGO_INCREMENTAL=0 cargo test --offline -p cordis-verus --lib persistence::tests
CARGO_INCREMENTAL=0 cargo test --offline -p cordis-verus \
  --test loader --test loader_update --test persistence
CARGO_INCREMENTAL=0 cargo clippy --offline --workspace --all-targets -- -D warnings
```

The two new [composition cases](../crates/cordis-kernel/tests/configuration_recorded.rs)
and existing regressions cover the scoped behavior described above. Broader
value-write/Future-drop scenarios, complete Component interpretation and full R2
acceptance remain open. Whole-kernel proof, full development, full negative
regression, Node regressions and release/platform acceptance were not run for
this batch. The following counts describe earlier sources.

### Historical configuration-Journal evidence

The preceding configuration-Journal batch passed 171 scoped Verus checks,
56 existing Rust regressions, formatting and strict workspace Clippy for all
targets. Its 291 canonical anchors passed preflight; no mutants were executed
in that batch. Its source/phase composition is extended by the current evidence
above; it does not serve as a fresh pass for the changed source.

### Historical source-checkpoint evidence

The preceding source-checkpoint batch passed **68 scoped Verus checks, 55 Rust regressions
(4 kernel, 51 actual host-path cases), and 4 strict negative controls**, plus
formatting and strict workspace Clippy for all targets. The mutations advance an
unprocessed checkpoint, drop pending sync, bypass the stored review guard or
discard a review during I/O. Each has a fresh matching positive, complete mutant
compilation and an exact named contract rejection. All 291 canonical mutation
anchors passed preflight; this is not full negative regression or calibration.

Reproduce the selected positive and runtime scope with the pinned toolchain:

```bash
source scripts/toolchain-env.sh
./scripts/verify.sh --verify-module configuration_save \
  --verify-only-module configuration_transaction --num-threads 2 --triggers-mode silent
CARGO_INCREMENTAL=0 cargo test --offline -p cordis-kernel --test configuration_save
CARGO_INCREMENTAL=0 cargo test --offline -p cordis-verus --lib persistence::tests
CARGO_INCREMENTAL=0 cargo test --offline -p cordis-verus \
  --test persistence --test loader --test loader_update
CARGO_INCREMENTAL=0 cargo clippy --offline --workspace --all-targets -- -D warnings
```

Whole-kernel proof, full development, full negatives and release/platform
acceptance were not run for this batch. R2's remaining semantic obligations are
listed above; these counts do not measure paper-wide completion.

### Historical recipe-history evidence

The earlier recipe-history source passed **282 scoped Verus checks, zero errors**, **128 Rust
regressions** (57 kernel and 71 actual host-path cases), and strict workspace
Clippy across all targets and features. Two affected existing strict mutants—
substituting the registered body and confirming a failed result—passed fresh
matching positive checks, whole-mutant compilation and exact contract rejection.
All 282 canonical negative anchors passed preflight; this is not full negative
regression or scoped calibration.

This section records the historical recipe-history batch and is linked from
[R2 execution progress](r2-execution.md). Counts for preceding batches above
remain historical evidence. Existing cases exercise the actual
Loader, configuration and persistence paths, including update cancellation and
recovery. New expansion/planning integration cases remain on the checklists above.

Use the pinned local toolchain to reproduce this recipe/native/Child/Journal/root
and configuration-adoption proof with its runtime regressions:

```bash
source scripts/toolchain-env.sh
./scripts/verify.sh \
  --verify-module lifecycle_state::native --verify-module reversible_value::joint \
  --verify-only-module lifecycle_state::registration::shared_child \
  --verify-only-module reversible_value::function \
  --verify-only-module reversible_value::service_function \
  --verify-module configuration_runtime --num-threads 2 --triggers-mode silent
CARGO_INCREMENTAL=0 cargo clippy --workspace --all-targets --all-features --offline -- -D warnings
CARGO_INCREMENTAL=0 cargo test --offline -p cordis-kernel \
  --test native_host --test native_runtime --test shared_child \
  --test registered_value_function --test configuration
CARGO_INCREMENTAL=0 cargo test --offline -p cordis-verus --all-features \
  --test loader --test loader_update --test service_configuration --test persistence \
  --test reversible_runtime
```

These commands select the changed native, recipe-history, common Journal,
registered-root and configuration-adoption contracts. They do not rerun all
configuration planning/expansion/save proofs, replace the complete development
recorder or establish R2 semantic acceptance.

Existing strict negative-control candidates cover structural phase gates,
path-cache validation, update/recovery gates, forward landing and target identity.
Each requires its own matching positive, successful whole-mutant compilation and
the named contract rejection. Resource limits and frontend failures are not
accepted evidence. This batch reran only the two affected candidates described
above; the remaining controls received anchor preflight only. New recipe-history
and planning/expansion candidates remain deferred.

Whole-kernel development checks, R2 semantic acceptance, complete negative
regression/calibration, Node runtime and release/platform checks remain separate.
