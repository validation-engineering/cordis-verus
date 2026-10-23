# Native operation contracts

[中文](native-operation-contracts.zh-CN.md) · [Remaining obligations](paper-mapping-inventory.md) · [Controlled effects](r3-controlled-effects.md)

The current [closed-data Session](r01-prewrite-replay.md) supports mixed scalar/typed calls, actual cleanup/resume, dynamic slots and closed reference values. The [provider/consumer/Child update delivery](cases/update-recovery.md) is a separate bounded result; R01 and the full resource boundary remain open. The batch sections below document earlier, narrower interfaces and must not be read as limitations of the newer Session.

[Guarded replay](r01-prewrite-replay.md) now includes `batch::run_exclusive`: a scalar batch that holds actual cell/slot locks, checks source inputs and allocation mappings before writing, and derives matching results through the original root interpreter. Typed primitive cursors and dynamic-selection certificates remain separate. This closes a scalar execution connection, not R01 or the complete resource boundary.

The separate `batch::run_exclusive_typed` entry now holds real typed allocations
throughout its target call sequence. It checks source continuity, initial inverse
debt, zero target revisions and actual episode-selected allocation routes. A
pre-invocation reserve check supplies enough revision space for the complete
stored function, including unvisited branches. The **same original interpreter**
then derives successful typed writes after admission and records the actual
value/head/depth/revision intervals. Source versions are never installed in the
target. Inverses enter the original queue and ordinary cleanup restores them
after the guards are released. Typed inverse capture retains its allocation
identity at the write, so collecting replay inputs cannot reacquire a held lock.

The typed batch also composes **source/target correspondence across whole calls**.
Before each invocation, `Tracker::prepare` checks its retained source inputs
against authenticated historical checkpoints, without `T: Eq` or live source
rereads. The original interpreter's reports then establish matching program
positions, payload identities and depths, and extend an injective head map for
each shared allocation. `Batch::typed_replay_matches` exports the relation and
the map's continuity between calls. `Certificate::inverse` connects corresponding
strict inverse domains for arbitrary related semantic states. Maps and
certificates erase; actual checkpoints and cleanup owners remain real.

This entry covers forward typed call sequences under held guards. Mixed
scalar/typed protected functions, restoration inside the sequence and resumed
protected execution still need composition. Historical restoration remains
supported by the separate primitive cursor. The scalar and typed batch entries
retain separate supported domains.


This audit connects the native operation families to their actual entry points,
state observations and recovery responsibilities. It supports S01/S02/P01/P03,
R01/R08 and G02 in the fixed inventory. It does not close those units or change
the original paper ledger. Node protocol recovery remains R07.

## State and observations

Use the existing `finite-strict-context/v1` interpretation from
[R1](r1-semantics.md). An allocation address is the actual Journal instance and
its allocation key. A service port is a lookup name; several ports may select
the same allocation. Rebinding a port does not redirect an already captured
target. Independent Journals do not acquire a common order from numeric labels.

The scalar observation is `(value, inverse depth)`. Typed payload observation
retains the `Arc<T>` identity, semantic head and inverse depth; revision is a
separate anti-stale value that can increase on restoration. Arbitrary mutation
inside `T` is not covered by equality of the retained `Arc<T>`.

Lifecycle state includes registry membership, parentage, committed provider
identities, current targets, Episode/work owners, publications, pending actions,
cleanup slots, issued tickets and failure/restart flags. Admission can depend on
these fields even when the visible service table is unchanged. S02 must preserve
the distinction between admission and recovery observations established in R1.

## Actual access and recovery paths

Each row groups the public operation with its shared implementation. A successful
local contract is evidence for that operation; composition across all rows is
still required. Ghost source histories and receipts erase from ordinary Rust.

| Operation family and actual code | Reads and writes | Domain and recovery responsibility |
| --- | --- | --- |
| [Allocation and snapshots](../crates/cordis-kernel/src/reversible_value.rs): `new_in`, `snapshot`; [typed allocation](../crates/cordis-kernel/src/reversible_value/payload.rs): `new_in`, `capture` | Allocate an object record in the actual Journal; snapshots read the object and its corresponding history under its lock. | Fresh scalar depth is zero. A snapshot describes its acquisition point, not a frozen future value. `new_in_following` also returns an authentic birth receipt after an earlier checkpoint. |
| [Scalar operations](../crates/cordis-kernel/src/reversible_value.rs): `apply`, `apply_pending_following` | Read and update the selected object's value/depth; issue the actual inverse and Journal entry. | Arithmetic and depth capacity are checked. The inverse is defined on the captured after-state. A raw inverse holder is responsible for restoring or registering that inverse. |
| [Controlled managed scalar](../crates/cordis-kernel/src/reversible_value/controlled.rs): `apply_controlled_effect`; [native selection](../crates/cordis-kernel/src/reversible_value/native_effect.rs): `apply_native_controlled` | Check declared selection and execution owner; execute the data instruction under the value lock; register its inverse in that owner's cleanup queue. | Closed acquisition rejects before a write. Other failures follow the actual primitive domain. A successful call cannot return with its inverse assigned to an invented target or queue. |
| [Extensible computation](../crates/cordis-kernel/src/reversible_value/effect.rs): `prepare_effect`, `commit_calculation`; [native landing](../crates/cordis-kernel/src/reversible_value/native_effect.rs): `apply_native_effect` | Observe a retained object, run `ScalarEffect::compute`, then recheck and commit the captured input. | The return-value law and interference rejection are established. The trait does not prohibit extra shared writes inside `compute`; this path is rejected by the controlled replay gate. |
| [Typed replacement and inverse](../crates/cordis-kernel/src/reversible_value/payload/restoration.rs): `apply_captured_following`, `restore_following`; [native capture](../crates/cordis-kernel/src/reversible_value/native_payload.rs): `capture_native_payload`, `land` | Retain the selected payload owner; check actual liveness/version/stack state; replace the retained value and record the real inverse. | Stale capture, retirement and capacity checks remain explicit. Restoration preserves the required semantic state while anti-stale revision can advance. `T` interiors and destructors need their own boundary contracts. |
| [Slot replacement and aliases](../crates/cordis-kernel/src/reversible_value/slot.rs): `capture`, `replace`, `capture_binding` | Change a versioned slot's current object reference; retained captures keep their previous object. | [Alias projection](../crates/cordis-kernel/src/reversible_value/alias.rs) updates all names selecting an allocation. Literal single-port semantics requires its explicit single-binding condition. Different port names alone do not prove independence. |
| [Publication](../crates/cordis-kernel/src/publication.rs) and [withdrawal](../crates/cordis-kernel/src/publication/cleanup.rs) | Change the owning Episode's service publication and cleanup obligations; consumers retain committed providers. | Publication, withdrawal, consumer retention and actual payload ownership must be composed. A publication being absent does not establish that all external resources are released. |
| [Root interpretation](../crates/cordis-kernel/src/reversible_value/managed/root.rs): `run_managed_root`; [function execution](../crates/cordis-kernel/src/reversible_value/managed.rs): `run_function` | Resolve every declared port before the first effect; execute actual arguments, outcome-selected branches and successful-prefix inverse registration. | The finite stored body and branch indices are checked. Controlled admission examines even unvisited callback branches. Completing this path does not classify arbitrary callback effects as stuttering. |
| [Child ownership](../crates/cordis-kernel/src/lifecycle_state/registration/shared_child.rs) and [native registry](../crates/cordis-kernel/src/lifecycle_state/native/runtime.rs): `register_shared_child`, `retire_shared_child` | Modify birth/parent/registry records and the actual parent-owned cleanup obligation. | Registry admission has guards beyond the service table. Retirement, child terminal completion and registry removal are distinct. R04 still composes these with consumer and repeated-Episode recovery. |
| [Cleanup and retries](../crates/cordis-kernel/src/cleanup_groups.rs): `dispatch`, `complete`, `retry`; [native cleanup](../crates/cordis-kernel/src/lifecycle_state/native/runtime.rs): `begin_cleanup`, `retry_managed_execution` | Issue a real action, retain blocked inverses, classify failures and match the current ticket before advancing. | Retryable failure retains the action; consumed `FnOnce` failure has a different contract. A successful host acknowledgement is a protocol fact, not a proof of arbitrary external restoration. |
| [Async landing](../crates/cordis-kernel/src/cleanup_queue/landing.rs) and [poll/restart control](../crates/cordis-kernel/src/poll_control.rs) | Record actual owner, pending result, failure and restart state; accept or divert a result according to the current state. | Stale owner/ticket checks are safety conditions. Eventual Future completion and host scheduling are separate G04 conditions. |
| [Configuration execution](../crates/cordis-kernel/src/lifecycle_state/native/runtime/configuration.rs) and [ordinary host adapters](../crates/cordis/src/runtime.rs) | Connect configuration/source records and real host calls to the checked kernel. | R2's production mapping is reused. File persistence, arbitrary factories and external effects retain explicit contracts; C01 still proves applicable final-configuration equivalence. |

## Implemented identity connection

The production path is:

```text
batch::run / batch::run_controlled
  -> Bank::bind(authentic Input)
  -> Input::seed_following(previous allocation receipt)
  -> scalar or typed new_in_following
  -> Journal::allocate_following (the original allocator and lock)
  -> Bank retains the real seed and publishes its actual slot
  -> original registered root interpreter
```

`Bank::wf` now establishes both source uniqueness and target uniqueness. Its
frontier is an erased authentic Journal receipt; every previous target key is
present at that checkpoint. The next allocation extends that real prefix and
must use a new key. Other Journal users may allocate or update in between: keys
remain allocated, so freshness still follows without assuming a quiet interval.

`Bank::mapping_entry` and `mapping_injective` derive the map from the actual bank.
`aliases` proves both directions: equal source allocations share a target, and
different source allocations stay distinct. Numeric identity exhaustion does
not turn an unknown source into an alias; the existing `Unnamed` error remains.
No additional runtime identity scan, expected allocation number or target state
is supplied to establish these properties.

The map applies to scalar and typed allocation identities. It does not claim
that a typed payload's interior is a fresh deep copy: the seed retains the actual
source `Arc<T>`, and that distinction remains visible.

## Strict scalar transport and the recovery equation

[The heap transport proof](../crates/cordis-kernel/src/reversible_value/managed/replay/bank/heap.rs)
uses this injective map to relate source and target scalar heaps. The relation
includes missing entries and the complete `(value, depth)` observation.
`Bank::scalar_contract` then proves the same forward definedness, result-selected
branch and corresponding updated state for the retained data instruction.
The two captured inverse maps also have matching domains on every pair of
related recovery inputs, and preserve the relation whenever restoration succeeds.

`Source::captured_scalar_contract` applies that law to the instruction, branch,
address and result retained from a real successful source step. It derives the
corresponding target primitive's definedness, output and continuation from the
source report and the stated input relation. It does not take replacement code
or an expected target result from its caller, and it does not yet prove that an
entire target invocation reaches this related input.

`Bank::scalar_independence` additionally derives target allocation separation
from source separation, then applies the existing full forward/inverse iterator
independence theorem. It does not certify two effects on the same object merely
because their arithmetic results sometimes commute.

These are local connections needed by R08 and G02. **The state relation at each
later call remains a precondition of the transport theorem.** R01 must derive it
from the real execution, resource access and previous results. Source-frozen
maps in Equation (55), re-executed target functions and legal Episode deletion
remain separate obligations; these lemmas do not equate them automatically.

## Checked source continuity and actual scalar observations

[`continuity::check`](../crates/cordis-kernel/src/reversible_value/managed/replay/continuity.rs)
checks the successful steps retained from actual inverse owners, in the supplied
call order. The batch obtains that order from the existing authenticated source
planner. For every repeated allocation, the next captured input must equal the
previous captured output. Scalar comparison includes inverse depth. Typed
comparison derives value/head/depth equality from the persistent histories; it
does not call `T::eq`, cast pointers or reread live source objects. A mismatch
identifies the two source call/step locations.

`Checked::recovery` derives definedness and roundtrip recovery of this finite
source word from the checked observations. It no longer takes composing inputs
or inverse success as caller premises. The initial map contains each object's
first captured input; it is not asserted to be one simultaneous global snapshot.
The check detects state discontinuity, not every omitted event: intervening
operations which return to the same complete observation need the separate
complete-history census.

[`batch::run_checked_scalar`](../crates/cordis-kernel/src/reversible_value/managed/replay/batch.rs)
connects this source check to actual scalar target execution:

1. Inspect the complete retained functions, including unvisited branches. This
   entry accepts successful source calls whose instructions are all `Kernel`.
   Source-order and continuity errors return before target registration.
2. Use the same provider construction, registration, Begin, root interpreter and
   Finish implementation as the existing batch. No alternative interpreter or
   expected target result is supplied.
3. Before Finish and the next call, compare inputs captured from the target's
   **actual retained inverses** with the source inputs. `check_scalar_observations`
   checks instruction positions and value/depth. Its proof derives matching
   outputs, selected branches and strict inverse states from those observations
   and the retained function. `scalar_inverse` exposes the full inverse-state
   equality without transferring either owner's inverse permission.

The entry returns `Result<CheckedScalarBatch<_, _>, PreflightError>`. On `Ok`,
inspect `result.batch.failure`: target admission or execution can still fail.
`Failure::Observation` identifies a completed invocation whose observations do
not match. Its original report, owner and already queued inverses remain in
`batch.calls`; no later call is started. **This is a check after invocation, not
an atomic guard before every write or automatic rollback.** A failure can have
real effects requiring the ordinary cleanup/retry protocol.

On a return with no batch failure, actual scalar input correspondence is an
established postcondition, not a premise supplied by the caller. This still does
not prove that every accepted source must replay successfully. The selection
check below additionally establishes the bank map for accepted scalar calls. Typed target version
transport, dynamic bindings, full lifecycle scheduling and Equation (55) remain
open. `run` and the mixed scalar/typed `run_controlled` retain their existing
profiles; the stronger scalar entry is opt-in.

Replay capture now retains each scalar inverse's actual after-state and each
target call's actual operands. Ordinary managed execution does not collect this
replay list. The source check borrows a temporary list of observations, using
linear extra space and a backward same-allocation search (quadratic worst-case
time). Histories and proof certificates erase; executable operands remain owned
by the explicit replay captures.

## Actual provider and allocation selection

[`check_scalar_replay`](../crates/cordis-kernel/src/reversible_value/managed/replay/selection.rs)
adds allocation correspondence to the state check. `run_checked_scalar` invokes
it on each actual report before Finish. The evidence follows the production path:

1. `Bank::find` locates the captured source allocation in the existing bank.
2. Actual provider Finish publishes the bank's slot. The service, host and
   recorded-owner contracts preserve existing publication entries through later
   Finish calls; `preserve_providers` composes this fact for the batch.
3. `Source::instantiate` binds the original interpreter's Begin capture to that
   actual publication table. The report's service binding identifies the
   Episode-committed provider and the slot revision used by the call.
4. The checker compares that provider with the prepared provider and requires
   captured revision zero. `Capture::initial_selection` then proves that the
   actual selected allocation is the bank seed, including its Journal identity.

This uses publication ownership and immutable capture evidence, without
assuming that equal allocation numbers from arbitrary namespaces identify the
same object. Existing source-namespace conditions on source ordering and bank
lookup remain explicit. A replacement in another Journal is also rejected by
the slot-version check. No live target object or current slot is reread.
The standalone helper requires certified provider-capture correspondence; the
production batch derives that premise from the real publication and Begin calls.

For a return with no batch failure, `scalar_replay_matches` proves the actual
source-to-target allocation mapping together with matching scalar inputs,
outputs and branches. `mapped_inverse` includes the actual strict inverse state;
`Batch::scalar_aliases` proves both directions of alias preservation across
actual calls. These guarantees refer to the recorded execution, so replacing a
slot *after* an invocation does not change its retained selection.

`Failure::Selection` reports a missing bank/provider binding, a different
committed provider or a nonzero captured slot revision. State/control-flow
mismatches retain `Failure::Observation`. Both preserve the actual report and
cleanup owner and stop subsequent calls. The check remains **after invocation**:
the rejected call can already have changed a resource.

This profile conservatively rejects every nonzero slot revision, even a swap
back to the original allocation. Supporting dynamic rebinding requires its own
transport contract; it is not silently treated as static replay. Per-step lookup
scans the bank and provider list. All new publication/capture proof metadata
erases, and ordinary `run`/`run_controlled` do not perform the new checks.

Regression tests exercise same-value/depth replacements in the same and a foreign
Journal, retained cleanup of the rejected call, and a slot replacement after a
successful invocation. In a temporary-copy mutation experiment, removing the
nonzero-revision guard is rejected at `Capture::initial_selection` because its
revision-zero precondition cannot be proved. This is scoped evidence; the full
negative-control suite and whole-project acceptance were not run for this batch.

## What remains and how to validate it

- P01: enforce the complete resource access boundary. Existing raw shared
  handles, callbacks, mutable payload interiors and external I/O still need
  classified contracts or prevention of untracked effects.
- R01: derive cross-call state correspondence, typed head/revision transport,
  and dynamic binding changes from actual execution. Identity injectivity alone
  does not discharge these obligations.
- R02/R08: compose the complete target lifecycle and exact recovery equation.
- S01/S02: propagate the chosen context/domain interpretation and all required
  revisions through the final theorems. This operation audit is an implementation
  review input, not a proof of the original unrestricted context.

Scoped validation must include the changed allocation modules, the bank and heap
modules, and the existing managed replay tests. Later integrated negative controls
must reject reuse of a previous target allocation, loss of the source alias
relation, and omission of inverse depth from the recovery domain. Keep solver
timeouts and compile failures distinct from a valid negative-control rejection.
Whole-kernel development and paper-wide acceptance remain separately recorded.

Reproduce the focused checks with the pinned local toolchain:

```sh
source scripts/toolchain-env.sh
"$VERUS" crates/cordis-kernel/src/lib.rs \
  --crate-name cordis_kernel --crate-type=lib --edition=2021 --no-cheating \
  --verify-only-module execution \
  --verify-only-module lifecycle_state::services \
  --verify-only-module lifecycle_state::native \
  --verify-only-module lifecycle_state::native::managed \
  --verify-only-module lifecycle_state::native::runtime \
  --verify-only-module reversible_value::slot \
  --verify-only-module reversible_value::managed::interleaving::history::lifecycle::native \
  --verify-only-module reversible_value::managed::interleaving::history::lifecycle::host \
  --verify-only-module reversible_value::managed::replay \
  --verify-only-module reversible_value::managed::replay::inputs \
  --verify-only-module reversible_value::managed::replay::inputs::payload_history \
  --verify-only-module reversible_value::managed::replay::continuity \
  --verify-only-module reversible_value::managed::replay::observation \
  --verify-only-module reversible_value::managed::replay::selection \
  --verify-only-module reversible_value::managed::replay::order \
  --verify-only-module reversible_value::managed::replay::scalar \
  --verify-only-module reversible_value::managed::replay::transport \
  --verify-only-module reversible_value::managed::replay::bank \
  --verify-only-module reversible_value::managed::replay::bank::heap \
  --verify-only-module reversible_value::managed::replay::batch \
  --num-threads 2 --triggers-mode silent
cargo test -p cordis-kernel --test managed_replay --test native_runtime \
  --test managed_function --locked --offline
python3 -B scripts/check-paper-mapping.py
```
