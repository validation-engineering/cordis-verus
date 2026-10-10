# Paper progress claims and executable contracts

English · [简体中文](progress-contracts.zh-CN.md)

The project's goal is a reviewable connection from paper constraints to running
code. For progress, that connection needs both directions: an accepted call must
implement a permitted transition, and an enabled transition must have an
implementation that accepts it. Within each contract's stated implementation
domain, this review connects admission, concrete iteration, dynamic child
registration, synchronous Mixed/Fresh steps, cross-call admitted landing and
finite executable runners to checked contracts. Kernel iteration, episode
admission and ordinary host coherence now use the same binding-identity semantics, without an
extra private-vector order/multiplicity guard.

The source is the pinned [paper, arXiv:2608.25512v1](https://arxiv.org/abs/2608.25512v1).
The [obligation ledger](paper-obligations.json) remains authoritative. Theorem 73
is still **partial**; these contracts do not establish paper-wide progress.

## What the paper actually asks for

| Paper item | Obligation | Corresponding code and remaining scope |
| --- | --- | --- |
| Definitions 53–54 and Table 1 | Target/committed identities determine whether loading, iteration or guarded unloading may proceed. | `semantics.rs` and `refinement.rs` describe these guards. The executable `Kernel` and `StageProtocol` contracts below connect selected guards to actual calls. |
| Theorem 73(1) | A nonquiet state has an applicable lifecycle rule under the theorem's hypotheses. | `draining_can_progress` proves the existence of an enabled cleanup in its all-Unloading profile. The new `begin_cleanup` success equivalence makes that guard sufficient for the real kernel call. Kernel iteration/finish now accept exactly under the paper Loading/coherent guard. Verified drivers connect captured bindings to this guard; complete host capture and general continuation domains remain separate obligations. |
| Theorem 73(2) | Bound per-fiber steps and target changes, then conclude that maximal lifecycle sequences end quietly. | `termination.rs` contains finite-trace bounds and a construction of a quiet execution under its fixed-registry, footprint, provision and continuation-rank premises. The actual `ProgramEpisode` runner derives finite execution from checked forward instructions. `FreshDriver::run_until_blocked` now bounds repeated real steps of one actor, including child registration, until terminal publication or the first checked error. This is not the full dynamic-registry theorem. |
| Corollary 69 | After terminal Unload, tables agree with the foreign-step replay modulo observation, and the owner table is empty. | `ProgramEpisode::execute_and_recover` restores supplied cells for its fixed program profile. Mixed/Fresh `unload` now accepts exactly when cleanup is permitted and its current LIFO inverse sequence is defined. Actual-history coverage now also proves that successful Unload empties the owner table under `owner_table_recovery`. Matching terminal Mixed script reports also establish the foreign-only value equation below. Fresh replay composition and arbitrary external resources remain separate. |
| Theorem 71(2) | An episode diverted during loading closes. | The ledger records a counterexample to the unconditional claim about the sequences allowed by the paper. Proving an eventual closure under additional scheduling assumptions would be a corrected, conditional claim. |
| Definition 74 / Theorem 80 | Describe support and establish canonical form/confluence. | Support is a state equation; confluence also needs representation, transport and commutation proofs. A temporal library does not supply those missing connections. |

Theorem 73 assumes acyclic precedence, bounded component lengths, finitely many
names over the sequence, and lifecycle-only steps. Its conclusion concerns
**maximal** lifecycle sequences. It does not explicitly assume a fair Node
scheduler. A finite prefix that stops while a rule is enabled is not maximal.
An infinite host execution that repeatedly does unrelated work is a different
object from the paper's lifecycle-only sequence. Adding weak fairness without
explaining this change would change the claim being checked.

## The strengthened calls

Calls on an existing machine require its `wf()` invariant; `run_from_empty`
constructs that machine itself and has no input-state premise. `old` means the
state before the call. Read the complete source contracts, including frames and
error behavior, rather than treating these summaries as independent axioms.

| Actual call | Checked acceptance condition | Paper connection |
| --- | --- | --- |
| [`Kernel::check_insert` / `insert`](../crates/cordis-kernel/src/lib.rs) | Success iff `insert_enabled(parent, dependencies, provisions)`: identity capacity, a registered parent when supplied, distinct declarations and unreserved provision ports. | The actual O-Insert registration domain, with representation bounds stated separately from the paper predicate. |
| [`Kernel::begin`](../crates/cordis-kernel/src/lib.rs) | `result.is_ok() == old.begin_enabled(id)`: Inactive, target available, generation present and below `u64::MAX`. Success increments the generation and commits the actual target. | Executable admission for L-Begin, with the implementation's bounded generation counter retained explicitly. The counter is erased by the paper projection. |
| [`Kernel::begin_cleanup`](../crates/cordis-kernel/src/lib.rs) | `result.is_ok() == old.cleanup_enabled(id)`: registered, Unloading, not already restoring, and no live committed dependent. | The executable start of guarded L-Unload. It preserves the paper state while enabling restoration; `finish_cleanup` performs the projected Unload. |
| [`MixedDriver::unload`](../crates/cordis-kernel/src/mixed_driver.rs), [`FreshDriver::unload`](../crates/cordis-kernel/src/fresh_driver.rs) | Success iff `unload_enabled`: Kernel cleanup permission **and** `restore_receipts(journal(actor), primitive_state).is_some()`. For the complete concrete Unit/Child/Provision/Xor journal, `journal_recovery` derived from actual histories discharges the inverse condition. | Executes the actual finite LIFO restoration for L-Unload. The recovery fact is derived from represented histories, not arbitrary `wf()`. Public errors preserve the complete machine; internal draft errors need not. |
| [`Kernel::check_iteration` / `finish`](../crates/cordis-kernel/src/lib.rs) | Success iff Loading and `coherent(id)`. `paper_coherence` and `paper_iteration_guard` prove that this is exactly the projected paper guard. | L-Iter admission and the control transition L-Finish. Provider identity is checked through existing uniqueness, typing and coverage invariants, independent of buffer order or duplicates. |
| [`StageProtocol::admit`](../crates/cordis-kernel/src/episode.rs) | `accepted == (old.pending || (!old.settled && !old.cancelled && matching_target))`. `matching_target` means a present target with the same complete binding-identity set. An already admitted stage stays admitted across cancellation or target loss. The final settled/cancellation flags are specified exactly. | Admission and retention of an outstanding iteration. `land`/`end` supply the token-level accumulator transitions for Iter/Finish or late Divert. Explicit host cancellation is an extension, not evidence that the paper target changed. |
| [`ChildEpisode::check_child` / `land_child`](../crates/cordis-kernel/src/ownership.rs), [`ChildDriver` wrappers](../crates/cordis-kernel/src/child_driver.rs) | Success iff `land_enabled`: pending, current captured identity/generation, and the current insertion domain. | Conditional Definition 52 registration and capture of the actual child inverse. Admission alone does not guarantee insertion. |
| [`MixedDriver::insert`](../crates/cordis-kernel/src/mixed_driver.rs) | Success iff `insertion_enabled`: a valid blueprint index, validity of the required bank prefix and the real Kernel insertion domain. | The closed interpreter's registration boundary; an unused invalid bank entry is not made valid by `wf()`. |
| [`FreshDriver::insert` / `begin` / `apply`](../crates/cordis-kernel/src/fresh_driver.rs), [`preparation_command`](../crates/cordis-kernel/src/fresh_preparation.rs) | For `Insert`, `Begin` and `Step`, success iff the current `preparation_enabled(command)`. Insert uses the full Mixed insertion domain; Begin also requires an empty retained journal and the Kernel Begin domain. | Connects the real setup dispatcher to exact local implementation domains. Other commands remain supported but are outside this domain equivalence. |
| [`MixedDriver::step`](../crates/cordis-kernel/src/mixed_driver.rs), [`FreshDriver::step`](../crates/cordis-kernel/src/fresh_driver.rs) | Success iff `step_enabled`: a registered coherent Loading actor, a current instruction, its primitive domain and, for a terminal instruction, complete publication after that instruction. | Exact local acceptance for the synchronous L-Iter/L-Finish interpreter, relevant to Lemma 57 and Theorem 73(1). It is not whole-run termination. |
| [`FreshDriver::admit` / `Admission::land`](../crates/cordis-kernel/src/admitted_fresh_driver.rs) | Admission succeeds iff `admission_enabled` (`ready`). Landing succeeds iff `land_enabled`: an unconsumed current ticket, the selected primitive's live domain and, only for a coherent terminal landing, `complete_after`. | Exact acceptance across checked intervening calls, including L-Divert after target loss. Admission does not reserve values or child provisions. |
| [`FreshDriver::run_until_blocked`](../crates/cordis-kernel/src/fresh_run.rs) | Under `wf()`, calls real `step` until terminal publication or its first error. The committed-step count is bounded by the input program-position rank. No fuel or future-success premise is required. | A finite concrete execution of one installed actor; its source refinement extends a well-formed source already represented by the input. It does not establish global quiescence. |
| [`run_from_empty`](../crates/cordis-kernel/src/fresh_bootstrap.rs) | Constructs a new machine, executes the actual setup script and runs one actor only if all setup calls succeed. Returns `SetupFailed`, `Blocked` or `Finished`. | Establishes one source execution from empty representing both the prepared and final machines, without an input source premise. Failed Insert/Begin/Step commands are disabled at the failure state; other command domains and global progress remain separate. |

A paper-enabled Begin can still be rejected when the implementation generation
counter is exhausted; this bound is not a premise printed in Theorem 73.

`ResourceEpisode::admit` and `ProgramEpisode::admit` expose the same acceptance
equivalence through their real wrappers. Their constructors establish that a
fresh episode is not cancelled; a successful restart does too. Callers can
therefore prove fresh admission without inspecting private fields.

This is stronger than a postcondition of the form “if the result is successful,
the next state is valid.” That one-way statement can allow an implementation
that rejects every request. Success equivalence rules out rejection of an
enabled request, within the function's stated preconditions.

Several adjacent methods already had adequate success conditions:
`StageProtocol::land` and `end` accept exactly when pending;
`Kernel::finish_cleanup` succeeds exactly when restoring;
`leave`/`leave_if_changed` characterize errors sufficiently for their existing
guarded paths. These were not missing contracts repaired by this change.

## From Definition 53 to actual admission

Definition 53 describes provider identities for dependency ports. The specification
projection [`binding_set`](../crates/cordis-kernel/src/episode.rs) observes complete
`(key, realm, provider)` identities and is erased from runtime code. The executable
`same_bindings` returns true exactly when
those sets are equal. Reordering or repeating an identical binding is harmless;
changing its key, realm or provider, or adding or dropping a distinct binding,
is a mismatch. `None` remains different from an available empty target.

The proof path is concrete:

1. `Kernel::target` returns a complete target or establishes unavailability;
   `Kernel::committed` relates the actual captured vector to the paper set.
2. [`Kernel::paper_captured_target`](../crates/cordis-kernel/src/lib.rs) uses
   `wf()`, a registered Loading actor and a capture equal to the paper committed
   set to prove that target/capture set equality is equivalent to paper
   coherence. This is the kernel's control projection of Definition 53,
   specialized to total Active provisions; actual host value availability is
   still checked separately.
3. [`Driver::admit`](../crates/cordis-kernel/src/driver.rs) and
   [`ProgramDriver::admit`](../crates/cordis-kernel/src/program.rs) read that real
   target and invoke their real episode. Under their maintained `wf()`, the
   result is `Ok` iff the actor is registered and Loading. Within `Ok`, the
   returned boolean is exactly `pending || (!settled && !cancelled && coherent)`.
   `Ok(false)` is a completed admission check that denies a new stage, not an
   error or an admitted stage.
4. [`ChildEpisode::admit_current`](../crates/cordis-kernel/src/ownership.rs)
   additionally checks the capture against the current commitment and episode
   generation. Its contract connects successful checks to the same admission
   formula. Equal bindings cannot revive a handle from an earlier generation;
   checked calls must continue to use the same Kernel instance.

The capture also comes from a checked Begin. `Kernel::begin` now establishes
`iteration_enabled(id)` on success; `refinement::begin_preserves_target` proves
that L-Begin preserves its newly captured target. Both verified drivers expose
fresh, noncancelled episode state and paper coherence after successful Begin.
[`Driver::begin_and_admit`](../crates/cordis-kernel/src/driver.rs) then calls the
real `begin` and `admit` in sequence. It succeeds exactly under the driver's
`begin_enabled` condition and establishes a pending first stage without requiring
the caller to assume admission succeeds. This one call has no intervening host
step and does not execute the stage's effect or establish callback termination.

`StageProtocol::can_finish`, the ordinary Rust
[`LifecycleDriver::coherent`](../crates/cordis-driver/src/shared.rs) and driver
blocker diagnostics use the same executable comparison. The native host calls
`admit` before polling a stage and `can_finish` at publication. Reusing this
verified function removes their extra vector-equality guard; it does not verify
the surrounding ordinary Rust host, locks, callback execution or episode capture.

The comparison keeps the stored vectors unchanged. Equal-length, elementwise
matching captures take an O(n) fast path; the fallback uses two bounded membership
scans, O(nm) worst-case for lengths n and m, without allocating another collection.
This is a semantic alignment, not a performance improvement claim. Inverse
journals, child accumulators and callback tokens keep their existing ordered,
LIFO behavior. The comparison alone does not validate arbitrary low-level
snapshots as legal provider maps; kernel provenance and invariants supply that
connection.

## Dynamic child registration has a checked domain

[`Kernel::check_insert`](../crates/cordis-kernel/src/lib.rs) is a read-only check
of the same `insert_enabled` predicate used by the real `insert`. Insertion
calls that check before writing any node or declaration, and succeeds exactly
when the predicate holds. The existing rejection order is preserved: identity
capacity first, unknown parent next, then provision conflicts and duplicate
dependencies. A rejected insertion preserves the kernel.

The paper connection is explicit.
[`refinement::insertion_domain`](../crates/cordis-kernel/src/refinement.rs)
describes the O-Insert parent-registration and provision-reservation premises;
`insertion_has_domain` derives them from the existing `Rule::Insert` relation.
[`Kernel::paper_insert_domain`](../crates/cordis-kernel/src/lib.rs) relates the
concrete input guard to those premises, plus the implementation's bounded
identity capacity and duplicate-free dependency/provision vectors. Ports use
both key and realm. An Inactive or retired but registered fiber still reserves
its provisions; absence of a published service value does not free that port.
Dependency availability and parent activity are not insertion prerequisites.
The new child is registered Inactive, and its later Begin checks readiness.
This registration bridge does not establish the original Component-membership
premise for an arbitrary child body.

The spec predicate
[`ChildEpisode::current_matches`](../crates/cordis-kernel/src/ownership.rs)
describes a registered Loading owner, an unbound or matching captured generation,
and equality of the captured/current committed binding sets. The spec predicate
`land_enabled` adds `pending` and `Kernel::insert_enabled` for that owner. Runtime
validation is performed by the executable `check_snapshot` and `check_child`.
Both the read-only `check_child` and
the actual `land_child` expose success iff this domain holds. The corresponding
[`ChildDriver`](../crates/cordis-kernel/src/child_driver.rs) calls expose the same
condition at the owned-driver boundary. Successful landing appends the child
identity returned by the real insertion to the real inverse journal. Current
target coherence is deliberately not an extra landing prerequisite: an already
admitted pending stage may land after retirement or target loss; the driver
then performs the existing diversion path.

[`ChildDriver::check_and_land_child`](../crates/cordis-kernel/src/child_driver.rs)
composes the real preflight and landing calls without an intervening registry
operation. Successful `check_child` establishes the domain needed to prove that
the following `land_child` succeeds; the caller does not assume its return value.
The combined call succeeds exactly under the original `land_enabled` condition
and records the actual child's inverse. This same-call result does not turn a
previous, separate preflight into a reservation.

Preflight reserves nothing: it does not admit a stage, capture a generation,
consume an identity or write an inverse. Its answer describes only the state
checked. If another registration or episode change intervenes, landing must
recheck; the actual methods already do so. The error frames are narrower than
whole-episode atomicity: `ChildEpisode::land_child` preserves the kernel,
children and stage view on error, but a detached handle may have captured its
generation before insertion fails. `ChildDriver::land_child` preserves control
and a registered actor's journal/pending state on error, while its admission
refresh may update cancellation. Read-only preflight itself changes none of these fields.

This closes the executable **registration-domain** contract, not totality of
child effects or a whole execution. The next section gives the separate exact
synchronous Mixed/Fresh step domain. Blueprint validity alone
does not ensure that a provision remains unreserved, a required value exists,
or a terminal stage has provided every declared service. The existing
[`guarded_child_domains.rs`](../crates/cordis-kernel/src/guarded_child_domains.rs)
witness still shows that equal table observations and coherent Loading actors
can have different child-allocation domains because a registered declaration
reserves a port. That counterexample, failure behavior and the original
Component/totality obligations are unchanged. No new failure transition is
introduced to obtain a progress conclusion.

## The actual Mixed/Fresh interpreter has an exact single-step domain

[`MixedDriver`](../crates/cordis-kernel/src/mixed_driver.rs) executes a closed
instruction bank against real `u64` service tables, the Kernel and a mixed
inverse journal. These same executable methods are compiled by Cargo and
checked by Verus. The predicates below describe their input state; they do not
assume that an interpreter or model run already returned success.

`ready(actor)` requires a registered Loading actor, coherence and a current
instruction. `installed_instruction` selects the installed blueprint and program
position, including the terminal Unit instruction. Within the existing `wf()`,
`primitive_enabled` gives the remaining effect domain:

| Instruction | Required state before the effect |
| --- | --- |
| Unit | No additional effect-domain restriction. |
| Provide | The actor has the declared slot and it has no value yet. |
| Xor | The committed/own-table provider resolves and that provider's actual table contains the value. |
| Child | The expected identity equals the actual next ID, the selected child blueprint and required bank prefix are valid, and the Kernel insertion domain holds. |

The real `provider` returns success iff the primitive-state resolver returns a
provider. That alone does not establish value availability: an unfilled own
provision slot can resolve but cannot supply a value to Xor. The real `execute`
succeeds iff `primitive_enabled` under its stated calling preconditions.

A terminal instruction also needs complete publication. `complete_after`
checks the input tables while accounting for this instruction's effect: a
Provide may fill the last missing slot in the same call. Requiring
`fully_provided` before executing that Provide would incorrectly reject it.
After the effect, `commit_landing` succeeds iff a continuation exists or the
actual table is fully provided and the actor remains coherent, under that
method's preconditions. `instruction_enabled` combines the primitive domain
with the terminal `complete_after` condition; `step_enabled` combines it with
`ready`. The public `MixedDriver::step` returns success **iff** this predicate
holds, rather than only proving safety conditional on success.

[`FreshDriver::selected_instruction`](../crates/cordis-kernel/src/fresh_driver.rs)
instantiates a Child template with the allocator's current `next_id` for this
call. Its `step_enabled` uses that instantiated instruction and the same effect
and terminal checks. The real `FreshDriver::step` has the same success
equivalence. Automatic freshness removes the caller's fixed expected-ID check;
it does not remove provision reservations, value availability or publication
requirements. No allocator reservation is made for a later call.

The public `step` methods execute on a draft and commit it only after all checks
succeed. An error therefore preserves the complete public machine under their
`same` relation, including allocator, tables, program position and journal.
Within `step_inner`, a successful `execute` can write values or insert a child
before a later `commit_landing` rejects publication. That internal error does
not restore the draft; the public method obtains rollback by discarding it.

This is a synchronous single-call result, relevant to Lemma 57's implementation
connection and Theorem 73(1)'s local enabledness. It does not establish the
original total recursive Component/context interpretation, a whole-run
termination bound. The cross-call admission protocol has its own exact domain
below; arbitrary callbacks and host scheduling remain separate. The strict guarded child counterexample still applies when
`primitive_enabled` is false; exact rejection describes that boundary instead
of introducing a new lifecycle failure rule.

## An admitted stage rechecks its live landing domain

The owning [`fresh::admitted::Admission`](../crates/cordis-kernel/src/admitted_fresh_driver.rs)
session captures actor, generation, blueprint, program position and instruction
template. `FreshDriver::admit` succeeds iff `admission_enabled(actor)`, which is the
inner driver's `ready(actor)` predicate. This checks coherent Loading control
and an installed position; it does not check every effect prerequisite or
reserve service values and provision ports. Admission can therefore succeed
while a subsequent landing fails for a missing value or a conflicting child
reservation, even without an intervening call.

The successful `admit` contract also states
`admitted.land_enabled() == self.step_enabled(actor)` for the input machine.
Immediately landing that fresh ticket, with no intervening operation, therefore
has exactly the same success condition as the synchronous `step`. This is an
equality of acceptance domains, not a claim that admission alone guarantees
landing: `admission_enabled` checks only the weaker `ready` condition. The
relation to that earlier input state need not survive intervening calls.

`Admission::apply` permits checked calls while the ticket is pending.
`selected_instruction` keeps the captured template and instantiates only a
Child's fresh identity from the current machine's allocator. The `bound`
predicate checks that the same actor is still registered and Loading, with the
captured generation, blueprint, position and template. It does not require the
current target to remain coherent.

The actual `land` succeeds **iff** `land_enabled` in its input state:

- The ticket is unconsumed and still `bound` to its owned machine.
- `primitive_enabled` holds for the selected instruction in that current machine.
- The target is no longer coherent, or the instruction has a continuation, or
  `complete_after` holds for the terminal instruction.

Thus a coherent terminal landing still has to complete publication, including
a last-slot Provide in this call. A landing after target loss instead records
the real inverse and diverts into Unloading, without requiring complete
publication. It must still satisfy the primitive domain: target loss does not
make a missing Xor value or a reserved child port valid. For a well-formed
registered Loading actor with an incoherent target and a matching receipt, the
real `commit_divert` is proved to succeed.
On successful `land`, `Landing.diverted` is exactly the negation of input-state
coherence; any returned child identity equals the machine's `next_id` before
that landing.

All landing errors preserve `Admission::same`, including the complete machine,
captured identity and consumed flag. A failed unused ticket therefore stays
unused and can be retried after checked calls make its domain valid. A consumed
or stale ticket remains rejected; retry does not rebind it to another episode.
An intervening registration can make an admitted action fail its landing domain;
retiring a conflicting entry still leaves its provision reserved until removal.
The existing execution branches and error order are unchanged by these stronger
contracts.

[Admission regressions](../crates/cordis-kernel/tests/admitted_fresh_driver.rs)
exercise a coherent terminal failure followed by target-loss diversion using
the same unconsumed ticket, and a child reservation conflict that persists
through retirement and succeeds only after removal. They check payloads,
journal prefixes, allocator state and single consumption. The universal
acceptance claim comes from the Verus contracts on the actual `admit` and
`land` methods, not from these examples alone.

This closes the local acceptance gap for this one-ticket, closed instruction
protocol. It does not make an arbitrary Future return, prove arbitrary callback
effects, or establish multi-step dynamic termination and paper-wide progress.
Theorem 73 and Lemma 57 retain their separate context/whole-execution obligations.

## A checked client, not a separate model

[`cancelled_admission_witness`](../crates/cordis-kernel/src/episode.rs) is an
executable Rust function checked by Verus. It creates a stage, admits a matching
target, cancels it, admits the already outstanding stage with no current target,
and calls the actual `land` or `end`. It proves that the result is cancelled,
settled and no longer pending, with exactly the supplied inverse token retained
when there is one. The early `pop` returns `None` while admission remains pending; once the
supplied result lands, the supplied token is retained.

The caller supplies the terminal result to this client. It does not run an
arbitrary Future until it returns, and a retained token is not itself a proof
that a host cleanup callback released a resource. `ResourceEpisode` separately
connects its tokens to actual journal writes and inverse operations.

The same `crates/cordis-kernel/src/` source is compiled by Cargo and checked by
Verus. The runtime calls these methods through
[`cordis-driver`](../crates/cordis-driver/src/shared.rs) and
[`runtime.rs`](../crates/cordis/src/runtime.rs). The driver has its own outstanding
action and capacity guards; the host also waits for pending setup/stages before
cleanup. Kernel acceptance alone therefore does not prove acceptance or
completion of an entire host workflow.

## Checked program domain, execution and recovery

[`ProgramEpisode::new`](../crates/cordis-kernel/src/program.rs) succeeds exactly
when `valid_program` holds. Its actual validation checks cell indices and both
possible destinations of each branch: every destination moves forward and
stays within the program or reaches its terminal position (`code.len()`). This establishes the interpreter's domain and a
finite rank from user-supplied instructions, instead of assuming every step
will succeed.

`run_to_completion` requires only the episode's internal `wf()` invariant. It
checks admission at runtime and returns `NotAdmitted` for an outstanding,
settled, cancelled or mismatched-target episode. On success it calls the real
`admit` and `step` methods until the terminal result. Its loop proves that each
call succeeds, a rank combining remaining instructions and the terminal flag
strictly decreases, and
`count.steps == count.writes + 1`, including the final `Finished` call even for
an empty program. `writes` is bounded by the initial remaining instruction
count. These counts measure interpreter calls, not the entire paper lifecycle.
A rejected run leaves resource cells, position and depth unchanged; admission
may mark a mismatched episode cancelled/settled.

`execute_and_recover` has no caller-supplied success or target-equality premise.
It succeeds exactly for a valid program and a target whose complete binding
identity set equals that of the supplied committed vector. It constructs the
episode, runs it and invokes the actual `rollback`. Its postcondition identifies every returned cell with the supplied
initial value, no owner and zero depth. The count is from that actual run.
Invalid instructions return `InvalidInstruction`; a valid program with a
mismatched target returns `NotAdmitted`.

This is a fixed synchronous instruction language with a target held constant
throughout the call. It covers data-dependent branches and real journal
inverses, but no dynamic child creation, general Future, changing target or
service-publication requirement. It is a concrete finite execution/recovery
result, not a proof that every host run reaches global quiescence.

## Running one Fresh actor to a terminal result or the first error

[`FreshDriver::run_until_blocked`](../crates/cordis-kernel/src/fresh_run.rs), in
`mixed_driver::fresh::runner`, repeatedly calls the actual transactional `step`.
It requires only the existing `wf()` invariant: no caller-supplied fuel, future
success premise or source trace. The re-exported `RunReport` contains the
runtime fields `steps: u128` and `error: Option<DriverError>`.

The loop stops at its first real step error, or at `Outcome::Finished` or a
finished Child outcome. With no error, `run_finished` guarantees that the actor
is registered and Active and has no current instruction. An error preserves
the already committed prefix; only the failed step is rolled back. The run is
not one transaction that undoes its earlier successful work. An unknown,
Inactive or already Active actor is reported through the existing step error
rather than silently treated as a successful run.

The decreasing rank is the actual remaining forward program positions:
`run_budget = code.len() - pc + 1` for a valid current position. An invalid or
missing position has rank one, allowing the real step call to report its error.
The extra position includes a possible terminal Unit call. Forward jumps can
skip positions, so this is an upper bound, not an exact execution length.
`steps` counts committed calls, including the terminal call; it does not count
the final failed attempt. The checked postconditions are:

- `steps <=` the input `run_budget`.
- With zero committed steps, the complete machine is `same` as the input.
- On error, `steps + 1 <=` that input budget and the final actor is not
  `step_enabled`.
- With no error, at least one step committed and `run_finished(actor)` holds.
- For an actor within the input allocator range, its journal grows by exactly
  `steps`, preserving the successful effect/inverse prefix.

An empty program still performs one terminal Unit call. A forward jump to the
end likewise leaves a terminal Unit call to execute. A new child stays
Inactive: the runner registers it and captures its inverse, but does not begin
or run the child's program. Stopping with this actor Active therefore does not
mean that all actors are quiet.

The refinement boundary is explicit. `RunReport::refines` says: **for any
well-formed source configuration already represented by the input machine**,
the report constructs an extension with exactly the successful real calls and
a represented final state. `source_chain` derives this sequence from their
actual acknowledgements; callers do not supply successful outcomes as a
premise. The public proof method `RunReport::advance_source` extracts this
finite source execution once `refines`, the input representation and source
well-formedness have been established, so another proof can compose the result.
This conditional extension does not establish the existence of such a source
for an arbitrary `wf()` input. The `run_from_empty` entry point below establishes
that input path through the actual `run_script` calls and composes the two
executions. Proof-only outcomes, machine snapshots and source sequences are
ghost data erased from executable Rust; no runtime history buffer is allocated
for this proof.

The [Fresh driver regressions](../crates/cordis-kernel/tests/fresh_driver.rs)
cover jumps, Xor/Child/Provide execution, terminal publication, blocked-prefix
recovery, terminal-child rollback, empty programs and invalid phases. This is
a finite-return result for one installed synchronous program. It does not make
a strict primitive total, run every child, guarantee eventual unblocking or
instantiate Theorem 73 for an entire dynamic registry or asynchronous host.

## The exact domain of real LIFO cleanup

[`MixedDriver::unload_enabled`](../crates/cordis-kernel/src/mixed_driver.rs)
combines two independent conditions:

```text
kernel.cleanup_enabled(actor)
    && restore_receipts(journal(actor), primitive_state).is_some()
```

The first is the real cleanup guard: a registered Unloading actor, not already
restoring, with no live committed dependent. The second interprets its actual
retained receipts from last to first using `mixed_grammar::undo` on the current
primitive state. It is not a flag that assumes the next call succeeds. The
predicate is proof-only: the executable method still calls `begin_cleanup`,
applies the real inverse journal and then calls `finish_cleanup`.

Under the existing `wf()`, public `MixedDriver::unload` and
`FreshDriver::unload` succeed **iff** their input `unload_enabled` holds.
`FreshDriver::same_unload_domain` proves that complete `same` machines have the
same domain. With a registered Unloading receipt owner, the internal `undo_one`
likewise succeeds iff the modeled undo of that receipt is defined, establishes
that its `primitive_state` equals the modeled undo result on success and preserves
all Kernel restoring flags. The loop keeps the actor restoring, removes one
receipt per successful inverse and decreases the actual journal length.
`unload_inner` has the same success equivalence and, on success, establishes an
empty journal, no current instruction and an Inactive actor after the modeled
restoration and commitment release. The public wrappers connect that result to
their existing Unload refinement acknowledgement.

Each failed `undo_one` preserves its own input. However, `unload_inner` can
already have entered cleanup and restored earlier receipts before a later
failure; its error has no complete-machine rollback contract. The public
wrappers execute on a copy and publish only on success, so **public errors
preserve the whole input machine**, including values, receipts and cleanup
state. A child inverse retires the captured child. It does not remove the
registry entry, execute that child's cleanup or rewind allocation.

This is an exact acceptance and finite-return contract, not a proof that
`wf()`, `!relied` or cleanup permission makes every inverse journal restorable.
The definedness of the complete inverse sequence remains an explicit conjunct.
For Lemma 57, this connects the concrete inverse implementation to the strict
source grammar. For Corollary 69, it supplies execution evidence for the modeled
restoration. The owner-table result is connected to actual history in the
[coverage proof below](#successful-recovery-empties-the-actual-owner-table); the
terminal Mixed value equation and its concrete scalar independence are connected
below; the general host observation equation remains separate. It
does not promise physical restoration of arbitrary external resources. For
Theorem 73, it connects a permitted and defined cleanup to a real finite call;
it does not prove global progress across dynamic children or eventual scheduling.
All three ledger items remain **partial**.

The `preparation_command` profile is still only Insert/Begin/Step. Separately,
the actual Mixed/Fresh `apply` Unload branch now succeeds iff its input
`unload_enabled` holds; this does not expand that preparation profile.
Existing [Mixed driver tests](../crates/cordis-kernel/tests/mixed_driver.rs)
exercise blocked provider cleanup, captured providers and mixed Xor/Child/Xor
restoration; tests complement the contracts without proving arbitrary inverse
definedness.

## Defined restoration for actual Unit/Child journals

In [`unit_child_recovery.rs`](../crates/cordis-kernel/src/unit_child_recovery.rs),
the proof-only `unit_child_journal(actor)` classifies the **actual retained
receipts** as `Inverse::Unit` or `Inverse::Child`. `unit_child_recovery()` states
that, for every registered actor in this profile, interpreting its entire
current journal with `restore_receipts` succeeds. This is a property of the
current machine, not a promise about a future call or a restriction that every
actor in the system must use only those instructions.

The bridge starts with a well-formed source represented by the machine. Actual
journal entries identify the source accumulator's history receipts; source
`retained` then gives a registered identity for every captured child that is
still referenced. A receipt's authentic origin alone would not suffice:
`history_sound` gives inverse definedness at its original landing, whereas
retention supplies the identity needed **now**. Unit leaves the state unchanged;
Child retires its captured registered identity. Both preserve registry
membership, so recursion proves that all remaining LIFO positions are defined.

Mixed/Fresh `run_script` derive `unit_child_recovery()` from the source histories
constructed by their real calls, including when they stop at an error.
`run_from_empty` also establishes it for both its prepared and returned machines.
There is no new runtime history buffer, restoration algorithm or strengthened
`wf()` assumption. The histories used for this argument are erased ghost data.

`cleanup_permitted(actor)` exposes the Kernel cleanup guard.
`unit_child_unload_domain` combines the recovery property and journal
classification to prove `unload_enabled(actor) == cleanup_permitted(actor)`.
The actual public `unload` therefore succeeds iff cleanup is permitted under
these conditions. If `run_script` stops on an Unload error and that actor's
journal contains only Unit/Child receipts, the returned machine does not permit
cleanup. This says which guard is false at the real stopping point; it does not
classify the specific error enum or require every input command to be enabled
initially.

This directly connects Definition 52's registered-name premise to executable
recovery, as reviewed in [PR-02](paper-review-guide.md#pr-02-child-retirement-needs-the-referenced-identity-to-remain-registered).
A retired child stays registered until a legal Remove; retirement neither removes
it nor executes its own cleanup. Parent ownership creates no implicit service
dependency. The following source invariants extend this result first to Provision
and then to the complete concrete journal including Xor. The Unit receipt itself is modeled as `Table(Unit)`, so the boundary is
the concrete receipt classification, not all receipts called Table in the model.
This supplies a restricted inverse bridge for Lemma 57 and local cleanup progress
for Theorem 73; both remain **partial**. It does not add Corollary 69's general
foreign-replay equation or whole-system termination; the concrete empty-owner-table
result is established separately below.

## Provision slots survive until their real inverse

[`provision_history.rs`](../crates/cordis-kernel/src/provision_history.rs) adds a
current-state invariant, `live_provisions`, for actual source accumulators:
every retained Provision receipt refers to a value still present in its owner's
slot, and that owner's live Provision receipts have distinct keys. The invariant
is derived by induction over Mixed/Fresh execution from empty. It is not an
extra premise silently inserted into executable `wf()`.

These two facts are both necessary. A defined Provision inverse removes an
existing value; if two retained receipts claimed the same slot, the later
inverse could make the earlier one undefined. Foreign Xor operations may change
the value, but preserve the occupied slot. The invariant does not require that
the current payload equal the originally provided payload.

[`provision_recovery.rs`](../crates/cordis-kernel/src/provision_recovery.rs)
connects that source invariant and child retention to the **actual receipts**.
`unit_child_provision_journal(actor)` permits Unit, Child and Provision in the
owner's current journal. `provision_recovery()` then states that every registered
actor in that profile has a defined entire `restore_receipts` sequence. In the
LIFO induction, Provision removes its own distinct slot while leaving the other
retained provision slots occupied; Unit and Child preserve table contents and
registry membership. Other actors may have Xor receipts: the restriction is on
the journal being restored, not all programs in the system.

Mixed/Fresh `run_script` derive this property from their real successful prefix,
including error returns. `run_from_empty` derives it for both the prepared and
final machine, whether setup fails, execution blocks or execution finishes.
These are erased proof data and contracts on the existing execution path, with
no new runtime buffer or recovery algorithm. `provision_unload_domain` reduces
`unload_enabled` to `cleanup_permitted` for this profile; public `unload` succeeds
iff that cleanup guard holds. A script Unload failure in the profile therefore
means the returned state does not permit cleanup. Bootstrap's `SetupFailed`
diagnostics remain limited to the separate Insert/Begin/Step preparation profile.

This extends the current-state inverse connection for Lemma 57 and the local
cleanup obligation in Theorem 73. The next result covers Xor journals as well.
Corollary 69's general foreign-replay equation and global termination remain
separate obligations. The owner-table result is established by coverage below.

## Xor completes the current-state domain of the concrete journal

[`operation_history.rs`](../crates/cordis-kernel/src/operation_history.rs)
extends the source argument to retained operations. `operation_slot` identifies
the captured provider and port of an operation receipt; `operation_at` relates it
to a live accumulator position. `live_operations` records three facts: the
receipt still resolves to its captured provider under the episode's committed
bindings; that provider remains registered with a value at the captured port;
and a later Provision in the same journal cannot remove a slot needed by an
earlier operation. The last condition matters for self operations: a successful
self Xor needs an earlier Provide, so LIFO recovery undoes the Xor before deleting
that value. It is a condition on actual history order, not an assumption that
arbitrary inverse operations commute.

`mixed_from_empty` and `fresh_from_empty` derive these facts throughout the real
source trace. Provider retirement or a changed current target does not replace
the episode's committed identity. The dependency guard prevents provider cleanup
while its consumer still holds that commitment, connecting the provider-lifetime
rules in Definitions 53/54 to the value needed by the inverse. This argument
complements Definition 52's child-name retention; it does not treat ownership as
a service dependency.

[`journal_recovery.rs`](../crates/cordis-kernel/src/journal_recovery.rs), exposed
as `mixed_driver::recovery_all`, connects this source invariant to the **actual
receipts** through `operations_from_source`. `restore_all` combines `live_xors`,
Provision uniqueness and value presence, and retained child identities to prove
defined LIFO restoration for every concrete receipt variant: Unit, Child,
Provision and Xor. Xor preserves the occupied slot, and its concrete `u64` scalar
inverse is total. These are the existing executable inverse operations, with no
new runtime journal or alternate recovery algorithm.

`journal_recovery_from_source` establishes `journal_recovery()`: every registered
actor's complete current journal has a defined `restore_receipts`. Mixed/Fresh
`run_script` derive it on every return, including the successful prefix before
an error. `run_from_empty` derives it for both the prepared and final machine in
all statuses. Under this property, `journal_unload_domain` proves
`unload_enabled(actor) == cleanup_permitted(actor)` without a receipt-profile
restriction. The real public Unload therefore succeeds iff the Kernel cleanup
guard holds; a script stopped by Unload has a false cleanup guard at its actual
stopping state. Bootstrap's `SetupFailed` error diagnostics remain limited to
the separate Insert/Begin/Step preparation profile.

The earlier `unit_child_recovery` and `provision_recovery` APIs remain available
as narrower results. This stronger result covers the complete synchronous
`u64`/Xor instruction language, not arbitrary plugin scalars or host callbacks.
It discharges the concrete journal's inverse-definedness obstacle for Lemma 57
and local cleanup in Theorem 73. Corollary 69's general foreign-replay observation
equation, global progress and host scheduling remain separate obligations. The
concrete empty-owner-table result is established by coverage below; the paper-wide statuses remain **partial**.

The [Xor recovery tests](../crates/cordis-kernel/tests/xor_recovery.rs) run real
scripts and bootstrap calls: self Xors interleaved with Provision/Child, captured
providers after retirement, two consumers with interleaved effects, and recovery
of a bootstrap prefix after incomplete publication. These are concrete behavior
regressions alongside the proof, not a proof for arbitrary host effects.

## Successful recovery empties the actual owner table

[`provision_coverage.rs`](../crates/cordis-kernel/src/provision_coverage.rs)
derives `provided_journals` throughout Mixed/Fresh execution from empty. It
supplies the converse of `live_provisions`: **every currently occupied owner
slot has a retained Provision inverse**, rather than only proving that every
Provision inverse still has its value. Without this coverage direction, an
inverse sequence could be defined yet leave an unrecorded owner value behind.
The induction follows actual successful source transitions, including dynamic
children, foreign operations and cleanup. It does not assume that a future
Unload will succeed.

[`owner_table_recovery.rs`](../crates/cordis-kernel/src/owner_table_recovery.rs),
exposed as `mixed_driver::owner_recovery`, connects the source coverage theorem
to the same table and receipts used by executable Unload.
`owner_table_recovery_from_source` establishes `owner_table_recovery()`: for
every registered actor, **if** its full `restore_receipts` is defined, the
resulting owner table is empty. The separate `journal_recovery()` property
establishes definedness; the new property specifies the result. Both cover all
four concrete receipt variants and are derived for every Mixed/Fresh
`run_script` return and both bootstrap machines, including failed prefixes.

Under the **input** `owner_table_recovery()` property, successful public
`unload(actor)` and `apply(Command::Unload { actor })` now ensure that the actual
output `table(actor)` is empty. `same_owner_table_recovery` transfers the
property to the existing transactional draft. This strengthens the contracts
on the current LIFO implementation without a new clearing operation or runtime
history buffer. These are guarantees at the stated entry and call boundaries;
individual mutators do not all expose preservation of the property, so a caller
must reestablish it when needed after further mutations. Public error behavior
and the separate cleanup guard are unchanged.

This connects **Corollary 69's empty-owner-table conclusion** to the concrete
synchronous Mixed/Fresh implementation. It does not establish the general
foreign-replay observation equation, arbitrary host-resource recovery or global
progress; Corollary 69 remains **partial**. Child retirement still leaves the
child's separate table and journal to its own cleanup.
[Owner-table regressions](../crates/cordis-kernel/tests/owner_table_recovery.rs)
exercise partial-loading recovery and a second episode on the same registration:
reproviding the old ports succeeds, foreign Xor effects recover, and a retired
child's independent value survives the parent's cleanup.

## Terminal Mixed scripts equal their foreign-only value replay

[`terminal_replay.rs`](../crates/cordis-kernel/src/terminal_replay.rs), exposed
as `mixed_driver::terminal_replay`, strengthens the actual **Mixed**
`ScriptReport`. `terminal_episode(transitions, owner, begin)` selects a Begin
in the successful transition log, requires that the last successful transition
is that owner's Unload, and excludes an intervening Unload by the same owner.
The actual source execution then supplies the installed interval; callers do
not assume it or provide a separate source trace.

`run_script` automatically establishes `terminal_recovery(bank)` for every
matching episode in its returned log. The proof method
`report.terminal_replay(bank, owner, begin)` extracts the represented source
execution and two results about the returned machine: the owner's table is
empty, and `value_observation()` equals `foreign_replay(...)`. The latter starts
from the snapshot **immediately after Begin** and applies `entangled::foreign_state`
to the actual value events before the terminal Unload, excluding the owner's
landings. Foreign Unloads retain their **actual captured inverse journals**.
The observation is Definition 51's projection of all registered tables,
including Loading values; it is distinct from Active-only service publication.

[`xor_recovery_algebra.rs`](../crates/cordis-kernel/src/xor_recovery_algebra.rs)
derives the scalar premise from the real interpreter library: every forward
operation and returned inverse is a `u64` Xor mask, and all such transformations
commute. The caller supplies no scalar commutation assumption. Owner Child
instructions are permitted, with their usual retirement inverse; the theorem
states equality of projected **values**, not equality of registry identities,
phases, journals or the allocator.

The statement applies to the successful prefix even when `report.error` is
`Some`: a later failed command leaves the machine unchanged and is absent from
`transitions`. It does not cover an earlier Unload followed by further successful
commands. No runtime replay buffer or second interpreter is introduced.

Foreign replay here is a value calculation, **not** a claim that deleting the
owner leaves executable lifecycle commands. An operation on a missing key is
identity in this value algebra. A consumer that originally used the owner's
new service may therefore have a defined counterfactual value calculation even
though its original Begin/Step would fail without that owner. This boundary is
part of the statement, not a relaxation of the real driver's checks.

This gives a concrete Theorem 68/Corollary 69 terminal value equation for Mixed
scripts. Fresh's dynamic-choice source bridge has not yet been connected to
this report contract; Fresh retains the inverse-domain and empty-owner-table
results above. Arbitrary plugin scalar operations, host effects, legal deletion
of lifecycle executions and global progress remain separate; the paper-wide
obligations stay **partial**. The two
[terminal replay regressions](../crates/cordis-kernel/tests/terminal_replay.rs)
compare real final values with explicit foreign-only calculations, including
owner-created service consumers and child values, an interior foreign Unload,
and a checked error immediately after the terminal successful Unload.

## From a new machine through setup and execution

[`run_from_empty(blueprints, setup_commands, actor)`](../crates/cordis-kernel/src/fresh_bootstrap.rs)
is an executable entry point reexported by `mixed_driver::fresh` with
`FromEmptyReport` and `FromEmptyStatus`. It constructs a new machine, calls the
actual `run_script`, then calls `run_until_blocked(actor)` only if every setup
command succeeded. The caller supplies no machine, source witness, fuel or
assumption that future calls succeed.

| Returned status | Actual stopping point and checked report |
| --- | --- |
| `SetupFailed(error)` | The first setup call that returned an error stops preparation. `setup` is the successful command prefix, shorter than the input commands; `steps == 0`, and the autonomous runner was not called. The selected actor may still be enabled. |
| `Blocked(error)` | Every setup command succeeded. The autonomous runner stopped at its first error, preserving committed steps; the final actor is not `step_enabled`, and `steps + 1 <= prepared.run_budget(actor)`. |
| `Finished` | Every setup command succeeded and the autonomous runner reached terminal publication. `steps > 0`, the actor is Active with no current instruction, and `steps <= prepared.run_budget(actor)`. |

`setup: Vec<Transition>` records real successful preparation calls, including any
`Command::Step` in the supplied script. `steps: u128` counts only committed calls
in the subsequent autonomous run, including its terminal call; it excludes both
setup calls and the failed attempt. With zero autonomous steps, the complete
returned machine is `same` as the prepared machine. Setup failure must not be
read as proof that the selected actor is blocked: preparation can fail on a
different actor while the selected actor is already ready.

`FromEmptyReport::refines` now establishes **one source execution from empty**
without a caller-supplied input representation. It represents the actual
prepared machine at the setup boundary and the returned machine at the end;
every source state is well formed and `resource_safe`. The preparation witness
establishes the premises of the existing conditional `RunReport::advance_source`.
`concatenate` joins the two executions at their identical boundary state once,
without adding an administrative or failed-call event. The public proof method
`FromEmptyReport::source_execution` extracts this established execution for
further composition. Prepared snapshots, autonomous outcomes and source states
are erased ghost data; the successful setup `Vec<Transition>` remains a runtime
allocation.

The setup domain is now exact for the
[`preparation_command`](../crates/cordis-kernel/src/fresh_preparation.rs) profile:
`Insert`, `Begin` and `Step`. These predicates are proof-only; the executable
branches and error order are unchanged.

| Command | Current-machine predicate used by `preparation_enabled` |
| --- | --- |
| `Insert { parent, blueprint }` | `FreshDriver::insertion_enabled`: the Mixed domain, including blueprint index, validity of the required bank prefix and the Kernel insertion checks for capacity, parent, declarations and reserved provisions. |
| `Begin { actor }` | `FreshDriver::begin_enabled`: a registered actor with an empty retained journal and the Kernel Begin domain, including Inactive phase, target availability and generation capacity. |
| `Step { actor }` | The existing `step_enabled`: a ready actor, the current primitive's exact domain and complete publication after a terminal instruction. |

For a command in this profile, `FreshDriver::apply` succeeds **iff** the input
machine satisfies `preparation_enabled(command)`. If `run_script` returns an
error and the failed command belongs to the profile, the returned machine does
not satisfy that command's predicate. For `run_from_empty`, `SetupFailed`
propagates this fact to both `prepared` and the returned machine, with the failed
command at `setup_commands[setup.len()]`. This is a predicate at the actual
failure state after the successful prefix, not a requirement that every command
be enabled in the initial empty machine. Earlier successful commands may include
commands outside the profile. Failure of this command still does not imply that
the separately selected autonomous actor is blocked.

`Retire`, `Depart`, `Unload` and `Remove` remain executable dispatcher commands.
`preparation_enabled` returns false for them solely because they are outside
this profile; the preparation equivalence is guarded by `preparation_command`,
so this is not a rejection claim. Unload has the separate exact `apply` branch
contract above; the preparation profile has not expanded. Retire/Depart/Remove
domains and dispatcher equivalences still require work. The contracts also do not
identify each error enum value (`Unknown`, `Retained`,
and so on) from an input predicate. They establish acceptance within the stated
implementation domain, including blueprint validity, finite capacity and strict
value availability; they do not prove acceptance of every paper-enabled setup
command. The successful-prefix source execution remains unchanged.

[Bootstrap regressions](../crates/cordis-kernel/tests/fresh_bootstrap.rs) cover
setup failure with an already enabled actor, successful preparation plus execution
and recovery, a strict primitive blockage, empty setup, an actor already
completed by setup, provider publication enabling a later Begin, invalid bank
prefixes, registered provision reservations and Begin/Step prefix retention.
Newly created children still remain Inactive. This closes
the initial-source existence gap for this concrete entry point, while multiple
actors, child execution, recovery domains and a global rank remain necessary
for a whole-system progress result. Lemma 57 and Theorem 73 remain **partial**.

## What remains before a broader progress claim

1. **Complete host capture and execution.** The vector-order/multiplicity gap
   is closed by the shared comparison and the verified driver capture bridge.
   The ordinary Rust/Node host still needs a proof connecting its actual captured
   values, episode identities, availability checks and publication boundaries to
   those contracts throughout asynchronous execution. Calling the verified
   matcher is not a refinement proof of the surrounding host.
2. **General continuation domains.** The fixed program constructor derives its
   domain and forward rank from actual checks; dynamic child registration now
   has an exact input-domain contract. Synchronous Mixed/Fresh steps now also
   expose exact effect and terminal-publication domains; the owning admitted
   protocol rechecks its exact domain across checked calls. General child bodies
   and arbitrary callbacks still need their own definedness bridges. The Fresh
   runner now derives finite return for one installed actor, but it can report
   a blocked primitive; this does not establish totality or eventual successful
   completion of every dynamic program. The strict guarded child example remains
   a boundary.
   Adding an error exit changes the transition system and needs separate review.
3. **Whole-system executions and preparation/recovery domains.** `run_from_empty`
   now establishes the initial source through actual setup and composes one
   actor's run, rather than leaving that entry premise to the caller. The
   Insert/Begin/Step preparation profile now has exact acceptance domains;
   direct Mixed/Fresh Unload now also has an exact guard-plus-inverse domain.
   Retire/Depart/Remove, the wider dispatcher and other recovery paths still
   need their own domain equivalences. Reachable histories now establish inverse
   definedness for the complete actual Unit/Child/Provision/Xor journal. This
   concrete inverse-domain result now composes with a terminal foreign-only value
   equation for Mixed script reports. Fresh dynamic-choice replay and host-effect
   contracts remain separate.
   Individual error variants are not characterized by the preparation predicates.
   Compose execution across multiple actors, dynamic children and recovery with
   the paper's global count/rank argument. These entry points do not instantiate
   `termination.rs` for the entire host.
   A scheduler contract is needed if the chosen statement quantifies over host
   executions that may delay enabled lifecycle work.

The production shared Driver now also uses a [verified cleanup-result protocol](cleanup-protocol.md).
It connects exact action completion and explicit failure/retry to the actual
commitment-release call. This is a local safety contract; host callback results,
external effects and eventual scheduling remain separate obligations.

## Is verus-tla needed here?

**Not for these contract repairs.** Ordinary Verus expresses and checks their
state predicates, success equivalences, executable loops with decreasing
ranks, resource recovery and finite-trace arguments. There is no added Cargo or runtime dependency in this change.

[`verus-tla`](https://github.com/anvil-verifier/verus-tla) provides reusable
temporal-logic definitions and proof rules. It can help if a later, explicitly
scoped claim quantifies over infinite host executions: for example, a cancelled
stage whose terminal reply has arrived will eventually settle, provided its
enabled advancement is eventually scheduled. The executable advancement must
first be proved to implement that temporal action, and the scheduling/reply
premises must remain visible. The library does not prove those premises merely
by importing it.

For the paper-to-code goal, the next priority is the remaining host-capture and
continuation bridges above. Choose a temporal library after stating a property
that benefits from its rules; do not replace an incomplete executable contract
with an unconnected temporal model.

## Reproduce the checks

From the repository root with the pinned toolchain and cached dependencies:

```sh
cargo test --offline -p cordis-kernel --lib iteration_tests
cargo test --offline -p cordis-kernel --test insert_domain
cargo test --offline -p cordis-kernel --test program checked_
cargo test --offline -p cordis-kernel --test episode_protocol
cargo test --offline -p cordis-kernel --test ownership
cargo test --offline -p cordis-kernel --test child_driver
cargo test --offline -p cordis-kernel --test mixed_driver
cargo test --offline -p cordis-kernel --test fresh_driver
cargo test --offline -p cordis-kernel --test fresh_bootstrap
cargo test --offline -p cordis-kernel --test admitted_fresh_driver
cargo test --offline -p cordis-kernel --test admitted_script
cargo test --offline -p cordis-kernel --test driver
cargo test --offline -p cordis-kernel --test episode_identity
python3 scripts/check-paper-coverage.py
python3 scripts/check-paper-review.py
python3 scripts/record-development.py --offline
```

The development recorder runs whole-kernel verification with `--no-cheating`,
compilation, Rust tests, Node compatibility tests and packaging checks. Its
[record](development-report.json) binds results to source hashes. It is separate
from the full release gate and all canonical negative controls.
