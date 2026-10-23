# R3: recovery from managed execution histories

[简体中文](r3-production-recovery.zh-CN.md) · [Episode recovery](r3-episode-recovery.md) · [Milestones](paper-refinement-roadmap.md)

This R3 batch connects the production mixed scalar/typed interpreter's actual
Begin and invocation-return observations to its retained inverse queue. Typed
history also explains restored interference and actual cleanup retry through
indexed Apply/Replace/Restore events. R3 remains in
progress: this is a production recovery building block, not full Equation (55)
for every production episode or a legal lifecycle-deletion theorem.

## What the real entry points guarantee

`Execution::run_function`, used by stored roots and Children, now establishes
`Report::recovery_history` for both successful functions and retained prefixes
before a failure. `NativeRuntime::run_managed_root` propagates that contract.

Each write names its actual `(Journal, allocation)` address. For two writes to
the same address, a **quiet gap** means that every intervening Journal commit
preserves that allocation's complete recorded state. Unrelated commits and
rejected scalar attempts are allowed. Different service names do not establish
independence; equal numeric keys in different Journals do not establish identity.

A typed gap can also return to the earlier **semantic head** at a higher revision.
The persistent source histories then prove equality of the full semantic state;
equal payload contents alone are insufficient. `restored::between` identifies
an actual `PayloadRestore` between those two writes. This permits a foreign
temporary write followed by restoration without pretending the gap was quiet.

From authentic history and these gap conditions, the proof derives that
consecutive writes to one allocation have matching output/input states. `recovery_word` then derives
forward replay and inverse definedness without assuming either succeeds.
`recover_retained` applies that result to the actual mixed cleanup-queue suffix;
`recovered_aliases` lifts the result to all names selecting those allocations.

The input map consists of **each allocation's first actual observation** in the
function. It is not claimed to be one simultaneous snapshot across Journals. The
recovery starts from the function's recorded final writes; a foreign write after
those writes can still block the real cleanup. The quiet-gap condition is a
sufficient condition inspected in ghost history, not a runtime scheduler promise
or a requirement to suppress other plugins.

## Actual Begin provenance

Registered root and Child dispatch now retains a persistent `Begin` witness from
`NativeRuntime::current_begin`. The position is derived from the current native
owner and its indexed execution history; it is not an expected checkpoint supplied
by the caller. The witness identifies the actual setup ticket and work domain.

`run_function_following` seeds the real receipt map before the first effect.
Every successful write in that Journal follows the retained checkpoint, including
writes in a failed function's prefix. The original `run_function` entry delegates
to the same interpreter with no supplied predecessor. The registered return
receipt also follows the checkpoint, including an empty or rejected function.
`RegisteredReport::episode_interval` connects these facts to the returned owner
and work ticket. Receipts in other Journals retain their own explicit domains;
this does not invent a cross-Journal order.

`managed_endpoint` now decodes scalar and typed values at real Journal cuts.
Typed values come from the inverse's authenticated source history at the recorded
revision. Missing, retired or unavailable typed records are not invented values.
`RegisteredReport::begin_values` uses the retained checkpoint immediately after
the actual Begin; `return_values` uses the real invocation-return receipt.

The actual `run_managed_root` return establishes `endpoint_recovery` and
`retained_recovery`. Under `endpoint_source`, they prove:

```text
replay(actual function steps, BeginValues) = Some(ReturnValues)
undo(actual retained mixed queue suffix, ReturnValues) = Some(BeginValues)
```

The condition requires all relevant writes in the same Journal, quiet boundaries
from Begin to each first write and from each last write to return, and admissible
gaps between writes to the same allocation. Those interior gaps may include the
typed restoration described above. No desired heap or successful inverse is a
premise. Failed functions retain the same guarantee for their successful prefix.

These maps cover allocations touched by this invocation. The actual mixed
dispatcher now retains source queue boundaries and establishes strict restoration,
failure retention and retry contracts. The [cleanup composition](r3-cleanup-recovery.md)
derives successful finite attempts and recovery of Begin values from actual emitted
results when their observed reads continue the proven return trajectory.
[Interleaved recovery](r3-interleaved-recovery.md) now includes foreign managed
writes, blocked attempts and restoration, derives exhaustion from actual later
successful restores, and decodes the common actual Unload cut. This value result
has explicit source and quiet-tail conditions; full publication/Child effects,
complete production trace construction and arbitrary intermediate cuts remain
separate obligations.

An earlier combined native Begin, managed, typed-payload, Mixed/Fresh script and
Xor batch passed scoped verification (401 verified, 0 errors). The current
interleaving/Unload integration's verified scope and pending acceptance are recorded
in [interleaved recovery](r3-interleaved-recovery.md). The earlier full development recorder was
interrupted before package acceptance; its raw whole-kernel, Rust and Node results
do not certify these subsequent source changes. The next integrated acceptance
must refresh the complete development record.

Pending acceptance cases for the combined endpoint/recovery contract:

- Repeated activation and dynamically registered Child roots select their own
  actual Begin, including interleaved commits by other owners.
- Empty functions, admission rejection and retained failed prefixes preserve the
  same invocation origin and causal return.
- A foreign Journal is not assigned an invented position in the native Journal.
- Contract mutations that substitute an earlier episode or discard the initial
  receipt are rejected at the named causal contract.
- Aliases and failed prefixes recover the actual Begin values; boundary writes
  and retired payloads must not be admitted as quiet endpoints.
- Interleaved typed write/restore returns to the prior head at a newer revision;
  same-value replacement alone must not satisfy that condition.
- Mutations that misclassify a replacement as restoration or sever the retained
  queue/endpoint relation must fail the designated semantic contract.

## Why typed history needs an authentic witness

A payload's common Journal record contains its identity and monotone revision;
its typed semantic history remains with the typed owner. Revision numbers alone
cannot prove that two payload observations have the same meaning.

`history::Witness::prefix` now compares actual persistent resource witnesses.
The real typed admission retains a witness, and the function report preserves
it alongside the existing write/registration receipts. `linked_pair` connects
the Journal gap to typed-history prefix equality, rather than accepting equal
histories as a caller premise. The additional resources and maps erase: this
batch adds no runtime history buffer, payload clones or locking to retain them.

`payload::semantic_history::valid` additionally classifies every retained typed
version against its indexed Journal mutation. The real constructor, raw replace,
managed apply and restore maintain this invariant. Apply gets a fresh head and
adds one outstanding inverse; raw replace gets a fresh head and resets the depth;
Restore returns to a smaller head and removes one outstanding inverse. Only an
actual Restore can land on an earlier head. These are contracts on the running
storage operations, not an independent history supplied by a caller.

## Actual cleanup, conflicts and retry

The real locked typed read now exports that its history extends the inverse's
actual forward history. `Attempt::strict_domain` proves:

```text
this actual attempt succeeds
    iff its live observed semantic state equals the inverse's captured output
    iff its live semantic head equals the inverse's expected head
```

Successful restoration recovers the captured input. A newer monotone revision
is allowed: a foreign inverse can restore the semantic head while advancing the
anti-stale read revision. An old read remains stale in that situation.
`Attempt::resumed_origin` now identifies the actual earlier `PayloadRestore`
whenever this attempt succeeds at a newer revision. Real restore and cleanup
returns establish that fact alongside the strict domain and conflict witness.

For a failed live attempt, `conflicting_write` identifies an actual later mutation
to the same allocation in the authenticated Journal. A closed attempt identifies
an actual `PayloadRetire` event through `retirement_write`. A quiet interval from
the inverse's forward commit to its locked read implies success. These facts are
established by real restore and typed cleanup return paths. Existing queue
contracts retain the failed inverse and distinguish new retry tickets from old
completions. None of these results promises that a conflicting plugin eventually
runs its inverse or that a scheduler eventually retries cleanup.

## Review and reproduction

| Link | Source |
| --- | --- |
| Authentic comparable history | [shared_value_history.rs](../crates/cordis-kernel/src/shared_value_history.rs): `Witness::prefix`, `compatible_map` |
| Runtime admission and report retention | [payload_cleanup.rs](../crates/cordis-kernel/src/payload_cleanup.rs), [managed_function.rs](../crates/cordis-kernel/src/managed_function.rs) |
| Journal gaps to actual scalar/typed state composition | [managed_recovery.rs](../crates/cordis-kernel/src/managed_recovery.rs): `linked_pair`, `establish_recovery` |
| Defined mixed word and actual queue suffix | [managed_recovery_word.rs](../crates/cordis-kernel/src/managed_recovery_word.rs): `defined`, `recover_retained` |
| Actual Begin and registered execution interval | [lifecycle_state/native/runtime/episode.rs](../crates/cordis-kernel/src/lifecycle_state/native/runtime/episode.rs), [managed_episode.rs](../crates/cordis-kernel/src/managed_episode.rs), [managed_root.rs](../crates/cordis-kernel/src/managed_root.rs) |
| Actual Begin/return values and retained queue recovery | [managed_endpoint.rs](../crates/cordis-kernel/src/managed_endpoint.rs), [managed_root_recovery.rs](../crates/cordis-kernel/src/managed_root_recovery.rs) |
| Typed mutation history and restored interference | [payload_semantic_history.rs](../crates/cordis-kernel/src/payload_semantic_history.rs), [managed_restored.rs](../crates/cordis-kernel/src/managed_restored.rs) |
| Real typed attempt, failure cause and strict domain | [payload_attempt.rs](../crates/cordis-kernel/src/payload_attempt.rs), [payload_recovery.rs](../crates/cordis-kernel/src/payload_recovery.rs) |

The [runtime cases](../crates/cordis-kernel/tests/managed_function.rs) include two
providers exposing aliases to the same scalar and typed allocations, an external
same-value write that still blocks cleanup, preservation of the real inverse,
a new retry ticket, recovery through the mixed LIFO queue, stale read rejection,
and refusal to repeat restoration or revive a retired allocation.

```sh
source scripts/toolchain-env.sh
cargo test -p cordis-kernel --test managed_function --locked --offline
python3 scripts/check-profile-controls.py production
python3 scripts/record-development.py --offline
```

The selected controls treat a changed allocation as quiet and weaken the actual
typed head guard to accept an already consumed head. Each requires a fresh
matching positive, whole-mutant compilation and the exact contract rejection.
Their source-bound report lives in `target/r3-production-controls/report.json`;
full negative regression/calibration remain `not_run`. The tracked development
record is separate; its old pass never applies automatically to changed sources.

## Remaining R3 obligations

- Extend conditional value recovery at actual Begin/Unload to complete production
  histories and all intermediate cuts. The [release-based theorem](r3-interleaved-recovery.md#from-the-actual-release-guard-to-successful-restoration) derives local closure;
  registration membership now comes from the running interpreter. Construct complete
  consuming-acknowledgement coverage from admitted production execution. Foreign restoration closure remains explicit.
- Compose publication, dynamic Child and pending registration with the established
  foreign-write/failure/restore/retry trajectory, without assuming a coherent
  snapshot or successful undo.
- Construct legal surviving executions for the explicitly admissible Child and
  consumer cases, then review the combined Equation (55)/(56) correspondence.

Original Theorem 68 and Corollary 69 remain `partial`; the R3 exit criteria and
whole-paper audit are unchanged. Arbitrary payload interiors, host callbacks and
external I/O are outside the typed replacement guarantee.
