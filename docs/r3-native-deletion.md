# R3: delete an interior native episode window

[简体中文](r3-native-deletion.zh-CN.md) · [Host ownership](r3-host-recovery.md) · [Milestones](paper-refinement-roadmap.md)

Package 4 constructs a **legal surviving native lifecycle/publication/owner
history from an actual production snapshot**. Selection is a history window,
so earlier and later Episodes of the same plugin remain intact. This closes a
native projection case of constructive deletion; **R3 remains in progress**.

## Guarantee

A certified `NativeRuntime` snapshot already contains a complete, ordered typed
projection of the real Journal. Given a source-admissible window, the constructor:

- removes selected activation/cleanup steps and selected Child registrations;
- retains every other step, in order, with its original typed publication and
  Episode owner payload;
- proves each surviving native step legal, including Begin admission and the
  consumer guard at Unload;
- rejoins the exact source state at the closing boundary and preserves all
  earlier and later transitions, including other Episodes of the selected owner;
- derives target identity freshness from actual source allocation history and
  maps every retained label to its original native Journal commit.

Target legality, a successful target Unload, and expected final tables are **not
inputs**. The result includes the paper control execution relation. `Restart`
remains the explicit host extension: strict paper execution is concluded only
when the target has no Restart, and a Restart-free source guarantees that fact.

## Source guards and diagnoses

`Window { start, end, region }` uses state indices; transitions in `[start, end)`
are selected. The region identifies owners whose Episodes are omitted and a
subset of names whose registrations are also erased. Guards inspect the actual
source, including intermediate states:

| Source condition | Why it is needed |
| --- | --- |
| Selected owners are inactive, with empty commitments and no publication/owner entry at both boundaries | An interior splice must meet the original prefix and suffix exactly. |
| Erased names are absent at both boundaries | Retire and Unload do not imply registry Remove. A still-registered Child prevents this exact splice. |
| Retained declarations avoid selected owners' provisions | A retained consumer must not lose the provider needed for its Begin or installed view. |
| Retained registrations do not name erased parents | A Child cannot survive without its registered parent. |
| Insertions under selected parents join the erased birth set | Removing a creating Episode cannot silently retain its Child birth. |

The proof-only query returns a source diagnosis for invalid bounds, an invalid
region, an opening/closing obstruction, an orphaned parent, a missing consumer,
or an omitted Child birth. These are failures of this admitted profile, not a
claim that every alternative deletion strategy is impossible.

## Actual entry points and composition

`NativeRuntime::deletion_snapshot` calls the existing production snapshot
operation and constructs its certificate. `Snapshot::delete_window` queries an
already captured snapshot. `Snapshot::delete_since_begin` locates the original
Begin using its authentic receipt and stored position, rather than mistaking
the later receipt checkpoint for the Begin itself.

For a managed invocation, `RecoveryCapture::with_deletion` uses the **same cut**
as the existing value/Child census and publication/owner/pending recovery. Its
opening is that capture's authentic pre-Begin boundary. It retains all existing
results and adds the deletion result; there is no extra Journal read.

These are verification-facing APIs. Their histories, selection and results are
`Ghost`/`Tracked` data erased by Cargo. They add no runtime event buffer, payload
retention, automatic rollback or runtime “proved” flag. A parent can finish its
own cleanup while the deletion query still rejects a registered Child. The
separate results deliberately retain that distinction.

## Paper-to-code review

| Obligation | Review path |
| --- | --- |
| Definitions 53–54: admission and dependency-safe Unload | `native_episode_deletion::{retained_target, control_step, transport}` proves guard preservation from source closure. |
| Lemma 79 constructive deletion, scoped to native control/publication/owner observations | `Window::{construct, delete}` builds the surviving history; no target trace is supplied. |
| Repeated Episodes and interior selection | `Window::unchanged_outside` preserves exact source transitions outside the selected window. |
| Birth and admission provenance | `Window::{births_closed, fresh}` and `Snapshot::deletion_source` preserve source birth constraints, allocation freshness and real commit identity. |
| Equations (55)/(56) remain distinct from legal execution | `RecoveryCapture::with_deletion` combines the existing value result with this native result at one actual cut, without equating their conclusions. |

Sources: [native deletion](../crates/cordis-kernel/src/lifecycle_state/native/runtime/history/deletion.rs),
[window construction](../crates/cordis-kernel/src/lifecycle_state/native/runtime/history/deletion/trace.rs),
[combined capture](../crates/cordis-kernel/src/reversible_value/managed/interleaving/history/lifecycle/deletion_capture.rs).
The original paper ledger and R3 acceptance criteria are unchanged.

## Nonempty evidence

The [proof client](../crates/cordis-kernel/src/lifecycle_state/native/runtime/history/deletion/client.rs) proves
its source path itself: 27 native steps contain earlier/later owner Episodes,
a consumer, an owned Child, a cleanup-failure stutter and an independent
provider. The constructor yields 11 legal steps, retaining the exact earlier
and later typed owner/publication payloads. Missing consumers, omitted births,
and closing before Child Remove or owner Unload are rejected. These counts
describe a proof fixture, not a performance measurement.

The [native regression](../crates/cordis-kernel/tests/native_runtime.rs) executes
both fixture variants through real calls. It checks failed consumer cleanup,
stale-reply rejection, a blocked parent, separate Child retirement/removal,
later owner activation and unchanged independent publication. Runtime assertions
validate this fixture; they are not the proof of arbitrary callbacks.

```sh
source scripts/toolchain-env.sh
cargo test -p cordis-kernel --test native_runtime interior_episode_deletion --locked --offline
python3 scripts/check-profile-controls.py deletion
python3 scripts/record-development.py --offline
```

Two strict semantic controls retain actions that should be erased or skip the
Child-birth closure check. Each must compile and fail its designated assertion,
with a fresh positive baseline. Timeouts, resource exhaustion and unrelated
failures do not count. Scoped evidence lives in `target/r3-deletion-controls/`;
the [development record](development-report.json) binds combined checks to exact
sources. Full negative regression remains separately reported as `not_run`.

## Remaining boundary

The target is a legal **native observation history**, not a new full Journal or
an executable replay of arbitrary Rust/Node callbacks. It retains original
source tickets and payload references; replaying allocation/generation counters,
shared slot interiors, inverse queues, host work and external I/O needs further
transport. Equal native endpoints do not prove heap-value recovery. Sharing a
cut with the existing recovery certificate does not by itself construct a legal
execution for the combined effect carrier.

The separate Mixed/Fresh construction still has its own whole-region guards.
Combining its shared-effect profile, episode selection, fixed-name Mixed code
transport and asynchronous landings remains open, as does Node protocol recovery.
Neither this package nor its development evidence claims whole-paper completion,
global termination, fairness or release acceptance.

[Package 5](r3-effect-deletion.md) now adds full Journal relation transport under explicit source-read and cause closure. Physical allocation/generation replay and arbitrary callback interpretation remain open.
