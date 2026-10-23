# R3: execute a retained managed invocation on a target host

[简体中文](r3-target-execution.zh-CN.md) · [Automatic source chain](r3-source-chain.md) · [Roadmap](paper-refinement-roadmap.md)

An opt-in `run_replayable_root` now preserves the executable inputs of an actual
registered managed invocation. Its source can register and run that program in
another native runtime using the existing Begin, managed interpreter, work
completion and recorded cleanup owner. This moves the target side beyond Kernel
control replay for one registered managed invocation. **R3 remains in progress.**

The shared-object extension now composes multiple actual target invocations,
including provider publication and retained failure owners. See
[shared target execution](r3-shared-target-batch.md) for the common-namespace
contract, executable profile and remaining source-to-target simulation work.

## One executable path

1. Source capture copies the function from the actual registration, including
   scalar calculations, branches and replacement `Arc<T>` inputs. It binds this
   copy to the actual returned invocation report, revision, action and work
   provenance. A failed invocation's successful prefix stays a failed prefix.
2. `Source::bind_control` observes the complete shared Journal after the actual
   return receipt and attaches the automatically recorded lifecycle commands.
   Coverage is derived under the real Journal lock; no second source transcript
   or assumed chronological prefix is supplied by the caller.
3. `Source::instantiate` installs a fresh target registration with the captured
   function and declarations. It checks the resolved dependency/provision lists
   and instruction ports before Begin. It rejects reused source lifecycle/work
   domains before modifying the target, preventing source-ticket substitution.
4. The actual target Begin creates its owner and captures target providers. A
   strengthened admission contract proves that a valid bound body with that
   fresh owner **enters the original interpreter and returns an invocation
   report**. Returning an invented admission failure is not an implementation
   of this contract. Primitive/service failures remain actual report outcomes.
5. The target report refers to target action/work tickets, target forward
   receipts and the inverses actually inserted in the target cleanup queue.
   That `RecordedExecution` uses the existing Finish, withdrawal, cleanup,
   failure, retry, Unload and final recovery-census APIs.

No desired target result, fabricated Journal frame or source inverse is passed
as an executable replay input. The original program runs against the target's
current services. Consequently different target inputs can produce different
results; input correspondence is a proof obligation, not an implicit guarantee.

## Local transport guarantee

The actual source and target steps are interpreted with the same preserved
program. For two successful steps at the same program counter:

- equal scalar value/depth inputs imply equal outputs and continuations;
- equal opaque payload values imply equal payload results and continuations,
  while target object heads and strict inverses remain target-local;
- the target inverse is retained in its actual queue slot and its registration
  refers to the target creating operation.

`TargetRun::pair_step` establishes this local relation from the two real reports.
It does not assume that every target operation succeeds or prove that an entire
selected source Journal is reproduced. A replacement Arc can be the same while
a newer target version still correctly blocks an old inverse.

## Actual input retention and individual target seeds

`run_replayable_root` also captures each successful step's original operand
through the inverse still retained in the returned owner's real queue. It copies
the scalar value/depth or the typed pre-write Arc/head/depth. `Input::wf` ties
these executable values to the actual step, program counter, queue token and
write/allocation provenance. Capture does not read the now-mutated object and
does not consume or duplicate restoration authority. A failed operation adds no
invented operand; its successful prefix is retained in order.

The retained Arc is the typed value carrier; it does not snapshot arbitrary
user-controlled interior mutable state.

`Source::inputs()` exposes these immutable records. `Input::seed(journal)`
constructs an individual resource in the target Journal using that captured
operand. Scalar inputs with nonzero depth return `OutstandingScalarHistory`:
that state must be produced by earlier target operations and their owned
inverses. A typed seed keeps the actual Arc value and starts its own head/depth
history. `seeded_operation` proves the source instruction is defined at this
supported initial state and has the corresponding result and continuation;
this is stronger than only comparing two already-successful primitive steps.
The executable `Source::seed_input` entry invokes this proof and exports the
`initializes` contract directly from the real source. It also reports
`MissingStep` for an index outside the successfully executed prefix.

```rust,ignore
let seed = captured.source.seed_input(0, &target_runtime.execution_journal())?;
// Publish the returned Seed::Scalar or Seed::Payload through the target provider.
// Then instantiate the captured function against those actual target services.
```

This is **not yet a shared replay heap**. Allocating a resource for every input
would break aliases. The scheduler must preserve executable allocation identity,
select the first retained input for each object and obtain later states by real
operations. Current input capture does not prove target service selection,
absence of interference or complete-window execution.

## Use and resource ownership

```rust,ignore
let (mut source_owner, captured) = source_runtime.run_replayable_root(id, execution);
let captured = captured?;
let source_cut = captured.source.bind_control(&source_runtime)?;
let mut target = captured.source.instantiate(&mut target_runtime, Destination {
    parent: None,
    anchor: target_anchor,
    host: (),
    work_domain: fresh_work_domain,
})?;
// Inspect target.report; operate target.owner through its normal lifecycle APIs.
```

The source retains function inputs and captured successful-prefix operands until
dropped, including replacement and pre-write Arc references. This retention is
proportional to the stored function and its executed prefix. This is explicit opt-in retention, with no default invocation change
and no unbounded event buffer. Source deregistration does not discard these inputs.
Control recording retains its own optional capacity and exhaustion policy.

The target inherits the saved realm context. This first executable path requires
exact resolved declaration/port agreement; unsupported parent/alias changes are
rejected before execution. Registration failures return the host. Binding or
Begin failures report the inactive target registration ID for caller cleanup;
they do not promise rollback. An executed report, including a failed prefix,
always returns its real cleanup owner.

## Review and acceptance

| Obligation | Executable/proof path |
| --- | --- |
| Actual retained body and source receipt | `managed_replay.rs`: `run_replayable_root`, `Source::wf` |
| Same complete source cut | `Source::bind_control`, `native_runtime.rs`: `publication_snapshot_following` |
| Fresh target work really enters the interpreter | `registered_root_ready`, `root_ready`, `managed_invocation_ready`, `Source::instantiate` |
| Captured operands and fresh resource initialization | `managed_replay.rs`: `Source::seed_input`; `managed_replay_inputs.rs`: `capture`, `captured`, `initializes`, `seeded_operation` |
| Actual scalar/payload step transport | `managed_replay_transport.rs`: `derive`, `paired`, `TargetRun::pair_step` |
| Target inverses and recovery | Returned `RecordedExecution`, `capture_release_census` |

The runtime cases cover source removal, shifted target IDs, separate resources,
failed-prefix execution on different inputs, real typed cleanup interference,
fresh retry tickets, final recovery capture and pre-execution rejection.
`python3 scripts/check-r3-target-execution-controls.py` separately checks that
skipping the actual interpreter or replacing the retained body with an empty one is
rejected by the designated proof contract.

For the operand-capture increment, the scoped Verus run reported **206 verified,
0 errors across seven affected modules**. All **five managed replay runtime cases**
passed. The cases
include source mutation after cleanup, target execution initialized from actual
retained operands, and refusal to invent outstanding scalar history. The prior
[development record](development-report.json) records an earlier source snapshot;
full development acceptance, the strict negative controls and release acceptance
have not been rerun for this increment. No old pass is promoted to this tree.

## Remaining R3 work

See the [fixed R3-A through R3-D acceptance packages](r3-remaining-work.md) for
dependencies, remaining risks and the current work estimate.


Compose retained invocations and their host operations into the complete selected
Journal execution: derive input correspondence and target reference/ticket maps
across invocations, publication, inverse creation and cleanup; cover general
interleavings, dynamic Child insertion, ownership-based effect selection and
revision/alias changes. The source-command deletion mask does not yet schedule
these target invocations automatically. Opaque callbacks, broader async landing
and the Node protocol need their own transport contracts. This increment does
not claim full-window replay, general Equation (55), global termination or whole
paper completion.
