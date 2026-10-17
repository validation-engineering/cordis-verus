# Checked functions with mixed effects

[简体中文](managed-functions.zh-CN.md) · [Rust API](../rust-api.md) · [R2 function semantics](../r2-function-semantics.md)

A stored native function can update a reversible scalar, replace a typed service
value, and choose its next operation from the actual result. The same checked
interpreter runs roots and Child bodies. On failure, successful operations keep
their exact inverses in the owner's real cleanup queue.

This is the first R2 delivery package: **finite managed function bodies with
mixed scalar and typed effects**. It connects the paper's operation,
continuation and inverse laws to code that users execute. It does not complete
the separate whole-host, Node or configuration refinement packages.

## Try it

From this checkout, with the project's Rust toolchain and cached dependencies:

```sh
cargo run -p cordis-verus --example managed_function --offline
```

The [example](../../crates/cordis/examples/managed_function.rs) executes a mixed
function, introduces a conflicting replacement, observes blocked cleanup and
provider retention, then restores the later writer and retries successfully.
It needs neither Node.js nor a Verus installation to run.

The unreleased API uses typed instruction constructors:

```rust,ignore
use cordis::{ManagedInstruction as I, Plugin, ValueBranch, ValueOperation};

let finish = ValueBranch { matched: None, unmatched: None };
let plugin = Plugin::native_function("request policy", vec![
    I::scalar(budget, ValueOperation::CompareExchange { expected: 10, value: 13 },
        ValueBranch { matched: Some(1), unmatched: Some(2) }),
    I::replace(label, "selected".to_owned(), finish),
    I::replace(label, "unmatched".to_owned(), finish),
])?;
let id = runtime.mount(&context, None, plugin)?;
runtime.settle().await?;
```

Here `budget` is a `ServiceKey<ReversibleValue>` and `label` is a
`ServiceKey<String>`. For a Child, pass the same plugin to `setup.mount(plugin)`.
`native_function` derives dependencies from **every** instruction, including
unselected branches. A continuation must point forward within the body or be
`None`; typed replacement selects `matched`. Existing provider and ordinary
callback APIs remain available. This body requires the native runtime; static
host dispatch returns an explicit error.

## Guarantees and review path

| User guarantee | Real execution | Paper/proof connection |
| --- | --- | --- |
| Run the installed body with its real keys and arguments | `Function::bind`, `run_managed_root` | Registered recipe, version and owner are checked; all declared keys are resolved before root issuance. Direct calls also reject substituted keys. |
| Select the continuation from the actual outcome | `Execution::run_function`, `execute_call` | `Step::interpretation` connects the concrete write, result and next instruction to Definition 29 / equation (31) and Definition 30. Both branches participate in the full-carrier grammar theorem. |
| Restore the exact successful prefix, including mixed effects | Actual scalar and typed inverse registration | `Report::interpret_queue` equates the real queue suffix with the strict semantic inverse on every recovery heap. `recoverable` derives round-trip recovery when the actual forward states compose; inverse success is not a premise. |
| Do not skip a blocked inverse or release its provider early | Existing checked cleanup dispatch and retry protocol | `next_inverse` connects the real LIFO selection to the last scalar or typed step; failed cleanup retains its inverse and committed dependencies. |
| Preserve real causality through local/foreign/local calls | `Journal::join_receipts`, actual locked observations and writes | Every earlier same-Journal write and inverse registration precedes the later write, even when another Journal intervenes. `execution_interval` connects these witnesses to the real invocation return. |
| Report the real failure without losing the prefix | Capture/read guards, scalar rejection receipts and locked typed rejection observations | `Failure::explained` distinguishes kind/availability, stale-computation, capacity and retired-payload failures. A rejected scalar attempt preserves the complete recorded state and pending obligations. |

The executable interpreter is [managed_function.rs](../../crates/cordis-kernel/src/managed_function.rs),
the universal operation/function laws are in
[managed_semantics.rs](../../crates/cordis-kernel/src/managed_semantics.rs),
and the actual queue/trace connection is in
[managed_trace.rs](../../crates/cordis-kernel/src/managed_trace.rs).
[managed_root.rs](../../crates/cordis-kernel/src/managed_root.rs) is the entry
called through the driver by the ordinary Rust host. These files are both Verus
inputs and Cargo-compiled production source; there is no substitute interpreter
used only for proofs.

## Exact semantic scope

The primitive carrier is a sum of scalar states and typed payload states. Typed
replacement tracks the actual `Arc<T>` identity, reversible head/depth and
strict inverse; its independent monotone revision prevents stale read checks
from becoming valid after restoration. Arbitrary `T` interiors and destructor
behavior are outside that interpretation.

The kernel is generic over verified `ScalarEffect` implementations, not just the
host's `ValueOperation` enumeration. The kernel acceptance case uses `ScaleAdd`
with typed replacement. An additional effect family must supply its own
forward/inverse laws and connect actual admission, storage and cleanup before
it joins this interpreter; an arbitrary Rust trait implementation or callback
does not acquire those guarantees automatically.

`Function::member` covers all semantic inputs, both branches and every explicit
resolution/fresh-head schedule. `Function::component` gives the corresponding
named-port Component law under its declared footprint. Actual reports instantiate
the allocation interpretation using real captures, results and retained inverses.
An allocation address includes **both Journal and object key**.

Aliases are explicit: writing a shared allocation affects every name that
selects it, while unrelated names are preserved. `single_key_projection` lifts
the actual write to the paper's literal single-name rule only when no other
current name selects that address. This condition is not inferred from Rust
key types. Resolution can change between instructions, and each inverse keeps
its original allocation. No unconditional original-carrier independence is
claimed for conflicting aliases.

A function is not an atomic multi-object transaction. Interleavings remain in
authenticated histories; foreign Journals remain separate. The strict inverse
may block on a later conflicting write. Recovery is guaranteed on a composing
forward history, not despite arbitrary conflicting mutations. Successful
returns and failed prefixes are both covered, without promising eventual
async scheduling or cleanup completion.

Proof witnesses and histories erase from the runtime artifact. Runtime reports
retain only the concrete finite result data; this adds no persistent execution
log. Dynamic publication and Child creation are not instructions in this
function language: a Child's **body** can use it, while the surrounding
registration/lifecycle protocol keeps its existing contracts.

## Delivery checks

The integrated acceptance cases are in
[kernel tests](../../crates/cordis-kernel/tests/managed_function.rs) and
[host tests](../../crates/cordis/tests/managed_function.rs): mixed roots and
Children, true/false continuation selection, aliases, local/foreign/local
causality, changed recipe arguments, rejected undeclared/substituted keys,
wrong owners, repeated invocation, retired storage, failed-prefix recovery,
cleanup conflict/retry and static-host rejection.

Four added canonical mutations challenge this connection: omit effect witnesses
at the real return; stop instead of taking the selected continuation; fabricate
a closed-episode read failure; and omit prior causes from a typed write. Each
requires a fresh matching positive, complete mutant compilation and the exact
reviewed function/diagnostic/source-anchor rejection. Compilation errors,
timeouts and solver limits are not accepted evidence.

[Development evidence](../development-report.json) records source hashes,
whole-kernel proof, workspace/Node regressions and packaging checks. Reproduce
the complete development acceptance with
`python3 scripts/record-development.py --offline`; full mutation regression is
separate (`python3 scripts/check-negative.py`). Selected negative checks are
not full-negative or release acceptance.

The remaining R2 work concerns the complete host observation and alias-to-Episode
association; full Node object/Fiber/HMR and configuration/source meaning; and
whole-host step grouping and final joint acceptance. Arbitrary callback effects
require explicit verified contracts. These are tracked in the
[refinement plan](../paper-refinement-plan.json), rather than counted as completed
by this finite-function package.
