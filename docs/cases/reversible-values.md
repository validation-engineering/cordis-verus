# Reversible service updates with actual inverse laws

[简体中文](reversible-values.zh-CN.md) · [R2 contracts](../r2-execution.md)

A plugin can update a declared `ReversibleValue` without writing a cleanup
callback. The checked kernel executes the operation, derives the result and
retains the actual inverse in that plugin's cleanup group before returning.
Cleanup succeeds only after the checked inverse restores the value.

```rust
use cordis::{Plugin, ReversibleValue, ServiceKey, ValueOperation};

let limit = ServiceKey::<ReversibleValue>::new("configuration limit");
let plugin = Plugin::new("temporary increase", move |setup| {
    let result = setup.update_reversible(limit, ValueOperation::Add(5))?;
    println!("{} -> {}", result.before, result.after);
    Ok(())
}).requires(limit);
```

The provider publishes `ReversibleValue::new(10)` using the ordinary
`setup.provide` API. Cloned values share the same checked lock. Available
operations are replacement, checked addition, XOR and compare/exchange.
`ValueProgram::new` additionally accepts finite programs with forward-only
branches selected from the actual comparison outcome. `run_value_program`
executes a complete program under the value lock and registers its inverses in
execution order. An overflow reports failure; every already executed operation
remains registered for cleanup. Empty programs are valid; invalid branch targets
are rejected before execution.

## Reproduce the failure and recovery

```sh
cargo run -p cordis-verus --example reversible_values
```

The example runs three real plugins:

1. A provider publishes `10`. Two consumers change it to `15`, then `22`.
2. The first consumer retires. Its inverse is blocked by the later write; the
   value remains `22`, and its inverse and dependencies remain retained.
3. Retiring the provider withdraws the second consumer. Its cleanup restores
   `15`. The provider remains retained because the first cleanup still failed.
4. `runtime.retry_cleanup(first)` restores `10`. The provider can now release.

A dependency withdrawal leaves its consumer registered and inactive; it does not
implicitly retire that consumer. The example checks this distinction.

## Paper-to-code review path

| Obligation | Actual code and proof |
| --- | --- |
| An operation returns a value, outcome and a true partial inverse | [`Cell::forward`, `operation`, `primitive_theory`](../../crates/cordis-kernel/src/reversible_value.rs) implement and prove the scalar premise used by the dependent grammar for Definition 30 and Lemma 39 |
| Results select the actual continuation | `Branch::select` and [`ReversibleValue::run`](../../crates/cordis-kernel/src/value_program.rs); no expected outcome is supplied by the host |
| Every installed program root and continuation has Component membership | `Program::member` and `Program::component` instantiate the full finite strict carrier from [R1](../r1-semantics.md), rather than a successful-input-only carrier |
| The observed value comes from the state that ran | The real `vstd::RwLock` holds `ValueState { value, depth }` and its ghost execution history; `snapshot` reads those actual fields while holding the lock |
| The inverse is the one produced by the actual operation | [`Execution::apply_value` and `run_value_program`](../../crates/cordis-kernel/src/execution.rs) retain real inverse objects; the program implementation is in `value_program.rs` |
| Cleanup cannot substitute another inverse or simply report success | [`CleanupQueue::dispatch`](../../crates/cordis-kernel/src/cleanup_completion.rs) selects, executes and acknowledges the actual stored inverse in one checked call |
| Failed restoration preserves recovery data | A blocked inverse remains in its original cleanup slot; the queue is failed, and the existing checked retry protocol produces the next attempt |
| A complete history corresponds to source steps | `history_interpretation` classifies every recorded write, successful inverse and rejected attempt; `ProgramReport::source_execution` constructs a contiguous dependent-grammar trace for the actual complete program or failing prefix |

The inverse's function is interpreted on **every input**: it returns the captured
pre-state exactly when the current `(value, depth)` equals its captured
post-state. The observation includes depth, so writing the same value again
still blocks an older inverse. Inverses are linear, have private fields, retain
their original shared target and cannot be cloned or redirected to another
value. Depth is a nesting level; it is not a globally unique revision number.

The trace is constructed in the implementation. Callers supply neither a source
execution nor an expected transcript. Ghost history is erased from Cargo builds;
there is no growing runtime audit log. Programs store their real code, outcomes
and inverses. No user callback runs under the value lock.

## Scope and remaining work

This is a production primitive and program path, used by both native Runtime and
the static Rust host. It proves the actual stored `u64` value's effect law; it
extends the earlier contracts that tracked opaque callback results and handles.
Its source interpretation is the dependent value grammar used by R1. It does
**not** interpret the entire Runtime registry as R1's recursive context.

Ordinary Rust closures, JavaScript objects, I/O, availability predicates and
external schedulers retain their existing boundaries. This API does not verify
the whole callback containing the call, expose these operations to Node, or
promise eventual restoration after interference. The complete host invariant,
its function fields, dynamic Child/publication composition and classification
of the entire native/Node trace remain R2 work. The existing three R2 exit
conditions and original-paper audit statuses remain unchanged.

The regression suite checks the primitive, concurrent access, same-value
interference, program branching and failing prefixes. Real Runtime tests check
retained dependencies, explicit retry, rejected escaped contexts and the static
host. Five compiling negative controls change result selection, ignore depth,
discard the real inverse, turn a failed restore into success or skip the actual continuation; each must be
rejected at its reviewed contract. Scoped evidence is separate from the complete
negative regression and release acceptance.
