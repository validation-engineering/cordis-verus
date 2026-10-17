# Stored functions and dynamic service resolution

[简体中文](r2-function-semantics.zh-CN.md) · [R2 progress](r2-execution.md) · [Rust API](rust-api.md)

The first R2 function package now also supports **mixed scalar and typed
replacement effects** through `Plugin::native_function`. Its stored root/Child
body has a full-carrier function interpretation, actual outcome-selected
continuations and the same strict mixed inverse queue used by cleanup. See the
[complete package, runnable example and proof boundary](cases/managed-functions.md).

The native runtime can store a complete finite multi-service function directly
in its registration. `Plugin::native_service_program` works as a root or a Child;
it derives dependencies from every instruction, including unselected branches.
The executable Verus interpreter runs the stored body and retains every
successful inverse. This is an unreleased R2 implementation, not whole-R2 acceptance.

```rust,ignore
let plugin = Plugin::native_service_program("adjust", vec![
    ServiceInstruction { key: left, operation: ValueOperation::Add(2),
        branch: ValueBranch { matched: Some(1), unmatched: Some(1) } },
    ServiceInstruction { key: right, operation: ValueOperation::Add(3),
        branch: ValueBranch { matched: None, unmatched: None } },
])?;
runtime.mount(&context, None, plugin)?;
```

Each instruction captures the current allocation of its Begin-bound service
slot. Different names may alias; a replaced slot may select a new allocation on
the next instruction. Each inverse retains its original allocation. Other
callers may interleave, so a body is not a multi-object transaction. Static host
dispatch rejects this native-only body explicitly.

## Production review path

| Concern | Actual implementation and contract |
| --- | --- |
| Stored function identity | `Body::Services(Function)` in [value_function.rs](../crates/cordis-kernel/src/value_function.rs); no opaque callback substitutes for this body |
| Declaration and realm binding | `Function::bind` in [service_function.rs](../crates/cordis-kernel/src/service_function.rs) resolves every stored key through the registered recipe, preserving operations and branches; the first registered match takes precedence over inherited aliases |
| Admission and completion | `NativeRuntime::run_service_root` checks the actual owner, lifecycle admission and current recipe; its real execution result determines root failure and completion |
| Actual calls | `Execution::run_service_program` in [service_program.rs](../crates/cordis-kernel/src/service_program.rs) resolves each slot, executes the actual operation and registers its inverse before continuing |
| Whole finite interpretation | [service_composition.rs](../crates/cordis-kernel/src/service_composition.rs) proves grammar membership for every resolution schedule and relates the actual success/failure report to its selected schedule |
| Accumulated inverse | [service_stack.rs](../crates/cordis-kernel/src/service_stack.rs) identifies the semantic reverse stack with the actual queue suffix, including failed prefixes |
| User-visible path | `Plugin::native_service_program`, native initialization and Child registration in [runtime.rs](../crates/cordis/src/runtime.rs), through [native.rs](../crates/cordis-driver/src/native.rs) |

Missing declarations, including those in unreachable instructions, are rejected
before root issuance. Wrong owners and retired/already-issued roots do not run.
A successful admission can still return an execution failure; the root then
settles as failed while preserving the exact successful-prefix inverse queue.
Ordinary callbacks can call `run_service_program` and receive the same body-level
contracts, without acquiring a proof for their surrounding callback code.

## Paper interpretation and its limits

Definition 29, equation (31), specifies a single context-binding operation with
an actual outcome and inverse. Definition 30 composes outcome-selected
continuations. Two aliased service names do not satisfy a literal single-name
write rule without additional conditions. This implementation therefore makes
resolution an explicit input and interprets effects on qualified allocations.

`Address { journal, key }` uses the real Journal identity, not just its local
numeric allocation key. `resolved_member` proves least-grammar membership for
every finite body's resolution schedule and all inputs in that allocation
carrier. `interpret_dynamic` instantiates it from actual captured bindings and
authenticated write/rejection receipts. Both possible branches participate in
the universal theorem; the actual result chooses the executed continuation.
The failed instruction resolves to its actual rejected allocation, and its
operation has an empty result on the recorded input. That rejection preserves
the complete recorded state and pending-obligation map.

This is a parameterized allocation interpretation of the complete finite body.
It does not prove unconditional Component membership for dynamic aliases on the
paper's original named-port carrier, nor infer fixed declared-port independence.
The earlier singleton-alias condition still controls that literal specialization.
The service lookup input is not silently treated as a fixed value across all
executions or across slot replacements.

`interpret_queue` connects the actual queue suffix to the exact strict reverse
stack on **every** recovery heap. `roundtrip` then proves recovery of any input
whose recorded forward before/after states compose. It does not assume inverse
success, reinterpret a blocked inverse as success, or promise recovery despite
a conflicting external write. Shared aliases and distinct Journals are both
represented in this stack. The producer also proves that the actual waiting queue appends exactly the
recorded instruction tokens. `CleanupDispatch::selected_from` exports the real
pop rule: a retry keeps its selected ticket; a new restore selects the last
waiting token. `next_queued_inverse` connects that returned dispatch to the
last actual prefix inverse. This composes storage, scheduling and payload
identity without assuming a synthetic LIFO list or eventual cleanup completion.

Within one Journal, the existing `source_trace`/`failed_trace` results retain all
interleaving events. Cross-Journal calls retain separate histories and qualified
addresses; no common atomic snapshot or total order is fabricated. Slot
selection, write, inverse registration and root completion remain distinct
implementation steps.

## Effects joined to the actual invocation return

The stored finite Value and Service bodies now retain authenticated witnesses
for their actual writes and inverse registrations. A Service failure retains
the actual rejected attempt; a Value report retains its actual complete object
observation, including a rejected final instruction. `record_recipes_following`
checks these witnesses against the authoritative Journal in the same write epoch
that records the real `Call` return. The report returns that commit's receipt.

`RegisteredReport::execution_interval` connects the existing operation and
inverse interpretation to this concrete return event:

- Every same-Journal write and inverse registration strictly precedes the return.
- A same-Journal failed attempt or failed Value observation also precedes it;
  returning failure does not erase the successful prefix or its inverses.
- Interleaving events remain in the common prefix. The steps need not be adjacent.
- Foreign value histories keep their own Journal identity. A local inverse
  registration is still included even when its forward write belongs to a
  foreign Journal; no cross-Journal total order is inferred.

The witnesses are collected by the actual interpreters, not supplied by an
ordinary host callback. They are persistent proof resources and erase from the
runtime artifact, including their maps and Journal references. The existing
bounded Journal commit is reused; this does not add a runtime effect log.

Review `Evidence::retain` in [value_registration.rs](../crates/cordis-kernel/src/value_registration.rs),
the actual producers in [value_program.rs](../crates/cordis-kernel/src/value_program.rs)
and [service_program.rs](../crates/cordis-kernel/src/service_program.rs), and
`record_recipes_following` in [native_runtime.rs](../crates/cordis-kernel/src/native_runtime.rs).
The two registered root entry points supply those actual reports and expose the
return interval theorem. This strengthens the implementation connection for
Definitions 29–30; it does not add a general callback law, original-carrier
Component theorem, or eventual-return guarantee.

## Evidence and remaining work

Two additional compiling mutations omit the actual Value/Service report
witnesses at the real invocation return. Both are rejected by the return
contract even though the function still computes and returns its actual result.

The integrated cases cover actual stored root/Child dispatch, explicit realms
before inherited aliases, two names for one allocation, another provider with a
foreign Journal, failed-prefix restoration, replacement recipe revisions,
repeated/retired/wrong-owner rejection, empty bodies, malformed branches and
static-host rejection. See [kernel cases](../crates/cordis-kernel/tests/registered_value_function.rs)
and [host cases](../crates/cordis/tests/reversible_runtime.rs).

Selected compiling negative controls cover substitution of the stored
operation, loss of the Journal qualifier, reversal of the interpreted stack in
the wrong order, taking the oldest actual cleanup token, and discarding the
final failure from a successful prefix. The binding, actual cleanup-stack and failed-prefix mutations change
runtime code; the address and interpreted-inverse mutations change the semantic
interpretation used by producer contracts. [R2 progress](r2-execution.md) records
the final source-bound checks and exclusions.

The mixed-function package extends this scalar-only path with typed replacement
and a parameterized full-carrier Component law. General callback bodies, new
effect families without verified laws, unconditional original-carrier composition
for conflicting aliases, Node object/version and
dynamic-interface semantics, configuration expansion, structural component
actions/reconstruction and persistence remain open. Actual in-place update and
inverse ownership now have [checked configuration contracts](r2-configuration-execution.md);
their whole-tree/joint observation is still incomplete. No paper-wide completion or arbitrary
callback/Future proof follows from this result.

## Non-scalar replacement primitive

Ordinary root/Child callbacks can now call `replace_service` to run a concrete
typed replacement and retain its checked inverse in the actual cleanup group.
The primitive has a full semantic-carrier operation/inverse law and a composing
reverse-stack theorem. `Plugin::native_function` now combines it with scalar
effects in a stored outcome-selected body, with explicit resolution/alias
conditions on its Component interpretation. Arbitrary surrounding callback
code remains outside that body theorem. See
[typed replacement and version separation](r2-execution.md#reversible-typed-payload-replacement).

The actual typed inverse now joins issue, locked observation, optional restoration
and acknowledgement in one authenticated protocol. Its interval retains all
interleavings and rejects reactivation of the completed ticket; see
[typed cleanup intervals](r2-execution.md#typed-cleanup-issue-read-and-acknowledgement).
The [mixed-function package](cases/managed-functions.md) now joins these
primitive effects to the actual registered invocation return. Whole-host step
grouping and arbitrary callback meaning remain separate obligations.
