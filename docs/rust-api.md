# Native Rust application API

[简体中文](rust-api.zh-CN.md)

Available in **`cordis-verus 0.2.0`**, this API provides typed dependency inputs, an
optional application driver, and structured callback errors. Rust applications
need neither Node.js nor Verus installed to execute the library.

Add the library with `cargo add cordis-verus@0.2.0 --rename cordis --features tokio`.
The `tokio` feature is optional; typed dependencies and structured errors are
available with default features. Run the complete example from the checkout:

```sh
cargo run -p cordis-verus --features tokio --example managed_app
```

## Configuration updates (unreleased)

The `ConfigUpdatePlan` API is unchanged. Its actual forward/inverse Futures now
live in a checked owner; Loader retains the real plans across cancellation,
retries failed rollback, and gates accepted revisions on completed updates.
Update targets include the runtime, activation and recipe version. Plugins must
still undo partial application and support retrying failed rollback. See the
[guarantees and proof boundary](r2-configuration-execution.md).

## Loader runtime access (unreleased)

`loader.runtime()` provides read access. `loader.runtime_mut()` returns
`RuntimeAccess`, with the runtime's mutation methods and read-only `Deref`.
This preserves the Loader's connection to its configuration and source Journal;
it no longer allows replacing the entire runtime through `&mut Runtime`.

```rust,ignore
loader.runtime_mut().restart(id)?;
let pending = loader.runtime_mut().settle();
pending.await?;
let checkpoint = loader.execution_snapshot();
```

`settle`, `join`, `replace` and `shutdown` consume the view so their futures can
outlive the temporary view while borrowing the Loader. Existing direct operation
calls remain supported. Helpers that require `&mut Runtime` need an owned Runtime
or a `RuntimeAccess` parameter. Use `loader.runtime()` for borrowed read results
that need to outlive a temporary operation view. The snapshot captures native/configuration/source
proof evidence; histories erase and it is not a serialized audit log. See the
[ownership contract](r2-configuration-execution.md#loader-runtime-ownership-and-joint-observation).

## Mixed native function bodies (unreleased)

`Plugin::native_function(name, instructions)?` stores a finite body containing
`ManagedInstruction::scalar(key, operation, branch)` and
`ManagedInstruction::replace(key, value, branch)`. Typed constructors preserve
the Rust key/value pairing. The builder declares every referenced service,
including unselected branches; no manual `.requires(...)` is needed for them.
Both branch targets must point forward or be `None`. Replacement follows
`matched`; scalar comparison follows its actual result.

Mount the result with `runtime.mount(...)` or `setup.mount(...)` for a Child.
Real root admission, installed recipe versions, effect arguments, return and
successful-prefix cleanup use the checked interpreter. Conflicting inverses
block and retain dependencies until the existing cleanup retry succeeds.

Run `cargo run -p cordis-verus --example managed_function --offline` from the
checkout for a complete conflict/recovery example. The [bilingual case and
proof review path](cases/managed-functions.md) explain the finite body,
shared aliases, cross-Journal histories and callback boundary. No Node runtime
is required; the static host rejects this native-only function body.

## Stored multi-service roots and Child bodies (unreleased)

`Plugin::native_service_program(name, instructions)?` stores the complete finite
body directly in the native registration and derives dependencies from every
instruction. Pass `Vec<ServiceInstruction>` using the same instruction format
below. Mount it with `runtime.mount(...)` or `setup.mount(...)` for a Child.
Registration resolves realms; each operation captures the current service slot.
Successful prefixes keep their real inverses even when the body fails. The
static host explicitly rejects this native-only body.

See [the function-to-code review path](r2-function-semantics.md) for dynamic
aliases, cross-Journal identities, strict recovery and the proof boundary.

## Finite calls across services

Use `setup.run_service_program(&instructions)` from a native root, Child or effect
callback. Each `ServiceInstruction` supplies `key`, `operation` and `branch`.
For example, this updates two declared services and retains both inverses:

```rust,ignore
setup.run_service_program(&[
    ServiceInstruction { key: left, operation: ValueOperation::Add(2),
        branch: ValueBranch { matched: Some(1), unmatched: Some(1) } },
    ServiceInstruction { key: right, operation: ValueOperation::Add(3),
        branch: ValueBranch { matched: None, unmatched: None } },
])?;
```

Declare every referenced key with `.requires(key)` or `.provides(key)`, including
unselected branches. Continuations must point forward within the body. Admission
failure performs no writes; an execution failure keeps prior inverses for the
owner's normal cleanup. Each call resolves its current slot, so aliases and slot
replacement remain supported. Other callers can interleave; the body is not a
multi-object transaction. The API requires the native host. Checked finite steps
do not prove the surrounding arbitrary callback or Future.

## Declare dependencies once

```rust
use cordis::{Plugin, ServiceKey};

let greeting = ServiceKey::<String>::of();
let consumer = Plugin::with_dependencies("consumer", (greeting,))
    .setup(|ctx, (greeting,)| {
        println!("{greeting}");
        ctx.on_cleanup(|| Ok(()));
        Ok(())
    });
```

The same description produces the admission requirements and the `Arc<T>` setup
parameters. `setup_async` accepts an async closure. A single key, `()`, tuples of
up to eight descriptions, and nested tuples are supported. Wrong parameter types
or tuple shapes fail to compile; missing providers wait at runtime.

`key.with_config(json)` supplies the provider's availability predicate input.
Repeated keys share one committed binding. Repeated explicit configurations for
the same key must agree; conflicts are rejected before registration or update.
An unconfigured occurrence shares that key's explicit configuration, if any.
These are required dependencies. Optional observations with separate reload rules
are outside this API.

| Key constructor | Identity |
| --- | --- |
| `ServiceKey::<T>::of()` | Shared by Rust type |
| `ServiceKey::<T>::named("name")` | Shared by type and name |
| `ServiceKey::<T>::new("label")` | Fresh on each call; label is diagnostic |

Shared identities are local to one linked host, not a dynamic-library or process
ABI. `Context::isolate` and `share` still select the realm. The sealed
`Dependencies` trait prevents a third-party description from declaring one set
of keys and resolving another. Additional manual reads remain runtime checked.

## Run an application

Enable Cargo feature `tokio` to use `App`. `App::new()` requires an entered Tokio
runtime; `App::with_handle(&handle)` accepts an explicit executor. One task owns
and polls the existing `Runtime`. The default crate features, typed builder and
manual `Runtime` remain executor independent.

```rust
use cordis::{App, Plugin, ServiceKey};

async fn run() -> Result<(), Box<dyn std::error::Error>> {
    let app = App::new()?;
    let greeting = ServiceKey::<String>::of();
    let consumer = app.plugin(
        Plugin::with_dependencies("consumer", greeting)
            .setup(|_, text| { println!("{text}"); Ok(()) }),
    ).await?;
    let provider = app.plugin(Plugin::new("provider", move |ctx| {
        ctx.provide(greeting, "Hello, Cordis".to_owned())?;
        Ok(())
    }).provides(greeting)).await?;
    consumer.ready().await?;
    provider.update(move |ctx| {
        ctx.provide(greeting, "Updated greeting".to_owned())?;
        Ok(())
    }).await?;
    consumer.ready().await?;
    app.shutdown().await?;
    Ok(())
}
```

Replacing the provider restores affected consumer episodes before releasing the
old provider. A consumer can then initialize again with its new committed
provider. Its cleanup still reads the old committed value. This follows the
existing lifecycle protocol; the facade does not implement a second scheduler
or service registry.

| Operation | Completion / result |
| --- | --- |
| `app.plugin(plugin)` / `plugin_in(context, plugin)` | Registration; returns an application-bound handle, without promising Active |
| `handle.settled()` | Current initialization/restoration is stable, possibly Inactive with missing dependencies |
| `handle.ready()` | Current episode is Active and initialization is stable |
| `handle.dispose()` | Retirement, cleanup and registry removal; retained cleanup failure returns an error |
| `handle.restart()` | Restart the existing recipe and wait for stability |
| `handle.update(...)` / `update_async(...)` | Replace setup with the existing service declarations and wait for stability |
| `handle.update_plugin(plugin)` | Replace a complete recipe, including typed inputs and configuration hook; reject changed declarations or injection configuration before mutation |
| `handle.retry_cleanup()` | Explicitly retry retained cleanup and wait for stability |
| `handle.snapshot()` | Inspect this plugin; `None` after registry removal |
| `app.shutdown()` | Seal admission, retire all plugins, drain and report failures |

`app.scoped(context)` is a view of the same application with a different default
context. `handle.plugin(...)` / `plugin_in(...)` creates an owned child. Disposing
the parent retires its children; ownership does not itself grant service access.
`app.get(key)` / `get_in(context, key)` reads an external snapshot, not a dependency
lease. All scoped views share shutdown and admission state.

Requests enqueue when methods are called. Dropping or timing out a returned
future cancels the wait, not the submitted operation. Handles wait for current
state; concurrent updates may coalesce, rather than each receiving a separate
version transaction. Await each update when intermediate versions matter.
`ready()` can wait indefinitely for a missing provider. Callbacks must not await
their own lifecycle, application shutdown, or disposal of a provider whose
restoration depends on that callback. Tokio must keep running and callbacks must
cooperate for progress. Always await explicit shutdown before stopping the executor.

A consumed one-shot cleanup error is reported but does not prevent drainage.
A retryable cleanup error retains its resources for an explicit retry. A waiting
handle reports its own one-shot errors and retained cleanup failures that block
it; unrelated plugin failures do not fail that handle. `app.cleanup_errors()`
inspects all historical cleanup receipts since the last shutdown report. Shutdown
reports and consumes that history, including errors already observed by a handle.
An error is not a successful restoration acknowledgement.

## Reversible service replacement (unreleased)

Native root and Child callbacks can call `setup.replace_service(key, new_value)`
to replace a declared non-scalar service and automatically retain its inverse.
Cleanup restores the original payload; a later managed write blocks restoration
until that write is restored and cleanup is explicitly retried. Restoration
advances the read revision, so old availability replies stay stale. Ordinary
`set` conflicts are not guaranteed to recover. Use `update_reversible` for
`ReversibleValue`; static storage and arbitrary interior mutations are outside
this API. [Contracts and boundaries](r2-execution.md#reversible-typed-payload-replacement).

## Extensible reversible values (unreleased)

The checkout adds `update_reversible_with` to both `Setup` and `AsyncSetup` for
declared `ReversibleValue` services. For example:

```rust
use cordis::{AsyncSetup, CallbackError, ReversibleValue, ScaleAdd, ServiceKey,
             ThenScalar, ValueOperation, ValueOutcome};

fn adjust(ctx: &AsyncSetup, key: ServiceKey<ReversibleValue>)
    -> Result<ValueOutcome, CallbackError>
{
    ctx.update_reversible_with(key, ThenScalar {
        first: ScaleAdd { scale: 2, offset: 1 },
        then: ValueOperation::Add(3),
    })
}
```

This calculates `2 * value + 4`, checks overflow, then makes one managed write.
`ThenScalar` passes the first actual result into the next calculation;
`ChooseScalar` selects a calculation from its predicate's actual `matched` flag.
The checked owner captures and registers the real inverse automatically, and
existing cleanup restores it or retains an interference failure for explicit retry.

Computation runs outside the host and value locks. Commit rechecks the captured
value/depth and whether the episode/group still accepts acquisition. A changed
state rejects the result; retry is explicit and recomputes from a fresh input.
Exact restoration to the captured state permits commit. A rejected outer call
does not add its own managed write or cleanup entry. Computation panics become
structured panic errors. There is no implicit rollback of extra side effects
performed inside user code.

On the native path, a checked capture binds the declaration and owner before
computation; landing verifies that owner again. A slot replaced during computation
affects later calls. This call and its inverse still target the captured object,
which may remain visible through another alias. Different service names do not
by themselves imply independence. The precise paper mapping is documented in
[native effects and aliases](r2-execution.md#native-extensible-effects-and-the-alias-aware-paper-mapping).

For a new primitive, implement and verify `ScalarEffect`'s model/result contract
as illustrated by [`ScaleAdd`](../crates/cordis-kernel/src/scalar_effect.rs).
There is no need to extend the kernel's fixed operation enum or supply an
inverse. Verus checks the primitive and the generic combinators; implementing
the erased Rust trait alone does not prove arbitrary code. This API currently
covers scalar calculations, not arbitrary service objects or external I/O.
Its proof and remaining integration work are recorded in
[R2 execution contracts](r2-execution.md#extensible-scalar-effects-and-managed-commit).

## Resumable value programs (unreleased)

`start_value_program(key, program)` creates a `ValueProgramCursor` bound to the
current episode/group and captured value. Pass it to `advance_value_program`
to execute one actual instruction: `Ok(Some(outcome))` reports a landed step,
`Ok(None)` means completion, and an arithmetic error leaves the current
instruction ready for explicit retry. Other plugins may write between calls;
the next instruction reads the value then present. Every successful step's
inverse is already retained by the runtime. Dropping the cursor does not undo
the program or discard those cleanup entries.

The cursor exposes its position and last observation, but no mutable code,
target or continuation. A different episode/group or closed owner is rejected.
`cursor.observe()` refreshes its checkpoint, including cleanup and retry; a
snapshot is an observation, not a promise about a subsequent concurrent read.
For an atomic finite program, the existing `run_value_program` holds the value
lock for the whole run. Both APIs are available on `Setup` and `AsyncSetup`.

See the [Child/interference/retry example](../crates/cordis/examples/interleaved_program.rs)
and the [slot/object proof boundary](r2-execution.md#actual-slot-versions-and-shared-object-identity).

`capture_reversible(key)` returns the committed provider, port and a capture with
`revision()` and the actual `Arc<ReversibleValue>`. `cursor.binding()` retains
the selection used to start that program. `set` and `ServiceHandle::set` replace
the live slot; subsequent reads select the new object, while existing cursors
and cleanup inverses continue using the old object. A different port sharing
that old object continues to observe its writes and restoration. A capture is
not a lifecycle lease or extra write permission. Its `refresh()` returns a new
selection without modifying the old one. A capture keeps its slot and original object alive until it is dropped.
Object/slot proof identities and
history are erased; versions are actual nonwrapping runtime counters. They track slot replacement,
not writes inside the selected object.

## Preserve error causes

`CallbackResult` is `Result<(), CallbackError>`. Both `ctx.get(key)` and
`ctx.require(key)` return `ServiceReadError`, and `?` preserves it through setup,
effects, cleanup, `RuntimeError`, `ShutdownError`, and `AppError`.

```rust
use cordis::{AppError, RuntimeError, ServiceReadFailure};

fn inspect(error: &AppError) {
    if let AppError::Runtime(RuntimeError::Setup { plugin, error }) = error {
        if let Some(read) = error.service_read() {
            assert_eq!(*plugin, read.plugin);
            if read.reason == ServiceReadFailure::Undeclared {
                eprintln!("{} was not declared at {}", read.service, read.location);
            }
        }
    }
}
```

A service read error records its reason, key/realm, service and Rust type, owner,
episode generation, committed provider when known, and caller location. Reasons
are `Undeclared`, `ClosedEpisode`, `MissingValue`, and `TypeMismatch`.

`CallbackError::kind()` distinguishes a text message, service read, panic,
cooperative cancellation, external error, and multiple failures. Preserve an
external library error with `.map_err(CallbackError::new)?`; inspect its original
type using `std::error::Error::source()` and `downcast_ref`. String errors use
`.into()`. An effect join keeps each failure in `errors()` when several occur.
Configuration update/rollback callbacks also retain their causes in
`LoaderError::Update`; recovery aggregates keep their source chain.

Errors are cloneable receipts. Built-in errors compare by value; opaque external
causes compare by identity. `failure()` / `cleanup_failure()` retain convenient
text views, while `setup_error()` / `cleanup_error()` return the structured
Runtime cause. Node and process protocol boundaries still transport error text;
Rust error types are not serialized across them. Explicitly converting an error
to a string in application code also discards its cause.

## Migrate from 0.1

- `CallbackResult` now uses `CallbackError`. Replace `Err(String)` with
  `Err(message.into())`; for an existing `Result<(), String>`, use
  `.map_err(Into::into)`. Use `.map_err(CallbackError::new)` to keep a library
  error's original type and source chain.
- `Setup::get` / `AsyncSetup::get` now return `ServiceReadError`. Prefer `?`
  inside callbacks. Call `.to_string()` only at an intentional text boundary.
- Match `RuntimeError::Setup { plugin, error }`, `RuntimeError::Cleanup { plugin,
  error }`, and `LoaderError::Update { entry, error }`; the old `message` field
  is replaced by a structured cause. Configuration update and rollback callbacks
  also use `CallbackResult`.
- Existing `Runtime`, `Plugin::new`, `.requires()` and fresh `ServiceKey::new`
  remain available. Choose canonical `of()` / `named()` explicitly when keys
  should be shared; enable feature `tokio` only when using `App`.

## Connection to the verified kernel

| API step | Existing implementation path |
| --- | --- |
| Dependency description | `typed::Dependencies::declare` → Plugin declarations → Context ports → lifecycle admission |
| Typed setup parameters | `Dependencies::resolve` → `AsyncSetup::require` → this episode's committed bindings |
| App and handle operations | One driver task → existing Runtime mutations/polls → shared lifecycle driver and kernel |
| Failed cleanup / retry | Existing cleanup journal and restoration receipts; errors retain causes without changing their outcome |

These adapters do not grant a new lifecycle authority. Verus proves the kernel
contracts, while compile-fail tests and lifecycle/error regression tests exercise
the ordinary Rust adapters. This is not a proof of the typed builder, Tokio
fairness, arbitrary plugin code, eventual cleanup, or the lifetime of escaped
`Arc` values. See [runtime semantics](semantics.md), the [adoption plan](adoption-plan.md),
and `typed_dependencies`, `app`, and `structured_errors` integration tests.

## Native finite roots and execution domains (unreleased)

Use `runtime.reversible_value(10)` to create checked objects in the native
lifecycle's execution domain. Publish them with the existing `provide` API.
`Plugin::native_value_program("adjust", key, program)` turns a validated
`ValueProgram` into a stored native root. Mount it with `Runtime::mount`, or
with `Setup::mount` as a Child. Its declared dependency is added automatically.
Each successful instruction registers its inverse; a later failure retains the
prefix for the existing cleanup protocol. The finite body is stored directly in
the checked registration; its execution uses the registered dependency realm
and current recipe revision, and root completion comes from its actual result.
`update_plugin` restores the old episode before running the replacement body.
The proof connects each finite instruction to its position in the domain trace.

`value.observe_execution()` pairs the real value with certified joint evidence;
`runtime.plugin_execution_snapshot(id)` observes that current native episode's
work, live cleanup groups, publication ownership, the actual failure/restart
control and managed publication/import/owned slots in one journal read epoch.
It returns `None` before Begin or after Unload. The host keeps its existing
episode mutex while taking this checkpoint. The proof fields are erased and
do not keep old service values alive.

`binding.capture().execution_snapshot()` preserves the captured slot revision
and object commit, even after replacement. Begin captures a shared slot reference;
subsequent reads can observe newer revisions. Both runtime snapshot methods collect
slot evidence before the common read lock without calling user code or retaining
payloads. The checkpoint's proof projection covers every actual service key:
local reversible slots resolve to their current object state, while opaque,
foreign-slot and foreign-object cases remain explicit. It remains coherent when
replacement occurs between receipt collection and the Journal read. A retained
capture's old local object also remains resolvable after replacement; current
slot selection and old-object cleanup are distinct. This does not make a later
runtime read atomic with the checkpoint. See the
[reference contracts](r2-execution.md#local-object-references-and-actual-service-observations).

`effect_handle.execution_snapshot()` and `service_handle.execution_snapshot()`
certify the actual cancellation/initialization/completion and error bookkeeping
in their domain. Effect completion follows checked runner retirement; service
completion is a named host report. A terminal service error can make `join()`
return an error while `finished()` remains false. See the
[shared status contracts](r2-execution.md#actual-shared-handle-status-in-the-execution-trajectory)
for the remaining host-association and scheduling boundaries. Native effect polling
checks its handle's Begin/work origin and exact shared Episode allocation.
`restart(id)` preserves retained cleanup failure; only successful explicit
`retry_cleanup(id)` clears it. Successful Unload clears restart before the next
Begin. See [Episode/control contracts](r2-execution.md#episode-association-and-actual-polling-control).

Cloned `AsyncSetup` handles and nested effects now share immutable context and
mutable Episode through one owner. Native identity, declarations and committed
providers come from the kernel's Begin context; effect admission reads those
bindings in the kernel. Metadata contains no service payloads, so retaining it
does not delay slot release. Static embeddings keep their explicit host binding
contract. Native realm maps and anchors now come from that same registered
Begin. Checked callback scopes identify the actual live queue and are included
in the production plugin checkpoint; stale or foreign scopes cannot register
resources through `AsyncSetup`. Context clones share an immutable realm map.
See [context/scope correspondence](r2-execution.md#registered-realms-and-callback-scopes).

`runtime.execution_snapshot()` captures the lifecycle's domain. History is
erased, so these are proof checkpoints, not serializable runtime audit logs.
Standalone `ReversibleValue::new` remains independent; foreign slot replacements
stay explicit external references. This constructor targets the native runtime.
See [scope and remaining boundaries](r2-execution.md#one-native-execution-domain)
and the [runnable example](../crates/cordis/examples/interleaved_program.rs).

At the kernel integration boundary, `Execution::observe_execution()` returns
`Some(snapshot)` for a native Begin-issued execution and `None` for unlinked
standalone/static owners. It certifies actual work and every live cleanup queue
under one read epoch. `observe_execution_after(&earlier)` additionally preserves
an earlier same-domain program/value history. These proof checkpoints include
real tickets, pending stages, failed cleanup and slot occupancy; arbitrary
callback semantics and the complete host state remain outside the projection.

### Declared scalar observations and writes

`Setup` and `AsyncSetup` expose `observe_reversible(key)` for a checked scalar
snapshot. Native `update_reversible` and `run_value_program` resolve the real
Begin binding inside the verified execution owner. Ordinary root/Child callbacks
and effect groups share this path; inverses enter the caller's actual cleanup
group before success is returned. Existing APIs and static host policies remain
available.

```rust,ignore
let before = setup.observe_reversible(counter)?.value();
let change = setup.update_reversible(counter, ValueOperation::Add(1))?;
// change.before is the actual guarded input; concurrent writers may have
// changed it since the earlier snapshot.
let after = setup.observe_reversible(counter)?.value();
```

Aliased service names observe the same allocation. Replacing one slot can split
those aliases; earlier inverses still restore the old object. The verified frame
uses allocation identity, with an explicit alias-closure premise for a stronger
port-level frame. These managed calls do not prove the surrounding callback.
`update_reversible_with` retains its existing unlocked computation/checked
landing contract. See [declared-call contracts](r2-execution.md#declared-native-calls-and-production-function-steps).
