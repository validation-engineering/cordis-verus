# Cordis native plugin SDK

Experimental version 1 C ABI for Rust plugins loaded by a resident Cordis host.
The host and each plugin compile independently. Library images remain mapped
for the process lifetime; replacing a plugin does not unload native code.

```rust
use cordis_plugin_api::{Module, PluginFactory};

// Implement PluginFactory and PluginInstance for your plugin.
// fn module() -> Module { Module::new("example.text", "1").factory(TextFactory) }
// cordis_plugin_api::export_plugin!(module);
```

See `examples/shared/mod.rs` and `examples/dynamic_fixture_v1.rs` for a complete
factory with synchronous and asynchronous services. Build a plugin as `cdylib`.
`PluginFuture` and `Arc<dyn PluginInstance>` are ordinary Rust values inside the
plugin; neither crosses the library boundary. `PluginContext::cancelled()`
provides cooperative cancellation. A cancelled job is still polled until its
future actually returns, then dropped by its creating library.

Version 1 supports setup, cleanup, JSON synchronous/asynchronous methods,
declared asynchronous JS service calls, streams, objects and callbacks,
Rust-owned streams and objects, dynamic provider publication and child plugins,
explicit versioned JSON checkpoints, and configuration-based state reconstruction.
The Node host sends `args` as the JSON
array of positional JavaScript arguments; the plugin defines each method's argument
schema. Arbitrary cross-library Rust values are not part of this ABI. Unsupported method
kinds cannot be described. Injection names must be nonempty and unique. The host validates
descriptors as well.

## Wire and ownership contract

The exported `cordis_plugin_v1` symbol returns a permanent `PluginApiV1` pointer.
Its C-layout header contains `CRDSPLG1`, ABI version 1, the complete table size,
and `invoke`. Host and plugin must use the same architecture and native C ABI.
The host checks the header before reading the function pointer. This is a
trusted native plugin interface, not a memory safety sandbox.

`invoke(request, length, output, context, wake)` accepts at most 1 MiB of JSON.
The host owns the request bytes, which remain readable during the call. The
plugin invokes `output(context, bytes, length)` synchronously exactly once on
status 0; output bytes are borrowed only during that callback and must be
copied by the host. Invalid pointer/length combinations return status 1 without
an output. Non-null invalid pointers cannot be validated by the SDK and violate
the C ABI contract. Responses are bounded to 1 MiB; individual values to 512 KiB.
Result arrays/objects may nest at most `MAX_VALUE_DEPTH` (64) containers. The
SDK checks depth before serialization and before committing a ready result, so
`ValueTooDeep` is a normal job error that can still be consumed and cleaned up.
This reserves space for protocol wrappers under the host JSON recursion limit.
No allocator or Rust destructor crosses this boundary.

`WakeV1` contains a `u64` token and permanent host `extern "C" fn(u64)` trampoline.
The plugin constructs its own Rust waker. The host trampoline must never unwind,
remain callable for the process lifetime, and ignore expired tokens. Output
callbacks also must never unwind. Module constructors must not reenter their own
lazy initialization. The host retains images while any code could refer to them.

Every response has exactly one of `{ "ok": value }` or `{ "error": string }`:

| Request `op` | Other fields | Success value |
| --- | --- | --- |
| `describe` | — | `{ module_id, version, factories, checkpoint_schemas }` |
| `create` | `factory`, `config` | `{ instance }` |
| `setup`, `cleanup` | `instance` | `{ job }` |
| `checkpoint` | `instance` | `{ schema, version, data }` |
| `restore` | `instance`, `checkpoint` | `null` |
| `call_sync` | `instance`, `service`, `method`, `args` | `{ value }` |
| `call_async` | `instance`, `service`, `method`, `args` | `{ job }` |
| `poll` | `job` | `{ state: "pending", calls?: [...], draining?: true, queuedCalls?: true }` or `{ state: "ready", result: { ok } / { error } }` |
| `resolve_call` | `job`, `request`, `result: ReverseResult` | `null` |
| `cancel`, `drop_job` | `job` | `null` |
| `destroy` | `instance` | `null` |

Handles are opaque, positive, monotonically allocated, never reused and never
wrapped. They are scoped to the originating library runtime. `poll` consumes a
ready result once. `drop_job` is required after that result and rejects pending
or faulted futures. `cancel` only requests cancellation. Cleanup requires all
prior jobs to have landed and been dropped. A failed cleanup can be retried.
Destroy requires successful cleanup and no jobs; an instance never set up can
also be destroyed because creation must have no external effects.

`create` must be free of external effects. Acquire resources during setup and
retain enough state for cleanup even when setup fails. Successful cleanup means
all resources and background tasks are actually drained. The SDK enforces its
job table and lifecycle protocol, but cannot verify arbitrary plugin I/O or
threads. Unwind panics are caught at the boundary; affected instances/jobs remain
faulted and cannot be declared cleaned or destroyed. Faulted jobs and custom
panic payloads can remain retained until process exit. Abort, invalid memory,
foreign exceptions and unwinding through host callbacks are outside containment.

SDK global table locks are released before user instance code. Concurrent or
reentrant polling of one job returns `JobBusy`; conflicting instance operations
return `InstanceBusy`. Plugin futures must be nonblocking, as with any executor.

## Declared calls back into JavaScript

Declare the dependency in `FactoryDescriptor.inject`, then call it from an
asynchronous setup, method or cleanup action:

```rust
# use cordis_plugin_api::{PluginContext, PluginResult};
# use serde_json::{json, Value};
async fn normalize(ctx: PluginContext, text: String) -> PluginResult<Value> {
    ctx.call("textPolicy", "normalize", json!([text])).await
}
```

`args` must be an array of positional JSON arguments. The host uses the original
Cordis action to execute the call against its committed JS provider, including
during cleanup. Ordinary actions reject newly requested work after cancellation;
cleanup actions can still call their retained dependencies. Every action closes
new admission when its main future returns, so a cloned context cannot extend
its authority. A call enqueues on its first poll; an unpolled future does nothing.
Dropping an already-polled call future never cancels the real JS operation.

`poll` delivers each queued call exactly once as
`{ request, kind: "call", service, method, args }`. Request IDs are scoped to the job, never
reused, and acknowledged with `resolve_call`. Unknown, duplicated and not-yet-
dispatched acknowledgements fail. The SDK stores the main future's result and
waits until every queued and dispatched call is actually acknowledged before
returning Ready, even when the plugin dropped those call futures. The host must
continue polling and dispatching batches while earlier JS calls remain pending.

At most 64 calls may be outstanding per job. Each call and each emitted batch is
bounded to 512 KiB of encoded JSON including the call fields and batch overhead;
new admission beyond capacity returns an error before dispatch. Argument/result
nesting obeys the 64-container bound. Results above size/depth limits become
normal call errors that preserve completion and cleanup. Before constructing
`resolve_call`, the host must normalize excessively large/deep JS results to an
error so the response itself fits the outer ABI request and parser limits.

The examples additionally export `native-js-consumer`, injecting `jsHost` and
providing `nativeJs.call({ method, args, service? })` plus `nativeJs.dropped(...)`.
Setup and cleanup await `jsHost.record([{ phase, version }])`. These exercise
cross-language dependency cleanup and draining discarded call awaiters; they do
not provide a second lifecycle graph or hide capabilities inside JSON values.

## Importing JavaScript resources

Use `ctx.open_stream(service, method, args)`, `open_object(...)` or
`open_callback(...)` for explicitly adapted JS resources. All are asynchronous
and require a declared injection and an array of JSON arguments. The returned
`JsStream`, `JsObject` and `JsCallback` are private action-scoped capabilities:
they cannot be constructed from a number or serialized into a JSON argument.
Cloning a capability does not extend its opening action's lifetime.

```rust
# use cordis_plugin_api::{PluginContext, PluginResult};
# use serde_json::{json, Value};
async fn consume(ctx: PluginContext) -> PluginResult<Value> {
    let stream = ctx.open_stream("source", "chunks", json!([])).await?;
    let counter = ctx.open_object("source", "counter", json!([])).await?;
    while let Some(chunk) = stream.next().await? {
        counter.call("append", json!([chunk])).await?;
    }
    let result = counter.call("read", json!([])).await?;
    counter.close().await?;
    stream.close().await?;
    Ok(result)
}
```

`JsObject::descriptor()` exposes the validated interface and captured ownership;
only its declared methods are callable. `JsCallback::invoke(args)` calls exactly
`call`; opening a callback with any other descriptor fails. Stream `next()`
returns `Option<Value>`, preserving a JSON null item separately from EOF.
Only one pull may be pending; object calls may overlap. Explicit `close()`
returns `StreamBusy` or `ObjectBusy` while operations remain pending, preventing
self-joining call chains. Close remains allowed after cancellation, and a failed
close can be retried within the action without reopening business operations.
A successfully closed capability allows idempotent close while its action lives;
after that action finishes, even a retained clone returns `ActionClosed`.

The resident action journal owns final release, including early returns,
forgotten capabilities, dropped opening futures and dropped pull/call futures.
An operation accepted on first poll still waits for its real JS acknowledgement.
Failed automatic close remains visible for lifecycle cleanup retry; it does not
become successful merely because the Rust awaiter was dropped. Owned objects run
the JS disposal hook; borrowed references do not dispose the external referent.
At most `MAX_REVERSE_RESOURCES` (1024) resource acquisition attempts may be
admitted per action, including failed opens; failed attempts never reset the
budget or permit handle reuse.

The same batch queue uses exported `ReverseCall` and tagged `ReverseOperation`:

| `kind` | Additional fields | Successful `resolve_call.result` |
| --- | --- | --- |
| `call` | `service`, `method`, `args` | `{ ok: value }` |
| `stream_open` | `service`, `method`, `args` | `{ stream: u64 }` |
| `stream_next` | `stream` | `{ item: { done: true } }` or `{ item: { done: false, value } }` |
| `stream_close` | `stream` | `{ ok: null }` |
| `object_open`, `callback_open` | `service`, `method`, `args` | `{ object: u64, descriptor }` |
| `object_call` | `object`, `method`, `args` | `{ ok: value }` |
| `object_close` | `object` | `{ ok: null }` |

Every operation can instead receive `{ error: string }`. Typed resource replies
are validated against the outstanding operation; a JSON `{ ok: { stream: ... } }`
never grants capability authority. Host resource handles are positive and never
reused within a job. Descriptor, item and method-result limits are checked before
adding protocol wrappers, so oversized or deep values still land as normal
errors and permit cleanup.

When the body returns, `poll` closes admission and includes `draining: true`
until all reverse replies land. `queuedCalls: true` means later batches remain
undelivered. The host must dispatch the current batch and wait until no queued
batch remains before starting the resident journal. It may then return streams
concurrently with pending pulls: `return()` can be what unblocks `next()`. Object
disposal still joins actual calls. SDK Ready and host action completion remain
separate obligations; native cleanup/resource-close success is not acknowledged
as final destruction until the host journal really finishes.

`examples/shared/reverse_resources.rs` exports `native-js-resources` with
`nativeJsResources.stream`, `object`, `callback`, dropped-await and escaped-clone
regressions. Setup/cleanup record their version through `jsHost.record`; optional
`cleanupStreamArgs` / `cleanupObjectArgs` acquire resources during cleanup to
exercise failed journal retry without rerunning an already-successful hook.

## Dynamic publication and child plugins

`ctx.mount(factory_name, config).await` mounts a factory already exported by the
same original module. `ctx.publish(factory, config).await` accepts any local
`impl PluginFactory`, retains its definition inside this library, and installs a
real provider child in the existing Context graph. Its descriptor may declare
dynamic service names. The host never receives a Rust factory pointer: it reads
the SDK's validated descriptor snapshot and requests `create_child` for each
activation. Each activation calls `PluginFactory::create` again; captured factory
state remains available until the actual child is removed.

Both operations return a `ChildHandle` after graph allocation, which may precede
service readiness. In a later action of that same instance:

```rust
# use cordis_plugin_api::{ChildHandle, PluginContext, PluginFactory, PluginResult};
# use serde_json::json;
async fn publish_from_active_action(
    ctx: &PluginContext,
    factory: impl PluginFactory,
) -> PluginResult<ChildHandle> {
    let child = ctx.publish(factory, json!({})).await?;
    child.initialized(ctx).await?;
    Ok(child)
}
async fn retire_and_wait(ctx: &PluginContext, child: &ChildHandle) -> PluginResult<()> {
    child.dispose(ctx).await?; // Retirement request acknowledged.
    child.join(ctx).await     // Actual graph removal acknowledged.
}
```

`status(ctx)` returns `ChildStatus { id, initialized, retiring, removed,
cleanup_failed, error }` (`cleanupFailed` on the wire). `id` is the actual graph
node ID as an optional decimal string; it is diagnostic metadata, not authority.
`initialized` describes the current active state, so it may become false during
a dependency restart. `retry_cleanup(ctx)` explicitly retries failed cleanup and
awaits the host's actual outcome. Failures remain visible instead of becoming
removal acknowledgements. The host rejects joins that would wait for their own
active caller or owner initialization.

Unlike JS stream/object imports, child handles belong to the entire creating
instance episode. They can be stored and cloned, but each operation requires a
live `PluginContext` from that same instance. Another instance, a later restart,
or an escaped completed action cannot use that authority. Dropping either the
handle or an already-polled creation future does not retire the graph node.
Its parent remains responsible for graph cleanup, including late allocation
acknowledgements. Cleanup actions may inspect, retire and join existing children;
they cannot mount or publish new ones.

Children inherit the parent's Context scope and actual committed dependency
ports. Each provider child has an explicit private owner-anchor dependency:
its consumers drain before owner resources are cleaned up. Ownership itself is
not an implicit dependency. Children with extra declared injections can restart
independently; the retained factory creates a fresh native instance. A publication
created during setup cannot become ready before its owner's initialization, so
setup must not await that child's `initialized()`.

This publication API supplies a factory-backed provider child. It does not offer
the typed in-process `ServiceHandle::set` value replacement contract, arbitrary
realm changes or cross-library `Arc` sharing. Model mutable service state inside
your instance, or publish a new definition and retire the old child explicitly.

At most `MAX_CHILDREN` (1024) child creation attempts and retained-definition
attempts are admitted per parent instance, including rejected attempts. Config
values are bounded before registering a definition; queued requests obey the
same 64-request and 512 KiB batch limits as other reverse operations. A factory's
descriptor is called and validated once per publication. Invalid descriptors or
queue rejection before dispatch release the unmounted definition. After dispatch,
the host owns release on preallocation rejection or observed graph removal.
Descriptor/destructor panic retains a fault and blocks false successful cleanup.

Reverse operations use `child_mount { factory, config }`,
`child_publish { definition, config }`, and `child_status`, `child_ready`,
`child_retire`, `child_join`, `child_retry_cleanup` with an opaque `child` handle.
Allocation replies are typed `{ child }`; status replies are typed
`{ child_state: ChildStatus }`. Control replies use `{ ok: null }` or `{ error }`.
They cannot be forged by returning similar-looking ordinary JSON DTOs.

The host additionally uses these SDK commands:

| Request `op` | Other fields | Success value |
| --- | --- | --- |
| `describe_definition` | `parent`, `definition` | Saved `FactoryDescriptor` |
| `create_child` | `parent`, `target`, `config` | `{ instance }` |
| `child_removed` | `parent`, `child` | `null` |
| `drop_definition` | `parent`, `definition` | `null` |

`target` is `{ kind: "module", factory }` or `{ kind: "retained", definition }`.
The host sends `child_removed` only after the actual graph Removed observation;
an early observation is preserved if the original allocation reply arrives later.
`drop_definition` requires no live child instances and, once assigned, actual
child removal. Parent cleanup/destruction rejects remaining child instances,
unremoved controls or retained definitions. The existing real graph remains the
lifecycle authority; these SDK tables enforce the native boundary's obligations.

`examples/shared/children.rs` exports `native-children` / `nativeChildren` plus
`native-child-leaf`. It exercises runtime publication, named mounting, readiness,
retirement/join, cleanup retry, discarded creation awaiters, nested children and
independent dependency restarts through `extraInject`.

## Rust-owned streams and objects

Declare a service method as `MethodKind::Stream` or `MethodKind::Object`, and
implement `PluginInstance::open_stream` or `open_object`. Their returned
`Arc<dyn PluginStream>` / `Arc<dyn PluginObject>` remains inside the library.
The resident host wraps an integer resource handle in its existing JavaScript
stream/object capability, retaining its original caller, publication and episode.

`PluginStream::next(ctx)` returns `StreamFuture<Output = Result<Option<Value>,
String>>`; `None` marks EOF but still requires close. Only one pull may be active.
`cancel()` requests cooperative cancellation without releasing resources;
`close(ctx)` runs after all pulls and their reverse JS calls have actually landed.
Close actions can call committed JS dependencies even after business cancellation.
Each stream item is checked against the value size/depth limits before adding
the small `{ done, value }` wire envelope.

`PluginObject` supplies a validated `ObjectDescriptor`, asynchronous `call`, and
`close`. Calls may overlap; close requires all admitted calls to have landed and
their job records to be dropped. Only declared object methods are callable.
Descriptor names must be nonempty, methods unique/nonempty, and its encoded JSON
must fit 512 KiB. `ObjectOwnership::Owned` runs the object's close hook before
release. `Borrowed` runs no close hook: it only releases the adapter's reference,
and the plugin or another explicit owner must retain the actual referent.

| Request `op` | Other fields | Success value |
| --- | --- | --- |
| `open_stream` | `instance`, `service`, `method`, `args` | `{ stream }` |
| `stream_next`, `stream_close` | `instance`, `stream` | `{ job }` |
| `stream_cancel`, `destroy_stream` | `instance`, `stream` | `null` |
| `open_object` | `instance`, `service`, `method`, `args` | `{ object, descriptor: { typeName, methods, ownership } }` |
| `object_call` | `instance`, `object`, `method`, `args` | `{ job }` |
| `object_close` | `instance`, `object` | `{ job }` |
| `destroy_object` | `instance`, `object` | `null` |

Resource jobs use the same poll/cancel/resolve-call protocol. A stream-next job
returns `{ done: true }` or `{ done: false, value }` inside its normal `ok` result.
Resource handles share the non-reusing allocator and are checked against their
original instance and kind on every operation. An instance admits at most 1024
live resources. Instance cleanup and destruction reject any remaining resource.

A failed close retains the resource, closes business admission, and can be
retried. After a successful close result is consumed and `drop_job` succeeds,
the host calls `destroy_stream` / `destroy_object` to release the originating
library's reference. This destructor runs before the host acknowledges final
release; a destructor panic retains a fault instead of reporting success. A
borrowed object's no-op close job still precedes reference destruction.
The SDK checks original object `Arc` identity across all instances: an owned
object cannot be exported again, even as borrowed, while that referent remains
alive; a new owned export also cannot alias any live borrowed handle. Multiple
borrowed handles are allowed. Conflicts return `ObjectOwnershipConflict`
without closing the original object. Weak identity records preserve the rule
after handle release without extending the referent's lifetime. Opening
hooks returning an error must clean up partial acquisition or retain it in their
own instance for cleanup. A descriptor panic after acquisition quarantines the
resource and faults the instance; it cannot silently bypass cleanup.

`examples/shared/resources.rs` provides `native-resource-consumer`, injecting
`jsHost` and exporting `nativeResources.stream(options)` / `object(options)`.
It exercises JS-gated operations, retryable close, version-bound values and
plugin-owned borrowed referents. This SDK table enforces the native protocol;
it does not replace the resident Driver's dependency or consumer lifecycle graph.


## Explicit checkpoint migration

A module factory opts into state migration with
`PluginFactory::checkpoint_schema() -> Option<CheckpointSchema>`. The SDK calls
this once when registering the module and publishes the validated declaration
in `ModuleDescriptor.checkpoint_schemas`, keyed by factory name:

```rust
use cordis_plugin_api::CheckpointSchema;
let schema = CheckpointSchema {
    schema: "example.counter".into(),
    version: 2,
    accepts: vec![1],
};
```

The current version is always accepted. `accepts` lists other versions handled
by the restore implementation; it may be empty. Schema names are nonempty and
at most 256 UTF-8 bytes. Versions are nonzero `u32` values; the compatibility
list contains at most 64 unique nonzero versions. Host preflight checks declared
compatibility before retiring the old generation. A declaration does not prove
that a plugin's decoder correctly migrates the data.

Implement synchronous `PluginInstance::checkpoint() -> PluginResult<Value>`
and `restore(checkpoint: Checkpoint) -> PluginResult<()>`. Both operate only on
local logical state: they receive no `PluginContext`, must not perform external
I/O or create new work, and must not include native addresses, resource handles,
child handles or other generation-bound capabilities in the data. Capture must
not destructively consume business state. Use setup to reacquire resources and
publish children after restoring their logical descriptions.

The host invokes capture at the actual retirement cleanup boundary, after
consumers and admitted calls have drained and before the plugin cleanup hook.
The SDK additionally requires an active module root with no remaining jobs,
exported resources, child instances, retained definitions or live child controls.
Only managed module roots are migrated automatically. Descendant state is the
parent author's responsibility; children can be reconstructed from declarative
state during setup. Merely seeing no SDK jobs is not evidence of host consumer
drain, so low-level hosts must use the real lifecycle boundary.

The SDK wraps the returned data in `Checkpoint { schema, version, data }` using
the cached factory declaration. Only `data` counts toward the 512 KiB and
64-container limits; protocol fields have separate bounded overhead. Failed
capture retains the original active instance for explicit host cleanup retry.
A successful capture is cached and closes SDK business admission. Cleanup
retries reuse that snapshot and never run capture again after partial cleanup.
An unwind panic retains a faulted instance rather than asserting cleanup.

Restore runs once on a fresh, not-yet-started instance, before setup and service
publication. The SDK validates schema, version and payload bounds before calling
user code. Any ordinary restore failure, including validation failure, moves
the candidate into the same cleanup-only state as failed setup. It cannot be
started or restored again: retry creates another fresh candidate and reuses the
retained host checkpoint. Cleanup must handle this partial initialization. A
successful restore permits setup; it cannot be repeated. The host retains copied
JSON independently of the originating instance, confirms actual source cleanup
and destruction before restoring, and controls checkpoint retention/release.

`examples/shared/checkpoint.rs` exports `native-checkpoint` / `nativeCheckpoint`
with a versioned counter. `read()` and `mutate(delta)` are synchronous;
`add({ delta, gate })` can wait on `jsHost.gate` to exercise retirement drain.
Version 1 serializes `{ value }`; version 2 serializes `{ counter }`, and both
restore versions 1 and 2. Configuration can inject capture, restore and cleanup
failures. The failing fixture library declares an incompatible schema for
preflight tests.
