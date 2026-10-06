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

Version 1 supports setup, cleanup, JSON synchronous/asynchronous methods and
configuration-based state reconstruction. The Node host sends `args` as the JSON
array of positional JavaScript arguments; the plugin defines each method's argument schema. Reverse JS calls/injections, streams,
objects, dynamic children, arbitrary cross-library Rust values and checkpoint
migration are not part of this ABI. Unsupported methods cannot be described,
and nonempty injections are rejected. The host validates descriptors as well.

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
| `describe` | — | `{ module_id, version, factories }` |
| `create` | `factory`, `config` | `{ instance }` |
| `setup`, `cleanup` | `instance` | `{ job }` |
| `call_sync` | `instance`, `service`, `method`, `args` | `{ value }` |
| `call_async` | `instance`, `service`, `method`, `args` | `{ job }` |
| `poll` | `job` | `{ state: "pending" }` or `{ state: "ready", result: { ok } / { error } }` |
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
