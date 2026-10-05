# cordis-node

Node-API host for `cordis-driver` and an extensible Rust plugin executor. A
`NativeDriver` owns one graph. JavaScript plugins and Rust factories mounted
through `ctx.rustPlugin()` use that same graph, publication registry, committed
bindings and cleanup tickets. The Rust executor does not construct a second
`cordis::Runtime`.

`NativeDriver.command()` exchanges graph metadata and opaque value handles.
`rustCommand()` exchanges explicitly declared JSON service DTOs with compiled
Rust factories. These are separate boundaries: arbitrary JavaScript objects,
Rust `Any` values, closures and references are not automatically converted.
Use decimal strings for integers that cannot be represented exactly in JS.

## Compiling your own factories

The public Rust SDK is `cordis_node::plugin`:

- Implement `PluginFactory::descriptor()` and `create(config)`; each activation
  receives a fresh `Arc<dyn PluginInstance>`.
- Describe required service names and every provided method as `sync`, `async`, `stream`, or `object`.
  Names are local to the ordinary Cordis isolation realm.
- Implement `setup(PluginContext)` and `cleanup(PluginContext)` returning
  `PluginFuture`, an owned, `Send` Rust future. Both can call injected JavaScript
  methods with `ctx.call(name, method, json_args).await`.
- Publish a described service with `ctx.provide(name).await`. Implement its
  `call_sync` and/or `call_async` adapters; validate method argument DTOs there.
- Register any number of implementations in `FactoryRegistry`, then export a
  constructor returning `NativeDriver::with_factories(registry)`.

```rust
use cordis_node::{NativeDriver, plugin::FactoryRegistry};
use napi_derive::napi;

#[napi]
pub fn create_driver() -> napi::Result<NativeDriver> {
    let mut factories = FactoryRegistry::new();
    factories.register(MyFactory).map_err(napi::Error::from_reason)?;
    NativeDriver::with_factories(factories)
}
```

Compile the embedding crate as a `cdylib`, with a path dependency on
`cordis-node`, the workspace's compatible `napi` / `napi-derive` versions, and
`napi_build::setup()` in its build script. Load the resulting `.node` module with
`new Context({ addon: absolutePath })`. The facade prefers the addon's
`createDriver()` export. Default addon's factory registry is empty.

[`examples/interop_fixture.rs`](examples/interop_fixture.rs) is a complete custom
addon using only this public SDK. Its factory is not built into `NativeDriver`.
It demonstrates typed Rust state, explicit JSON validation, JS dependencies,
Rust services, asynchronous cancellation, a worker-originated reverse call,
streams, explicit object/callback adapters, and cleanup retry. Build it with:

```sh
cargo build -p cordis-node --example interop_fixture
```

`node scripts/build-node.mjs --offline` builds both the default binding and this
example and copies their Cargo-reported artifacts to the package and the test
output directory. The example's fault injection methods are test fixtures.
They are not registered in the ordinary addon.

## Scheduling and ownership

Plugin futures are polled outside the Driver borrow. No mutable Driver borrow
or backend borrow is held while JavaScript runs. `PluginContext` returns service
requests to JS, and resumes only after a matching reply. Request and job IDs
are decimal strings, monotonic within a driver. A duplicate reply is rejected.
A dropped request future does not mean its external call completed: the job
continues to own that request until the real reply arrives.

`rustWake(callback)` uses a nonblocking Node thread-safe callback. Rust futures
and worker-originated requests wake the executor without polling timers. Pending
jobs retain Node's event loop; idle domains do not. A completed action closes all
escaped `PluginContext` clones to new requests.

Each asynchronous method call has its own cancellation token. Consumer cleanup
cancels and drains its calls without canceling another consumer's calls. Owner
withdrawal cancels its outstanding business work. Cancellation is cooperative:
use `ctx.cancellation().check()` or `cancelled().await`, and still allow already
started external work to land. A future that never lands prevents cleanup;
cancellation is not permission to destroy resources still in use. Sync methods
and each future poll must be bounded and must not block the Node thread.

Cleanup can call the episode's committed JS dependencies. An admitted reverse
call can finish its old committed dependency chain after withdrawal. New root
lookups cannot regain that old publication. Native guards validate the exact
publication, generations and the current committed dependency closure. Restoration
privileges are distinct from ordinary in-flight continuation admission.

A failed cleanup retains its Rust instance for an explicit retry. Release is
allowed only after successful cleanup and after all jobs and external requests
have landed. Normal domain disposal closes the wake callback. Finalization
closes local admission, wakes pending Rust request waiters with `ActionClosed`,
cancels job tokens, and contains individual user destructor panics; it is not a
replacement for asynchronous cleanup.

A Rust panic caught at the Node boundary permanently faults the whole driver and releases its wake
handle. The adapter does not continue from partially mutated plugin state or
report cleanup as successful. Rust process aborts, double panics inside one
user destructor, and nonterminating plugin code cannot be isolated in-process.

## Pull streams

Declare `MethodKind::Stream` and implement `PluginInstance::open_stream` with an
`Arc<dyn PluginStream>`. `next(ctx)` returns one JSON item or EOF; `cancel()` only
requests cooperative cancellation, and asynchronous `close(ctx)` runs after any
outstanding pull and reverse RPC really land. There is at most one pending pull,
no prefetch, and close failure retains the resource for retry. JavaScript receives
an async iterator usable with `for await`; the consumer Fiber and provider session
also own idle streams. A withdrawn or cleaning consumer cannot acquire new streams.

For the other direction, `ctx.open_stream(service, method, args).await` returns a
`JsStream` scoped to that Rust action. Use `next().await` and `close().await`.
Explicit Rust-side close returns `StreamBusy` without changing admission while
`next` is pending; await the pull first. This prevents a cloned capability from
joining its own reverse-call chain. Framework cancellation and journal cleanup
retain the separate return-before-join path that can wake a blocked next.
Even when the handle is dropped, the action journal requests JS `return()` and
waits for its real result before completing the job. Cancellation sends return
before joining pending next, and failed or incomplete return retains the stream
for owner cleanup. The JS iterator must explicitly implement `return()` and use
boolean `done`; `done:false` does not confirm release. Each restoration RPC has
its own exact request authority, distinct from concurrently executing business RPCs.

This is an explicit JSON element adapter, not a general object/closure handle or
an arbitrary async runtime. See [the usage guide](../../docs/rust-node-plugins.md)
and `tests/node-compat/rust-streams.test.mjs` for lifecycle examples.

## Explicit objects and callbacks

Declare `MethodKind::Object` and implement bounded `PluginInstance::open_object`
returning an `Arc<dyn PluginObject>`. Construct its interface with
`ObjectDescriptor::new(type_name, methods, ownership)`; this validates a nonempty
name and distinct method names before it can describe an acquired resource.
`PluginObject::call(ctx, method, args)` returns a `PluginFuture`, so every declared
object method is asynchronous. Its arguments and result are still explicit JSON
DTOs. Objects, closures and implementation state remain in their defining language.

JavaScript receives a privately branded handle with `typeName`, `ownership`, a
fixed `methods` list, `call(method, ...args)` and `close()`. Each call checks the
original consumer generation and publication, and has its own cancellation token.
Several calls may be in flight. Close rejects new calls, cancels the existing
calls, waits for their futures and external RPCs to land, and then releases the
resource. Concurrent JS close attempts share one promise; failed close retains the
object and its dependencies for an explicit retry.

`ObjectOwnership::Owned` invokes the asynchronous `PluginObject::close` hook.
`Borrowed` releases the adapter reference without invoking that hook. Borrowed
release is not a guarantee about the last Rust `Arc` or JS garbage collection:
the defining plugin must retain the referent for the required lifetime. Multiple
borrowed leases are allowed. The same Rust object `Arc` cannot be owned twice or
owned while borrowed leases are active, and an already closed owned referent
cannot be acquired again. These identity rules apply within one native driver.

Objects are separate from stream pre-cleanup. A consumer can use its old objects
from ordinary cleanup inverses. Only after all those inverses succeed does the JS
host close the remaining objects in reverse acquisition order. If an inverse
fails, objects remain available to retry; if object close fails, that object and
earlier objects remain owned. Provider withdrawal cancels business calls without
prematurely closing objects still needed by committed consumers.

For the opposite direction, a JS service factory returns `adaptObject(target,
{typeName, methods, ownership, dispose})`. Owned adapters require an explicit
async-capable disposer; borrowed adapters cannot declare one. Rust acquires it
with `ctx.open_object(service, method, args).await`, obtaining a `JsObject` with
`descriptor()`, `call(method, args).await` and `close().await`. These handles are
scoped to the opening Rust action. A forgotten handle is closed by that action's
journal after its pending object calls land; objects close in reverse acquisition
order after stream draining. Failed close stops that pass and retains the object
for owner cleanup retry. Explicit Rust-side `JsObject::close` returns `ObjectBusy`
without changing admission while any method call or close is still pending;
await those calls before explicit close. This prevents cloned capabilities from
joining their own reverse-call chain. Automatic journal cleanup still waits for
every real call, and no path consumes a hidden close retry. Late open replies are
registered and reclaimed before their action can complete.

A callback uses exactly the same ownership protocol with the single declared
method `call`. Rust exporters use `ObjectDescriptor::callback(type_name,
ownership)`. Rust consumers use `ctx.open_callback(...).await`, yielding a
`JsCallback` with `invoke(json_args).await` and `close().await`; JS exporters use
`adaptCallback(fn, options)`. JS callback handles also expose `invoke(...args)`.
These are explicit service-factory acquisitions, not arbitrary function arguments
or magic capability IDs embedded in DTOs. Neither ordinary JSON calls nor stream
elements accept adapter objects or callback functions.

## Boundary and validation

This crate is experimental and not published. Native plugins and Node-API glue
are trusted host code, not a sandbox. The Verus kernel proves its own lifecycle
and registry contracts; it does not prove arbitrary Rust futures, JS callbacks,
DTO schemas, NAPI glue or this executor. The SDK supports the static subset of real `cordis::Plugin` through explicit typed bindings. Full dynamic Runtime migration and a stable Rust dynamic-library ABI remain outside this contract.

Deterministic SDK tests run with `cargo test -p cordis-node --test plugin_runtime`.
`tests/node-compat/rust-interop.test.mjs` exercises the real custom addon and
JavaScript facade, including two-way calls, withdrawal, isolation, cancellation,
cleanup retries and contained fault paths. `rust-streams.test.mjs` and
`rust-objects.test.mjs` exercise the corresponding explicit resource adapters.


## Existing typed plugins

Use `FactoryRegistry::register_typed(TypedFactory::new(name, make_plugin))`, with
explicit `.requires(key, name)` and `.provides(key, name, adapter)` bindings.
`TypedService<T>` defines the JSON/stream/object view over the original shared
slot. One real `cordis::Plugin` definition persists per logical Fiber; each
activation gets a new static episode driven by the same Node graph. No second
Runtime or lifecycle lease is constructed. Full usage, supported operations and
failure semantics are in [the typed guide](../../docs/typed-rust-plugins.md).

The old API's `FnOnce` cleanup cannot be replayed. Failure stays failed across
retry rather than consuming a callback and reporting empty cleanup as success.
Legacy callback panics isolated by the static executor become setup/cleanup
failures; adapter and other boundary panics still fault the domain.
