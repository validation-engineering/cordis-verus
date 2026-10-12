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
