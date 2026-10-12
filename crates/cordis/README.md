# cordis-verus

An independent Rust Cordis runtime backed by the executable, Verus-verified
`cordis-kernel`. It provides typed services, plugin lifecycle management,
asynchronous setup and effects, dynamic children, scoped events and timers,
JSON configuration, reversible in-place updates, dynamic service publication,
and external executable plugins with snapshot-backed code reload.

Add the host library (the dependency alias preserves `use cordis::...`):

```toml
[dependencies]
cordis = { package = "cordis-verus", version = "0.1.0" }
```

```rust
use cordis::{Context, Plugin, Runtime};

let mut runtime = Runtime::new();
let _plugin = runtime.mount(&Context::new(), None, Plugin::new("hello", |ctx| {
    ctx.on_cleanup(|| Ok(()));
    Ok(())
})).unwrap();
```

The current source also includes an **unreleased** Rust convenience API:

```rust
use cordis::{Plugin, ServiceKey};

let greeting = ServiceKey::<String>::of();
let consumer = Plugin::with_dependencies("consumer", greeting)
    .setup(|_, greeting| { println!("{greeting}"); Ok(()) });
```

A key or tuple of keys generates both required dependencies and setup parameters.
`setup_async` accepts an async closure; `key.with_config(...)` carries availability
predicate input. Canonical `of()` / `named()` keys compose across modules in one
linked host; `new()` creates a fresh identity. Isolation remains explicit.

With the optional `tokio` feature, `App::new()` runs one driver task owning the
existing Runtime. `app.plugin(plugin).await` returns a `PluginHandle`:
`settled()` waits for stability (including missing dependencies), `ready()` waits
for Active, and `dispose()` waits for cleanup and removal. Requests enqueue when
called; dropping the wait does not cancel an accepted operation. Explicitly await
`app.shutdown()` before stopping the executor. Failed retryable cleanup retains resources
for `handle.retry_cleanup()` and another shutdown. One-shot cleanup failures drain
and are reported by the waiting handle. `app.cleanup_errors()` inspects historical
failures; shutdown reports and consumes that history, including failures already
observed by a handle. Callbacks must not await their
own lifecycle or disposal of a provider that they keep alive.

`get` and `require` return `ServiceReadError` with key/realm, caller, generation,
committed provider, failure reason and source location. `CallbackResult` retains
that cause through Runtime and application waits. `CallbackError::new(error)`
keeps external error types accessible through `Error::source()`; effect joins
preserve multiple failures. Node and process protocols still transport error text.
Typed inputs use committed reads, not current-target lookup.

`app.scoped(context)` shares the driver with a different default context;
`handle.plugin(...)` creates an owned child. Handles support snapshots, synchronous
and asynchronous setup updates, and `update_plugin(...)` with a complete typed
recipe. Changed declarations are rejected before disturbing the existing plugin.
These ordinary Rust adapters are tested; the kernel proofs do not automatically
prove them, Tokio fairness, arbitrary callbacks or eventual cleanup completion.

Run `cargo run -p cordis-verus --features tokio --example managed_app` from the
source checkout. This convenience API is not included in the published 0.1.0.

Version 0.1 is experimental. APIs may change in a 0.x minor release. This is a
Rust interface, not a TypeScript plugin loader, and does not run DeepSeek Harness.
The host adapter is behavior-tested; its arbitrary callbacks, futures, file I/O,
and synchronization are not covered by the kernel's formal proofs.

Drive the runtime and explicitly dispose/settle plugins when shutting down.
Dropping the runtime does not execute asynchronous cleanup. See the source
distribution's `docs/runtime.md` and `docs/loader.md` for runnable workflows and
the exact lifecycle semantics.

Licensed under MIT; see `LICENSE` and `NOTICE` in this package.
