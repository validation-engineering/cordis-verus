# cordis

An independent Rust Cordis runtime backed by the executable, Verus-verified
`cordis-kernel`. It provides typed services, plugin lifecycle management,
asynchronous setup and effects, dynamic children, scoped events and timers,
JSON configuration, reversible in-place updates, dynamic service publication,
and external executable plugins with snapshot-backed code reload.

```rust
use cordis::{Context, Plugin, Runtime};

let mut runtime = Runtime::new();
let _plugin = runtime.mount(&Context::new(), None, Plugin::new("hello", |ctx| {
    ctx.on_cleanup(|| Ok(()));
    Ok(())
})).unwrap();
```

Version 0.1 is experimental. APIs may change in a 0.x minor release. This is a
Rust interface, not a TypeScript plugin loader, and does not run DeepSeek Harness.
The host adapter is behavior-tested; its arbitrary callbacks, futures, file I/O,
and synchronization are not covered by the kernel's formal proofs.

Drive the runtime and explicitly dispose/settle plugins when shutting down.
Dropping the runtime does not execute asynchronous cleanup. See the source
distribution's `docs/runtime.md` and `docs/loader.md` for runnable workflows and
the exact lifecycle semantics.

Licensed under MIT; see `LICENSE` and `NOTICE` in this package.
