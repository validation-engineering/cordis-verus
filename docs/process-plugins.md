# External executable plugins

`cordis::process_plugin` loads executable code in a separate process. A plugin
can be a native binary or an executable script with a suitable interpreter.
The host passes a path and separate arguments to `std::process::Command`; it
never constructs a shell command. Existing Cordis TypeScript plugins do not
implement this protocol automatically. An adapter process must translate their
application interface if they are to be reused.

The transport and filesystem handling are ordinary Rust. Verus does not prove
subprocess behavior, external code, filesystem operations, or RPC results.
Processes run with the host user's permissions and inherited environment; this
is a lifecycle boundary, **not a security sandbox**.

## Application integration

Create a shared typed service key and register a watched executable factory:

```rust,no_run
use cordis::config::Schema;
use cordis::loader::{ConfigTree, Entry, FactoryRegistry, Loader};
use cordis::process_plugin::{ProcessClient, ProcessPlugin, ProcessPluginWatcher};
use cordis::{Context, ServiceKey};
use serde_json::json;

async fn application() -> Result<(), Box<dyn std::error::Error>> {
    let model = ServiceKey::<ProcessClient>::new("model");
    let context = Context::new();
    let mut registry = FactoryRegistry::new();
    registry.register_service("model", model);
    let mut watcher = ProcessPluginWatcher::new();
    watcher.register(
        &mut registry,
        "external-model",
        Schema::Any,
        ProcessPlugin::new("/opt/my-harness/model-worker")
            .arg("--stdio")
            .watch_file("model-settings.json"),
        model,
    )?;
    let mut loader = Loader::new(context.clone(), registry);
    loader.apply(ConfigTree {
        entries: vec![Entry::plugin(
            "model", "external-model", json!({"model":"example-model"}),
        )],
    }).await?;

    let client = loader.runtime().get(&context, model).unwrap();
    let response = client.call("complete", json!({"prompt":"hello"}))?;
    println!("{response}");

    // Application scheduling supplies the polling interval. This reads code
    // files; Loader::poll_reload() separately reads the JSON configuration tree.
    if !watcher.poll(loader.registry_mut())?.is_empty() {
        loader.reload().await?;
    }
    loader.dispose().await?;
    assert!(client.is_closed());
    Ok(())
}
```

`ProcessPlugin::plugin(name, key)` also constructs a provider directly, without a
Loader. `spawn()` gives a standalone client when application code deliberately
owns the process itself. Dropping the last client closes it. Provider setup
registers cleanup before publishing the client, so failed setup also releases
the process.

A factory does not spawn a process while the configuration is being validated.
Only plugin setup does. A successful `initialize` response is required before
the service becomes available. Watched factories send the validated, defaulted
entry configuration as initialization parameters; this replaces the recipe's
standalone `initialize(...)` value. Consumers use the same service key in
`.requires(model)` and `setup.get(model)`.

Calls and process initialization use **blocking** I/O workers with bounded waits.
They do not require a particular async executor, but calling `call()` from an
async task blocks that executor thread. An application can put these calls on
its own blocking executor. Initialization currently runs in synchronous plugin
setup and can block the thread driving Loader/Runtime up to its configured
startup deadline and cleanup time; it is not an async process API.

## Wire protocol

The protocol is a serialized subset of JSON-RPC 2.0 over UTF-8 JSON lines.
Every request and response ends with `\n`. Child stdout carries protocol frames
only. Logs go to stderr, which is inherited rather than left in an unread pipe.

The first request is always `initialize`, with the effective plugin config:

```json
{"jsonrpc":"2.0","id":1,"method":"initialize","params":{"model":"example-model"}}
```

The child returns a result, including `null` if there is no initialization data:

```json
{"jsonrpc":"2.0","id":1,"result":null}
```

An application request and its two possible response shapes are:

```json
{"jsonrpc":"2.0","id":2,"method":"complete","params":{"prompt":"hello"}}
{"jsonrpc":"2.0","id":2,"result":{"text":"Hello"}}
{"jsonrpc":"2.0","id":2,"error":{"code":-32001,"message":"model unavailable","data":{"retryable":true}}}
```

Only one of `result` or `error` is accepted. Response IDs must match the current
request, error codes must be integers, and error messages must be strings. A
remote application error is returned to the caller without closing the client.
Malformed JSON, unexpected IDs, EOF, write failures, oversized responses, and
response deadlines close the transport. There are no notifications, batches,
streaming responses, reverse RPC, or concurrent in-flight requests. Concurrent
callers are serialized through a bounded rendezvous channel.

Defaults are 10 seconds for initialization, 30 seconds per request, 2 seconds
for cleanup, and 1 MiB per frame including the newline. Builder methods change
these limits. An outgoing oversized frame is rejected without touching the
child. Queue timeout also leaves the active request intact. Once a sent request
times out, the whole transport is closed so a late response cannot be consumed
as the next request's response.

Deadlines bound host waits for admission, protocol I/O, and reaping, with OS
scheduling overhead. A timed-out request can additionally spend the cleanup
budget terminating its child. These are not hard real-time guarantees for OS
process creation or filesystem operations.

## Code updates and recovery

`ProcessPluginWatcher` compares executable and explicitly declared dependency
**contents and permissions**. Polling prepares every changed revision before it
registers any factory. Missing files, non-regular files, non-executable programs
on Unix, or excessive artifact size return an error without changing existing
registrations or running providers. Total captured files are limited to 256 MiB
per plugin revision.

Each revision retains captured bytes and a private artifact directory. Every
process launch receives another private copy from those captured bytes. This
means a child modifying its own working files cannot change the code used by a
later rollback. Factories and live clients retain the corresponding artifacts;
the directories are removed when their last owner is dropped. A crash of the
host may leave temporary directories for normal system-temp cleanup.

Declared dependencies must be regular files below the executable's parent
directory. Relative paths are resolved there, and their relative layout is
preserved. In watcher mode the working directory defaults to the captured root;
an explicit working directory must also be below that root. Absolute arguments
that exactly name captured files are rewritten to their private copies. Other
arguments are passed literally. Programs should use relative artifact paths
and a separate explicit location for persistent application state.

Only the executable and declared files are captured. System interpreters,
shared libraries, undeclared imports, network resources, and absolute paths
embedded in code are not recursively discovered or frozen. A Python/Node runner
can be supplied by an executable wrapper, with its application scripts declared
as watched files. The wrapper must use relative paths into the captured tree.
The watcher does not compile source code; an external build step must atomically
publish a new executable and any required files. A poll can observe separately
published files at different moments; publish an artifact tree coherently when
cross-file consistency matters.

After `poll()` returns changed names, `loader.reload().await` performs normal
lifecycle replacement. The old provider remains available to its committed
consumers during their cleanup. Once provider cleanup starts, the old client
closes request admission before killing and reaping the direct child. Retained
external client handles then reject calls. If the new process fails to
initialize, Loader can rebuild the previously committed factory from its actual
old captured code, even while the source executable on disk is broken.

A failed apply restores the running configuration, but the registry still
contains the rejected candidate factory, as for other Loader factory updates.
An explicit `reload()` retries it; publishing a corrected executable and polling
registers a new revision. Code polling is not an automatic retry scheduler.

Shutdown is idempotent and currently terminates the child rather than performing
a graceful shutdown RPC. In-flight external requests are aborted. The adapter
owns only the direct child; plugins must not detach descendants or leave inherited
stdio handles in background processes. It is not a process-group supervisor.
If the OS cannot confirm exit within the cleanup limit, shutdown reports an
error; dropping the last client also installs a best-effort reaper. Kernel or
process-group supervision and stronger isolation belong to the application.

## Executable validation

Run the actual subprocess tests with:

```sh
cargo test -p cordis --test process_plugin --offline
```

On Unix these create executable fixtures, exercise literal argument passing,
concurrent callers, remote and protocol errors, startup/request timeouts,
owner cleanup, code replacement, dependency snapshots, and rollback after a
broken new executable. The fixtures use POSIX shell builtins; no network or
model endpoint is required. The public transport uses portable `std` APIs;
the executable fixture tests are currently Unix-specific.
