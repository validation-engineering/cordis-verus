# Native Rust plugin replacement

A resident `cordis.node` can load independently compiled Rust `cdylib` plugins
and replace their managed instances without replacing the native Driver or
restarting Node. The controller uses the same domain transaction queue,
provider identities, consumer cleanup barriers and owned plugin graph as
JavaScript plugins.

This is a trusted native-code deployment boundary. It is not a sandbox, a
stable Rust ABI, state migration, or physical library unloading. JavaScript
module HMR remains a separate mechanism described in
[official-in-place-hmr.md](official-in-place-hmr.md).

## Build and load

Write the plugin with the [`cordis-plugin-api` SDK](../crates/cordis-plugin-api/README.md),
compile it as a `cdylib`, and export its versioned C entrypoint with
`cordis_plugin_api::export_plugin!(module)`. The SDK keeps Rust instances,
Futures, allocators and destructors inside their originating library. Only a
versioned C function table, byte buffers, numeric handles and wake callbacks
cross the library boundary.

The repository includes `dynamic_fixture_v1`, `dynamic_fixture_v2` and
`dynamic_fixture_fail` examples. `npm run build:native -- --offline` builds and
copies these to `target/node-compat/dynamic-fixture-<version>.dylib` on macOS,
`.so` on Linux or `.dll` on Windows. For the text fixture:

```js
import { Context } from '@cordis-verus/compat-cordis';
import { loadRustModule } from '@cordis-verus/compat-loader/rust-module';

const ctx = new Context();
const plugins = await loadRustModule(ctx, {
  path: '/absolute/path/text-v1.dylib',
  sha256: trustedManifest.v1.sha256,
  plugins: [{ id: 'text', factory: 'native-text-analysis', config: {} }],
});

ctx.nativeText.analyze({ text: 'native code update' });
// { version: 'v1', words: 3, characters: 18, text: 'native code update' }
await ctx.nativeText.delayed({ text: 'async native' });

await plugins.reload({
  path: '/absolute/path/text-v2.dylib',
  sha256: trustedManifest.v2.sha256,
});
ctx.nativeText.analyze({ text: 'native code update' }); // version: 'v2'

await plugins.dispose();
await ctx.dispose();
```

Use the absolute artifact path and an expected lowercase SHA-256 digest. The
native loader checks the source bytes and loads a private immutable copy,
not the mutable build output. The digest identifies the main library bytes;
it does not authenticate the publisher, contain OS shared-library dependencies,
or make executing native code safe. Use a trusted build manifest in deployment.

Every configured entry has a stable controller-local `id`, an exported factory
name and optional finite JSON config. Recipes are copied at admission and kept
for recovery. A controller replaces its complete owned group. Use multiple
controllers or isolated Context views for independently replaceable modules;
all views still share the original native Driver. Initial creation must happen
from an external coordinator, not inside a lifecycle callback that would await
its own domain transaction.

The initial ABI supports JSON configuration, synchronous JSON service methods,
asynchronous setup/methods/cleanup, cancellation and wake notifications.
Service arguments are positional JSON arrays (`analyze({text})` crosses as
`[{text}]`). The descriptor fixes service and method names. Injected host
services, reverse JavaScript calls, cross-library objects/streams, dynamic
publication, child-plugin creation and arbitrary shared `Arc<T>` values are
not part of this ABI. The existing statically linked typed Rust adapter keeps
those already-supported capabilities; its code is not made replaceable by
loading a native module.

## Replacement and recovery

`reload()` first validates the candidate artifact, module identity and requested
factory names without running plugin setup. It then retires the old owned
group and waits for real removal, including retained consumers, child ownership,
asynchronous calls and plugin cleanup. Only after that barrier can candidate
setup publish its services. All entries must reach Active before the controller
increments its committed revision.

The activation transaction covers the controller's configured entries. External
consumers still participate in dependency withdrawal and cleanup barriers, but
their new setup is outside this controller's commit condition. If an external
consumer rejects a new service implementation, the managed provider may commit
while that consumer is Failed; its Fiber await/result and the Context snapshot
expose that failure. Applications that require coordinated consumer activation
must place those components under an application-level coordinator. The module
controller does not claim a global activation rollback.

Each loaded factory has an immutable reference that includes its code image.
A dependency restart of an old logical Fiber continues using that same image.
Loading another image never overwrites a process-global factory-name alias.
Only the controller's replacement transaction changes its configured instances.

The service can be temporarily unavailable during replacement. This is not
zero-downtime handoff. Old service handles become stale, and an instance recreated
from old code has a new Fiber identity.

If candidate activation fails, the controller first drains that candidate, then
recreates the old code and config. `NATIVE_MODULE_RELOAD_FAILED` with
`error.details.restored === true` means that reactivation succeeded. It does not
mean old objects, memory or external I/O were rolled back.

If an inverse fails, the controller retains its journal and reports `blocked`.
Call `retryCleanup()` explicitly after the cause has been corrected. That method
only retries failed cleanup and removes retained resources; it never performs
setup under recovery-only transaction authority. The next ordinary `reload()`
continues the journal:

- If the failure was retiring the old instance and candidate setup never ran,
  replacement resumes directly from the confirmed retirement. The old recipe
  remains available for rollback. Reconstructing and immediately retiring an
  unnecessary old instance would repeat per-instance cleanup failures.
- If candidate cleanup or old-version restoration failed, retained resources
  are drained and the old recipe is restored before a new replacement attempt.

An external consumer with its own failed inverse may also block retirement.
Its owner must explicitly retry that consumer; the module controller only
retries cleanup in its own managed subtree. No timeout or wrapper disappearance
is treated as successful cleanup. A non-cooperative native Future can therefore
prevent a replacement from finishing.

`dispose()` closes controller admission and drains its managed resources. A
failed disposal retains cleanup access for `retryCleanup()` and another
`dispose()`. Reentrant callback operations, stale owner generations and new
requests after domain shutdown are rejected. Requests already admitted before
shutdown finish in the existing domain FIFO.

For applications that must keep a handle even if the initial setup fails, use
an explicit controller:

```js
import { RustModuleController } from '@cordis-verus/compat-loader/rust-module';

const plugins = new RustModuleController(ctx, {
  plugins: [{ id: 'text', factory: 'native-text-analysis', config: {} }],
});
await plugins.reload(artifact);
```

The `loadRustModule()` helper also attaches this controller to the rejected
`error.controller` when initial activation fails, so a failed inverse can still
be retried or disposed.

## Diagnostics and retained code

`plugins.snapshot()` returns a frozen view of the committed module metadata,
revision, managed entry Fiber IDs and immutable factory references. It also
lists journal roots retained after cleanup failure. The snapshot's state is the
last controller transaction state; actual entry states remain visible if an
outside owner disposes them. A stale owner's next reload is rejected.

`plugins.inspect()` adds live native diagnostics under `images`:

- `modules`: modules registered in this Context's Driver, including current
  instance/job counts and `retainedInstances`/`retainedJobs` whose destruction
  could not be confirmed.
- `retainedImageCount` and `retainedImageLimit`: the code-image count and hard
  limit shared by environments using the same resident addon image. The initial
  limit is **128**, including loaded images that failed descriptor validation.
  This counter is not a per-controller or per-Context allowance. Loading an
  independent copy of the resident addon has an independent static budget.
- `retained: true`, `unloadSupported: false`: successful instance cleanup does
  not unload code mappings.

Identical digests already loaded in the same Driver reuse their factory
references after the supplied bytes are verified. A new image consumes the
shared budget even if it is later rejected or its setup fails. Roll a host
process before exhausting the budget; disposing a controller does not reset it.
Neither mapping count nor `Library::close` would establish a bound on native
memory use or prove arbitrary plugin threads and TLS destructors are safe to
unload. Physical unload is intentionally unsupported.

## Verification boundary

Tests load real v1/v2/failing Rust libraries into one resident addon, exercise
both Cordis profiles, fixed old-generation references, asynchronous cancellation,
failed cleanup retry, candidate rollback, digest rejection and post-disposal
resource diagnostics. Controller tests additionally cover domain FIFO, shutdown,
stale owners, reentry, external consumer barriers and post-allocation observer
failures.

These are host/ABI integration tests. Existing Verus contracts still govern the
native lifecycle kernel; they do not prove the C boundary, OS dynamic loader,
arbitrary Rust plugin cleanup claims or external side effects. Rust core changes
and statically linked addon changes still require rebuilding the resident addon
and restarting its host.
