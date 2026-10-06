# Native Rust plugin replacement

A resident `cordis.node` can load independently compiled Rust `cdylib` plugins
and replace their managed instances without replacing the native Driver or
restarting Node. The controller uses the same domain transaction queue,
provider identities, consumer cleanup barriers and owned plugin graph as
JavaScript plugins.

This is a trusted native-code deployment boundary. It is not a sandbox, a
stable Rust ABI or physical library unloading. Explicit versioned JSON state
migration is available for opted-in managed roots. JavaScript
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
for recovery. `reload(artifact)` retains the latest successfully committed recipes.
`reconcile({ path, sha256, plugins })` changes the artifact and complete recipe
list in one domain revision, including configuration changes and added or removed
entries. An empty `plugins` list retires the owned group while retaining validated
module identity; a later reconciliation can enable it again. Candidate failure
restores the previous artifact and its own immutable recipes. Queued `reload()`
uses the recipes committed by earlier successful revisions.
A controller replaces its complete owned group. Use multiple
controllers or isolated Context views for independently replaceable modules;
all views still share the original native Driver. Initial creation must happen
from an external coordinator, not inside a lifecycle callback that would await
its own domain transaction.

The ABI supports JSON configuration, synchronous JSON service methods,
asynchronous setup/methods/cleanup, declared host service dependencies,
asynchronous reverse JavaScript calls, pull streams and explicit object/callback
interfaces in both directions, cancellation and wake notifications. Service arguments are
positional JSON arrays (`analyze({text})` crosses as `[{text}]`). The descriptor
fixes each factory's service and method names. A plugin can also mount a named
factory from its own image or publish a runtime-created factory as an owned
child. Arbitrary shared `Arc<T>` values do not cross this ABI. The statically
linked typed Rust adapter retains its
existing capabilities; loading a native module does not replace its code.

## Calling JavaScript services from Rust

Declare every dependency in `FactoryDescriptor.inject`, then use the SDK's
`PluginContext::call()` during async setup, service calls or cleanup:

```rust
// In PluginFactory::descriptor():
// inject: vec!["jsHost".into()],

fn setup(&self, ctx: PluginContext) -> PluginFuture {
    Box::pin(async move {
        ctx.call("jsHost", "record", serde_json::json!(["ready"])).await?;
        Ok(serde_json::Value::Null)
    })
}
```

The corresponding provider is an ordinary plugin in the same Context graph:

```js
await ctx.plugin(child => {
  child.provide('jsHost', {
    async record(message) {
      await auditLog.write(message);
      return null;
    },
  });
});
```

Both synchronous and Promise-returning JS methods are awaited through this Rust
API. Arguments must be positional finite JSON arrays; results must be finite
JSON with Unicode scalar strings and keys. Unpaired UTF-16 surrogates are
rejected before native decoding. JS exceptions become Rust `Err(String)`. There is no synchronous reverse
call from a Rust synchronous method. The SDK bounds outstanding requests, data
size and nesting depth; a result that exceeds these bounds becomes a normal
call error so its job can still finish and be released.

`inject` participates in the existing dependency graph and service isolation
realms. A required service must be available before the native factory starts.
Changing its provider retires the consumer's old episode and restarts it with
its original native factory reference; loading another library alone does not
change that reference. Cleanup retains access to the episode's committed old
provider until the consumer has actually finished. The ordinary Loader wrapper
still requires its configured children to become Active when initially loaded.

The C function table remains version 1. Reverse calls travel as bounded request
records returned by job polling, followed by explicit result delivery into the
originating library and job. The resident host uses the same `PluginContext`
transport as statically linked Rust plugins, and invokes JS after leaving native
execution. No JS callback, Rust Future, trait object or allocator crosses the
library boundary.

A context admits calls only while its owning action is alive. Once its Rust
body returns, escaped context clones cannot start more work. Already admitted
JS calls must really finish before the job can report completion, even if Rust
drops the future awaiting their result. Cancellation is cooperative: it does
not abort an arbitrary JS Promise or pass an AbortSignal through JSON. Replacement
and shutdown therefore wait for outstanding calls; an unresolved Promise can
block them. Cleanup can make the reverse calls it needs to release resources.
Reentrant mutation checks also apply to JS reached through this boundary.

The `native-js-consumer` fixture demonstrates setup/cleanup calls and async
methods against `jsHost`; its real cdylib tests cover provider restart, isolated
realms, dropped futures, cancellation drain, stale handles and wire limits.

## Consuming JavaScript streams, objects and callbacks

The same declared dependencies can supply resources to an independent native
plugin. Use `PluginContext::open_stream`, `open_object` or `open_callback` during
async setup, service methods or cleanup. Each acquisition belongs to the action
that opened it. `JsStream`, `JsObject` and `JsCallback` are explicit capabilities;
they cannot be serialized inside JSON or moved to another action by cloning.

```rust
// In an async action with inject: vec!["textPipeline".into()]:
let stream = ctx.open_stream("textPipeline", "chunks", serde_json::json!([text])).await?;
let sink = ctx.open_object("textPipeline", "session", serde_json::json!([])).await?;
while let Some(chunk) = stream.next().await? {
    sink.call("append", serde_json::json!([chunk])).await?;
}
let result = sink.call("snapshot", serde_json::json!([])).await?;
sink.close().await?;
stream.close().await?;
// Returning early with an error also leaves the action journal responsible
// for closing both resources; it does not silently discard their cleanup.
```

A JS stream provider returns an async iterator with an explicit `return()`.
Opening it does not pull an item. Objects must use the public `adaptObject`
helper; a plain object with similar properties does not grant a capability:

```js
import { adaptObject, adaptCallback } from '@cordis-verus/compat-cordis';

child.provide('jsHost', {
  async *stream() { yield 'hello'; yield '世界'; },
  object() {
    let count = 0;
    return adaptObject({ add: n => count += n, read: () => count }, {
      typeName: 'Counter', methods: ['add', 'read'], ownership: 'owned',
      dispose() { /* release resources belonging to this counter */ },
    });
  },
  callback() { return adaptCallback(value => ({ doubled: value * 2 })); },
});
```

`JsObject::descriptor()` exposes the captured type name, method allowlist and
ownership. `call()` only accepts declared methods and positional JSON arrays.
`open_callback()` requires the single `call` method and returns a capability
with `invoke()` and `close()`. Borrowed object release removes the adapter's
reference without invoking a destructor; the JS provider must retain the
referent's owner. Owned release awaits the supplied `dispose` function.

Resources are bound to their opening native action and the episode's committed
JS provider. Ending the Rust body closes further admission, then the resident
journal waits for admitted operations and releases remaining resources. This
also covers dropped acquisition or operation futures and escaped handle clones.
Escaped handles reject further work after their action closes; they never
select a new action or provider.
The SDK uses typed request/reply records and action-local identities on the C
boundary. Resource identities are not delivered as ordinary service JSON. Each
action allows at most 1,024 acquisition attempts, including failed opens, and
64 outstanding reverse requests; closing a handle does not reuse its identity.

Explicit close is available after cancellation. It reports `StreamBusy` or
`ObjectBusy` when it would join an outstanding operation on the same capability,
so a callback cannot deadlock by awaiting its own close. Finish that operation
before explicit close. Framework cancellation can issue iterator `return()` to
unblock an outstanding `next()` and still waits for both actual outcomes.
Object disposal waits for all admitted methods. Cancellation does not abort an
arbitrary JS Promise; an unresolved operation can still block shutdown.

Failed close remains visible and retryable. Explicit close can retry while its
action is alive; after that action ends, lifecycle cleanup retries retained
resources. Reverse resources acquired by a native cleanup or close hook must
finish before the original native instance or resource is destroyed. Retrying
that finalization does not repeat a native hook that already succeeded.

The `native-js-resources` fixture and
[`rust-module-js-resources.test.mjs`](../tests/node-loader/rust-module-js-resources.test.mjs)
exercise these contracts through real cdylibs in both compatibility profiles,
including late acquisition, failed close, cancellation, provider updates and
same-process native code replacement. The installed npm package smoke also
executes stream, object and callback acquisitions through this boundary.

## Dynamic publications and child plugins

An asynchronous native action can create a real child in the same Context graph:

```rust
// Registered factory names resolve within this instance's original code image.
let child = ctx.mount("worker", serde_json::json!({"queue": "notes"})).await?;

// RuntimeWorkerFactory implements PluginFactory. Its descriptor may select a
// service name at runtime; its create() makes a fresh instance per activation.
let publication = ctx.publish(
    RuntimeWorkerFactory::new("notesAnalyzer"), serde_json::json!({}),
).await?;
// Save these ChildHandle values in the parent instance for later actions.
```

`publish()` retains the factory in its originating library; no trait object or
Rust allocator crosses the ABI. The descriptor is validated and captured once.
`mount()` uses a factory already exported by the same image, even if another
image with the same factory name has subsequently been loaded. Both operations
create native ownership edges and ordinary parent cleanup entries. Nested
factories use the same path. They inherit the parent's Context isolation and
committed dependency ports, plus an explicit private owner-anchor dependency.

The creation future acknowledges allocation, not successful setup. A parent
setup must finish before its anchor-dependent children can activate. In a later
action, use `child.initialized(&ctx).await` to wait for Active, or
`child.status(&ctx).await` to inspect the actual native node. A setup waiting for
its own child, or a consumer joining a provider it keeps alive, returns
`ReentrantServiceJoin` instead of waiting indefinitely.

`ChildHandle` can be retained across actions of its parent instance. Every
operation takes the current `PluginContext` and checks that owner identity;
cloning the handle or retaining an old context does not authorize a new episode.
Dropping a creation future or handle does not remove the child. Its owner still
has to clean it up, and the admitted creation request still has to land.

`child.dispose(&ctx).await` requests retirement. `child.join(&ctx).await` waits
for actual removal, including consumer inverses, admitted calls and descendant
cleanup. A cleanup failure leaves the real node and retained factory available;
`child.retry_cleanup(&ctx).await` explicitly retries that cleanup. Status reports
allocation identity, initialization, retirement, removal and cleanup failure.
An error is not evidence of removal. Allocation followed by an observer error
still keeps its cleanup entry until the allocated node is removed.

Each parent instance has a bounded child-creation budget. Dynamic definitions
stay pinned through dependency restarts and are released after actual child
removal; failed or cancelled parent cleanup cannot destroy them early. Native
code replacement drains the old subtree before the controller activates its
replacement. These factory publications provide fresh activation semantics;
they do not implement the statically linked typed adapter's shared-slot
`ServiceHandle::set()` or transfer arbitrary Rust memory between libraries.

The `native-children` fixture and
[`rust-module-children.test.mjs`](../tests/node-loader/rust-module-children.test.mjs)
exercise publication, named and nested children, isolation, consumer barriers,
cleanup retry, failed allocation observers and replacement through real cdylibs.
The extracted npm package smoke creates and removes both kinds of child.

## Streams and objects defined by a native module

Declare `MethodKind::Stream` or `MethodKind::Object` and implement
`PluginInstance::open_stream` or `open_object`. These bounded synchronous
constructors return an SDK `Arc<dyn PluginStream>` or `Arc<dyn PluginObject>`
inside the defining library. Only an opaque integer identity and the declared
object interface cross the C ABI. The resident host adapts them to the same
stream/object capabilities used by statically linked Rust plugins.

```js
// After mounting the SDK's native-resource-consumer example (injects jsHost):
for await (const item of ctx.nativeResources.stream({ values: ['hello', '世界'] })) {
  console.log(item); // { version: 'v1', index: 0, value: 'hello' }, ...
}
const counter = ctx.nativeResources.object({ start: 10 });
try {
  console.log(await counter.call('add', 5)); // { version: 'v1', value: 15 }
} finally {
  await counter.close();
}
```

A stream admits one pull at a time. `next()` runs only when requested; EOF,
`for await` break, explicit `return()` and consumer teardown close the stream.
An object's descriptor defines its type name, allowed methods and `owned` or
`borrowed` ownership. Calls may overlap. Closing an owned object runs its async
close hook; releasing a borrowed reference does not run that hook. The plugin
must retain the referent's actual owner. These capabilities cannot be hidden
inside JSON arguments or transferred to another consumer episode.

Stream pulls, object calls and both close hooks can use `ctx.call()` against
that instance's declared JS dependencies. Close shuts admission, requests
cooperative cancellation and joins every admitted operation, including its
reverse JS calls, before executing the close hook. A blocked external Promise
can therefore block replacement or shutdown. A close error retains the native
resource and prevents successful teardown; explicit close or cleanup retry can
finish it. Successful close is followed by destruction in the original library,
and only then may instance cleanup complete.

The host records the opening consumer, committed publication and exact native
instance. Updating a JS dependency or replacing native code drains and closes
old capabilities; an old handle never redirects to the replacement. Cleanup
hooks keep their original dependency authority. Self-wait checks also apply
when a resource operation calls back into JS. Objects, stream values and job
results use the existing bounded JSON rules; this is not shared Rust memory or
an ABI for arbitrary traits. The module images remain mapped after logical
resource release.

## Ordinary Loader plugins

`createRustModulePlugin()` provides an ordinary plugin factory for a Loader entry
or for a child mounted during managed setup. It uses the same native ABI and
owned lifecycle graph, without creating a `RustModuleController` or entering a
second host transaction:

```js
import { createRustModulePlugin } from '@cordis-verus/compat-loader/rust-module-plugin';

const plugin = createRustModulePlugin(ctx, {
  name: 'native-text',
  // Optional expected module_id. Otherwise the first successful validation pins it.
  pluginId: 'text-analysis',
});
const fiber = await ctx.plugin(plugin, {
  path: '/absolute/path/immutable-text-v1.dylib',
  sha256: trustedManifest.v1.sha256,
  plugins: [{ id: 'text', factory: 'native-text-analysis', config: {} }],
});
await fiber.dispose();
```

Use the actual `module_id` exported by your plugin, or omit `pluginId`. Create one
factory per logical Loader entry; do not share a single identity-pinned factory
between unrelated native modules. The factory is bound to its Context domain and
owner activation. A foreign domain or a removed owner is rejected.

Its synchronous Standard Schema validates and copies finite JSON, then preflights
the artifact bytes, ABI, module identity and requested factories. It returns a
frozen JSON value associated with the prepared module. Normal Fiber configuration
validation happens before retiring an active episode. `apply()` consumes the
prepared value and mounts ordinary owned children; it does not load a different
artifact or obtain host coordinator authority. The root setup succeeds only after
all configured children reach Active. An empty recipe list keeps an ordinary root
Fiber with no native children.

A UI may compose an outer schema for field metadata, but its Standard Schema
validator must return the exact value produced by this validator. Cloning or
reconstructing that value loses its prepared association. Raw configuration can
be validated again, including on a later activation. Keep the source artifacts
immutable and content-addressed so restart and restoration can verify the original
bytes even after a new build has been published. The native loader's private code
copy does not make a mutable source path suitable for later validation.

This factory does not independently roll back a failed setup. Its Loader or
application coordinator owns configuration restoration and explicit cleanup
retries. Applications may compose official ConfigEditor calls and checks of named
consumers within [`officialTransaction()`](official-config-transactions.md#composing-host-operations).
Configured native children reaching Active does not establish that every external
consumer is ready. Artifact validation can execute trusted library constructors
and consume a retained-image slot, even when later validation rejects the module.

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

## Explicit state migration

A factory declares `PluginFactory::checkpoint_schema()` and implements the
synchronous `PluginInstance::checkpoint()` and `restore(Checkpoint)` hooks in
the [SDK](../crates/cordis-plugin-api/README.md#explicit-checkpoint-migration).
A managed root recipe opts in separately:

```js
const controller = await loadRustModule(ctx, {
  ...trustedManifest.v1,
  plugins: [{ id: 'counter', factory: 'native-checkpoint', state: 'migrate' }],
});
ctx.nativeCheckpoint.mutate(37);
await controller.reload(trustedManifest.v2);
// v2 receives the old logical value, converted by its restore hook.
```

The portable envelope is `{ schema, version, data }`. Matching uses the stable
recipe ID, factory name and module plugin ID. A new recipe or changed factory
starts fresh. Removing `state: 'migrate'` explicitly chooses reconstruction from
configuration. Candidate schema metadata is checked before old publication
withdrawal; the candidate still validates the actual data in `restore`, before
its setup or service publication. Code and config stay pinned independently of
the state bundle.

Capture happens inside native cleanup, after real consumer and child retirement,
owned work, exported resources and reverse JS resource finalization have drained,
and before the plugin's native cleanup hook. Consumer cleanup writes are included.
The synchronous hook receives no `PluginContext` and may only snapshot local
logical data. Successful capture seals SDK business admission and is cached;
cleanup retry reuses it. If capture fails, native cleanup and replacement stop,
and the old instance stays available for explicit `retryCleanup()`. A restore or
setup failure still cleans the partial candidate before a fresh old-code instance
restores the original checkpoint. Recovery failures retain that same source.
Terminal controller disposal cancels unnecessary checkpoint capture.

`createRustModulePlugin` supports the same recipe and also preserves logical state
across ordinary restarts of its outer Fiber. A host which validates additional
consumers must keep a transaction open through their acceptance:

```js
import { beginRustModuleMigration } from '@cordis-verus/compat-loader/rust-module-plugin';
import { officialTransaction } from '@cordis-verus/compat-loader/harness';

await officialTransaction(ctx, async () => {
  const entry = ctx.loader.resolve('native-analysis');
  const before = structuredClone(entry.options.config);
  const migration = beginRustModuleMigration(ctx, entry.fiber);
  try {
    await ctx.configEditor.edit(entry, () => candidateConfig);
    await checkRequiredConsumers();
    migration.commit();
  } catch (error) {
    migration.rollback();
    await ctx.configEditor.edit(entry, () => before);
    await checkRequiredConsumers();
    migration.commit(); // Accept the fully restored application, too.
    throw error;
  } finally {
    migration.release();
  }
});
```

The receipt is valid only in that active host transaction. Managed callbacks,
retained continuations and cleanup-only recovery transactions cannot use it.
It pins the original checkpoint through ConfigEditor's automatic restoration
and through a later consumer failure. `rollback()` selects state; the official
Loader remains responsible for restoring configuration. Only an explicit `commit()` accepts the
new or restored application. An uncommitted `release()` retains the original
recovery state, including when native providers are Active but a required
consumer failed to recover. Failed cleanup must
still be explicitly retried before a subsequent revision.

Payloads stay in memory, outside JSON/YAML configuration and artifact manifests.
The host keeps at most 64 tokens and 16 MiB of serialized source metadata plus
checkpoint data per Backend; each data value is bounded to 512 KiB and 64 nested
containers. Transactions need room for both old receipts and newly armed roots.
Successful commits, actual outer-Fiber removal and terminal controller disposal
release obsolete tokens. Ordinary episode restarts recycle prior receipts.
`inspect().images.checkpoints` exposes tokens, bytes and both limits. These are
protocol storage counts, not an allocator or process memory bound.

The plugin owns the business meaning of its schema, including version upgrades.
It must coordinate any independently spawned work before snapshotting, keep
cleanup from changing the transferable logical result, and handle partial
restore in cleanup. A checkpoint is not crash persistence, an external-I/O
transaction or a snapshot of arbitrary Rust memory. Native pointers, `Arc`,
resources, callbacks and child handles cannot be restored across images; save
logical child descriptions and create fresh owned publications during setup.
The Harness fleet example follows this pattern for dynamic worker names.

## Diagnostics and retained code

`plugins.snapshot()` returns a frozen view of the committed module metadata,
revision, managed entry Fiber IDs and immutable factory references. It also
lists journal roots retained after cleanup failure. The snapshot's state is the
last controller transaction state; actual entry states remain visible if an
outside owner disposes them. A stale owner's next reload is rejected.

`plugins.inspect()` adds live native diagnostics under `images`:

- `modules`: modules registered in this Context's Driver, including current
  instance/job/stream/object counts and `reverseCalls` awaiting JS completion.
  `retainedInstances`, `retainedJobs`, `retainedStreams`, `retainedObjects` and
  `retainedReverseCalls` record resources whose completion or destruction could
  not be confirmed.
- `retainedImageCount` and `retainedImageLimit`: the code-image count and hard
  limit shared by environments using the same resident addon image. The initial
  limit is **128**, including loaded images that failed descriptor validation.
  This counter is not a per-controller or per-Context allowance. Loading an
  independent copy of the resident addon has an independent static budget.
- `retained: true`, `unloadSupported: false`: successful instance cleanup does
  not unload code mappings.

These counts describe tracked host adapters and leases, not every allocation
inside arbitrary plugin code. If acquisition fails before a handle is returned
(for example, a panicking object descriptor), the SDK may quarantine a resource
which the host cannot enumerate individually. Its owning instance remains
retained and cleanup fails; zero known stream/object handles alone is not proof
of complete cleanup. Successful teardown requires every resource counter and
the graph's cleanup result to agree.

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
failed cleanup retry, candidate rollback, versioned checkpoints, capture/restore
failures, transaction-pinned rollback, digest rejection and post-disposal
resource diagnostics. Controller tests additionally cover domain FIFO, shutdown,
stale owners, reentry, external consumer barriers and post-allocation observer
failures. Ordinary-plugin tests exercise managed setup, validation before old
retirement, immutable prepared configuration, stale owners, foreign domains,
explicit host restoration and final native resource counts.

These are host/ABI integration tests. Existing Verus contracts still govern the
native lifecycle kernel; they do not prove the C boundary, OS dynamic loader,
arbitrary Rust plugin cleanup claims or external side effects. Rust core changes
and statically linked addon changes still require rebuilding the resident addon
and restarting its host.
