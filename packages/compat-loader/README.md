# Native Cordis JSON Loader

This experimental package loads real JS Cordis plugins through `compat-cordis` and the Rust native driver. It adds a **JSON configuration API** and an explicit **whole-Worker code replacement API**. It does not yet implement the upstream Loader/Include classes or Harness configuration language. A Loader can use either native Context profile; the Worker bootstrap selects the Cordis profile.

Build the native addon first (`npm run build:native`). No additional runtime dependencies are required beyond the sibling facade package and Node 22.22+.

## Load a configuration in the current environment

```js
import { Context } from '@cordis-verus/compat-cordis';
import { Loader } from '@cordis-verus/compat-loader';

const context = new Context();
const loader = new Loader(context);
await loader.loadFile('./cordis.json');
console.log(loader.diagnostics());
await loader.update('greeting', { config: { prefix: 'Welcome' } });
await loader.dispose();
await context.dispose();
```

Start the program with `--import @cordis-verus/compat-cordis/register` when plugin sources import the original `cordis` package name. The registered facade is still the only lifecycle implementation.

```json
[
  {
    "id": "greeting",
    "name": "./plugins/greeting.mjs",
    "config": { "prefix": "Hello" }
  },
  {
    "id": "tools",
    "include": "./tools.json",
    "isolate": ["tools"]
  }
]
```

An input is an entry array or `{ "entries": [...] }`. Every entry has an explicit stable `id`. Module and include paths resolve relative to the configuration file that contains them. `include` adds a group; `group: true` with `entries` creates an inline group. Nested entry IDs use `/`, for example `tools/search`. IDs may contain letters, digits, `_`, `-` and `.`. Include cycles, duplicate IDs, unsupported fields and invalid JSON values fail before the active graph is stopped.

Supported options are `id`, `name`, `config`, `disabled`, `group`, `entries`, `include`, `inject`, `isolate` and `intercept`. `inject` accepts service names or a name-to-config mapping. `isolate: ["service"]` creates an entry-specific realm; `isolate: {"service": "shared-label"}` intentionally shares that label between entries in this Loader. Groups own their child fibers. Disabled groups retain entry records while skipping module imports and activation for their descendants.

Entries returned by `resolve()` keep their object identity across successful updates and restoration. A persistent Loader owner contains the configured tree. Updates compare each stable ID's canonical module URL, prepared plugin object identity and optional revision, JSON config, injection, isolation, interception, source base URL and parent. Unchanged fibers remain mounted; changed entries and descendants of changed parents are retired and recreated. Adding or removing children does not restart an unchanged group. JSON object key order and sibling reordering do not restart instances; sibling order governs newly mounted entries and diagnostics, while retained instances keep their original effect registration order.

A preserved consumer can still run cleanup and setup again when its dependency changes: the shared native driver owns that transition, and the consumer keeps its Fiber ID while its episode changes. A group's dependency restart recreates its owned children from the latest committed recipe. Changing a group's isolation/injection/interception replaces its entire subtree. Config changes currently replace the changed plugin rather than invoke upstream in-place update hooks. Explicit entry inject metadata uses a forwarding plugin callback and is not an exact upstream registry-identity implementation. The application Context and unrelated plugins are not disposed by `loader.dispose()`.

### Readiness, serialization and restoration

`await ctx.plugin()` can settle Pending. The Loader therefore checks every enabled configured entry after settlement. By default a missing dependency rejects activation with `DEPENDENCIES_UNAVAILABLE` and structured `details.entries` diagnostics. `allowPending: true` accepts a partially available tree. Diagnostics cover configured entries; arbitrary plugin-created children retain their own lifecycle API.

External `apply`, `loadFile`, `update`, `setEnabled`, `reload` and `dispose` calls enter the runtime domain's shared mutation queue at admission. All Loaders over the same Context domain share that queue with external Fiber updates, restarts, disposal and domain shutdown. Preparing a candidate is part of the transaction, so another Loader cannot activate a competing revision while its modules are being prepared. Independent Context domains keep separate queues.

Plugin setup can immediately create and await `ctx.plugin()` children; effect registration and native completion continue during a transaction. Loader retirement, recovery and cleanup use scoped transaction steps, without queueing behind their own operation. Calling a Loader mutation from an active lifecycle callback or another transaction, including a different Loader's callback or module preparation, is rejected as `REENTRANT_MUTATION`. This also applies when the requested close is already queued; joining that Promise would wait on the action currently blocking it.

`loader.dispose()` closes only that Loader and joins repeated external requests. `context.dispose()` closes admission for new domain revisions as soon as shutdown is requested, waits for previously admitted transactions, and then drains the graph. An admitted transaction can still finish plugin setup and cleanup. A cleanup failure anywhere in the domain blocks subsequent ordinary revisions; explicit cleanup retry and disposal remain available. This does not make module evaluation or external side effects atomic, add configuration write-back, or invalidate Node's module caches.

The Loader imports modules and validates candidate JSON inputs before disturbing the old tree. Runtime plugin schema validation still occurs when the replacement is mounted. It retains the old module objects and an immutable JSON recipe. Each activation gets fresh configuration objects. The changed old subtrees and their dependent cleanup drain before replacements mount. If candidate setup fails, every candidate-created fiber and its children must be removed before the replaced part of the old recipe can restart. Unaffected siblings and parents remain mounted. Group controllers are restored to the old recipe as well, so a later dependency notification cannot reactivate rejected configuration. A retained consumer that failed while observing the candidate is explicitly restarted against the restored dependencies. A cleanup failure leaves the Loader `blocked`; it does not activate the old recipe or a queued replacement. After fixing the external cause, `retryCleanup()` retries failed inverses and drains the whole Loader, including retained siblings, returning to an empty state. The caller can then explicitly load a configuration. Successful inverses are not repeated.

`RELOAD_FAILED` with `details.restored: true` means the replaced part of the old recipe was instantiated again; replaced live objects do not survive. Unchanged entries can keep their instances. Module evaluation, arbitrary global state and external file/network/database effects are not rolled back.

`loader.reload()` re-reads its last file and included JSON files, then reconciles the changed subtrees. With unchanged configuration and factory identities, it does not remount the graph. After a programmatic `update()` the source is an in-memory recipe; subsequent `reload()` uses that recipe and asks the ModuleHost to prepare its factories again. There is no implicit write-back to the original configuration files and no background file watcher.

## Explicit transactions for the official Harness Loader

The separate `@cordis-verus/compat-loader/harness` entry adapts the **installed,
unchanged** official Harness `Loader` and `Include` classes. It does not replace
this package's JSON API. `LoaderTransactions` offers explicit host operations;
`installOfficialTransactions` additionally connects the official configuration UI
and refresh/HMR queues when installed by the application before boot.
The tested contract is Harness Cordis 4.0.4, Loader 1.0.5 and Include 1.0.9.
Use the native Harness profile and a live, fully initialized tree:

```js
import { LoaderTransactions } from '@cordis-verus/compat-loader/harness';

// ctx and ctx.loader already belong to the booted official application.
// Select an Include file owned by this host, not an unrelated profile overlay.
const edits = new LoaderTransactions(ctx, ctx.loader.resolve('custom').subtree);
await edits.update('greeting', { config: { prefix: 'Welcome' } });
const id = await edits.create({ name: './another-plugin.mjs', config: {} });
// create preserves the official fully qualified id; resolve it from the root.
const rootEdits = new LoaderTransactions(ctx, ctx.loader);
await rootEdits.remove(id);
await edits.close(); // closes this adapter's admission; does not dispose the tree
```

`create`, `update` and `remove` enter the same domain FIFO as Fiber revisions,
JSON Loader updates and Context shutdown **before** changing options or files.
Cloneable options are snapshotted at admission, including `undefined` deletion
values; functions and other non-cloneable values reject before admission.
The adapter retains old and new Fibers, waits for official Loader and native
lifecycle work, and observes the actual Include write queues, including writes
scheduled by timers or teardown. This is conservatively a **whole Loader graph
barrier**: sibling Includes and existing work may delay it or report failure.
Use it from an external host operation, outside plugin setup/cleanup actions.

Success means that the observed lifecycle and persistence work completed. It is
not an atomic rollback mechanism or a guarantee of physical-disk durability after
power loss. An `OFFICIAL_PERSISTENCE_FAILED` error names affected files and retains
causes; running plugin changes may already have happened. A subsequent explicit
revision can retry the official write queue. Cleanup failures still block new
revisions until actual cleanup recovery succeeds. Pending dependencies retain
upstream Pending semantics; completion does not certify every plugin Active.
`revision` counts successful operations, `requestedRevision` counts admitted
requests, and `lastFailure` retains the last failed request's operation and error.

A cached adapter belongs to its tree owner's current episode. If that Include
is removed or restarted, `STALE_LOADER` rejects old requests before mutation;
obtain a new adapter for the new tree. Foreign domains, incompatible class shapes
and methods replaced after construction are rejected. Nested removal selects the
entry's owning tree and local id before invoking the unchanged official method.

The bridge uses `MutationSteps.capture(callback)`, whose authority lasts only
through the callback's synchronous call stack in that domain. A returned Promise
does not extend that authority; plugin lifecycle callbacks and async update
continuations cannot borrow it. Ignored lifecycle Promises are still joined.

The explicit adapter does not intercept arbitrary direct object or file mutations.
Applications can additionally call `installOfficialTransactions` with the pinned
`Entry`, `EntryGroup`, `EntryTree`, `Hmr` and `ConfigEditor` classes **before boot**.
The companion Harness application already installs it in its default preload.
That host bridge admits ConfigEditor edits before acquiring the profile file lock,
then keeps write/reconcile/rollback and Include refresh in the same domain slot.
It also orders `hmr.runExclusive` with configuration and shutdown work. The original
methods still implement the configuration semantics; no upstream source files
are rewritten. See [official configuration transactions](../../docs/official-config-transactions.md)
for setup, failure and callback contracts.

A failed inverse is not automatically retried by rollback. Readiness and restart
report the retained native barrier even when a transient JavaScript error has
already been observed; explicit cleanup recovery is required. Event and edit
callbacks cannot borrow transaction steps. `steps.observe(fiber, callback)` retains
the callback's episode identity, and `steps.isCurrent()` lets a trusted bridge
check its exact coordinator origin before capturing a synchronous continuation.
These are host APIs, not a sandbox for arbitrary application code.

Official main-thread `partialReload()` now performs dependency-closed ESM/CJS
replacement in the existing Context. It waits for old cleanup before changing
caches, preserves unrelated identities and retains a recovery journal when
candidate cleanup or old restoration fails. The official watcher includes pure
CJS leaves. See [in-place HMR](../../docs/official-in-place-hmr.md) for observed
graph coverage, concurrency, failure and native-addon boundaries.
[Worker module graphs](../../docs/module-graph-reloads.md) replace a complete
captured environment; application native addons use `ProcessDomain` below.
Runtime shape checks do not certify a different upstream version or arbitrary
EntryTree subclass.

The core gate checks admission contracts, callback isolation and type declarations;
the companion `cordis-harness` gate executes installed official classes, default
boot, real JSON/YAML edits, write/rollback failures, cleanup barriers and stale
owner rejection. These are behavioral checks, not proofs of filesystem durability
or arbitrary callback effects.

## Replace code in a fresh Worker

`ModuleHost` imports canonical file URLs. It **does not invalidate Node's ESM or CommonJS caches**. Changing a source file and calling `loader.reload()` is not code HMR. `ModuleHost.reset()` explicitly rejects with `DOMAIN_RESTART_REQUIRED`. A file edit at an already imported URL does not change the cached factory identity and is not a request for code replacement.

An embedding host can supply an adapter for **already prepared factories**:

```js
import { ModuleHost } from '@cordis-verus/compat-loader';

const moduleHost = new ModuleHost({
  loadModule: async canonicalURL => preparedFactories.get(canonicalURL),
});
// Each value is { plugin, namespace?, revision?: string | number }.
const loader = new Loader(context, { moduleHost });
```

Resolution still requires an explicit existing file path and applies `rootDirectory` confinement. The adapter replaces only module loading; it does not bypass JSON validation or lifecycle cleanup. It must return the same plugin object and revision while the executable factory is unchanged. A changed identity or revision requests replacement of entries using that module. Revision is a comparison token, not a claim that Node's dependency cache was reset. Publish immutable factory snapshots: the retained old plugin object must remain executable for rollback. Building source, evaluating it in another environment, deciding the dependency closure and maintaining those factory snapshots remain the embedding host's responsibility. Use `WorkerDomain` or `ProcessDomain` when an ESM/CommonJS environment and its transitive dependencies must actually be replaced.

Use a `WorkerDomain` for real code replacement, including changed transitive imports:

```js
import { WorkerDomain } from '@cordis-verus/compat-loader/worker';

const domain = new WorkerDomain({ entry: 'cordis.json' });
await domain.load('./plugin-project');
console.log(await domain.call('greeting', 'hello', 'Alice'));
// Build/publish the candidate project directory first.
await domain.reload('./plugin-project');
await domain.dispose();
```

Each load captures the local project directory and its dependencies/assets into a retained artifact, with content hashes and permissions. Each Worker receives a separate launch copy. Mutating launch files cannot change the retained recovery recipe. A new Worker owns a new Node environment, native Driver and real module cache. No query suffix is used to simulate dependency-graph reload.

Replacement follows this order:

1. Capture the candidate artifact while the old Worker is available.
2. Stop new requests and drain admitted service calls, then normally dispose the old native graph and exit the Worker.
3. Start the candidate Worker and require configured entries to become ready.
4. On startup failure, normally drain and exit that candidate; only then restart the retained old artifact in another fresh Worker.

A cleanup failure or unknown timeout blocks replacement. An unexpected Worker exit is `abandoned`, not a successful shutdown. `abandon()` explicitly terminates remaining Workers and returns `{ abandoned: true, cleanupConfirmed: false }`; it never automatically restores the old artifact. The default operation timeout is 30 seconds and is only a failure detector, not a cancellation or cleanup proof.

Objects/functions stay ordinary JS objects **inside** each Worker. `WorkerDomain.call(service, method, ...args)` is an explicit asynchronous JSON boundary between environments. It has no transparent callback/stream/object transport. A Worker is not an operating-system process or a security sandbox; a native crash can affect the whole process.

### Replace an OS process

Use `ProcessDomain` from `@cordis-verus/compat-loader/process` for application
native addons or a whole application process. It has the same captured-artifact
load/reload/call workflow and adds a read-only PID. A successful replacement needs
both a cleanup acknowledgement and exit code zero; a timeout or crash is not
normal cleanup. An optional trusted `hostModule` can host the official Harness
without creating another Context. See the [process contract and example](../../docs/module-graph-reloads.md#processdomain-application-native-addons-and-external-hosts)
for adapter, provenance and failure boundaries. The companion Harness exposes an
opt-in [official Web supervisor](https://github.com/validation-engineering/cordis-harness/blob/main/docs/process-supervisor.md).

### Artifact contract

Publish a complete, stable input directory before capture. Include all relative imports, installed dependencies, resources and configuration. The directory must not change during capture. `.git` is excluded; symlinks, special files and artifacts exceeding configured limits are rejected. Defaults are 256 MiB and 20,000 files. Materialize symlinked package dependencies before capture. The facade/addon and Node runtime come from the host installation, not the captured project.

Keep persistent writable data outside the captured directory and pass its path explicitly in JSON config. Per-launch writable changes are discarded after shutdown. Entry modules and all JSON Include files must be inside the artifact. Arbitrary imports made by plugin code can still escape that directory; they are not a captured dependency or a sandboxed operation. Complete dependency discovery, package installation and signed release manifests remain future work.

## Current compatibility boundary

This package supports explicit file module paths and Node's normal execution of built JS/CJS. Bare npm plugin entry names, source TS transformation, YAML/custom tags, JS expressions, upstream Loader event/API compatibility, automatic config write-back, transparent in-process code HMR and Harness lazy/volatile configuration are not implemented. Plugin dependencies may use Node's normal package imports once installed in the project. A `cordis` import is routed by the existing facade bootstrap; embedded/private Cordis copies are not detected by this package.

The implementation is ordinary JS host code. Its tests establish the listed behavior; they do not add Verus proofs for module loading, arbitrary plugin callbacks, Worker teardown or filesystem operations.

Run `node --test --test-timeout=30000 tests/node-loader/*.test.mjs` from the repository root. The tests execute actual plugin files, nested JSON Include and isolated groups, candidate children, explicit readiness checks, code changes to a transitive import, snapshot recovery, cleanup failure, queued/reentrant updates, Worker crash and TypeScript usage.

## Local distribution check

`node scripts/check-npm-package.mjs --offline` stages the facade, Loader and Harness profile packages, includes the freshly recorded host-native addon and notices, runs `npm pack --ignore-scripts`, and installs the tarballs in a separate temporary project. It verifies that no workspace path or symlink supplies the packages, then runs native, Loader, Worker, Process (including an application native addon) and Harness profile examples from that installation. The report and local tarballs are written to `target/release-artifacts/npm`. Only the tested OS/architecture/Node combination is recorded as validated; this check uploads nothing and does not establish a prebuilt distribution matrix or registry publish eligibility.
