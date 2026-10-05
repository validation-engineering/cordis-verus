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

Resolution still requires an explicit existing file path and applies `rootDirectory` confinement. The adapter replaces only module loading; it does not bypass JSON validation or lifecycle cleanup. It must return the same plugin object and revision while the executable factory is unchanged. A changed identity or revision requests replacement of entries using that module. Revision is a comparison token, not a claim that Node's dependency cache was reset. Publish immutable factory snapshots: the retained old plugin object must remain executable for rollback. Building source, evaluating it in another environment, deciding the dependency closure and maintaining those factory snapshots remain the embedding host's responsibility. Use `WorkerDomain` when an ESM/CommonJS environment and its transitive dependencies must actually be replaced.

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

### Artifact contract

Publish a complete, stable input directory before capture. Include all relative imports, installed dependencies, resources and configuration. The directory must not change during capture. `.git` is excluded; symlinks, special files and artifacts exceeding configured limits are rejected. Defaults are 256 MiB and 20,000 files. Materialize symlinked package dependencies before capture. The facade/addon and Node runtime come from the host installation, not the captured project.

Keep persistent writable data outside the captured directory and pass its path explicitly in JSON config. Per-launch writable changes are discarded after shutdown. Entry modules and all JSON Include files must be inside the artifact. Arbitrary imports made by plugin code can still escape that directory; they are not a captured dependency or a sandboxed operation. Complete dependency discovery, package installation and signed release manifests remain future work.

## Current compatibility boundary

This package supports explicit file module paths and Node's normal execution of built JS/CJS. Bare npm plugin entry names, source TS transformation, YAML/custom tags, JS expressions, upstream Loader event/API compatibility, automatic config write-back, transparent in-process code HMR and Harness lazy/volatile configuration are not implemented. Plugin dependencies may use Node's normal package imports once installed in the project. A `cordis` import is routed by the existing facade bootstrap; embedded/private Cordis copies are not detected by this package.

The implementation is ordinary JS host code. Its tests establish the listed behavior; they do not add Verus proofs for module loading, arbitrary plugin callbacks, Worker teardown or filesystem operations.

Run `node --test --test-timeout=30000 tests/node-loader/*.test.mjs` from the repository root. The tests execute actual plugin files, nested JSON Include and isolated groups, candidate children, explicit readiness checks, code changes to a transitive import, snapshot recovery, cleanup failure, queued/reentrant updates, Worker crash and TypeScript usage.

## Local distribution check

`node scripts/check-npm-package.mjs --offline` stages the facade, Loader and Harness profile packages, includes the freshly recorded host-native addon and notices, runs `npm pack --ignore-scripts`, and installs the tarballs in a separate temporary project. It verifies that no workspace path or symlink supplies the packages, then runs native, Loader, Worker and Harness profile examples from that installation. The report and local tarballs are written to `target/release-artifacts/npm`. Only the tested OS/architecture/Node combination is recorded as validated; this check uploads nothing and does not establish a prebuilt distribution matrix or registry publish eligibility.
