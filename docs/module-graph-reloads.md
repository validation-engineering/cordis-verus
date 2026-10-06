# Module graphs and reproducible Worker reloads

`@cordis-verus/compat-loader/worker` now exposes the dependency edges observed by
Node in a running `WorkerDomain`, and a reviewable plan for replacing its captured
artifact. This is a full Worker restart boundary. It does not preserve JavaScript
objects, mutate the current module namespace, or clear Node's caches in place.
The official Harness main-thread HMR service is a separate integration.

```js
import { WorkerDomain } from '@cordis-verus/compat-loader/worker';

const domain = new WorkerDomain({ entry: 'cordis.json' });
await domain.load('./materialized-project');

const graph = await domain.moduleGraph();
const plan = await domain.planReload();
console.log(plan.changedFiles, plan.affectedModules, plan.unobservedChanges);
if (plan.strategy === 'process-restart-required') {
  // Hand this artifact to a separately configured process supervisor.
  // WorkerDomain does not silently launch one or terminate the active Worker.
} else if (!plan.identical) {
  const result = await domain.reload();
  console.log(result.digest, result.plan);
}
await domain.dispose();
```

`planReload(directory?)` captures candidate bytes and compares their hashes and
modes with the retained active artifact. It never imports or evaluates candidate
JavaScript. It also reports added/removed directories, including empty ones.
Planning is advisory: `reload()` captures the source again, and returns the plan
for the exact captured bytes it actually used. Callers must compare that returned
digest if they care about edits made between planning and execution. An explicit
`reload()` still restarts when bytes are identical; the caller can use
`plan.identical` to avoid an unnecessary restart.

## Observed edges and invalidation

Synchronous Node resolve/load hooks record the actual ESM, CommonJS,
`createRequire(import.meta.url)`, package conditional-export, and executed dynamic
import resolutions. Nodes use paths relative to the artifact; URL queries and
fragments remain part of module identity. Edges retain the original specifier and
whether Node resolved it with import or require conditions. CommonJS cache hits
can bypass resolve hooks: snapshots additionally read Node's `require.cache`
child records, without deleting or modifying them. Such edges have
`source: 'require-cache'` and `specifier: null`, since that cache does not retain
the original specifier. Builtins and the
selected Cordis host facade appear as external endpoints, not copied project
files. The host facade continues to use the one native-backed runtime inside that
Worker.

For each changed file, the plan identifies previously observed modules backed by
that path and walks reverse dependency edges to their importers. Cycles are
visited once, including CommonJS cyclic cache hits. This is useful for explaining why a change affects a plugin and for
future finer-grained module adapters. The executor currently replaces the entire
Worker even if the observed closure is small.

`coverage: 'observed'` is deliberate. An unexecuted dynamic import, filesystem
resource read, or a resolution route affected by `package.json` is not a complete
static graph. `unobservedChanges` lists changed files with no observed module
node. These changes still belong to the captured artifact and trigger the same
conservative restart. A service call which performs a dynamic import can add edges
between snapshots. Graph inspection does not drain business calls or freeze their
behavior. Dependencies must be materialized within the artifact; symlinks remain
unsupported. Ordinary project imports resolving outside that artifact fail with
`MODULE_OUTSIDE_ARTIFACT`, preserving the underlying error cause through the
Worker boundary.

This mechanism is not a sandbox or a static verifier. Plugins which load code
through VM evaluation, direct `process.dlopen`, custom module hooks, or a fabricated
external `createRequire` base are outside this observed-graph contract. Arbitrary
external effects are not undone by module replacement.

## Native addons and failure recovery

Any application artifact containing a `.node` file is classified as
`process-restart-required`, including currently unreferenced addons. `load()` and
`reload()` reject it with `PROCESS_RESTART_REQUIRED` before closing the current
Worker. This conservative policy avoids implicitly certifying third-party addons
for multiple Node environments or unload/reload. The pinned host facade's native
addon is part of the separately tested host runtime, outside the application
artifact; it is not counted as an application addon. No general process supervisor
is implemented by this API.

For an eligible candidate, the existing supervisor sequence remains:

1. Close business admission and drain calls already accepted by the old Worker.
2. Wait for normal plugin cleanup, a shutdown acknowledgement, and a successful
   Worker exit.
3. Launch the candidate from a private copy of its captured files.
4. If startup fails, confirm candidate cleanup and recreate the retained old
   artifact in another fresh Worker.
5. Release the old artifact only after successful replacement.

A failed candidate cannot replace its old dependencies with changed source files:
restoration uses the retained, hash-checked artifact. Old or candidate cleanup
failure leaves the domain blocked; abnormal exit remains abandonment. Neither a
timeout nor forced termination is normal cleanup. There is still a restart gap,
and external clients must reconnect through JSON endpoints. No atomic rollback of
external side effects is claimed.

## Evidence and remaining scope

`tests/node-loader/module-graph.test.mjs` executes real ESM-to-CJS transitive
changes, `createRequire`, conditional exports, a delayed dynamic import, candidate
planning without evaluation, exact re-capture after planning, failed candidate
restoration, application-addon refusal before retirement, and source escape
rejection. The existing Worker lifecycle suite covers in-flight call draining,
cleanup failure, crash/exit acknowledgement, and retained-artifact integrity.
Actual declarations are compiled in `tests/node-loader/types/module-graph.ts`.

Still separate work: same-environment ESM/CJS module replacement with identity
contracts, certified application native addons or a process supervisor, complete
static graph extraction for an arbitrary build tool, and connecting the official Harness module watcher to a Worker/process boundary.
The [official configuration bridge](official-config-transactions.md) coordinates
configuration revisions and rejects main-thread module-cache replacement. This feature is not a paper proof of module loading
or arbitrary plugin code.

The mechanism follows Node's documented [synchronous customization hooks](https://nodejs.org/api/module.html#synchronous-customization-hooks)
and the distinction between [ESM and CommonJS caches](https://nodejs.org/api/esm.html#no-requirecache).
Acceptance uses the project's pinned Node 22.22 baseline; current documentation
alone does not establish support on older Node versions.
