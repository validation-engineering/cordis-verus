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
artifact; it is not counted as an application addon. `ProcessDomain`, described below, provides that separate OS process boundary.

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

Supported same-environment ESM/CJS replacement is now provided by the
[official in-place HMR adapter](official-in-place-hmr.md), with explicit ownership,
identity and cleanup contracts. The [official configuration bridge](official-config-transactions.md)
coordinates configuration revisions and the admitted HMR path. The Harness
application also offers an opt-in Web/standard process supervisor. These are
separate strategies from the Worker graph replacement described above.

Remaining work includes complete static graph extraction for arbitrary build
tools, unexecuted dynamic imports, broader application supervisor coverage and
cross-platform acceptance. Arbitrary native addons still require a process
boundary; independently compiled plugins can instead use the explicit
[native module ABI](native-rust-modules.md). None of these mechanisms establishes
a paper proof of module loading or arbitrary plugin code.

The mechanism follows Node's documented [synchronous customization hooks](https://nodejs.org/api/module.html#synchronous-customization-hooks)
and the distinction between [ESM and CommonJS caches](https://nodejs.org/api/esm.html#no-requirecache).
Acceptance uses the project's pinned Node 22.22 baseline; current documentation
alone does not establish support on older Node versions.


## ProcessDomain: application native addons and external hosts

The exported `@cordis-verus/compat-loader/process` API executes each artifact in
its own operating-system Node process. It reuses the Worker supervisor's serial
revision queue, captured artifact journal, restoration sequence and cleanup
barriers. `pid` identifies the currently active child, and changes on every
replacement and restoration. The default host creates exactly one native Cordis
Context and JSON Loader in that child.

```js
import { ProcessDomain } from '@cordis-verus/compat-loader/process';

const domain = new ProcessDomain({ entry: 'cordis.json', timeout: 30_000 });
const loaded = await domain.load('./materialized-project');
console.log(domain.pid, loaded.plan.strategy); // a child PID, process-restart
await domain.call('tools', 'execute', { operation: 'inspect' });
await domain.reload();
await domain.dispose();
```

Unlike `WorkerDomain`, this executor permits captured application `.node` addons.
Their code is loaded only in the child, and replacing the domain replaces its OS
process. The observed graph still records their actual resolution. This avoids
assuming that an arbitrary addon is safe to unload or reinitialize in a Worker.
The regression and extracted-package smoke load a real copied Node-API binary;
they do not infer native support from a filename-only fixture.

Business calls use Node's dedicated JSON IPC channel, independently of stdout and
stderr. Only finite JSON values cross that API. A parent closes new admission,
waits for accepted calls to land, requests host cleanup, receives an explicit
cleanup acknowledgement, and then requires a normal exit with code zero. An
acknowledgement alone is insufficient: a leaked timer/socket that keeps the child
alive blocks replacement. An unexpected exit or IPC disconnect, even exit zero,
is abandonment. Startup/call/exit timeouts establish no cleanup success; failed
cleanup blocks new revisions until explicit disposal succeeds or `abandon()`
terminates the child. Forced termination returns `cleanupConfirmed: false`.
Candidate startup failure restores the old captured bytes only after candidate
cleanup and exit have both been confirmed. Old cleanup failure, candidate cleanup
failure and failed old-artifact restoration remain distinct outcomes.

`env` overlays the inherited environment and is snapshotted at construction;
`NODE_OPTIONS` and `NODE_PATH` are removed so implicit preload flags cannot replace
the explicit bootstrap. `cwd` optionally selects an existing persistent workspace
outside the private artifact copy. It is never removed by the supervisor. Output
inherits the parent's streams by default; `stdio: 'ignore'` discards it, or
`onOutput({ stream, data })` receives UTF-8 chunks. Output is not retained in
diagnostics, and observers must handle its potentially sensitive contents.
Exceptions from this observational callback do not interrupt cleanup.

Every launch comes from `Artifact.launch()` and owns a private temporary copy.
The release function accepts only directories registered by that allocator;
source project directories, arbitrary paths and persistent `cwd` are rejected as
cleanup targets. A failed spawn without a PID still releases its allocated copy
when explicitly abandoned.

### Trusted host adapter contract

A host such as the official Harness CLI already creates its own Context and
composition. Supply `hostModule` to use that implementation instead of creating a
second JSON Loader Context:

```js
// trusted-host.mjs — kept outside the replaceable application artifact
export function createHost({ directory, entry, allowPending }) {
  const host = createApplicationHost({ directory, entry, allowPending });
  return {
    ready: host.start(),
    call: (service, method, args) => host.call(service, method, args),
    diagnostics: () => host.diagnostics(),
    close: () => host.close(),
  };
}
```

`createHost` must be synchronous and immediately return its cleanup controller.
`ready` is a Promise that settles after actual initialization. Its rejection does
not hide that controller: the supervisor still calls `close()` to drain partial
startup. If module evaluation or `createHost` fails before exposing a controller,
clean teardown cannot be established, and the child remains blocked pending
explicit abandonment. `close()` must wait for application cleanup; normal process
exit remains independently checked. Do not use `process.exit()` to simulate an
acknowledgement or bypass pending work.

The host's root module is canonicalized and hashed when constructing the
supervisor. `hostProvenance` and the process reload plan expose that identity.
The hash is checked before candidate retirement/launch and around child import;
changes require a reviewed new supervisor. This does **not** capture or certify
all transitive host dependencies: the embedding application must separately lock
and verify its host installation. Application artifacts remain separate, immutable
restoration inputs; the adapter must load their private `directory`, not mutable
original source. Host initialization is outside the application module graph.
Captured plugin dependencies remain confined to their artifact, builtins, and
the exact Cordis or Harness facade URL. A trusted adapter may supply the official
single-Context composition without turning all external paths into allowed
application imports.

The process boundary isolates ordinary addon crashes and module-global state. It
is not an OS security sandbox, does not stop deliberately spawned grandchildren,
and does not roll back filesystem/network side effects. Arbitrary addons, native
ABIs, platforms and host adapters require their own acceptance evidence. The
current process tests cover real PIDs, addon import/restart, transitive updates,
accepted-call draining, candidate rollback, both cleanup failure phases, failed
restoration, partial-host startup, malformed IPC, failed spawn, persistent-path
protection, and timeout/abandonment.
