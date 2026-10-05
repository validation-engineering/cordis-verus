# Real Harness plugin graph differential

Run from the repository root after installing the exact npm lock and building
the native addon:

```sh
npm ci --ignore-scripts
npm run build:native
node scripts/check-harness-compat.mjs
```

`--backend=upstream` runs the original baseline without requiring an addon;
`--backend=native` runs the native assertions only. The default `all` is required
for a compatibility result: it executes both backends in separate Node processes
and compares their complete ordered observation traces with `assert.deepEqual`.
A failed assertion, failed child process, missing trace, timeout, or unequal trace
fails the command. There is no allowed-failure or skip list.

The fixture mounts shipping sources from the exact DeepSeek Harness revision in
`upstream.lock.json`:

- `SessionStore`, including its pending optional `typert` injection.
- `SystemPrompt` and `ToolRuntime`, with the actual schema and execution pipeline.
- `SessionProjectionRegistry` and the real `tool-todo` plugin.
- The real `createScope` primitive, which owns a pending fiber and its resources.

The global scenario verifies tool schemas and prompt assembly, successful calls,
argument and policy rejection, real session events and projection snapshots,
pre-dispatch cancellation, cancellation while awaiting policy, plugin disposal,
and reloading the same plugin with different policy. The scoped scenario verifies
scope-local tool visibility, prompt assembly, event routing, immediate observer
registration while the scope fiber is still pending, concurrent disposal callers,
child-plugin cleanup, and calls after disposal. Root disposal must remove the
actual service/plugin registry entries in both scenarios.

No Harness service or plugin is replaced. The fixture supplies ordinary requests,
policy/observation callbacks, and an `{ id, session }` agent data carrier backed by
the real `SessionStore`, matching the upstream tool-todo unit-test convention.
It does not run an agent loop, provider, model, sandbox process, or network call.
This is evidence for this graph and these cases, not complete Harness or paper
conformance.

The esbuild resolver selects original workspace `src` entrypoints instead of
missing generated `lib` files. The single runtime-relative package metadata read
in LLM attribution receives an exact copy of its original package manifest beside
the generated bundles. Upstream source files are never modified. All six required
shipping modules must occur in the esbuild input graph; missing workspace exports
are fatal rather than replaced with stubs.

Reports live under `target/harness-compat/{all,upstream,native}.json` and contain
raw traces and errors, upstream commit/tree identity, resolved workspace entries,
esbuild inputs and bundle digests, runtime asset provenance, native build evidence,
source hashes, and the installed npm dependency digest. The command checks a clean
locked upstream checkout and input/dependency hashes before and after execution.
The native addon must match its source/build record. Stale or concurrently changed
inputs fail the check. Reports and bundles are generated outputs, not committed
certificates.

Observations explicitly project session events to their sequence, type and data;
wall-clock metadata is outside this fixture's contract. There are no post-run
trace edits, sorting, timing normalization, or expected divergences that can turn
a failed comparison into a pass.
