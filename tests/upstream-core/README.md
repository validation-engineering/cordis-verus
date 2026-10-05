# Upstream conformance evidence

Run the 12 unmodified core spec files from the locked Cordis checkout:

```sh
npm ci --ignore-scripts
npm run build:native
node scripts/check-upstream-core.mjs
```

The runner first verifies the Git revision, tree and clean checkout. A Vite
resolver selects either the original public entry point or the native facade;
assertions, test bodies and helpers are not rewritten. Native runs reject direct
imports of upstream runtime internals. The original baseline contains 87 tests.
Type-only `events.types.ts` is outside this behavioral run.

`--backend=upstream` and `--backend=native` select a single execution for diagnosis.
Reports under `target/upstream-core/` retain every assertion status, failure text
and process exit status. A failed or skipped test makes the run fail; known
semantic differences are not silently converted into passes. Native source
hashes, facade files, upstream sources/tests, the npm lock and installed dependency
bytes bind each report to its actual inputs. Generated Vite caches are excluded
from dependency input hashes.

The profiles are different behavioral contracts. Run their shared fixtures with:

```sh
node scripts/check-node-profiles.mjs
```

This executes the same configuration and failed-dependency-refresh fixture
against both original/native Cordis and original/native Harness. Harness also
runs a synchronous mount-observer cancellation fixture that registers and drains
an effect before the child ever activates. Comparison is exact, without trace
normalization. Policy manifests in `tests/compat/profiles/` record a source audit;
they do not declare complete compatibility. The profiles report is written to
`target/node-compat/profiles.json` and has a failing exit status on a mismatch.

The original Harness returns an `Object.create(fiber)` awaitable wrapper from
`plugin()`. Its `update()` implementation writes through `this`, unlike original
Cordis. Calling `update()` on that unawaited wrapper can shadow raw configuration
instead of changing the actual Fiber. Configuration fixtures intentionally use
the real Fiber returned by `await application` so the normal profile policy and
that wrapper behavior are not conflated.
