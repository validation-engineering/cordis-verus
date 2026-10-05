# Experimental native Cordis facade

This package executes JavaScript plugins in Node and delegates activation, dependency
selection, invalidation, cleanup admission and removal to `cordis-driver` through
`cordis-node`. It does not include the upstream Fiber scheduler. Values, callbacks,
closures, iterators and Promise objects stay in the Node environment.

From the repository root:

```sh
node scripts/build-node.mjs
node --test tests/node-compat/*.test.mjs
npm run test:types
```

```js
import { Context, Service } from './packages/compat-cordis/index.js'

class Greeter extends Service {
  constructor(ctx) {
    super(ctx, 'greeter')
  }
  greet(name) { return `Hello, ${name}` }
}

const ctx = new Context()
await ctx.plugin(Greeter)
await ctx.inject(['greeter'], ctx => {
  console.log(ctx.greeter.greet('Alice'))
  return () => console.log('consumer cleanup')
})
await ctx.dispose()
```

`Context.settle()`, `Context.dispose()` and `Context.snapshot()` are explicit native
host extensions. `await ctx.plugin()` can return a Pending fiber when a dependency
is absent, as upstream does. Check its state when readiness is required. IDs use
decimal strings at the native protocol boundary; public uid retains upstream number/null shape.

The default addon is selected from `native/manifest.json`; a local build keeps its
binary at `native/cordis.node`, while an assembled bundle uses `native/prebuilds/`.
Selection verifies the target, Node-API floor, binary SHA-256 and build provenance.
`@cordis-verus/compat-cordis/native-artifacts` exposes the same selector for auditing.
`CORDIS_NATIVE_BINDING` or the Context constructor's `addon` option can select an
explicit custom build, outside the default artifact manifest. Missing/incompatible
addons fail: startup validates the ABI, profile, package identity and object-table value model before constructing the driver. There is no JavaScript scheduler fallback. ESM and CommonJS share the
same constructors and symbols. The package is private until its compatibility and
platform matrix are accepted. Node 22.22 is the local development baseline, not a
claim that the Node 24 or multi-platform release matrix passed.

The implemented surface includes function/object/class plugins, initialization,
service injection, dynamic publications and checks, isolation, callable services,
mixins/accessors, method/class decorators, LoggerService, events, effects and
explicit owned tasks. Rust and Node use the same lifecycle control driver.
`@cordis-verus/compat-harness` selects a separate configuration/retry policy;
`@cordis-verus/compat-loader` adds JSON loading and fresh-Worker artifact recovery.

This is not complete Cordis/Harness compatibility. The full upstream suite is
executed unchanged and preserves known lifecycle safety differences. Deep imports,
complete upstream types/Loader APIs, fine-grained HMR and mixed Rust/JS business
services remain separate work. See `docs/node-compatibility.md` for commands,
evidence, profile policies and remaining acceptance gates.

JavaScript callbacks are not Verus-verified. Invocation provenance detects stale
managed setup continuations, but cannot identify arbitrary escaped closures that
retain the same Context object. Async iterators must cooperate with cancellation;
a pending user Promise can keep disposal draining.

The language-level `utils.js`, `service.js`, `events.js` and `logger.js` are adapted from the
MIT-licensed upstream Cordis commit
`f8ea3cd50f1a5724e8e715995bcde131c9c12b2c`. Their copyright and license are retained
in `LICENSE.upstream`. Lifecycle scheduling is independently implemented by the
Rust driver; reused JavaScript modules do not implement the original scheduler.

Local packaging: run `node scripts/check-npm-package.mjs` from the repository root
after building. It packs and independently installs all three packages offline,
requires the installed manifest to equal the source manifest, and rejects unlisted
or custom SDK `.node` files. `scripts/package-native.mjs` combines locally supplied
artifacts from the same source snapshot without downloading or publishing.
Only targets with actual artifact provenance are available; declaring a target is
not evidence that its CI job or release acceptance passed. Hashes are not signatures.
See `docs/native-distribution.md` in the source repository for the complete contract.
