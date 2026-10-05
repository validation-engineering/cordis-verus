# Load a Cordis plugin over the native driver

From the repository root, build the addon and run the example:

```sh
npm ci
npm run build:native
node --import ./packages/compat-cordis/register.js examples/node/basic.mjs
```

`basic.mjs` and its dynamically imported plugin both use the original
`import { Context, Service } from 'cordis'` API. The explicit preload routes those
imports to this repository's compatibility facade. Plugin values, classes and
configuration callbacks stay in JavaScript; the Rust addon decides lifecycle
transitions and committed dependency identities. Disposal waits for the consumer
cleanup before the provider's cleanup.

For an application that has installed the workspace package, the equivalent
bootstrap is:

```sh
node --import @cordis-verus/compat-cordis/register app.mjs
```

The package is currently private and is not published to npm. The example uses
a local plugin module; an installed plugin can likewise be loaded with
`await import('plugin-package')`, provided it uses the implemented API subset.
Its dependency on `cordis` must be external to its build output, rather than
bundled into its own scheduler implementation.

The bootstrap uses synchronous Node module hooks so ESM, CommonJS and
`createRequire()` share one facade. It must run before plugin imports. See the
[Node 22.22 module hook documentation](https://nodejs.org/download/release/v22.22.0/docs/api/module.html#customization-hooks).

This is an experimental entry point, not a complete ecosystem compatibility
claim. Only the bare `cordis` specifier is routed. Cordis deep imports,
`@cordisjs/core`, and the Harness profile are rejected explicitly. A plugin's
relative or absolute import of a private original runtime, an already loaded
runtime, or a bundled copy cannot be certified by this bare-import hook.
Unrelated modules use normal Node resolution. The preload changes only its Node
environment; it does not edit global npm configuration or package installations.

Use built JavaScript modules for this example. The bootstrap does not provide a
TypeScript compiler, tsconfig aliases, package installation, Loader, Includes,
configuration persistence, module replacement, or HMR. Those remain separate
architecture milestones. Node's own treatment of TypeScript sources is not a
compatibility guarantee of this bootstrap.
