# JSON Loader and Worker code replacement

After `npm run build:native`, run from the repository root:

```sh
node examples/node-loader/main.mjs
node examples/node-loader/worker.mjs
```

The first example loads a real plugin that imports `cordis`, then applies new JSON configuration. The second captures this project and runs the plugin in a fresh Node Worker. See [the package documentation](../../packages/compat-loader/README.md) for reload, failure recovery and the supported scope. The in-process Loader reuses module caches; only explicit Worker replacement creates a fresh code environment.
