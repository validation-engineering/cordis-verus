# DeepSeek Cordis compatibility

`@validation-engineering/cordis-compat-deepseek` provides compatibility with the pinned **`@deepseek-ai/cordis` 4.0.4** interface over the shared Rust driver. It is a Cordis runtime interface, not the complete DeepSeek Harness application. Use the companion Harness application for the official CLI, Web UI and agent workflows.

The name identifies the compatible runtime distribution: **Cordis**, **compatibility**, **DeepSeek**. This replaces the ambiguous `@validation-engineering/cordis-harness` package name. The internal `harness` policy and lifecycle behavior remain unchanged. See [package boundaries and migration](../../docs/package-boundaries.md).

```js
import { Context } from '@validation-engineering/cordis-compat-deepseek';
const app = new Context();
const instance = await app.plugin((ctx, config) => {
  ctx.logger.info('started', config);
}, { enabled: true });
instance.update({ enabled: false }); // Harness update returns void
await instance.await();
await app.dispose();
```

For unchanged plugins importing the upstream name, start Node 22.22 or newer with `--import @validation-engineering/cordis-compat-deepseek/register`. ESM, dynamic import, CommonJS and createRequire route bare `@deepseek-ai/cordis` to this package. Mixed Cordis profiles and upstream deep imports are rejected by the bootstrap. The core npm package includes the matching precompiled native addon for all four supported platforms; compiling is only needed for source development or custom native code.

Raw configuration is resolved through `internal/config` and Standard Schema on every activation, after required services are available. Pending updates defer resolution. Active updates resolve synchronously and emit `internal/update`; their return value is void. Related dependency notifications may retry failed setup. Cleanup failures remain blocked until an explicit retry succeeds.

The facade intentionally fixes the upstream wrapper receiver defect: `ctx.plugin(...).update(...)` targets the actual fiber, just as the standalone profile does. Native cancellation, publication lease draining and cleanup failure reporting are stronger contracts than upstream; full behavioral equality is not claimed. The shared Logger/Context/Service API does not mean every Harness Loader, lazy/volatile configuration, HMR or application package is supported. See `docs/node-compatibility.md` for the evidence matrix.

Type declarations are generated from the common facade surface by `scripts/sync-profile-types.mjs`, with Harness's void update contract and its own Context augmentation scope.
