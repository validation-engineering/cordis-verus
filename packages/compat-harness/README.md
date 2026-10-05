# Harness Cordis profile

`@cordis-verus/compat-harness` selects the pinned `@deepseek-ai/cordis` 4.0.4 policy in the shared Rust driver. It is experimental; it does not run the upstream JavaScript scheduler.

```js
import { Context } from '@cordis-verus/compat-harness';
const app = new Context();
const instance = await app.plugin((ctx, config) => {
  ctx.logger.info('started', config);
}, { enabled: true });
instance.update({ enabled: false }); // Harness update returns void
await instance.await();
await app.dispose();
```

For unchanged plugins importing the upstream name, start Node 22.22 or newer with `--import @cordis-verus/compat-harness/register`. ESM, dynamic import, CommonJS and createRequire route bare `@deepseek-ai/cordis` to this package. Mixed Cordis profiles and upstream deep imports are rejected by the bootstrap. Build the matching native addon from the repository with `npm run build:native`.

Raw configuration is resolved through `internal/config` and Standard Schema on every activation, after required services are available. Pending updates defer resolution. Active updates resolve synchronously and emit `internal/update`; their return value is void. Related dependency notifications may retry failed setup. Cleanup failures remain blocked until an explicit retry succeeds.

The facade intentionally fixes the upstream wrapper receiver defect: `ctx.plugin(...).update(...)` targets the actual fiber, just as the standalone profile does. Native cancellation, publication lease draining and cleanup failure reporting are stronger contracts than upstream; full behavioral equality is not claimed. The shared Logger/Context/Service API does not mean every Harness Loader, lazy/volatile configuration, HMR or application package is supported. See `docs/node-compatibility.md` for the evidence matrix.

Type declarations are generated from the common facade surface by `scripts/sync-profile-types.mjs`, with Harness's void update contract and its own Context augmentation scope.
