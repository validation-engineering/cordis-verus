# Official in-place module reload

The native preload installs `installOfficialTransactions()` before booting the pinned official Harness classes. `Hmr.partialReload()` now replaces JavaScript plugin generations inside the existing main-thread Context. The official watcher, debounce, configuration paths and `runExclusive()` queue remain in use; the adapter replaces the unsafe cache/disposal part of the pinned implementation. No upstream source files are edited.

## Operation

Use the ordinary official HMR watcher for local plugin files. Explicit host-controlled reloads can use the same service:

```js
// Use the canonical module URL, as the official watcher does.
ctx.hmr.stashed.add(new URL('./plugins/search/implementation.mjs', ctx.baseUrl).href);
await ctx.hmr.partialReload();
```

`partialReload()` admits directly through the domain queue; wrapping it in `hmr.runExclusive()` is optional. An invocation already in the admitted official queue joins that transaction. Managed setup, cleanup and event callbacks cannot acquire this host authority. Accepted revisions precede shutdown; requests after shutdown admission and retained old HMR handles fail.

The execution sequence is:

1. Read the existing ESM jobs, CJS cache children and previously observed resolution edges. Determine every configured plugin that depends on changed modules, including shared leaves.
2. Reject unsupported host ownership and native-addon boundaries before retiring old plugins.
3. Dispose affected old plugin roots and wait for every cleanup result. Only after confirmed cleanup, remove affected ESM/CJS cache entries.
4. Import canonical URLs and activate replacement factories. No query-string import trick is used. Unchanged dependency and unrelated entry identities remain intact.
5. On failure, dispose every candidate, restore the exact old cache entries and module factories, and reactivate the old plugins. The failed request still rejects.

Named Loader entry factories include their direct registry instances in the affected runtime. An affected factory exported only as a separate named value or mounted only through an unresolvable builtin is not silently left running: observable unmanaged factory ownership rejects before cleanup. An affected parent recreates its owned descendants through its normal setup; the host does not mount duplicate children under disposed owners.

## Dependency coverage and cache isolation

The graph includes static ESM links, `require.cache` child links, and successful synchronous Node resolution observations installed before application imports. The latter cover executed `import()` and `createRequire()` edges. The official watcher additionally admits changed require-only CJS leaves to its existing batch.

This is an observed graph, not a static analysis of arbitrary JavaScript. Imports that have never executed are unknown. External references retained outside the configured application, another HMR domain's module ownership, the runtime facade, HMR's own coordinator and application native addons require a different boundary. Arbitrary closures containing undiscoverable module references are outside this contract.

ESM and CJS caches are process-global, so coordinated HMR operations share a process cache queue inside their domain admission. Candidate import/setup work carries an independent asynchronous origin. Recovery removes candidate additions only; ordinary concurrent imports through an unchanged shared utility keep their cache entries and graph edges. An ordinary import of an affected module during cache replacement rejects with `OFFICIAL_HMR_MODULE_BUSY`. This is an admission check for supported loader paths, not a JavaScript sandbox or an arbitrary resource rollback mechanism.

Native addons are never unloaded in place. A known application addon dependency rejects before old teardown. Candidate resolution refuses a newly introduced `.node` load, and the candidate graph is checked again before setup. The native Cordis facade remains a trusted, unchanged host boundary. Use `ProcessDomain` when the application's native libraries or complete environment must change.

## Failures and resumable recovery

| Code | Result |
| --- | --- |
| `OFFICIAL_HMR_CLEANUP_FAILED` | Old cleanup is unconfirmed; caches are unchanged. |
| `OFFICIAL_HMR_RELOAD_FAILED` | Candidate failed, but old cache identities and factories were restored (`details.restored: true`). |
| `OFFICIAL_HMR_RECOVERY_BLOCKED` | Candidate or retained cleanup failed; old activation has not been claimed. |
| `OFFICIAL_HMR_RESTORE_FAILED` | Old caches are restored, but old activation failed. |
| `OFFICIAL_HMR_HOST_BOUNDARY` | An observed owner lies outside supported replacement scope. |
| `OFFICIAL_HMR_NATIVE_ADDON` | An application addon requires a process boundary. |

Failure causes retain both candidate and cleanup/restoration errors. `hmr.lastReloadFailure` exposes a currently retained recovery failure, if any. The journal preserves old factories, configurations, parents and cache entries across partial cleanup and restoration failure. Nothing automatically retries a failed inverse.

After explicitly repairing the failure and successfully calling `retryCleanup()` on the failed Fiber, the next normal `partialReload()` resumes the retained journal before processing its new batch. It finishes outstanding candidate disposal, restores the old caches and factories, and then plans the new revision. This uses an ordinary admitted transaction; recovery-only transactions never gain permission to mount plugins. Parent generation and Loader entry/configuration identity are checked before restoration. Replacing or deleting the owning configuration can make that retained recipe stale; such a failure is reported instead of resurrecting a removed entry.

Old module evaluation side effects, unmanaged I/O and external process state cannot be rolled back by restoring Node caches. Plugins should register owned resources and async cleanup through their Context. In-place reload does not promise that Node/V8 releases all memory associated with prior module generations; long-running environments can use an explicit Worker or Process restart policy.

## Validation scope

The companion application executes real pinned Loader, HMR and Timer classes with `--expose-internals`. Tests cover ESM, CJS, `createRequire`, executed dynamic imports, transitive/shared changes, unrelated identity, async inverse ordering, syntax/setup/cleanup/restoration failures, retained recovery, native addons, concurrent ordinary imports, real filesystem watcher dispatch, domain FIFO, shutdown, stale HMR handles and callback reentry. The default Web and headless CLI compositions are checked separately. These are Node-host integration results, not Verus proofs of module evaluation or arbitrary plugin callbacks.
