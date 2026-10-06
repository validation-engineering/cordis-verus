# Coordinating official Harness configuration changes

`@cordis-verus/compat-loader/harness` provides two related interfaces:

- `LoaderTransactions` explicitly coordinates a host-owned official Loader or Include tree.
- `installOfficialTransactions()` installs transparent coordination for the pinned official ConfigEditor, Include refresh and HMR configuration queue. The `cordis-harness` native bootstrap installs it before mounting the default application.

The adapter keeps one native Harness Context graph. Official files remain unchanged. The installed methods still perform the official profile merge, schema validation, YAML expression handling, filesystem locking, atomic replacement and rollback. This is a host execution contract backed by tests, not a proof of those JavaScript callbacks or filesystem operations.

## Installation

Register the native Harness facade before loading the official classes, then install the bridges before creating the application graph:

```js
import '@cordis-verus/compat-harness/register';
import { installOfficialTransactions } from '@cordis-verus/compat-loader/harness';

const [{ Entry, EntryGroup, EntryTree }, { default: Hmr }, { ConfigEditor }] = await Promise.all([
  import('@deepseek-ai/cordis-plugin-loader'),
  import('@deepseek-ai/dsh-hmr'),
  import('@deepseek-ai/dsh-config-editor'),
]);
installOfficialTransactions({ Entry, EntryGroup, EntryTree, Hmr, ConfigEditor });
```

The installation uses the exact classes loaded by the application. Repeating it with the same identities is harmless; mixing previously installed classes with another set fails. Structural checks do not certify unpinned upstream versions. The application distribution records and verifies its official package inputs separately.

The bridge recognizes the published Include and the bundled `HostResolvedRootInclude` used by packaged application boot. It discovers both through the shared EntryGroup initialization path, so the private bundled Include class does not require a source rewrite.

## Admission and completion

`ConfigEditor.edit()` enters the native domain queue before the original method starts. This places admission before the official filesystem lock, profile read, write and reconciliation. It works with or without an HMR service. When ConfigEditor calls HMR internally, that call joins the admitted coordinator instead of opening a second domain transaction.

An external `hmr.runExclusive(operation)` also enters the domain queue before its original HMR queue. Its callback is a host-owned transaction operation; it is not an authorization boundary for untrusted JavaScript. Nested operations keep the original HMR rejection behavior. Calls from managed plugin setup, cleanup or an active observer cannot acquire coordinator authority through this entrypoint.

An Include refresh enters the same queue before reading its file. After the official asynchronous read, the bridge captures only the synchronous EntryGroup/Entry mutation prefix at the next known official boundary. Each capture checks the active transaction, exact callback origin and execution domain again. An AsyncLocalStorage scope alone grants no permission. Initialization and cleanup continue to use their existing lifecycle rules.

The admitted slot remains occupied until the official operation returns, its discovered Loader tasks and Fiber readiness complete, and observed Include write queues finish. This includes the original ConfigEditor rollback when reconciliation rejects. The current implementation conservatively observes the entire Loader graph, so unrelated pending Include writes can delay or reject completion. Context shutdown waits behind admitted work and rejects new external revisions.

Service identities are checked both before admission and at execution. A removed or replaced ConfigEditor/HMR instance fails with `STALE_OFFICIAL_SERVICE`. A retained Include from an old activation fails with `STALE_LOADER`.

## Callback boundaries

ConfigEditor expects a synchronous `change(current, inherited)` callback. The adapter invokes it as an observer owned by the target Fiber. It receives no transaction steps. Detached asynchronous descendants retain a distinct origin and cannot reenter the active domain revision. Thenable inspection and assimilation also occur in observer scope; asynchronous results return an adopted Promise. Later arbitrary property access by host code is the host caller's responsibility. Ordinary event observers likewise have their own episode identity; a valid waterfall continuation restores its caller only within the runtime's checked continuation contract.

These rules protect lifecycle admission. They are not a JavaScript sandbox: trusted plugin code can still directly modify objects or perform arbitrary filesystem operations. Applications must use the coordinated entrypoints for configuration mutations. Direct writes to `entry.options`, unrelated file APIs, and arbitrary custom EntryTree implementations are outside the contract.

## Failures and recovery

- A failed ConfigEditor candidate runs the official rollback before the outer request completes. A successful rollback restores the profile document and running configuration; the rejected edit still reports the candidate failure.
- A rollback file or reconciliation failure remains a failure. The adapter does not invent a successful rollback or claim that arbitrary plugin effects are reversible.
- Include persistence failures use `OFFICIAL_PERSISTENCE_FAILED`. ConfigEditor's direct atomic-write errors retain their original error contract, including filesystem failures and aggregate causes.
- Unconfirmed cleanup blocks later configuration admission before another file or options change. The runtime preserves the failed inverse and its native barrier; an explicit successful cleanup retry is required before subsequent revisions.
- A completed write means the official filesystem operation returned. It does not establish crash durability through `fsync` or a cross-file atomic commit.

## Module replacement

The pinned official `Hmr.partialReload()` clears Node caches before replacement and continues past a failed disposal. The native adapter rejects this path immediately with `OFFICIAL_IN_PROCESS_HMR_UNSUPPORTED`, before analyzing or modifying the live cache. The running generation remains intact.

Use the separate [Worker host](../packages/compat-loader/README.md) for module graph generations and replacement in a separate Node Worker environment. A Worker generation restart can refresh the complete dependency graph while keeping old-generation cleanup and activation outcomes explicit. This is not automatic migration of the default official application into a Worker, and this iteration does not claim transparent in-process module HMR.

## Evidence

The application regression suite uses real installed ConfigEditor, Loader, Include, HMR, Timer and Schemastery packages, plus real temporary profile files. It exercises filesystem-lock admission, FIFO and shutdown, the no-HMR path, asynchronous Include refresh, callback isolation, successful rollback, actual rollback rename failure, failed-cleanup recovery, packaged Include subclasses and stale service handles. Ordering checks use explicit Promise gates.

Core tests cover installation contracts, scoped coordinator authority, observer continuations and cleanup barriers. Development evidence, release negatives, cross-platform artifacts and paper refinement remain distinct gates.
