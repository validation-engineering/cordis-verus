import { Context } from '@cordis-verus/compat-cordis';
import { loadRustModule, RustModuleController, type RustModuleDescriptor } from '@cordis-verus/compat-loader/rust-module';
const ctx = new Context();
const controller = await loadRustModule(ctx, { path: '/plugin.dylib', sha256: 'digest', plugins: [
  { id: 'text', factory: 'native-text-analysis', config: { threshold: 3 } },
] });
const snapshot = await controller.reload({ path: '/plugin-v2.dylib', sha256: 'digest-v2' });
const descriptor: RustModuleDescriptor | null = snapshot.module;
void descriptor;
const budget: number = controller.inspect().images.retainedImageLimit;
void budget;
const retained: true = snapshot.retained;
void retained;
await controller.reconcile({ path: '/plugin-v3.dylib', sha256: 'digest-v3', plugins: [{ id: 'changed', factory: 'native-text-analysis', config: { threshold: 4 } }] });
await controller.reconcile({ path: '/plugin-v3.dylib', sha256: 'digest-v3', plugins: [] });
// @ts-expect-error Reconciliation requires a complete replacement recipe.
controller.reconcile({ path: '/plugin-v3.dylib', sha256: 'digest-v3' });
// @ts-expect-error Reconciled config remains JSON.
controller.reconcile({ path: '/plugin-v3.dylib', sha256: 'digest-v3', plugins: [{ id: 'text', factory: 'native-text-analysis', config: () => {} }] });
await controller.retryCleanup();
await controller.dispose();
new RustModuleController(ctx, { plugins: [{ id: 'text', factory: 'native-text-analysis' }] });
// @ts-expect-error Artifact digests are mandatory.
controller.reload({ path: '/plugin.dylib' });
// @ts-expect-error Plugin config crosses a JSON ABI boundary.
new RustModuleController(ctx, { plugins: [{ id: 'text', factory: 'native-text-analysis', config: () => {} }] });
// @ts-expect-error Generation identity is readonly.
snapshot.module!.factories[0].ref = 'next';
// @ts-expect-error Controllers do not expose physical image unloading.
controller.unload();

const resources = controller.inspect().images.modules[0].resources;
const tracked: number[] = [resources.streams, resources.objects, resources.retainedStreams, resources.retainedObjects];
void tracked;
const methodKind: "sync" | "async" | "stream" | "object" = controller.inspect().images.modules[0].factories[0].services[0].methods[0].kind;
void methodKind;
