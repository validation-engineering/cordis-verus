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
