import { Context, type Plugin } from '@cordis-verus/compat-cordis';
import { createRustModulePlugin, beginRustModuleMigration } from '@cordis-verus/compat-loader/rust-module-plugin';
import type { RustModuleRevision } from '@cordis-verus/compat-loader/rust-module';
const ctx = new Context();
const plugin = createRustModulePlugin(ctx, { name: 'analysis', pluginId: 'text-analysis' });
const ordinaryPlugin: Plugin<RustModuleRevision> = plugin;
const raw: RustModuleRevision = { path: '/plugin.dylib', sha256: 'digest', plugins: [{ id: 'text', factory: 'analysis', config: { enabled: true } }] };
const validated = plugin.Config['~standard'].validate(raw);
if ('value' in validated) await ctx.plugin(ordinaryPlugin, validated.value);
// @ts-expect-error Native plugin configs require a digest.
ctx.plugin(plugin, { path: '/plugin.dylib', plugins: [] });
// @ts-expect-error Plugins do not acquire the host controller's reload authority.
plugin.reload(raw);
import { officialTransaction } from '@cordis-verus/compat-loader/harness';
const result: number = await officialTransaction(ctx, async () => 42);
void result;
// @ts-expect-error Only a host operation callback can form an official transaction.
officialTransaction(ctx, 42);

const stateful: RustModuleRevision = { ...raw, plugins: [{ id: 'counter', factory: 'counter', state: 'migrate' }] };
void stateful;
const migration = beginRustModuleMigration(ctx, ctx.fiber);
migration.rollback(); migration.commit(); migration.release();
// @ts-expect-error Arbitrary transfer policies are not supported.
const invalidState: RustModuleRevision = { ...raw, plugins: [{ id: 'counter', factory: 'counter', state: 'copy-memory' }] };
void invalidState;
