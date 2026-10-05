import { Context } from '../../../packages/compat-cordis/index.js';
import { Loader, ModuleHost, Include, type ConfigTree } from '../../../packages/compat-loader/index.js';
import { Artifact, WorkerDomain } from '../../../packages/compat-loader/worker.js';
const tree: ConfigTree = { entries: [
  { id: 'tools', include: './tools.json', isolate: ['tools'] },
  { id: 'plugin', name: './plugin.mjs', config: { nested: [1, true, null] } },
] };
const context = new Context();
const loader = new Loader(context, { moduleHost: new ModuleHost() });
await loader.apply(tree);
await loader.update('plugin', { config: { enabled: true } });
const entry = loader.resolve('plugin');
const id: string = entry.id;
void id;
await Include.read('./plugins.json');
await loader.dispose();
await context.dispose();
const domain = new WorkerDomain({ entry: 'plugins.json' });
await domain.load('./project');
await domain.call('tools', 'execute', { name: 'search' });
// @ts-expect-error Cross-environment calls have an explicit JSON contract.
await domain.call('tools', 'execute', () => {});
await domain.reload();
await domain.dispose();
const artifact = await Artifact.capture('./project');
const digest: string = artifact.digest;
void digest;
await artifact.dispose();
const preparedPlugin = (_ctx: Context) => {};
new ModuleHost({loadModule: async canonicalURL => ({plugin:preparedPlugin, revision:canonicalURL})});
// @ts-expect-error Revision comparison tokens cannot be mutable objects.
new ModuleHost({loadModule: async () => ({plugin:preparedPlugin, revision:{version:1}})});

import { LoaderTransactions, type OfficialEntryTree } from '../../../packages/compat-loader/harness.js';
declare const officialTree: OfficialEntryTree;
const transactions = new LoaderTransactions(context, officialTree);
const officialId: string = await transactions.create({ name: 'cordis:probe', config: { enabled: true } });
await transactions.update(officialId, { disabled: undefined });
await transactions.remove(officialId);
await transactions.close();
const revision: number = transactions.revision;
void revision;
// @ts-expect-error New official entries require a module name.
transactions.create({ config: {} });
// @ts-expect-error Revision metadata cannot be assigned by callers.
transactions.revision = 3;
