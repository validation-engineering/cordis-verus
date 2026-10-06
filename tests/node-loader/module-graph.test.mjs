import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, writeFile, readFile, rm, mkdir } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';
import { WorkerDomain } from '../../packages/compat-loader/worker.js';

async function fixture() {
  const directory = await mkdtemp(join(tmpdir(), 'cordis-graph-'));
  const external = await mkdtemp(join(tmpdir(), 'cordis-graph-trace-'));
  const trace = join(external, 'trace.log');
  const marker = join(external, 'evaluated.log');
  const domain = new WorkerDomain({ timeout: 5000 });
  await writeFile(trace, '');
  await writeFile(join(directory, 'cordis.json'), JSON.stringify([{ id: 'probe', name: './plugin.mjs', config: { trace } }]));
  const source = `
import { Service } from 'cordis';
import { appendFileSync } from 'node:fs';
import { label } from './middle.mjs';
export default class Probe extends Service {
  constructor(ctx, config) {
    super(ctx, 'probe');
    this.value = label;
    appendFileSync(config.trace, 'start:' + label + '\\n');
    ctx.effect(() => () => appendFileSync(config.trace, 'stop:' + label + '\\n'));
  }
  valueOf() { return this.value; }
  async dynamic() { return (await import('./late.mjs')).label; }
}
`;
  await writeFile(join(directory, 'plugin.mjs'), source);
  await writeFile(join(directory, 'middle.mjs'), "import { createRequire } from 'node:module';\nconst require = createRequire(import.meta.url);\nexport const label = require('./middle.cjs').label;\n");
  await writeFile(join(directory, 'middle.cjs'), "module.exports = require('./leaf.cjs');\n");
  await writeFile(join(directory, 'leaf.cjs'), "exports.label = 'old';\n");
  await writeFile(join(directory, 'late.mjs'), "export const label = 'late-old';\n");
  return {
    directory, external, trace, marker, domain, source,
    write: (file, content) => writeFile(join(directory, file), content),
    lines: async () => (await readFile(trace, 'utf8')).trim().split('\n'),
    cleanup: async () => {
      if (domain.state !== 'closed') await domain.abandon();
      await rm(directory, { recursive: true, force: true });
      await rm(external, { recursive: true, force: true });
    },
  };
}

const edge = (graph, from, to, kind) => graph.edges.some(item => item.from === from && item.to === to && item.kind === kind);

test('Worker graph records real ESM, createRequire and CommonJS transitive edges and reload closure', async () => {
  const p = await fixture();
  try {
    const first = await p.domain.load(p.directory);
    const graph = await p.domain.moduleGraph();
    assert.equal(graph.coverage, 'observed');
    assert.deepEqual(graph.roots, ['plugin.mjs']);
    assert.ok(edge(graph, 'plugin.mjs', 'middle.mjs', 'import'));
    assert.ok(edge(graph, 'middle.mjs', 'middle.cjs', 'require'));
    assert.ok(edge(graph, 'middle.cjs', 'leaf.cjs', 'require'));
    assert.ok(edge(graph, 'plugin.mjs', 'host:cordis', 'import'));
    assert.equal(graph.modules.find(item => item.id === 'leaf.cjs').format, 'commonjs');
    assert.equal(await p.domain.call('probe', 'valueOf'), 'old');
    await p.write('leaf.cjs', "exports.label = 'new';\n");
    const plan = await p.domain.planReload();
    assert.equal(plan.strategy, 'worker-restart');
    assert.equal(plan.currentDigest, first.digest);
    assert.deepEqual(plan.changedFiles, [{ path: 'leaf.cjs', change: 'modified', kind: 'module' }]);
    assert.deepEqual(plan.affectedModules, ['leaf.cjs', 'middle.cjs', 'middle.mjs', 'plugin.mjs']);
    assert.equal(await p.domain.call('probe', 'valueOf'), 'old');
    const second = await p.domain.reload();
    assert.deepEqual(second.plan, plan);
    assert.equal(await p.domain.call('probe', 'valueOf'), 'new');
    await p.domain.dispose();
    assert.deepEqual(await p.lines(), ['start:old', 'stop:old', 'start:new', 'stop:new']);
  } finally { await p.cleanup(); }
});

test('dynamic imports join the graph only after execution and then invalidate their importers', async () => {
  const p = await fixture();
  try {
    await p.domain.load(p.directory);
    assert.ok(!(await p.domain.moduleGraph()).modules.some(item => item.path === 'late.mjs'));
    await p.write('late.mjs', "export const label = 'late-new';\n");
    const before = await p.domain.planReload();
    assert.deepEqual(before.affectedModules, []);
    assert.deepEqual(before.unobservedChanges, ['late.mjs']);
    assert.equal(await p.domain.call('probe', 'dynamic'), 'late-old');
    assert.ok(edge(await p.domain.moduleGraph(), 'plugin.mjs', 'late.mjs', 'import'));
    const after = await p.domain.planReload();
    assert.deepEqual(after.affectedModules, ['late.mjs', 'plugin.mjs']);
    await p.domain.reload();
    assert.equal(await p.domain.call('probe', 'dynamic'), 'late-new');
  } finally { await p.cleanup(); }
});

test('planning never evaluates candidate code and reload recaptures edits made after the plan', async () => {
  const p = await fixture();
  try {
    await p.domain.load(p.directory);
    await p.write('leaf.cjs', `require('node:fs').writeFileSync(${JSON.stringify(p.marker)}, 'executed'); exports.label = 'planned';\n`);
    const planned = await p.domain.planReload();
    await assert.rejects(readFile(p.marker), { code: 'ENOENT' });
    assert.deepEqual(await p.lines(), ['start:old']);
    await p.write('leaf.cjs', "exports.label = 'latest';\n");
    const applied = await p.domain.reload();
    assert.notEqual(applied.plan.candidateDigest, planned.candidateDigest);
    assert.equal(await p.domain.call('probe', 'valueOf'), 'latest');
    await assert.rejects(readFile(p.marker), { code: 'ENOENT' });
  } finally { await p.cleanup(); }
});

test('failed candidate restores the complete retained CJS/ESM graph in a fresh Worker', async () => {
  const p = await fixture();
  try {
    const first = await p.domain.load(p.directory);
    await p.write('leaf.cjs', "throw new Error('candidate evaluation failed');\n");
    await assert.rejects(p.domain.reload(), error => error.code === 'RELOAD_FAILED' && error.details.restored);
    assert.equal(p.domain.lastRecovery.digest, first.digest);
    assert.equal(await p.domain.call('probe', 'valueOf'), 'old');
    assert.ok(edge(await p.domain.moduleGraph(), 'middle.cjs', 'leaf.cjs', 'require'));
    assert.deepEqual(await p.lines(), ['start:old', 'stop:old', 'start:old']);
    await p.write('leaf.cjs', "exports.label = 'recovered';\n");
    await p.domain.reload();
    assert.equal(await p.domain.call('probe', 'valueOf'), 'recovered');
  } finally { await p.cleanup(); }
});

test('application native addons are classified and rejected before the current Worker is closed', async () => {
  const p = await fixture();
  try {
    await p.domain.load(p.directory);
    await p.write('untrusted.node', 'not an addon; no dlopen should be attempted');
    const plan = await p.domain.planReload();
    assert.equal(plan.strategy, 'process-restart-required');
    assert.deepEqual(plan.nativeAddons, ['untrusted.node']);
    await assert.rejects(p.domain.reload(), error => error.code === 'PROCESS_RESTART_REQUIRED' && error.details.plan.nativeAddons[0] === 'untrusted.node');
    assert.equal(p.domain.state, 'active');
    assert.equal(await p.domain.call('probe', 'valueOf'), 'old');
    assert.deepEqual(await p.lines(), ['start:old']);
  } finally { await p.cleanup(); }
});

test('resource/metadata and unobserved file changes retain a conservative full artifact restart', async () => {
  const p = await fixture();
  try {
    await p.domain.load(p.directory);
    await p.write('package.json', JSON.stringify({ type: 'module' }));
    await p.write('data.txt', 'resource');
    await mkdir(join(p.directory, 'empty'));
    const plan = await p.domain.planReload();
    assert.equal(plan.strategy, 'worker-restart');
    assert.deepEqual(plan.changedFiles.map(item => [item.path, item.kind]), [['data.txt', 'resource'], ['package.json', 'metadata']]);
    assert.deepEqual(plan.changedDirectories, ['empty']);
    assert.deepEqual(plan.unobservedChanges, ['data.txt', 'package.json']);
    await p.domain.reload();
    assert.equal((await p.domain.planReload()).identical, true);
  } finally { await p.cleanup(); }
});

test('transitive absolute imports outside the captured artifact are rejected and the old graph restored', async () => {
  const p = await fixture();
  try {
    await p.domain.load(p.directory);
    const external = join(p.external, 'outside.mjs');
    await writeFile(external, "export const label = 'outside';\n");
    await p.write('middle.mjs', `export { label } from ${JSON.stringify(pathToFileURL(external).href)};\n`);
    await assert.rejects(p.domain.reload(), error => error.code === 'RELOAD_FAILED' && error.cause?.cause?.code === 'MODULE_OUTSIDE_ARTIFACT');
    assert.equal(await p.domain.call('probe', 'valueOf'), 'old');
  } finally { await p.cleanup(); }
});

test('a materialized package with conditional exports records the actual import and require resolutions', async () => {
  const p = await fixture();
  try {
    const pkg = join(p.directory, 'node_modules', 'labels');
    await mkdir(pkg, { recursive: true });
    await writeFile(join(pkg, 'package.json'), JSON.stringify({ name: 'labels', exports: { import: './import.mjs', require: './require.cjs' } }));
    await writeFile(join(pkg, 'import.mjs'), "export const label = 'esm';\n");
    await writeFile(join(pkg, 'require.cjs'), "exports.label = 'cjs';\n");
    await p.write('middle.mjs', "import { label as esm } from 'labels';\nimport { createRequire } from 'node:module';\nexport const label = esm + ':' + createRequire(import.meta.url)('labels').label;\n");
    await p.domain.load(p.directory);
    assert.equal(await p.domain.call('probe', 'valueOf'), 'esm:cjs');
    const graph = await p.domain.moduleGraph();
    assert.ok(edge(graph, 'middle.mjs', 'node_modules/labels/import.mjs', 'import'));
    assert.ok(edge(graph, 'middle.mjs', 'node_modules/labels/require.cjs', 'require'));
    await writeFile(join(pkg, 'require.cjs'), "exports.label = 'new';\n");
    const plan = await p.domain.planReload();
    assert.deepEqual(plan.affectedModules, ['middle.mjs', 'node_modules/labels/require.cjs', 'plugin.mjs']);
    await p.domain.reload();
    assert.equal(await p.domain.call('probe', 'valueOf'), 'esm:new');
  } finally { await p.cleanup(); }
});

test('graph and planning requests respect shutdown admission and need an active recipe', async () => {
  const p = await fixture();
  try {
    await assert.rejects(p.domain.moduleGraph(), { code: 'DOMAIN_NOT_READY' });
    await assert.rejects(p.domain.planReload(), { code: 'NO_RECIPE' });
    const plan = await p.domain.planReload(p.directory);
    assert.equal(plan.currentDigest, null);
    assert.equal((await readFile(p.trace)).length, 0);
    await p.domain.load(p.directory);
    const close = p.domain.dispose();
    await assert.rejects(p.domain.moduleGraph(), { code: 'DOMAIN_CLOSED' });
    await assert.rejects(p.domain.planReload(), { code: 'DOMAIN_CLOSED' });
    await close;
  } finally { await p.cleanup(); }
});

test('cyclic CommonJS dependencies have a finite complete reverse closure', async () => {
  const p = await fixture();
  try {
    await p.write('leaf.cjs', "exports.label = 'cycle-old'; require('./middle.cjs');\n");
    await p.domain.load(p.directory);
    await p.write('leaf.cjs', "exports.label = 'cycle-new'; require('./middle.cjs');\n");
    const plan = await p.domain.planReload();
    assert.deepEqual(plan.affectedModules, ['leaf.cjs', 'middle.cjs', 'middle.mjs', 'plugin.mjs']);
    const graph = await p.domain.moduleGraph();
    assert.ok(edge(graph, 'leaf.cjs', 'middle.cjs', 'require'));
    assert.deepEqual(graph.edges.find(item => item.from === 'leaf.cjs' && item.to === 'middle.cjs'), { from: 'leaf.cjs', to: 'middle.cjs', specifier: null, source: 'require-cache', kind: 'require' });
    await p.domain.reload();
    assert.equal(await p.domain.call('probe', 'valueOf'), 'cycle-new');
  } finally { await p.cleanup(); }
});

test('removed transitive files are planned and a failed candidate restores their retained bytes', async () => {
  const p = await fixture();
  try {
    await p.domain.load(p.directory);
    await rm(join(p.directory, 'leaf.cjs'));
    const plan = await p.domain.planReload();
    assert.deepEqual(plan.changedFiles, [{ path: 'leaf.cjs', change: 'removed', kind: 'module' }]);
    assert.deepEqual(plan.affectedModules, ['leaf.cjs', 'middle.cjs', 'middle.mjs', 'plugin.mjs']);
    await assert.rejects(p.domain.reload(), { code: 'RELOAD_FAILED' });
    assert.equal(await p.domain.call('probe', 'valueOf'), 'old');
  } finally { await p.cleanup(); }
});
