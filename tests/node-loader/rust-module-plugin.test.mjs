import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { Context, domainMutation, resolveConfig } from '../../packages/compat-cordis/index.js';
import { createRustModulePlugin } from '@cordis-verus/compat-loader/rust-module-plugin';

const extension = process.platform === 'darwin' ? 'dylib' : process.platform === 'win32' ? 'dll' : 'so';
const revision = (version, config = {}) => {
  const path = fileURLToPath(new URL(`../../target/node-compat/dynamic-fixture-${version}.${extension}`, import.meta.url));
  return { path, sha256: createHash('sha256').update(readFileSync(path)).digest('hex'),
    plugins: [{ id: 'text', factory: 'native-text-analysis', config }] };
};
const resources = ctx => ctx.fiber._domain.rust.command({ op: 'module_info' }).modules;
const analyze = (ctx, version) => assert.equal(ctx.nativeText.analyze({ text: 'live' }).version, version);

for (const profile of ['cordis', 'harness']) {
  test(`normal native module plugin can mount inside managed setup without host authority (${profile})`, async () => {
    const ctx = new Context({ profile });
    try {
      const plugin = createRustModulePlugin(ctx), driver = ctx.fiber._domain.driver;
      const outer = ctx.plugin(async child => { await child.plugin(plugin, revision('v1')); });
      await outer;
      analyze(ctx, 'v1');
      assert.equal(ctx.fiber._domain.driver, driver);
      await outer.dispose();
      assert.ok(resources(ctx).every(module => Object.values(module.resources).every(count => count === 0)));
    } finally { await ctx.dispose(); }
  });

  test(`native entry preflight rejects invalid bytes before retiring old children (${profile})`, async () => {
    const ctx = new Context({ profile });
    try {
      const plugin = createRustModulePlugin(ctx), fiber = await ctx.plugin(plugin, revision('v1'));
      const old = ctx.nativeText, generation = fiber._generation;
      await assert.rejects(domainMutation(ctx, steps => steps.update(fiber, { ...revision('v2'), sha256: '0'.repeat(64) }, true)), /mismatch|digest|sha/i);
      assert.equal(fiber._generation, generation);
      assert.equal(old.analyze({ text: 'still live' }).version, 'v1');
      await domainMutation(ctx, steps => steps.update(fiber, revision('v2'), true));
      analyze(ctx, 'v2');
      assert.throws(() => old.analyze({ text: 'retired' }), error => error.code === 'STALE_EPISODE');
      await domainMutation(ctx, steps => steps.update(fiber, { ...revision('v2'), plugins: [] }, true));
      assert.equal(ctx.get('nativeText'), undefined);
      await fiber.dispose();
      assert.ok(resources(ctx).every(module => Object.values(module.resources).every(count => count === 0)));
    } finally { await ctx.dispose(); }
  });
}

test('native schema captures immutable JSON and apply never reloads or accepts a clone', async () => {
  const ctx = new Context(), other = new Context();
  try {
    const plugin = createRustModulePlugin(ctx), raw = revision('v1', { setup_pending: true });
    const prepared = resolveConfig(plugin, raw);
    raw.plugins[0].config.setup_pending = false;
    assert.equal(prepared.plugins[0].config.setup_pending, true);
    assert.ok(Object.isFrozen(prepared.plugins[0].config));
    await assert.rejects(plugin.apply(ctx, structuredClone(prepared)), error => error.code === 'NATIVE_MODULE_UNPREPARED');
    await assert.rejects(plugin.apply(other, prepared), error => error.code === 'FOREIGN_DOMAIN');
    const host = ctx.fiber._domain.rust, load = host.loadModule;
    host.loadModule = () => { throw new Error('apply must consume the prepared image'); };
    try { await plugin.apply(ctx, prepared); analyze(ctx, 'v1'); }
    finally { host.loadModule = load; }
  } finally { await ctx.dispose(); await other.dispose(); }
});

test('native schema rejects executable configs, absent factories and foreign module identity', async () => {
  const ctx = new Context();
  try {
    const plugin = createRustModulePlugin(ctx);
    let reads = 0;
    const raw = revision('v1');
    Object.defineProperty(raw, 'plugins', { enumerable: true, get() { reads++; return []; } });
    assert.ok(plugin.Config['~standard'].validate(raw).issues);
    assert.equal(reads, 0);
    const missing = revision('v1'); missing.plugins[0].factory = 'absent';
    assert.throws(() => resolveConfig(plugin, missing), /does not export/);
    assert.throws(() => resolveConfig(createRustModulePlugin(ctx, { pluginId: 'foreign' }), revision('v1')), /identity/);
    assert.throws(() => resolveConfig(plugin, { ...revision('v1'), plugins: [{ id: 'a', factory: 'native-text-analysis' }, { id: 'a', factory: 'native-text-analysis' }] }), /unique ids/);
  } finally { await ctx.dispose(); }
});

test('ordinary native plugin reports setup failure and can be restored by its host', async () => {
  const ctx = new Context({ profile: 'harness' });
  try {
    const plugin = createRustModulePlugin(ctx), fiber = await ctx.plugin(plugin, revision('v1'));
    await assert.rejects(domainMutation(ctx, steps => steps.update(fiber, revision('fail'), true)), /CandidateSetupFailed|setup/i);
    await domainMutation(ctx, steps => steps.update(fiber, revision('v1'), true));
    analyze(ctx, 'v1');
    await fiber.dispose();
    assert.ok(resources(ctx).every(module => Object.values(module.resources).every(count => count === 0)));
  } finally { await ctx.dispose(); }
});

test('native plugin schema and prepared values expire with their owner', async () => {
  const ctx = new Context();
  const plugin = createRustModulePlugin(ctx), prepared = resolveConfig(plugin, revision('v1'));
  await ctx.dispose();
  assert.throws(() => resolveConfig(plugin, revision('v1')), /removed or previous/);
  await assert.rejects(plugin.apply(ctx, prepared), error => error.code === 'NATIVE_MODULE_OWNER_REMOVED');
});
