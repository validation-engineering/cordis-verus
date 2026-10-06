import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { Context, FiberState, domainMutation } from '../../packages/compat-cordis/index.js';
import { loadRustModule } from '../../packages/compat-loader/rust-module.js';

const extension = process.platform === 'darwin' ? 'dylib' : process.platform === 'win32' ? 'dll' : 'so';
const artifact = version => {
  const path = fileURLToPath(new URL(`../../target/node-compat/dynamic-fixture-${version}.${extension}`, import.meta.url));
  return { path, sha256: createHash('sha256').update(readFileSync(path)).digest('hex') };
};
const options = (version = 'v1', config = {}) => ({ ...artifact(version), plugins: [{ id: 'manager', factory: 'native-children', config }] });
const turn = () => new Promise(resolve => setImmediate(resolve));
const message = error => [error?.message, ...(error?.errors ?? []).map(message), error?.cause ? message(error.cause) : ''].join(' | ');
async function waitFor(predicate, label) {
  const deadline = Date.now() + 8000;
  while (!await predicate()) { if (Date.now() > deadline) throw new Error(`Timed out: ${label}`); await turn(); }
}
const phases = (trace, phase) => trace.filter(item => item.phase === phase);
function zeroResources(ctx) {
  assert.equal(ctx.fiber._domain.rust.nativeChildren.size, 0);
  for (const module of ctx.fiber._domain.rust.command({ op: 'module_info' }).modules) {
    for (const [kind, count] of Object.entries(module.resources)) assert.equal(count, 0, `${module.buildId}: ${kind}`);
  }
}
function provider(trace, revision = 'old', hook) {
  return { async record(event) { trace.push({ ...event, provider: revision }); await hook?.(event); return null; } };
}
async function environment(profile, config = {}, hook) {
  const ctx = new Context({ profile }), trace = [];
  ctx.provide('jsHost', provider(trace, 'old', hook));
  try {
    const controller = await loadRustModule(ctx, options('v1', config));
    return { ctx, trace, controller, manager: ctx.nativeChildren };
  } catch (error) { await ctx.dispose(); throw error; }
}

export function registerChildrenTests(profile) {
  test(`native publication creates a real provider child and can be withdrawn and republished (${profile})`, async () => {
    const { ctx, controller, manager, trace } = await environment(profile);
    try {
      await manager.publish({ key: 'first', service: 'runtimeValue', label: 'first' });
      await manager.ready({ key: 'first' });
      const first = await manager.status({ key: 'first' });
      assert.equal(first.initialized, true); assert.equal(first.removed, false);
      const node = ctx.snapshot().plugins.find(node => node.id === first.id);
      assert.equal(node.parent, controller.snapshot().entries[0].fiberId);
      const old = ctx.runtimeValue;
      assert.deepEqual(await old.read(7), { version: 'v1', label: 'first', service: 'runtimeValue', value: 7 });
      await manager.dispose({ key: 'first' }); await manager.join({ key: 'first' });
      assert.equal((await manager.status({ key: 'first' })).removed, true);
      assert.equal(ctx.snapshot().plugins.some(node => node.id === first.id), false);
      assert.throws(() => old.read(8), /STALE|no longer admitted/);
      await manager.publish({ key: 'second', service: 'runtimeValue', label: 'second' });
      await manager.ready({ key: 'second' });
      assert.notEqual((await manager.status({ key: 'second' })).id, first.id);
      assert.equal((await ctx.runtimeValue.read(9)).label, 'second');
      await controller.dispose(); zeroResources(ctx);
      assert.equal(phases(trace, 'child-cleanup').length, 2);
    } finally { await ctx.dispose(); }
  });

  test(`native named factories and recursively published factories keep real ownership edges (${profile})`, async () => {
    const { ctx, controller, manager } = await environment(profile, { initial: { key: 'outer', service: 'outerValue', nested: { service: 'innerValue', label: 'inner' } } });
    try {
      await manager.ready({ key: 'outer' }); await ctx.settle();
      await manager.mount({ key: 'named', factory: 'native-child-leaf', config: { label: 'named' } });
      await manager.ready({ key: 'named' });
      assert.equal((await ctx.nativeNamedChild.read('n')).label, 'named');
      assert.equal((await ctx.innerValue.read('i')).label, 'inner');
      const outer = await manager.status({ key: 'outer' });
      assert(ctx.snapshot().plugins.some(node => node.parent === outer.id));
      await manager.dispose({ key: 'outer' }); await manager.join({ key: 'outer' });
      assert.equal(ctx.snapshot().plugins.some(node => node.parent === outer.id), false);
      await controller.dispose(); zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });

  test(`native setup cannot wait for its own anchor-dependent publication (${profile})`, { timeout: 15000 }, async () => {
    const ctx = new Context({ profile }), trace = [];
    ctx.provide('jsHost', provider(trace));
    try {
      await assert.rejects(loadRustModule(ctx, options('v1', { initial: { key: 'initial' }, joinSetup: true })), error => /ReentrantServiceJoin/.test(message(error)));
      await ctx.settle().catch(() => {});
      zeroResources(ctx);
      assert.equal(ctx.snapshot().plugins.length, 1);
      assert.equal(phases(trace, 'child-setup').length, 0);
    } finally { await ctx.dispose(); }
  });

  test(`native creation rejects missing factories without retaining definitions (${profile})`, async () => {
    const { ctx, controller, manager } = await environment(profile);
    try {
      await assert.rejects(manager.mount({ factory: 'not-in-this-image' }), /Unknown.*Factory/);
      await manager.publish({ key: 'valid', service: 'validatedValue' }); await manager.ready({ key: 'valid' });
      await controller.dispose(); zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });

  test(`native child join waits for actual consumer cleanup and preserves its committed service (${profile})`, { timeout: 15000 }, async () => {
    const { ctx, controller, manager } = await environment(profile, { initial: { key: 'initial', service: 'heldValue' } });
    const entered = Promise.withResolvers(), release = Promise.withResolvers();
    let joined;
    try {
      await manager.ready({ key: 'initial' });
      const observations = [];
      const consumer = await ctx.plugin({ inject: ['heldValue'], apply(c) {
        return async () => { entered.resolve(); await release.promise; observations.push(await c.heldValue.read('cleanup')); };
      } });
      await manager.dispose({ key: 'initial' });
      joined = manager.join({ key: 'initial' }); joined.catch(() => {});
      await entered.promise; let finished = false; joined.then(() => { finished = true; }); await turn();
      assert.equal(finished, false);
      assert.equal((await manager.status({ key: 'initial' })).removed, false);
      release.resolve(); await joined;
      assert.equal(observations[0].value, 'cleanup'); assert.equal(observations[0].version, 'v1');
      assert.equal(consumer.state, FiberState.PENDING);
      await controller.dispose(); zeroResources(ctx);
    } finally { release.resolve(); await Promise.allSettled([joined]); await ctx.dispose(); }
  });

  test(`native child refuses a join held alive by the calling consumer (${profile})`, { timeout: 15000 }, async () => {
    const { ctx, controller, manager } = await environment(profile, { initial: { key: 'initial', service: 'heldValue' } });
    try {
      await manager.ready({ key: 'initial' });
      const consumer = await ctx.plugin({ inject: ['heldValue', 'nativeChildren'], async apply(c) {
        await assert.rejects(c.nativeChildren.join({ key: 'initial' }), /ReentrantServiceJoin/);
      } });
      assert.equal(consumer.state, FiberState.ACTIVE);
      await controller.dispose(); zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });

  test(`native child cleanup failure retains the node and retries the actual cleanup (${profile})`, { timeout: 15000 }, async () => {
    const { ctx, controller, manager, trace } = await environment(profile, { initial: { key: 'initial', service: 'retryValue', failCleanupOnce: true } });
    try {
      await manager.ready({ key: 'initial' });
      const { id } = await manager.status({ key: 'initial' });
      await manager.dispose({ key: 'initial' });
      await assert.rejects(manager.join({ key: 'initial' }), /ChildCleanupFailed|child-cleanup|CleanupFailed/);
      const failed = await manager.status({ key: 'initial' });
      assert.equal(failed.removed, false); assert.equal(failed.cleanupFailed, true);
      assert(ctx.snapshot().plugins.some(node => node.id === id && node.cleanupFailed));
      await ctx.settle().catch(() => {});
      await manager.retry_cleanup({ key: 'initial' });
      await manager.join({ key: 'initial' }).catch(error => assert.match(message(error), /CleanupFailed|child-cleanup/));
      assert.equal((await manager.status({ key: 'initial' })).removed, true);
      assert.deepEqual(phases(trace, 'child-cleanup').map(event => event.attempt), [1, 2]);
      await controller.dispose(); zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });

  test(`native setup failure remains a child failure with explicit retirement (${profile})`, async () => {
    const { ctx, controller, manager } = await environment(profile);
    try {
      await manager.publish({ key: 'failed', service: 'failedValue', failSetup: true });
      await assert.rejects(manager.ready({ key: 'failed' }), /ChildSetupFailed|SetupFailed/);
      await ctx.settle().catch(() => {});
      assert.equal(controller.snapshot().entries[0].state, FiberState.ACTIVE);
      await manager.dispose({ key: 'failed' });
      await manager.join({ key: 'failed' }).catch(error => assert.match(message(error), /SetupFailed/));
      assert.equal((await manager.status({ key: 'failed' })).removed, true);
      await controller.dispose(); zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });

  test(`native dropped publication awaiters still create owned nodes which teardown really removes (${profile})`, async () => {
    const { ctx, controller, manager, trace } = await environment(profile);
    try {
      await manager.dropped_publish({ service: 'droppedValue', label: 'dropped' }); await ctx.settle();
      assert.equal((await ctx.droppedValue.read(1)).label, 'dropped');
      await controller.dispose(); zeroResources(ctx);
      assert.equal(phases(trace, 'child-cleanup').filter(event => event.label === 'dropped').length, 1);
    } finally { await ctx.dispose(); }
  });

  test(`native publication allocated before an observer throws still joins reserved cleanup (${profile})`, { timeout: 15000 }, async () => {
    const { ctx, controller, manager } = await environment(profile);
    const entered = Promise.withResolvers(), release = Promise.withResolvers();
    let child, joined;
    const remove = ctx.on('internal/plugin', fiber => {
      if (!fiber._nativeChild) return;
      child = fiber;
      fiber.effect(() => async () => { entered.resolve(); await release.promise; });
      throw new Error('native child observer failed after allocation');
    });
    try {
      await manager.publish({ key: 'observer', service: 'observerValue' });
      await entered.promise;
      const status = await manager.status({ key: 'observer' });
      assert.equal(status.id, child.id); assert.equal(status.removed, false);
      joined = manager.join({ key: 'observer' }); joined.catch(() => {});
      let done = false; joined.then(() => { done = true; }, () => { done = true; }); await turn(); assert.equal(done, false);
      release.resolve(); await assert.rejects(joined, /observer failed after allocation/);
      await ctx.settle().catch(() => {});
      assert.equal((await manager.status({ key: 'observer' })).removed, true);
      await remove(); await controller.dispose(); zeroResources(ctx);
    } finally { release.resolve(); await Promise.allSettled([joined]); await remove(); await ctx.settle().catch(() => {}); await ctx.dispose(); }
  });

  for (const [label, failure, expected] of [
    ['oversized', 'x'.repeat(1024 * 1024), 'PluginErrorTooLarge'],
    ['invalid-Unicode', String.fromCharCode(0xd800), 'PluginErrorInvalidUnicode'],
  ]) {
    test(`native ${label} child-observer failures stay bounded and keep their removal receipt (${profile})`, async () => {
      const { ctx, controller, manager } = await environment(profile);
      const remove = ctx.on('internal/plugin', fiber => { if (fiber._nativeChild) throw new Error(failure); });
      try {
        await manager.publish({ key: 'bounded', service: 'boundedValue' });
        await assert.rejects(manager.join({ key: 'bounded' }), error => message(error).includes(expected));
        await ctx.settle().catch(() => {});
        assert.equal((await manager.status({ key: 'bounded' })).removed, true);
        await remove(); await controller.dispose(); zeroResources(ctx);
      } finally { await remove(); await ctx.settle().catch(() => {}); await ctx.dispose(); }
    });
  }

  test(`native finalization errors cannot erase the graph's one JS Removed acknowledgement (${profile})`, async () => {
    const { ctx, controller, manager } = await environment(profile, { initial: { key: 'initial', service: 'finalValue' } });
    const host = ctx.fiber._domain.rust, original = host.command;
    try {
      await manager.ready({ key: 'initial' });
      const { id } = await manager.status({ key: 'initial' });
      const fiber = ctx.fiber._domain.fibers.get(id);
      // The graph has removed the child. Inject a transport finalization error
      // after the real SDK acknowledgement to exercise JS's one-shot event path.
      host.command = function(command) {
        const result = original.call(this, command);
        if (command.op === 'forget' && command.id === id) {
          this.command = original;
          throw new Error('injected definition-finalization transport failure');
        }
        return result;
      };
      await manager.dispose({ key: 'initial' }); await manager.join({ key: 'initial' });
      await ctx.settle().catch(() => {});
      assert.equal(fiber._removedFlag, true);
      assert.equal(ctx.fiber._domain.fibers.has(id), false);
      assert.equal(ctx.snapshot().plugins.some(node => node.id === id), false);
      assert(ctx.fiber._domain.diagnostics.some(item => item.kind === 'rust-definition-finalization' && item.fiber === id && item.cleanup === 'unconfirmed'));
      await controller.dispose(); zeroResources(ctx);
    } finally { host.command = original; await ctx.dispose(); }
  });

  test(`native publication cannot borrow recovery coordinator admission (${profile})`, async () => {
    const { ctx, controller, manager } = await environment(profile);
    const release = Promise.withResolvers();
    const recovering = domainMutation(ctx, () => release.promise, { recovery: true });
    try {
      await assert.rejects(manager.publish({ key: 'blocked', service: 'blockedValue' }), /CLEANUP_BLOCKED|recovery/i);
      assert.equal(ctx.fiber._domain.rust.nativeChildren.size, 0);
    } finally { release.resolve(); await recovering; }
    try {
      await manager.publish({ key: 'allowed', service: 'allowedValue' }); await manager.ready({ key: 'allowed' });
      await controller.dispose(); zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });

  test(`native child teardown drains an in-flight reverse service before replacing its code (${profile})`, { timeout: 15000 }, async () => {
    const entered = Promise.withResolvers(), release = Promise.withResolvers();
    const { ctx, controller, manager, trace } = await environment(profile, { initial: { key: 'initial', service: 'movingValue' } }, async event => {
      if (event.phase === 'child-read') { entered.resolve(); await release.promise; }
    });
    let call, replacing;
    try {
      await manager.ready({ key: 'initial' });
      const driver = ctx.fiber._domain.driver, old = ctx.movingValue;
      call = old.read('old-call'); call.catch(() => {}); await entered.promise;
      let changed = false;
      replacing = controller.reload(artifact('v2')).then(() => { changed = true; }); replacing.catch(() => {});
      await turn(); assert.equal(changed, false);
      assert.equal(phases(trace, 'children-cleanup').length, 0);
      release.resolve(); await call; await replacing;
      await ctx.nativeChildren.ready({ key: 'initial' });
      assert.equal((await ctx.movingValue.read('new-call')).version, 'v2');
      assert.equal(ctx.fiber._domain.driver, driver);
      assert.throws(() => old.read('stale'), /STALE|no longer admitted/);
      assert.throws(() => manager.publish({ key: 'stale' }), /STALE|no longer admitted/);
      await controller.dispose(); zeroResources(ctx);
    } finally { release.resolve(); await Promise.allSettled([call, replacing]); await ctx.dispose(); }
  });

  test(`native children follow provider restart with the original image and old cleanup receipts (${profile})`, async () => {
    const ctx = new Context({ profile }), trace = [];
    const js = await ctx.plugin((c, revision) => { c.provide('jsHost', provider(trace, revision)); }, 'old');
    let controller;
    try {
      controller = await loadRustModule(ctx, options('v1', { initial: { key: 'initial', service: 'restartValue' } }));
      await ctx.nativeChildren.ready({ key: 'initial' });
      const id = (await ctx.nativeChildren.status({ key: 'initial' })).id;
      ctx.fiber._domain.rust.loadModule(artifact('v2'));
      await js.update('new'); await ctx.settle();
      await ctx.nativeChildren.ready({ key: 'initial' });
      assert.equal((await ctx.restartValue.read(1)).version, 'v1');
      assert.notEqual((await ctx.nativeChildren.status({ key: 'initial' })).id, id);
      assert(phases(trace, 'child-cleanup').some(event => event.provider === 'old' && event.version === 'v1'));
      await controller.dispose(); zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });

  test(`native retained factories create fresh child activations without restarting the parent (${profile})`, { timeout: 15000 }, async () => {
    const { ctx, controller, manager, trace } = await environment(profile);
    const gate = await ctx.plugin(c => { c.provide('leafGate', {}); });
    try {
      await manager.publish({ key: 'independent', service: 'independentValue', extraInject: 'leafGate' });
      await manager.ready({ key: 'independent' });
      const { id } = await manager.status({ key: 'independent' });
      const owner = controller.snapshot().entries[0].fiberId;
      await gate.dispose(); await ctx.settle();
      assert.equal((await manager.status({ key: 'independent' })).initialized, false);
      assert.equal(ctx.snapshot().plugins.find(node => node.id === id).state.toLowerCase(), 'pending');
      assert.equal(controller.snapshot().entries[0].fiberId, owner);
      await ctx.plugin(c => { c.provide('leafGate', {}); });
      await manager.ready({ key: 'independent' });
      assert.equal((await manager.status({ key: 'independent' })).id, id);
      assert.equal(phases(trace, 'child-setup').length, 2);
      assert.equal(phases(trace, 'children-setup').length, 1);
      assert.equal(phases(trace, 'child-cleanup').length, 1);
      await controller.dispose(); zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });

  test(`native child removed by an allocation observer accepts its late mount acknowledgement (${profile})`, async () => {
    const { ctx, controller, manager } = await environment(profile);
    let disposed;
    const remove = ctx.on('internal/plugin', fiber => {
      if (fiber._nativeChild) { disposed = fiber.dispose(); disposed.catch(() => {}); }
    });
    try {
      await manager.publish({ key: 'early', service: 'earlyValue' });
      await disposed; await ctx.settle();
      assert.equal((await manager.status({ key: 'early' })).removed, true);
      await manager.join({ key: 'early' });
      await remove(); await controller.dispose(); zeroResources(ctx);
    } finally { await remove(); await Promise.allSettled([disposed]); await ctx.dispose(); }
  });

  test(`native conflicting publications report failure without replacing the existing service (${profile})`, async () => {
    const { ctx, controller, manager } = await environment(profile, { initial: { key: 'initial', service: 'uniqueValue', label: 'original' } });
    try {
      await manager.ready({ key: 'initial' });
      await manager.publish({ key: 'conflict', service: 'uniqueValue', label: 'conflict' });
      await assert.rejects(manager.ready({ key: 'conflict' }), /registered|Duplicate|conflict/i);
      await ctx.settle().catch(() => {});
      assert.equal((await ctx.uniqueValue.read(1)).label, 'original');
      await manager.dispose({ key: 'conflict' });
      await manager.join({ key: 'conflict' }).catch(error => assert.match(message(error), /registered|Duplicate|conflict/i));
      assert.equal((await manager.status({ key: 'conflict' })).removed, true);
      await controller.dispose(); zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });

  test(`native publications inherit isolation without sharing names across scopes (${profile})`, async () => {
    const ctx = new Context({ profile }), trace = [];
    const left = ['jsHost', 'nativeChildren', 'scopedValue'].reduce((scope, name) => scope.isolate(name), ctx);
    const right = ['jsHost', 'nativeChildren', 'scopedValue'].reduce((scope, name) => scope.isolate(name), ctx);
    left.provide('jsHost', provider(trace, 'left')); right.provide('jsHost', provider(trace, 'right'));
    try {
      const first = await loadRustModule(left, options('v1', { initial: { key: 'initial', service: 'scopedValue', label: 'left' } }));
      const second = await loadRustModule(right, options('v1', { initial: { key: 'initial', service: 'scopedValue', label: 'right' } }));
      await left.nativeChildren.ready({ key: 'initial' }); await right.nativeChildren.ready({ key: 'initial' });
      assert.equal((await left.scopedValue.read(1)).label, 'left');
      assert.equal((await right.scopedValue.read(2)).label, 'right');
      await first.dispose(); assert.equal((await right.scopedValue.read(3)).label, 'right');
      await second.dispose(); zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });
}
