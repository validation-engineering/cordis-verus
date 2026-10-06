import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { Context, FiberState } from '../../packages/compat-cordis/index.js';
import { loadRustModule } from '../../packages/compat-loader/rust-module.js';

const extension = process.platform === 'darwin' ? 'dylib' : process.platform === 'win32' ? 'dll' : 'so';
const artifact = version => {
  const path = fileURLToPath(new URL(`../../target/node-compat/dynamic-fixture-${version}.${extension}`, import.meta.url));
  return { path, sha256: createHash('sha256').update(readFileSync(path)).digest('hex') };
};
const options = (version = 'v1', config = {}) => ({ ...artifact(version),
  plugins: [{ id: 'consumer', factory: 'native-js-consumer', config }] });
const turn = () => new Promise(resolve => setImmediate(resolve));
const zeroResources = ctx => {
  const info = ctx.fiber._domain.rust.command({ op: 'module_info' });
  assert.ok(info.modules.every(module => Object.values(module.resources).every(count => count === 0)), JSON.stringify(info));
};
const invoke = (ctx, method, ...args) => ctx.nativeJs.call({ method, args });

for (const profile of ['cordis', 'harness']) {
  test(`dynamic Rust awaits sync/async JS methods and propagates errors (${profile})`, async () => {
    const ctx = new Context({ profile }), trace = [];
    try {
      ctx.provide('jsHost', { record: event => { trace.push(event); return null; },
        sum: (a, b) => a + b,
        query: async value => { await turn(); return { value, source: 'javascript' }; },
        fail: () => { throw new Error('js-failure'); },
        failAsync: async () => { await turn(); throw new Error('js-async-failure'); },
        invalid: () => ({ value: 1n }),
        invalidUnicode: () => '\ud800',
        invalidKey: () => ({['\ud800']: null}),
        invalidError: () => { throw '\ud800'; },
      });
      const controller = await loadRustModule(ctx, options());
      assert.equal(await invoke(ctx, 'sum', 2, 3), 5);
      assert.deepEqual(await invoke(ctx, 'query', ['nested', 9]), { value: ['nested', 9], source: 'javascript' });
      await assert.rejects(invoke(ctx, 'fail'), /js-failure/);
      await assert.rejects(invoke(ctx, 'failAsync'), /js-async-failure/);
      await assert.rejects(invoke(ctx, 'invalid'), /finite JSON/);
      await assert.rejects(invoke(ctx, 'invalidUnicode'), /InvalidUnicode/);
      await assert.rejects(invoke(ctx, 'invalidKey'), /InvalidUnicode/);
      await assert.rejects(invoke(ctx, 'invalidError'), /PluginErrorInvalidUnicode/);
      await assert.rejects(invoke(ctx, 'absent'), /Unknown JS method/);
      await assert.rejects(ctx.nativeJs.call({ service: 'unlisted', method: 'read', args: [] }), /UndeclaredInjection/);
      assert.equal(await invoke(ctx, 'sum', 7, 8), 15);
      await controller.dispose();
      assert.deepEqual(trace, [{ phase: 'setup', version: 'v1' }, { phase: 'cleanup', version: 'v1' }]);
      zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });

  test(`dynamic Rust dependency restart cleans the committed JS provider and pins native code (${profile})`, async () => {
    const ctx = new Context({ profile }), events = [];
    try {
      const provider = await ctx.plugin((child, config) => {
        child.provide('jsHost', { record: event => { events.push([event.phase, event.version, config.revision]); return null; },
          read: () => config.revision });
        return () => { events.push(['provider-cleanup', config.revision]); };
      }, { revision: 'old' });
      const controller = await loadRustModule(ctx, options());
      const old = ctx.nativeJs, before = controller.snapshot().entries[0];
      ctx.fiber._domain.rust.loadModule(artifact('v2'));
      assert.equal(await invoke(ctx, 'read'), 'old');
      await provider.update({ revision: 'new' }, true);
      await ctx.settle();
      assert.equal(await invoke(ctx, 'read'), 'new');
      assert.equal(controller.snapshot().entries[0].factoryRef, before.factoryRef);
      assert.equal(controller.snapshot().entries[0].fiberId, before.fiberId);
      assert.deepEqual(events.slice(0, 4), [
        ['setup', 'v1', 'old'], ['cleanup', 'v1', 'old'], ['provider-cleanup', 'old'], ['setup', 'v1', 'new'],
      ]);
      assert.throws(() => old.call({ method: 'read', args: [] }), error => error.code === 'STALE_EPISODE');
      await controller.dispose();
      await provider.dispose();
      zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });

  test(`dynamic Rust required JS dependencies wait and respect isolated realms (${profile})`, async () => {
    const ctx = new Context({ profile });
    try {
      const module = ctx.fiber._domain.rust.loadModule(artifact('v1'));
      const plugin = module.factories.get('native-js-consumer');
      const left = ctx.isolate('jsHost').isolate('nativeJs');
      const right = ctx.isolate('jsHost').isolate('nativeJs');
      const pending = await left.plugin(plugin);
      assert.equal(pending.state, FiberState.PENDING);
      assert.equal(left.get('nativeJs'), undefined);
      left.provide('jsHost', { record: () => null, read: () => 'left' });
      right.provide('jsHost', { record: () => null, read: () => 'right' });
      await right.plugin(plugin);
      await ctx.settle();
      assert.equal(pending.state, FiberState.ACTIVE);
      assert.equal(await invoke(left, 'read'), 'left');
      assert.equal(await invoke(right, 'read'), 'right');
      assert.equal(ctx.get('nativeJs'), undefined);
      await ctx.dispose();
      zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });

  test(`native replacement drains an admitted JS Promise before cleanup (${profile})`, async () => {
    const ctx = new Context({ profile }), entered = Promise.withResolvers(), gate = Promise.withResolvers(), trace = [];
    let closing, call;
    try {
      ctx.provide('jsHost', { record: event => { trace.push(event); return null; },
        query: async () => { entered.resolve(); await gate.promise; trace.push('js-landed'); return 'landed'; } });
      const controller = await loadRustModule(ctx, options());
      call = invoke(ctx, 'query');
      call.catch(() => {});
      await entered.promise;
      let completed = false;
      closing = controller.reload(artifact('v2')).then(() => { completed = true; });
      closing.catch(() => {});
      await turn();
      assert.equal(completed, false);
      assert.deepEqual(trace, [{ phase: 'setup', version: 'v1' }]);
      gate.resolve();
      assert.equal(await call, 'landed');
      await closing;
      assert.deepEqual(trace.slice(1), ['js-landed', { phase: 'cleanup', version: 'v1' }, { phase: 'setup', version: 'v2' }]);
      await controller.dispose();
      zeroResources(ctx);
    } finally { gate.resolve(); await Promise.allSettled([call, closing]); await ctx.dispose(); }
  });

  test(`dropping a Rust reverse-call future still drains its JS work (${profile})`, async () => {
    const ctx = new Context({ profile }), entered = Promise.withResolvers(), gate = Promise.withResolvers();
    let call;
    try {
      ctx.provide('jsHost', { record: () => null,
        query: async () => { entered.resolve(); await gate.promise; return 'joined'; } });
      const controller = await loadRustModule(ctx, options());
      let completed = false;
      call = ctx.nativeJs.dropped({ method: 'query', args: [] }).then(value => { completed = true; return value; });
      call.catch(() => {});
      await entered.promise;
      await turn();
      assert.equal(completed, false);
      gate.resolve();
      await call;
      await controller.dispose();
      zeroResources(ctx);
    } finally { gate.resolve(); await Promise.allSettled([call]); await ctx.dispose(); }
  });

  test(`dynamic reverse results remain scoped to concurrent jobs and consumers (${profile})`, async () => {
    const ctx = new Context({ profile }), entered = [Promise.withResolvers(), Promise.withResolvers()], gates = [Promise.withResolvers(), Promise.withResolvers()];
    let first, second, closing;
    try {
      ctx.provide('jsHost', { record: () => null, query: async index => {
        entered[index].resolve(); await gates[index].promise; return index;
      } });
      const controller = await loadRustModule(ctx, options());
      const a = await ctx.inject(['nativeJs'], child => { first = invoke(child, 'query', 0); });
      const b = await ctx.inject(['nativeJs'], child => { second = invoke(child, 'query', 1); });
      await Promise.all(entered.map(item => item.promise));
      let finishedA = false, finishedB = false;
      second.then(() => { finishedB = true; }, () => {});
      closing = a.dispose().then(() => { finishedA = true; });
      closing.catch(() => {});
      await turn();
      assert.equal(finishedA, false);
      assert.equal(finishedB, false);
      gates[0].resolve();
      assert.equal(await first, 0);
      await closing;
      assert.equal(finishedB, false);
      gates[1].resolve();
      assert.equal(await second, 1);
      await b.dispose();
      await controller.dispose();
      zeroResources(ctx);
    } finally {
      for (const gate of gates) gate.resolve();
      await Promise.allSettled([first, second, closing]);
      await ctx.dispose();
    }
  });

  test(`dynamic partial setup and cleanup retry keep the committed JS service (${profile})`, async () => {
    const ctx = new Context({ profile }), trace = [];
    let controller;
    try {
      ctx.provide('jsHost', { record: event => { trace.push(event); return null; } });
      const module = ctx.fiber._domain.rust.loadModule(artifact('v1'));
      const failed = ctx.plugin(module.factories.get('native-js-consumer'), { fail_setup: true });
      await assert.rejects(Promise.resolve(failed), /SetupFailed|setup/i);
      await failed.dispose();
      assert.deepEqual(trace, [{ phase: 'setup', version: 'v1' }, { phase: 'cleanup', version: 'v1' }]);
      controller = await loadRustModule(ctx, options('v1', { fail_cleanup_once: true }));
      await assert.rejects(controller.dispose(), error => error.code === 'NATIVE_MODULE_CLEANUP_BLOCKED');
      assert.equal(controller.state, 'blocked');
      await controller.retryCleanup();
      await controller.dispose();
      assert.deepEqual(trace.slice(2), [
        { phase: 'setup', version: 'v1' }, { phase: 'cleanup', version: 'v1' }, { phase: 'cleanup', version: 'v1' },
      ]);
      zeroResources(ctx);
    } finally {
      if (controller?.state === 'blocked') await controller.retryCleanup();
      await controller?.dispose();
      await ctx.dispose();
    }
  });

  test(`dynamic reverse callback cannot await its own mutation (${profile})`, async () => {
    const ctx = new Context({ profile });
    let controller, provider;
    try {
      provider = await ctx.plugin(child => {
        child.provide('jsHost', { record: () => null, query: async () => {
          await assert.rejects(ctx.dispose(), error => error.code === 'REENTRANT_MUTATION');
          assert.throws(() => provider.dispose(), error => error.code === 'REENTRANT_MUTATION');
          await assert.rejects(controller.reload(artifact('v2')), error => error.code === 'REENTRANT_MUTATION');
          return 'guarded';
        } });
      });
      controller = await loadRustModule(ctx, options());
      assert.equal(await invoke(ctx, 'query'), 'guarded');
      await controller.dispose();
      await provider.dispose();
      zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });
}

test('dynamic reverse replies at the size/depth boundary finish as releasable jobs', async () => {
  const ctx = new Context();
  try {
    const near = 'a'.repeat(512 * 1024 - 2);
    const nested = depth => Array.from({ length: depth }).reduce(value => [value], null);
    ctx.provide('jsHost', { record: () => null,
      near: () => near, large: () => 'a'.repeat(1024 * 1024),
      nested: depth => nested(depth), error: () => { throw new Error('e'.repeat(1024 * 1024)); },
    });
    const controller = await loadRustModule(ctx, options());
    assert.equal(await invoke(ctx, 'near'), near);
    await assert.rejects(invoke(ctx, 'large'), /TooLarge|limit|size/i);
    assert.deepEqual(await invoke(ctx, 'nested', 64), nested(64));
    await assert.rejects(invoke(ctx, 'nested', 65), /Deep|depth/i);
    await assert.rejects(invoke(ctx, 'nested', 130), /Deep|depth/i);
    await assert.rejects(invoke(ctx, 'error'), /TooLarge|limit|size/i);
    await controller.dispose();
    zeroResources(ctx);
  } finally { await ctx.dispose(); }
});
