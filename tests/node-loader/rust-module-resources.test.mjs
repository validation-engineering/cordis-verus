import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { Context } from '../../packages/compat-cordis/index.js';
import { jsonValue } from '../../packages/compat-cordis/rust-plugin.js';
import { loadRustModule } from '../../packages/compat-loader/rust-module.js';

const extension = process.platform === 'darwin' ? 'dylib' : process.platform === 'win32' ? 'dll' : 'so';
const artifact = version => {
  const path = fileURLToPath(new URL(`../../target/node-compat/dynamic-fixture-${version}.${extension}`, import.meta.url));
  return { path, sha256: createHash('sha256').update(readFileSync(path)).digest('hex') };
};
const options = (version = 'v1') => ({ ...artifact(version), plugins: [{ id: 'resources', factory: 'native-resource-consumer' }] });
const turn = () => new Promise(resolve => setImmediate(resolve));
// Do not leave a test waiting for a gate that a failed native operation will
// never reach. Promise.race also observes losers after the gate is reached.
const awaitEntry = (entered, ...operations) => Promise.race([entered, ...operations.map(operation => operation.then(() => {
  throw new Error('Native operation ended before reaching its test gate');
}))]);
const events = (trace, phase) => trace.filter(event => event.phase === phase);
const inventory = ctx => ctx.fiber._domain.rust.command({ op: 'module_info' }).modules;
function zeroResources(ctx) {
  const modules = inventory(ctx);
  assert(modules.length > 0);
  for (const module of modules) for (const [kind, count] of Object.entries(module.resources)) {
    assert.equal(count, 0, `${module.buildId}: ${kind}`);
  }
}
function count(ctx, kind) { return inventory(ctx).reduce((sum, module) => sum + module.resources[kind], 0); }
async function fixture(profile, { gate, record } = {}) {
  const ctx = new Context({ profile }), trace = [];
  ctx.provide('jsHost', {
    record: async event => { trace.push(event); return await record?.(event) ?? null; },
    gate: async event => await gate?.(event) ?? null,
  });
  try {
    const controller = await loadRustModule(ctx, options());
    return { ctx, trace, controller };
  } catch (error) { await ctx.dispose(); throw error; }
}

for (const profile of ['cordis', 'harness']) {
  test(`dynamic streams pull on demand, close at EOF and on for-await break (${profile})`, async () => {
    const { ctx, trace, controller } = await fixture(profile);
    try {
      const stream = ctx.nativeResources.stream({ values: ['世界', null, { n: 2 }] });
      await turn();
      assert.equal(events(trace, 'stream-next').length, 0);
      assert.equal(count(ctx, 'streams'), 1);
      assert.deepEqual(await stream.next(), { done: false, value: { version: 'v1', index: 0, value: '世界' } });
      const rest = [];
      for await (const item of stream) rest.push(item);
      assert.deepEqual(rest, [{ version: 'v1', index: 1, value: null }, { version: 'v1', index: 2, value: { n: 2 } }]);
      await stream.return();
      assert.equal(events(trace, 'stream-close').length, 1);
      for await (const item of ctx.nativeResources.stream({ values: [1, 2, 3] })) { assert.equal(item.value, 1); break; }
      assert.equal(events(trace, 'stream-close').length, 2);
      assert.equal(count(ctx, 'streams'), 0);
      await controller.dispose(); zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });

  test(`dynamic objects retain typed state, enforce methods and release owned versus borrowed references (${profile})`, async () => {
    const { ctx, trace, controller } = await fixture(profile);
    try {
      const object = ctx.nativeResources.object({ start: 3 });
      assert.equal(object.ownership, 'owned');
      assert.deepEqual(await object.call('read'), { version: 'v1', value: 3 });
      assert.deepEqual(await object.call('add', 4), { version: 'v1', value: 7 });
      await assert.rejects(object.call('missing'), /UndeclaredObjectMethod/);
      assert.throws(() => jsonValue(object), /Opaque/);
      assert.equal(count(ctx, 'objects'), 1);
      await object.close(); await object.close();
      await assert.rejects(object.call('read'), /STALE|no longer admitted/);
      assert.equal(events(trace, 'object-close').length, 1);
      const borrowed = ctx.nativeResources.object({ ownership: 'borrowed', start: 9 });
      assert.equal(borrowed.ownership, 'borrowed');
      assert.deepEqual(await borrowed.call('read'), { version: 'v1', value: 9 });
      await borrowed.close();
      assert.equal(events(trace, 'object-close').length, 1);
      assert.equal(count(ctx, 'objects'), 0);
      await controller.dispose(); zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });

  test(`dynamic stream return cancels but joins the actual reverse JS pull (${profile})`, { timeout: 15000 }, async () => {
    const entered = Promise.withResolvers(), release = Promise.withResolvers();
    const { ctx, trace, controller } = await fixture(profile, { gate: async () => { entered.resolve(); await release.promise; } });
    let pull, closing;
    try {
      const stream = ctx.nativeResources.stream({ values: [1], gateNext: true });
      pull = stream.next(); pull.catch(() => {});
      await awaitEntry(entered.promise, pull);
      await assert.rejects(stream.next(), /StreamBusy/);
      let closed = false;
      const returned = stream.return();
      assert.equal(returned, stream.return());
      closing = returned.then(() => { closed = true; }); closing.catch(() => {});
      await turn(); assert.equal(closed, false);
      assert.equal(events(trace, 'stream-close').length, 0);
      assert.equal(count(ctx, 'streams'), 1);
      release.resolve();
      await Promise.allSettled([pull]); await closing;
      assert.equal(events(trace, 'stream-close').length, 1);
      assert.equal(count(ctx, 'streams'), 0);
      await controller.dispose(); zeroResources(ctx);
    } finally { release.resolve(); await Promise.allSettled([pull, closing]); await ctx.dispose(); }
  });

  test(`dynamic object close joins every concurrent call before its destructor (${profile})`, { timeout: 15000 }, async () => {
    const entered = Promise.withResolvers(), releases = [Promise.withResolvers(), Promise.withResolvers()];
    let started = 0;
    const { ctx, trace, controller } = await fixture(profile, { gate: async () => {
      const index = started++;
      if (started === 2) entered.resolve();
      await releases[index].promise;
    } });
    let first, second, closing;
    try {
      const object = ctx.nativeResources.object({ gateCalls: true });
      first = object.call('read'); second = object.call('read');
      first.catch(() => {}); second.catch(() => {});
      await awaitEntry(entered.promise, first, second);
      let closed = false;
      const returned = object.close(); assert.equal(returned, object.close());
      closing = returned.then(() => { closed = true; }); closing.catch(() => {});
      await assert.rejects(object.call('read'), /STALE|no longer admitted/);
      releases[0].resolve(); await Promise.allSettled([first]); await turn();
      assert.equal(closed, false); assert.equal(events(trace, 'object-close').length, 0);
      releases[1].resolve(); await Promise.allSettled([second]); await closing;
      assert.equal(events(trace, 'object-close').length, 1);
      await controller.dispose(); zeroResources(ctx);
    } finally { releases.forEach(item => item.resolve()); await Promise.allSettled([first, second, closing]); await ctx.dispose(); }
  });

  test(`failed native stream and object close keep resources until a successful retry (${profile})`, async () => {
    const { ctx, trace, controller } = await fixture(profile);
    try {
      const stream = ctx.nativeResources.stream({ failCloseOnce: true });
      const object = ctx.nativeResources.object({ failCloseOnce: true });
      await assert.rejects(stream.return(), /close/i);
      await assert.rejects(object.close(), /close/i);
      assert.equal(count(ctx, 'streams'), 1); assert.equal(count(ctx, 'objects'), 1);
      await assert.rejects(stream.next(), /STALE|no longer admitted/);
      await assert.rejects(object.call('read'), /STALE|no longer admitted/);
      await stream.return(); await object.close();
      assert.deepEqual(events(trace, 'stream-close').map(event => event.attempt), [1, 2]);
      assert.deepEqual(events(trace, 'object-close').map(event => event.attempt), [1, 2]);
      await controller.dispose(); zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });

  test(`native code replacement waits for stream and object operations and invalidates old handles (${profile})`, { timeout: 15000 }, async () => {
    const entered = Promise.withResolvers(), release = Promise.withResolvers();
    let started = 0;
    const { ctx, trace, controller } = await fixture(profile, { gate: async () => { if (++started === 2) entered.resolve(); await release.promise; } });
    let pull, call, reloading;
    try {
      const driver = ctx.fiber._domain.driver, pid = process.pid;
      const stream = ctx.nativeResources.stream({ values: [1], gateNext: true });
      const object = ctx.nativeResources.object({ gateCalls: true });
      pull = stream.next(); call = object.call('read');
      pull.catch(() => {}); call.catch(() => {});
      await awaitEntry(entered.promise, pull, call);
      let replaced = false;
      reloading = controller.reload(artifact('v2')).then(() => { replaced = true; }); reloading.catch(() => {});
      await turn(); assert.equal(replaced, false);
      assert.equal(events(trace, 'resource-cleanup').length, 0);
      release.resolve(); await Promise.allSettled([pull, call]); await reloading;
      for (const phase of ['stream-close', 'object-close']) {
        assert.equal(events(trace, phase).length, 1);
        assert(trace.indexOf(events(trace, phase)[0]) < trace.indexOf(events(trace, 'resource-cleanup')[0]));
      }
      assert.equal(events(trace, 'resource-cleanup')[0].version, 'v1');
      await assert.rejects(stream.next(), /STALE|no longer admitted/);
      await assert.rejects(object.call('read'), /STALE|no longer admitted/);
      const fresh = ctx.nativeResources.object();
      assert.equal((await fresh.call('read')).version, 'v2'); await fresh.close();
      assert.equal(ctx.fiber._domain.driver, driver); assert.equal(process.pid, pid);
      await controller.dispose(); zeroResources(ctx);
    } finally { release.resolve(); await Promise.allSettled([pull, call, reloading]); await ctx.dispose(); }
  });

  test(`resource consumers clean the committed JS provider before dependency replacement (${profile})`, async () => {
    const ctx = new Context({ profile }), trace = [];
    try {
      const provider = await ctx.plugin((child, config) => {
        child.provide('jsHost', { record: event => { trace.push({ ...event, provider: config.revision }); return null; }, gate: () => null });
        return () => { trace.push({ phase: 'provider-cleanup', provider: config.revision }); };
      }, { revision: 'old' });
      const controller = await loadRustModule(ctx, options());
      const before = controller.snapshot().entries[0];
      const stream = ctx.nativeResources.stream(), object = ctx.nativeResources.object();
      ctx.fiber._domain.rust.loadModule(artifact('v2'));
      await provider.update({ revision: 'new' }, true); await ctx.settle();
      for (const phase of ['stream-close', 'object-close', 'resource-cleanup']) {
        const matching = events(trace, phase); assert.equal(matching.length, 1); assert.equal(matching[0].provider, 'old');
        assert(trace.indexOf(matching[0]) < trace.indexOf(events(trace, 'provider-cleanup')[0]));
      }
      assert.equal(events(trace, 'provider-cleanup').length, 1);
      assert.deepEqual(events(trace, 'resource-setup').map(event => [event.version, event.provider]), [['v1', 'old'], ['v1', 'new']]);
      assert.equal(controller.snapshot().entries[0].factoryRef, before.factoryRef);
      await assert.rejects(stream.next(), /STALE|no longer admitted/);
      await assert.rejects(object.call('read'), /STALE|no longer admitted/);
      await controller.dispose(); await provider.dispose(); zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });

  test(`individual consumers own native resources and cleanup inverses keep their object authority (${profile})`, async () => {
    const { ctx, trace, controller } = await fixture(profile);
    let first, second, stream;
    try {
      const a = await ctx.inject(['nativeResources'], child => {
        first = child.nativeResources.object({ start: 7, label: 'first' });
        stream = child.nativeResources.stream({ label: 'first' });
        return async () => { trace.push({ phase: 'inverse', value: await first.call('read') }); };
      });
      const b = await ctx.inject(['nativeResources'], child => { second = child.nativeResources.object({ start: 9, label: 'second' }); });
      await a.dispose();
      assert.deepEqual(events(trace, 'inverse').map(event => event.value), [{ version: 'v1', value: 7 }]);
      assert.equal(events(trace, 'object-close').length, 1);
      assert.equal(events(trace, 'stream-close').length, 1);
      await assert.rejects(first.call('read'), /STALE|no longer admitted/);
      await assert.rejects(stream.next(), /STALE|no longer admitted/);
      assert.deepEqual(await second.call('read'), { version: 'v1', value: 9 });
      const foreign = await ctx.inject(['nativeResources'], async () => { await assert.rejects(second.call('read'), /ObjectOwnerMismatch/); });
      await foreign.dispose(); await b.dispose();
      await controller.dispose(); zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });

  test(`reverse JS callbacks cannot await their own native resource close (${profile})`, async () => {
    let stream, object;
    const { ctx, controller } = await fixture(profile, { gate: async event => {
      if (event.phase === 'stream-next') await assert.rejects(stream.return(), /ReentrantStreamClose/);
      else await assert.rejects(object.close(), /ReentrantObjectClose/);
    } });
    try {
      stream = ctx.nativeResources.stream({ values: [1], gateNext: true });
      assert.equal((await stream.next()).value.value, 1);
      await stream.return();
      object = ctx.nativeResources.object({ gateCalls: true });
      assert.equal((await object.call('read')).version, 'v1'); await object.close();
      await controller.dispose(); zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });

  test(`failed resource close blocks native replacement until explicit lifecycle cleanup retry (${profile})`, async () => {
    const { ctx, trace, controller } = await fixture(profile);
    try {
      const object = ctx.nativeResources.object({ failCloseOnce: true });
      await assert.rejects(controller.reload(artifact('v2')), error => error.code === 'NATIVE_MODULE_CLEANUP_BLOCKED');
      assert.equal(controller.state, 'blocked');
      assert.equal(count(ctx, 'objects'), 1);
      assert.equal(events(trace, 'resource-cleanup').length, 0);
      await assert.rejects(object.call('read'), /STALE|no longer admitted/);
      await controller.retryCleanup();
      await controller.reload(artifact('v2'));
      const fresh = ctx.nativeResources.object();
      assert.equal((await fresh.call('read')).version, 'v2');
      await fresh.close(); await controller.dispose(); zeroResources(ctx);
    } finally {
      try {
        if (controller.state === 'blocked') await controller.retryCleanup();
        await controller.dispose();
      } finally { await ctx.dispose(); }
    }
  });

  test(`a failed resource candidate restores original code after retiring old capabilities (${profile})`, async () => {
    const { ctx, controller } = await fixture(profile);
    try {
      const old = ctx.nativeResources.object(), stream = ctx.nativeResources.stream();
      const before = controller.snapshot();
      await assert.rejects(controller.reload(artifact('fail')), error => error.code === 'NATIVE_MODULE_RELOAD_FAILED' && error.details.restored);
      assert.equal(controller.snapshot().entries[0].factoryRef, before.entries[0].factoryRef);
      await assert.rejects(old.call('read'), /STALE|no longer admitted/);
      await assert.rejects(stream.next(), /STALE|no longer admitted/);
      const fresh = ctx.nativeResources.object({ start: 11 });
      assert.deepEqual(await fresh.call('read'), { version: 'v1', value: 11 }); await fresh.close();
      await controller.dispose(); zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });
}
