import test from 'node:test';
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { fileURLToPath } from 'node:url';
import { Context as CordisContext, FiberState } from '../../packages/compat-cordis/index.js';
import { Context as HarnessContext } from '../../packages/compat-harness/index.js';

const require = createRequire(import.meta.url);
const coreAddon = fileURLToPath(new URL('../../packages/compat-cordis/native/cordis.node', import.meta.url));
const rustAddon = fileURLToPath(new URL('../../target/node-compat/interop-fixture.node', import.meta.url));

// Count real native commands, without replacing the graph or relying on timings.
// Fault injection wraps that same boundary to check that readiness cannot conceal
// a native failure after a previously successful quiescent scan.
function instrument(addon = coreAddon) {
  const { NativeDriver } = require(addon);
  const prototype = NativeDriver.prototype;
  const original = prototype.command;
  const calls = [];
  let intercept;
  prototype.command = function (encoded) {
    const command = JSON.parse(encoded);
    calls.push(command);
    const run = () => original.call(this, encoded);
    return intercept ? intercept(command, run) : run();
  };
  return {
    calls,
    count: op => calls.filter(command => command.op === op).length,
    reset: () => { calls.length = 0; },
    intercept: callback => { intercept = callback; },
    restore: () => { prototype.command = original; },
  };
}

async function assertQuiet(ctx, fiber, monitor) {
  await ctx.settle();
  monitor.reset();
  for (let i = 0; i < 8; i++) {
    assert.equal((await fiber.await()).id, fiber.id);
    await ctx.settle();
  }
  assert.equal(monitor.count('drive'), 0, 'settled readiness does not drive the unchanged graph');
  assert.equal(monitor.count('snapshot'), 0, 'settled readiness does not rescan the unchanged graph');
}

for (const [profile, Context] of [['cordis', CordisContext], ['harness', HarnessContext]]) {
  test(`${profile} repeated readiness of active and blocked fibers avoids native graph scans`, async () => {
    const monitor = instrument(), ctx = new Context();
    try {
      const active = await ctx.plugin(() => {});
      const blocked = await ctx.inject(['later'], () => {});
      assert.equal(blocked.state, FiberState.PENDING);
      await assertQuiet(ctx, active, monitor);
      await assertQuiet(ctx, blocked, monitor);
      // Successful service reads and explicit snapshots do not invalidate it.
      assert.equal(ctx.get('later'), undefined);
      ctx.snapshot();
      monitor.reset();
      await active.await();
      assert.equal(monitor.count('drive'), 0);
    } finally { await ctx.dispose(); monitor.restore(); }
  });

  test(`${profile} mutation, notification, restart and withdrawal invalidate settled readiness`, async () => {
    const monitor = instrument(), ctx = new Context(), trace = [];
    try {
      let providerContext;
      const provider = await ctx.plugin(child => {
        providerContext = child;
        child.provide('value', { enabled: true, label: 'first' }, function () { return this.enabled; });
      });
      const consumer = await ctx.inject(['value'], child => {
        trace.push(`setup:${child.value.label}`);
        return () => trace.push(`cleanup:${child.value.label}`);
      });
      await assertQuiet(ctx, consumer, monitor);
      providerContext.set('value', { enabled: false, label: 'second' });
      await ctx.settle();
      assert(monitor.count('drive') > 0, 'set invalidates the native pump even without an implicit notification');
      assert.equal(consumer.state, FiberState.ACTIVE);
      await assertQuiet(ctx, consumer, monitor);
      providerContext.reflect.notify(['value']);
      await ctx.settle();
      assert.equal(consumer.state, FiberState.PENDING);
      assert.deepEqual(trace, ['setup:first', 'cleanup:second']);
      await assertQuiet(ctx, consumer, monitor);
      await provider.restart();
      await ctx.settle();
      assert.equal(consumer.state, FiberState.ACTIVE);
      assert.deepEqual(trace, ['setup:first', 'cleanup:second', 'setup:first']);
      await assertQuiet(ctx, consumer, monitor);
      await provider.dispose();
      assert.equal(consumer.state, FiberState.PENDING);
      assert.deepEqual(trace, ['setup:first', 'cleanup:second', 'setup:first', 'cleanup:first']);
      await assertQuiet(ctx, consumer, monitor);
    } finally { await ctx.dispose(); monitor.restore(); }
  });

  test(`${profile} synchronous status observers may mutate and recursively pump the domain`, async () => {
    const monitor = instrument(), ctx = new Context(), trace = [];
    try {
      ctx.provide('checked', { enabled: true }, function () { return this.enabled; });
      const consumer = await ctx.inject(['checked'], () => {
        trace.push('setup');
        return () => trace.push('cleanup');
      });
      await assertQuiet(ctx, consumer, monitor);
      let nested;
      const off = ctx.on('internal/status', fiber => {
        if (fiber.name !== 'trigger' || fiber.state !== FiberState.ACTIVE || nested) return;
        ctx.set('checked', { enabled: false });
        ctx.reflect.notify(['checked']);
        // plugin() pumps synchronously inside the outer snapshot's status hook.
        nested = ctx.plugin({ name: 'nested', apply() { trace.push('nested'); } });
      });
      await ctx.plugin({ name: 'trigger', apply() {} });
      await ctx.settle();
      assert(nested);
      assert.equal(nested.state, FiberState.ACTIVE);
      assert.equal(consumer.state, FiberState.PENDING);
      assert(trace.includes('cleanup'));
      assert(trace.includes('nested'));
      off();
      await assertQuiet(ctx, nested, monitor);
    } finally { await ctx.dispose(); monitor.restore(); }
  });

  test(`${profile} cleanup failure remains visible while quiescent and explicit retry resumes progress`, async () => {
    const monitor = instrument(), ctx = new Context();
    let fail = true, cleanups = 0;
    const fiber = await ctx.plugin(child => {
      child.effect(() => () => { cleanups++; if (fail) throw new Error('inverse unavailable'); });
    });
    try {
      await assertQuiet(ctx, fiber, monitor);
      await assert.rejects(fiber.dispose(), /cleanup failed/i);
      assert(ctx.snapshot().plugins.some(item => item.id === fiber.id && item.cleanupFailed));
      await assert.rejects(fiber.await(), /cleanup failed/i);
      fail = false;
      monitor.reset();
      await fiber.retryCleanup();
      assert(monitor.count('drive') > 0);
      assert.equal(cleanups, 2);
      assert.equal(fiber.state, FiberState.DISPOSED);
      await assertQuiet(ctx, fiber, monitor);
    } finally {
      fail = false;
      if (ctx.snapshot().plugins.some(item => item.id === fiber.id && item.cleanupFailed)) await fiber.retryCleanup();
      await ctx.dispose(); monitor.restore();
    }
  });

  test(`${profile} rejected reads and unknown native commands invalidate prior quiescence`, async () => {
    const monitor = instrument(), ctx = new Context();
    try {
      const fiber = await ctx.plugin(() => {});
      await assertQuiet(ctx, fiber, monitor);
      assert.throws(() => fiber._domain.command({ op: 'unknown-future-command' }), /unknown variant/i);
      await fiber.await();
      assert(monitor.count('drive') > 0, 'a failed command does not preserve a clean cache');
      await assertQuiet(ctx, fiber, monitor);
      let faulted = false;
      monitor.intercept((command, run) => {
        if (command.op === 'snapshot') faulted = true;
        if (faulted) throw new Error('DomainFaulted: simulated native fault');
        return run();
      });
      assert.throws(() => ctx.snapshot(), /DomainFaulted/);
      await assert.rejects(fiber.await(), /DomainFaulted/);
      assert(monitor.count('drive') > 0, 'readiness must revisit the faulted native domain');
      monitor.intercept(undefined);
      await ctx.settle();
    } finally { monitor.intercept(undefined); await ctx.dispose(); monitor.restore(); }
  });

  test(`${profile} incomplete native drive replies cannot establish quiescence`, async () => {
    const monitor = instrument(), ctx = new Context();
    try {
      const fiber = await ctx.plugin(() => {});
      await assertQuiet(ctx, fiber, monitor);
      monitor.intercept((command, run) => {
        const reply = run();
        if (command.op !== 'drive') return reply;
        const parsed = JSON.parse(reply);
        delete parsed.released;
        return JSON.stringify(parsed);
      });
      // check issuance is deliberately a writer even with no pending checks.
      fiber._domain.refreshChecks();
      await fiber.await();
      monitor.reset();
      await fiber.await();
      assert(monitor.count('drive') > 0, 'missing completion evidence must not be cached');
      monitor.intercept(undefined);
      await assertQuiet(ctx, fiber, monitor);
    } finally { monitor.intercept(undefined); await ctx.dispose(); monitor.restore(); }
  });

  test(`${profile} Rust commands invalidate graph readiness and retain episode admission`, async () => {
    const monitor = instrument(rustAddon), ctx = new Context({ addon: rustAddon }), trace = [];
    try {
      ctx.provide('jsSource', {
        read: () => 7,
        query: async value => value,
        record: (...args) => { trace.push(args); return null; },
      });
      const fiber = await ctx.rustPlugin('fixture.counter');
      await assertQuiet(ctx, fiber, monitor);
      const old = ctx.rustCounter;
      assert.equal(old.add(2), 9);
      await fiber.await();
      assert(monitor.count('drive') > 0, 'even a synchronous Rust command conservatively invalidates');
      await assertQuiet(ctx, fiber, monitor);
      assert.deepEqual(await old.delay(1, { done: true }), { done: true });
      await fiber.await();
      assert(monitor.count('drive') > 0, 'native future polling invalidates readiness');
      await fiber.restart();
      assert.throws(() => old.read(), /STALE|no longer admitted/);
      assert.equal(ctx.rustCounter.read(), 7);
      await assertQuiet(ctx, fiber, monitor);
      const current = ctx.rustCounter;
      await fiber.dispose();
      assert.throws(() => current.read(), /STALE|no longer admitted/);
      assert.deepEqual(trace, [['cleanup', 9], ['cleanup', 7]]);
      await assertQuiet(ctx, fiber, monitor);
    } finally { await ctx.dispose(); monitor.restore(); }
  });
}
