import test from 'node:test';
import assert from 'node:assert/strict';
import { setImmediate as nextTurn } from 'node:timers/promises';
import { Context as CordisContext } from '../../packages/compat-cordis/index.js';
import { Context as HarnessContext } from '../../packages/compat-harness/index.js';
import { Loader, ModuleHost } from '../../packages/compat-loader/index.js';

const fixture = name => new URL(`./fixtures/${name}.mjs`, import.meta.url).href;
const tree = label => [{ id: 'entry', name: fixture('tracked'), config: { label } }];
const reentrant = error => error.code === 'REENTRANT_MUTATION';
const closed = error => error.code === 'DOMAIN_CLOSED';
function prepared(plugin, beforePrepare = async () => {}) {
  const host = new ModuleHost({ loadModule: async () => ({ plugin }) });
  const prepare = host.prepare.bind(host);
  host.prepare = async input => { await beforePrepare(input); return prepare(input); };
  return host;
}
function tracked(events) {
  return (ctx, config) => {
    events.push(`setup:${config.label}`);
    ctx.effect(() => () => { events.push(`cleanup:${config.label}`); });
  };
}

for (const [profile, Context] of [['cordis', CordisContext], ['harness', HarnessContext]]) {
  test(`${profile} two Loaders share admission order across preparation and replacement`, async () => {
    const ctx = new Context(), events = [], preparations = [];
    const entered = Promise.withResolvers(), release = Promise.withResolvers();
    const plugin = tracked(events);
    const first = new Loader(ctx, { moduleHost: prepared(plugin, async input => {
      const label = input.tree[0].options.config.label;
      preparations.push(label);
      if (label === 'a1') { entered.resolve(); await release.promise; }
    }) });
    const second = new Loader(ctx.extend({ caller: 'second' }), { moduleHost: prepared(plugin, input => {
      preparations.push(input.tree[0].options.config.label);
    }) });
    const one = first.apply(tree('a1'));
    try {
      await entered.promise;
      const two = second.apply(tree('b1'));
      const three = first.apply(tree('a2'));
      await nextTurn();
      assert.deepEqual(preparations, ['a1']);
      release.resolve();
      await Promise.all([one, two, three]);
      assert.deepEqual(preparations, ['a1', 'b1', 'a2']);
      assert.deepEqual(events, ['setup:a1', 'setup:b1', 'cleanup:a1', 'setup:a2']);
      await first.dispose();
      await second.apply(tree('b2'));
      assert.equal(second.resolve('entry').state, 'active');
      await second.dispose();
    } finally { release.resolve(); await ctx.dispose(); }
  });

  test(`${profile} direct Fiber disposal shares the Loader admission queue`, async () => {
    const ctx = new Context(), events = [];
    const entered = Promise.withResolvers(), release = Promise.withResolvers();
    const plugin = tracked(events);
    const external = await ctx.plugin(plugin, { label: 'external' });
    const first = new Loader(ctx, { moduleHost: prepared(plugin, async () => {
      entered.resolve(); await release.promise;
    }) });
    const second = new Loader(ctx, { moduleHost: prepared(plugin) });
    const loading = first.apply(tree('first'));
    try {
      await entered.promise;
      const disposal = external.dispose();
      const queued = second.apply(tree('second'));
      await nextTurn();
      assert.deepEqual(events, ['setup:external']);
      assert.notEqual(external.uid, null);
      release.resolve();
      await Promise.all([loading, disposal, queued]);
      assert.deepEqual(events, ['setup:external', 'setup:first', 'cleanup:external', 'setup:second']);
      await first.dispose();
      await second.dispose();
    } finally { release.resolve(); await ctx.dispose(); }
  });

  test(`${profile} a queued Loader close cannot be joined from the action ahead of it`, async () => {
    const ctx = new Context(), events = [];
    const entered = Promise.withResolvers(), release = Promise.withResolvers();
    const second = new Loader(ctx, { moduleHost: prepared(tracked(events)) });
    await second.apply(tree('second'));
    const first = new Loader(ctx, { moduleHost: prepared(async () => {
      await assert.rejects(second.dispose(), reentrant);
      events.push('reentrant join rejected');
    }, async () => { entered.resolve(); await release.promise; }) });
    const loading = first.apply(tree('first'));
    try {
      await entered.promise;
      const closing = second.dispose();
      assert.equal(second.dispose(), closing);
      release.resolve();
      await Promise.all([loading, closing]);
      assert.deepEqual(events, ['setup:second', 'reentrant join rejected', 'cleanup:second']);
      await first.dispose();
    } finally { release.resolve(); await ctx.dispose(); }
  });

  test(`${profile} another Loader cannot be mutated or accidentally closed from active setup`, async () => {
    const ctx = new Context(), events = [];
    const second = new Loader(ctx, { moduleHost: prepared(tracked(events)) });
    const first = new Loader(ctx, { moduleHost: prepared(async child => {
      await assert.rejects(second.apply(tree('forbidden')), reentrant);
      await assert.rejects(second.dispose(), reentrant);
      await child.plugin(nested => { nested.effect(() => () => events.push('child cleanup')); });
    }) });
    try {
      await first.apply(tree('first'));
      assert.deepEqual(events, []);
      await second.apply(tree('allowed'));
      assert.equal(second.resolve('entry').state, 'active');
      await first.dispose();
      assert.deepEqual(events, ['setup:allowed', 'child cleanup']);
      await second.dispose();
    } finally { await ctx.dispose(); }
  });

  test(`${profile} module preparation cannot recursively await another Loader transaction`, async () => {
    const ctx = new Context(), events = [];
    const second = new Loader(ctx, { moduleHost: prepared(tracked(events)) });
    const first = new Loader(ctx, { moduleHost: prepared(tracked(events), async () => {
      await assert.rejects(second.apply(tree('forbidden')), reentrant);
      await assert.rejects(second.dispose(), reentrant);
    }) });
    try {
      await first.apply(tree('first'));
      await second.apply(tree('second'));
      assert.deepEqual(events, ['setup:first', 'setup:second']);
      await first.dispose();
      await second.dispose();
    } finally { await ctx.dispose(); }
  });

  test(`${profile} cleanup can drain while another Loader's global mutation is rejected`, async () => {
    const ctx = new Context(), events = [];
    const second = new Loader(ctx, { moduleHost: prepared(tracked(events)) });
    const first = new Loader(ctx, { moduleHost: prepared(child => {
      child.effect(() => async () => {
        await assert.rejects(second.apply(tree('forbidden')), reentrant);
        await assert.rejects(second.dispose(), reentrant);
        events.push('cleanup checked');
      });
    }) });
    try {
      await first.apply(tree('first'));
      await first.dispose();
      await second.apply(tree('second'));
      assert.deepEqual(events, ['cleanup checked', 'setup:second']);
      await second.dispose();
    } finally { await ctx.dispose(); }
  });

  test(`${profile} domain shutdown waits for admitted preparation and rejects later Loader work`, async () => {
    const ctx = new Context(), events = [];
    const entered = Promise.withResolvers(), release = Promise.withResolvers();
    const first = new Loader(ctx, { moduleHost: prepared(tracked(events), async () => {
      entered.resolve(); await release.promise;
    }) });
    const second = new Loader(ctx, { moduleHost: prepared(tracked(events)) });
    const loading = first.apply(tree('admitted'));
    try {
      await entered.promise;
      const shutdown = ctx.dispose();
      await assert.rejects(second.apply(tree('late')), closed);
      await assert.rejects(first.reload(), closed);
      release.resolve();
      await loading;
      await shutdown;
      assert.deepEqual(events, ['setup:admitted', 'cleanup:admitted']);
      assert.equal(ctx.snapshot().plugins.length, 0);
    } finally { release.resolve(); await ctx.dispose(); }
  });

  test(`${profile} failed cleanup blocks a different Loader until explicit recovery`, async () => {
    const ctx = new Context(), audit = [], events = [];
    ctx.provide('audit', audit);
    const first = new Loader(ctx);
    const second = new Loader(ctx, { moduleHost: prepared(tracked(events)) });
    const providers = (value, extra = {}) => [{ id: 'provider', name: fixture('provider'), config: { value, ...extra } }];
    try {
      await first.apply(providers('old'));
      const candidate = first.apply(providers('candidate', { fail: true, cleanupFailure: true }));
      const queued = second.apply(tree('must-not-start'));
      await assert.rejects(candidate, error => error.code === 'CLEANUP_BLOCKED');
      await assert.rejects(queued, error => error.code === 'CLEANUP_BLOCKED');
      assert.deepEqual(events, []);
      const failed = [...ctx.registry.values()].flatMap(runtime => [...runtime.fibers]).find(fiber => fiber.config?.cleanupFailure);
      failed.config.cleanupFailure = false;
      await first.retryCleanup();
      await second.apply(tree('recovered'));
      assert.deepEqual(events, ['setup:recovered']);
      await first.dispose();
      await second.dispose();
    } finally {
      for (const runtime of ctx.registry.values()) for (const fiber of runtime.fibers) if (fiber.config?.cleanupFailure) fiber.config.cleanupFailure = false;
      if (first.state === 'blocked') await first.retryCleanup();
      await ctx.dispose();
    }
  });
}
