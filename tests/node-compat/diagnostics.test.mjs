import test from 'node:test';
import assert from 'node:assert/strict';
import {createRequire} from 'node:module';
import {fileURLToPath} from 'node:url';
import {Context as CordisContext, symbols} from '../../packages/compat-cordis/index.js';
import {Context as HarnessContext} from '../../packages/compat-harness/index.js';

const observedAddon = fileURLToPath(new URL('./fixtures/observed-driver.cjs', import.meta.url));
const observedDriver = createRequire(import.meta.url)(observedAddon);

const node = (ctx, fiber, options) => ctx.snapshot(options).plugins.find(item => item.id === fiber.id);
for (const [profile, Context] of [['cordis',CordisContext],['harness',HarnessContext]]) {
  test(`${profile}: internal lifecycle observation does not build full diagnostic graphs`, async () => {
    observedDriver.takeCommands();
    const ctx = new Context({addon: observedAddon});
    const owner = await ctx.plugin(c => { c.effect(() => () => {}); });
    await owner.restart(); await owner.dispose(); await ctx.settle();
    const internal = observedDriver.takeCommands();
    assert(internal.includes('snapshot_state'));
    assert(!internal.includes('snapshot'));
    const snapshot = ctx.snapshot();
    assert.equal(snapshot.diagnosticsSchema,'cordis.driver/v1');
    assert.deepEqual(observedDriver.takeCommands(),['snapshot']);
    await ctx.dispose();
    assert(!observedDriver.takeCommands().includes('snapshot'));
  });

  test(`${profile}: missing, isolated and rejected dependencies are readable without rechecking`, async () => {
    const ctx = new Context(); let checks = 0, fail = false;
    ctx.provide('checked', {secret: 'SERVICE_PAYLOAD_SENTINEL'}, () => { checks++; if (fail) throw new Error('check unavailable'); return false; });
    const absent = await ctx.inject(['missing'], () => { throw new Error('must not activate'); });
    const isolated = await ctx.isolate('checked', Symbol('private')).inject(['checked'], () => { throw new Error('must not activate'); });
    const rejected = await ctx.inject(['checked'], () => { throw new Error('must not activate'); });
    try {
      assert.equal(ctx.snapshot().diagnosticsSchema, 'cordis.driver/v1');
      assert(node(ctx,absent).blockers.some(b => b.code === 'MissingProvider' && b.port.service === 'missing'));
      assert(node(ctx,isolated).blockers.some(b => b.code === 'RealmMismatch' && b.port.service === 'checked' && b.port.realmLabel === 'private'));
      assert(node(ctx,rejected).blockers.some(b => b.code === 'CheckRejected'));
      const before = ctx.snapshot(), count = checks;
      for (let i = 0; i < 4; i++) assert.deepEqual(ctx.snapshot(), before);
      assert.equal(checks, count);
      assert(!JSON.stringify(before).includes('SERVICE_PAYLOAD_SENTINEL'));
      fail = true; ctx.reflect.notify(['checked']); await ctx.settle();
      const error = node(ctx,rejected).blockers.find(b => b.code === 'CheckError');
      assert.match(error.error, /check unavailable/);
      const failureCount = checks; ctx.snapshot({includeTiming:true}); ctx.snapshot();
      assert.equal(checks, failureCount);
    } finally { await ctx.dispose(); }
  });

  test(`${profile}: pending cleanup identifies the retained consumer, episode and labeled inverse`, async () => {
    const ctx = new Context(), gate = Promise.withResolvers(), entered = Promise.withResolvers();
    let providerCleaned = false;
    const provider = await ctx.plugin(c => { c.provide('resource', {}); return () => { providerCleaned = true; }; });
    const consumer = await ctx.inject(['resource'], c => {
      c.effect(() => async () => { entered.resolve(); await gate.promise; }, 'flush final buffer');
    });
    const disposal = provider.dispose();
    try {
      await entered.promise;
      const providerNode = node(ctx,provider), consumerNode = node(ctx,consumer);
      assert(providerNode.blockers.some(b => b.code === 'CommittedConsumers' && b.consumers.some(c => c.id === consumer.id && c.generation === consumerNode.generation)));
      assert.equal(consumerNode.host.action.stage, 'inverses');
      assert.equal(consumerNode.host.action.ticket.kind, 'cleanup');
      const inverse = consumerNode.host.inverses.find(i => i.parent !== null && i.label === 'flush final buffer');
      assert.equal(inverse.state, 'running'); assert.equal(inverse.attempts, 1);
      assert.equal(inverse.owner, consumer.id); assert.equal(inverse.generation, consumerNode.generation);
      assert.equal(inverse.elapsedMs, undefined);
      const before = ctx.snapshot();
      await new Promise(resolve => setTimeout(resolve, 5));
      assert.deepEqual(ctx.snapshot(),before, 'default observations are stable while waiting');
      const timing = node(ctx,consumer,{includeTiming:true});
      assert(timing.host.action.elapsedMs >= 0);
      assert(timing.host.inverses.find(i => i.id === inverse.id).elapsedMs >= 0);
      assert.equal(providerCleaned,false);
      assert.deepEqual(ctx.snapshot(), before, 'timing observation does not mutate the snapshot');
    } finally { gate.resolve(); await disposal; await ctx.dispose(); }
    assert(providerCleaned);
    assert.equal(ctx.snapshot().plugins.length,0);
  });

  test(`${profile}: nested failed inverse keeps its identity and explicit retry does not repeat successes`, async () => {
    const ctx = new Context(); let broken = true, successes = 0, attempts = 0, dispose;
    const owner = await ctx.plugin(c => {
      dispose = c.effect(() => c.effect(function* () {
        yield () => { successes++; };
        yield () => { attempts++; if (broken) throw new Error('flush must retry'); };
      }, 'inner flush'), 'outer cleanup');
    });
    await assert.rejects(owner.dispose());
    const failed = node(ctx,owner);
    assert(failed.blockers.some(b => b.code === 'CleanupFailed' && b.retryable));
    const inner = failed.host.inverses.find(i => i.label === 'inner flush' && /flush must retry/.test(i.error ?? ''));
    assert(inner); assert.equal(inner.state,'failed'); assert.equal(inner.attempts,1);
    const before = ctx.snapshot();
    // Mutable effect metadata is not consulted by snapshot.
    Object.defineProperty(dispose, symbols.effect, {get() { throw new Error('diagnostics invoked effect getter'); }});
    const external = ctx.snapshot();
    external.plugins.find(p => p.id === owner.id).host.inverses[0].label = 'forged label';
    assert.deepEqual(ctx.snapshot(), before);
    assert.equal(attempts,1); assert.equal(successes,1);
    broken = false;
    await owner.retryCleanup();
    assert.equal(attempts,2); assert.equal(successes,1);
    await ctx.dispose();
  });

  test(`${profile}: raw returned cleanup functions receive stable diagnostic identities`, async () => {
    const ctx = new Context(); let broken = true;
    const owner = await ctx.plugin(() => () => { if (broken) throw new Error('raw inverse failure'); });
    await assert.rejects(owner.dispose());
    const inverse = node(ctx,owner).host.inverses.find(i => i.label === 'plugin cleanup');
    assert.equal(inverse.state,'failed'); assert.equal(inverse.attempts,1);
    assert.match(inverse.error,/raw inverse failure/);
    assert.deepEqual(node(ctx,owner).host.inverses.find(i => i.id === inverse.id), inverse);
    broken = false; await owner.retryCleanup(); await ctx.dispose();
  });

  test(`${profile}: repeated raw callbacks retain the failed registration rather than the successful one`, async () => {
    const ctx = new Context(); let calls = 0;
    const cleanup = () => { if (++calls === 1) throw new Error('last registration failed'); };
    const owner = await ctx.plugin(function* () { yield cleanup; yield cleanup; });
    const registered = node(ctx,owner).host.inverses;
    assert.equal(registered.length,2);
    await assert.rejects(owner.dispose());
    const retained = node(ctx,owner).host.inverses;
    assert.equal(calls,2); assert.equal(retained.length,1);
    assert.equal(retained[0].id,registered[1].id);
    assert.equal(retained[0].state,'failed');
    await owner.retryCleanup(); assert.equal(calls,3);
    await ctx.dispose();
  });

  test(`${profile}: prepared resources retain their origin when admitted into the first episode`, async () => {
    const ctx = new Context(); let prepared;
    const off = ctx.on('internal/plugin', fiber => {
      fiber.ctx.effect(() => () => {}, 'prepared resource');
      prepared = node(ctx,fiber).host.inverses;
    });
    const owner = await ctx.plugin(() => {}); off();
    assert(prepared.length > 0);
    assert(prepared.every(i => i.generation === '0' && i.registeredGeneration === '0'));
    const active = node(ctx,owner);
    assert(active.host.inverses.every(i => i.generation === active.generation && i.registeredGeneration === '0'));
    assert.deepEqual(active.host.inverses.map(i => i.id),prepared.map(i => i.id));
    await ctx.dispose();
  });

  test(`${profile}: old continuations report actual old and current episode identities`, async () => {
    const ctx = new Context(), gate = Promise.withResolvers(); let late, first = true;
    const owner = await ctx.plugin(c => {
      if (!first) return;
      first = false;
      late = gate.promise.then(() => c.effect(() => { throw new Error('must not acquire'); }));
    });
    const previous = node(ctx,owner).generation;
    await owner.restart();
    const current = node(ctx,owner).generation;
    assert.notEqual(current,previous);
    const before = ctx.snapshot();
    gate.resolve();
    await assert.rejects(late, error => {
      assert.equal(error.code,'STALE_EPISODE');
      assert.deepEqual(error.details, {owner:owner.id,requestedGeneration:previous,currentGeneration:current,removed:false,operation:'get:effect'});
      assert(Object.isFrozen(error.details));
      return true;
    });
    assert.deepEqual(ctx.snapshot(),before);
    await ctx.dispose();
  });

  test(`${profile}: manual asynchronous inverse is visible before cleanup admission`, async () => {
    const ctx = new Context(), gate = Promise.withResolvers(); let dispose;
    const owner = await ctx.plugin(c => { dispose = c.effect(() => () => gate.promise,'manual close'); });
    const waiting = dispose();
    try {
      const observed = node(ctx,owner);
      assert.equal(observed.state,'Active');
      assert(observed.host.inverses.some(i => i.state === 'running' && i.label === 'manual close'));
      assert.equal(observed.pendingAction,null);
    } finally { gate.resolve(); await waiting; }
    assert(!node(ctx,owner).host.inverses.some(i => i.label === 'manual close'));
    await ctx.dispose();
  });
}
