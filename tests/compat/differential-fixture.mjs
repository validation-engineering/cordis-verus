import assert from 'node:assert/strict';
import {Context, Service} from 'cordis';
import TimerService from '../../upstream/cordis/packages/timer/src/index.ts';
import {coreFixture} from '../node-compat/fixture.mjs';

const settle = async ctx => { if (ctx.settle) await ctx.settle(); };
const results = {};
results.core = await coreFixture({Context, Service}, settle);

// This imports and executes the upstream Timer source without modifying it.
{
  const ctx = new Context();
  const provider = ctx.plugin(TimerService);
  await provider;
  const trace = [];
  const child = ctx.inject(['timer'], async c => {
    trace.push(typeof c.timeout, typeof c.interval, c.timer instanceof TimerService);
    await c.timeout(0);
    trace.push('timeout');
    const interval = c.interval(1);
    trace.push((await interval.next()).done);
    trace.push((await interval.return('finished')).value);
    c.timeout(() => trace.push('cancelled timer fired'), 50);
    return () => trace.push('consumer inverse');
  });
  await child;
  await child.dispose();
  await ctx.timeout(60);
  await provider.dispose();
  await settle(ctx);
  assert.deepEqual(trace, ['function', 'function', true, 'timeout', false, 'finished', 'consumer inverse']);
  results.upstreamTimer = trace;
}
{
  const ctx = new Context();
  const trace = [];
  ctx.on('event', () => { trace.push(1); ctx.on('event', () => trace.push(3)); });
  ctx.once('event', () => trace.push(2));
  ctx.emit('event');
  ctx.emit('event');
  ctx.on('bail', () => false);
  ctx.on('bail', () => 0);
  ctx.on('bail', () => 42);
  trace.push(ctx.bail('bail'));
  ctx.on('waterfall', next => { trace.push('before'); const value = next(); trace.push('after'); return value + 1; });
  trace.push(ctx.waterfall('waterfall', () => 4));
  results.events = trace;
}
{
  const ctx = new Context();
  const trace = [];
  const parent = ctx.plugin(async c => {
    await c.plugin(() => { trace.push('child'); return () => trace.push('child inverse'); });
    trace.push('parent');
    return () => trace.push('parent inverse');
  });
  trace.push('plugin returned');
  await parent;
  await parent.dispose();
  await settle(ctx);
  results.childAwait = trace;
}
{
  const ctx = new Context();
  const trace = [];
  const left = ctx.isolate('message', Symbol('same'));
  const right = ctx.isolate('message', Symbol('same'));
  left.provide('message', 'left'); right.provide('message', 'right');
  const a = left.inject(['message'], c => { trace.push(c.message); });
  const b = right.inject(['message'], c => { trace.push(c.message); });
  await Promise.all([a, b]);
  trace.push(ctx.get('message') === undefined);
  await a.dispose(); await b.dispose();
  results.realms = trace;
}
{
  const ctx = new Context(), trace = [];
  const definition = ctx.isolate('value');
  definition.provide('value', 'definition');
  class Relay extends Service {
    static inject = ['value'];
    constructor(c) { super(c, 'relay'); }
    read() { return this.ctx.value; }
  }
  const provider = await definition.plugin(Relay);
  const use = definition.isolate('value');
  use.provide('value', 'caller');
  const consumer = await use.inject(['relay'], c => {
    trace.push(c.relay.read());
    return () => trace.push(c.relay.read());
  });
  await consumer.dispose();
  await provider.dispose();
  await settle(ctx);
  assert.deepEqual(trace, ['definition', 'definition']);
  results.shadowRealm = trace;
}
process.stdout.write(JSON.stringify(results) + '\n');
