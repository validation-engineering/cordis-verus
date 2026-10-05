import test from 'node:test';
import assert from 'node:assert/strict';
import { Context, FiberState } from '../../packages/compat-harness/index.js';

test('observer-owned resources drain before a never-started reservation is removed',async()=>{
  const ctx=new Context();const gate=Promise.withResolvers(),entered=Promise.withResolvers();let disposal;
  const trace=[];const plugin={name:'prepared',inject:['missing'],apply:()=>{trace.push('unexpected setup');}};
  ctx.on('internal/plugin',fiber=>{
    if(fiber.runtime?.name!==plugin.name||fiber.uid===null)return;
    fiber.ctx.effect(()=>{trace.push('effect');return async()=>{entered.resolve();await gate.promise;trace.push('inverse');};});
    disposal=fiber.dispose();
  });
  const reserved=ctx.plugin(plugin);await entered.promise;
  assert.equal(ctx.snapshot().plugins.some(node=>node.id===reserved.id),true);
  assert.equal(reserved.state,FiberState.UNLOADING);assert.deepEqual(trace,['effect']);
  gate.resolve();await disposal;assert.deepEqual(trace,['effect','inverse']);
  assert.equal(ctx.snapshot().plugins.some(node=>node.id===reserved.id),false);await ctx.dispose();
});

test('prepared publication becomes visible on activation and is readable throughout cleanup',async()=>{
  const ctx=new Context();const trace=[];const plugin={name:'prepared-provider',inject:['trigger'],apply:c=>{trace.push(c.prepared.answer);}};
  ctx.on('internal/plugin',fiber=>{
    if(fiber.runtime?.name!==plugin.name||fiber.uid===null)return;
    fiber.ctx.effect(()=>()=>trace.push(`cleanup:${fiber.ctx.prepared.answer}`));
    fiber.ctx.provide('prepared',{answer:42});
    fiber.ctx.on('test',()=>trace.push('event'));
  });
  const provider=ctx.plugin(plugin);await provider;assert.equal(ctx.get('prepared'),undefined);
  ctx.provide('trigger',true);await provider;assert.equal(ctx.prepared.answer,42);
  ctx.emit('test');await provider.dispose();assert.deepEqual(trace,[42,'event','cleanup:42']);
  assert.equal(ctx.prepared,undefined);await ctx.dispose();
});

test('cancelled prepared publications retain owner cleanup access and reclaim values',async()=>{
  const ctx=new Context();const trace=[];let disposal;
  const plugin={name:'cancel-before-start',inject:['missing'],apply:()=>{throw new Error('must not start');}};
  ctx.on('internal/plugin',fiber=>{
    if(fiber.runtime?.name!==plugin.name||fiber.uid===null)return;
    fiber.ctx.effect(()=>()=>trace.push(fiber.ctx.prepared));
    fiber.ctx.provide('prepared',42);
    disposal=fiber.dispose();
  });
  ctx.plugin(plugin);await disposal;assert.deepEqual(trace,[42]);assert.equal(ctx.prepared,undefined);await ctx.dispose();
});

test('prepared cleanup failure keeps the reservation and retries remaining inverses',async()=>{
  const ctx=new Context();let failed=true,disposal;const seen=[];
  const plugin={name:'prepared-retry',inject:['missing'],apply:()=>{}};
  ctx.on('internal/plugin',fiber=>{
    if(fiber.runtime?.name!==plugin.name||fiber.uid===null)return;
    fiber.ctx.effect(()=>()=>{if(failed)throw new Error('cleanup retry');seen.push(fiber.ctx.prepared);});
    fiber.ctx.provide('prepared',42);disposal=fiber.dispose();
  });
  const reserved=ctx.plugin(plugin);await assert.rejects(disposal,/cleanup/i);
  assert.equal(ctx.snapshot().plugins.find(node=>node.id===reserved.id).cleanupFailed,true);
  failed=false;await reserved.retryCleanup();assert.deepEqual(seen,[42]);await ctx.dispose();
});

test('owned tasks require an activation instead of silently crossing reservation generation',async()=>{
  const ctx=new Context();let checked=false;
  const off=ctx.on('internal/plugin',fiber=>{
    if(fiber.uid===null)return;
    assert.throws(()=>fiber.ctx.task(()=>{}),/admitted activation/);checked=true;
  });
  const child=ctx.plugin({inject:['missing'],apply:()=>{}});off();assert.equal(checked,true);
  await child.dispose();await ctx.dispose();
});
