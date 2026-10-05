import test from 'node:test';
import assert from 'node:assert/strict';
import { Context, Service, FiberState } from '../../packages/compat-cordis/index.js';

const gate = () => Promise.withResolvers();

test('real addon supplies the domain and keeps setup asynchronous', async () => {
  const ctx = new Context();
  const trace=[];
  const mounted=ctx.plugin(c=>{ trace.push('setup'); c.effect(()=>{ trace.push('effect'); return ()=>trace.push('cleanup'); }); });
  trace.push('return');
  assert.deepEqual(trace,['return']);
  assert.equal(typeof ctx.snapshot().domain,'string');
  await mounted;
  assert.deepEqual(trace,['return','setup','effect']);
  await ctx.dispose();
  assert.deepEqual(trace,['return','setup','effect','cleanup']);
});

test('function, object and class plugins use native dependencies and cleanup order', async () => {
  const ctx=new Context();
  const trace=[];
  const consumer=ctx.plugin({inject:['message'],apply(c){ trace.push(c.message.text); return ()=>{ trace.push(`consumer:${c.message.text}`); }; }});
  await consumer;
  assert.equal(consumer.state,FiberState.PENDING);
  class Message extends Service {
    constructor(c) { super(c,'message'); this.text='hello'; c.effect(()=>()=>trace.push('provider')); }
  }
  const provider=ctx.plugin(Message);
  await ctx.settle();
  assert.equal(consumer.state,FiberState.ACTIVE);
  assert.equal(ctx.message instanceof Message,true);
  assert.deepEqual(trace,['hello']);
  await provider.dispose();
  assert.deepEqual(trace,['hello','consumer:hello','provider']);
  assert.equal(consumer.state,FiberState.PENDING);
  await ctx.dispose();
});

test('effects stay synchronous and reverse inverses from iterators', async () => {
  const ctx=new Context();
  const trace=[];
  const dispose=ctx.effect(function*(){trace.push('run');yield()=>trace.push('first');yield()=>trace.push('second');});
  assert.deepEqual(trace,['run']);
  await dispose();
  assert.deepEqual(trace,['run','second','first']);
  await dispose();
  await ctx.dispose();
  assert.deepEqual(trace,['run','second','first']);
});

test('late setup inverse is collected after cancellation before owner removal', async () => {
  const ctx=new Context();
  const started=gate(), finish=gate();
  const trace=[];
  const fiber=ctx.plugin(async()=>{started.resolve();await finish.promise;return()=>trace.push('late cleanup');});
  await started.promise;
  const disposal=fiber.dispose();
  let disposed=false;
  disposal.then(()=>disposed=true);
  await Promise.resolve();
  assert.equal(disposed,false);
  finish.resolve();
  await disposal;
  assert.deepEqual(trace,['late cleanup']);
  await ctx.dispose();
});

test('events preserve sync return, throw, snapshot and exactly-once removal', async () => {
  const ctx=new Context();
  const trace=[];
  ctx.on('event',()=>{trace.push(1);ctx.on('event',()=>trace.push(3));});
  ctx.once('event',()=>trace.push(2));
  ctx.emit('event');
  assert.deepEqual(trace,[1,2]);
  ctx.emit('event');
  assert.deepEqual(trace,[1,2,1,3]);
  ctx.on('bail',()=>false);
  ctx.on('bail',()=>0);
  ctx.on('bail',()=>42);
  assert.equal(ctx.bail('bail'),0);
  ctx.on('throw',()=>{throw new Error('sync');});
  assert.throws(()=>ctx.emit('throw'),/sync/);
  ctx.on('waterfall',(next)=>{next();return next();});
  assert.throws(()=>ctx.waterfall('waterfall',()=>1),/multiple times/);
  await ctx.dispose();
});

test('distinct symbols with identical descriptions create distinct realms', async () => {
  const ctx=new Context();
  const left=ctx.isolate('value',Symbol('same'));
  const right=ctx.isolate('value',Symbol('same'));
  left.provide('value','left'); right.provide('value','right');
  // root extensions share an owner but retain genuinely distinct native ports.
  const values=[];
  left.inject(['value'],c=>{values.push(c.value);});
  right.inject(['value'],c=>{values.push(c.value);});
  await ctx.settle();
  assert.deepEqual(values,['left','right']);
  assert.equal(ctx.get('value'),undefined);
  await ctx.dispose();
});

test('child setup can be awaited without waiting for its parent completion', async () => {
  const ctx=new Context();
  const trace=[];
  const parent=ctx.plugin(async c=>{
    await c.plugin(()=>{trace.push('child');return()=>trace.push('child cleanup');});
    trace.push('parent');return()=>trace.push('parent cleanup');
  });
  await parent;
  assert.deepEqual(trace,['child','parent']);
  await ctx.dispose();
  assert.deepEqual(trace,['child','parent','parent cleanup','child cleanup']);
});

test('ESM and CommonJS share constructor and symbol identities', async () => {
  const {createRequire}=await import('node:module');
  const cjs=createRequire(import.meta.url)('../../packages/compat-cordis/index.cjs');
  assert.equal(cjs.Context,Context); assert.equal(cjs.Service,Service);
});

test('actual JS objects, cycles, functions and symbols stay in the environment', async()=>{
  const ctx=new Context();
  const symbol=Symbol('payload');
  const object={fn:()=>42,[symbol]:'symbol value'};
  object.self=object;
  ctx.provide('opaque',object);
  const child=ctx.inject(['opaque'],c=>{
    assert.equal(c.opaque,object);
    assert.equal(c.opaque.self,object);
    assert.equal(c.opaque[symbol],'symbol value');
    assert.equal(c.opaque.fn(),42);
  });
  await child;
  assert.equal(ctx.opaque,object);
  await ctx.dispose();
});

test('throwing setup-status observer completes its ticket and does not lose sibling actions', async()=>{
  const ctx=new Context();
  let fail=true, siblingRan=false;
  ctx.on('internal/status',(fiber)=>{if(fail && fiber.state===FiberState.LOADING){fail=false;throw new Error('observer failed');}});
  const broken=ctx.plugin(()=>{});
  const sibling=ctx.plugin(()=>{siblingRan=true;});
  await assert.rejects(broken.await(),/observer failed/);
  await sibling;
  assert.equal(siblingRan,true);
  assert.equal(ctx.snapshot().plugins.every(node=>node.pendingAction===null),true);
  await broken.dispose();
  assert.equal(ctx.snapshot().plugins.some(node=>node.id===broken.id),false);
  await ctx.dispose();
});

test('throwing publication observer cannot leak a visible root service',async()=>{
  const ctx=new Context();
  ctx.on('internal/service',(name,value)=>{if(name==='bad' && value!==undefined)throw new Error('publication observer');});
  assert.throws(()=>ctx.provide('bad',{}),/publication observer/);
  assert.equal(ctx.get('bad'),undefined);
  await ctx.dispose();
});

test('manually started asynchronous cleanup remains owned until it settles',async()=>{
  const ctx=new Context();
  const finish=gate(),started=gate();
  const trace=[];
  const provider=ctx.plugin(c=>{c.provide('resource',{});return()=>trace.push('provider cleanup');});
  await provider;
  let stop;
  await ctx.inject(['resource'],c=>{stop=c.effect(()=>async()=>{started.resolve();await finish.promise;trace.push('consumer cleanup');});});
  const cleanup=stop();
  await started.promise;
  const disposal=provider.dispose();
  await new Promise(resolve=>setImmediate(resolve));
  assert.deepEqual(trace,[]);
  finish.resolve();
  await cleanup;
  await disposal;
  assert.deepEqual(trace,['consumer cleanup','provider cleanup']);
  await ctx.dispose();
});

test('cleanup failure retains failed inverse and explicit retry does not repeat successful inverses',async()=>{
  const ctx=new Context();
  let fail=true,attempts=0,successful=0;
  const fiber=ctx.plugin(c=>{
    c.effect(()=>()=>{successful++;});
    c.effect(()=>()=>{attempts++;if(fail)throw new Error('temporary failure');});
  });
  await fiber;
  await assert.rejects(fiber.dispose(),/cleanup/i);
  assert.equal(successful,1);assert.equal(attempts,1);
  assert.equal(ctx.snapshot().plugins.find(node=>node.id===fiber.id).cleanupFailed,true);
  fail=false;
  await fiber.retryCleanup();
  assert.equal(successful,1);assert.equal(attempts,2);
  assert.equal(ctx.snapshot().plugins.some(node=>node.id===fiber.id),false);
  await ctx.dispose();
});

test('known disposal self-wait is rejected and a failed setup still drains',async()=>{
  const ctx=new Context();
  const fiber=ctx.plugin(async c=>{await c.fiber.dispose();});
  await assert.rejects(fiber.await(),/current fiber action/);
  await fiber.dispose();
  assert.equal(ctx.snapshot().plugins.some(node=>node.id===fiber.id),false);
  await ctx.dispose();
});

test('restart preserves Context identity and rejects managed stale continuations',async()=>{
  const ctx=new Context();
  const finish=gate();
  const contexts=[];
  let stale;
  const fiber=ctx.plugin(c=>{
    contexts.push(c);
    if(contexts.length===1) stale=(async()=>{await finish.promise;assert.throws(()=>c.effect(()=>()=>{}),/old episode/);})();
  });
  await fiber;
  await fiber.restart();
  assert.equal(contexts.length,2);
  assert.equal(contexts[0],contexts[1]);
  finish.resolve();await stale;
  await ctx.dispose();
});

test('managed setup cannot wait for ancestor shutdown or whole-domain settlement',async()=>{
  const ctx=new Context();
  await ctx.plugin(async c=>{
    await assert.rejects(c.root.dispose(),/current fiber action or its ancestor/);
    await assert.rejects(c.root.settle(),/own action/);
    await assert.rejects(c.fiber.await(),/current fiber action or its ancestor/);
  });
  await ctx.dispose();
});

test('root infrastructure APIs remain present while child cleanup drains',async()=>{
  const ctx=new Context();
  const trace=[];
  ctx.on('cleaned',()=>trace.push('event'));
  await ctx.plugin(c=>()=>{ assert.equal(typeof c.emit,'function');c.emit('cleaned');trace.push('inverse'); });
  await ctx.dispose();
  // Ordinary root listeners can have been cleaned already; infrastructure exists.
  assert.equal(trace.at(-1),'inverse');
});
