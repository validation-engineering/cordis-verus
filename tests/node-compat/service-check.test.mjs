import test from 'node:test';
import assert from 'node:assert/strict';
import {Context,Service,FiberState,Inject,symbols} from '../../packages/compat-cordis/index.js';

test('Service.check controls individual consumers and set does not notify implicitly',async()=>{
  const ctx=new Context(); let calls=0; const trace=[];
  class Feature extends Service {
    constructor(c){super(c,'feature');this.enabled=false;}
    [Service.check](){calls++;return this.enabled;}
  }
  await ctx.plugin(Feature);
  const child=ctx.inject(['feature'],c=>{trace.push('setup');return()=>trace.push(`cleanup:${c.feature.enabled}`);});
  await child; assert.equal(child.state,FiberState.PENDING);assert.equal(calls,1);
  ctx.feature.enabled=true; await ctx.settle(); assert.equal(child.state,FiberState.PENDING);assert.equal(calls,1);
  ctx.reflect.notify(['feature']);await ctx.settle();assert.equal(child.state,FiberState.ACTIVE);assert.equal(calls,2);
  ctx.feature.enabled=false; ctx.reflect.notify(['feature']);await ctx.settle();assert.equal(child.state,FiberState.PENDING);
  assert.deepEqual(trace,['setup','cleanup:false']);await ctx.dispose();
});

test('plain checked values keep synchronous notification and require explicit set notification',async()=>{
  const ctx=new Context();let calls=0;
  ctx.provide('value',{enabled:true},function(){calls++;return this.enabled;});
  const child=ctx.inject(['value'],()=>{});await child;assert.equal(calls,1);
  ctx.set('value',{enabled:false});await ctx.settle();assert.equal(calls,1);assert.equal(child.state,FiberState.ACTIVE);
  ctx.reflect.notify(['value']);assert.equal(calls,2);await ctx.settle();assert.equal(child.state,FiberState.PENDING);
  await ctx.dispose();
});

test('reentrant set invalidates an in-flight check instead of adopting its old result',async()=>{
  const ctx=new Context();let calls=0;
  ctx.provide('value',{enabled:true},function(){calls++;if(calls===1)ctx.set('value',{enabled:false});return this.enabled;});
  const child=ctx.inject(['value'],()=>{});await child;assert.equal(child.state,FiberState.PENDING);assert.equal(calls,1);
  await ctx.settle();assert.equal(calls,1);
  assert.match(ctx.snapshot().checkErrors[0].error,/invalidated/);
  ctx.reflect.notify(['value']);await ctx.settle();assert.equal(calls,2);assert.equal(child.state,FiberState.PENDING);
  await ctx.dispose();
});

test('reentrant notify advances only real notifications and commits the latest check',async()=>{
  const ctx=new Context();let calls=0;
  ctx.provide('value',{},()=>{calls++;if(calls===1){ctx.reflect.notify(['value']);return false;}return true;});
  const child=ctx.inject(['value'],()=>{});await child;assert.equal(calls,2);assert.equal(child.state,FiberState.ACTIVE);
  await ctx.dispose();
});

test('cyclic Service.check notification is bounded and does not claim readiness',async()=>{
  const ctx=new Context();let calls=0;
  ctx.provide('value',{},()=>{calls++;ctx.reflect.notify(['value']);return true;});
  assert.throws(()=>ctx.inject(['value'],()=>{}),/256 calls/);
  assert.equal(calls,256);
  await ctx.dispose();
});

test('check exceptions are unavailable diagnostics and later notifications can recover',async()=>{
  const ctx=new Context();let broken=true;
  ctx.provide('value',{},()=>{if(broken)throw new Error('checker failed');return true;});
  const child=ctx.inject(['value'],()=>{});await child;assert.equal(child.state,FiberState.PENDING);
  assert.match(ctx.snapshot().checkErrors[0].error,/checker failed/);
  broken=false;ctx.reflect.notify(['value']);await ctx.settle();assert.equal(child.state,FiberState.ACTIVE);
  await ctx.dispose();
});

test('internal/plugin observers may change required injection before native sealing',async()=>{
  const ctx=new Context();ctx.provide('value',42);const values=[];
  const off=ctx.on('internal/plugin',fiber=>{fiber.inject={value:null};});
  const child=ctx.plugin(c=>{values.push(c.value);});off();await child;
  assert.deepEqual(values,[42]);await ctx.dispose();
});

test('observer disposal owns an unsealed child without starting its setup',async()=>{
  const ctx=new Context();let ran=false;
  ctx.on('internal/plugin',fiber=>{fiber.dispose();});
  const child=ctx.plugin(()=>{ran=true;});await ctx.settle();assert.equal(ran,false);assert.equal(child.uid,null);
  await ctx.dispose();
});

test('cross-owner replacement waits for old leases without deleting the old owner',async()=>{
  const ctx=new Context();const gate=Promise.withResolvers();const entered=Promise.withResolvers();const trace=[];
  let revoke;
  const first=ctx.plugin(c=>{revoke=c.provide('value',{label:'old'});});await first;
  const child=ctx.inject(['value'],c=>{trace.push(`setup:${c.value.label}`);return async()=>{trace.push(`cleanup:${c.value.label}`);entered.resolve();await gate.promise;};});await child;
  const drained=revoke();
  const second=ctx.plugin(c=>{c.provide('value',{label:'new'});});await second;
  await entered.promise;assert.equal(ctx.value.label,'new');assert.equal(first.state,FiberState.ACTIVE);
  let finished=false;drained.then(()=>finished=true);await Promise.resolve();assert.equal(finished,false);
  gate.resolve();await drained;await ctx.settle();assert.deepEqual(trace,['setup:old','cleanup:old','setup:new']);
  assert.equal(first.state,FiberState.ACTIVE);await ctx.dispose();
});

test('method Inject uses an owned child and class decorators preserve inherited injection',async()=>{
  const ctx=new Context();ctx.provide('value',9);const trace=[];const initializers=[];
  class Base extends Service {constructor(c){super(c,'base');for(const initialize of initializers)initialize.call(this);} run(){trace.push(this.ctx.value);return()=>trace.push('cleanup');}}
  Inject('value')(Base.prototype.run,{kind:'method',addInitializer:fn=>initializers.push(fn)});
  const mounted=ctx.plugin(Base);await ctx.settle();assert.deepEqual(trace,[9]);await mounted.dispose();assert.deepEqual(trace,[9,'cleanup']);
  class Parent{};Inject('value')(Parent,{kind:'class'});class Child extends Parent{};Inject('extra')(Child,{kind:'class'});
  assert.deepEqual({...Inject.resolve(Child.inject)},{value:null,extra:null});assert.equal(Parent.inject.extra,undefined);
  await ctx.dispose();
});

test('rejected async check and schema results are observed while rejecting their unsupported contract',async()=>{
  const {spawnSync}=await import('node:child_process');
  const result=spawnSync(process.execPath,['--unhandled-rejections=strict','--input-type=module','--eval',`
    import assert from 'node:assert/strict';
    import {Context,FiberState} from './packages/compat-cordis/index.js';
    const c=new Context();
    c.provide('value',{},async()=>{throw new Error('async check escaped');});
    const child=await c.inject(['value'],()=>{});assert.equal(child.state,FiberState.PENDING);
    assert.match(c.snapshot().checkErrors[0].error,/synchronously/);
    assert.throws(()=>c.plugin({Config:{'~standard':{validate:async()=>{throw new Error('async schema escaped');}}},apply:()=>{}}),/Async config/);
    await new Promise(resolve=>setImmediate(resolve));await c.dispose();
  `],{encoding:'utf8',timeout:10000});
  assert.ifError(result.error);assert.equal(result.status,0,result.stderr);
});
