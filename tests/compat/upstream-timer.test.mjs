import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { registerHooks, stripTypeScriptTypes } from 'node:module';
import { Context, Service } from '../../packages/compat-cordis/index.js';

const timerUrl=new URL('../../upstream/cordis/packages/timer/src/index.ts',import.meta.url).href;
const facadeUrl=new URL('../../packages/compat-cordis/index.js',import.meta.url).href;
const hooks=registerHooks({
  resolve(specifier,context,nextResolve) {
    if (specifier==='cordis' && context.parentURL===timerUrl) return {url:facadeUrl,shortCircuit:true};
    return nextResolve(specifier,context);
  },
  load(url,context,nextLoad) {
    if (url===timerUrl) return {format:'module',source:stripTypeScriptTypes(readFileSync(new URL(url),'utf8'),{mode:'transform',sourceUrl:url}),shortCircuit:true};
    return nextLoad(url,context);
  },
});
const {default: TimerService}=await import(timerUrl);
hooks.deregister();

test('unmodified locked upstream TimerService loads through native driver', async t=>{
  t.mock.timers.enable({apis:['setTimeout','setInterval']});
  const ctx=new Context();
  const timer=ctx.plugin(TimerService);
  await timer;
  assert.equal(ctx.timer instanceof Service,true);
  assert.equal(ctx.timer instanceof TimerService,true);
  const trace=[];
  const consumer=ctx.inject(['timer'],c=>{
    c.timeout(()=>trace.push('timeout'),10);
    c.interval(()=>trace.push('interval'),20);
  });
  await consumer;
  t.mock.timers.tick(10);
  assert.deepEqual(trace,['timeout']);
  t.mock.timers.tick(10);
  assert.deepEqual(trace,['timeout','interval']);
  await consumer.dispose();
  t.mock.timers.tick(100);
  assert.deepEqual(trace,['timeout','interval']);
  await ctx.dispose();
});

test('TimerService Promise timer cancellation rejects and releases resource',async t=>{
  t.mock.timers.enable({apis:['setTimeout','setInterval']});
  const ctx=new Context();
  await ctx.plugin(TimerService);
  let timerPromise;
  const consumer=ctx.inject(['timer'],c=>{ timerPromise=c.timeout(100); });
  await consumer;
  const rejected=assert.rejects(timerPromise,/disposed/);
  await consumer.dispose();
  await rejected;
  await ctx.dispose();
});
