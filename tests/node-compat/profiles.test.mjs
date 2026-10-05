import test from 'node:test';
import assert from 'node:assert/strict';
import {spawnSync} from 'node:child_process';
import {createRequire} from 'node:module';
import {Context as CordisContext, FiberState} from '../../packages/compat-cordis/index.js';
import {Context as HarnessContext} from '../../packages/compat-harness/index.js';

for (const [profile,Context] of [['cordis',CordisContext],['harness',HarnessContext]]) {
  test(`${profile} has an immutable native profile and a matching update return contract`,async()=>{
    const ctx=new Context();const seen=[];const wrapped=ctx.plugin((_c,config)=>{seen.push(config);},1);
    await wrapped;const result=wrapped.update(2);
    assert.equal(result===undefined,profile==='harness');
    await wrapped.await();assert.deepEqual(seen,[1,2]);assert.equal(Object.hasOwn(wrapped,'config'),false);
    assert.equal(ctx.snapshot().profile,profile);await ctx.dispose();
  });
}

test('Harness resolves raw config only with dependencies and resolves again after dependency refresh',async()=>{
  const ctx=new HarnessContext();const trace=[];
  ctx.on('internal/config',function(config,next){trace.push(['resolve',this.ctx.value]);return {...next(),value:this.ctx.value};});
  const wrapped=ctx.plugin({inject:['value'],Config:{'~standard':{validate(config){trace.push(['schema',config.value]);return{value:config};}}},apply:(_c,config)=>{trace.push(['setup',config.value]);}},{});
  await wrapped;assert.deepEqual(trace,[]);assert.equal(wrapped.state,FiberState.PENDING);
  wrapped.update({});assert.deepEqual(trace,[]);
  const revoke=ctx.provide('value',1);await wrapped;
  await revoke();await ctx.settle();ctx.provide('value',2);await wrapped;
  assert.deepEqual(trace,[['resolve',1],['schema',1],['setup',1],['resolve',2],['schema',2],['setup',2]]);
  await ctx.dispose();
});

test('failed setup stays latched in Cordis and retries on relevant notifications in Harness',async()=>{
  for(const [Context,retries] of [[CordisContext,false],[HarnessContext,true]]){
    const ctx=new Context();let calls=0;
    ctx.provide('value',1);const child=ctx.inject(['value'],()=>{if(++calls===1)throw new Error('first failure');});
    await assert.rejects(Promise.resolve(child),/first failure/);await ctx.settle();
    ctx.reflect.notify(['unrelated']);await ctx.settle();assert.equal(calls,1);
    ctx.reflect.notify(['value']);await ctx.settle();assert.equal(calls,retries?2:1);
    assert.equal(child.state,retries?FiberState.ACTIVE:FiberState.FAILED);
    await ctx.dispose();
  }
});

test('Harness cancellation at the initial checkpoint prevents plugin execution',async()=>{
  const ctx=new HarnessContext();let ran=false;
  const child=ctx.plugin(()=>{ran=true;});
  const readiness=child.await(); // emits the setup action, before its await checkpoint
  const disposal=child.dispose();
  await Promise.all([readiness,disposal]);assert.equal(ran,false);await ctx.dispose();
});

test('Harness bootstrap routes scoped ESM/CJS/dynamic imports and rejects mixed schedulers',()=>{
  const script=`
    import assert from 'node:assert/strict'; import {createRequire} from 'node:module';
    import {Context} from '@deepseek-ai/cordis';
    const cjs=createRequire(import.meta.url)('@deepseek-ai/cordis');
    assert.equal(Context,cjs.Context);assert.equal(Context,(await import('@deepseek-ai/cordis')).Context);
    const ctx=new Context();assert.equal(ctx.snapshot().profile,'harness');await ctx.dispose();
    await assert.rejects(import('cordis'),{code:'ERR_CORDIS_UNSUPPORTED_IMPORT'});
    await assert.rejects(import('@deepseek-ai/cordis/internal'),{code:'ERR_CORDIS_UNSUPPORTED_IMPORT'});
  `;
  const result=spawnSync(process.execPath,['--import','./packages/compat-harness/register.js','--input-type=module','--eval',script],{encoding:'utf8',timeout:10000});
  assert.ifError(result.error);assert.equal(result.status,0,result.stderr);
});

test('native profiles cannot be reconfigured after allocation or initial configuration',()=>{
  const {NativeDriver}=createRequire(import.meta.url)('../../packages/compat-cordis/native/cordis.node');
  const driver=new NativeDriver();driver.command(JSON.stringify({op:'configure',profile:'harness'}));
  assert.throws(()=>driver.command(JSON.stringify({op:'configure',profile:'cordis'})),/ProfileFrozen/);
  const allocated=new NativeDriver();allocated.command(JSON.stringify({op:'mount'}));
  assert.throws(()=>allocated.command(JSON.stringify({op:'configure',profile:'harness'})),/ProfileFrozen/);
  allocated.command(JSON.stringify({op:'retire',id:'0'}));
  allocated.command(JSON.stringify({op:'drive'}));
  assert.throws(()=>allocated.command(JSON.stringify({op:'configure',profile:'harness'})),/ProfileFrozen/);
});

test('Harness teardown observers cannot interrupt cleanup and duplicate disposal joins',async()=>{
  const ctx=new HarnessContext();const trace=[];let duplicate;
  ctx.on('internal/plugin',fiber=>{if(fiber.uid===null){duplicate=fiber.dispose();trace.push('first');throw new Error('observer sync');}});
  ctx.on('internal/plugin',async fiber=>{if(fiber.uid===null){trace.push('second');throw new Error('observer async');}});
  const owner=await ctx.plugin(()=>()=>trace.push('inverse'));
  const disposal=owner.dispose();await disposal;await duplicate;
  assert.deepEqual(trace,['first','second','inverse']);
  assert.equal(ctx.logger.buffer.filter(message=>message.type==='error').length,2);
  await ctx.dispose();
});
