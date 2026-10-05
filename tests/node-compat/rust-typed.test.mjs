import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { Context,FiberState } from '../../packages/compat-cordis/index.js';
const addon=fileURLToPath(new URL('../../target/node-compat/interop-fixture.node',import.meta.url));
const turn=()=>new Promise(resolve=>setImmediate(resolve));
async function environment(t) {
  const ctx=new Context({addon});
  t.after(()=>ctx.dispose());
  const control=await ctx.rustPlugin('fixture.typedControl');
  return {ctx,control};
}
const phases=(events,label)=>events.filter(item=>item.label===label).map(item=>item.phase);
async function waitFor(control,phase,label) {
  for(let i=0;i<200;i++){
    if(control.events().some(item=>item.phase===phase&&item.label===label))return;
    await turn();
  }
  throw new Error('typed fixture did not reach '+phase+':'+label);
}

test('real typed provider and consumer share one Arc and observe JS mutation',async t=>{
  const {ctx}=await environment(t);
  await ctx.rustPlugin('fixture.typedCounter',{label:'shared',initial:10});
  await ctx.rustPlugin('fixture.typedConsumer');
  assert.deepEqual(ctx.typedCounter.read(),{value:10,activation:1,label:'shared'});
  assert.deepEqual(ctx.typedConsumer.read(),{value:10,activation:1,label:'shared',sameInstance:true});
  assert.equal(ctx.typedCounter.add(5),15);
  assert.equal(ctx.typedConsumer.read().value,15);
  assert.deepEqual(await ctx.typedCounter.readAsync(),{value:15,activation:1,label:'shared'});
  assert.equal(ctx.snapshot().plugins.length,4); // root + three actual factories, no hidden Runtime graph
});

test('typed service mappings preserve two realms and independent Fiber FnMut state',async t=>{
  const {ctx}=await environment(t);
  const left=ctx.isolate('typedCounter').isolate('typedConsumer');
  const right=ctx.isolate('typedCounter').isolate('typedConsumer');
  const a=await left.rustPlugin('fixture.typedCounter',{label:'left',initial:10});
  await right.rustPlugin('fixture.typedCounter',{label:'right',initial:20});
  await left.rustPlugin('fixture.typedConsumer');await right.rustPlugin('fixture.typedConsumer');
  assert.equal(left.typedConsumer.read().sameInstance,true);assert.equal(right.typedConsumer.read().sameInstance,true);
  left.typedCounter.add(3);assert.equal(left.typedConsumer.read().value,13);assert.equal(right.typedConsumer.read().value,20);
  await a.restart();await ctx.settle();
  assert.equal(left.typedCounter.read().activation,2);assert.equal(left.typedConsumer.read().activation,2);
  assert.equal(right.typedCounter.read().activation,1);
  assert.equal(ctx.get('typedCounter'),undefined);
});

test('same-config restart preserves the actual Plugin FnMut definition and invalidates old views',async t=>{
  const {ctx}=await environment(t);
  const fiber=await ctx.rustPlugin('fixture.typedCounter',{label:'restart',initial:3});
  const old=ctx.typedCounter;old.add(4);
  await fiber.restart();
  assert.deepEqual(ctx.typedCounter.read(),{value:3,activation:2,label:'restart'});
  assert.throws(()=>old.read(),/STALE|no longer admitted/);
  const events=ctx.typedControl.events();
  assert.equal(events.find(item=>item.phase==='counter:cleanup'&&item.label==='restart').value,7);
  assert.equal(phases(events,'restart').includes('definition:drop'),false);
  await fiber.dispose();
  assert.equal(phases(ctx.typedControl.events(),'restart').filter(value=>value==='definition:drop').length,1);
});

test('Pending after dependency withdrawal retains the definition until its real removal',async t=>{
  const {ctx,control}=await environment(t);
  const fiber=await ctx.rustPlugin('fixture.typedCounter',{label:'pending'});
  await control.dispose();
  assert.equal(fiber.state,FiberState.PENDING);
  await ctx.rustPlugin('fixture.typedControl');
  await ctx.settle();
  assert.equal(ctx.typedCounter.read().activation,2);
  assert.equal(phases(ctx.typedControl.events(),'pending').includes('definition:drop'),false);
  await fiber.dispose();
  assert.equal(phases(ctx.typedControl.events(),'pending').filter(value=>value==='definition:drop').length,1);
});

test('provider withdrawal drains JS and typed consumers before the original typed inverse',async t=>{
  const {ctx}=await environment(t);
  const provider=await ctx.rustPlugin('fixture.typedCounter',{label:'withdraw'});
  const consumer=await ctx.rustPlugin('fixture.typedConsumer');
  const js=await ctx.inject(['typedConsumer','typedControl'],c=>()=>{
    assert.equal(c.typedConsumer.read().value,12);c.typedControl.note('withdraw');
  });
  ctx.typedCounter.add(5);
  const old=ctx.typedCounter;
  await provider.dispose();
  assert.throws(()=>old.read(),/STALE|no longer admitted/);
  assert.equal(consumer.state,FiberState.PENDING);assert.equal(js.state,FiberState.PENDING);
  const events=ctx.typedControl.events().filter(item=>item.label==='withdraw');
  const trace=events.map(item=>item.phase);
  for(const phase of ['js:cleanup','consumer:cleanup','counter:cleanup','counter:earlier']) {
    assert.equal(trace.filter(item=>item===phase).length,1,phase+' must execute exactly once');
  }
  assert.ok(trace.indexOf('js:cleanup')<trace.indexOf('consumer:cleanup'));
  assert.ok(trace.indexOf('consumer:cleanup')<trace.indexOf('counter:cleanup'));
  assert.ok(trace.indexOf('counter:cleanup')<trace.indexOf('counter:earlier'));
  assert.equal(events.find(item=>item.phase==='consumer:cleanup').sameInstance,true);
  assert.equal(events.find(item=>item.phase==='consumer:cleanup').value,12);
});

test('partial typed setup restores acquired inverses and releases definition only on Removed',async t=>{
  const {ctx}=await environment(t);
  const fiber=ctx.rustPlugin('fixture.typedCounter',{label:'partial',failSetup:true});
  await assert.rejects(Promise.resolve(fiber),/typed partial setup failure/);
  assert.equal(ctx.get('typedCounter'),undefined);
  assert.deepEqual(phases(ctx.typedControl.events(),'partial'),['counter:setup','counter:cleanup','counter:earlier']);
  await fiber.dispose();
  assert.deepEqual(phases(ctx.typedControl.events(),'partial'),['counter:setup','counter:cleanup','counter:earlier','definition:drop']);
});

test('real Plugin::new_async publishes only when setup has landed',async t=>{
  const {ctx}=await environment(t);
  const fiber=ctx.rustPlugin('fixture.typedCounter',{label:'async',asyncSetup:true});
  const mounting=Promise.resolve(fiber);mounting.catch(()=>{});
  try {
    await waitFor(ctx.typedControl,'counter:waiting','async');
    assert.equal(ctx.get('typedCounter'),undefined);
    ctx.typedControl.release('setup:async');await mounting;
    assert.equal(ctx.typedCounter.read().activation,1);
    assert.equal(ctx.typedControl.events().find(item=>item.phase==='counter:landed').cancelled,false);
  } finally {
    ctx.typedControl.release('setup:async');
    await Promise.allSettled([mounting]);
  }
});

test('cancelling async typed setup waits for its future to land before cleanup',async t=>{
  const {ctx}=await environment(t);
  const fiber=ctx.rustPlugin('fixture.typedCounter',{label:'cancel',asyncSetup:true});
  const mounting=Promise.resolve(fiber);mounting.catch(()=>{});
  let closing;
  try {
    await waitFor(ctx.typedControl,'counter:waiting','cancel');
    let closed=false;closing=fiber.dispose().then(()=>closed=true);closing.catch(()=>{});
    await turn();assert.equal(closed,false);
    assert.equal(phases(ctx.typedControl.events(),'cancel').includes('counter:cleanup'),false);
    ctx.typedControl.release('setup:cancel');
    await closing;await Promise.allSettled([mounting]);
    const events=ctx.typedControl.events();
    assert.equal(events.find(item=>item.phase==='counter:landed'&&item.label==='cancel').cancelled,true);
    assert.deepEqual(phases(events,'cancel'),['counter:setup','counter:waiting','counter:landed','counter:cleanup','counter:earlier','definition:drop']);
    assert.equal(ctx.get('typedCounter'),undefined);
  } finally {
    ctx.typedControl.release('setup:cancel');
    await Promise.allSettled([mounting,closing]);
  }
});

test('typed asynchronous inverse is awaited before removal and earlier inverses',async t=>{
  const {ctx}=await environment(t);
  const provider=await ctx.rustPlugin('fixture.typedCounter',{label:'cleanup',asyncCleanup:true});
  let closed=false;const closing=provider.dispose().then(()=>closed=true);closing.catch(()=>{});
  try {
    await waitFor(ctx.typedControl,'counter:cleanup-wait','cleanup');
    assert.equal(closed,false);assert.equal(phases(ctx.typedControl.events(),'cleanup').includes('counter:earlier'),false);
    ctx.typedControl.release('cleanup:cleanup');await closing;
    assert.deepEqual(phases(ctx.typedControl.events(),'cleanup'),['counter:setup','counter:cleanup-wait','counter:cleanup','counter:earlier','definition:drop']);
  } finally {
    ctx.typedControl.release('cleanup:cleanup');
    await Promise.allSettled([closing]);
  }
});

test('FnOnce typed cleanup failure remains sticky and cannot become an empty successful retry',()=>{
  const index=new URL('../../packages/compat-cordis/index.js',import.meta.url).href;
  const script=`import assert from 'node:assert/strict';import {Context} from ${JSON.stringify(index)};
const ctx=new Context({addon:${JSON.stringify(addon)}});await ctx.rustPlugin('fixture.typedControl');
const provider=await ctx.rustPlugin('fixture.typedCounter',{label:'sticky',failCleanup:true});
const typedFailure=error=>/typed inverse failed/.test(error.message)||Array.from(error.errors??[]).some(typedFailure)||(error.cause?typedFailure(error.cause):false);
await assert.rejects(provider.dispose(),typedFailure);
await assert.rejects(provider.retryCleanup(),typedFailure);
const events=ctx.typedControl.events().filter(item=>item.label==='sticky');
assert.equal(events.filter(item=>item.phase==='counter:cleanup').length,1);
assert.equal(events.some(item=>item.phase==='counter:earlier'||item.phase==='definition:drop'),false);
assert.ok(ctx.snapshot().plugins.some(item=>item.id===provider.id&&item.cleanupFailed));
console.log(JSON.stringify({cleanup:'blocked',replayed:false,removed:false}));
`;
  const result=spawnSync(process.execPath,['--input-type=module','--eval',script],{encoding:'utf8',timeout:10000});
  assert.equal(result.status,0,result.stderr);
  assert.deepEqual(JSON.parse(result.stdout.trim()),{cleanup:'blocked',replayed:false,removed:false});
});

test('same-named distinct ServiceKeys cannot substitute for the original typed identity',async t=>{
  const {ctx}=await environment(t);
  await ctx.rustPlugin('fixture.typedCounter');
  const wrong=ctx.rustPlugin('fixture.typedWrongKey');
  await assert.rejects(Promise.resolve(wrong),/TypedServiceMismatch/);
  assert.equal(ctx.get('typedConsumer'),undefined);await wrong.dispose();
});

test('a JS-only service with matching method names is not a typed Rust provider',async t=>{
  const {ctx}=await environment(t);
  await ctx.plugin(c=>{c.provide('typedCounter',{read:()=>({value:7})});});
  const consumer=ctx.rustPlugin('fixture.typedConsumer');
  await assert.rejects(Promise.resolve(consumer),/TypedProviderRequired/);
  assert.equal(ctx.get('typedConsumer'),undefined);await consumer.dispose();
});

test('changed config on the same typed Fiber fails explicitly rather than reusing another definition',async t=>{
  const {ctx}=await environment(t);
  const original={label:'config',initial:3};
  const provider=await ctx.rustPlugin('fixture.typedCounter',original);
  await assert.rejects(provider.update({label:'config',initial:99}),/TypedMountDefinitionChanged/);
  assert.equal(ctx.get('typedCounter'),undefined);
  assert.equal(phases(ctx.typedControl.events(),'config').includes('definition:drop'),false);
  await provider.update(original);
  assert.deepEqual(ctx.typedCounter.read(),{value:3,activation:2,label:'config'});
});

for(const operation of ['publish','mount','effect','set','refresh','provide_checked']) {
  test('typed static host rejects '+operation+' even when the plugin catches its error',async t=>{
    const {ctx}=await environment(t);
    const fiber=ctx.rustPlugin('fixture.typedCounter',{label:operation,unsupported:operation,ignoreUnsupported:true});
    await assert.rejects(Promise.resolve(fiber),/UnsupportedStaticFeature/);
    assert.equal(ctx.get('typedCounter'),undefined);
    assert.deepEqual(phases(ctx.typedControl.events(),operation),['counter:setup','counter:cleanup','counter:earlier']);
    await fiber.dispose();
  });
}
