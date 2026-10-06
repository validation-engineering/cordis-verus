import test from 'node:test';
import assert from 'node:assert/strict';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import { Context as CordisContext, FiberState } from '../../packages/compat-cordis/index.js';
import { Context as HarnessContext } from '../../packages/compat-harness/index.js';
const addon=fileURLToPath(new URL('../../target/node-compat/interop-fixture.node',import.meta.url));

for (const [profile,Context] of [['cordis',CordisContext],['harness',HarnessContext]]) {
  async function environment(t) {
    const ctx=new Context({addon});
    t.after(()=>ctx.dispose());
    await ctx.rustPlugin('fixture.typedControl');
    return ctx;
  }
  test(`${profile}: checked typed values reevaluate each consumer config after sync and async updates`,async t=>{
    const ctx=await environment(t);
    await ctx.rustPlugin('fixture.typedLive',{initial:5});
    const low=await ctx.plugin({inject:{typedLiveValue:{minimum:3}},apply(c){ assert.ok(c.typedLiveValue.read()>=3); }});
    const high=await ctx.plugin({inject:{typedLiveValue:{minimum:10}},apply(c){ assert.ok(c.typedLiveValue.read()>=10); }});
    assert.equal(low.state,FiberState.ACTIVE);assert.equal(high.state,FiberState.PENDING);
    const oldPublication=ctx.reflect.get('typedLiveValue',false);
    await ctx.typedLiveControl.setAsync(12);await ctx.settle();
    assert.equal(low.state,FiberState.ACTIVE);assert.equal(high.state,FiberState.ACTIVE);
    assert.equal(oldPublication.read(),12); // Same publication and interface, new typed slot payload.
    ctx.typedLiveControl.set(1);await ctx.settle();
    assert.equal(low.state,FiberState.PENDING);assert.equal(high.state,FiberState.PENDING);
    ctx.typedLiveControl.set(7);await ctx.settle();
    assert.equal(low.state,FiberState.ACTIVE);assert.equal(high.state,FiberState.PENDING);
  });
  test(`${profile}: typed consumer retains its committed slot and prior Arc through availability cleanup`,async t=>{
    const ctx=await environment(t);
    await ctx.rustPlugin('fixture.typedLive',{initial:5});
    const reader=await ctx.intercept('typedLiveValue',{minimum:0}).rustPlugin('fixture.typedLiveReader');
    assert.deepEqual(ctx.typedLiveReader.read(),{current:5,original:5,sameArc:true});
    ctx.typedLiveControl.set(9);await ctx.settle();
    assert.deepEqual(ctx.typedLiveReader.read(),{current:9,original:5,sameArc:false});
    ctx.typedLiveControl.set(-1);await ctx.settle();
    assert.equal(reader.state,FiberState.PENDING);
    const cleanup=ctx.typedControl.events().find(event=>event.phase==='live-reader:cleanup');
    assert.deepEqual(cleanup,{phase:'live-reader:cleanup',current:-1,original:5});
    ctx.typedLiveControl.set(2);await ctx.settle();
    assert.deepEqual(ctx.typedLiveReader.read(),{current:2,original:2,sameArc:true});
  });
  test(`${profile}: availability maps consumer realms and drops old episode refresh`,async t=>{
    const ctx=await environment(t);
    const left=ctx.isolate('typedLiveValue').isolate('typedLiveControl');
    const right=ctx.isolate('typedLiveValue').isolate('typedLiveControl');
    const owner=await left.rustPlugin('fixture.typedLive',{label:'left',initial:1});
    await right.rustPlugin('fixture.typedLive',{label:'right',initial:20});
    const a=await left.plugin({inject:{typedLiveValue:{minimum:5}},apply(){}});
    const b=await right.plugin({inject:{typedLiveValue:{minimum:5}},apply(){}});
    assert.equal(a.state,FiberState.PENDING);assert.equal(b.state,FiberState.ACTIVE);
    left.typedLiveControl.set(8);await ctx.settle();
    assert.equal(a.state,FiberState.ACTIVE);assert.equal(right.typedLiveValue.read(),20);
    const old=left.typedLiveControl;
    await owner.restart();await ctx.settle();
    assert.throws(()=>old.set(99),/STALE|no longer admitted/);
    assert.throws(()=>ctx.typedControl.refreshOld('left:1'),/completed|cancelled/);
    assert.equal(left.typedLiveValue.read(),1);assert.equal(a.state,FiberState.PENDING);
    assert.equal(b.state,FiberState.ACTIVE);
  });
  test(`${profile}: native availability rejects forged and replayed tickets and mismatched typed mappings`,async t=>{
    const ctx=await environment(t);
    const owner=await ctx.rustPlugin('fixture.typedLive');
    const host=owner._domain.rust, original=host.command.bind(host);
    let captured;
    host.command=request=>{
      if(request.op==='typed_check') {
        captured=structuredClone(request);
        assert.throws(()=>original({...request,ticket:{...request.ticket,publication:'999999'}}),/TypedCheckPublicationMismatch/);
        assert.throws(()=>original({...request,ticket:{...request.ticket,domain:'999999'}}),/StaleCheck/);
        assert.throws(()=>original({...request,realms:{...request.realms,typedControl:{...request.realms.typedControl,key:'999999'}}}),/TypedCheckPortMismatch/);
      }
      return original(request);
    };
    try {
      const consumer=await ctx.plugin({inject:{typedLiveValue:{minimum:0}},apply(){}});
      assert.equal(consumer.state,FiberState.ACTIVE);assert.ok(captured);
      assert.throws(()=>original(captured),/StaleCheck/);
    } finally {host.command=original;}
  });
  test(`${profile}: checked typed setup failure restores and check panic only denies availability`,async t=>{
    const ctx=await environment(t);
    const failing=ctx.rustPlugin('fixture.typedLive',{label:'partial',failSetup:true});
    await assert.rejects(Promise.resolve(failing),/live partial setup failed/);
    assert.equal(ctx.get('typedLiveValue'),undefined);
    assert.equal(ctx.typedControl.events().filter(e=>e.phase==='live:cleanup'&&e.label==='partial').length,1);
    await failing.dispose();
    await ctx.rustPlugin('fixture.typedLive',{panicCheck:true});
    const dependent=await ctx.plugin({inject:['typedLiveValue'],apply(){throw new Error('must not activate');}});
    assert.equal(dependent.state,FiberState.PENDING);
    assert.equal(ctx.typedLiveValue.read(),5); // Predicate panic does not poison the Node domain.
  });
}

test('failed live typed cleanup retains its publication and rejects all retained update handles',()=>{
  const index=new URL('../../packages/compat-cordis/index.js',import.meta.url).href;
  const script=`import assert from 'node:assert/strict';import {Context} from ${JSON.stringify(index)};
  const ctx=new Context({addon:${JSON.stringify(addon)}});await ctx.rustPlugin('fixture.typedControl');
  const owner=await ctx.rustPlugin('fixture.typedLive',{label:'failed',failCleanup:true});
  const hasFailure=e=>String(e.message).includes('live cleanup failed')||Array.from(e.errors??[]).some(hasFailure)||(e.cause?hasFailure(e.cause):false);
  await assert.rejects(owner.dispose(),hasFailure);await assert.rejects(owner.retryCleanup(),hasFailure);
  assert.throws(()=>ctx.typedControl.refreshOld('failed:1'),/cancelled|completed/);
  assert.ok(ctx.snapshot().plugins.find(p=>p.id===owner.id)?.cleanupFailed);
  assert.equal(ctx.typedControl.events().filter(e=>e.phase==='live:cleanup').length,1);console.log('retained');`;
  const result=spawnSync(process.execPath,['--input-type=module','--eval',script],{encoding:'utf8',timeout:10000});
  assert.equal(result.status,0,result.stderr);assert.equal(result.stdout.trim(),'retained');
});
