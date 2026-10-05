import test from 'node:test';
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {Context,FiberState} from '../../packages/compat-cordis/index.js';
const addon=fileURLToPath(new URL('../../target/node-compat/interop-fixture.node',import.meta.url));
function environment(options={}) {
  const ctx=new Context({addon}), trace=[];
  ctx.provide('jsSource',{
    read:()=>options.initial??7,
    query:options.query??(async (...args)=>({args,from:'javascript'})),
    record:(...args)=>{trace.push(args);return null;},
  });
  return {ctx,trace};
}

test('user-compiled factory shares one graph with JS, supports sync/async and real Rust Future wake',async()=>{
  const {ctx,trace}=environment();
  const rust=await ctx.rustPlugin('fixture.counter');
  assert.equal(rust.state,FiberState.ACTIVE);
  assert.equal(ctx.rustCounter.read(),7);
  assert.equal(ctx.rustCounter.add(3),10);
  const child=await ctx.inject(['rustCounter'],async c=>{
    assert.equal(c.rustCounter.read(),10);
    assert.equal(c.rustCounter.ctx.fiber.id,c.fiber.id);
    assert.deepEqual(await c.rustCounter.request('hello',{count:2}),{args:['hello',{count:2}],from:'javascript'});
    assert.deepEqual(await c.rustCounter.delay(2,{answer:42}),{answer:42});
    assert.deepEqual(await c.rustCounter.threadRequest('worker'),{args:['worker'],from:'javascript'});
  });
  const nodes=ctx.snapshot().plugins;
  assert.equal(nodes.filter(node=>node.id===rust.id).length,1);
  assert.equal(nodes.filter(node=>node.id===child.id).length,1);
  assert.equal(nodes.length,3);
  await ctx.dispose();
  assert.deepEqual(trace,[['cleanup',10]]);
});

test('old Rust wrappers and detached methods cannot redirect across episodes',async()=>{
  const {ctx}=environment();
  const rust=await ctx.rustPlugin('fixture.counter');
  const old=ctx.rustCounter,read=old.read;
  await rust.restart();
  assert.equal(ctx.rustCounter.read(),7);
  assert.throws(()=>old.read(),/STALE|no longer admitted/);
  assert.throws(()=>read(),/STALE|no longer admitted/);
  const current=ctx.rustCounter;
  await rust.dispose();
  assert.throws(()=>current.read(),/STALE|no longer admitted/);
  await ctx.dispose();
});

test('a consumer cancels only its own Rust call and cleanup drains actual completion',async()=>{
  const {ctx}=environment();
  await ctx.rustPlugin('fixture.counter');
  let first,second,done=false;
  const a=await ctx.inject(['rustCounter'],c=>{first=c.rustCounter.waitCancelled();});
  const b=await ctx.inject(['rustCounter'],c=>{second=c.rustCounter.waitCancelled();second.then(()=>done=true);});
  await a.dispose();
  assert.equal(await first,'cancelled');
  assert.equal(done,false);
  assert.equal(ctx.rustCounter.read(),7);
  await b.dispose();
  assert.equal(await second,'cancelled');
  await ctx.dispose();
});

test('provider retirement preserves a committed consumer cleanup call',async()=>{
  const {ctx,trace}=environment();
  const rust=await ctx.rustPlugin('fixture.counter');
  const publicView=ctx.rustCounter;
  let cleanupRead;
  await ctx.inject(['rustCounter'],c=>()=>{cleanupRead=c.rustCounter.read();});
  const closing=rust.dispose();
  assert.throws(()=>publicView.read(),/STALE|no longer admitted/);
  await closing;
  assert.equal(cleanupRead,7);
  assert.deepEqual(trace,[['cleanup',7]]);
  await ctx.dispose();
});

test('Rust cancellation waits for an already dispatched JavaScript promise',async()=>{
  const entered=Promise.withResolvers(),gate=Promise.withResolvers();
  const {ctx,trace}=environment({query:async()=>{entered.resolve();await gate.promise;return 'landed';}});
  const rust=await ctx.rustPlugin('fixture.counter');
  const call=ctx.rustCounter.request();
  await entered.promise;
  let closed=false;
  const closing=rust.dispose().then(()=>closed=true);
  await new Promise(resolve=>setImmediate(resolve));
  assert.equal(closed,false);
  assert.deepEqual(trace,[]);
  gate.resolve();
  assert.equal(await call,'landed');
  await closing;
  assert.equal(closed,true);
  await ctx.dispose();
});

test('Rust partial setup failure cleans its acquired instance and publication',async()=>{
  const {ctx,trace}=environment();
  const pending=ctx.rustPlugin('fixture.counter',{failSetup:true});
  await assert.rejects(Promise.resolve(pending),/configured setup failure/);
  assert.equal(ctx.rustCounter,undefined);
  assert.deepEqual(trace,[['cleanup',7]]);
  await pending.dispose();
  await ctx.dispose();
});

test('failed Rust cleanup retains the instance and committed JS dependencies for retry',async()=>{
  const {ctx,trace}=environment();
  const rust=await ctx.rustPlugin('fixture.counter',{failCleanupOnce:true});
  await assert.rejects(rust.dispose(),/cleanup|Native/i);
  assert.deepEqual(trace,[['cleanup',7]]);
  assert.ok(ctx.snapshot().plugins.some(node=>node.id===rust.id && node.cleanupFailed));
  await rust.retryCleanup();
  assert.deepEqual(trace,[['cleanup',7],['cleanup',7]]);
  await ctx.dispose();
});

test('reverse JavaScript call cannot wait for its Rust action or ancestor disposal',async()=>{
  let ctx,rust;
  ({ctx}=environment({query:async()=>{
    await assert.rejects(ctx.dispose(),error=>error.code==='REENTRANT_MUTATION');
    assert.throws(()=>rust.dispose(),error=>error.code==='REENTRANT_MUTATION');
    return 'safe';
  }}));
  rust=await ctx.rustPlugin('fixture.counter');
  assert.equal(await ctx.rustCounter.request(),'safe');
  await ctx.dispose();
});

test('Rust factory injection and publication respect the same JS isolation realms',async()=>{
  const ctx=new Context({addon});
  const left=ctx.isolate('jsSource').isolate('rustCounter');
  const right=ctx.isolate('jsSource').isolate('rustCounter');
  left.provide('jsSource',{read:()=>10,record:()=>null});
  right.provide('jsSource',{read:()=>20,record:()=>null});
  await left.rustPlugin('fixture.counter');
  await right.rustPlugin('fixture.counter');
  assert.equal(left.rustCounter.read(),10);
  assert.equal(right.rustCounter.read(),20);
  assert.equal(ctx.rustCounter,undefined);
  await ctx.dispose();
});

test('cleanup drains Rust calls created by a previous call continuation',async()=>{
  const first=Promise.withResolvers(),second=Promise.withResolvers();
  const gates=[Promise.withResolvers(),Promise.withResolvers()];
  const {ctx}=environment({query:async index=>{[first,second][index].resolve();await gates[index].promise;return index;}});
  await ctx.rustPlugin('fixture.counter');
  let chain;
  const consumer=await ctx.inject(['rustCounter'],c=>()=>{
    chain=c.rustCounter.request(0).then(()=>c.rustCounter.request(1));
  });
  let closed=false;
  const closing=consumer.dispose().then(()=>closed=true);
  await first.promise;
  gates[0].resolve();
  await second.promise;
  await new Promise(resolve=>setImmediate(resolve));
  assert.equal(closed,false);
  gates[1].resolve();
  assert.equal(await chain,1);
  await closing;
  await ctx.dispose();
});

test('reverse calls reject waiting for a service dependency outside the ownership ancestors',async()=>{
  const ctx=new Context({addon});
  let source;
  source=await ctx.plugin(c=>{
    c.provide('jsSource',{
      read:()=>7,record:()=>null,
      query:()=>{assert.throws(()=>source.dispose(),error=>error.code==='REENTRANT_MUTATION');return 'safe';},
    });
  });
  await ctx.rustPlugin('fixture.counter');
  assert.equal(await ctx.rustCounter.request(),'safe');
  await ctx.dispose();
});

test('chained cleanup crosses Rust, traceable JS and another withdrawn Rust provider',async()=>{
  const {Service}=await import('../../packages/compat-cordis/index.js');
  const ctx=new Context({addon}),observations=[],late=Promise.withResolvers();
  let continuation;
  const b=ctx.isolate('jsSource').isolate('rustCounter');
  b.provide('jsSource',{read:()=>11,record:()=>null});
  const provider=await b.rustPlugin('fixture.counter');
  class Relay extends Service {
    static inject=['rustCounter'];
    constructor(c){super(c,'jsSource');}
    read(){return this.ctx.rustCounter.read();}
    query(){continuation??=late.promise.then(()=>this.ctx.rustCounter.read());const value=this.ctx.rustCounter.read();observations.push(['query',value]);return value;}
    record(){const value=this.ctx.rustCounter.read();observations.push(['cleanup',value]);return null;}
  }
  const middle=b.isolate('jsSource');
  await middle.plugin(Relay);
  const a=middle.isolate('rustCounter');
  await a.rustPlugin('fixture.counter');
  await a.inject(['rustCounter'],c=>async()=>{assert.equal(await c.rustCounter.request(),11);});
  assert.equal(await a.rustCounter.request(),11);
  const stale=assert.rejects(continuation,/StaleAuthority/);
  late.resolve();
  await stale;
  await provider.dispose();
  assert.deepEqual(observations,[['query',11],['query',11],['cleanup',11]]);
  await ctx.dispose();
});

test('default and user addon instances have independent factory registries and graphs',async()=>{
  const ordinary=new Context();
  const {ctx}=environment();
  assert.throws(()=>ordinary.rustPlugin('fixture.counter'),/not registered/);
  await ctx.rustPlugin('fixture.counter');
  assert.equal(ctx.rustCounter.read(),7);
  assert.equal(ordinary.rustCounter,undefined);
  await ordinary.dispose();
  assert.equal(ctx.rustCounter.read(),7);
  await ctx.dispose();
});

test('dependency withdrawal wakes Rust setup cancellation without directly retiring that Rust fiber',async()=>{
  const ctx=new Context({addon}),entered=Promise.withResolvers(),trace=[];
  const source=await ctx.plugin(c=>c.provide('jsSource',{
    read:()=>7,
    record:(...args)=>{trace.push(args);if(args[0]==='setup-wait')entered.resolve();return null;},
  }));
  const rust=ctx.rustPlugin('fixture.counter',{waitSetupCancellation:true});
  const ready=Promise.resolve(rust);
  ready.catch(()=>{});
  await entered.promise;
  await source.dispose();
  await assert.rejects(ready,/Cancelled/);
  assert.deepEqual(trace,[['setup-wait',7],['cleanup',7]]);
  assert.ok(ctx.snapshot().plugins.some(item=>item.id===rust.id && !item.retired));
  await ctx.dispose();
});

test('Rust poll panic rejects pending work and does not keep the Node environment alive',()=>{
  const facade=new URL('../../packages/compat-cordis/index.js',import.meta.url).href;
  const code=`
    import assert from 'node:assert/strict';
    import {Context} from ${JSON.stringify(facade)};
    const ctx=new Context({addon:${JSON.stringify(addon)}});
    ctx.provide('jsSource',{read:()=>7,record:()=>null});
    await ctx.rustPlugin('fixture.counter');
    const other=ctx.rustCounter.delay(20,'late');
    const failed=ctx.rustCounter.panicPoll();
    await assert.rejects(failed,/DomainFaulted/);
    await assert.rejects(other,/DomainFaulted/);
    await assert.rejects(ctx.dispose(),/DomainFaulted/);
    console.log('fault-contained-cleanup-unconfirmed');
  `;
  const result=spawnSync(process.execPath,['--input-type=module','--eval',code],{encoding:'utf8',timeout:10000});
  assert.ifError(result.error);
  assert.equal(result.status,0,result.stdout+result.stderr);
  assert.match(result.stdout,/fault-contained-cleanup-unconfirmed/);
});

test('an admitted reverse call completes its old dependency chain after withdrawal',async()=>{
  const {Service}=await import('../../packages/compat-cordis/index.js');
  const ctx=new Context({addon}),entered=Promise.withResolvers(),gate=Promise.withResolvers();
  const b=ctx.isolate('jsSource').isolate('rustCounter');
  b.provide('jsSource',{read:()=>23,record:()=>null});
  const provider=await b.rustPlugin('fixture.counter');
  class Relay extends Service {
    static inject=['rustCounter'];
    constructor(c){super(c,'jsSource');}
    read(){return this.ctx.rustCounter.read();}
    async query(){entered.resolve();await gate.promise;return this.ctx.rustCounter.read();}
    record(){assert.equal(this.ctx.rustCounter.read(),23);return null;}
  }
  const middle=b.isolate('jsSource');
  await middle.plugin(Relay);
  const a=middle.isolate('rustCounter');
  await a.rustPlugin('fixture.counter');
  const call=a.rustCounter.request();
  await entered.promise;
  let disposed=false;
  const closing=provider.dispose().then(()=>disposed=true);
  await new Promise(resolve=>setImmediate(resolve));
  assert.equal(disposed,false);
  gate.resolve();
  assert.equal(await call,23);
  await closing;
  await ctx.dispose();
});
