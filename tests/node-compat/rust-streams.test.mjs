import test from 'node:test';
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {Context} from '../../packages/compat-cordis/index.js';
const addon=fileURLToPath(new URL('../../target/node-compat/interop-fixture.node',import.meta.url));
const turn=()=>new Promise(resolve=>setImmediate(resolve));
function environment(stream,record) {
  const ctx=new Context({addon}),trace=[];
  ctx.provide('jsSource',{
    read:()=>7,query:async()=>null,stream,
    record:(...args)=>{trace.push(args);return record?.(...args)??null;},
  });
  return {ctx,trace};
}
const matching=(trace,name)=>trace.filter(item=>item[0]===name);

test('Rust streams are pull-driven async iterators and EOF waits for close',async()=>{
  const {ctx,trace}=environment();
  await ctx.rustPlugin('fixture.counter');
  const stream=ctx.rustCounter.stream({count:3});
  await turn();
  assert.deepEqual(matching(trace,'stream-pull'),[]);
  assert.deepEqual(await stream.next(),{done:false,value:0});
  await turn();
  assert.equal(matching(trace,'stream-pull').length,1);
  const rest=[];
  for await (const value of stream) rest.push(value);
  assert.deepEqual(rest,[1,2]);
  assert.equal(matching(trace,'stream-close').length,1);
  assert.deepEqual(await stream.return(),{done:true,value:undefined});
  assert.equal(matching(trace,'stream-close').length,1);
  await ctx.dispose();
});

test('for-await break closes a Rust stream exactly once',async()=>{
  const {ctx,trace}=environment();
  await ctx.rustPlugin('fixture.counter');
  const stream=ctx.rustCounter.stream({count:100});
  for await (const value of stream) { assert.equal(value,0); break; }
  assert.equal(matching(trace,'stream-pull').length,1);
  assert.equal(matching(trace,'stream-close').length,1);
  await ctx.dispose();
  assert.equal(matching(trace,'stream-close').length,1);
});

test('idle streams remain owned by a consumer and are closed on unload',async()=>{
  const {ctx,trace}=environment();
  await ctx.rustPlugin('fixture.counter');
  let stream;
  const consumer=await ctx.inject(['rustCounter'],c=>{stream=c.rustCounter.stream({count:100});});
  await consumer.dispose();
  assert.equal(matching(trace,'stream-pull').length,0);
  assert.equal(matching(trace,'stream-close').length,1);
  await assert.rejects(stream.next(),/STALE|no longer admitted/);
  await ctx.dispose();
});

test('concurrent pulls are bounded and return cancels then joins the in-flight pull',async()=>{
  const entered=Promise.withResolvers();
  const {ctx,trace}=environment(undefined,(phase)=>{if(phase==='stream-pull')entered.resolve();});
  await ctx.rustPlugin('fixture.counter');
  const stream=ctx.rustCounter.stream({waitForCancel:true});
  const pull=stream.next();
  pull.catch(()=>{});
  await entered.promise;
  await assert.rejects(stream.next(),/StreamBusy/);
  const a=stream.return(),b=stream.return();
  assert.equal(a,b);
  await Promise.allSettled([pull,a]);
  assert.equal(matching(trace,'stream-close').length,1);
  await ctx.dispose();
});

test('consumer cancellation does not cancel another consumer stream',async()=>{
  const {ctx,trace}=environment();
  await ctx.rustPlugin('fixture.counter');
  let first,second;
  const a=await ctx.inject(['rustCounter'],c=>{first=c.rustCounter.stream();});
  const b=await ctx.inject(['rustCounter'],c=>{second=c.rustCounter.stream();});
  await a.dispose();
  assert.equal(matching(trace,'stream-close').length,1);
  assert.deepEqual(await second.next(),{done:false,value:0});
  await assert.rejects(first.next(),/STALE|no longer admitted/);
  await b.dispose();
  assert.equal(matching(trace,'stream-close').length,2);
  await ctx.dispose();
});

test('failed Rust stream close retains its lease and succeeds on explicit retry',async()=>{
  const {ctx,trace}=environment();
  await ctx.rustPlugin('fixture.counter');
  const stream=ctx.rustCounter.stream({failCloseOnce:true});
  await assert.rejects(stream.return(),/close|Close/);
  await assert.rejects(stream.next(),/STALE|no longer admitted/);
  assert.equal(matching(trace,'stream-close').length,1);
  await stream.return();
  assert.equal(matching(trace,'stream-close').length,2);
  await ctx.dispose();
});

test('withdrawal waits for a stream pull reverse JS call to actually land',async()=>{
  const entered=Promise.withResolvers(),gate=Promise.withResolvers();
  const {ctx,trace}=environment(undefined,async phase=>{if(phase==='stream-pull'){entered.resolve();await gate.promise;}});
  const provider=await ctx.rustPlugin('fixture.counter');
  const stream=ctx.rustCounter.stream();
  const pull=stream.next();
  pull.catch(()=>{});
  await entered.promise;
  let closed=false;
  const closing=provider.dispose().then(()=>closed=true);
  await turn();
  assert.equal(closed,false);
  assert.equal(matching(trace,'stream-close').length,0);
  gate.resolve();
  await Promise.allSettled([pull,closing]);
  assert.equal(closed,true);
  assert.equal(matching(trace,'stream-close').length,1);
  await ctx.dispose();
});

test('Rust consumes JS stream values and journals natural EOF return',async()=>{
  let pulls=0,returns=0;
  const {ctx}=environment(()=>({
    async next(){return pulls<3?{done:false,value:pulls++}:{done:true};},
    async return(){returns++;return {done:true};},
  }));
  await ctx.rustPlugin('fixture.counter');
  assert.deepEqual(await ctx.rustCounter.consumeStream(),[0,1,2]);
  assert.equal(returns,1);
  await ctx.dispose();
  assert.equal(returns,1);
});

test('dropped JS stream is returned before its Rust job completes',async()=>{
  const entered=Promise.withResolvers(),gate=Promise.withResolvers();
  let pulls=0,returned=0;
  const {ctx}=environment(()=>({
    async next(){return {done:false,value:++pulls};},
    async return(){returned++;entered.resolve();await gate.promise;return {done:true};},
  }));
  await ctx.rustPlugin('fixture.counter');
  let landed=false;
  const call=ctx.rustCounter.takeStream(1).then(value=>{landed=true;return value;});
  await entered.promise;
  await turn();
  assert.equal(landed,false);
  assert.equal(pulls,1);
  gate.resolve();
  assert.deepEqual(await call,[1]);
  assert.equal(returned,1);
  await ctx.dispose();
});

test('provider cancellation returns JS iterator before joining a blocked next',async()=>{
  const entered=Promise.withResolvers(),gate=Promise.withResolvers();
  let returned=0;
  const {ctx}=environment(()=>({
    async next(){entered.resolve();await gate.promise;return {done:true};},
    async return(){returned++;gate.resolve();return {done:true};},
  }));
  const provider=await ctx.rustPlugin('fixture.counter');
  const call=ctx.rustCounter.consumeStream();
  call.catch(()=>{});
  await entered.promise;
  await provider.dispose();
  await Promise.allSettled([call]);
  assert.equal(returned,1);
  await ctx.dispose();
});

test('JS return failure is retained until owner cleanup retries with old dependencies',async()=>{
  let returned=0;
  const {ctx,trace}=environment(()=>({
    async next(){return {done:false,value:1};},
    async return(){if(++returned===1)throw new Error('first return failed');return {done:true};},
  }));
  const provider=await ctx.rustPlugin('fixture.counter');
  await assert.rejects(ctx.rustCounter.takeStream(1),/first return failed/);
  assert.equal(returned,1);
  await provider.dispose();
  assert.equal(returned,2);
  assert.equal(matching(trace,'cleanup').length,1);
  await ctx.dispose();
});

test('incomplete JS return is not accepted as resource release',async()=>{
  let returned=0;
  const {ctx}=environment(()=>({
    async next(){return {done:false,value:1};},
    async return(){return {done:++returned>1,value:null};},
  }));
  const provider=await ctx.rustPlugin('fixture.counter');
  await assert.rejects(ctx.rustCounter.takeStream(0),/IncompleteStreamClose/);
  assert.equal(returned,1);
  await provider.dispose();
  assert.equal(returned,2);
  await ctx.dispose();
});

test('consumer close failure retains inverses and only failed streams retry',async()=>{
  const {ctx,trace}=environment();
  await ctx.rustPlugin('fixture.counter');
  let inverse=0;
  const consumer=await ctx.inject(['rustCounter'],c=>{
    c.rustCounter.stream();
    c.rustCounter.stream({failCloseOnce:true});
    return ()=>{inverse++;};
  });
  await assert.rejects(consumer.dispose(),/cleanup|Native/i);
  assert.equal(inverse,0);
  assert.equal(matching(trace,'stream-close').length,2);
  assert.equal(ctx.snapshot().plugins.find(item=>item.id===consumer.id).cleanupFailed,true);
  await consumer.retryCleanup();
  assert.equal(inverse,1);
  assert.equal(matching(trace,'stream-close').length,3);
  await ctx.dispose();
});

test('cleanup cannot acquire an idle Rust stream after its resource barrier',async()=>{
  const {ctx,trace}=environment();
  await ctx.rustPlugin('fixture.counter');
  const consumer=await ctx.inject(['rustCounter'],c=>()=>{
    assert.throws(()=>c.rustCounter.stream(),/StreamAdmissionClosed/);
  });
  await consumer.dispose();
  assert.equal(matching(trace,'stream-close').length,0);
  await ctx.dispose();
});

test('an old or transferred stream cannot obtain another consumer admission',async()=>{
  const {ctx}=environment();
  await ctx.rustPlugin('fixture.counter');
  let stream;
  const consumer=await ctx.inject(['rustCounter'],c=>{stream=c.rustCounter.stream();});
  const old=stream;
  await ctx.inject(['rustCounter'],async()=>{
    await assert.rejects(stream.next(),/StreamOwnerMismatch/);
  });
  await consumer.restart();
  await assert.rejects(old.next(),/STALE|no longer admitted/);
  assert.deepEqual(await stream.next(),{done:false,value:0});
  await ctx.dispose();
});

test('a reverse callback cannot await its own stream close',async()=>{
  let stream;
  const {ctx}=environment(undefined,async phase=>{
    if(phase==='stream-pull') await assert.rejects(stream.return(),/ReentrantStreamClose/);
  });
  await ctx.rustPlugin('fixture.counter');
  stream=ctx.rustCounter.stream();
  assert.deepEqual(await stream.next(),{done:false,value:0});
  await stream.return();
  await ctx.dispose();
});

test('late JS stream open after cancellation is acquired then returned without pulling',async()=>{
  const entered=Promise.withResolvers(),gate=Promise.withResolvers();
  let returned=0,pulled=0;
  const {ctx}=environment(async()=>{
    entered.resolve();await gate.promise;
    return {async next(){pulled++;return {done:true};},async return(){returned++;return {done:true};}};
  });
  const provider=await ctx.rustPlugin('fixture.counter');
  const call=ctx.rustCounter.consumeStream();
  call.catch(()=>{});
  await entered.promise;
  let closed=false;
  const closing=provider.dispose().then(()=>closed=true);
  await turn();
  assert.equal(closed,false);
  gate.resolve();
  await closing;
  await Promise.allSettled([call]);
  assert.equal(returned,1);
  assert.equal(pulled,0);
  await ctx.dispose();
});

test('orphan iterator cleanup can call a withdrawn Rust dependency through its JS service',async()=>{
  const {Service}=await import('../../packages/compat-cordis/index.js');
  const ctx=new Context({addon}),observations=[];
  const b=ctx.isolate('jsSource').isolate('rustCounter');
  b.provide('jsSource',{read:()=>31,record:()=>null});
  const provider=await b.rustPlugin('fixture.counter');
  let attempts=0;
  class Relay extends Service {
    static inject=['rustCounter'];
    constructor(c){super(c,'jsSource');}
    read(){return this.ctx.rustCounter.read();}
    record(){return null;}
    stream(){
      const current=this.ctx;
      return {
        get next(){throw new Error('invalid next getter');},
        async return(){
          observations.push(current.rustCounter.read());
          if(++attempts===1)throw new Error('first orphan return failed');
          return {done:true};
        },
      };
    }
  }
  const middle=b.isolate('jsSource');
  await middle.plugin(Relay);
  const a=middle.isolate('rustCounter');
  await a.rustPlugin('fixture.counter');
  await assert.rejects(a.rustCounter.takeStream(1),/Invalid JS stream/);
  assert.deepEqual(observations,[31]);
  await provider.dispose();
  assert.deepEqual(observations,[31,31]);
  assert.equal(attempts,2);
  await ctx.dispose();
});

test('another native domain cannot reuse its reverse-call authority for a stream',async()=>{
  const first=environment(),second=environment();
  await first.ctx.rustPlugin('fixture.counter');
  await second.ctx.rustPlugin('fixture.counter');
  const stream=first.ctx.rustCounter.stream();
  second.ctx.jsSource.query=async()=>{
    await assert.rejects(stream.next(),/StreamOwnerMismatch/);
    return 'isolated';
  };
  assert.equal(await second.ctx.rustCounter.request(),'isolated');
  assert.deepEqual(await stream.next(),{done:false,value:0});
  await second.ctx.dispose();
  await first.ctx.dispose();
});


test('a native fault rejects pending stream pulls without reporting successful close',()=>{
  const facade=new URL('../../packages/compat-cordis/index.js',import.meta.url).href;
  const code=`
    import assert from 'node:assert/strict';
    import {Context} from ${JSON.stringify(facade)};
    const ctx=new Context({addon:${JSON.stringify(addon)}});
    const entered=Promise.withResolvers();
    ctx.provide('jsSource',{read:()=>7,record:phase=>{if(phase==='stream-pull')entered.resolve();return null;}});
    await ctx.rustPlugin('fixture.counter');
    const stream=ctx.rustCounter.stream({waitForCancel:true});
    const rejected=assert.rejects(stream.next(),/DomainFaulted/);
    await entered.promise;
    await assert.rejects(ctx.rustCounter.panicPoll(),/DomainFaulted/);
    await rejected;
    await assert.rejects(stream.return(),/DomainFaulted/);
    console.log('stream-fault-cleanup-unconfirmed');
  `;
  const result=spawnSync(process.execPath,['--input-type=module','--eval',code],{encoding:'utf8',timeout:10000});
  assert.ifError(result.error);
  assert.equal(result.status,0,result.stdout+result.stderr);
  assert.match(result.stdout,/stream-fault-cleanup-unconfirmed/);
});
