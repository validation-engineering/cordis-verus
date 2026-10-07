import test from 'node:test';
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {Context,Service,adaptObject,adaptCallback} from '../../packages/compat-cordis/index.js';
import {jsonValue} from '../../packages/compat-cordis/rust-plugin.js';
const addon=fileURLToPath(new URL('../../target/node-compat/interop-fixture.node',import.meta.url));
const turn=()=>new Promise(resolve=>setImmediate(resolve));
function environment(options={}) {
  const ctx=new Context({addon}),trace=[];
  ctx.provide('jsSource',{
    read:()=>7,query:options.query??(async(...args)=>args),object:options.object,callback:options.callback,
    record:(...args)=>{trace.push(args);return options.record?.(...args)??null;},
  });
  return {ctx,trace};
}
const closes=trace=>trace.filter(item=>item[0]==='object-close');

test('Rust opaque handles expose a fixed interface, keep typed state and reject JSON smuggling',async()=>{
  const {ctx,trace}=environment();
  await ctx.rustPlugin('fixture.counter');
  const handle=ctx.rustCounter.object();
  assert.equal(handle.typeName,'fixture.CounterObject');
  assert.equal(handle.ownership,'owned');
  assert.equal(await handle.call('read'),7);
  assert.equal(await handle.call('add',5),12);
  await assert.rejects(handle.call('undeclared'),/UndeclaredObjectMethod/);
  assert.throws(()=>jsonValue(handle),/Opaque/);
  await handle.close();
  await handle.close();
  assert.equal(closes(trace).length,1);
  await assert.rejects(handle.call('read'),/STALE|no longer admitted/);
  let conversions=0;
  for (const method of [Symbol('method'), {toString(){conversions++;throw new Error('must not convert stale arguments');}}]) {
    await assert.rejects(handle.call(method),error=>error.code==='STALE_EPISODE' && error.details.operation==='Rust object:call');
  }
  assert.equal(conversions,0);
  await ctx.dispose();
});

test('nested effect inverses use their old object before its automatic release',async()=>{
  const {ctx,trace}=environment();
  await ctx.rustPlugin('fixture.counter');
  const consumer=await ctx.inject(['rustCounter'],c=>c.effect(async()=>{
    const handle=c.rustCounter.object();
    await handle.call('add',2);
    return async()=>{trace.push(['inverse',await handle.call('read')]);};
  }));
  await consumer.dispose();
  assert.deepEqual(trace,[['inverse',9],['object-close','object',1]]);
  await ctx.dispose();
});

test('failed user inverse preserves objects and provider leases for cleanup retry',async()=>{
  const {ctx,trace}=environment();
  const provider=await ctx.rustPlugin('fixture.counter');
  let attempt=0;
  const consumer=await ctx.inject(['rustCounter'],c=>{
    const object=c.rustCounter.object();
    return async()=>{trace.push(['inverse',await object.call('read')]);if(++attempt===1)throw new Error('retry inverse');};
  });
  await assert.rejects(provider.dispose(),/cleanup|Native/i);
  assert.equal(closes(trace).length,0);
  assert.equal(trace.some(item=>item[0]==='cleanup'),false);
  await consumer.retryCleanup();
  await provider.dispose();
  assert.deepEqual(trace,[['inverse',7],['inverse',7],['object-close','object',1],['cleanup',7]]);
  await ctx.dispose();
});

test('a Rust provider instance survives its own failed JS inverse before teardown',async()=>{
  const {ctx,trace}=environment();
  const provider=await ctx.rustPlugin('fixture.counter');
  const object=provider.ctx.rustCounter.object();
  let count=0;
  provider.ctx.effect(()=>async()=>{
    trace.push(['provider-inverse',await object.call('read')]);
    if(++count===1)throw new Error('provider inverse failed');
  });
  await assert.rejects(provider.dispose(),/cleanup|Native/i);
  assert.equal(closes(trace).length,0);
  assert.equal(trace.some(item=>item[0]==='cleanup'),false);
  await provider.retryCleanup();
  assert.deepEqual(trace,[['provider-inverse',7],['provider-inverse',7],['object-close','object',1],['cleanup',7]]);
  await ctx.dispose();
});

test('object release is LIFO and a failed close retains older acquisitions',async()=>{
  const {ctx,trace}=environment();
  await ctx.rustPlugin('fixture.counter');
  const consumer=await ctx.inject(['rustCounter'],c=>{
    c.rustCounter.object({label:'first'});
    c.rustCounter.object({label:'second',failCloseOnce:true});
  });
  await assert.rejects(consumer.dispose(),/cleanup|Native/i);
  assert.deepEqual(closes(trace),[['object-close','second',1]]);
  await consumer.retryCleanup();
  assert.deepEqual(closes(trace),[['object-close','second',1],['object-close','second',2],['object-close','first',1]]);
  await ctx.dispose();
});

test('borrowed Rust object release never calls its explicit destructor',async()=>{
  const {ctx,trace}=environment();
  await ctx.rustPlugin('fixture.counter');
  const handle=ctx.rustCounter.object({borrowed:true});
  assert.equal(await handle.call('read'),7);
  await handle.close();
  assert.deepEqual(closes(trace),[]);
  assert.equal(ctx.rustCounter.read(),7);
  await ctx.dispose();
});

test('close cancels and joins all object calls and rejects new method admission',async()=>{
  const entered=Promise.withResolvers(),gate=Promise.withResolvers();
  const {ctx,trace}=environment({query:async()=>{entered.resolve();await gate.promise;return 'landed';}});
  await ctx.rustPlugin('fixture.counter');
  const object=ctx.rustCounter.object();
  const call=object.call('query');
  const cancelled=object.call('waitCancelled');
  await entered.promise;
  const a=object.close(),b=object.close();
  assert.equal(a,b);
  await assert.rejects(object.call('read'),/STALE|no longer admitted/);
  await turn();
  assert.equal(await cancelled,'cancelled');
  assert.deepEqual(closes(trace),[]);
  gate.resolve();
  assert.equal(await call,'landed');
  await a;
  assert.equal(closes(trace).length,1);
  await ctx.dispose();
});

test('cleanup cannot acquire new objects, while a restarted or transferred old handle is rejected',async()=>{
  const {ctx}=environment();
  await ctx.rustPlugin('fixture.counter');
  let object;
  const consumer=await ctx.inject(['rustCounter'],c=>{
    object=c.rustCounter.object();
    return ()=>assert.throws(()=>c.rustCounter.object(),/ObjectAdmissionClosed/);
  });
  const old=object;
  await ctx.inject(['rustCounter'],async()=>{await assert.rejects(object.call('read'),/ObjectOwnerMismatch/);});
  await consumer.restart();
  await assert.rejects(old.call('read'),/STALE|no longer admitted/);
  assert.equal(await object.call('read'),7);
  await ctx.dispose();
});

test('Rust callback adapters invoke JavaScript and close as ordinary owned objects',async()=>{
  const {ctx,trace}=environment({query:async(a,b)=>a+b});
  await ctx.rustPlugin('fixture.counter');
  const callback=ctx.rustCounter.callback({label:'callback'});
  assert.deepEqual(callback.methods,['call']);
  assert.equal(await callback.invoke(20,22),42);
  await callback.close();
  assert.deepEqual(closes(trace),[['object-close','callback',1]]);
  await ctx.dispose();
});

test('nested reverse calls cannot wait for an ancestor object close',async()=>{
  let first,second;
  const {ctx}=environment({query:async which=>{
    if(which==='first')return second.invoke('second');
    await assert.rejects(first.close(),/ReentrantObjectClose/);
    return 'no deadlock';
  }});
  await ctx.rustPlugin('fixture.counter');
  first=ctx.rustCounter.callback();
  second=ctx.rustCounter.callback();
  assert.equal(await first.invoke('first'),'no deadlock');
  await ctx.dispose();
});

test('Rust consumes a borrowed JS object without guessing a dispose method',async()=>{
  let disposed=0;
  const target={value:42,read(){return this.value;},dispose(){disposed++;}};
  const {ctx}=environment({object:()=>adaptObject(target,{typeName:'Borrowed',methods:['read'],ownership:'borrowed'})});
  await ctx.rustPlugin('fixture.counter');
  assert.equal(await ctx.rustCounter.useObject(),42);
  assert.equal(disposed,0);
  assert.equal(await ctx.rustCounter.useObject('read',[],true),42);
  await ctx.dispose();
  assert.equal(disposed,0);
});

test('Rust callback capability is explicit and action-scoped with owned cleanup',async()=>{
  let disposed=0;
  const {ctx}=environment({callback:()=>adaptCallback((value)=>({answer:value*2}),{ownership:'owned',dispose:()=>{disposed++;}})});
  await ctx.rustPlugin('fixture.counter');
  assert.deepEqual(await ctx.rustCounter.useCallback(21),{answer:42});
  assert.equal(disposed,1);
  await ctx.dispose();
  assert.equal(disposed,1);
});

test('foreign object journal waits for actual disposal before completing its Rust action',async()=>{
  const entered=Promise.withResolvers(),gate=Promise.withResolvers();
  const {ctx}=environment({object:()=>adaptObject({read:()=>7},{typeName:'Owned',methods:['read'],ownership:'owned',dispose:async()=>{entered.resolve();await gate.promise;}})});
  await ctx.rustPlugin('fixture.counter');
  let landed=false;
  const call=ctx.rustCounter.takeObject().then(value=>{landed=true;return value;});
  await entered.promise;
  assert.equal(landed,false);
  gate.resolve();
  await call;
  assert.equal(landed,true);
  await ctx.dispose();
});

test('dropped object method Future still lands before the foreign object is disposed',async()=>{
  const entered=Promise.withResolvers(),gate=Promise.withResolvers();
  let disposed=0;
  const {ctx}=environment({object:()=>adaptObject({async query(){entered.resolve();await gate.promise;return 'real result';}},
    {typeName:'InFlight',methods:['query'],ownership:'owned',dispose:()=>{disposed++;}})});
  const provider=await ctx.rustPlugin('fixture.counter');
  const call=ctx.rustCounter.dropObjectCall();
  await entered.promise;
  let closed=false;
  const closing=provider.dispose().then(()=>closed=true);
  await turn();
  assert.equal(disposed,0);
  assert.equal(closed,false);
  gate.resolve();
  await call;
  await closing;
  assert.equal(disposed,1);
  await ctx.dispose();
});

test('foreign object cleanup stops on failure and retries in acquisition LIFO order',async()=>{
  const order=[];let attempts=0;
  const {ctx}=environment({object:name=>adaptObject({read:()=>name},{typeName:'Ordered',methods:['read'],ownership:'owned',dispose:()=>{
    order.push(name);if(name==='second' && ++attempts===1)throw new Error('second close failed');
  }})});
  const provider=await ctx.rustPlugin('fixture.counter');
  await assert.rejects(ctx.rustCounter.twoObjects(),/second close failed/);
  assert.deepEqual(order,['second']);
  await provider.dispose();
  assert.deepEqual(order,['second','second','first']);
  await ctx.dispose();
});

test('late object acquisition after cancel is owned and disposed without a business call',async()=>{
  const entered=Promise.withResolvers(),gate=Promise.withResolvers();
  let called=0,disposed=0;
  const {ctx}=environment({object:async()=>{
    entered.resolve();await gate.promise;
    return adaptObject({read(){called++;return 1;}},{typeName:'Late',methods:['read'],ownership:'owned',dispose:()=>{disposed++;}});
  }});
  const provider=await ctx.rustPlugin('fixture.counter');
  const call=ctx.rustCounter.useObject();call.catch(()=>{});
  await entered.promise;
  const closing=provider.dispose();
  await turn();
  gate.resolve();
  await closing;
  await assert.rejects(call,/Cancelled/);
  assert.equal(called,0);
  assert.equal(disposed,1);
  await ctx.dispose();
});

test('foreign object orphan cleanup can use the withdrawn Rust dependency chain',async()=>{
  const ctx=new Context({addon}),seen=[];
  const b=ctx.isolate('jsSource').isolate('rustCounter');
  b.provide('jsSource',{read:()=>37,record:()=>null});
  const provider=await b.rustPlugin('fixture.counter');
  let attempts=0;
  class Relay extends Service {
    static inject=['rustCounter'];
    constructor(c){super(c,'jsSource');}
    read(){return this.ctx.rustCounter.read();}
    record(){return null;}
    object(){
      const current=this.ctx;
      return adaptObject({get read(){throw new Error('bad method getter');}},
        {typeName:'Orphan',methods:['read'],ownership:'owned',dispose:()=>{
          seen.push(current.rustCounter.read());if(++attempts===1)throw new Error('first disposal failed');
        }});
    }
  }
  const middle=b.isolate('jsSource');await middle.plugin(Relay);
  const a=middle.isolate('rustCounter');await a.rustPlugin('fixture.counter');
  await assert.rejects(a.rustCounter.useObject(),/Invalid JS object/);
  assert.deepEqual(seen,[37]);
  await provider.dispose();
  assert.deepEqual(seen,[37,37]);
  await ctx.dispose();
});
