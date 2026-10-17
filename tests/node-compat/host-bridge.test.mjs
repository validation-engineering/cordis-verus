import test from 'node:test';
import assert from 'node:assert/strict';
import {createRequire} from 'node:module';
import {HostBridge} from '../../packages/compat-cordis/host-bridge.js';
import {Context} from '../../packages/compat-cordis/index.js';
const native=createRequire(import.meta.url)('../../packages/compat-cordis/native/cordis.node');
const command=(driver,request)=>JSON.parse(driver.command(JSON.stringify(request)));
const make=()=>{const driver=new native.NativeDriver();return {driver,host:new HostBridge(driver)};};
const mount=(driver,host)=>{const {id}=command(driver,{op:'mount',dependencies:[],provisions:[]});const fiber={id};host.bind(id,fiber);return fiber;};

test('actual Node weak references recover exact primitive and opaque object identities',()=>{
  const {driver,host}=make();let observed=0;
  const object=new Proxy({}, {get(){observed++;throw new Error('must not inspect payload');}});
  const values=[undefined,null,Symbol('service'),12345678901234567890n,object,()=>42];
  for(const value of values){const box=host.create(value);assert.strictEqual(host.get(box.id),value);host.delete(box.id);assert.equal(host.get(box.id),undefined);}
  assert.equal(observed,0);driver.validateHostSnapshot();
});

test('host mode rejects unbound numeric writes and cross-domain object capabilities',()=>{
  const left=make(),right=make();const a=left.host.create({name:'left'}),b=right.host.create({name:'right'});
  assert.equal(a.id,b.id);assert.notStrictEqual(a,b);
  const fiber=mount(left.driver,left.host);
  const action=command(left.driver,{op:'drive'}).actions[0];
  const publish={op:'publish',id:fiber.id,generation:action.ticket.generation,key:'7',realm:'2',value:b.id};
  assert.throws(()=>left.driver.command(JSON.stringify(publish)),/HostBridgeRequired/);
  assert.throws(()=>left.driver.objectCommand(JSON.stringify(publish),b),/Domain/);
  assert.deepEqual(left.host.get(a.id),{name:'left'});
});

test('real action claims reject a different Fiber, repeated dispatch and early recipe release',()=>{
  const {driver,host}=make();const fiber=mount(driver,host);const other=mount(driver,host);
  const actions=command(driver,{op:'drive'}).actions;
  const ticket=actions.find(a=>a.id===fiber.id).ticket;
  assert.throws(()=>host.begin(ticket,other,{}),/Fiber mismatch/);
  const recipe={callback:()=>17,config:{mode:'A'}};
  const call=host.begin(ticket,fiber,recipe);
  assert.strictEqual(host.recipe(call),recipe);assert(Object.isFrozen(recipe));
  assert.throws(()=>host.begin(ticket,fiber,{}),/Busy/);
  assert.throws(()=>host.unbind(fiber.id),/Retained/);
  const box=driver.actionRecipe(call);
  assert.throws(()=>host.delete(box.id),/Retained/);
  host.complete(call,true);
  assert.equal(host.get(box.id),undefined);
  assert.throws(()=>host.complete(call,true),/Stale/);
  assert.throws(()=>host.begin(ticket,fiber,{}),/Stale/);
  driver.validateHostSnapshot();
});

test('new callback revision is independent of an already completed invocation',()=>{
  const {driver,host}=make();const fiber=mount(driver,host);
  let action=command(driver,{op:'drive'}).actions[0];
  const first=host.begin(action.ticket,fiber,{callback:()=> 'A',config:{version:1}});
  assert.equal(host.recipe(first).callback(),'A');host.complete(first,true);
  command(driver,{op:'restart',id:fiber.id});
  action=command(driver,{op:'drive'}).actions.find(a=>a.kind==='cleanup');
  const cleanup=host.begin(action.ticket,fiber,{kind:'cleanup'});host.complete(cleanup,true);
  action=command(driver,{op:'drive'}).actions.find(a=>a.kind==='setup');
  const next=host.begin(action.ticket,fiber,{callback:()=> 'B',config:{version:2}});
  assert.throws(()=>host.complete(first,true),/Stale/);
  assert.equal(host.recipe(next).callback(),'B');assert.equal(host.recipe(next).config.version,2);
  host.complete(next,true);driver.validateHostSnapshot();
});

test('withdrawal and failed cleanup retain the actual JS object through retry',async()=>{
  const ctx=new Context();let attempts=0;const seen=[];
  const provider=ctx.plugin(c=>{c.provide('service',{version:1});});await provider;
  const consumer=ctx.plugin({inject:['service'],apply(c){
    c.effect(()=>()=>{seen.push(c.service.version);if(++attempts===1)throw new Error('retry me');});
  }});await consumer;
  provider.ctx.service={version:2};
  await assert.rejects(consumer.dispose(),/retry me|Cleanup/i);
  assert.equal(provider.state,2);assert.deepEqual(seen,[2]);
  await consumer.retryCleanup();assert.deepEqual(seen,[2,2]);
  await provider.dispose();await ctx.dispose();
});

test('a yielded setup keeps its captured callback while a later restart chooses the new revision',async()=>{
  const ctx=new Context();const started=Promise.withResolvers(),finish=Promise.withResolvers();const seen=[];
  const fiber=ctx.plugin(async(c,config)=>{seen.push(`A:${config.version}`);started.resolve();await finish.promise;return()=>seen.push('undo A');},{version:1});
  await started.promise;
  fiber.runtime.callback=(_c,config)=>{seen.push(`B:${config.version}`);return()=>seen.push('undo B');};
  finish.resolve();await fiber;await fiber.restart();
  assert.deepEqual(seen,['A:1','undo A','B:1']);
  await ctx.dispose();assert.deepEqual(seen,['A:1','undo A','B:1','undo B']);
});
