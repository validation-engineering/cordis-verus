import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { Context, FiberState } from '../../packages/compat-cordis/index.js';
import { selectNativeArtifact } from '../../packages/compat-cordis/native-artifacts.js';
export const scenarios=Object.freeze({
  'native.lifecycle':{batch:20,unit:'mount-setup-cleanup-remove cycle',description:'Rust shared driver through JSON and N-API, including command encoding/decoding; not isolated kernel CPU time'},
  'facade.syncService':{batch:500,unit:'call',description:'Committed JS service lookup and synchronous method call'},
  'facade.asyncService':{batch:100,unit:'call',description:'Committed JS service lookup and awaited resolved-Promise method call'},
  'rust.syncService':{batch:100,unit:'call',description:'JS to Rust JSON DTO synchronous service through the native SDK fixture'},
  'rust.asyncRoundTrip':{batch:10,unit:'call',description:'JS to Rust Future to async JS service and back; no artificial sleep'},
  'rust.pullStream':{batch:2,unit:'item',description:'Full Rust pull stream consumption including open, EOF, reverse JS record callbacks and close amortized per item'},
  'facade.mountDispose':{batch:5,unit:'mount/dispose cycle',description:'Await plugin activation and effect disposal in a retained Context'},
  'facade.settledReadiness':{batch:1,unit:'settled fiber readiness read',description:'Sequential Fiber.await reads of an already settled Harness-profile graph with fixed fanout consumers and eight committed providers; graph construction and final disposal are outside timing'},
  'facade.providerWithdrawal':{batch:1,unit:'provider group withdrawal',description:'Dispose one provider after fixed fanout consumers activate; graph setup and final Context removal are outside timing'},
});
export async function prepareScenario(name,{fixturePath,fanout,streamItems}) {
  if(name==='native.lifecycle') {
    const binding=createRequire(import.meta.url)(selectNativeArtifact().path),driver=new binding.NativeDriver();
    const command=value=>JSON.parse(driver.command(JSON.stringify(value)));
    const finish=()=>{
      for(let rounds=0;rounds<10;rounds++) {
        const actions=command({op:'drive'}).actions;
        if(!actions.length)return;
        for(const action of actions) {
          if(action.kind==='removed')continue;
          assert.ok(['setup','cleanup'].includes(action.kind));
          command({op:'complete',ticket:action.ticket,success:true});
        }
      }
      throw new Error('Native benchmark driver did not settle');
    };
    return {runSync(count){for(let i=0;i<count;i++){const {id}=command({op:'mount'});finish();command({op:'retire',id});finish();}return count;},validate(value,count){assert.equal(value,count);assert.equal(command({op:'snapshot'}).plugins.length,0);},async close(){}};
  }
  if(name==='facade.settledReadiness') {
    const ctx=new Context({profile:'harness'}),fibers=[],names=Array.from({length:8},(_,i)=>'benchReady'+i);
    let setups=0,cleanups=0,providerCleanups=0;
    try {
      for(const [i,name] of names.entries())await ctx.plugin(c=>{c.provide(name,i);return()=>{providerCleanups++;};});
      for(let i=0;i<fanout;i++)fibers.push(await ctx.inject(names,c=>{
        for(const [value,name] of names.entries())assert.equal(c[name],value);
        setups++;
        return()=>{for(const [value,name] of names.entries())assert.equal(c[name],value);cleanups++;};
      }));
      await ctx.settle();
    } catch(error) {await ctx.dispose();throw error;}
    return {unitsPerIteration:fanout,async run(count){
      let reads=0;
      for(let i=0;i<count;i++)for(const fiber of fibers){await fiber.await();reads++;}
      return reads;
    },validate(value,count){
      assert.equal(value,count*fanout);assert.equal(setups,fanout);assert.equal(cleanups,0);assert.equal(providerCleanups,0);
      assert.ok(fibers.every(fiber=>fiber.state===FiberState.ACTIVE));
    },async close(){
      await ctx.dispose();assert.equal(cleanups,fanout);assert.equal(providerCleanups,8);assert.equal(ctx.snapshot().plugins.length,0);
    }};
  }
  if(name==='facade.providerWithdrawal') {
    let ctx,provider,consumers,trace;
    return {iterations:1,async beforeSample(){
      ctx=new Context();trace=[];consumers=[];
      provider=await ctx.plugin(c=>{c.provide('benchValue',7);return()=>trace.push('provider');});
      for(let i=0;i<fanout;i++)consumers.push(await ctx.inject(['benchValue'],c=>()=>{assert.equal(c.benchValue,7);trace.push('consumer');}));
    },async run(){await provider.dispose();return 1;},validate(value){assert.equal(value,1);assert.equal(trace.length,fanout+1);assert.equal(trace.at(-1),'provider');assert.ok(consumers.every(item=>item.state===FiberState.PENDING));},async afterSample(){await ctx.dispose();ctx=null;},async close(){if(ctx)await ctx.dispose();}};
  }
  const rust=name.startsWith('rust.'),ctx=new Context(rust?{addon:fixturePath}:{});
  let consumer,cleaned=0,streamPulls=0,streamCloses=0,lastPulls=0,lastCloses=0;
  try {
    if(rust) {
      ctx.provide('jsSource',{read:()=>7,query:async value=>value,record:phase=>{if(phase==='stream-pull')streamPulls++;if(phase==='stream-close')streamCloses++;return null;}});
      await ctx.rustPlugin('fixture.counter');
      await ctx.inject(['rustCounter'],c=>{consumer=c;});
    } else if(name!=='facade.mountDispose') {
      await ctx.plugin(c=>{c.provide('bench',{sync:value=>value+1,async:async value=>value+1});});
      await ctx.inject(['bench'],c=>{consumer=c;});
    }
  } catch(error) {await ctx.dispose();throw error;}
  const scenario={async close(){await ctx.dispose();}};
  if(name==='facade.syncService')Object.assign(scenario,{runSync(count){let sum=0;for(let i=0;i<count;i++)sum+=consumer.bench.sync(i);return sum;},validate(value,count){assert.equal(value,count*(count+1)/2);}});
  else if(name==='facade.asyncService')Object.assign(scenario,{async run(count){let sum=0;for(let i=0;i<count;i++)sum+=await consumer.bench.async(i);return sum;},validate(value,count){assert.equal(value,count*(count+1)/2);}});
  else if(name==='rust.syncService')Object.assign(scenario,{runSync(count){let sum=0;for(let i=0;i<count;i++)sum+=consumer.rustCounter.read();return sum;},validate(value,count){assert.equal(value,count*7);}});
  else if(name==='rust.asyncRoundTrip')Object.assign(scenario,{async run(count){let sum=0;for(let i=0;i<count;i++)sum+=await consumer.rustCounter.request(i);return sum;},validate(value,count){assert.equal(value,count*(count-1)/2);}});
  else if(name==='rust.pullStream')Object.assign(scenario,{unitsPerIteration:streamItems,beforeSample(){lastPulls=streamPulls;lastCloses=streamCloses;},async run(count){let sum=0;for(let i=0;i<count;i++)for await(const value of consumer.rustCounter.stream({count:streamItems}))sum+=value;return sum;},validate(value,count){assert.equal(value,count*streamItems*(streamItems-1)/2);assert.equal(streamCloses-lastCloses,count);assert.equal(streamPulls-lastPulls,count*(streamItems+1));}});
  else if(name==='facade.mountDispose')Object.assign(scenario,{beforeSample(){cleaned=0;},async run(count){for(let i=0;i<count;i++){const fiber=await ctx.plugin(c=>{c.effect(()=>()=>{cleaned++;});});await fiber.dispose();}return count;},validate(value,count){assert.equal(value,count);assert.equal(cleaned,count);assert.equal(ctx.snapshot().plugins.length,1);}});
  else throw new Error('Unknown benchmark scenario: '+name);
  return scenario;
}
