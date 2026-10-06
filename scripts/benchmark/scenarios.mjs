import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { Context, FiberState } from '../../packages/compat-cordis/index.js';
import { loadRustModule } from '../../packages/compat-loader/rust-module.js';
import { selectNativeArtifact } from '../../packages/compat-cordis/native-artifacts.js';
export const scenarios=Object.freeze({
  'native.lifecycle':{batch:20,unit:'mount-setup-cleanup-remove cycle',description:'Rust shared driver through JSON and N-API, including command encoding/decoding; not isolated kernel CPU time'},
  'facade.syncService':{batch:500,unit:'call',description:'Committed JS service lookup and synchronous method call'},
  'facade.asyncService':{batch:100,unit:'call',description:'Committed JS service lookup and awaited resolved-Promise method call'},
  'rust.syncService':{batch:100,unit:'call',description:'JS to Rust JSON DTO synchronous service through the native SDK fixture'},
  'rust.asyncRoundTrip':{batch:10,unit:'call',description:'JS to Rust Future to async JS service and back; no artificial sleep'},
  'rust.checkpointReplace':{batch:10,unit:'native checkpoint replacement cycle',dynamicFixtures:true,description:'Alternating two retained cdylib images with logical state migration, real consumer cleanup writes and per-batch native/graph accounting'},
  'rust.pullStream':{batch:2,unit:'item',description:'Full Rust pull stream consumption including open, EOF, reverse JS record callbacks and close amortized per item'},
  'facade.residentRestart':{batch:10,unit:'provider restart cycle',description:'Repeated provider activation and committed consumer rebinding in one retained Context, retaining the provider identity'},
  'facade.residentReplace':{batch:10,unit:'provider replacement cycle',description:'Fresh provider mount/dispose and committed consumer rebinding in one retained Context; records identity/publication/lease history growth'},
  'facade.mountDispose':{batch:5,unit:'mount/dispose cycle',description:'Await plugin activation and effect disposal in a retained Context'},
  'facade.settledReadiness':{batch:1,unit:'settled fiber readiness read',description:'Sequential Fiber.await reads of an already settled Harness-profile graph with fixed fanout consumers and eight committed providers; graph construction and final disposal are outside timing'},
  'facade.providerWithdrawal':{batch:1,unit:'provider group withdrawal',description:'Dispose one provider after fixed fanout consumers activate; graph setup and final Context removal are outside timing'},
});
export async function prepareScenario(name,{fixturePath,dynamicFixtures,fanout,streamItems}) {
  if(name==='rust.checkpointReplace')return prepareCheckpointReplacement(dynamicFixtures,fanout);
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
  if(name==='facade.residentRestart'||name==='facade.residentReplace') {
    const ctx=new Context({profile:'harness'}),consumers=[];
    let provider,version=0,cycles=0,providerCleanups=0,consumerCleanups=0;
    const setup=c=>{const current=++version;c.provide('residentValue',current);return()=>{providerCleanups++;};};
    try {
      provider=await ctx.plugin(setup);
      for(let i=0;i<fanout;i++)consumers.push(await ctx.inject(['residentValue'],c=>{
        const committed=c.residentValue;
        return()=>{assert.equal(c.residentValue,committed);consumerCleanups++;};
      }));
      await ctx.settle();
    } catch(error) {await ctx.dispose();throw error;}
    return {async run(count){
      for(let i=0;i<count;i++) {
        if(name==='facade.residentRestart')await provider.restart();
        else {await provider.dispose();provider=await ctx.plugin(setup);}
        await ctx.settle();cycles++;
      }
      return count;
    },validate(value,count){
      assert.equal(value,count);assert.equal(version,cycles+1);
      assert.equal(providerCleanups,cycles);assert.equal(consumerCleanups,cycles*fanout);
      assert.ok(consumers.every(fiber=>fiber.state===FiberState.ACTIVE));
      const stats=ctx.snapshot().storage;
      assert.equal(stats.registeredPlugins,fanout+2);assert.equal(stats.liveBindings,fanout);
      assert.equal(stats.liveLeases,fanout);assert.equal(stats.pendingActions,0);
    },checkpoint(){return {completedCycles:cycles,storage:ctx.snapshot().storage};},async close(){
      await ctx.dispose();
      assert.equal(providerCleanups,cycles+1);assert.equal(consumerCleanups,(cycles+1)*fanout);
      const stats=ctx.snapshot().storage;
      for(const key of ['registeredPlugins','liveBindings','liveLeases','publishedValues','pendingActions'])assert.equal(stats[key],0,key);
    }};
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


async function prepareCheckpointReplacement(dynamicFixtures,fanout) {
  assert.ok(dynamicFixtures?.v1?.path&&dynamicFixtures?.v2?.path,'Native checkpoint benchmark requires both dynamic fixtures');
  assert.notEqual(dynamicFixtures.v1.sha256,dynamicFixtures.v2.sha256,'Native checkpoint fixtures must be distinct');
  assert.ok(Number.isSafeInteger(fanout)&&fanout>0,'Native checkpoint fanout must be positive');
  const ctx=new Context({profile:'harness'}),driver=ctx.fiber._domain.driver,host=ctx.fiber._domain.rust,consumers=[];
  const resourceKeys=['instances','jobs','retainedInstances','retainedJobs','reverseCalls','retainedReverseCalls','streams','objects','retainedStreams','retainedObjects'];
  let controller,cycles=0,providerSetups=0,providerCleanups=0,consumerSetups=0,consumerCleanups=0;
  let firstHandle,currentFiberId,previousFiberId=null,logical,closing=false,closed=false,aborting=false;
  const expectedLogical=()=>({value:cycles*(fanout+1),version:cycles%2?'v2':'v1',restoredFrom:cycles===0?null:cycles%2?1:2});
  const nativeSnapshot=()=>{
    const info=host.command({op:'module_info'}),resources=Object.fromEntries(resourceKeys.map(key=>[key,0]));
    assert.equal(info.modules.length,2);
    for(const module of info.modules) {
      assert.deepEqual(Object.keys(module.resources).sort(),[...resourceKeys].sort());
      for(const key of resourceKeys) {assert.ok(Number.isSafeInteger(module.resources[key])&&module.resources[key]>=0);resources[key]+=module.resources[key];}
    }
    return {retainedImageCount:info.retainedImageCount,retainedImageLimit:info.retainedImageLimit,moduleCount:info.modules.length,resources,checkpoints:{...info.checkpoints}};
  };
  const checkNative=(expectClosed=closed)=>{
    const native=nativeSnapshot();
    assert.equal(native.retainedImageCount,2);assert.equal(native.retainedImageLimit,128);
    for(const key of resourceKeys)assert.equal(native.resources[key],!expectClosed&&key==='instances'?1:0,key);
    assert.equal(native.checkpoints.tokens,expectClosed?0:1);assert.equal(native.checkpoints.tokenLimit,64);assert.equal(native.checkpoints.byteLimit,16*1024*1024);
    assert.ok(native.checkpoints.bytes>=0&&native.checkpoints.bytes<=native.checkpoints.byteLimit);
    if(expectClosed)assert.equal(native.checkpoints.bytes,0);
    return native;
  };
  try {
    // Image loading is setup, outside measurement. Subsequent cycles replace
    // instances only, so image retention cannot masquerade as a resource leak.
    host.loadModule(dynamicFixtures.v1);host.loadModule(dynamicFixtures.v2);
    ctx.provide('jsHost',{record(event){
      if(event.phase==='checkpoint-setup')providerSetups++;
      else if(event.phase==='checkpoint-cleanup') {
        providerCleanups++;
        if(!aborting) {
          assert.equal(consumerCleanups,providerCleanups*fanout,'Consumers really finish before provider cleanup');
          assert.equal(event.value,closing?cycles*(fanout+1)+fanout:(cycles+1)*(fanout+1),"Capture includes the consumers' final writes");
        }
      } else assert.fail('Unexpected checkpoint fixture event');
      return null;
    }});
    controller=await loadRustModule(ctx,{...dynamicFixtures.v1,plugins:[{id:'counter',factory:'native-checkpoint',state:'migrate'}]});
    firstHandle=ctx.nativeCheckpoint;
    currentFiberId=controller.snapshot().entries[0].fiberId;
    for(let i=0;i<fanout;i++)consumers.push(await ctx.inject(['nativeCheckpoint'],consumer=>{
      consumerSetups++;
      const committedVersion=consumer.nativeCheckpoint.read().version;
      return()=>{assert.equal(consumer.nativeCheckpoint.read().version,committedVersion);consumer.nativeCheckpoint.mutate(1);consumerCleanups++;};
    }));
    await ctx.settle();logical=ctx.nativeCheckpoint.read();assert.deepEqual(logical,expectedLogical());checkNative();
  } catch(error) {
    aborting=true;closing=true;
    try {await ctx.dispose();} catch(cleanup) {throw new AggregateError([error,cleanup],'Native checkpoint preparation and cleanup failed');}
    throw error;
  }
  return {
    async run(count) {
      assert.equal(closed,false);
      try {for(let i=0;i<count;i++) {
        const oldHandle=ctx.nativeCheckpoint,oldFiber=currentFiberId;
        oldHandle.mutate(1);
        await controller.reload(dynamicFixtures[cycles%2?'v1':'v2']);
        await ctx.settle();cycles++;
        assert.equal(ctx.fiber._domain.driver,driver);
        currentFiberId=controller.snapshot().entries[0].fiberId;previousFiberId=oldFiber;
        assert.notEqual(currentFiberId,oldFiber,'Replacement allocates a fresh graph identity');
        assert.throws(()=>oldHandle.read(),/STALE|no longer admitted/);
        logical=ctx.nativeCheckpoint.read();assert.deepEqual(logical,expectedLogical());
        assert.equal(providerSetups,cycles+1);assert.equal(providerCleanups,cycles);
        assert.equal(consumerSetups,(cycles+1)*fanout);assert.equal(consumerCleanups,cycles*fanout);
        assert.ok(consumers.every(fiber=>fiber.state===FiberState.ACTIVE));
      }} catch(error) {aborting=true;throw error;}
      return count;
    },
    validate(value,count) {
      assert.equal(value,count);assert.equal(ctx.fiber._domain.driver,driver);
      assert.deepEqual(logical,expectedLogical());assert.throws(()=>firstHandle.read(),/STALE|no longer admitted/);
      checkNative();
      const storage=ctx.snapshot().storage;
      assert.equal(storage.registeredPlugins,fanout+3);assert.equal(storage.liveBindings,fanout+1);
      assert.equal(storage.liveLeases,fanout+1);assert.equal(storage.publishedValues,3);assert.equal(storage.pendingActions,0);
    },
    checkpoint() {
      return {completedCycles:cycles,storage:ctx.snapshot().storage,native:checkNative(),logical:{...logical},currentFiberId,previousFiberId,providerSetups,providerCleanups,consumerSetups,consumerCleanups};
    },
    async close() {
      if(closed)return;
      // Preserve the measured state. Terminal retirement adds another fanout
      // cleanup writes, but there is no next generation to migrate them into.
      closing=true;
      const failures=[];
      try {await controller.dispose();} catch(error) {aborting=true;failures.push(error);}
      try {await ctx.dispose();} catch(error) {aborting=true;failures.push(error);}
      if(failures.length)throw new AggregateError(failures,'Native checkpoint benchmark cleanup failed');
      if(!aborting) {assert.equal(providerCleanups,cycles+1);assert.equal(consumerCleanups,(cycles+1)*fanout);}
      assert.throws(()=>firstHandle.read(),/STALE|no longer admitted/);
      for(const key of ['registeredPlugins','liveBindings','liveLeases','publishedValues','pendingActions'])assert.equal(ctx.snapshot().storage[key],0,key);
      checkNative(true);closed=true;
    },
  };
}
