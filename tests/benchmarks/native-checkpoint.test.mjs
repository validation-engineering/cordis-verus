import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { readFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import { dynamicFixtureInputs } from '../../scripts/benchmark/inputs.mjs';
import { scenarios, prepareScenario } from '../../scripts/benchmark/scenarios.mjs';
import { RECLAIMED_STORAGE_SCHEMA, summarize, validateCheckpoints } from '../../scripts/benchmark/statistics.mjs';

const root=fileURLToPath(new URL('../..',import.meta.url));
const worker=fileURLToPath(new URL('../../scripts/benchmark/worker.mjs',import.meta.url));
const name='rust.checkpointReplace';
const method={samples:2,warmup:1,scale:1,fanout:2,streamItems:1,gc:'natural'};
const fixtures=async()=>dynamicFixtureInputs(root,JSON.parse(await readFile(new URL('../../target/node-compat/build.json',import.meta.url))));

test('native checkpoint scenario declares its two-image inputs and rejects missing artifacts',async()=>{
  assert.equal(scenarios[name].batch,10);assert.equal(scenarios[name].dynamicFixtures,true);
  await assert.rejects(prepareScenario(name,{fanout:2}),/both dynamic fixtures/);
  await assert.rejects(prepareScenario(name,{fanout:2,dynamicFixtures:{v1:{path:'/one',sha256:'same'},v2:{path:'/two',sha256:'same'}}}),/distinct/);
});

test('native checkpoint replacement records bounded live resources and increasing real identity history',async()=>{
  const env={...process.env};for(const key of ['NODE_OPTIONS','NODE_PATH','CORDIS_NATIVE_BINDING'])delete env[key];
  const child=spawnSync(process.execPath,[worker,JSON.stringify({name,method,dynamicFixtures:await fixtures()})],{env,encoding:'utf8',timeout:30000});
  assert.equal(child.status,0,child.stderr);
  const result=JSON.parse(child.stdout),points=result.checkpoints;
  validateCheckpoints(result,method);
  assert.equal(result.cleanupConfirmed,true);assert.equal(result.iterationsPerSample,10);assert.equal(result.unitsPerSample,10);
  assert.equal(result.samplesMs.length,2);assert.equal(result.cpuSamplesMicroseconds.length,2);
  assert.deepEqual(result.statistics,summarize(result.samplesMs,10));
  assert.deepEqual(points.map(point=>point.completedCycles),[0,10,20,30,30]);
  for(const point of points)assert.equal(point.storageSchema,RECLAIMED_STORAGE_SCHEMA);
  for(const point of points.slice(0,-1)) {
    const cycles=point.completedCycles;
    assert.equal(point.storage.registeredPlugins,5);assert.equal(point.storage.liveBindings,3);
    assert.equal(point.storage.liveLeases,3);assert.equal(point.storage.publishedValues,3);
    assert.equal(point.storage.identitySlots,5+2*cycles);
    assert.equal(point.storage.publicationRecords,3+2*cycles);
    assert.equal(point.storage.leaseRecords,3);assert.equal(point.storage.leaseAllocations,3*(cycles+1));
    assert.equal(point.providerSetups,cycles+1);assert.equal(point.providerCleanups,cycles);
    assert.equal(point.consumerSetups,2*(cycles+1));assert.equal(point.consumerCleanups,2*cycles);
    assert.equal(point.native.retainedImageCount,2);assert.equal(point.native.moduleCount,2);
    assert.equal(point.native.checkpoints.tokens,1);assert.ok(point.native.checkpoints.bytes>0);
    assert.equal(point.logical.value,3*cycles);assert.equal(point.logical.version,'v1');
    assert.equal(point.logical.restoredFrom,cycles===0?null:2);
    assert.ok(point.memoryBytes.rss>0);
    if(cycles)assert.notEqual(point.currentFiberId,point.previousFiberId);
  }
  const closed=points.at(-1);
  assert.deepEqual(closed.logical,points.at(-2).logical,'Terminal consumer writes are outside the measured migration result');
  assert.equal(closed.storage.leaseRecords,0);assert.equal(closed.storage.leaseAllocations,93);
  assert.equal(closed.providerCleanups,31);assert.equal(closed.consumerCleanups,62);
  assert.equal(closed.native.checkpoints.tokens,0);assert.equal(closed.native.checkpoints.bytes,0);
  assert.ok(Object.values(closed.native.resources).every(count=>count===0));
  const corruptions=[
    report=>delete report.checkpoints[1].native,
    report=>delete report.checkpoints[1].native.resources.reverseCalls,
    report=>report.checkpoints[1].native.resources.jobs=1,
    report=>report.checkpoints[1].native.resources.retainedJobs=1,
    report=>report.checkpoints[1].native.moduleCount=3,
    report=>report.checkpoints[1].native.retainedImageCount=3,
    report=>report.checkpoints[1].native.retainedImageLimit=0,
    report=>delete report.checkpoints[1].native.checkpoints,
    report=>report.checkpoints[1].native.checkpoints.tokens=2,
    report=>report.checkpoints[1].native.checkpoints.bytes=16777217,
    report=>report.checkpoints.at(-1).native.checkpoints.bytes=1,
    report=>report.checkpoints.at(-1).native.resources.instances=1,
    report=>report.checkpoints[1].logical.value++,
    report=>report.checkpoints[1].logical.version='v2',
    report=>report.checkpoints[1].logical.restoredFrom=1,
    report=>report.checkpoints[0].logical.restoredFrom=2,
    report=>delete report.checkpoints[1].logical,
    report=>report.checkpoints[1].storage.publishedValues=2,
    report=>report.unitsPerSample++,
    report=>delete report.checkpoints[1].storage.leaseAllocations,
    report=>report.checkpoints[1].storage.leaseAllocations--,
    report=>report.checkpoints[1].storage.leaseRecords++,
    report=>report.checkpoints.at(-1).storage.leaseRecords=1,
    report=>delete report.checkpoints[1].storageSchema,
  ];
  for(const mutate of corruptions) {
    const changed=structuredClone(result);mutate(changed);
    assert.throws(()=>validateCheckpoints(changed,method),/checkpoint/i);
  }
});

test('odd native replacement exposes the actual v1-to-v2 schema transition before shutdown',async()=>{
  const scenario=await prepareScenario(name,{dynamicFixtures:await fixtures(),fanout:1});
  try {
    assert.deepEqual(scenario.checkpoint().logical,{value:0,version:'v1',restoredFrom:null});
    const result=await scenario.run(1);scenario.validate(result,1);
    assert.deepEqual(scenario.checkpoint().logical,{value:2,version:'v2',restoredFrom:1});
  } finally {await scenario.close();}
  assert.equal(scenario.checkpoint().native.checkpoints.tokens,0);
});

for(const failure of ['prepare','close'])test('native checkpoint '+failure+' failure preserves its error and still drains the Context',async()=>{
  // Fault injection runs in its own process: images intentionally stay mapped,
  // and each successful benchmark starts with exactly the same two-image budget.
  const source=`
    import assert from 'node:assert/strict';
    import { RegistryService } from './packages/compat-cordis/runtime.js';
    import { RustModuleController } from './packages/compat-loader/rust-module.js';
    import { prepareScenario } from './scripts/benchmark/scenarios.mjs';
    const failure=${JSON.stringify(failure)},dynamicFixtures=JSON.parse(process.argv[1]);
    const sentinel=new Error('Injected '+failure+' failure');
    const inject=RegistryService.prototype.inject,dispose=RustModuleController.prototype.dispose;
    let context,scenario,calls=0;
    RegistryService.prototype.inject=function(...args){
      context=this.ctx;
      if(failure==='prepare'&&++calls===2)throw sentinel;
      return inject.apply(this,args);
    };
    try {
      if(failure==='prepare') {
        await assert.rejects(prepareScenario('rust.checkpointReplace',{dynamicFixtures,fanout:2}),error=>error===sentinel);
      } else {
        scenario=await prepareScenario('rust.checkpointReplace',{dynamicFixtures,fanout:2});
        RustModuleController.prototype.dispose=async()=>{throw sentinel;};
        await assert.rejects(scenario.close(),error=>error instanceof AggregateError&&error.errors.includes(sentinel));
      }
      assert.equal(context.snapshot().plugins.length,0,'Context cleanup still runs');
      const inventory=context.fiber._domain.rust.command({op:'module_info'});
      assert.equal(inventory.checkpoints.tokens,0);assert.equal(inventory.checkpoints.bytes,0);
      for(const module of inventory.modules)assert.ok(Object.values(module.resources).every(count=>count===0));
    } finally {
      RegistryService.prototype.inject=inject;RustModuleController.prototype.dispose=dispose;
      if(context&&!context.fiber._domain.closed)await context.dispose();
    }
  `;
  const env={...process.env};for(const key of ['NODE_OPTIONS','NODE_PATH','CORDIS_NATIVE_BINDING'])delete env[key];
  const child=spawnSync(process.execPath,['--input-type=module','--eval',source,JSON.stringify(await fixtures())],{cwd:root,env,encoding:'utf8',timeout:15000});
  assert.equal(child.status,0,child.stderr);
});
