import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { LEGACY_STORAGE_SCHEMA,RECLAIMED_STORAGE_SCHEMA,SCHEMA,checkpointStorage,compareReports,digest,summarize,validateReport } from '../../scripts/benchmark/statistics.mjs';
import { parseBaseline,parseOptions } from '../../scripts/benchmark.mjs';
function fixture(samples=[1,2,3,4,5]) {
  const sourceHashes={'runtime.js':digest('source')};
  return {schema:SCHEMA,status:'passed',measurementStatus:'passed',checkedAt:'time does not affect method',
    inputs:{sourceHashes,sourceDigest:digest(sourceHashes),harnessDigest:digest('harness'),nativeArtifactSha256:digest('native'),nativeManifestSha256:digest('manifest'),buildReportSha256:digest('build'),sdkFixtureSha256:digest('sdk')},
    environment:{platform:'darwin',architecture:'arm64',node:'v22.22.0',nodeApi:'10',driverAbi:1,cpuModel:'test CPU'},
    method:{samples:samples.length,warmup:1,scenarios:['example'],gc:'before-and-after'},
    results:[{name:'example',unit:'call',unitsPerSample:10,samplesMs:samples,statistics:summarize(samples,10),cleanupConfirmed:true}]};
}
test('nearest-rank percentiles and throughput use all raw batch samples',()=>{
  const result=summarize([5,1,3,2,4],10);
  assert.deepEqual(result.nanosecondsPerUnit,{min:100000,p50:300000,p95:500000,p99:500000,max:500000,mean:300000});
  assert.equal(result.totalUnits,50);assert.equal(result.unitsPerSecond,50*1000/15);
  assert.equal(summarize(Array.from({length:100},(_,i)=>i+1),1).nanosecondsPerUnit.p95,95000000);
});
test('statistics reject zero, negative, nonfinite samples and invalid counts',()=>{
  for(const values of [[],[0],[-1],[NaN],[Infinity],['1']])assert.throws(()=>summarize(values,1),/Invalid benchmark/);
  for(const count of [0,-1,1.5,NaN])assert.throws(()=>summarize([1],count),/Invalid benchmark/);
});
test('explicit threshold separates a measured regression from a passing comparison',()=>{
  const baseline=fixture(),candidate=fixture([2,4,6,8,10]);
  assert.equal(compareReports(candidate,baseline,{threshold:.2}).status,'performance-regression');
  assert.equal(compareReports(candidate,baseline,{threshold:1}).status,'passed');
  assert.equal(compareReports(candidate,baseline,{threshold:.2}).comparisons[0].ratio,2);
  assert.throws(()=>compareReports(candidate,baseline),/explicit/);
});
test('baseline rejects changed source unless caller pins that exact prior source digest',()=>{
  const baseline=fixture(),candidate=fixture();
  candidate.inputs.sourceHashes['runtime.js']=digest('new source');candidate.inputs.sourceDigest=digest(candidate.inputs.sourceHashes);
  assert.throws(()=>compareReports(candidate,baseline,{threshold:.2}),/Stale baseline: source/);
  assert.throws(()=>compareReports(candidate,baseline,{threshold:.2,baselineSource:digest('wrong')}),/explicit baseline/);
  assert.equal(compareReports(candidate,baseline,{threshold:.2,baselineSource:baseline.inputs.sourceDigest}).crossSource,true);
});
test('source override cannot bypass changed environment or benchmark methodology',()=>{
  const baseline=fixture();
  for(const mutate of [r=>r.environment.node='v24.0.0',r=>r.environment.cpuModel='other',r=>r.method.gc='natural',r=>r.inputs.harnessDigest=digest('new harness')]){
    const candidate=fixture();mutate(candidate);
    assert.throws(()=>compareReports(candidate,baseline,{threshold:.2,baselineSource:baseline.inputs.sourceDigest}),/baseline:|baseline method/);
  }
});
test('timestamps and manifest provenance re-creation do not change source/method compatibility',()=>{
  const baseline=fixture(),candidate=fixture();candidate.checkedAt='new time';candidate.inputs.nativeManifestSha256=digest('new timestamp');candidate.inputs.buildReportSha256=digest('new build path');
  assert.equal(compareReports(candidate,baseline,{threshold:0}).status,'passed');
});
test('failed, incomplete, changed raw data and promoted regression baselines are rejected',()=>{
  for(const mutate of [r=>r.status='measurement-failed',r=>r.measurementStatus='failed',r=>r.results.pop(),r=>r.results[0].cleanupConfirmed=false,r=>delete r.inputs.sdkFixtureSha256,r=>delete r.environment,r=>r.results[0].samplesMs[0]=9,r=>r.inputs.sourceHashes['runtime.js']=digest('tampered'),r=>r.results.push(r.results[0])]){
    const baseline=fixture();mutate(baseline);assert.throws(()=>validateReport(baseline));
  }
  const baseline=fixture();baseline.status='performance-regression';
  assert.throws(()=>compareReports(fixture(),baseline,{threshold:.2}),/cannot be promoted/);
});
test('CLI requires explicit comparison policy and protects baseline output',()=>{
  assert.equal(parseOptions(['--samples','10','--warmup','0']).samples,10);
  assert.throws(()=>parseOptions(['--baseline','previous.json']),/explicit/);
  for(const value of ['', '   '])assert.throws(()=>parseOptions(['--baseline',value]),/nonempty path/);
  assert.throws(()=>parseOptions(['--baseline','same.json','--output','same.json','--max-regression','.2']),/overwrite/);
  for(const args of [['--samples','1'],['--scale','0'],['--scenario','unknown'],['--metric','max'],['--baseline-source','foo']])assert.throws(()=>parseOptions(args));
});

test('an explicitly supplied falsy JSON baseline is rejected instead of ignored',()=>{
  for(const value of ['null','false','0','""','[]','{}'])assert.throws(()=>parseBaseline(value),/complete successful measurement/);
  assert.equal(parseBaseline(JSON.stringify(fixture())).status,'passed');
});


test('native checkpoint reports require two distinct versioned fixture hashes',()=>{
  for(const dynamic of [undefined,null,{}, {v1:digest('v1')}, {v1:digest('same'),v2:digest('same')}, {v1:digest('v1'),v2:'stale'}, {v1:digest('v1'),v2:digest('v2'),fail:digest('fail')}]) {
    const report=fixture();
    report.method.scenarios=['rust.checkpointReplace'];report.results[0].name='rust.checkpointReplace';
    if(dynamic!==undefined)report.inputs.dynamicFixtureSha256=dynamic;
    assert.throws(()=>validateReport(report),/dynamic fixture evidence/);
  }
  // Existing reports remain valid; optional evidence is still checked when present.
  const report=fixture();report.inputs.dynamicFixtureSha256={v1:digest('v1'),v2:digest('v2')};
  assert.equal(validateReport(report),report);
});


function residentFixture(schema) {
  const report=fixture([1,2]);
  report.method={...report.method,warmup:0,scale:1,fanout:2,scenarios:['facade.residentReplace']};
  const result=report.results[0];result.name='facade.residentReplace';result.unit='provider replacement cycle';result.iterationsPerSample=10;
  result.checkpoints=[0,10,20,20].map((cycles,index)=>{
    const closed=index===3,live=closed?0:2,allocations=2*(cycles+1);
    return {stage:index===0?'initial':closed?'closed':'sample',...(index>0&&!closed?{batch:index}:{}),completedCycles:cycles,
      ...(schema?{storageSchema:schema}:{}),
      storage:{registeredPlugins:closed?0:4,identitySlots:4+cycles,declarationRecords:4,bindingRecords:allocations,
        liveBindings:live,publicationRecords:cycles+1,leaseRecords:schema===RECLAIMED_STORAGE_SCHEMA?live:allocations,
        ...(schema===RECLAIMED_STORAGE_SCHEMA?{leaseAllocations:allocations}:{}),liveLeases:live,publishedValues:closed?0:1,pendingActions:0},
      memoryBytes:{rss:1,heapTotal:1,heapUsed:1,external:0,arrayBuffers:0,maxRssBytes:1}};
  });
  return report;
}

test('checkpoint storage tags preserve raw old/new snapshots without synthesized allocations',()=>{
  const legacy={leaseRecords:62,liveLeases:2},current={leaseRecords:2,liveLeases:2,leaseAllocations:62};
  assert.equal(checkpointStorage(legacy).storage,legacy);assert.equal(checkpointStorage(current).storage,current);
  assert.equal(checkpointStorage(legacy).storageSchema,LEGACY_STORAGE_SCHEMA);
  assert.equal(checkpointStorage(current).storageSchema,RECLAIMED_STORAGE_SCHEMA);
  assert.equal(Object.hasOwn(legacy,'leaseAllocations'),false);
});

test('historical untagged and newly tagged legacy checkpoints retain their original lease semantics',async()=>{
  for(const schema of [undefined,LEGACY_STORAGE_SCHEMA,RECLAIMED_STORAGE_SCHEMA])assert.equal(validateReport(residentFixture(schema)).status,'passed');
  for(const name of ['2026-10-06-resident-before.json','2026-10-06-resident-after.json','2026-10-06-native-checkpoint-run1.json']) {
    const report=JSON.parse(await readFile(new URL('../../docs/performance/'+name,import.meta.url),'utf8'));
    const original=JSON.stringify(report);
    assert.equal(validateReport(report),report);
    assert.equal(JSON.stringify(report),original,'Validation must not rewrite historical observations');
    for(const result of report.results)for(const point of result.checkpoints) {
      assert.equal(Object.hasOwn(point,'storageSchema'),false);assert.equal(Object.hasOwn(point.storage,'leaseAllocations'),false);
    }
  }
});

test('storage schema rejects missing, mixed, unknown or inconsistent allocation semantics',()=>{
  for(const mutate of [
    r=>delete r.results[0].checkpoints[1].storageSchema,
    r=>r.results[0].checkpoints[1].storageSchema=null,
    r=>r.results[0].checkpoints[1].storageSchema='unknown',
    r=>r.results[0].checkpoints[1].storageSchema=LEGACY_STORAGE_SCHEMA,
    r=>delete r.results[0].checkpoints[1].storage.leaseAllocations,
    r=>r.results[0].checkpoints[1].storage.leaseAllocations=1,
    r=>r.results[0].checkpoints[1].storage.leaseAllocations++,
    r=>r.results[0].checkpoints[1].storage.leaseRecords=22,
    r=>r.results[0].checkpoints.at(-1).storage.leaseRecords=1,
    r=>r.results[0].checkpoints.at(-1).storage.leaseAllocations++,
  ]) {
    const report=residentFixture(RECLAIMED_STORAGE_SCHEMA);mutate(report);
    assert.throws(()=>validateReport(report),/checkpoint/i);
  }
  const legacy=residentFixture(LEGACY_STORAGE_SCHEMA);legacy.results[0].checkpoints[1].storage.leaseRecords--;
  assert.throws(()=>validateReport(legacy),/allocation history/);
  const mixed=residentFixture(LEGACY_STORAGE_SCHEMA);
  mixed.results[0].checkpoints[1]=residentFixture(RECLAIMED_STORAGE_SCHEMA).results[0].checkpoints[1];
  assert.throws(()=>validateReport(mixed),/storage schema changed/);
});

test('same-harness latency comparison exposes old/new storage semantics and still pins old source',()=>{
  const baseline=residentFixture(LEGACY_STORAGE_SCHEMA),candidate=residentFixture(RECLAIMED_STORAGE_SCHEMA);
  candidate.inputs.sourceHashes['runtime.js']=digest('reclaimed leases');candidate.inputs.sourceDigest=digest(candidate.inputs.sourceHashes);
  assert.throws(()=>compareReports(candidate,baseline,{threshold:0}),/source changed/);
  const comparison=compareReports(candidate,baseline,{threshold:0,baselineSource:baseline.inputs.sourceDigest});
  assert.equal(comparison.status,'passed');assert.equal(comparison.crossSource,true);
  assert.equal(comparison.comparisons[0].baselineStorageSchema,LEGACY_STORAGE_SCHEMA);
  assert.equal(comparison.comparisons[0].candidateStorageSchema,RECLAIMED_STORAGE_SCHEMA);
  assert.equal(comparison.comparisons[0].ratio,1);
  assert.equal(Object.hasOwn(baseline.results[0].checkpoints[0].storage,'leaseAllocations'),false);
});
