import test from 'node:test';
import assert from 'node:assert/strict';
import { SCHEMA,compareReports,digest,summarize,validateReport } from '../../scripts/benchmark/statistics.mjs';
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
