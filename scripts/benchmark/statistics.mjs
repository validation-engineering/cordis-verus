import { createHash } from 'node:crypto';
export const SCHEMA='cordis-verus.benchmark/v1';
export function canonical(value) {
  if (Array.isArray(value)) return value.map(canonical);
  if (value && typeof value==='object') return Object.fromEntries(Object.entries(value).sort(([a],[b])=>a<b?-1:a>b?1:0).map(([key,item])=>[key,canonical(item)]));
  return value;
}
export const digest=value=>createHash('sha256').update(typeof value==='string'||Buffer.isBuffer(value)?value:JSON.stringify(canonical(value))).digest('hex');
export function summarize(samplesMs,unitsPerSample) {
  if(!Array.isArray(samplesMs)||!samplesMs.length||samplesMs.some(value=>!Number.isFinite(value)||value<=0)||!Number.isSafeInteger(unitsPerSample)||unitsPerSample<=0) throw new Error('Invalid benchmark samples or unit count');
  const values=samplesMs.map(value=>value*1e6/unitsPerSample).sort((a,b)=>a-b);
  const percentile=p=>values[Math.max(0,Math.ceil(values.length*p)-1)];
  const totalMs=samplesMs.reduce((sum,value)=>sum+value,0);
  return {sampleCount:values.length,unitsPerSample,totalUnits:values.length*unitsPerSample,
    nanosecondsPerUnit:{min:values[0],p50:percentile(.5),p95:percentile(.95),p99:percentile(.99),max:values.at(-1),mean:totalMs*1e6/(values.length*unitsPerSample)},
    unitsPerSecond:values.length*unitsPerSample*1000/totalMs};
}
export function validateCheckpoints(result,method) {
  const required=['facade.residentRestart','facade.residentReplace'].includes(result.name);
  if(!required&&result.checkpoints===undefined)return;
  const points=result.checkpoints,total=method.warmup+method.samples;
  if(!Array.isArray(points)||points.length!==total+2||!Number.isSafeInteger(result.iterationsPerSample)||result.iterationsPerSample<=0)throw new Error('Incomplete resident checkpoints');
  const counters=['registeredPlugins','identitySlots','declarationRecords','bindingRecords','liveBindings','publicationRecords','leaseRecords','liveLeases','publishedValues','pendingActions'];
  for(const [index,point] of points.entries()) {
    const closed=index===total+1,cycles=Math.min(index,total)*result.iterationsPerSample;
    const stage=index===0?'initial':closed?'closed':index<=method.warmup?'warmup':'sample';
    if(point.stage!==stage||point.completedCycles!==cycles||index>0&&!closed&&point.batch!==index
      ||counters.some(key=>!Number.isSafeInteger(point.storage?.[key])||point.storage[key]<0)
      ||['rss','heapTotal','heapUsed','external','arrayBuffers','maxRssBytes'].some(key=>!Number.isFinite(point.memoryBytes?.[key])||point.memoryBytes[key]<0))throw new Error('Invalid resident checkpoint');
    if(index>0&&['identitySlots','publicationRecords','leaseRecords'].some(key=>point.storage[key]<points[index-1].storage[key]))throw new Error('Resident checkpoint lost stable identity history');
    if(closed&&['registeredPlugins','liveBindings','liveLeases','publishedValues','pendingActions'].some(key=>point.storage[key]!==0))throw new Error('Resident cleanup checkpoint has live resources');
  }
}
export function validateReport(report) {
  const hash=/^[a-f0-9]{64}$/;
  if(report?.schema!==SCHEMA||report.measurementStatus!=='passed'||!['passed','performance-regression'].includes(report.status)) throw new Error('Baseline/candidate does not contain a complete successful measurement');
  if(!report.inputs?.sourceHashes||Array.isArray(report.inputs.sourceHashes)||typeof report.inputs.sourceHashes!=='object'||!Object.keys(report.inputs.sourceHashes).length||Object.values(report.inputs.sourceHashes).some(value=>!hash.test(value))||report.inputs.sourceDigest!==digest(report.inputs.sourceHashes)||!hash.test(report.inputs.harnessDigest)) throw new Error('Invalid or changed benchmark source binding');
  if(['nativeArtifactSha256','nativeManifestSha256','buildReportSha256','sdkFixtureSha256'].some(key=>!hash.test(report.inputs[key])))throw new Error('Incomplete benchmark native/build evidence');
  if(!report.environment||typeof report.environment!=='object'||!report.environment.platform||!report.environment.architecture||!report.environment.node||!report.environment.cpuModel||!report.environment.nodeApi||report.environment.driverAbi!==1)throw new Error('Incomplete benchmark environment');
  if(!Array.isArray(report.results)||!report.results.length||!Array.isArray(report.method?.scenarios)||new Set(report.method.scenarios).size!==report.method.scenarios.length||report.results.length!==report.method.scenarios.length) throw new Error('Incomplete benchmark scenario set');
  if(!Number.isSafeInteger(report.method.samples)||report.method.samples<2||!Number.isSafeInteger(report.method.warmup)||report.method.warmup<0) throw new Error('Invalid benchmark sampling method');
  const seen=new Set();
  for(const result of report.results) {
    if(!result||result.cleanupConfirmed!==true||typeof result.unit!=='string'||!result.unit||seen.has(result.name)||!report.method.scenarios.includes(result.name)||result.samplesMs?.length!==report.method.samples) throw new Error('Incomplete or duplicate benchmark samples');
    seen.add(result.name);
    validateCheckpoints(result,report.method);
    if(JSON.stringify(canonical(result.statistics))!==JSON.stringify(canonical(summarize(result.samplesMs,result.unitsPerSample)))) throw new Error('Benchmark statistics do not match the raw samples');
  }
  return report;
}
export function compareReports(candidate,baseline,{threshold,metric='p95',baselineSource}={}) {
  validateReport(candidate);validateReport(baseline);
  if(baseline.status!=='passed') throw new Error('A regression report cannot be promoted to a passing baseline');
  if(!Number.isFinite(threshold)||threshold<0||!['p50','p95','p99','mean'].includes(metric)) throw new Error('Baseline comparison requires an explicit nonnegative threshold and valid metric');
  if(digest(candidate.method)!==digest(baseline.method)||candidate.inputs.harnessDigest!==baseline.inputs.harnessDigest) throw new Error('Stale baseline: benchmark method or harness changed');
  if(digest(candidate.environment)!==digest(baseline.environment)) throw new Error('Incompatible baseline: platform, CPU, Node/ABI, or build profile changed');
  if(baselineSource!==undefined && baselineSource!==baseline.inputs.sourceDigest) throw new Error('Stale baseline: explicit baseline source digest does not match');
  if(candidate.inputs.sourceDigest!==baseline.inputs.sourceDigest && baselineSource!==baseline.inputs.sourceDigest) throw new Error('Stale baseline: source changed; explicitly pin --baseline-source to compare revisions');
  const comparisons=candidate.results.map(result=>{
    const prior=baseline.results.find(item=>item.name===result.name);
    if(result.unitsPerSample!==prior.unitsPerSample||result.unit!==prior.unit) throw new Error('Stale baseline: scenario units changed');
    const current=result.statistics.nanosecondsPerUnit[metric],previous=prior.statistics.nanosecondsPerUnit[metric];
    const ratio=current/previous;
    return {name:result.name,metric,baselineNanoseconds:previous,candidateNanoseconds:current,ratio,regressed:ratio>1+threshold};
  });
  return {status:comparisons.some(item=>item.regressed)?'performance-regression':'passed',threshold,metric,
    baselineSourceDigest:baseline.inputs.sourceDigest,candidateSourceDigest:candidate.inputs.sourceDigest,crossSource:candidate.inputs.sourceDigest!==baseline.inputs.sourceDigest,comparisons};
}
