import { monitorEventLoopDelay, performance } from 'node:perf_hooks';
import { setTimeout as delay, setImmediate as turn } from 'node:timers/promises';
import { prepareScenario,scenarios } from './scenarios.mjs';
import { summarize } from './statistics.mjs';
const {name,method,fixturePath}=JSON.parse(process.argv[2]);
if(!scenarios[name])throw new Error('Unknown benchmark worker scenario');
const scenario=await prepareScenario(name,{fixturePath,fanout:method.fanout,streamItems:method.streamItems});
const iterations=scenario.iterations??scenarios[name].batch*method.scale;
const unitsPerSample=iterations*(scenario.unitsPerIteration??1),samplesMs=[],cpuSamples=[],checkpoints=[];
const memory=()=>({...process.memoryUsage(),maxRssBytes:process.resourceUsage().maxRSS*1024});
const loop=monitorEventLoopDelay({resolution:1});
let result;
try {
  if(method.gc==='before-and-after')global.gc();
  const before=memory();
  if(scenario.checkpoint)checkpoints.push({stage:'initial',...scenario.checkpoint(),memoryBytes:before});
  for(let i=0;i<method.warmup+method.samples;i++) {
    await scenario.beforeSample?.();
    if(i===method.warmup){loop.enable();await delay(5);}
    const cpu=process.cpuUsage(),started=performance.now();
    // A synchronous benchmark must not gain one Promise await per operation.
    const value=scenario.runSync?scenario.runSync(iterations):await scenario.run(iterations);
    const elapsed=performance.now()-started,used=process.cpuUsage(cpu);
    scenario.validate(value,iterations);
    await scenario.afterSample?.();
    if(scenario.checkpoint)checkpoints.push({stage:i<method.warmup?'warmup':'sample',batch:i+1,...scenario.checkpoint(),memoryBytes:memory()});
    if(i>=method.warmup){samplesMs.push(elapsed);cpuSamples.push(used);}
    await turn();
  }
  const afterSamples=memory();
  await delay(5);loop.disable();
  await scenario.close();
  if(method.gc==='before-and-after')global.gc();
  const afterCleanup=memory();
  if(scenario.checkpoint)checkpoints.push({stage:'closed',...scenario.checkpoint(),memoryBytes:afterCleanup});
  result={name,unit:scenarios[name].unit,description:scenarios[name].description,iterationsPerSample:iterations,unitsPerSample,samplesMs,
    statistics:summarize(samplesMs,unitsPerSample),cpuSamplesMicroseconds:cpuSamples,
    memoryBytes:{before,afterSamples,afterCleanup,rssRetainedDelta:afterCleanup.rss-before.rss,heapRetainedDelta:afterCleanup.heapUsed-before.heapUsed},
    eventLoopDelayNanoseconds:loop.count?{count:loop.count,min:loop.min,max:loop.max,mean:loop.mean,p95:loop.percentile(95)}:null,
    ...(scenario.checkpoint?{checkpoints}:{}),cleanupConfirmed:true};
} catch(error) {
  loop.disable();
  try{await scenario.close();}catch(cleanup){throw new AggregateError([error,cleanup],'Benchmark and cleanup failed');}
  throw error;
}
process.stdout.write(JSON.stringify(result)+'\n');
