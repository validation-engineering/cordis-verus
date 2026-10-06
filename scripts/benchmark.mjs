#!/usr/bin/env node
/** Reproducible local measurements; no compiler, network, proof, or publication. */
import { spawnSync } from 'node:child_process';
import { randomUUID } from 'node:crypto';
import { mkdir, readFile, realpath, rename, rm, writeFile } from 'node:fs/promises';
import { dirname,join,resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { collectInputs } from './benchmark/inputs.mjs';
import { scenarios } from './benchmark/scenarios.mjs';
import { SCHEMA,compareReports,digest,validateReport } from './benchmark/statistics.mjs';
const root=resolve(dirname(fileURLToPath(import.meta.url)),'..');
export function parseOptions(args) {
  const options={output:join(root,'target/benchmarks/latest.json'),samples:25,warmup:5,scale:1,fanout:16,streamItems:16,timeoutMs:60000,gc:'before-and-after',metric:'p95',scenarios:[]};
  const names={'--output':'output','--samples':'samples','--warmup':'warmup','--scale':'scale','--fanout':'fanout','--stream-items':'streamItems','--timeout-ms':'timeoutMs','--baseline':'baseline','--baseline-source':'baselineSource','--max-regression':'threshold','--metric':'metric'};
  for(let i=0;i<args.length;i++) {
    const flag=args[i];
    if(flag==='--help'){options.help=true;continue;}
    if(flag==='--no-gc'){options.gc='natural';continue;}
    if(flag==='--scenario'){const name=args[++i];if(!scenarios[name]||options.scenarios.includes(name))throw new Error('Invalid or duplicate --scenario');options.scenarios.push(name);continue;}
    const key=names[flag];if(!key||args[i+1]===undefined)throw new Error('Unknown option or missing value: '+flag);
    options[key]=args[++i];
  }
  for(const [name,min,max] of [['samples',2,10000],['warmup',0,10000],['scale',1,1000],['fanout',1,1000],['streamItems',1,10000],['timeoutMs',100,3600000]]){
    options[name]=Number(options[name]);if(!Number.isSafeInteger(options[name])||options[name]<min||options[name]>max)throw new Error('Invalid --'+name);
  }
  if(!['p50','p95','p99','mean'].includes(options.metric))throw new Error('Invalid --metric');
  if(options.baseline!==undefined){if(typeof options.baseline!=='string'||!options.baseline.trim())throw new Error('--baseline requires a nonempty path');options.baseline=resolve(options.baseline);options.threshold=Number(options.threshold);if(!Number.isFinite(options.threshold)||options.threshold<0)throw new Error('--baseline requires explicit --max-regression (e.g. 0.20)');}
  else if(options.threshold!==undefined||options.baselineSource!==undefined)throw new Error('Baseline options require --baseline');
  options.output=resolve(options.output);
  if(options.baseline===options.output)throw new Error('Output must not overwrite its baseline');
  if(!options.scenarios.length)options.scenarios=Object.keys(scenarios);
  return options;
}
export function parseBaseline(bytes) {
  const report=validateReport(JSON.parse(bytes));
  if(report.status!=='passed')throw new Error('A regression report cannot be promoted to a passing baseline');
  return report;
}
async function save(path,report) {
  await mkdir(dirname(path),{recursive:true});const temporary=path+'.'+randomUUID()+'.tmp';
  try {await writeFile(temporary,JSON.stringify(report,null,2)+'\n');await rename(temporary,path);}
  finally {await rm(temporary,{force:true});}
}
export async function main(args=process.argv.slice(2)) {
  const options=parseOptions(args);
  if(options.help){console.log('Usage: node scripts/benchmark.mjs [--output FILE] [--samples 25] [--warmup 5] [--scale 1] [--fanout 16] [--stream-items 16] [--scenario NAME] [--no-gc] [--timeout-ms 60000] [--baseline FILE --max-regression 0.20 --metric p95 [--baseline-source DIGEST]]\nScenarios: '+Object.keys(scenarios).join(', '));return 0;}
  if(options.baseline!==undefined){let baselinePath,outputPath;try{baselinePath=await realpath(options.baseline);}catch(error){if(error.code!=='ENOENT')throw error;}try{outputPath=await realpath(options.output);}catch(error){if(error.code!=='ENOENT')throw error;}if(baselinePath&&baselinePath===outputPath)throw new Error('Output must not overwrite its baseline through a path alias');}
  const method={version:1,samples:options.samples,warmup:options.warmup,scale:options.scale,fanout:options.fanout,streamItems:options.streamItems,gc:options.gc,scenarios:options.scenarios,concurrency:1,percentiles:'nearest-rank over batch-amortized ns/unit',isolation:'fresh Node process per scenario',timer:'performance.now milliseconds',eventLoopResolutionMs:1};
  let report={schema:SCHEMA,status:'running',measurementStatus:'incomplete',startedAt:new Date().toISOString(),method,results:[],uploaded:false,proofExecuted:false};
  await save(options.output,report);
  try {
    for(const name of ['NODE_OPTIONS','NODE_PATH','CORDIS_NATIVE_BINDING'])if(process.env[name])throw new Error('Unset '+name+' for an attributable benchmark');
    const baselineBytes=options.baseline!==undefined?await readFile(options.baseline):undefined;
    const baseline=options.baseline!==undefined?parseBaseline(baselineBytes):undefined;
    const inputOptions={dynamicFixtures:options.scenarios.some(name=>scenarios[name].dynamicFixtures===true)};
    const before=await collectInputs(root,inputOptions);report={...report,inputs:before.inputs,environment:before.environment};
    for(const name of options.scenarios) {
      const result=spawnSync(process.execPath,[...(options.gc==='before-and-after'?['--expose-gc']:[]),join(root,'scripts/benchmark/worker.mjs'),JSON.stringify({name,method,fixturePath:before.fixturePath,dynamicFixtures:before.dynamicFixtures})],{cwd:root,env:process.env,encoding:'utf8',timeout:options.timeoutMs,killSignal:'SIGKILL',maxBuffer:32*1024*1024});
      if(result.error||result.status!==0)throw new Error('Scenario '+name+' failed; cleanup unconfirmed if the worker was terminated: '+(result.error?.message??result.stderr));
      const observation=JSON.parse(result.stdout.trim());
      if(observation.name!==name||observation.cleanupConfirmed!==true)throw new Error('Incomplete worker result: '+name);
      report.results.push(observation);
      console.error(name+': p95 '+observation.statistics.nanosecondsPerUnit.p95.toFixed(0)+' ns/'+observation.unit);
    }
    const after=await collectInputs(root,inputOptions);
    if(digest(before)!==digest(after))throw new Error('Source, build, native artifact or environment changed during measurement');
    report={...report,status:'passed',measurementStatus:'passed',completedAt:new Date().toISOString()};
    validateReport(report);
    if(options.baseline!==undefined){report.comparison={...compareReports(report,baseline,options),baselineReportSha256:digest(baselineBytes)};report.status=report.comparison.status;}
    await save(options.output,report);
    console.log(report.status+': '+options.output);
    return report.status==='performance-regression'?2:0;
  } catch(error) {
    report={schema:SCHEMA,status:'measurement-failed',measurementStatus:'failed',startedAt:report.startedAt,failedAt:new Date().toISOString(),method,inputs:report.inputs,environment:report.environment,failure:String(error?.stack??error),results:[],uploaded:false,proofExecuted:false};
    await save(options.output,report);console.error(report.failure);return 1;
  }
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url)){
  try{process.exitCode=await main();}catch(error){console.error(String(error));process.exitCode=1;}
}
