import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { summarize } from '../../scripts/benchmark/statistics.mjs';

const worker=fileURLToPath(new URL('../../scripts/benchmark/worker.mjs',import.meta.url));
test('settled readiness worker reports per-fiber units, excludes warmup, and drains committed providers',()=>{
  const method={samples:2,warmup:1,scale:2,fanout:3,streamItems:1,gc:'natural'};
  const env={...process.env};for(const name of ['NODE_OPTIONS','NODE_PATH','CORDIS_NATIVE_BINDING'])delete env[name];
  const result=spawnSync(process.execPath,[worker,JSON.stringify({name:'facade.settledReadiness',method})],{env,encoding:'utf8',timeout:10000});
  assert.equal(result.status,0,result.stderr);
  const report=JSON.parse(result.stdout);
  assert.equal(report.name,'facade.settledReadiness');
  assert.equal(report.iterationsPerSample,2);assert.equal(report.unitsPerSample,6);
  assert.equal(report.samplesMs.length,2);assert.equal(report.cpuSamplesMicroseconds.length,2);
  assert.deepEqual(report.statistics,summarize(report.samplesMs,6));
  assert.equal(report.statistics.totalUnits,12);assert.equal(report.cleanupConfirmed,true);
});
