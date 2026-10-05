import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdtemp,readFile,realpath,rm,symlink,writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { tmpdir } from 'node:os';
import { fileURLToPath } from 'node:url';
const script=fileURLToPath(new URL('../../scripts/benchmark.mjs',import.meta.url));
test('preflight failure replaces prior success without loading a benchmark or claiming cleanup',async t=>{
  const directory=await mkdtemp(join(tmpdir(),'cordis-bench-failure-'));t.after(()=>rm(directory,{recursive:true,force:true}));
  const output=join(directory,'result.json');await writeFile(output,JSON.stringify({status:'passed',old:true}));
  const env={...process.env,CORDIS_NATIVE_BINDING:'deliberate-test-override'};delete env.NODE_OPTIONS;delete env.NODE_PATH;
  const result=spawnSync(process.execPath,[script,'--output',output],{env,encoding:'utf8',timeout:10000});
  assert.equal(result.status,1,result.stderr);
  const report=JSON.parse(await readFile(output,'utf8'));
  assert.equal(report.status,'measurement-failed');assert.equal(report.measurementStatus,'failed');
  assert.equal(report.old,undefined);assert.deepEqual(report.results,[]);assert.match(report.failure,/Unset CORDIS_NATIVE_BINDING/);
});
test('CLI refuses an output symlink alias to its baseline before writing either file',async t=>{
  const directory=await realpath(await mkdtemp(join(tmpdir(),'cordis-bench-baseline-')));t.after(()=>rm(directory,{recursive:true,force:true}));
  const baseline=join(directory,'baseline.json'),alias=join(directory,'alias.json');
  await writeFile(baseline,'preserved baseline bytes');await symlink(baseline,alias);
  const env={...process.env};delete env.NODE_OPTIONS;delete env.NODE_PATH;delete env.CORDIS_NATIVE_BINDING;
  const result=spawnSync(process.execPath,[script,'--output',alias,'--baseline',baseline,'--max-regression','.2'],{env,encoding:'utf8',timeout:10000});
  assert.equal(result.status,1);assert.match(result.stderr,/path alias/);assert.equal(await readFile(baseline,'utf8'),'preserved baseline bytes');
});

test('invalid or missing explicit baseline writes failure before native measurement',async t=>{
  const directory=await mkdtemp(join(tmpdir(),'cordis-bench-invalid-baseline-'));t.after(()=>rm(directory,{recursive:true,force:true}));
  const baseline=join(directory,'baseline.json'),output=join(directory,'result.json');
  const env={...process.env};for(const name of ['NODE_OPTIONS','NODE_PATH','CORDIS_NATIVE_BINDING'])delete env[name];
  for(const content of ['null',undefined]) {
    if(content===undefined)await rm(baseline);else await writeFile(baseline,content);
    await writeFile(output,'{"status":"passed","old":true}');
    const result=spawnSync(process.execPath,[script,'--output',output,'--baseline',baseline,'--max-regression','.2'],{env,encoding:'utf8',timeout:10000});
    assert.equal(result.status,1);const report=JSON.parse(await readFile(output,'utf8'));
    assert.equal(report.status,'measurement-failed');assert.deepEqual(report.results,[]);assert.equal(report.inputs,undefined);assert.equal(report.old,undefined);
    assert.match(report.failure,content===undefined?/ENOENT/:/complete successful measurement/);
  }
});
