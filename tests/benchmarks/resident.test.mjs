import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import { RECLAIMED_STORAGE_SCHEMA, validateCheckpoints } from '../../scripts/benchmark/statistics.mjs';
const worker=fileURLToPath(new URL('../../scripts/benchmark/worker.mjs',import.meta.url));
for(const name of ['facade.residentRestart','facade.residentReplace']) {
  test(name+' records accumulated history while live resources stay bounded and drain',()=>{
    const method={samples:2,warmup:1,scale:1,fanout:2,streamItems:1,gc:'natural'};
    const env={...process.env};for(const key of ['NODE_OPTIONS','NODE_PATH','CORDIS_NATIVE_BINDING'])delete env[key];
    const child=spawnSync(process.execPath,[worker,JSON.stringify({name,method})],{env,encoding:'utf8',timeout:20000});
    assert.equal(child.status,0,child.stderr);
    const result=JSON.parse(child.stdout),points=result.checkpoints;
    validateCheckpoints(result,method);
    assert.equal(result.cleanupConfirmed,true);
    assert.deepEqual(points.map(p=>p.completedCycles),[0,10,20,30,30]);
    for(const point of points)assert.equal(point.storageSchema,RECLAIMED_STORAGE_SCHEMA);
    for(const point of points.slice(0,-1)) {
      assert.equal(point.storage.registeredPlugins,4);assert.equal(point.storage.liveBindings,2);
      assert.equal(point.storage.liveLeases,2);assert.equal(point.storage.leaseRecords,2);
      assert.equal(point.storage.leaseAllocations,2*(point.completedCycles+1));assert.equal(point.storage.pendingActions,0);
      assert.equal(point.storage.identitySlots,4+(name==='facade.residentReplace'?point.completedCycles:0));
      assert.ok(point.memoryBytes.rss>0);
    }
    assert.equal(points.at(-2).storage.publicationRecords-points[0].storage.publicationRecords,30);
    assert.equal(points.at(-2).storage.leaseAllocations-points[0].storage.leaseAllocations,60);
    assert.equal(points.at(-1).storage.leaseRecords,0);assert.equal(points.at(-1).storage.leaseAllocations,62);
    for(const mutate of [r=>r.checkpoints.pop(),r=>r.checkpoints[1].completedCycles--,r=>r.checkpoints.at(-1).storage.liveLeases=1,r=>r.checkpoints[1].storage.identitySlots=-1,r=>r.checkpoints[1].memoryBytes.rss=null]) {
      const changed=structuredClone(result);mutate(changed);
      assert.throws(()=>validateCheckpoints(changed,method),/checkpoint/i);
    }
  });
}
