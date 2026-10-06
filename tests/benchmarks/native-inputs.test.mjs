import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdir,mkdtemp,readFile,rm,symlink,writeFile } from 'node:fs/promises';
import { dirname,isAbsolute,join,relative } from 'node:path';
import { tmpdir } from 'node:os';
import { benchmarkSourceInputs,collectInputs,dynamicFixtureInputs,nativeSourceInputs } from '../../scripts/benchmark/inputs.mjs';
import { digest } from '../../scripts/benchmark/statistics.mjs';

test('benchmark rejects a build when its typed Cordis Rust dependency changes',async t=>{
  const root=await mkdtemp(join(tmpdir(),'cordis-native-inputs-'));t.after(()=>rm(root,{recursive:true,force:true}));
  const files=['Cargo.toml','Cargo.lock','toolchain.lock.json','scripts/build-node.sh','scripts/build-node.mjs','scripts/toolchain-env.sh','scripts/write-native-manifest.mjs','packages/compat-cordis/native-artifacts.js','packages/compat-cordis/package.json'];
  for(const name of ['cordis-kernel','cordis-driver','cordis','cordis-node','cordis-plugin-api'])files.push('crates/'+name+'/Cargo.toml','crates/'+name+'/src/lib.rs');
  for(const name of files){const path=join(root,name);await mkdir(dirname(path),{recursive:true});await writeFile(path,'fixture input '+name);}
  await writeFile(join(root,'crates/cordis/README.md'),'documentation is not a native source input');
  const original=await nativeSourceInputs(root);
  assert.equal(original.sourceHashes['crates/cordis/src/lib.rs'],digest(await readFile(join(root,'crates/cordis/src/lib.rs'))));
  assert.equal(original.sourceHashes['crates/cordis/Cargo.toml'],digest(await readFile(join(root,'crates/cordis/Cargo.toml'))));
  assert.equal(original.sourceHashes['crates/cordis/README.md'],undefined);
  const build=join(root,'target/node-compat/build.json');await mkdir(dirname(build),{recursive:true});
  await writeFile(build,JSON.stringify({schema:'cordis-verus.node-build/v1',sourceHashes:original.sourceHashes}));
  for(const name of ['crates/cordis/src/lib.rs','crates/cordis/Cargo.toml']){
    const path=join(root,name),before=await readFile(path);
    try{await writeFile(path,Buffer.concat([before,Buffer.from('changed runtime dependency')]));await assert.rejects(collectInputs(root),/Native build sources are stale/);}
    finally{await writeFile(path,before);}
  }
  assert.deepEqual((await nativeSourceInputs(root)).sourceHashes,original.sourceHashes);
});

async function dynamicEvidence(t) {
  const root=await mkdtemp(join(tmpdir(),'cordis-dynamic-inputs-'));t.after(()=>rm(root,{recursive:true,force:true}));
  const extension={darwin:'.dylib',linux:'.so',win32:'.dll'}[process.platform],build={dynamicFixtures:{}};
  for(const version of ['v1','v2']) {
    const path=`target/node-compat/dynamic-fixture-${version}${extension}`,bytes=Buffer.from('independent fixture '+version);
    await mkdir(dirname(join(root,path)),{recursive:true});await writeFile(join(root,path),bytes);
    build.dynamicFixtures[version]={path,sha256:digest(bytes)};
  }
  return {root,build};
}
test('dynamic benchmark evidence binds each generation to its fixed image and worker SHA',async t=>{
  const {root,build}=await dynamicEvidence(t),fixtures=await dynamicFixtureInputs(root,build);
  assert.deepEqual(Object.keys(fixtures),['v1','v2']);
  for(const version of ['v1','v2']) {
    assert.equal(isAbsolute(fixtures[version].path),true);
    assert.equal(relative(root,fixtures[version].path).split('\\').join('/'),build.dynamicFixtures[version].path);
    assert.equal(fixtures[version].sha256,digest(await readFile(fixtures[version].path)));
  }
  assert.deepEqual(await dynamicFixtureInputs(root,build),fixtures);
});
test('dynamic benchmark rejects omitted or redirected build evidence',async t=>{
  const {root,build}=await dynamicEvidence(t);
  for(const mutate of [
    value=>delete value.dynamicFixtures,
    value=>delete value.dynamicFixtures.v1,
    value=>delete value.dynamicFixtures.v2,
    value=>delete value.dynamicFixtures.v1.path,
    value=>value.dynamicFixtures.v1.path=value.dynamicFixtures.v2.path,
    value=>value.dynamicFixtures.v1.path='../dynamic-fixture-v1.dylib',
    value=>value.dynamicFixtures.v1.path=join(root,value.dynamicFixtures.v1.path),
    value=>delete value.dynamicFixtures.v1.sha256,
    value=>value.dynamicFixtures.v2.sha256='not-a-sha256',
  ]) {
    const changed=structuredClone(build);mutate(changed);
    await assert.rejects(dynamicFixtureInputs(root,changed),/fixture path|fixture SHA-256/);
  }
});
test('dynamic benchmark rejects swapped, changed, or missing image bytes on a second collection',async t=>{
  const {root,build}=await dynamicEvidence(t),before=await dynamicFixtureInputs(root,build);
  const first=before.v1.path,second=before.v2.path,firstBytes=await readFile(first),secondBytes=await readFile(second);
  for(const bytes of [secondBytes,Buffer.concat([firstBytes,Buffer.from('modified after preflight')])]) {
    await writeFile(first,bytes);
    await assert.rejects(dynamicFixtureInputs(root,build),/Dynamic v1 fixture is stale/);
  }
  await rm(first);await assert.rejects(dynamicFixtureInputs(root,build),{code:'ENOENT'});
  await writeFile(first,firstBytes);assert.deepEqual(await dynamicFixtureInputs(root,build),before);
  // Even a refreshed report and valid new bytes must change the before/after
  // measurement binding; validating each collection alone is insufficient.
  const updated=Buffer.concat([firstBytes,Buffer.from('rebuilt')]);await writeFile(first,updated);
  build.dynamicFixtures.v1.sha256=digest(updated);
  assert.notEqual(digest(await dynamicFixtureInputs(root,build)),digest(before));
});
test('dynamic benchmark rejects alias paths and duplicate generations',async t=>{
  const {root,build}=await dynamicEvidence(t),first=join(root,build.dynamicFixtures.v1.path);
  const bytes=await readFile(first),alias=join(root,'alias-image');await writeFile(alias,bytes);
  await rm(first);await symlink(alias,first);
  await assert.rejects(dynamicFixtureInputs(root,build),/cannot contain symlinks/);
  await rm(first);await mkdir(first);
  await assert.rejects(dynamicFixtureInputs(root,build),/regular file/);
  await rm(first,{recursive:true});await writeFile(first,bytes);
  await writeFile(join(root,build.dynamicFixtures.v2.path),bytes);build.dynamicFixtures.v2.sha256=digest(bytes);
  await assert.rejects(dynamicFixtureInputs(root,build),/generations must be distinct/);
});
test('benchmark source binding includes Loader implementation, types and package metadata',async t=>{
  const root=await mkdtemp(join(tmpdir(),'cordis-loader-inputs-'));t.after(()=>rm(root,{recursive:true,force:true}));
  const loader=['index.js','nested/worker.mjs','legacy.cjs','rust-module.d.ts','package.json'].map(name=>'packages/compat-loader/'+name);
  const files=['scripts/benchmark.mjs','scripts/benchmark/inputs.mjs','package.json','package-lock.json','packages/compat-cordis/index.js',...loader];
  for(const name of files){const path=join(root,name);await mkdir(dirname(path),{recursive:true});await writeFile(path,'fixture '+name);}
  await writeFile(join(root,'packages/compat-loader/README.md'),'Not executed by the benchmark');
  const original=await benchmarkSourceInputs(root,[]);
  for(const name of loader)assert.equal(original.sourceHashes[name],digest(await readFile(join(root,name))));
  assert.equal(original.sourceHashes['packages/compat-loader/README.md'],undefined);
  for(const name of loader) {
    const path=join(root,name),before=await readFile(path);
    await writeFile(path,Buffer.concat([before,Buffer.from(' changed')]));
    const changed=await benchmarkSourceInputs(root,[]);
    assert.notEqual(digest(changed.sourceHashes),digest(original.sourceHashes),name);
    assert.equal(changed.harnessDigest,original.harnessDigest,'Runtime changes do not change benchmark methodology');
    await writeFile(path,before);
  }
  assert.deepEqual(await benchmarkSourceInputs(root,[]),original);
});
