import assert from 'node:assert/strict';
import { lstat, readFile, readdir } from 'node:fs/promises';
import { join, relative, resolve } from 'node:path';
import { cpus, release, totalmem } from 'node:os';
import { createRequire } from 'node:module';
import { selectNativeArtifact } from '../../packages/compat-cordis/native-artifacts.js';
import { digest } from './statistics.mjs';
export async function filesUnder(root,directory,accept) {
  const found=[];
  async function visit(path) {
    for(const entry of await readdir(path,{withFileTypes:true})) {
      if(['node_modules','target','.git'].includes(entry.name)||(entry.name==='native'&&relative(root,path)==='packages/compat-cordis'))continue;
      const next=join(path,entry.name);
      if(entry.isSymbolicLink())throw new Error('Benchmark inputs cannot be symlinks: '+next);
      if(entry.isDirectory())await visit(next);else if(entry.isFile()&&accept(next))found.push(relative(root,next).split('\\').join('/'));
    }
  }
  await visit(join(root,directory)); return found.sort();
}
const hashes=async(root,names)=>Object.fromEntries(await Promise.all([...new Set(names)].sort().map(async name=>[name,digest(await readFile(join(root,name)))])));
export async function nativeSourceInputs(root) {
  const files=['Cargo.toml','Cargo.lock','toolchain.lock.json','scripts/build-node.sh','scripts/build-node.mjs','scripts/toolchain-env.sh','scripts/write-native-manifest.mjs','packages/compat-cordis/native-artifacts.js','packages/compat-cordis/package.json'];
  for(const name of ['cordis-kernel','cordis-driver','cordis','cordis-node','cordis-plugin-api']) files.push(...await filesUnder(root,'crates/'+name,path=>/\.(rs|toml)$/.test(path)));
  return {files,sourceHashes:await hashes(root,files)};
}
// Only scenarios loading these independent C-ABI images require their evidence.
// A filename supplied by build.json must not redirect execution to another image.
export async function dynamicFixtureInputs(root,build) {
  const extension={darwin:'.dylib',linux:'.so',win32:'.dll'}[process.platform];
  assert.ok(extension,'Unsupported dynamic fixture platform');
  const fixtures={};
  for(const version of ['v1','v2']) {
    const expected=`target/node-compat/dynamic-fixture-${version}${extension}`,entry=build.dynamicFixtures?.[version];
    assert.equal(entry?.path,expected,`Missing or unexpected dynamic ${version} fixture path; run build:native first`);
    assert.match(entry.sha256??'',/^[a-f0-9]{64}$/,`Invalid dynamic ${version} fixture SHA-256`);
    let path=resolve(root);
    for(const part of expected.split('/')) {
      path=join(path,part);
      assert.equal((await lstat(path)).isSymbolicLink(),false,`Dynamic fixture paths cannot contain symlinks: ${expected}`);
    }
    assert.ok((await lstat(path)).isFile(),`Dynamic fixture must be a regular file: ${expected}`);
    const sha256=digest(await readFile(path));
    assert.equal(sha256,entry.sha256,`Dynamic ${version} fixture is stale; run build:native first`);
    fixtures[version]={path,sha256};
  }
  assert.notEqual(fixtures.v1.sha256,fixtures.v2.sha256,'Dynamic fixture generations must be distinct');
  return fixtures;
}
export async function benchmarkSourceInputs(root,nativeFiles) {
  const harnessNames=['scripts/benchmark.mjs',...await filesUnder(root,'scripts/benchmark',path=>path.endsWith('.mjs'))];
  const sourceNames=[...nativeFiles,...harnessNames,'package.json','package-lock.json'];
  // The module controller performs the measured migration and cleanup work.
  for(const name of ['compat-cordis','compat-loader'])sourceNames.push(...await filesUnder(root,'packages/'+name,path=>/\.(js|cjs|mjs|json|ts)$/.test(path)));
  return {sourceHashes:await hashes(root,sourceNames),harnessDigest:digest(await hashes(root,harnessNames))};
}
export async function collectInputs(root,{dynamicFixtures:requireDynamicFixtures=false}={}) {
  const buildBytes=await readFile(join(root,'target/node-compat/build.json')),build=JSON.parse(buildBytes);
  const {files:nativeFiles,sourceHashes:nativeHashes}=await nativeSourceInputs(root);
  assert.equal(build.schema,'cordis-verus.node-build/v1','Unsupported native build evidence');
  assert.deepEqual(build.sourceHashes,nativeHashes,'Native build sources are stale; run build:native first');
  assert.equal(build.platform,process.platform);assert.equal(build.architecture,process.arch);assert.equal(build.node,process.version,'Benchmark with the Node version that built the native artifact');
  const selected=selectNativeArtifact();
  assert.equal(selected.entry.sha256,build.artifactSha256);
  assert.equal(selected.provenance.build.reportSha256,digest(buildBytes));
  assert.equal(build.interopFixture?.path,'target/node-compat/interop-fixture.node');
  const fixturePath=join(root,build.interopFixture.path),fixtureSha256=digest(await readFile(fixturePath));
  assert.equal(fixtureSha256,build.interopFixture.sha256,'Rust SDK fixture is stale');
  const dynamicFixtures=requireDynamicFixtures?await dynamicFixtureInputs(root,build):undefined;
  const {sourceHashes,harnessDigest}=await benchmarkSourceInputs(root,nativeFiles);
  const binding=createRequire(import.meta.url)(selected.path),info=JSON.parse(binding.bindingInfo()),processors=cpus();
  const environment={platform:process.platform,architecture:process.arch,osRelease:release(),cpuModel:processors[0]?.model??'unknown',cpuCount:processors.length,totalMemoryBytes:totalmem(),node:process.version,nodeApi:process.versions.napi,nodeModuleAbi:process.versions.modules,driverAbi:info.abi,bindingProfile:info.profile,compilerProfile:build.compilerProfile,toolchainLockSha256:build.toolchainLockSha256,libc:selected.entry.libc};
  return {environment,inputs:{sourceHashes,sourceDigest:digest(sourceHashes),harnessDigest,nativeArtifactSha256:selected.entry.sha256,nativeManifestSha256:selected.manifestSha256,buildReportSha256:digest(buildBytes),sdkFixtureSha256:fixtureSha256,nativeTarget:selected.entry.target,...(dynamicFixtures?{dynamicFixtureSha256:Object.fromEntries(Object.entries(dynamicFixtures).map(([version,fixture])=>[version,fixture.sha256]))}:{})},fixturePath,...(dynamicFixtures?{dynamicFixtures}:{})};
}
