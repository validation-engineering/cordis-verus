import assert from 'node:assert/strict';
import { readFile, readdir } from 'node:fs/promises';
import { join, relative } from 'node:path';
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
  for(const name of ['cordis-kernel','cordis-driver','cordis','cordis-node']) files.push(...await filesUnder(root,'crates/'+name,path=>/\.(rs|toml)$/.test(path)));
  return {files,sourceHashes:await hashes(root,files)};
}
export async function collectInputs(root) {
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
  const harnessNames=['scripts/benchmark.mjs',...await filesUnder(root,'scripts/benchmark',path=>path.endsWith('.mjs'))];
  const sourceNames=[...nativeFiles,...harnessNames,'package.json','package-lock.json',...await filesUnder(root,'packages/compat-cordis',path=>/\.(js|cjs|mjs|json|ts)$/.test(path))];
  const sourceHashes=await hashes(root,sourceNames),harnessHashes=await hashes(root,harnessNames);
  const binding=createRequire(import.meta.url)(selected.path),info=JSON.parse(binding.bindingInfo()),processors=cpus();
  const environment={platform:process.platform,architecture:process.arch,osRelease:release(),cpuModel:processors[0]?.model??'unknown',cpuCount:processors.length,totalMemoryBytes:totalmem(),node:process.version,nodeApi:process.versions.napi,nodeModuleAbi:process.versions.modules,driverAbi:info.abi,bindingProfile:info.profile,compilerProfile:build.compilerProfile,toolchainLockSha256:build.toolchainLockSha256,libc:selected.entry.libc};
  return {environment,inputs:{sourceHashes,sourceDigest:digest(sourceHashes),harnessDigest:digest(harnessHashes),nativeArtifactSha256:selected.entry.sha256,nativeManifestSha256:selected.manifestSha256,buildReportSha256:digest(buildBytes),sdkFixtureSha256:fixtureSha256,nativeTarget:selected.entry.target},fixturePath};
}
