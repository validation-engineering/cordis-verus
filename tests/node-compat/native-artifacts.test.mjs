import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { createRequire } from 'node:module';
import { copyFile, mkdir, mkdtemp, readFile, realpath, rename, rm, symlink, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import test from 'node:test';
import { nativeTargets, nativeTargetFor, selectNativeArtifact, sourceDigest, verifyNativeManifest } from '../../packages/compat-cordis/native-artifacts.js';
import { assembleNativeBundle } from '../../scripts/package-native.mjs';
import { writeNativeManifest } from '../../scripts/write-native-manifest.mjs';
const hash=value=>createHash('sha256').update(value).digest('hex');
const json=value=>JSON.stringify(value,null,2)+'\n';
const version=JSON.parse(await readFile(new URL('../../packages/compat-cordis/package.json',import.meta.url))).version;
// Deliberately non-executable fixtures: these test metadata integrity, never claim host loading.
async function fixture(t,target=nativeTargets[0],source='same source') {
  const root=await realpath(await mkdtemp(join(tmpdir(),'cordis-native-manifest-test-')));
  t.after(()=>rm(root,{recursive:true,force:true}));
  const directory=join(root,'native'); await mkdir(join(directory,'provenance'),{recursive:true});
  const bytes=Buffer.from('synthetic test bytes '+target.id), sources={'Cargo.lock':hash('lock'),'toolchain.lock.json':hash('toolchain'),'source.rs':hash(source)};
  const provenance={schema:'cordis-verus.native-provenance/v1',status:'host-load-passed',artifactKind:'default-core',target:target.id,artifactSha256:hash(bytes),factories:[],
    binding:{abi:1,package:'cordis-node',version,profile:'cordis-4.0.0-rc.10-experimental',values:'javascript-object-table'},
    build:{reportSha256:hash('build report'),sourceHashes:sources,sourceDigest:sourceDigest(sources),cargoLockSha256:sources['Cargo.lock'],toolchainLockSha256:sources['toolchain.lock.json']},
    validation:{platform:target.platform,architecture:target.architecture,libc:target.libc,node:'v22.22.0',nodeApi:10,nodeModuleAbi:127,osRelease:'synthetic-test',checkedAt:'2026-10-05T00:00:00Z',otherTargets:'not validated',uploaded:false}};
  const entry={target:target.id,platform:target.platform,architecture:target.architecture,libc:target.libc,nodeApi:8,kind:'default-core',file:'cordis.node',sha256:hash(bytes),bytes:bytes.length,provenance:'provenance/'+target.id+'.json',provenanceSha256:hash(json(provenance))};
  const manifest={schema:'cordis-verus.native-manifest/v1',package:'@cordis-verus/compat-cordis',version,driverAbi:1,artifacts:[entry]};
  await writeFile(join(directory,'cordis.node'),bytes);
  async function save() { entry.provenanceSha256=hash(json(provenance)); await writeFile(join(directory,entry.provenance),json(provenance)); await writeFile(join(directory,'manifest.json'),json(manifest)); }
  await save(); return {root,directory,bytes,target,entry,manifest,provenance,save};
}
const rejectsCode=(fn,code)=>assert.throws(fn,error=>error.code===code);
test('native manifest selects exact target and retains only its recorded validation',async t=>{
  const f=await fixture(t); const selected=selectNativeArtifact({directory:f.directory,target:{...f.target,nodeApi:10}});
  assert.equal(selected.path,join(f.directory,'cordis.node'));
  assert.equal(selected.provenance.validation.otherTargets,'not validated');
  assert.equal(selected.manifestSha256,hash(await readFile(join(f.directory,'manifest.json'))));
  assert.equal(verifyNativeManifest(f.directory).artifacts.length,1);
  rejectsCode(()=>selectNativeArtifact({directory:f.directory,target:nativeTargets[1]}),'NATIVE_ARTIFACT_MISSING');
});
test('native selector rejects undeclared platform, architecture, libc and old Node API',()=>{
  for(const target of [{platform:'win32',architecture:'x64',nodeApi:10},{platform:'linux',architecture:'arm64',libc:'gnu',nodeApi:10},{platform:'linux',architecture:'x64',libc:'musl',nodeApi:10}]) rejectsCode(()=>nativeTargetFor(target),'NATIVE_TARGET_UNSUPPORTED');
  rejectsCode(()=>nativeTargetFor({...nativeTargets[0],nodeApi:7}),'NATIVE_NODE_API');
});
test('binary and provenance byte tampering fail before native loading',async t=>{
  const f=await fixture(t); await writeFile(join(f.directory,'cordis.node'),'corrupt');
  rejectsCode(()=>verifyNativeManifest(f.directory),'NATIVE_INTEGRITY');
  await writeFile(join(f.directory,'cordis.node'),f.bytes);
  await writeFile(join(f.directory,f.entry.provenance),'{}');
  rejectsCode(()=>verifyNativeManifest(f.directory),'NATIVE_INTEGRITY');
});
test('manifest rejects ambiguous target, version, path traversal and missing artifact',async t=>{
  const f=await fixture(t); f.manifest.artifacts.push({...f.entry}); await f.save();
  rejectsCode(()=>verifyNativeManifest(f.directory),'NATIVE_MANIFEST_INVALID');
  f.manifest.artifacts.pop(); f.manifest.version='999'; await f.save();
  rejectsCode(()=>verifyNativeManifest(f.directory),'NATIVE_MANIFEST_INVALID');
  f.manifest.version=version; f.entry.file='../outside.node'; await f.save();
  rejectsCode(()=>verifyNativeManifest(f.directory),'NATIVE_MANIFEST_INVALID');
  f.entry.file='missing.node'; await f.save();
  rejectsCode(()=>selectNativeArtifact({directory:f.directory,target:f.target}),'NATIVE_ARTIFACT_MISSING');
});
test('native artifact symlinks are rejected even when target bytes match',async t=>{
  const f=await fixture(t); await writeFile(join(f.root,'outside.node'),f.bytes); await rm(join(f.directory,'cordis.node'));
  await symlink(join(f.root,'outside.node'),join(f.directory,'cordis.node'));
  rejectsCode(()=>verifyNativeManifest(f.directory),'NATIVE_ARTIFACT_SYMLINK');
});
test('custom SDK factories and overstated or incomplete build provenance are rejected',async t=>{
  const changes=[p=>p.factories.push({name:'custom'}),p=>p.validation.uploaded=true,p=>p.validation.otherTargets='verified',p=>p.build.sourceDigest=hash('changed'),p=>delete p.build.sourceHashes['Cargo.lock'],p=>p.validation.libc='wrong'];
  for(const change of changes) { const f=await fixture(t); change(f.provenance); await f.save(); rejectsCode(()=>verifyNativeManifest(f.directory),'NATIVE_PROVENANCE'); }
});
test('local bundle combines distinct verified target bytes without executing foreign artifacts',async t=>{
  const a=await fixture(t), b=await fixture(t,nativeTargets[2]);
  const output=join(a.root,'bundle'); const bundle=await assembleNativeBundle([a.directory,b.directory],output);
  assert.equal(bundle.artifacts.length,2);
  for(const f of [a,b]) { const selected=selectNativeArtifact({directory:output,target:f.target}); assert.deepEqual(await readFile(selected.path),f.bytes); assert.equal(selected.provenance.validation.osRelease,'synthetic-test'); assert.match(selected.entry.file,/^prebuilds\//); }
  await assert.rejects(assembleNativeBundle([a.directory],output),/already exists/);
});
test('local bundle rejects mixed source snapshots, duplicate targets and overlapping outputs',async t=>{
  const a=await fixture(t), b=await fixture(t,nativeTargets[2],'different source');
  await assert.rejects(assembleNativeBundle([a.directory,b.directory],join(a.root,'different')),/different source/);
  await assert.rejects(assembleNativeBundle([a.directory,a.directory],join(a.root,'duplicate')),/Duplicate native/);
  await assert.rejects(assembleNativeBundle([a.directory],join(a.directory,'..looks-outside')),/overlap/);
  await assert.rejects(assembleNativeBundle([a.directory],a.root),/overlap/);
});

test('manifest writer cannot certify changed bytes through an old require-cache binding',async t=>{
  const root=await realpath(await mkdtemp(join(tmpdir(),'cordis-native-cache-test-')));
  t.after(()=>rm(root,{recursive:true,force:true}));
  const directory=join(root,'packages/compat-cordis/native'); await mkdir(directory,{recursive:true});
  const addon=join(directory,'cordis.node');
  await copyFile(new URL('../../packages/compat-cordis/native/cordis.node',import.meta.url),addon);
  const loaded=createRequire(import.meta.url)(addon);
  assert.equal(JSON.parse(loaded.bindingInfo()).abi,1);
  // Rename prevents altering the image already memory-mapped by the loader.
  const corrupt=Buffer.from('this is not a native binary');
  await writeFile(join(directory,'replacement.node'),corrupt);
  await rename(join(directory,'replacement.node'),addon);
  const sources={'Cargo.lock':hash('lock'),'toolchain.lock.json':hash('toolchain')};
  const build={schema:'cordis-verus.node-build/v1',platform:process.platform,architecture:process.arch,node:process.version,
    sourceHashes:sources,artifactSha256:hash(corrupt),cargoLockSha256:sources['Cargo.lock'],toolchainLockSha256:sources['toolchain.lock.json']};
  const buildPath=join(root,'build.json'); await writeFile(buildPath,json(build));
  await writeFile(join(directory,'manifest.json'),'stale success');
  assert.throws(()=>writeNativeManifest(root,buildPath),/Fresh native artifact load failed/);
  await assert.rejects(readFile(join(directory,'manifest.json')),error=>error.code==='ENOENT');
});
test('manifest writer rejects metadata symlinks before touching outside canaries',async t=>{
  for(const kind of ['directory','file','manifest']) {
    const root=await realpath(await mkdtemp(join(tmpdir(),'cordis-native-symlink-test-')));
    t.after(()=>rm(root,{recursive:true,force:true}));
    const directory=join(root,'packages/compat-cordis/native'), outside=join(root,'outside');
    await mkdir(directory,{recursive:true}); await mkdir(outside);
    const target=nativeTargetFor(), name=target.id+'.json', canary=join(outside,name);
    await writeFile(canary,'unchanged canary');
    const addon=join(directory,'cordis.node');
    await copyFile(new URL('../../packages/compat-cordis/native/cordis.node',import.meta.url),addon);
    if(kind==='directory') await symlink(outside,join(directory,'provenance'));
    else if(kind==='file') { await mkdir(join(directory,'provenance')); await symlink(canary,join(directory,'provenance',name)); }
    else await symlink(canary,join(directory,'manifest.json'));
    const bytes=await readFile(addon), build={schema:'cordis-verus.node-build/v1',platform:process.platform,architecture:process.arch,node:process.version,artifactSha256:hash(bytes)};
    const buildPath=join(root,'build.json'); await writeFile(buildPath,json(build));
    assert.throws(()=>writeNativeManifest(root,buildPath),/cannot be a symlink/);
    assert.equal(await readFile(canary,'utf8'),'unchanged canary');
  }
});
