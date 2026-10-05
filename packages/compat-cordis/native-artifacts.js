// Hashes bind local bytes to their recorded build inputs; they are not signatures.
import { createHash } from 'node:crypto';
import { lstatSync, readFileSync, realpathSync } from 'node:fs';
import { dirname, isAbsolute, join, relative, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const packageRoot = dirname(fileURLToPath(import.meta.url));
const packageVersion = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8')).version;
export const nativeTargets = Object.freeze([
  Object.freeze({ id:'darwin-arm64-napi8', platform:'darwin', architecture:'arm64', libc:null, nodeApi:8 }),
  Object.freeze({ id:'darwin-x64-napi8', platform:'darwin', architecture:'x64', libc:null, nodeApi:8 }),
  Object.freeze({ id:'linux-x64-gnu-napi8', platform:'linux', architecture:'x64', libc:'gnu', nodeApi:8 }),
]);
export class NativeArtifactError extends Error {
  constructor(code, message, cause) { super(message, cause ? {cause} : undefined); this.name='NativeArtifactError'; this.code=code; }
}
const fail = (code, message) => { throw new NativeArtifactError(code, message); };
const digest = bytes => createHash('sha256').update(bytes).digest('hex');
const hashPattern = /^[a-f0-9]{64}$/;
const object = value => value && typeof value==='object' && !Array.isArray(value);
export const sourceDigest = hashes => digest(JSON.stringify(Object.fromEntries(Object.entries(hashes).sort(([a],[b])=>a<b?-1:a>b?1:0))));
export function currentNativeTarget() {
  return { platform:process.platform, architecture:process.arch,
    libc:process.platform==='linux' ? process.report.getReport().header.glibcVersionRuntime ? 'gnu' : 'musl' : null,
    nodeApi:Number(process.versions.napi) };
}
export function nativeTargetFor(target = currentNativeTarget()) {
  const match=nativeTargets.find(item=>item.platform===target.platform && item.architecture===target.architecture && item.libc===(target.libc??null));
  if (!match) fail('NATIVE_TARGET_UNSUPPORTED', `No declared native target for ${target.platform}/${target.architecture}/${target.libc??'none'}`);
  if (!Number.isInteger(target.nodeApi) || target.nodeApi<match.nodeApi) fail('NATIVE_NODE_API', `Native target requires Node-API ${match.nodeApi}; runtime has ${target.nodeApi}`);
  return match;
}
function safeRelative(name) {
  return typeof name==='string' && !!name && !name.includes('\\') && !isAbsolute(name)
    && !name.split('/').some(part=>!part || part==='.' || part==='..');
}
function checkedFile(directory, name) {
  if (!safeRelative(name)) fail('NATIVE_MANIFEST_INVALID', `Unsafe native artifact path: ${name}`);
  let cursor=directory;
  for (const part of name.split('/')) {
    cursor=join(cursor,part);
    if (lstatSync(cursor).isSymbolicLink()) fail('NATIVE_ARTIFACT_SYMLINK', `Native artifact paths cannot contain symlinks: ${name}`);
  }
  if (!lstatSync(cursor).isFile()) fail('NATIVE_MANIFEST_INVALID', `Native artifact is not a regular file: ${name}`);
  const location=relative(directory,realpathSync(cursor));
  if (isAbsolute(location) || location==='..' || location.startsWith('../')) fail('NATIVE_MANIFEST_INVALID', `Native artifact escapes its package: ${name}`);
  return cursor;
}
function jsonFile(path) {
  try { return JSON.parse(readFileSync(path,'utf8')); }
  catch (cause) { throw new NativeArtifactError('NATIVE_MANIFEST_INVALID', `Cannot read native metadata ${path}`,cause); }
}
/** Verify all listed artifacts without loading or claiming to execute foreign binaries. */
export function verifyNativeManifest(directory = join(packageRoot,'native')) {
  directory=resolve(directory);
  if (lstatSync(directory).isSymbolicLink()) fail('NATIVE_ARTIFACT_SYMLINK','Native artifact directory cannot be a symlink');
  directory=realpathSync(directory);
  const manifestPath=checkedFile(directory,'manifest.json');
  const manifest=jsonFile(manifestPath);
  if (!object(manifest) || manifest.schema!=='cordis-verus.native-manifest/v1'
    || manifest.package!=='@cordis-verus/compat-cordis' || manifest.version!==packageVersion || manifest.driverAbi!==1
    || !Array.isArray(manifest.artifacts) || !manifest.artifacts.length) fail('NATIVE_MANIFEST_INVALID','Unsupported or incomplete native manifest');
  const seen=new Set(), artifacts=[];
  for (const entry of manifest.artifacts) {
    const declared=nativeTargets.find(item=>item.id===entry?.target);
    if (!declared || seen.has(entry.target) || entry.platform!==declared.platform || entry.architecture!==declared.architecture
      || entry.libc!==declared.libc || entry.nodeApi!==declared.nodeApi || entry.kind!=='default-core'
      || !hashPattern.test(entry.sha256) || !hashPattern.test(entry.provenanceSha256)
      || !Number.isSafeInteger(entry.bytes) || entry.bytes<=0) fail('NATIVE_MANIFEST_INVALID','Invalid, duplicate, or non-default native artifact');
    seen.add(entry.target);
    const path=checkedFile(directory,entry.file), bytes=readFileSync(path);
    if (bytes.length!==entry.bytes || digest(bytes)!==entry.sha256) fail('NATIVE_INTEGRITY',`Native binary changed: ${entry.file}`);
    const provenancePath=checkedFile(directory,entry.provenance), provenanceBytes=readFileSync(provenancePath);
    if (digest(provenanceBytes)!==entry.provenanceSha256) fail('NATIVE_INTEGRITY',`Native provenance changed: ${entry.provenance}`);
    const provenance=jsonFile(provenancePath);
    if (!object(provenance)) fail('NATIVE_PROVENANCE','Native provenance must be an object');
    const build=provenance.build, validation=provenance.validation;
    if (provenance.schema!=='cordis-verus.native-provenance/v1' || provenance.status!=='host-load-passed'
      || provenance.artifactKind!=='default-core' || provenance.target!==entry.target || provenance.artifactSha256!==entry.sha256
      || provenance.binding?.abi!==1 || provenance.binding?.package!=='cordis-node' || provenance.binding?.version!==manifest.version
      || provenance.binding?.profile!=='cordis-4.0.0-rc.10-experimental' || provenance.binding?.values!=='javascript-object-table'
      || !Array.isArray(provenance.factories) || provenance.factories.length
      || !object(build?.sourceHashes) || !Object.keys(build.sourceHashes).length
      || Object.entries(build.sourceHashes).some(([name,hash])=>!safeRelative(name)||!hashPattern.test(hash))
      || build.sourceDigest!==sourceDigest(build.sourceHashes) || !hashPattern.test(build.reportSha256)
      || !hashPattern.test(build.cargoLockSha256) || !hashPattern.test(build.toolchainLockSha256)
      || build.cargoLockSha256!==build.sourceHashes['Cargo.lock'] || build.toolchainLockSha256!==build.sourceHashes['toolchain.lock.json']
      || validation?.platform!==entry.platform || validation?.architecture!==entry.architecture || validation?.libc!==entry.libc
      || !Number.isInteger(validation?.nodeApi) || validation.nodeApi<entry.nodeApi || !/^v\d+\.\d+\.\d+/.test(validation?.node??'')
      || !Number.isInteger(validation?.nodeModuleAbi) || validation.nodeModuleAbi<=0 || typeof validation?.osRelease!=='string'
      || !Number.isFinite(Date.parse(validation?.checkedAt)) || validation?.otherTargets!=='not validated'
      || validation?.uploaded!==false) fail('NATIVE_PROVENANCE',`Incomplete or inconsistent default-core provenance: ${entry.provenance}`);
    artifacts.push({entry,path,provenance,provenancePath});
  }
  return {directory,manifest,manifestPath,manifestSha256:digest(readFileSync(manifestPath)),artifacts};
}
/** Same selection and integrity checks for a source checkout and installed package. */
export function selectNativeArtifact(options = {}) {
  const target=nativeTargetFor(options.target??currentNativeTarget());
  let verified;
  try { verified=verifyNativeManifest(options.directory); }
  catch (cause) {
    if (cause instanceof NativeArtifactError) throw cause;
    throw new NativeArtifactError('NATIVE_ARTIFACT_MISSING','Native manifest or binary is missing; build it with node scripts/build-node.mjs',cause);
  }
  const artifact=verified.artifacts.find(item=>item.entry.target===target.id);
  if (!artifact) fail('NATIVE_ARTIFACT_MISSING',`No locally validated artifact for ${target.id}; available: ${verified.artifacts.map(item=>item.entry.target).join(', ')}`);
  return {...artifact,manifest:verified.manifest,manifestSha256:verified.manifestSha256};
}
