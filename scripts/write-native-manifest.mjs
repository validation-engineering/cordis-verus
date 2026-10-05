import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { lstatSync, mkdirSync, mkdtempSync, readFileSync, writeFileSync, renameSync, rmSync } from 'node:fs';
import { join } from 'node:path';
import { release, tmpdir } from 'node:os';
import { currentNativeTarget, nativeTargetFor, sourceDigest, verifyNativeManifest } from '../packages/compat-cordis/native-artifacts.js';
const digest = bytes => createHash('sha256').update(bytes).digest('hex');
const json = value => JSON.stringify(value,null,2)+'\n';

function rejectSymlink(path) {
  try { if(lstatSync(path).isSymbolicLink()) throw new Error('Native metadata path cannot be a symlink: '+path); }
  catch(error) { if(error.code!=='ENOENT') throw error; }
}
/** Called only after the actual host addon and isolated SDK fixture were loaded. */
export function writeNativeManifest(root, buildPath) {
  for(const suffix of ['', 'packages', 'packages/compat-cordis', 'packages/compat-cordis/native', 'packages/compat-cordis/native/provenance', 'packages/compat-cordis/native/manifest.json']) rejectSymlink(join(root,suffix));
  rmSync(join(root,'packages/compat-cordis/native/manifest.json'),{force:true});
  const reportBytes=readFileSync(buildPath), build=JSON.parse(reportBytes);
  const directory=join(root,'packages/compat-cordis/native'), path=join(directory,'cordis.node');
  const bytes=readFileSync(path), sha256=digest(bytes), target=currentNativeTarget(), declared=nativeTargetFor(target);
  if (build.schema!=='cordis-verus.node-build/v1' || build.platform!==target.platform || build.architecture!==target.architecture
    || build.node!==process.version || build.artifactSha256!==sha256) throw new Error('Native build report does not describe the current host artifact');
  const provenanceName=`provenance/${declared.id}.json`;
  rejectSymlink(path); rejectSymlink(join(directory,provenanceName));
  // A fresh process loads a private snapshot; require cache cannot certify new bytes.
  const temporary=mkdtempSync(join(tmpdir(),'cordis-native-build-'));
  let info;
  try {
    const snapshot=join(temporary,sha256+'.node');
    writeFileSync(snapshot,bytes,{mode:0o400});
    const script=`const fs=require('node:fs'); const crypto=require('node:crypto');
      const hash=()=>crypto.createHash('sha256').update(fs.readFileSync(process.argv[1])).digest('hex');
      const before=hash(); const binding=require(process.argv[1]);
      const driver=typeof binding.createDriver==='function'?binding.createDriver():new binding.NativeDriver();
      console.log(JSON.stringify({before,after:hash(),binding:JSON.parse(binding.bindingInfo()),sdk:JSON.parse(driver.rustInfo())}));`;
    const env={...process.env};
    for(const key of ['NODE_OPTIONS','NODE_PATH','CORDIS_NATIVE_BINDING']) delete env[key];
    const loaded=spawnSync(process.execPath,['--eval',script,snapshot],{env,encoding:'utf8',timeout:30000,maxBuffer:1024*1024});
    if(loaded.error) throw loaded.error;
    if(loaded.status!==0) throw new Error('Fresh native artifact load failed: '+loaded.stderr);
    const observation=JSON.parse(loaded.stdout.trim());
    if(observation.before!==sha256 || observation.after!==sha256 || digest(readFileSync(snapshot))!==sha256
      || digest(readFileSync(path))!==sha256) throw new Error('Native artifact changed during isolated loading');
    info=observation.binding;
    if(observation.sdk.abi!==1 || !Array.isArray(observation.sdk.factories) || observation.sdk.factories.length)
      throw new Error('Custom Rust SDK factories must never enter the default native distribution');
  } finally { rmSync(temporary,{recursive:true,force:true}); }
  const provenance={
    schema:'cordis-verus.native-provenance/v1',status:'host-load-passed',artifactKind:'default-core',target:declared.id,
    artifactSha256:sha256,binding:info,factories:[],
    build:{reportSha256:digest(reportBytes),sourceHashes:build.sourceHashes,sourceDigest:sourceDigest(build.sourceHashes),
      cargoLockSha256:build.cargoLockSha256,toolchainLockSha256:build.toolchainLockSha256,
      profile:build.compilerProfile??null,command:['cargo','build','--locked','-p','cordis-node','--lib','--examples']},
    validation:{platform:target.platform,architecture:target.architecture,libc:target.libc,node:process.version,
      nodeApi:target.nodeApi,nodeModuleAbi:Number(process.versions.modules),osRelease:release(),checkedAt:new Date().toISOString(),
      otherTargets:'not validated',uploaded:false},
  };
  const provenanceBytes=Buffer.from(json(provenance));
  mkdirSync(join(directory,'provenance'),{recursive:true});
  const manifest={schema:'cordis-verus.native-manifest/v1',package:'@cordis-verus/compat-cordis',version:info.version,driverAbi:1,
    artifacts:[{target:declared.id,platform:declared.platform,architecture:declared.architecture,libc:declared.libc,nodeApi:declared.nodeApi,
      kind:'default-core',file:'cordis.node',sha256,bytes:bytes.length,provenance:provenanceName,provenanceSha256:digest(provenanceBytes)}]};
  const staging=mkdtempSync(join(directory,'.manifest-'));
  try {
    writeFileSync(join(staging,'provenance.json'),provenanceBytes);
    writeFileSync(join(staging,'manifest.json'),json(manifest));
    rejectSymlink(join(directory,'provenance')); rejectSymlink(join(directory,provenanceName));
    rejectSymlink(join(directory,'manifest.json'));
    renameSync(join(staging,'provenance.json'),join(directory,provenanceName));
    renameSync(join(staging,'manifest.json'),join(directory,'manifest.json'));
    verifyNativeManifest(directory);
  } catch(error) { rmSync(join(directory,'manifest.json'),{force:true}); throw error; }
  finally { rmSync(staging,{recursive:true,force:true}); }
  return manifest;
}
