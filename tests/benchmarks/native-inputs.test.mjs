import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdir,mkdtemp,readFile,rm,writeFile } from 'node:fs/promises';
import { dirname,join } from 'node:path';
import { tmpdir } from 'node:os';
import { collectInputs,nativeSourceInputs } from '../../scripts/benchmark/inputs.mjs';
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
