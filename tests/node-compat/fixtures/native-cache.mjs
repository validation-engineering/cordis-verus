// Run in a disposable process: Windows keeps a loaded native image locked.
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { createRequire } from 'node:module';
import { copyFile, mkdir, readFile, rename, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { writeNativeManifest } from '../../../scripts/write-native-manifest.mjs';
const hash=value=>createHash('sha256').update(value).digest('hex');
const json=value=>JSON.stringify(value,null,2)+'\n';
const root=process.argv[2];
const directory=join(root,'packages/compat-cordis/native'); await mkdir(directory,{recursive:true});
const addon=join(directory,'cordis.node');
const require=createRequire(import.meta.url);
// Windows locks a loaded DLL against replacement. Keep that real binding in
// a separate file, then seed its cached Module under the candidate filename.
// Unix can exercise the same stale-cache condition through an actual rename.
const loadedPath=process.platform==='win32'?join(directory,'cached.node'):addon;
await copyFile(new URL('../../../packages/compat-cordis/native/cordis.node',import.meta.url),loadedPath);
const loaded=require(loadedPath);
assert.equal(JSON.parse(loaded.bindingInfo()).abi,1);
// Never modify the bytes of an image already memory-mapped by the loader.
const corrupt=Buffer.from('this is not a native binary');
await writeFile(join(directory,'replacement.node'),corrupt);
await rename(join(directory,'replacement.node'),addon);
if(loadedPath!==addon) require.cache[addon]=require.cache[loadedPath];
assert.equal(require(addon),loaded, 'The stale cache would accept these corrupt bytes');
const sources={'Cargo.lock':hash('lock'),'toolchain.lock.json':hash('toolchain')};
const build={schema:'cordis-verus.node-build/v1',platform:process.platform,architecture:process.arch,node:process.version,
  sourceHashes:sources,artifactSha256:hash(corrupt),cargoLockSha256:sources['Cargo.lock'],toolchainLockSha256:sources['toolchain.lock.json']};
const buildPath=join(root,'build.json'); await writeFile(buildPath,json(build));
await writeFile(join(directory,'manifest.json'),'stale success');
assert.throws(()=>writeNativeManifest(root,buildPath),/Fresh native artifact load failed/);
await assert.rejects(readFile(join(directory,'manifest.json')),error=>error.code==='ENOENT');
