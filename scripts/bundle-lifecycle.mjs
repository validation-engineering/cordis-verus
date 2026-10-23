import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFile,writeFile,mkdir} from 'node:fs/promises';
import {spawnSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';
import path from 'node:path';
import {build,version} from 'esbuild';
const root=fileURLToPath(new URL('../',import.meta.url));
const output=path.join(root,'target/lifecycle-campaign/node');
const digest=async file=>createHash('sha256').update(await readFile(path.resolve(root,file))).digest('hex');
const lock=JSON.parse(await readFile(path.join(root,'upstream.lock.json'),'utf8'));
const upstream=lock.repositories.cordis;
function git(args) {
  const r=spawnSync('git',['-C',upstream.path,...args],{cwd:root,encoding:'utf8',timeout:30000});
  assert.equal(r.status,0,r.stderr); return r.stdout.trim();
}
assert.equal(git(['rev-parse','HEAD']),upstream.revision);
assert.equal(git(['rev-parse','HEAD^{tree}']),upstream.tree);
assert.equal(git(['status','--porcelain=v1','--untracked-files=all']),'');
await mkdir(output,{recursive:true});
const nativeBuild=JSON.parse(await readFile(path.join(root,'target/node-compat/build.json'),'utf8'));
assert.equal(await digest('packages/compat-cordis/native/cordis.node'),nativeBuild.artifactSha256);
for(const [file,hash] of Object.entries(nativeBuild.sourceHashes)) assert.equal(await digest(file),hash,`Rebuild stale native addon: ${file}`);
const report={schema:'cordis-verus.lifecycle-bundles/v1',node:process.version,esbuild:version,
  upstream,nativeBuild,inputs:{},artifacts:{}};
for(const backend of ['native','upstream']) {
  const outfile=path.join(output,`${backend}.mjs`);
  const result=await build({absWorkingDir:root,entryPoints:['tests/compat/lifecycle-scenario.mjs'],outfile,
    bundle:true,format:'esm',platform:'node',target:'node22',metafile:true,
    alias:{cosmokit:path.join(root,'node_modules/cosmokit/lib/index.mjs')},
    plugins:[{name:'cordis-profile',setup(builder){builder.onResolve({filter:/^cordis$/},()=>({
      path:path.join(root,backend==='upstream' ? `${upstream.path}/packages/core/src/index.ts` : 'packages/compat-cordis/index.js'),
      external:backend==='native',
    }));}}]});
  for(const file of Object.keys(result.metafile.inputs)) report.inputs[file]=await digest(file);
  if(backend==='native') assert(!Object.keys(result.metafile.inputs).some(file=>file.includes('/core/src/fiber.')));
  report.artifacts[backend]={path:outfile,sha256:await digest(outfile)};
}
await writeFile(path.join(output,'bundles.json'),JSON.stringify(report,null,2)+'\n');
console.log('Built source-bound lifecycle comparison bundles');
