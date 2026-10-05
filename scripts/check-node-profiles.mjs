// Shared source, four real executions, strict trace comparison per profile.
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFile,readdir,mkdir,writeFile,unlink} from 'node:fs/promises';
import {spawnSync} from 'node:child_process';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {installedDependencyEvidence} from '../tests/upstream-core/evidence.mjs';

const root=fileURLToPath(new URL('../',import.meta.url));
const output=path.join(root,'target/node-compat');
const reportPath=path.join(output,'profiles.json');
const digest=value=>createHash('sha256').update(value).digest('hex');
const hash=async name=>digest(await readFile(path.resolve(root,name)));
assert.equal(process.argv.length,2,'Usage: check-node-profiles.mjs');
await mkdir(output,{recursive:true});
await unlink(reportPath).catch(error=>{if(error.code!=='ENOENT')throw error;});
const {build,version:esbuild}=await import('esbuild');
const lock=JSON.parse(await readFile(path.join(root,'upstream.lock.json'),'utf8'));
function git(repository,args){const r=spawnSync('git',['-C',repository.path,...args],{cwd:root,encoding:'utf8'});assert.equal(r.status,0,r.stderr);return r.stdout.trim();}
function checkUpstream(repository){assert.equal(git(repository,['rev-parse','HEAD']),repository.revision);assert.equal(git(repository,['rev-parse','HEAD^{tree}']),repository.tree);assert.equal(git(repository,['status','--porcelain=v1','--untracked-files=all']),'');}
const report={schema:'cordis-verus.node-profiles/v1',node:process.version,esbuild,normalization:'none',installedDependencies:await installedDependencyEvidence(root),inputs:{},profiles:{},status:'running'};
for(const name of ['upstream.lock.json','package-lock.json','scripts/check-node-profiles.mjs','tests/upstream-core/profile-fixture.mjs','tests/upstream-core/evidence.mjs','packages/compat-cordis/native/cordis.node'])report.inputs[name]=await hash(name);
for(const file of await readdir(path.join(root,'packages/compat-cordis')))if(/\.(js|cjs|json)$/.test(file)){const name=`packages/compat-cordis/${file}`;report.inputs[name]=await hash(name);}
const nativeBuild=JSON.parse(await readFile(path.join(output,'build.json'),'utf8'));
assert.equal(nativeBuild.artifactSha256,report.inputs['packages/compat-cordis/native/cordis.node'],'Rebuild native addon');
assert(nativeBuild.sourceHashes && Object.keys(nativeBuild.sourceHashes).length,'Missing native source evidence');
for(const [name,expected] of Object.entries(nativeBuild.sourceHashes)){assert.equal(await hash(name),expected,`Stale addon source: ${name}`);report.inputs[name]=expected;}
report.nativeBuild=nativeBuild;
for(const profile of ['cordis','harness']){
  const manifestPath=`tests/compat/profiles/${profile==='cordis'?'cordis':'deepseek-harness'}.json`;
  const manifest=JSON.parse(await readFile(path.join(root,manifestPath),'utf8'));
  report.inputs[manifestPath]=await hash(manifestPath);
  const repository=lock.repositories[manifest.upstreamRepository];
  assert.equal(repository.revision,manifest.revision);
  checkUpstream(repository);
  const results={profile:manifest,observations:{},runs:{},status:'running'};
  for(const backend of ['upstream','native']){
    const outfile=path.join(output,`profile-${profile}-${backend}.mjs`);
    const built=await build({
      absWorkingDir:root,entryPoints:['tests/upstream-core/profile-fixture.mjs'],outfile,bundle:true,platform:'node',format:'esm',target:'node22',metafile:true,
      alias:{cosmokit:path.join(root,'node_modules/cosmokit/lib/index.mjs'),'@deepseek-ai/cosmokit':path.join(root,'upstream/deepseek-harness/vendor/cosmokit/src/index.ts')},
      plugins:[{name:'selected-cordis-profile',setup(builder){builder.onResolve({filter:/^cordis$/},()=>({path:path.join(root,backend==='native'?'packages/compat-cordis/index.js':profile==='cordis'?'upstream/cordis/packages/core/src/index.ts':'upstream/deepseek-harness/vendor/cordis/src/index.ts'),external:backend==='native'}));}}],
    });
    for(const name of [...Object.keys(built.metafile.inputs),path.relative(root,outfile)]){const actual=await hash(name);if(report.inputs[name])assert.equal(actual,report.inputs[name]);else report.inputs[name]=actual;}
    const run=spawnSync(process.execPath,[outfile],{cwd:root,encoding:'utf8',timeout:30000,maxBuffer:4*1024*1024,env:{...process.env,CORDIS_PROFILE_FIXTURE_RUN:'1',CORDIS_PROFILE:profile}});
    results.runs[backend]={exitCode:run.status,signal:run.signal,error:run.error?.message,stderr:run.stderr};
    try {results.observations[backend]=JSON.parse(run.stdout);}catch{results.runs[backend].stdout=run.stdout;}
  }
  try {
    for(const backend of ['upstream','native']){assert.equal(results.runs[backend].exitCode,0,`${backend} fixture process failed`);assert(results.observations[backend],`${backend} fixture returned no trace`);}
    assert.deepEqual(results.observations.native,results.observations.upstream);
    results.status='passed';
  } catch(error) {results.status='failed';results.difference=error.message;}
  report.profiles[profile]=results;
  checkUpstream(repository);
  console.log(`${profile}: ${results.status}`);
}
for(const [name,expected] of Object.entries(report.inputs))assert.equal(await hash(name),expected,`Input changed during run: ${name}`);
assert.deepEqual(await installedDependencyEvidence(root),report.installedDependencies,'Installed test dependencies changed during run');
report.status=Object.values(report.profiles).every(profile=>profile.status==='passed')?'passed':'failed';
await writeFile(reportPath,JSON.stringify(report,null,2)+'\n');
console.log(`Profile evidence: ${path.relative(root,reportPath)}`);
process.exitCode=report.status==='passed'?0:1;
