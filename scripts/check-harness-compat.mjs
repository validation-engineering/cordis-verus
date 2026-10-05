// Execute the unchanged locked Harness services and tool against both Cordis
// implementations. No rewritten source, omitted failure, or normalized trace.
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFile,readdir,mkdir,writeFile,unlink,access} from 'node:fs/promises';
import {spawnSync} from 'node:child_process';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {installedDependencyEvidence} from '../tests/upstream-core/evidence.mjs';

const root=fileURLToPath(new URL('../',import.meta.url));
const output=path.join(root,'target/harness-compat');
const selection=process.argv[2]?.replace(/^--backend=/,'')??'all';
assert(process.argv.length<=3 && ['all','upstream','native'].includes(selection),
  'Usage: check-harness-compat.mjs [--backend=upstream|native|all]');
const backends=selection==='all'?['upstream','native']:[selection];
const reportPath=path.join(output,`${selection}.json`);
const digest=value=>createHash('sha256').update(value).digest('hex');
const hash=async name=>digest(await readFile(path.resolve(root,name)));
await mkdir(path.join(output,'bundles'),{recursive:true});
await unlink(reportPath).catch(error=>{if(error.code!=='ENOENT')throw error;});
let report;
let phase='preflight';
try {
const {build,version:esbuild}=await import('esbuild');
const lock=JSON.parse(await readFile(path.join(root,'upstream.lock.json'),'utf8'));
const repository=lock.repositories.deepseekHarness;
function git(args) {
  const result=spawnSync('git',['-C',repository.path,...args],{cwd:root,encoding:'utf8'});
  assert.equal(result.status,0,result.stderr);
  return result.stdout.trim();
}
function checkUpstream() {
  assert.equal(git(['rev-parse','HEAD']),repository.revision);
  assert.equal(git(['rev-parse','HEAD^{tree}']),repository.tree);
  assert.equal(git(['status','--porcelain=v1','--untracked-files=all']),'');
}
checkUpstream();
report={
  schema:'cordis-verus.real-harness-compat/v1',node:process.version,esbuild,
  upstream:{revision:repository.revision,tree:repository.tree},
  selection,normalization:'none',conformanceClaim:false,
  scope:'Real SessionStore, SystemPrompt, ToolRuntime, SessionProjectionRegistry, tool-todo, scope; minimal agent id/session data only; no LLM/provider/network requests.',
  observations:'Ordered API outcomes, schemas, tool results, event type/data/seq, projection snapshots, scoped admission and cleanup. Deliberately excludes wall-clock metadata; no post-run trace transformations.',
  installedDependencies:await installedDependencyEvidence(root),inputs:{},resolvedPackages:{},bundles:{},scenarios:{},status:'running',
};
async function addInput(name) {
  name=path.relative(root,path.resolve(root,name));
  const actual=await hash(name);
  if(report.inputs[name])assert.equal(actual,report.inputs[name],`Input changed while bundling: ${name}`);
  else report.inputs[name]=actual;
}
for(const name of ['upstream.lock.json','package.json','package-lock.json','scripts/check-harness-compat.mjs',
  'tests/compat/harness/fixture.mjs','tests/upstream-core/evidence.mjs','tests/compat/profiles/deepseek-harness.json'])await addInput(name);
if(backends.includes('native')) {
  for(const directory of ['packages/compat-cordis','packages/compat-harness']) {
    for(const file of await readdir(path.join(root,directory)))if(/\.(js|cjs|json)$/.test(file))await addInput(`${directory}/${file}`);
  }
  await addInput('packages/compat-cordis/native/cordis.node');
  const evidence=JSON.parse(await readFile(path.join(root,'target/node-compat/build.json'),'utf8'));
  assert.equal(evidence.artifactSha256,report.inputs['packages/compat-cordis/native/cordis.node'],'Rebuild native addon');
  assert(evidence.sourceHashes && Object.keys(evidence.sourceHashes).length,'Missing native source evidence');
  for(const [name,expected] of Object.entries(evidence.sourceHashes)){
    assert.equal(await hash(name),expected,`Stale native addon: ${name}`);
    await addInput(name);
  }
  report.nativeBuild=evidence;
}

// Resolve workspace imports to their actual shipping source entry. This is
// necessary because the immutable checkout intentionally has no lib/ outputs.
// Fail closed on absent entries instead of supplying a replacement module.
const packages=new Map();
async function catalog(directory) {
  for(const entry of await readdir(directory,{withFileTypes:true})) {
    if(entry.name==='node_modules' || entry.name.startsWith('.'))continue;
    const location=path.join(directory,entry.name);
    if(entry.isDirectory())await catalog(location);
    else if(entry.name==='package.json') {
      const manifest=JSON.parse(await readFile(location,'utf8'));
      if(manifest.name?.startsWith('@deepseek-ai/')) {
        assert(!packages.has(manifest.name),`Duplicate workspace name: ${manifest.name}`);
        packages.set(manifest.name,{directory,manifest,path:location});
      }
    }
  }
}
await catalog(path.join(root,repository.path,'packages'));
await catalog(path.join(root,repository.path,'vendor'));
// LLM attribution reads ../package.json via createRequire(import.meta.url).
// Preserve that runtime-relative asset as the exact original manifest; do not
// rewrite the upstream attribution code or substitute a made-up version.
const llmManifest=path.join(repository.path,'packages/llm/llm/package.json');
await addInput(llmManifest);
await writeFile(path.join(output,'package.json'),await readFile(path.join(root,llmManifest)));
await addInput(path.join(output,'package.json'));
report.runtimeAssets={'target/harness-compat/package.json':llmManifest};
for(const backend of backends) {
  phase=`bundle:${backend}`;
  const outfile=path.join(output,'bundles',`${backend}.mjs`);
  const built=await build({
    absWorkingDir:root,entryPoints:['tests/compat/harness/fixture.mjs'],outfile,
    bundle:true,platform:'node',format:'esm',target:'node22',metafile:true,
    plugins:[{name:'locked-harness-workspace',setup(builder) {
      builder.onResolve({filter:/^@deepseek-ai\//},async args=>{
        if(args.path==='@deepseek-ai/cordis' && backend==='native') {
          return {path:path.join(root,'packages/compat-harness/index.js'),external:true};
        }
        const [,name,suffix]=args.path.match(/^(@deepseek-ai\/[^/]+)(?:\/(.*))?$/)??[];
        const entry=packages.get(name);
        assert(entry,`Unresolved real Harness package: ${args.path}`);
        await addInput(entry.path);
        let relative;
        if(!suffix)relative='src/index.ts';
        else if(suffix.startsWith('src/'))relative=suffix;
        else if(suffix==='package.json')relative=suffix;
        else {
          const exported=entry.manifest.exports?.[`./${suffix}`];
          const file=typeof exported==='string'?exported:exported?.default??exported?.import;
          assert(file?.startsWith('./lib/'),`Unsupported source export: ${args.path}`);
          relative=file.replace(/^\.\/lib\/(?:types\/)?/,'src/').replace(/\.[mc]?js$/,'.ts');
        }
        const resolved=path.join(entry.directory,relative);
        await access(resolved);
        report.resolvedPackages[args.path]=path.relative(root,resolved);
        return {path:resolved};
      });
    }}],
  });
  for(const name of [...Object.keys(built.metafile.inputs),outfile])await addInput(name);
  report.bundles[backend]={path:path.relative(root,outfile),inputs:Object.keys(built.metafile.inputs)};
  // Prevent an accidentally empty or substitute bundle from passing a trace.
  for(const required of [
    'packages/core/session/src/index.ts','packages/core/system-prompt/src/index.ts',
    'packages/core/tools/src/index.ts','packages/session/session-projection/src/index.ts',
    'packages/todo/tool-todo/src/index.ts','packages/core/scope/src/index.ts',
  ])assert(Object.hasOwn(built.metafile.inputs,`${repository.path}/${required}`),`Missing real module: ${required}`);
  for(const scenario of ['global','scoped']) {
    phase=`execute:${backend}/${scenario}`;
    const run=spawnSync(process.execPath,[outfile],{
      cwd:root,encoding:'utf8',timeout:30000,maxBuffer:8*1024*1024,
      env:{...process.env,CORDIS_HARNESS_SCENARIO:scenario},
    });
    const result={exitCode:run.status,signal:run.signal,error:run.error?.message,stderr:run.stderr};
    try {result.observation=JSON.parse(run.stdout);}catch{result.stdout=run.stdout;}
    (report.scenarios[scenario]??={runs:{}}).runs[backend]=result;
    console.log(`${backend}/${scenario}: ${run.status===0 && result.observation?.status==='passed'?'passed':'failed'}`);
  }
}
for(const [scenario,result] of Object.entries(report.scenarios)) {
  try {
    for(const backend of backends) {
      assert.equal(result.runs[backend].exitCode,0,`${backend}/${scenario} process failed`);
      assert.equal(result.runs[backend].observation?.status,'passed',`${backend}/${scenario} semantic assertions failed`);
    }
    if(selection==='all')assert.deepEqual(result.runs.native.observation,result.runs.upstream.observation);
    result.status='passed';
  } catch(error) {result.status='failed';result.difference=error.message;}
}
phase='postflight';
checkUpstream();
for(const [name,expected] of Object.entries(report.inputs))assert.equal(await hash(name),expected,`Input changed during run: ${name}`);
assert.deepEqual(await installedDependencyEvidence(root),report.installedDependencies,'Installed dependencies changed during run');
report.status=Object.values(report.scenarios).every(result=>result.status==='passed')?'passed':'failed';
await writeFile(reportPath,JSON.stringify(report,null,2)+'\n');
console.log(`Harness evidence: ${path.relative(root,reportPath)} (${report.status})`);
process.exitCode=report.status==='passed'?0:1;

} catch(error) {
  report??={schema:'cordis-verus.real-harness-compat/v1',selection,conformanceClaim:false};
  report.status='failed';
  report.runnerFailure={phase,name:error.name,message:error.message};
  await writeFile(reportPath,JSON.stringify(report,null,2)+'\n');
  console.error(`Harness check failed during ${phase}: ${error.message}`);
  console.error(`Failure evidence: ${path.relative(root,reportPath)}`);
  process.exitCode=1;
}
