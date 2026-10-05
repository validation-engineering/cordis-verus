// Full behavioral conformance run; failed cases are evidence, never skipped.
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFile, readdir, mkdir, writeFile, unlink} from 'node:fs/promises';
import {spawnSync} from 'node:child_process';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {installedDependencyEvidence} from '../tests/upstream-core/evidence.mjs';

const root = fileURLToPath(new URL('../', import.meta.url));
const output = path.join(root, 'target/upstream-core');
const digest = value => createHash('sha256').update(value).digest('hex');
const hash = async name => digest(await readFile(path.resolve(root, name)));
const args = process.argv.slice(2);
assert(args.length <= 1 && args.every(arg => /^--backend=(upstream|native|all)$/.test(arg)), 'Usage: check-upstream-core.mjs [--backend=upstream|native|all]');
const requested = args[0]?.split('=')[1] ?? 'all';
await mkdir(output, {recursive: true});
const reportPath = path.join(output, `${requested}.json`);
await unlink(reportPath).catch(error => { if (error.code !== 'ENOENT') throw error; });
const lock = JSON.parse(await readFile(path.join(root, 'upstream.lock.json'), 'utf8'));
const upstream = lock.repositories.cordis;
function git(args) {
  const result = spawnSync('git', ['-C', upstream.path, ...args], {cwd: root, encoding: 'utf8'});
  assert.equal(result.status, 0, result.stderr);
  return result.stdout.trim();
}
function checkUpstream() {
  assert.equal(git(['rev-parse', 'HEAD']), upstream.revision, 'Wrong upstream revision');
  assert.equal(git(['rev-parse', 'HEAD^{tree}']), upstream.tree, 'Wrong upstream tree');
  assert.equal(git(['status', '--porcelain=v1', '--untracked-files=all']), '', 'Upstream source or tests changed');
}
checkUpstream();
const testDirectory = path.join(upstream.path, 'packages/core/tests');
const suites = (await readdir(path.join(root, testDirectory))).filter(name => name.endsWith('.spec.ts')).sort();
assert.equal(suites.length, 12, 'Re-audit suite discovery when the locked upstream changes');
const report = {
  schema: 'cordis-verus.upstream-core/v1',
  profile: {name: 'cordis', version: '4.0.0-rc.10', revision: upstream.revision, tree: upstream.tree},
  node: process.version, runner: {name: 'vitest', version: JSON.parse(await readFile(path.join(root, 'node_modules/vitest/package.json'), 'utf8')).version},
  upstreamSuiteCount: suites.length, sourceEdits: false, traceNormalization: 'none',
  typeOnlyTestsIncluded: false, inputs: {}, installedDependencies:await installedDependencyEvidence(root), runs: {}, status: 'running',
};
for (const name of ['upstream.lock.json', 'package-lock.json', 'scripts/check-upstream-core.mjs', 'tests/upstream-core/vitest.config.mjs','tests/upstream-core/evidence.mjs']) report.inputs[name] = await hash(name);
for (const relative of git(['ls-files', 'packages/core/src', 'packages/core/tests']).split('\n').filter(Boolean)) {
  const name = `${upstream.path}/${relative}`;
  report.inputs[name] = await hash(name);
}
const selected = requested === 'all' ? ['upstream', 'native'] : [requested];
if (selected.includes('native')) {
  for (const file of await readdir(path.join(root, 'packages/compat-cordis'))) {
    if (/\.(?:js|cjs|json)$/.test(file)) {
      const name = `packages/compat-cordis/${file}`;
      report.inputs[name] = await hash(name);
    }
  }
  report.inputs['packages/compat-cordis/native/cordis.node'] = await hash('packages/compat-cordis/native/cordis.node');
  const nativeBuild=JSON.parse(await readFile(path.join(root,'target/node-compat/build.json'),'utf8'));
  assert.equal(nativeBuild.artifactSha256,report.inputs['packages/compat-cordis/native/cordis.node'],'Rebuild native addon');
  assert(nativeBuild.sourceHashes && Object.keys(nativeBuild.sourceHashes).length,'Missing native source evidence');
  for(const [name,expected] of Object.entries(nativeBuild.sourceHashes)) {assert.equal(await hash(name),expected,`Stale addon source: ${name}`);report.inputs[name]=expected;}
  report.nativeBuild=nativeBuild;
}
for (const backend of selected) {
  const resultPath = path.join(output, `${backend}.vitest.json`);
  await unlink(resultPath).catch(error => { if (error.code !== 'ENOENT') throw error; });
  const invocation = ['node_modules/vitest/vitest.mjs', 'run', '--config', 'tests/upstream-core/vitest.config.mjs', '--reporter=json', `--outputFile=${resultPath}`];
  console.log(`Running ${suites.length} unchanged upstream core suites against ${backend}...`);
  const result = spawnSync(process.execPath, invocation, {
    cwd: root, env: {...process.env, CORDIS_CORE_BACKEND: backend}, encoding: 'utf8',
    timeout: 300000, maxBuffer: 32 * 1024 * 1024,
  });
  await writeFile(path.join(output, `${backend}.log`), (result.stdout ?? '') + (result.stderr ?? ''));
  let parsed;
  try { parsed = JSON.parse(await readFile(resultPath, 'utf8')); } catch {}
  const run = {
    exitCode: result.status, signal: result.signal, processError: result.error?.message,
    passed: parsed?.numPassedTests ?? 0, failed: parsed?.numFailedTests ?? 0,
    pending: parsed?.numPendingTests ?? 0, todo: parsed?.numTodoTests ?? 0,
    total: parsed?.numTotalTests ?? 0,
    unhandledErrors: parsed?.unhandledErrors ?? [],
    suites: (parsed?.testResults ?? []).map(suite => ({
      file: path.relative(root, suite.name), status: suite.status, message: suite.message,
      cases: suite.assertionResults.map(test => ({name: test.fullName, status: test.status, failures: test.failureMessages})),
    })),
  };
  run.status = result.status === 0 && run.failed === 0 && run.total > 0 && run.pending === 0 && run.todo === 0 && run.suites.length === suites.length && run.unhandledErrors.length === 0 ? 'passed' : 'failed';
  report.runs[backend] = run;
  console.log(`${backend}: ${run.passed}/${run.total} passed, ${run.failed} failed, ${run.pending} pending; ${run.status}`);
}
checkUpstream();
for (const [name, expected] of Object.entries(report.inputs)) assert.equal(await hash(name), expected, `Input changed during run: ${name}`);
assert.deepEqual(await installedDependencyEvidence(root),report.installedDependencies,'Installed runner dependencies changed during run');
report.status = Object.values(report.runs).every(run => run.status === 'passed') ? 'passed' : 'failed';
await writeFile(reportPath, JSON.stringify(report, null, 2) + '\n');
console.log(`Full core report: ${path.relative(root, reportPath)}`);
process.exitCode = report.status === 'passed' ? 0 : 1;
