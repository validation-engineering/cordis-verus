// Execute unchanged workloads against four actual runtime entries; retain raw traces.
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFile, readdir, mkdir, writeFile, unlink, realpath } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { createRequire } from 'node:module';
import { fileURLToPath, pathToFileURL } from 'node:url';
import path from 'node:path';
import os from 'node:os';

const here = path.resolve(fileURLToPath(new URL('../', import.meta.url)));
const args = process.argv.slice(2);
assert(args.length % 2 === 0 && args.every((value, index) => index % 2 !== 0 || ['--root', '--output'].includes(value)),
  'Usage: node scripts/reproduce-lifecycle-cases.mjs [--root PATH] [--output PATH]');
const option = (name, fallback) => {
  const index = args.indexOf(name);
  return index < 0 ? fallback : args[index + 1];
};
const root = path.resolve(option('--root', here));
const output = path.resolve(option('--output', path.join(root, 'target/lifecycle-cases')));
const fixture = path.join(here, 'tests/cases/lifecycle-fixture.mjs');
const require = createRequire(path.join(root, 'package.json'));
const { build, version: esbuild } = require('esbuild');
const { installedDependencyEvidence } = await import(pathToFileURL(path.join(root, 'tests/upstream-core/evidence.mjs')));
const digest = data => createHash('sha256').update(data).digest('hex');
const hash = async filename => digest(await readFile(filename));
const git = (cwd, ...gitArgs) => {
  const run = spawnSync('git', ['-C', cwd, ...gitArgs], { encoding: 'utf8' });
  assert.equal(run.status, 0, run.stderr);
  return run.stdout.trim();
};
const lock = JSON.parse(await readFile(path.join(root, 'upstream.lock.json'), 'utf8'));
const checkUpstream = repository => {
  const directory = path.join(root, repository.path);
  assert.equal(git(directory, 'rev-parse', '--show-toplevel'), directory);
  assert.equal(git(directory, 'rev-parse', 'HEAD'), repository.revision);
  assert.equal(git(directory, 'rev-parse', 'HEAD^{tree}'), repository.tree);
  assert.equal(git(directory, 'status', '--porcelain=v1', '--untracked-files=all'), '');
};
await mkdir(output, { recursive: true });
await unlink(path.join(output, 'report.json')).catch(error => { if (error.code !== 'ENOENT') throw error; });
const report = {
  schema: 'cordis-verus.lifecycle-cases/v1', checkedAt: new Date().toISOString(),
  environment: { node: process.version, platform: process.platform, arch: process.arch, osRelease: os.release(), nodeComponents: process.versions, cpu: os.cpus()[0]?.model, esbuild },
  repository: { commit: git(root, 'rev-parse', 'HEAD'), workingTree: git(root, 'status', '--porcelain=v1', '--untracked-files=all') },
  classification: 'Pinned-version behavioral comparison; not a latest-upstream claim or release acceptance.',
  normalization: 'none', inputs: {}, runnerInputs: {}, runs: {}, status: 'running',
  installedDependencies: await installedDependencyEvidence(root),
};
const recordInput = async filename => {
  const relative = path.relative(root, filename), actual = await hash(filename);
  if (report.inputs[relative]) assert.equal(report.inputs[relative], actual);
  report.inputs[relative] = actual;
};
for (const filename of ['package-lock.json', 'upstream.lock.json', 'tests/upstream-core/evidence.mjs', 'packages/compat-cordis/native/cordis.node', 'packages/compat-harness/index.js', 'packages/compat-harness/package.json']) await recordInput(path.join(root, filename));
for (const filename of await readdir(path.join(root, 'packages/compat-cordis'))) if (/\.(js|cjs|json)$/.test(filename)) await recordInput(path.join(root, 'packages/compat-cordis', filename));
for (const filename of [fileURLToPath(import.meta.url), fixture]) report.runnerInputs[path.relative(here, filename)] = await hash(filename);
const nativeBuild = JSON.parse(await readFile(path.join(root, 'target/node-compat/build.json'), 'utf8'));
assert.equal(nativeBuild.artifactSha256, report.inputs['packages/compat-cordis/native/cordis.node'], 'Native addon artifact changed; rebuild it.');
assert(Object.keys(nativeBuild.sourceHashes ?? {}).length > 0, 'Missing native source evidence.');
for (const [filename, expected] of Object.entries(nativeBuild.sourceHashes)) {
  await recordInput(path.join(root, filename));
  assert.equal(report.inputs[filename], expected, `Native addon is stale: ${filename}`);
}
report.nativeBuild = nativeBuild;
// Harness re-exports the bare core package. Check the same ESM resolution that
// its entry uses instead of trusting a workspace symlink label alone.
const resolution = spawnSync(process.execPath, ['--input-type=module', '--eval',
  "process.stdout.write(import.meta.resolve('@cordis-verus/compat-cordis'))"], {
  cwd: path.join(root, 'packages/compat-harness'), encoding: 'utf8', timeout: 10000,
  env: { ...process.env, NODE_OPTIONS: '' },
});
assert.equal(resolution.status, 0, resolution.stderr);
const resolvedCore = await realpath(fileURLToPath(resolution.stdout));
assert.equal(resolvedCore, await realpath(path.join(root, 'packages/compat-cordis/index.js')),
  'Harness must resolve the exact core facade whose source bytes were recorded.');
report.harnessCoreResolution = path.relative(root, resolvedCore);
for (const profile of ['cordis', 'harness']) {
  const repository = lock.repositories[profile === 'cordis' ? 'cordis' : 'deepseekHarness'];
  checkUpstream(repository);
  for (const backend of ['upstream', 'native']) {
    const label = `${profile}-${backend}`;
    const directory = path.join(output, label);
    await mkdir(directory, { recursive: true });
    const entry = backend === 'native'
      ? `packages/compat-${profile}/index.js`
      : profile === 'cordis' ? 'upstream/cordis/packages/core/src/index.ts' : 'upstream/deepseek-harness/vendor/cordis/src/index.ts';
    const packageFile = path.join(path.dirname(entry), backend === 'upstream' ? '../package.json' : 'package.json');
    const packageInfo = JSON.parse(await readFile(path.join(root, packageFile), 'utf8'));
    await recordInput(path.join(root, packageFile));
    const outfile = path.join(directory, 'fixture.mjs');
    const built = await build({
      absWorkingDir: root, entryPoints: [fixture], outfile, bundle: true, platform: 'node', format: 'esm', target: 'node22', metafile: true,
      alias: { cosmokit: path.join(root, 'node_modules/cosmokit/lib/index.mjs'), '@deepseek-ai/cosmokit': path.join(root, 'upstream/deepseek-harness/vendor/cosmokit/src/index.ts') },
      plugins: [{ name: 'actual-runtime-entry', setup(builder) { builder.onResolve({ filter: /^cordis$/ }, () => ({ path: path.join(root, entry), external: backend === 'native' })); } }],
    });
    const modules = {};
    for (const filename of Object.keys(built.metafile.inputs)) {
      const absolute = path.resolve(root, filename);
      modules[absolute === fixture ? 'tests/cases/lifecycle-fixture.mjs' : path.relative(root, absolute)] = await hash(absolute);
      if (absolute !== fixture) await recordInput(absolute);
    }
    const run = spawnSync(process.execPath, [outfile], { cwd: root, encoding: 'utf8', timeout: 20000, maxBuffer: 4 * 1024 * 1024, env: { ...process.env, NODE_OPTIONS: '', CORDIS_NATIVE_BINDING: path.join(root, 'packages/compat-cordis/native/cordis.node'), CORDIS_CASE_OUTPUT: directory } });
    let observations;
    try { observations = JSON.parse(run.stdout); } catch { /* Keep process output and report a failed fixture. */ }
    const record = report.runs[label] = {
      profile, backend, entry, package: { name: packageInfo.name, version: packageInfo.version },
      upstream: { revision: repository.revision, tree: repository.tree },
      bundleSha256: await hash(outfile), moduleHashes: modules,
      nativeArtifact: backend === 'native' ? 'packages/compat-cordis/native/cordis.node' : null,
      childNodeOptions: '',
      exitCode: run.status, signal: run.signal, error: run.error?.message ?? null,
      stdout: run.stdout, stderr: run.stderr, observations,
    };
    await writeFile(path.join(directory, 'stdout.txt'), run.stdout);
    await writeFile(path.join(directory, 'stderr.txt'), run.stderr);
    try {
      assert.equal(run.status, 0, `${label} process failed`);
      assert(observations, `${label} returned no observations`);
      const order = observations.disposalOrder, failure = observations.cleanupFailure;
      assert.equal(order.disposal.status, 'fulfilled');
      assert.equal(order.writes.length, 2);
      assert.equal(order.writes[0].ok, true);
      assert.equal(order.writes[1].error, backend === 'native' ? null : 'ERR_STREAM_WRITE_AFTER_END');
      assert.equal(order.finalWriteSucceeded, backend === 'native');
      assert.equal(order.finalWriteBeforeProviderClose, backend === 'native');
      assert.equal(order.bothLinesPersisted, backend === 'native');
      assert.equal(failure.firstDisposal, backend === 'native' ? 'rejected' : 'fulfilled');
      assert.equal(failure.attemptsAfterFirstDisposal, 1);
      assert.equal(failure.explicitRetryAvailable, backend === 'native');
      assert.equal(failure.retry, backend === 'native' ? 'fulfilled' : 'unsupported');
      assert.equal(failure.attempts, backend === 'native' ? 2 : 1);
      record.status = 'observed-as-declared';
    } catch (error) { record.status = 'unexpected'; record.difference = error.message; }
    console.log(`${label}: ${record.status}`);
  }
  checkUpstream(repository);
}
for (const [filename, expected] of Object.entries(report.inputs)) assert.equal(await hash(path.join(root, filename)), expected, `Input changed during execution: ${filename}`);
for (const [filename, expected] of Object.entries(report.runnerInputs)) assert.equal(await hash(path.join(here, filename)), expected, `Runner changed during execution: ${filename}`);
assert.deepEqual(await installedDependencyEvidence(root), report.installedDependencies, 'Installed dependencies changed during execution.');
report.status = Object.values(report.runs).every(run => run.status === 'observed-as-declared') ? 'passed' : 'failed';
await writeFile(path.join(output, 'report.json'), `${JSON.stringify(report, null, 2)}\n`);
console.log(`Evidence: ${path.join(output, 'report.json')}`);
process.exitCode = report.status === 'passed' ? 0 : 1;
