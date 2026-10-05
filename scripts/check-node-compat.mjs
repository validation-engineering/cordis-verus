// Differential evidence for the locked original Cordis profile only.
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFile, readdir, mkdir, writeFile, unlink } from 'node:fs/promises';
import { spawnSync } from 'node:child_process';
import { fileURLToPath } from 'node:url';
import path from 'node:path';

const root = fileURLToPath(new URL('../', import.meta.url));
const output = path.join(root, 'target/node-compat');
const reportPath = path.join(output, 'differential.json');
const digest = buffer => createHash('sha256').update(buffer).digest('hex');
const fileDigest = async name => digest(await readFile(path.resolve(root, name)));
function run(command, args, options = {}) {
  const result = spawnSync(command, args, { cwd: root, encoding: 'utf8', timeout: 30000, maxBuffer: 8 * 1024 * 1024, ...options });
  if (result.error || result.status !== 0) throw new Error(`${command} failed: ${result.error ?? result.stderr ?? result.signal}`);
  return (result.stdout ?? '').trim();
}
function checkUpstream() {
  assert.equal(run('git', ['-C', upstream.path, 'rev-parse', 'HEAD']), upstream.revision, 'Wrong upstream commit');
  assert.equal(run('git', ['-C', upstream.path, 'rev-parse', 'HEAD^{tree}']), upstream.tree, 'Wrong upstream tree');
  assert.equal(run('git', ['-C', upstream.path, 'status', '--porcelain=v1', '--untracked-files=all']), '', 'Upstream must remain unmodified');
}
const args = process.argv.slice(2);
if (args.length > 1 || args.some(arg => arg !== '--build')) throw new Error('Usage: check-node-compat.mjs [--build]');
await mkdir(output, { recursive: true });
await unlink(reportPath).catch(error => { if (error.code !== 'ENOENT') throw error; });
// Invalidate before any dependency/lock/build/Timer failure in this run.
if (args.includes('--build')) {
  run(process.execPath, ['scripts/build-node.mjs'], { stdio: 'inherit', timeout: 300000 });
  run(process.execPath, ['--test', '--test-timeout=30000', 'tests/compat/upstream-timer.test.mjs'], { stdio: 'inherit', timeout: 60000 });
}
const { build, version: esbuildVersion } = await import('esbuild');
const lock = JSON.parse(await readFile(path.join(root, 'upstream.lock.json'), 'utf8'));
const upstream = lock.repositories.cordis;
checkUpstream();
const packageJson = JSON.parse(await readFile(path.join(root, upstream.path, 'packages/core/package.json'), 'utf8'));
assert.equal(packageJson.version, '4.0.0-rc.10');
const report = {
  schema: 'cordis-verus.node-differential/v1',
  profile: { name: 'cordis', version: packageJson.version, revision: upstream.revision, tree: upstream.tree },
  node: process.version, esbuild: esbuildVersion, observations: {}, inputs: {},
  normalization: 'none', nativeLifecycleUsesUpstreamFiber: false,
};
for (const name of ['upstream.lock.json', 'Cargo.lock', 'package-lock.json', 'scripts/check-node-compat.mjs', 'packages/compat-cordis/native/cordis.node']) report.inputs[name] = await fileDigest(name);
// Snapshot all native external imports and all source inputs before either run.
for (const name of await readdir(path.join(root, 'packages/compat-cordis'))) {
  if (/\.(js|cjs|json)$/.test(name)) {
    const relative = `packages/compat-cordis/${name}`;
    report.inputs[relative] = await fileDigest(relative);
  }
}
for (const directory of ['packages/core/src', 'packages/timer/src']) {
  const names = run('git', ['-C', upstream.path, 'ls-files', directory]).split('\n').filter(Boolean);
  for (const name of names) report.inputs[`${upstream.path}/${name}`] = await fileDigest(`${upstream.path}/${name}`);
}
for (const name of ['tests/compat/differential-fixture.mjs', 'tests/node-compat/fixture.mjs']) report.inputs[name] = await fileDigest(name);
const nativeBuild = JSON.parse(await readFile(path.join(output, 'build.json'), 'utf8'));
assert.equal(nativeBuild.artifactSha256, report.inputs['packages/compat-cordis/native/cordis.node']);
assert(nativeBuild.sourceHashes && Object.keys(nativeBuild.sourceHashes).length > 0, 'Rebuild addon with source-bound evidence');
for (const [name, hash] of Object.entries(nativeBuild.sourceHashes)) {
  assert.equal(await fileDigest(name), hash, `Stale addon source: ${name}; rebuild it`);
  report.inputs[name] = hash;
}
report.nativeBuild = nativeBuild;
for (const backend of ['upstream', 'native']) {
  const outfile = path.join(output, `differential-${backend}.mjs`);
  const built = await build({
    absWorkingDir: root, entryPoints: ['tests/compat/differential-fixture.mjs'], outfile,
    bundle: true, format: 'esm', platform: 'node', target: 'node22', metafile: true,
    alias: { cosmokit: path.join(root, 'node_modules/cosmokit/lib/index.mjs') },
    plugins: [{ name: 'cordis-profile', setup(builder) {
      builder.onResolve({ filter: /^cordis$/ }, () => ({
        path: path.join(root, backend === 'upstream' ? `${upstream.path}/packages/core/src/index.ts` : 'packages/compat-cordis/index.js'),
        external: backend === 'native',
      }));
    }}],
  });
  const inputs = Object.keys(built.metafile.inputs);
  if (backend === 'native') assert(!inputs.some(name => name.includes('/core/src/fiber.')), 'Native backend imported upstream scheduler');
  for (const name of inputs) {
    const hash = await fileDigest(name);
    if (report.inputs[name]) assert.equal(hash, report.inputs[name], `Source changed during bundling: ${name}`);
    else report.inputs[name] = hash;
  }
  report.inputs[path.relative(root, outfile)] = await fileDigest(outfile);
  report.observations[backend] = JSON.parse(run(process.execPath, [outfile]));
}
checkUpstream();
for (const [name, expected] of Object.entries(report.inputs)) assert.equal(await fileDigest(name), expected, `Input changed: ${name}`);
assert.deepEqual(report.observations.native, report.observations.upstream);
report.status = 'passed';
report.fixtureCount = Object.keys(report.observations.native).length;
await writeFile(reportPath, JSON.stringify(report, null, 2) + '\n');
console.log(`Native/upstream differential passed: ${report.fixtureCount} shared fixtures; no trace normalization. Report: target/node-compat/differential.json`);
