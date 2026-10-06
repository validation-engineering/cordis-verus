#!/usr/bin/env node
/** Pack and install the local native/JS distribution without publishing or network access. */
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { copyFile, lstat, mkdir, mkdtemp, readFile, readdir, realpath, rm, writeFile } from 'node:fs/promises';
import { dirname, join, resolve, relative } from 'node:path';
import { tmpdir } from 'node:os';
import { fileURLToPath } from 'node:url';
import { selectNativeArtifact, verifyNativeManifest } from '../packages/compat-cordis/native-artifacts.js';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const packageDirectories = ['packages/compat-cordis', 'packages/compat-loader', 'packages/compat-harness'];
const output = join(root, 'target/release-artifacts/npm');
const reportPath = join(output, 'package-report.json');
const digest = bytes => createHash('sha256').update(bytes).digest('hex');
const fileDigest = async path => digest(await readFile(path));
const npm = process.platform === 'win32' ? 'npm.cmd' : 'npm';

async function filesUnder(directory, accept = () => true) {
  const result = [];
  async function visit(at) {
    for (const entry of (await readdir(at, { withFileTypes: true })).sort((a, b) => a.name.localeCompare(b.name))) {
      if (['node_modules', '.git', 'target'].includes(entry.name)) continue;
      const path = join(at, entry.name);
      if (entry.isSymbolicLink()) throw new Error(`Unexpected distribution source symlink: ${path}`);
      if (entry.isDirectory()) await visit(path);
      else if (entry.isFile() && accept(path)) result.push(path);
    }
  }
  await visit(directory);
  return result;
}

async function nativeInputs() {
  const files = ['Cargo.toml', 'Cargo.lock', 'toolchain.lock.json', 'scripts/build-node.sh', 'scripts/build-node.mjs', 'scripts/toolchain-env.sh', 'scripts/write-native-manifest.mjs', 'packages/compat-cordis/native-artifacts.js', 'packages/compat-cordis/package.json'];
  for (const name of ['cordis-kernel', 'cordis-driver', 'cordis', 'cordis-node', 'cordis-plugin-api']) {
    for (const path of await filesUnder(join(root, 'crates', name), name => /\.(rs|toml)$/.test(name))) files.push(relative(root, path).split('\\').join('/'));
  }
  return Object.fromEntries(await Promise.all(files.sort().map(async name => [name, await fileDigest(join(root, name))])));
}
async function inputs() {
  const files = ['package.json', 'package-lock.json', 'LICENSE', 'NOTICE', 'scripts/check-npm-package.mjs'];
  for (const directory of packageDirectories) for (const path of await filesUnder(join(root, directory))) files.push(relative(root, path).split('\\').join('/'));
  return Object.fromEntries(await Promise.all(files.sort().map(async name => [name, await fileDigest(join(root, name))])));
}
function assertHashes(actual, expected, message) {
  const changed = [...new Set([...Object.keys(actual), ...Object.keys(expected)])]
    .filter(name => actual[name] !== expected[name]).sort();
  assert.equal(changed.length, 0, `${message}: ${changed.slice(0, 10).join(', ')}${changed.length > 10 ? ` (+${changed.length - 10} more)` : ''}`);
}
function run(command, args, cwd, env) {
  const result = spawnSync(command, args, { cwd, env, encoding: 'utf8', timeout: 120000, maxBuffer: 32 * 1024 * 1024 });
  if (result.error) throw result.error;
  if (result.status !== 0) throw new Error(`${command} failed (${result.status}):\n${result.stdout}\n${result.stderr}`);
  return result.stdout.trim();
}

const smoke = `
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { realpath, mkdir, writeFile, copyFile, readFile } from 'node:fs/promises';
import { Context } from '@cordis-verus/compat-cordis';
import { selectNativeArtifact } from '@cordis-verus/compat-cordis/native-artifacts';
import { Loader } from '@cordis-verus/compat-loader';
import { WorkerDomain } from '@cordis-verus/compat-loader/worker';
import { ProcessDomain } from '@cordis-verus/compat-loader/process';
import { loadRustModule } from '@cordis-verus/compat-loader/rust-module';
const require = createRequire(import.meta.url);
const facade = fileURLToPath(import.meta.resolve('@cordis-verus/compat-cordis'));
const loaderPath = fileURLToPath(import.meta.resolve('@cordis-verus/compat-loader'));
const installed = await realpath(join(process.cwd(), 'node_modules'));
for (const path of [facade, loaderPath]) assert.ok((await realpath(path)).startsWith(installed + '/'));
assert.equal(require('@cordis-verus/compat-cordis').Context, Context);
const selected=selectNativeArtifact();
assert.ok(selected.path.startsWith(installed + '/'));
const binding = require(selected.path);
const nativeDriver=typeof binding.createDriver==='function'?binding.createDriver():new binding.NativeDriver();
assert.deepEqual(JSON.parse(nativeDriver.rustInfo()).factories, []);
const info = JSON.parse(binding.bindingInfo());
const project = join(process.cwd(), 'project');
await mkdir(project);
await writeFile(join(project, 'plugin.mjs'), "import { Service } from 'cordis'; export default class Message extends Service { constructor(ctx, config) { super(ctx, 'message'); this.prefix = config.prefix; } hello(name) { return this.prefix + ':' + name; } }");
await writeFile(join(project, 'cordis.json'), JSON.stringify([{ id: 'message', name: './plugin.mjs', config: { prefix: 'packed' } }]));
const context = new Context();
const loader = new Loader(context);
await loader.loadFile(join(project, 'cordis.json'));
assert.equal(context.message.hello('native'), 'packed:native');
await loader.update('message', { config: { prefix: 'updated' } });
assert.equal(context.message.hello('native'), 'updated:native');
await loader.dispose();
await context.dispose();
const domain = new WorkerDomain({ timeout: 10000 });
try {
  const loaded = await domain.load(project);
  assert.equal(loaded.plan.strategy, 'worker-restart');
  const graph = await domain.moduleGraph();
  assert.equal(graph.coverage, 'observed');
  assert.ok(graph.modules.some(module => module.path === 'plugin.mjs'));
  assert.equal((await domain.planReload()).identical, true);
  assert.equal(await domain.call('message', 'hello', 'worker'), 'packed:worker');
} finally { await domain.dispose(); }
await copyFile(selected.path, join(project, 'application.node'));
await writeFile(join(project, 'plugin.mjs'), "import { Service } from 'cordis'; import { createRequire } from 'node:module'; const addon = createRequire(import.meta.url)('./application.node'); export default class Message extends Service { constructor(ctx) { super(ctx, 'message'); } abi() { return JSON.parse(addon.bindingInfo()).abi; } }");
const isolated = new ProcessDomain({ timeout: 10000, stdio: 'ignore' });
try {
  const loaded = await isolated.load(project);
  assert.equal(loaded.plan.strategy, 'process-restart');
  assert.deepEqual(loaded.plan.nativeAddons, ['application.node']);
  assert.notEqual(isolated.pid, process.pid);
  assert.equal(await isolated.call('message', 'abi'), 1);
  assert.ok((await isolated.moduleGraph()).modules.some(module => module.path === 'application.node'));
} finally { await isolated.dispose(); }
const artifacts = JSON.parse(await readFile(join(process.cwd(), 'dynamic-modules.json'), 'utf8'));
const nativeContext = new Context();
let nativeModule;
try {
  const residentDriver = nativeContext.fiber._domain.driver;
  nativeModule = await loadRustModule(nativeContext, {...artifacts.v1, plugins:[{id:'text',factory:'native-text-analysis',config:{setup_pending:true,cleanup_pending:true}}]});
  const oldService = nativeContext.nativeText;
  assert.deepEqual(oldService.analyze({text:'native code update'}), {version:'v1',words:3,characters:18,text:'native code update'});
  await nativeModule.reload(artifacts.v2);
  assert.equal(nativeContext.nativeText.analyze({text:'same process'}).version, 'v2');
  assert.equal((await nativeContext.nativeText.delayed({text:'async native'})).version, 'v2');
  assert.equal(nativeContext.fiber._domain.driver, residentDriver);
  assert.throws(() => oldService.analyze({text:'old handle'}), { code: 'STALE_EPISODE' });
  const committed = nativeModule.snapshot();
  await assert.rejects(nativeModule.reload(artifacts.fail), error => error.code === 'NATIVE_MODULE_RELOAD_FAILED' && error.details.restored);
  assert.equal(nativeContext.nativeText.analyze({text:'recovered'}).version, 'v2');
  assert.equal(nativeModule.snapshot().entries[0].factoryRef, committed.entries[0].factoryRef);
  assert.equal(nativeContext.fiber._domain.driver, residentDriver);
  await nativeModule.dispose();
  assert.ok(nativeModule.inspect().images.modules.every(module => Object.values(module.resources).every(count => count === 0)));
  assert.equal(nativeContext.snapshot().plugins.length, 1);
} finally {
  if (nativeModule) await nativeModule.dispose();
  await nativeContext.dispose();
}
console.log(JSON.stringify({ binding: info, nativeManifestSha256:selected.manifestSha256, nativeTarget:selected.entry.target, tests: ['native-manifest-selection', 'default-core-only', 'packed-native-load', 'ESM-CJS-identity', 'original-cordis-import', 'JSON-loader-update', 'Worker-artifact-load', 'Process-native-artifact-load', 'Rust-module-in-place-reload'] }));
`;

const harnessSmoke = `
import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { Context, Service } from '@deepseek-ai/cordis';
import { Context as PackageContext } from '@cordis-verus/compat-harness';
import { LoaderTransactions, installOfficialTransactions } from '@cordis-verus/compat-loader/harness';
assert.equal(typeof LoaderTransactions, 'function');
assert.equal(typeof installOfficialTransactions, 'function');
const require = createRequire(import.meta.url);
assert.equal(Context, PackageContext);
assert.equal(require('@cordis-verus/compat-harness').Context, Context);
const context = new Context();
assert.equal(context.snapshot().profile, 'harness');
class Message extends Service { constructor(ctx) { super(ctx, 'packedHarness'); this.value = 'packed'; } }
await context.plugin(Message);
assert.equal(context.get('packedHarness').value, 'packed');
await context.dispose();
console.log(JSON.stringify({ profile: 'harness', tests: ['scoped-original-import', 'ESM-CJS-profile-identity', 'native-harness-domain', 'Service-class', 'official-loader-adapter-export'] }));
`;

async function main() {
  if (process.argv.slice(2).some(arg => arg !== '--offline') || process.argv.length > 3) throw new Error('Usage: check-npm-package.mjs [--offline] (always offline)');
  await mkdir(output, { recursive: true });
  await rm(reportPath, { force: true });
  const buildPath = join(root, 'target/node-compat/build.json');
  const build = JSON.parse(await readFile(buildPath, 'utf8'));
  assert.equal(build.schema, 'cordis-verus.node-build/v1');
  assert.equal(build.platform, process.platform, 'Native artifact belongs to another platform');
  assert.equal(build.architecture, process.arch, 'Native artifact belongs to another architecture');
  assertHashes(await nativeInputs(), build.sourceHashes, 'Native build is stale; run npm run build:native');
  const selected=selectNativeArtifact();
  const verified=verifyNativeManifest();
  assert.equal(selected.provenance.build.reportSha256, await fileDigest(buildPath), 'Native provenance has a different build record');
  assertHashes(selected.provenance.build.sourceHashes, build.sourceHashes, 'Native provenance has a different source snapshot');
  const nativePath = selected.path;
  assert.equal(await fileDigest(nativePath), build.artifactSha256, 'Native binary differs from its build record');
  const extension = {darwin:'.dylib',linux:'.so',win32:'.dll'}[process.platform];
  assert.ok(extension, 'Unsupported dynamic plugin fixture platform');
  assert.deepEqual(Object.keys(build.dynamicFixtures ?? {}).sort(), ['fail','v1','v2'], 'Dynamic plugin fixture build evidence is incomplete');
  const dynamicSources = {};
  for (const version of ['v1','v2','fail']) {
    const artifact = build.dynamicFixtures[version];
    const expected = `target/node-compat/dynamic-fixture-${version}${extension}`;
    assert.equal(artifact.path, expected, 'Dynamic fixture path differs from its expected build output');
    const source = join(root, expected), stat = await lstat(source);
    assert.ok(stat.isFile() && !stat.isSymbolicLink(), 'Dynamic fixture must be a regular build artifact');
    assert.equal(await fileDigest(source), artifact.sha256, 'Dynamic plugin fixture is stale');
    dynamicSources[version] = source;
  }
  const before = await inputs();
  const temporary = await realpath(await mkdtemp(join(tmpdir(), 'cordis-npm-package-')));
  const packageResults = [];
  try {
    const archives = join(temporary, 'archives');
    const consumer = join(temporary, 'consumer');
    const cache = join(temporary, 'npm-cache');
    await mkdir(archives); await mkdir(consumer);
    const userConfig = join(temporary, 'user.npmrc');
    const globalConfig = join(temporary, 'global.npmrc');
    await writeFile(userConfig, ''); await writeFile(globalConfig, '');
    const env = { ...process.env, npm_config_cache: cache, npm_config_userconfig: userConfig, npm_config_globalconfig: globalConfig };
    // No source-workspace fallback, inherited preload or alternate native binary.
    for (const key of ['NODE_PATH', 'NODE_OPTIONS', 'CORDIS_NATIVE_BINDING']) delete env[key];
    for (const directory of packageDirectories) {
      const source = join(root, directory);
      const stage = join(temporary, 'staging', directory.split('/').at(-1));
      await mkdir(stage, { recursive: true });
      for (const path of await filesUnder(source)) {
        const destination = join(stage, relative(source, path));
        await mkdir(dirname(destination), { recursive: true });
        await copyFile(path, destination);
      }
      // Own and upstream notices travel with the staged local distribution.
      for (const filename of ['LICENSE', 'NOTICE']) await copyFile(join(root, filename), join(stage, filename));
      const packed = JSON.parse(run(npm, ['pack', '--ignore-scripts', '--offline', '--json', '--pack-destination', archives], stage, env));
      assert.equal(packed.length, 1);
      const record = packed[0];
      assert.match(record.filename, /^[A-Za-z0-9_.-]+\.tgz$/);
      const paths = record.files.map(item => item.path);
      for (const required of ['package.json', 'index.js', 'index.d.ts', 'README.md', 'LICENSE', 'NOTICE']) assert.ok(paths.includes(required), `${record.name} lacks ${required}`);
      for (const path of paths) assert.ok(!path.startsWith('/') && !path.split('/').some(part => ['..', '.git', 'node_modules', 'upstream', 'target'].includes(part)), `Unsafe packed file ${path}`);
      if (record.name === '@cordis-verus/compat-cordis') {
        const expected=verified.artifacts.map(item=>'native/'+item.entry.file);
        for (const required of ['native/manifest.json',...expected,...verified.artifacts.map(item=>'native/'+item.entry.provenance)]) assert.ok(paths.includes(required), 'Packed facade lacks '+required);
        assert.deepEqual(paths.filter(name=>name.endsWith('.node')).sort(), expected.sort(), 'Unlisted or custom SDK addon in default distribution');
      }
      const archive = join(archives, record.filename);
      packageResults.push({ name: record.name, version: record.version, filename: record.filename, sha256: await fileDigest(archive), files: paths });
    }
    await writeFile(join(consumer, 'package.json'), JSON.stringify({ name: 'cordis-isolated-install-check', version: '0.0.0', private: true, type: 'module' }));
    run(npm, ['install', '--ignore-scripts', '--offline', '--no-audit', '--no-fund', ...packageResults.map(item => join(archives, item.filename))], consumer, env);
    for (const item of packageResults) {
      const installed = join(consumer, 'node_modules', item.name);
      assert.equal((await lstat(installed)).isSymbolicLink(), false, 'Installation must extract tarballs, not link source');
      for (const path of await filesUnder(installed)) assert.ok((await realpath(path)).startsWith(consumer + '/'));
    }
    // Plugin images are independent application artifacts, not hidden factories
    // linked into the default addon. Verify and copy them outside the checkout.
    const dynamicDirectory = join(consumer, 'dynamic-modules');
    await mkdir(dynamicDirectory);
    const dynamicArtifacts = {};
    for (const [version, source] of Object.entries(dynamicSources)) {
      const path = join(dynamicDirectory, `text-${version}${extension}`);
      await copyFile(source, path);
      const sha256 = await fileDigest(path);
      assert.equal(sha256, build.dynamicFixtures[version].sha256, 'Copied dynamic plugin fixture changed');
      dynamicArtifacts[version] = {path,sha256};
    }
    await writeFile(join(consumer, 'dynamic-modules.json'), JSON.stringify(dynamicArtifacts));
    await writeFile(join(consumer, 'smoke.mjs'), smoke);
    const observation = JSON.parse(run(process.execPath, ['--import', '@cordis-verus/compat-cordis/register', 'smoke.mjs'], consumer, env));
    assert.equal(observation.nativeManifestSha256, selected.manifestSha256, 'Installed native manifest differs from checkout');
    assert.equal(observation.nativeTarget, selected.entry.target);
    await writeFile(join(consumer, 'harness-smoke.mjs'), harnessSmoke);
    const harnessObservation = JSON.parse(run(process.execPath, ['--import', '@cordis-verus/compat-harness/register', 'harness-smoke.mjs'], consumer, env));
    for (const [version, source] of Object.entries(dynamicSources)) {
      assert.equal(await fileDigest(source), build.dynamicFixtures[version].sha256, 'Dynamic plugin fixture changed during distribution check');
    }
    assertHashes(await inputs(), before, 'Package inputs changed during distribution check');
    assertHashes(await nativeInputs(), build.sourceHashes, 'Native sources changed during distribution check');
    for (const item of packageResults) await copyFile(join(archives, item.filename), join(output, item.filename));
    const report = {
      schema: 'cordis-verus.npm-package/v1', status: 'passed', checkedAt: new Date().toISOString(),
      registryPublishChecked: false, uploaded: false, offline: true,
      testedTarget: { platform: process.platform, architecture: process.arch, node: process.version, nodeApi: process.versions.napi, nodeModuleAbi: process.versions.modules, driverAbi: observation.binding.abi },
      otherTargets: 'not validated', nativeManifestSha256:selected.manifestSha256, nativeTarget:selected.entry.target, buildReportSha256: await fileDigest(buildPath), nativeArtifactSha256: build.artifactSha256,
      sourceHashes: before, nativeSourceHashes: build.sourceHashes, packages: packageResults, observation, harnessObservation,
    };
    await writeFile(reportPath, JSON.stringify(report, null, 2) + '\n');
    console.log(`Packed and independently installed ${packageResults.length} npm artifacts on ${process.platform}/${process.arch} ${process.version}.`);
    console.log(`Report: ${reportPath}. No upload; other targets remain unvalidated.`);
  } finally { await rm(temporary, { recursive: true, force: true }); }
}
await main();
