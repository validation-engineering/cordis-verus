#!/usr/bin/env node
/** Install a release into a NEW project. No Rust, Verus, checkout or lifecycle scripts. */
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { copyFile, lstat, mkdir, mkdtemp, readFile, realpath, rename, rm, rmdir, writeFile } from 'node:fs/promises';
import { dirname, join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { fileURLToPath } from 'node:url';

const hash = bytes => createHash('sha256').update(bytes).digest('hex');
const names = ['@cordis-verus/compat-cordis', '@cordis-verus/compat-harness', '@cordis-verus/compat-loader'];
const targets = ['darwin-arm64-napi8', 'darwin-x64-napi8', 'linux-x64-gnu-napi8'];
const safeName = name => typeof name === 'string' && /^[a-zA-Z0-9][a-zA-Z0-9_.-]*$/.test(name);
const sha = value => typeof value === 'string' && /^[a-f0-9]{64}$/.test(value);
export function hostTarget(platform = process.platform, architecture = process.arch, libc = platform === 'linux' ? (process.report.getReport().header.glibcVersionRuntime ? 'gnu' : 'musl') : null) {
  const target = `${platform}-${architecture}${libc ? `-${libc}` : ''}-napi8`;
  assert(targets.includes(target), `Unsupported release platform: ${platform}/${architecture}/${libc}`);
  return target;
}
export function validateManifest(record, target) {
  assert.equal(record?.schema, 'cordis-verus.runtime-release/v1');
  assert.equal(record.target, target, 'Release belongs to another platform');
  assert(targets.includes(target));
  assert.match(record.sourceCommit, /^[a-f0-9]{40}$/);
  assert.equal(record.acceptance?.fullQuality, true, 'A development report is not a runtime release');
  assert.equal(record.acceptance?.paperCompletion, false);
  assert(Number.isSafeInteger(record.acceptance?.negativeControls) && record.acceptance.negativeControls > 0);
  assert(sha(record.nativeManifestSha256) && sha(record.nativeArtifactSha256));
  assert(Array.isArray(record.packages) && record.packages.length === 3);
  assert.deepEqual(record.packages.map(item => item.name).sort(), names);
  const files = new Set();
  for (const item of [...record.packages, record.evidence]) {
    assert(safeName(item?.file) && sha(item.sha256) && Number.isSafeInteger(item.bytes) && item.bytes > 0, 'Invalid release asset');
    assert(!files.has(item.file), 'Duplicate release asset'); files.add(item.file);
  }
  for (const item of record.packages) {
    assert(item.file.endsWith('.tgz') && typeof item.version === 'string' && item.version.length > 0);
  }
  return record;
}
function cleanEnvironment() {
  const env = { ...process.env };
  for (const name of Object.keys(env)) if (/^npm_config_/i.test(name) || ['NODE_OPTIONS', 'NODE_PATH', 'CORDIS_NATIVE_BINDING'].includes(name)) delete env[name];
  return env;
}
function run(command, args, cwd, env) {
  const result = spawnSync(command, args, { cwd, env, encoding: 'utf8', timeout: 180000, maxBuffer: 8 * 1024 * 1024 });
  if (result.error) throw result.error;
  assert.equal(result.status, 0, `${command} failed:\n${result.stderr}\n${result.stdout}`);
  return result.stdout;
}
async function absent(path) {
  try { await lstat(path); throw new Error(`Refusing to overwrite existing path: ${path}`); }
  catch (error) { if (error.code !== 'ENOENT') throw error; }
}
async function regular(path) {
  const info = await lstat(path);
  assert(info.isFile() && !info.isSymbolicLink(), `Expected regular asset: ${path}`);
  return readFile(path);
}
const smoke = `import assert from 'node:assert/strict';
import { Context } from '@cordis-verus/compat-cordis';
import { Context as HarnessContext } from '@cordis-verus/compat-harness';
import { Loader } from '@cordis-verus/compat-loader';
import { selectNativeArtifact } from '@cordis-verus/compat-cordis/native-artifacts';
const selected = selectNativeArtifact();
assert.equal(selected.entry.target, process.env.CORDIS_RELEASE_TARGET);
assert.equal(selected.manifestSha256, process.env.CORDIS_RELEASE_MANIFEST);
assert.equal(selected.entry.sha256, process.env.CORDIS_RELEASE_BINARY);
assert.equal(selected.provenance.build.sourceDigest, process.env.CORDIS_RELEASE_SOURCE_DIGEST);
assert.equal(typeof Loader, 'function');
for (const [Type, profile] of [[Context, 'cordis'], [HarnessContext, 'harness']]) {
  const ctx = new Type();
  try {
    assert.equal(ctx.snapshot().profile, profile);
    await ctx.plugin(c => { c.provide('releaseSmoke', { read: () => 42 }); });
    assert.equal(ctx.releaseSmoke.read(), 42);
  } finally { await ctx.dispose(); }
}
console.log('Verified native release installation.');
`;
const example = `import { Context } from '@cordis-verus/compat-cordis';
const ctx = new Context();
try {
  await ctx.plugin(c => { c.provide('greeter', { greet: name => 'Hello, ' + name }); });
  console.log(ctx.greeter.greet('Cordis'));
} finally { await ctx.dispose(); }
`;
export async function installRelease({ project, fromDirectory, release, repository = 'validation-engineering/cordis-verus' }) {
  assert(project && Boolean(fromDirectory) !== Boolean(release), 'Specify --project and exactly one of --from-directory or --release');
  assert.match(repository, /^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/);
  if (release) assert.match(release, /^[A-Za-z0-9][A-Za-z0-9_.-]*$/, 'Use an explicit simple release tag');
  const nodeVersion = process.versions.node.split('.').map(Number);
  assert(nodeVersion[0] > 22 || (nodeVersion[0] === 22 && nodeVersion[1] >= 22), 'Node.js 22.22 or newer is required');
  assert(Number(process.versions.napi) >= 8, 'Node-API 8 is required');
  const target = hostTarget();
  // The parent must already exist. Resolve it once so commits cannot follow a changed symlink.
  const requested = resolve(project);
  const parent = await realpath(dirname(requested));
  const destination = join(parent, requested.split('/').at(-1));
  await absent(destination);
  const temporary = await mkdtemp(join(tmpdir(), 'cordis-release-download-'));
  let staged, reserved = false;
  try {
    const assets = join(temporary, 'assets'); await mkdir(assets);
    async function fetchAsset(name) {
      assert(safeName(name), 'Unsafe asset name');
      const to = join(assets, name);
      if (fromDirectory) await writeFile(to, await regular(join(resolve(fromDirectory), name)));
      else run('gh', ['release', 'download', release, '--repo', repository, '--pattern', name, '--dir', assets], temporary, cleanEnvironment());
      return regular(to);
    }
    const manifestName = `cordis-runtime-${target}.json`;
    const manifestBytes = await fetchAsset(manifestName);
    const manifest = validateManifest(JSON.parse(manifestBytes), target);
    for (const item of [...manifest.packages, manifest.evidence]) {
      const bytes = await fetchAsset(item.file);
      assert.equal(bytes.length, item.bytes, `Wrong size: ${item.file}`);
      assert.equal(hash(bytes), item.sha256, `SHA-256 mismatch: ${item.file}`);
    }
    const evidence = JSON.parse(await readFile(join(assets, manifest.evidence.file), 'utf8'));
    assert.equal(evidence.sourceCommit, manifest.sourceCommit);
    assert.equal(evidence.verification?.schema, 'cordis-verus.verification/v3');
    assert.equal(evidence.verification.status, 'passed');
    assert.equal(evidence.verification.proof?.success, true);
    assert.equal(evidence.verification.proof?.errors, 0);
    assert.equal(evidence.verification.proof?.['is-verifying-entire-crate'], true);
    assert.equal(evidence.verification.negativeControls?.length, manifest.acceptance.negativeControls);
    for (const control of evidence.verification.negativeControls) {
      assert.equal(control.compiles, true);
      assert.equal(control['verification-results']?.success, false);
      assert.equal(control['verification-results']?.['is-verifying-entire-crate'], true);
      assert(control['verification-results']?.errors > 0);
    }
    const packages = evidence.npm;
    assert.equal(packages?.status, 'passed');
    assert.equal(packages.nativeTarget, target);
    assert.equal(packages.nativeManifestSha256, manifest.nativeManifestSha256);
    assert.equal(packages.nativeArtifactSha256, manifest.nativeArtifactSha256);
    assert(packages.nativeSourceHashes && Object.keys(packages.nativeSourceHashes).length, 'Missing native source provenance');
    for (const [file, expected] of Object.entries(packages.nativeSourceHashes)) {
      assert(sha(expected) && evidence.verification.sha256?.[file] === expected, `Native source lacks matching full-quality evidence: ${file}`);
    }
    const nativeSourceDigest = hash(JSON.stringify(Object.fromEntries(Object.entries(packages.nativeSourceHashes).sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0))));
    assert.deepEqual(packages.packages.map(item => [item.name, item.version, item.sha256]).sort(), manifest.packages.map(item => [item.name, item.version, item.sha256]).sort());
    staged = await mkdtemp(join(parent, '.cordis-project-'));
    await writeFile(join(staged, 'package.json'), JSON.stringify({ name: 'cordis-application', version: '0.0.0', private: true, type: 'module', scripts: { start: 'node app.mjs' } }, null, 2) + '\n');
    const env = cleanEnvironment();
    env.npm_config_cache = join(temporary, 'npm-cache');
    env.npm_config_userconfig = join(temporary, 'user.npmrc');
    env.npm_config_globalconfig = join(temporary, 'global.npmrc');
    await writeFile(env.npm_config_userconfig, ''); await writeFile(env.npm_config_globalconfig, '');
    // Preserve local tarballs: package-lock remains reinstallable after staging is removed.
    const vendor = join(staged, '.vendor/cordis'); await mkdir(vendor, { recursive: true });
    for (const item of manifest.packages) await copyFile(join(assets, item.file), join(vendor, item.file));
    run('npm', ['install', '--offline', '--ignore-scripts', '--no-audit', '--no-fund', ...manifest.packages.map(item => `./.vendor/cordis/${item.file}`)], staged, env);
    await writeFile(join(staged, 'verify-release.mjs'), smoke);
    run(process.execPath, ['verify-release.mjs'], staged, { ...env, CORDIS_RELEASE_TARGET: target, CORDIS_RELEASE_MANIFEST: manifest.nativeManifestSha256, CORDIS_RELEASE_BINARY: manifest.nativeArtifactSha256, CORDIS_RELEASE_SOURCE_DIGEST: nativeSourceDigest });
    await rm(join(staged, 'verify-release.mjs'));
    await writeFile(join(staged, 'app.mjs'), example);
    await writeFile(join(vendor, manifestName), manifestBytes);
    await copyFile(join(assets, manifest.evidence.file), join(vendor, manifest.evidence.file));
    await writeFile(join(staged, 'cordis-release.json'), JSON.stringify({ sourceCommit: manifest.sourceCommit, target, repository, release: release ?? null, manifestSha256: hash(manifestBytes), fullQuality: true, paperCompletion: false }, null, 2) + '\n');
    // Exclusive reservation detects a path created while installation ran.
    await mkdir(destination); reserved = true;
    await rename(staged, destination); staged = undefined; reserved = false;
    return { project: destination, target, sourceCommit: manifest.sourceCommit };
  } finally {
    if (reserved) await rmdir(destination);
    if (staged) await rm(staged, { recursive: true, force: true });
    await rm(temporary, { recursive: true, force: true });
  }
}
if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try {
    const options = {}, keys = { '--project': 'project', '--from-directory': 'fromDirectory', '--release': 'release', '--repository': 'repository' };
    const args = process.argv.slice(2);
    if (args.length === 1 && args[0] === '--help') {
      console.log('Usage: node install-cordis.mjs --project NEW_DIRECTORY (--release TAG [--repository OWNER/REPO] | --from-directory ASSETS)');
    } else {
      for (let i = 0; i < args.length; i += 2) {
        assert(keys[args[i]] && args[i + 1] && !options[keys[args[i]]], 'Invalid or duplicate argument; use --help');
        options[keys[args[i]]] = args[i + 1];
      }
      console.log(JSON.stringify(await installRelease(options), null, 2));
      console.log('Run npm start in the new project. No source compilation was performed.');
    }
  } catch (error) { console.error(error.message); process.exitCode = 1; }
}
