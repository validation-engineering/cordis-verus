#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import { copyFileSync, mkdirSync, readFileSync, readdirSync, writeFileSync, unlinkSync, renameSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { createRequire } from 'node:module';
import { writeNativeManifest } from './write-native-manifest.mjs';
const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const args = process.argv.slice(2);
if (args.some(arg => arg !== '--offline') || args.length > 1) throw new Error('Usage: build-node.mjs [--offline]');
const sha256 = path => createHash('sha256').update(readFileSync(path)).digest('hex');
function sourceHashes() {
  const files = ['Cargo.toml', 'Cargo.lock', 'toolchain.lock.json', 'scripts/build-node.sh', 'scripts/build-node.mjs', 'scripts/toolchain-env.sh', 'scripts/write-native-manifest.mjs', 'packages/compat-cordis/native-artifacts.js', 'packages/compat-cordis/package.json'];
  function visit(directory) {
    for (const entry of readdirSync(join(root, directory), { withFileTypes: true })) {
      const name = `${directory}/${entry.name}`;
      if (entry.isDirectory()) visit(name);
      else if (entry.isFile() && /\.(rs|toml)$/.test(name)) files.push(name);
    }
  }
  for (const name of ['cordis-kernel', 'cordis-driver', 'cordis', 'cordis-node', 'cordis-plugin-api']) visit(`crates/${name}`);
  return Object.fromEntries(files.sort().map(name => [name, sha256(join(root, name))]));
}
const report = join(root, 'target/node-compat/build.json');
for (const path of [report, join(root,'packages/compat-cordis/native/manifest.json')]) {
  try { unlinkSync(path); } catch (error) { if (error.code !== 'ENOENT') throw error; }
}
// Replace generated addons with a fresh inode. Overwriting a previously loaded
// signed Mach-O in place can leave macOS code-signature caches on the old inode.
// Rename also lets existing processes retain their mapped generation safely.
function installAddon(source, destination) {
  const temporary = `${destination}.${process.pid}.tmp`;
  try {
    copyFileSync(source, temporary);
    renameSync(temporary, destination);
  } finally {
    try { unlinkSync(temporary); } catch (error) { if (error.code !== 'ENOENT') throw error; }
  }
}
const before = sourceHashes();
const result = spawnSync('bash', [join(root, 'scripts/build-node.sh'), ...args], { cwd: root, stdio: ['inherit', 'pipe', 'inherit'], encoding: 'utf8', maxBuffer: 32 * 1024 * 1024 });
if (result.error) throw result.error;
if (result.status !== 0) process.exit(result.status ?? 1);
const filenames = { darwin: 'libcordis_node.dylib', linux: 'libcordis_node.so', win32: 'cordis_node.dll' };
if (!filenames[process.platform]) throw new Error(`Unsupported platform: ${process.platform}`);
// Cargo may use config/env target-dir and build.target overrides. Its emitted
// compiler-artifact is authoritative; guessing target/debug can copy stale code.
const messages = result.stdout.trim().split('\n').filter(Boolean).map(line => JSON.parse(line));
const artifacts = messages.filter(item => item.reason === 'compiler-artifact' && item.target?.name === 'cordis_node' && item.target.kind.includes('cdylib'));
const candidates = artifacts.flatMap(item => item.filenames).filter(name => name.endsWith(filenames[process.platform]));
if (candidates.length !== 1) throw new Error('Cargo did not emit exactly one compatible cordis_node cdylib');
const compilerProfile = artifacts[0].profile;
if (compilerProfile?.opt_level !== '3' || compilerProfile.debug_assertions !== true || compilerProfile.overflow_checks !== true) {
  throw new Error('Native artifacts require optimization level 3 with debug assertions and overflow checks enabled');
}
const source = candidates[0];
const output = join(root, 'packages/compat-cordis/native/cordis.node');
mkdirSync(dirname(output), { recursive: true });
installAddon(source, output);
// Reject a cross-target binary that cannot actually load in this Node environment.
const binding = createRequire(import.meta.url)(output);
if (JSON.parse(binding.bindingInfo()).abi !== 1 || typeof binding.NativeDriver !== 'function') throw new Error('Incompatible native binding');
const fixtureNames = {darwin:'libinterop_fixture.dylib',linux:'libinterop_fixture.so',win32:'interop_fixture.dll'};
const fixtureArtifacts = messages.filter(item => item.reason === 'compiler-artifact' && item.target?.name === 'interop_fixture')
  .flatMap(item => item.filenames).filter(name => name.endsWith(fixtureNames[process.platform]));
if (fixtureArtifacts.length !== 1) throw new Error('Cargo did not emit exactly one Rust plugin example addon');
const fixture = join(root,'target/node-compat/interop-fixture.node');
mkdirSync(dirname(fixture),{recursive:true});
installAddon(fixtureArtifacts[0],fixture);
const custom = createRequire(import.meta.url)(fixture);
if (typeof custom.createDriver !== 'function' || !JSON.parse(custom.createDriver().rustInfo()).factories.some(factory => factory.name === 'fixture.counter')) throw new Error('Custom Rust factory addon is not extensible');
// Independent C-ABI plugin generations exercise the resident default addon.
const dynamicFixtures = {};
const dynamicExtension = {darwin:'.dylib',linux:'.so',win32:'.dll'}[process.platform];
for (const version of ['v1','v2','fail']) {
  const target = `dynamic_fixture_${version}`;
  const prefix = process.platform === 'win32' ? '' : 'lib';
  const filename = `${prefix}${target}${dynamicExtension}`;
  const compiled = messages.filter(item => item.reason === 'compiler-artifact' && item.target?.name === target)
    .flatMap(item => item.filenames).filter(name => name.endsWith(filename));
  if (compiled.length !== 1) throw new Error(`Cargo did not emit exactly one dynamic plugin fixture: ${target}`);
  const path = `target/node-compat/dynamic-fixture-${version}${dynamicExtension}`;
  installAddon(compiled[0],join(root,path));
  dynamicFixtures[version] = {path,sha256:sha256(join(root,path))};
}
if (JSON.stringify(sourceHashes()) !== JSON.stringify(before)) throw new Error('Native sources changed during build; rerun');
const evidence = { schema: 'cordis-verus.node-build/v1', sourceHashes: before, dynamicFixtures, interopFixture:{path:'target/node-compat/interop-fixture.node',sha256:sha256(fixture)}, compilerArtifact: source, compilerProfile: artifacts[0].profile, platform: process.platform, architecture: process.arch, node: process.version, artifactSha256: sha256(output), cargoLockSha256: sha256(join(root, 'Cargo.lock')), toolchainLockSha256: sha256(join(root, 'toolchain.lock.json')) };
mkdirSync(join(root, 'target/node-compat'), { recursive: true });
writeFileSync(report, JSON.stringify(evidence, null, 2) + '\n');
try { writeNativeManifest(root,report); }
catch(error) {
  for(const path of [report,join(root,'packages/compat-cordis/native/manifest.json')]) {try{unlinkSync(path);}catch{}}
  throw error;
}
console.log(`Built native binding: ${output}`);
