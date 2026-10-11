#!/usr/bin/env node
/** Exercise the universal tarballs outside the checkout, with no compiler. */
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { copyFile, lstat, mkdir, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import { join, resolve } from 'node:path';
import { tmpdir } from 'node:os';
import { fileURLToPath } from 'node:url';
import { hostTarget, npmCommand } from './install-cordis.mjs';

const digest = bytes => createHash('sha256').update(bytes).digest('hex');
const names = ['@validation-engineering/cordis', '@validation-engineering/cordis-harness', '@validation-engineering/cordis-loader'];
const targets = ['darwin-arm64-napi8', 'darwin-x64-napi8', 'linux-x64-gnu-napi8', 'win32-x64-napi8'];
export function validateRegistry(record) {
  assert.equal(record?.schema, 'cordis-verus.npm-registry/v1');
  assert.match(record.sourceCommit, /^[a-f0-9]{40}$/);
  assert.deepEqual(Object.keys(record.targets).sort(), targets);
  assert.deepEqual(record.packages.map(item => item.name).sort(), names);
  assert.equal(new Set(record.packages.map(item => item.file)).size, 3);
  assert.equal(new Set(record.packages.map(item => item.version)).size, 1);
  assert.match(record.nativeManifestSha256, /^[a-f0-9]{64}$/);
  for (const item of record.packages) {
    assert.match(item.file, /^[A-Za-z0-9][A-Za-z0-9_.-]*\.tgz$/);
    assert.match(item.version, /^\d+\.\d+\.\d+(?:-[A-Za-z0-9.-]+)?$/);
    assert.match(item.sha256, /^[a-f0-9]{64}$/);
    assert.match(item.integrity, /^sha512-[A-Za-z0-9+/]+={0,2}$/);
    assert(Number.isSafeInteger(item.bytes) && item.bytes > 0);
  }
  for (const target of targets) for (const key of ['sha256', 'sourceDigest']) assert.match(record.targets[target][key], /^[a-f0-9]{64}$/);
  return record;
}
const smoke = `import assert from 'node:assert/strict';
import { createRequire } from 'node:module';
import { mkdir, writeFile } from 'node:fs/promises';
import { join } from 'node:path';
import { Context } from '@validation-engineering/cordis';
import { Context as HarnessContext } from '@validation-engineering/cordis-harness';
import { Loader } from '@validation-engineering/cordis-loader';
import { selectNativeArtifact, verifyNativeManifest } from '@validation-engineering/cordis/native-artifacts';
const require = createRequire(import.meta.url);
assert.equal(require('@validation-engineering/cordis').Context, Context);
const expected = JSON.parse(process.env.CORDIS_REGISTRY_EXPECTED);
const selected = selectNativeArtifact();
assert.equal(selected.entry.target, expected.target);
assert.equal(selected.entry.sha256, expected.sha256);
assert.equal(selected.provenance.build.sourceDigest, expected.sourceDigest);
assert.equal(selected.manifestSha256, expected.manifestSha256);
assert.deepEqual(verifyNativeManifest().artifacts.map(item => item.entry.target).sort(), expected.targets);
for (const [Type, profile] of [[Context, 'cordis'], [HarnessContext, 'harness']]) {
  const ctx = new Type();
  try {
    assert.equal(ctx.snapshot().profile, profile);
    await ctx.plugin(c => { c.provide('message', { read: () => 'Hello, Cordis' }); });
    assert.equal(ctx.message.read(), 'Hello, Cordis');
  } finally { await ctx.dispose(); }
}
await mkdir('plugins', {recursive:true});
await writeFile('plugins/hello.mjs', "import { Service } from 'cordis'; export default class Hello extends Service { constructor(ctx, config) { super(ctx, 'hello'); this.value=config.value; } read() { return this.value; } }");
await writeFile('cordis.json', JSON.stringify([{id:'hello',name:'./plugins/hello.mjs',config:{value:42}}]));
const ctx = new Context(), loader = new Loader(ctx);
try { await loader.loadFile(join(process.cwd(), 'cordis.json')); assert.equal(ctx.hello.read(), 42); }
finally { await loader.dispose(); await ctx.dispose(); }
console.log('Universal npm package: native selection, ESM/CJS, both profiles and original Cordis plugin passed.');
`;

export async function checkRegistry(directory, output, registry = false) {
  directory = resolve(directory);
  const record = validateRegistry(JSON.parse(await readFile(join(directory, 'npm-registry.json'), 'utf8')));
  const target = hostTarget();
  const temporary = await mkdtemp(join(tmpdir(), 'cordis registry install '));
  try {
    const env = {...process.env};
    for (const key of Object.keys(env)) if (/^npm_config_/i.test(key) || ['NODE_PATH','NODE_OPTIONS','CORDIS_NATIVE_BINDING'].includes(key)) delete env[key];
    env.npm_config_cache = join(temporary, 'cache');
    env.npm_config_userconfig = join(temporary, 'user.npmrc');
    env.npm_config_globalconfig = join(temporary, 'global.npmrc');
    await writeFile(env.npm_config_userconfig, ''); await writeFile(env.npm_config_globalconfig, '');
    env.CORDIS_REGISTRY_EXPECTED = JSON.stringify({...record.targets[target], target, manifestSha256:record.nativeManifestSha256, targets});
    function run(command) {
      const result = spawnSync(command[0], command.slice(1), {cwd:temporary, env, encoding:'utf8', timeout:180000});
      if (result.error) throw result.error;
      assert.equal(result.status, 0, `${command[0]} failed:\n${result.stdout}\n${result.stderr}`);
    }
    await mkdir(join(temporary, 'vendor'));
    for (const item of record.packages) {
      const path = join(directory, item.file), info = await lstat(path);
      assert(info.isFile() && !info.isSymbolicLink());
      const bytes = await readFile(path);
      assert.equal(bytes.length, item.bytes); assert.equal(digest(bytes), item.sha256);
      assert.equal('sha512-'+createHash('sha512').update(bytes).digest('base64'), item.integrity);
      await copyFile(path, join(temporary, 'vendor', item.file));
    }
    await writeFile(join(temporary, 'package.json'), JSON.stringify({name:'cordis-registry-consumer',private:true,type:'module'}));
    const npm = npmCommand(env);
    const specs = record.packages.map(item => registry ? `${item.name}@${item.version}` : `./vendor/${item.file}`);
    run([...npm, 'install', '--ignore-scripts', '--no-audit', '--no-fund', ...(registry ? ['--registry=https://registry.npmjs.org/'] : ['--offline']), ...specs]);
    const lock = JSON.parse(await readFile(join(temporary, 'package-lock.json'), 'utf8'));
    for (const item of record.packages) assert.equal(lock.packages['node_modules/'+item.name].integrity, item.integrity, 'Installed archive differs from the accepted registry candidate');
    await writeFile(join(temporary, 'smoke.mjs'), smoke);
    run([process.execPath, '--import', '@validation-engineering/cordis/register', 'smoke.mjs']);
    run([...npm, 'ci', '--offline', '--ignore-scripts', '--no-audit', '--no-fund']);
    run([process.execPath, '--import', '@validation-engineering/cordis/register', 'smoke.mjs']);
    const result = {schema:'cordis-verus.npm-registry-install/v1', status:'passed', sourceCommit:record.sourceCommit,
      target, registry, packages:record.packages, nativeManifestSha256:record.nativeManifestSha256,
      node:process.version, offlineReinstall:'passed'};
    if (output) await writeFile(output, JSON.stringify(result, null, 2)+'\n');
    console.log(JSON.stringify({target, status:'passed', registry, offlineReinstall:'passed'}));
    return result;
  } finally { await rm(temporary, {recursive:true, force:true}); }
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const args = process.argv.slice(2), options = {};
  while (args.length) {
    const key = args.shift();
    if (key === '--registry') { options.registry = true; continue; }
    assert(['--from-directory','--output'].includes(key) && args.length, 'Usage: check-npm-registry.mjs --from-directory ASSETS [--output RECEIPT] [--registry]');
    assert(!(key in options), 'Duplicate argument'); options[key] = args.shift();
  }
  assert(options['--from-directory'], 'Missing --from-directory');
  await checkRegistry(options['--from-directory'], options['--output'], options.registry);
}
