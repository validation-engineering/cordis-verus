import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { chmod, lstat, mkdir, mkdtemp, readFile, readdir, rm, symlink, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import test from 'node:test';
import { hostTarget, installRelease, validateManifest } from '../../scripts/install-cordis.mjs';

const hash = value => createHash('sha256').update(value).digest('hex');
const target = hostTarget();
const names = ['@cordis-verus/compat-cordis', '@cordis-verus/compat-harness', '@cordis-verus/compat-loader'];
// Synthetic records exercise rejection/rollback only. They are not release evidence.
async function fixture() {
  const root = await mkdtemp(join(tmpdir(), 'cordis-release-test-'));
  const assets = join(root, 'assets'); await mkdir(assets);
  const packages = names.map((name, index) => ({ name, version: '0.1.0', file: `package-${index}.tgz`, bytes: 7, sha256: hash('invalid') }));
  for (const item of packages) await writeFile(join(assets, item.file), 'invalid');
  const evidence = {
    sourceCommit: 'a'.repeat(40),
    verification: { schema: 'cordis-verus.verification/v3', status: 'passed', sha256: { 'fixture.rs': 'd'.repeat(64) }, proof: { success: true, errors: 0, 'is-verifying-entire-crate': true },
      negativeControls: [{ compiles: true, 'verification-results': { success: false, errors: 1, 'is-verifying-entire-crate': true } }] },
    npm: { status: 'passed', nativeSourceHashes: { 'fixture.rs': 'd'.repeat(64) }, nativeTarget: target, nativeManifestSha256: 'b'.repeat(64), nativeArtifactSha256: 'c'.repeat(64), packages },
  };
  const bytes = JSON.stringify(evidence); await writeFile(join(assets, 'evidence.json'), bytes);
  const manifest = { schema: 'cordis-verus.runtime-release/v1', target, sourceCommit: evidence.sourceCommit,
    acceptance: { fullQuality: true, paperCompletion: false, negativeControls: 1 },
    nativeManifestSha256: evidence.npm.nativeManifestSha256, nativeArtifactSha256: evidence.npm.nativeArtifactSha256,
    packages, evidence: { file: 'evidence.json', bytes: Buffer.byteLength(bytes), sha256: hash(bytes) } };
  const save = () => writeFile(join(assets, `cordis-runtime-${target}.json`), JSON.stringify(manifest));
  await save();
  return { root, assets, project: join(root, 'app'), manifest, save, dispose: () => rm(root, { recursive: true, force: true }) };
}
async function noProject(f) {
  await assert.rejects(lstat(f.project), { code: 'ENOENT' });
  assert.deepEqual((await readdir(f.root)).sort(), ['assets']);
}

test('release installer selects only supported host targets', () => {
  assert.equal(hostTarget('darwin', 'arm64', null), 'darwin-arm64-napi8');
  assert.equal(hostTarget('linux', 'x64', 'gnu'), 'linux-x64-gnu-napi8');
  assert.throws(() => hostTarget('linux', 'x64', 'musl'), /Unsupported/);
  assert.throws(() => hostTarget('win32', 'x64', null), /Unsupported/);
});
test('release manifest rejects development evidence, wrong target, missing and unsafe packages', async () => {
  const f = await fixture();
  try {
    validateManifest(f.manifest, target);
    for (const mutate of [r => { r.acceptance.fullQuality = false; }, r => { r.target = 'other'; },
      r => { r.packages.pop(); }, r => { r.packages[0].file = '../escape.tgz'; },
      r => { r.packages[1].file = r.packages[0].file; }, r => { r.evidence.sha256 = 'invalid'; }]) {
      const record = structuredClone(f.manifest); mutate(record);
      assert.throws(() => validateManifest(record, target));
    }
  } finally { await f.dispose(); }
});
test('release installer refuses an existing project before reading assets', async () => {
  const f = await fixture();
  try {
    await mkdir(f.project); await writeFile(join(f.project, 'keep'), 'user data');
    await assert.rejects(installRelease({ project: f.project, fromDirectory: '/missing' }), /overwrite/);
    assert.equal(await readFile(join(f.project, 'keep'), 'utf8'), 'user data');
  } finally { await f.dispose(); }
});
test('missing release assets do not create a destination or staging directory', async () => {
  const f = await fixture();
  try {
    await assert.rejects(installRelease({ project: f.project, fromDirectory: join(f.root, 'absent') }), /ENOENT/);
    await noProject(f);
  } finally { await f.dispose(); }
});
test('changed tarball bytes abort before installing anything', async () => {
  const f = await fixture();
  try {
    await writeFile(join(f.assets, f.manifest.packages[0].file), 'changed');
    await assert.rejects(installRelease({ project: f.project, fromDirectory: f.assets }), /SHA-256 mismatch/);
    await noProject(f);
  } finally { await f.dispose(); }
});
test('local symlink assets are rejected', async () => {
  const f = await fixture();
  try {
    const path = join(f.assets, f.manifest.packages[0].file); await rm(path);
    await symlink(f.manifest.packages[1].file, path);
    await assert.rejects(installRelease({ project: f.project, fromDirectory: f.assets }), /regular asset/);
    await noProject(f);
  } finally { await f.dispose(); }
});
test('invalid evidence is rejected before npm runs', async () => {
  const f = await fixture();
  try {
    f.manifest.acceptance.negativeControls = 2; await f.save();
    await assert.rejects(installRelease({ project: f.project, fromDirectory: f.assets }));
    await noProject(f);
  } finally { await f.dispose(); }
});
test('real offline npm failure removes the staged project and preserves the caller directory', async () => {
  const f = await fixture();
  try {
    await assert.rejects(installRelease({ project: f.project, fromDirectory: f.assets }), /npm failed/);
    await noProject(f);
  } finally { await f.dispose(); }
});
test('explicit tag and single source are required without filesystem changes', async () => {
  const f = await fixture();
  try {
    await assert.rejects(installRelease({ project: f.project, fromDirectory: f.assets, release: 'v1' }), /exactly one/);
    await assert.rejects(installRelease({ project: f.project, release: '--latest' }), /release tag/);
    await noProject(f);
  } finally { await f.dispose(); }
});

test('native source provenance must be covered by the full-quality record', async () => {
  const f = await fixture();
  try {
    const path = join(f.assets, f.manifest.evidence.file);
    const evidence = JSON.parse(await readFile(path, 'utf8'));
    evidence.verification.sha256['fixture.rs'] = 'e'.repeat(64);
    const bytes = JSON.stringify(evidence); await writeFile(path, bytes);
    f.manifest.evidence.bytes = Buffer.byteLength(bytes); f.manifest.evidence.sha256 = hash(bytes); await f.save();
    await assert.rejects(installRelease({ project: f.project, fromDirectory: f.assets }), /matching full-quality evidence/);
    await noProject(f);
  } finally { await f.dispose(); }
});
test('GitHub download failure does not create a destination', async () => {
  const f = await fixture(), oldPath = process.env.PATH;
  try {
    const bin = join(f.root, 'bin'); await mkdir(bin);
    const gh = join(bin, 'gh');
    await writeFile(gh, '#!/bin/sh\necho download-unavailable >&2\nexit 1\n'); await chmod(gh, 0o755);
    process.env.PATH = bin;
    await assert.rejects(installRelease({ project: f.project, release: 'v0.1.0-fixture' }), /download-unavailable/);
    await assert.rejects(lstat(f.project), { code: 'ENOENT' });
    assert.deepEqual((await readdir(f.root)).sort(), ['assets', 'bin']);
  } finally { process.env.PATH = oldPath; await f.dispose(); }
});
