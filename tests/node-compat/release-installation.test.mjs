import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { lstat, mkdir, mkdtemp, readFile, readdir, rm, symlink, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import test, { mock } from 'node:test';
import { hostTarget, installRelease, validateManifest } from '../../scripts/install-cordis.mjs';

const hash = value => createHash('sha256').update(value).digest('hex');
const target = hostTarget();
const names = ['@validation-engineering/cordis', '@validation-engineering/cordis-compat-deepseek', '@validation-engineering/cordis-loader'];
// Synthetic records exercise rejection/rollback only. They are not release evidence.
async function fixture() {
  const root = await mkdtemp(join(tmpdir(), 'cordis-release-test-'));
  const assets = join(root, 'assets'); await mkdir(assets);
  const packages = names.map((name, index) => ({ name, version: '0.1.0', file: `package-${index}.tgz`, bytes: 7, sha256: hash('invalid') }));
  for (const item of packages) await writeFile(join(assets, item.file), 'invalid');
  const evidence = {
    sourceCommit: 'a'.repeat(40),
    verification: { schema: 'cordis-verus.verification/v4', status: 'passed', releaseAcceptance: true, paperCoverage: { completionClaimed: false }, sha256: { 'fixture.rs': 'd'.repeat(64) }, proof: { success: true, errors: 0, verified: 40, 'encountered-error': false, 'encountered-vir-error': false, 'is-verifying-entire-crate': true },
      negativeControls: { status: 'not_run', requiredForRelease: false, workflow: '.github/workflows/negative-regression.yml' } },
    npm: { status: 'passed', nativeSourceHashes: { 'fixture.rs': 'd'.repeat(64) }, nativeTarget: target, nativeManifestSha256: 'b'.repeat(64), nativeArtifactSha256: 'c'.repeat(64), packages },
  };
  evidence.verification.proofExecution = {
    schema: 'cordis-verus.positive-proof/v1', status: 'passed', returncode: 0, compiled: true, noCheating: true,
    proof: evidence.verification.proof, sourceHashes: evidence.verification.sha256,
    artifact: { path: 'target/verus/libcordis_kernel.rlib', bytes: 8, sha256: 'a'.repeat(64) },
  };
  evidence.verification.npmDistribution = evidence.npm;
  const bytes = JSON.stringify(evidence); await writeFile(join(assets, 'evidence.json'), bytes);
  const manifest = { schema: 'cordis-verus.runtime-release/v3', target, sourceCommit: evidence.sourceCommit,
    acceptance: { releaseQuality: true, paperCompletion: false, negativeControls: 'not_run' },
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
  assert.equal(hostTarget('win32', 'x64', null), 'win32-x64-napi8');
  assert.throws(() => hostTarget('win32', 'arm64', null), /Unsupported/);
});
test('release manifest rejects development evidence, wrong target, missing and unsafe packages', async () => {
  const f = await fixture();
  try {
    validateManifest(f.manifest, target);
    for (const mutate of [r => { r.acceptance.releaseQuality = false; }, r => { r.target = 'other'; },
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
    f.manifest.acceptance.negativeControls = 'passed'; await f.save();
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
    evidence.verification.proofExecution.sourceHashes['fixture.rs'] = 'e'.repeat(64);
    const bytes = JSON.stringify(evidence); await writeFile(path, bytes);
    f.manifest.evidence.bytes = Buffer.byteLength(bytes); f.manifest.evidence.sha256 = hash(bytes); await f.save();
    await assert.rejects(installRelease({ project: f.project, fromDirectory: f.assets }), /matching full-quality evidence/);
    await noProject(f);
  } finally { await f.dispose(); }
});
test('GitHub download failure does not create a destination', async () => {
  const f = await fixture();
  const download = mock.method(globalThis, 'fetch', async () => { throw new Error('download-unavailable'); });
  try {
    await assert.rejects(installRelease({ project: f.project, release: 'v0.1.0-fixture' }), /download-unavailable/);
    await noProject(f);
  } finally { download.mock.restore(); await f.dispose(); }
});


test('release evidence rejects legacy, partial or uncompiled proof and misleading negatives before npm', async () => {
  for (const mutate of [v => { v.schema = 'cordis-verus.verification/v3'; },
    v => { v.releaseAcceptance = false; }, v => { v.proof.verified = 0; },
    v => { v.proof['is-verifying-entire-crate'] = false; }, v => { v.proofExecution.compiled = false; },
    v => { v.proofExecution.noCheating = false; }, v => { v.negativeControls.status = 'passed'; },
    v => { v.npmDistribution = {}; }]) {
    const f = await fixture();
    try {
      const path = join(f.assets, f.manifest.evidence.file);
      const evidence = JSON.parse(await readFile(path, 'utf8')); mutate(evidence.verification);
      const bytes = JSON.stringify(evidence); await writeFile(path, bytes);
      f.manifest.evidence.bytes = Buffer.byteLength(bytes); f.manifest.evidence.sha256 = hash(bytes); await f.save();
      await assert.rejects(installRelease({ project: f.project, fromDirectory: f.assets }), { code: 'ERR_ASSERTION' });
      await noProject(f);
    } finally { await f.dispose(); }
  }
});


test('shared proof cannot replace a missing, stale or failed host runtime acceptance', async () => {
  for (const mutate of [r => { r.sha256 = {}; }, r => { r.sourceCommit = 'e'.repeat(40); },
    r => { r.target = 'other'; }, r => { r.steps.pop(); }, r => { r.tests.nodeCompatibility.skipped = 1; },
    r => { r.npmDistribution = {}; }, r => { r.proofExecuted = true; }]) {
    const f = await fixture();
    try {
      const path = join(f.assets, f.manifest.evidence.file);
      const evidence = JSON.parse(await readFile(path, 'utf8'));
      evidence.runtimeValidation = {
        schema:'cordis-verus.runtime-validation/v1',status:'passed',proofExecuted:false,releaseAcceptance:false,
        sourceCommit:evidence.sourceCommit,target,sha256:evidence.verification.sha256,
        steps:['clippy','rust-tests','examples','native-build','node-tests','crate-packages','npm-packages'].map(name=>({name,status:'passed'})),
        tests:{total:1,nodeCompatibility:{tests:1,pass:1,fail:0,cancelled:0,skipped:0,todo:0}},
        logSha256:'f'.repeat(64),npmDistribution:evidence.npm,
      };
      mutate(evidence.runtimeValidation);
      const bytes = JSON.stringify(evidence); await writeFile(path, bytes);
      f.manifest.evidence.bytes = Buffer.byteLength(bytes); f.manifest.evidence.sha256 = hash(bytes); await f.save();
      await assert.rejects(installRelease({project:f.project,fromDirectory:f.assets}), {code:'ERR_ASSERTION'});
      await noProject(f);
    } finally { await f.dispose(); }
  }
});
