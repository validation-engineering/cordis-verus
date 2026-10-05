import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, writeFile, readFile, rm, symlink, mkdir, stat } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { WorkerDomain, Artifact } from '../../packages/compat-loader/worker.js';

const plugin = `
import { Service } from 'cordis';
import { label } from './dependency.mjs';
import { appendFileSync, writeFileSync } from 'node:fs';
export default class Message extends Service {
  constructor(ctx, config) {
    super(ctx, 'message');
    this.value = label;
    this.trace = config.trace;
    appendFileSync(config.trace, 'start:' + label + '\\n');
    ctx.effect(() => () => {
      appendFileSync(config.trace, 'stop:' + label + '\\n');
      if (config.cleanupFailure) throw new Error('candidate cleanup failed');
    });
    if (config.mutateLaunch) writeFileSync(new URL('./dependency.mjs', import.meta.url), 'export const label = "tampered";');
    if (config.fail) throw new Error('candidate setup failed');
  }
  hello(name) { return this.value + ':' + name; }
  async wait() {
    await new Promise(resolve => setTimeout(resolve, 50));
    appendFileSync(this.trace, 'call:done\\n');
    return 'done';
  }
  crash() { process.exit(23); }
  crashZero() { process.exit(0); }
}
`;
async function fixture() {
  const directory = await mkdtemp(join(tmpdir(), 'cordis-project-'));
  const external = await mkdtemp(join(tmpdir(), 'cordis-trace-'));
  const trace = join(external, 'trace.log');
  await writeFile(trace, '');
  await writeFile(join(directory, 'plugin.mjs'), plugin);
  const write = async (label, extra = {}) => {
    await writeFile(join(directory, 'dependency.mjs'), `export const label = ${JSON.stringify(label)};`);
    await writeFile(join(directory, 'plugins.json'), JSON.stringify([{ id: 'message', name: './plugin.mjs', config: { trace, ...extra } }]));
    await writeFile(join(directory, 'cordis.json'), JSON.stringify([{ id: 'plugins', include: './plugins.json' }]));
  };
  const lines = async () => (await readFile(trace, 'utf8')).trim().split('\n');
  const cleanup = async () => { await rm(directory, { recursive: true, force: true }); await rm(external, { recursive: true, force: true }); };
  return { directory, write, lines, cleanup };
}

test('WorkerDomain loads unmodified cordis import and reloads a transitive ESM dependency', async () => {
  const project = await fixture();
  const domain = new WorkerDomain({ timeout: 3000 });
  try {
    await project.write('old');
    const first = await domain.load(project.directory);
    assert.equal(await domain.call('message', 'hello', 'Alice'), 'old:Alice');
    assert.equal((await domain.diagnostics())[1].id, 'plugins/message');
    await project.write('new');
    const second = await domain.reload();
    assert.notEqual(first.digest, second.digest);
    assert.equal(await domain.call('message', 'hello', 'Alice'), 'new:Alice');
    await domain.dispose();
    assert.deepEqual(await project.lines(), ['start:old', 'stop:old', 'start:new', 'stop:new']);
  } finally { if (domain.state !== 'closed') await domain.abandon(); await project.cleanup(); }
});

test('failed code reload restores captured old dependencies even if launch and source changed', async () => {
  const project = await fixture();
  const domain = new WorkerDomain({ timeout: 3000 });
  try {
    await project.write('old', { mutateLaunch: true });
    const first = await domain.load(project.directory);
    await project.write('candidate', { fail: true });
    await assert.rejects(domain.reload(), error => error.code === 'RELOAD_FAILED' && error.details.restored);
    assert.equal(domain.lastRecovery.digest, first.digest);
    assert.equal(await domain.call('message', 'hello', 'Alice'), 'old:Alice');
    assert.deepEqual(await project.lines(), ['start:old', 'stop:old', 'start:candidate', 'stop:candidate', 'start:old']);
    await domain.dispose();
  } finally { if (domain.state !== 'closed') await domain.abandon(); await project.cleanup(); }
});

test('worker cleanup failure blocks restoration and forced abandonment is explicit', async () => {
  const project = await fixture();
  const domain = new WorkerDomain({ timeout: 3000 });
  try {
    await project.write('old');
    await domain.load(project.directory);
    await project.write('candidate', { fail: true, cleanupFailure: true });
    await assert.rejects(domain.reload(), error => error.code === 'CLEANUP_BLOCKED');
    assert.equal(domain.state, 'blocked');
    assert.deepEqual(await project.lines(), ['start:old', 'stop:old', 'start:candidate', 'stop:candidate']);
    await assert.rejects(domain.load(project.directory), error => error.code === 'DOMAIN_BLOCKED');
    assert.deepEqual(await domain.abandon(), { abandoned: true, cleanupConfirmed: false });
  } finally { if (domain.state !== 'abandoned') await domain.abandon(); await project.cleanup(); }
});

test('Worker shutdown drains in-flight service calls before plugin cleanup', async () => {
  const project = await fixture();
  const domain = new WorkerDomain({ timeout: 3000 });
  try {
    await project.write('one');
    await domain.load(project.directory);
    const call = domain.call('message', 'wait');
    const shutdown = domain.dispose();
    await assert.rejects(domain.call('message', 'hello', 'late'), error => error.code === 'DOMAIN_NOT_READY');
    assert.equal(await call, 'done');
    await shutdown;
    assert.deepEqual(await project.lines(), ['start:one', 'call:done', 'stop:one']);
  } finally { if (domain.state !== 'closed') await domain.abandon(); await project.cleanup(); }
});

test('unexpected Worker exit cannot be reported as successful cleanup or rollback', async () => {
  const project = await fixture();
  const domain = new WorkerDomain({ timeout: 3000 });
  try {
    await project.write('crashing');
    await domain.load(project.directory);
    await assert.rejects(domain.call('message', 'crash'), error => error.code === 'DOMAIN_ABANDONED');
    assert.equal(domain.state, 'abandoned');
    await assert.rejects(domain.reload(), error => error.code === 'DOMAIN_BLOCKED');
    assert.deepEqual(await project.lines(), ['start:crashing']);
  } finally { await domain.abandon(); await project.cleanup(); }
});

test('artifact capture rejects symlinks and runtime boundaries reject non-JSON arguments', async () => {
  const project = await fixture();
  const domain = new WorkerDomain({ timeout: 3000 });
  try {
    await project.write('one');
    await domain.load(project.directory);
    await assert.rejects(domain.call('message', 'hello', () => {}), /JSON/);
    await domain.dispose();
    await symlink('dependency.mjs', join(project.directory, 'alias.mjs'));
    await assert.rejects(Artifact.capture(project.directory), error => error.code === 'ARTIFACT_SYMLINK');
  } finally { if (domain.state !== 'closed') await domain.abandon(); await project.cleanup(); }
});


test('artifact digest retains empty directories and excludes uncaptured later additions', async () => {
  const project = await fixture();
  let artifact;
  let launch;
  try {
    await project.write('one');
    await mkdir(join(project.directory, 'empty-data'));
    artifact = await Artifact.capture(project.directory);
    await writeFile(join(artifact.root, 'injected.mjs'), 'throw new Error("not captured")');
    launch = await artifact.launch('cordis.json');
    assert.equal((await stat(join(launch.directory, 'empty-data'))).isDirectory(), true);
    await assert.rejects(readFile(join(launch.directory, 'injected.mjs')), error => error.code === 'ENOENT');
    await writeFile(join(artifact.root, 'dependency.mjs'), 'export const label = "modified"');
    await assert.rejects(artifact.launch('cordis.json'), error => error.code === 'ARTIFACT_CHANGED');
  } finally {
    if (launch) await rm(launch.directory, { recursive: true, force: true });
    if (artifact) await artifact.dispose();
    await project.cleanup();
  }
});

test('Worker configuration includes cannot leave the captured artifact', async () => {
  const project = await fixture();
  const domain = new WorkerDomain({ timeout: 3000 });
  try {
    await project.write('one');
    await writeFile(join(project.directory, 'cordis.json'), JSON.stringify([{ id: 'outside', include: join(project.directory, 'plugins.json') }]));
    await assert.rejects(domain.load(project.directory), error => error.code === 'CONFIG_OUTSIDE_ARTIFACT');
    assert.equal(domain.state, 'empty');
    await domain.dispose();
  } finally { if (domain.state !== 'closed') await domain.abandon(); await project.cleanup(); }
});


test('exit zero during shutdown still requires a normal disposal acknowledgement', async () => {
  const project = await fixture();
  const domain = new WorkerDomain({ timeout: 3000 });
  try {
    await project.write('exit-zero');
    await domain.load(project.directory);
    const call = domain.call('message', 'crashZero');
    const shutdown = domain.dispose();
    await Promise.all([
      assert.rejects(call, error => error.code === 'DOMAIN_ABANDONED'),
      assert.rejects(shutdown, error => error.code === 'DOMAIN_ABANDONED'),
    ]);
    assert.equal(domain.state, 'abandoned');
    assert.deepEqual(await project.lines(), ['start:exit-zero']);
  } finally { await domain.abandon(); await project.cleanup(); }
});
