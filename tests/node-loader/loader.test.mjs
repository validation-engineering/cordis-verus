import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, writeFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';
import { Context } from '../../packages/compat-cordis/index.js';
import { Loader, ModuleHost, readConfig } from '../../packages/compat-loader/index.js';

const fixture = name => new URL(`./fixtures/${name}.mjs`, import.meta.url).href;
const tree = (value, extra = {}) => [
  { id: 'provider', name: fixture('provider'), config: { value, ...extra } },
  { id: 'consumer', name: fixture('consumer') },
];
const host = () => { const ctx = new Context(); const audit = []; ctx.provide('audit', audit); return { ctx, audit, loader: new Loader(ctx) }; };

test('real module plugins load with stable entries and cleanup before replacement', async () => {
  const { ctx, audit, loader } = host();
  try {
    await loader.apply(tree('one'));
    const entry = loader.resolve('provider');
    assert.deepEqual(audit, ['start:one', 'consume:one']);
    await loader.update('provider', { config: { value: 'two' } });
    assert.equal(loader.resolve('provider'), entry);
    assert.equal(entry.state, 'active');
    assert.deepEqual(audit, ['start:one', 'consume:one', 'release:one', 'stop:one', 'start:two', 'consume:two']);
    await loader.dispose();
    assert.deepEqual(audit.slice(-2), ['release:two', 'stop:two']);
  } finally { await ctx.dispose(); }
});

test('candidate setup may await native child creation while external mutations serialize', async () => {
  const { ctx, audit, loader } = host();
  try {
    await loader.apply([{ id: 'parent', name: fixture('children') }]);
    assert.deepEqual(audit, ['child started', 'parent ready']);
    const first = loader.apply(tree('one'));
    const second = loader.apply(tree('two'));
    await Promise.all([first, second]);
    assert.equal(loader.resolve('provider').options.config.value, 'two');
    assert.ok(audit.indexOf('stop:one') < audit.indexOf('start:two'));
    await loader.dispose();
  } finally { await ctx.dispose(); }
});

test('failed candidate is fully drained before the old loaded function recipe restarts', async () => {
  const { ctx, audit, loader } = host();
  try {
    await loader.apply(tree('old'));
    const entry = loader.resolve('provider');
    await assert.rejects(loader.apply(tree('candidate', { fail: true })), error => error.code === 'RELOAD_FAILED' && error.details.restored);
    assert.equal(loader.resolve('provider'), entry);
    assert.equal(ctx.message.value, 'old');
    assert.ok(audit.indexOf('stop:candidate') < audit.lastIndexOf('start:old'));
    assert.equal(loader.lastRecovery.restored, true);
    await loader.dispose();
  } finally { await ctx.dispose(); }
});

test('missing dependencies are diagnosed separately from settled Pending', async () => {
  const { ctx, loader } = host();
  try {
    await assert.rejects(loader.apply([{ id: 'consumer', name: fixture('consumer') }]), error => error.code === 'DEPENDENCIES_UNAVAILABLE' && error.details.entries[0].unavailableServices.includes('message'));
    assert.equal(loader.state, 'empty');
    assert.equal(ctx.snapshot().plugins.length, 1);
    await loader.dispose();
  } finally { await ctx.dispose(); }
});

test('JSON includes preserve source-relative modules, stable paths and independent isolation', async () => {
  const { ctx, audit, loader } = host();
  const directory = await mkdtemp(join(tmpdir(), 'cordis-loader-'));
  try {
    await writeFile(join(directory, 'included.json'), JSON.stringify(tree('included')));
    await writeFile(join(directory, 'root.json'), JSON.stringify([
      { id: 'left', include: './included.json', isolate: ['message'] },
      { id: 'right', group: true, isolate: ['message'], entries: tree('right') },
    ]));
    await loader.loadFile(join(directory, 'root.json'));
    assert.equal(loader.resolve('left/provider').state, 'active');
    assert.equal(loader.resolve('right/consumer').state, 'active');
    assert.equal(ctx.get('message'), undefined);
    assert.deepEqual(audit.filter(value => value.startsWith('consume:')).sort(), ['consume:included', 'consume:right']);
    await loader.setEnabled('left', false);
    assert.equal(loader.resolve('left/provider').state, 'disabled');
    assert.equal(loader.resolve('right/provider').state, 'active');
    await loader.dispose();
  } finally { await ctx.dispose(); await rm(directory, { recursive: true, force: true }); }
});

test('validation and failed imports leave the old graph untouched', async () => {
  const { ctx, audit, loader } = host();
  try {
    await loader.apply(tree('old'));
    await assert.rejects(loader.apply([{ id: 'wrong', name: './missing.mjs' }]), /ENOENT/);
    await assert.rejects(loader.apply([{ id: 'bad', name: fixture('provider'), config: { invalid: () => {} } }]), /JSON/);
    assert.equal(ctx.message.value, 'old');
    assert.deepEqual(audit, ['start:old', 'consume:old']);
    await loader.dispose();
  } finally { await ctx.dispose(); }
});

test('include cycles and unsupported ESM reset fail explicitly', async () => {
  const directory = await mkdtemp(join(tmpdir(), 'cordis-cycle-'));
  try {
    await writeFile(join(directory, 'loop.json'), JSON.stringify([{ id: 'loop', include: './loop.json' }]));
    await assert.rejects(readConfig(join(directory, 'loop.json')), error => error.code === 'INCLUDE_CYCLE');
    assert.throws(() => new ModuleHost().reset(), error => error.code === 'DOMAIN_RESTART_REQUIRED');
    await assert.rejects(new ModuleHost().load('some-package', pathToFileURL(`${directory}/`).href), error => error.code === 'MODULE_SPECIFIER');
  } finally { await rm(directory, { recursive: true, force: true }); }
});

test('reentrant external mutation fails explicitly instead of deadlocking candidate setup', async () => {
  const { ctx, audit, loader } = host();
  audit.loader = loader;
  try {
    await loader.apply(tree('old'));
    await assert.rejects(loader.apply([{ id: 'nested', name: fixture('reentrant') }]), error => error.code === 'RELOAD_FAILED' && error.cause.code === 'REENTRANT_MUTATION');
    assert.equal(ctx.message.value, 'old');
    await loader.dispose();
  } finally { await ctx.dispose(); }
});

test('a failed candidate cleanup blocks already queued replacement work', async () => {
  const { ctx, audit, loader } = host();
  try {
    await loader.apply(tree('old'));
    const candidate = loader.apply(tree('candidate', { fail: true, cleanupFailure: true }));
    const queued = loader.apply(tree('must-not-start'));
    await assert.rejects(candidate, error => error.code === 'CLEANUP_BLOCKED');
    await assert.rejects(queued, error => error.code === 'CLEANUP_BLOCKED');
    assert.equal(loader.state, 'blocked');
    assert.equal(audit.includes('start:must-not-start'), false);
    assert.equal(audit.filter(value => value === 'start:old').length, 1);
    // Make only the failing inverse recoverable; successful effects stay drained.
    const failed = [...ctx.registry.values()].flatMap(runtime => [...runtime.fibers]).find(fiber => fiber.config?.cleanupFailure);
    failed.config.cleanupFailure = false;
    await loader.retryCleanup();
    assert.equal(loader.state, 'empty');
    await loader.apply(tree('recovered'));
    await loader.dispose();
  } finally { await ctx.dispose(); }
});
