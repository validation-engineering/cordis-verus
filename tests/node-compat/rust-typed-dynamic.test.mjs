import test from 'node:test';
import assert from 'node:assert/strict';
import { fileURLToPath } from 'node:url';
import { spawnSync } from 'node:child_process';
import { Context as CordisContext, FiberState } from '../../packages/compat-cordis/index.js';
import { Context as HarnessContext } from '../../packages/compat-harness/index.js';
const addon = fileURLToPath(new URL('../../target/node-compat/interop-fixture.node', import.meta.url));
const turn = () => new Promise(resolve => setImmediate(resolve));
const errorMessages = error => [error?.message, ...(error?.errors ?? []).map(errorMessages), error?.cause ? errorMessages(error.cause) : ""].join(" | ");
async function waitFor(predicate, description) {
  const deadline = Date.now() + 8000;
  while (!predicate()) {
    if (Date.now() >= deadline) throw new Error(`Timed out: ${description}`);
    await turn();
  }
}
for (const [profile, Context] of [['cordis', CordisContext], ['harness', HarnessContext]]) {
  async function environment(t) {
    const ctx = new Context({ addon });
    t.after(async () => { await ctx.dispose(); assert.equal(ctx.snapshot().plugins.length, 0); });
    await ctx.rustPlugin('fixture.typedControl');
    return ctx;
  }
  test(`${profile}: typed dynamic publication shares its original Arc with a real typed consumer`, async t => {
    const ctx = await environment(t);
    const owner = await ctx.rustPlugin('fixture.typedDynamic', { publishDuringSetup: 7 });
    await ctx.settle();
    const reader = await ctx.rustPlugin('fixture.typedDynamicReader');
    assert.equal(ctx.typedDynamicValue.read(), 7);
    assert.deepEqual(ctx.typedDynamicReader.read(), { current: 7, original: 7, sameArc: true });
    assert.equal(ctx.typedControl.events().find(event => event.phase === 'dynamic-reader:setup')?.sameArc, true);
    const published = ctx.typedDynamicManager.status('initial');
    assert.equal(published.initialized, true);
    assert.ok(ctx.snapshot().plugins.some(node => node.id === published.id));
    assert.equal(ctx.snapshot().plugins.length, 5); // root, control, owner, publication child, consumer
    const original = ctx.typedDynamicValue;
    ctx.typedDynamicManager.set('initial', 12);
    await ctx.settle();
    assert.equal(original.read(), 12);
    assert.deepEqual(ctx.typedDynamicReader.read(), { current: 12, original: 7, sameArc: false });
    await owner.dispose();
    assert.equal(reader.state, FiberState.PENDING);
    assert.throws(() => original.read(), /STALE|no longer admitted/);
    const events = ctx.typedControl.events();
    assert.equal(events.find(event => event.phase === 'dynamic-reader:cleanup')?.value, 12);
    assert.ok(events.findIndex(event => event.phase === 'dynamic-reader:cleanup') < events.findIndex(event => event.phase === 'dynamic-owner:cleanup'));
  });
  test(`${profile}: active typed handle can withdraw, join and republish without restarting its owner`, async t => {
    const ctx = await environment(t);
    const owner = await ctx.rustPlugin('fixture.typedDynamic');
    const manager = ctx.typedDynamicManager;
    manager.publish('first', 3);
    await ctx.settle();
    const old = ctx.typedDynamicValue;
    const id = manager.status('first').id;
    manager.dispose('first');
    await manager.join('first');
    await ctx.settle();
    assert.equal(manager.status('first').finished, true);
    assert.equal(ctx.snapshot().plugins.some(node => node.id === id), false);
    assert.equal(owner.state, FiberState.ACTIVE);
    assert.throws(() => old.read(), /STALE|no longer admitted/);
    assert.throws(() => manager.set('first', 9), /cancelled/);
    manager.publish('second', 8);
    await ctx.settle();
    assert.equal(ctx.typedDynamicValue.read(), 8);
    assert.notEqual(manager.status('second').id, id);
    assert.equal(ctx.snapshot().plugins.length, 4);
  });
  test(`${profile}: owner restart closes prior dynamic handles and preserves the logical owner`, async t => {
    const ctx = await environment(t);
    const owner = await ctx.rustPlugin('fixture.typedDynamic', { publishDuringSetup: 6 });
    await ctx.settle();
    const manager = ctx.typedDynamicManager, value = ctx.typedDynamicValue;
    const first = manager.status('initial').id;
    await owner.restart();
    await ctx.settle();
    assert.equal(owner.state, FiberState.ACTIVE);
    assert.throws(() => manager.publish('stale', 100), /STALE|no longer admitted/);
    assert.throws(() => value.read(), /STALE|no longer admitted/);
    assert.equal(ctx.typedDynamicValue.read(), 6);
    assert.notEqual(ctx.typedDynamicManager.status('initial').id, first);
    assert.equal(ctx.snapshot().plugins.some(node => node.id === first), false);
    assert.equal(ctx.typedControl.events().filter(event => event.phase === 'dynamic-owner:cleanup').length, 1);
  });
  test(`${profile}: conflicting publication reports its handle error while the owner and first service remain active`, async t => {
    const ctx = await environment(t);
    const owner = await ctx.rustPlugin('fixture.typedDynamic', { publishDuringSetup: 2 });
    await ctx.settle();
    const manager = ctx.typedDynamicManager;
    manager.publish('conflict', 9);
    await ctx.settle().catch(() => {});
    const conflict = manager.status('conflict');
    assert.ok(conflict.errors.some(error => /registered|Duplicate|conflict/i.test(error)), JSON.stringify(conflict));
    assert.equal(owner.state, FiberState.ACTIVE);
    assert.equal(ctx.typedDynamicValue.read(), 2);
    manager.dispose('conflict');
    await assert.rejects(manager.join('conflict'), /registered|Duplicate|conflict/i);
    await ctx.settle().catch(() => {});
    assert.equal(manager.status('conflict').finished, true);
    if (conflict.id !== null) assert.equal(ctx.snapshot().plugins.some(node => node.id === conflict.id), false);
  });
  test(`${profile}: publication join waits for a JavaScript consumer inverse before republishing`, async t => {
    const ctx = await environment(t);
    await ctx.rustPlugin('fixture.typedDynamic', { publishDuringSetup: 1 });
    await ctx.settle();
    const entered = Promise.withResolvers(), gate = Promise.withResolvers();
    const seen = [], manager = ctx.typedDynamicManager;
    let block = true;
    try {
    const consumer = await ctx.plugin({ inject: ['typedDynamicValue'], apply(c) {
      seen.push(c.typedDynamicValue.read());
      return async () => {
        if (block) { entered.resolve(); await gate.promise; }
        seen.push(c.typedDynamicValue.read());
      };
    } });
    manager.dispose('initial');
    let done = false;
    const join = manager.join('initial').then(() => { done = true; });
    await entered.promise;
    await turn();
    assert.equal(done, false);
    assert.equal(manager.status('initial').finished, false);
    assert.ok(ctx.snapshot().plugins.some(node => node.id === manager.status('initial').id));
    assert.equal(ctx.get('typedDynamicValue'), undefined);
    block = false; gate.resolve();
    await join; await ctx.settle();
    assert.deepEqual(seen, [1, 1]);
    assert.equal(consumer.state, FiberState.PENDING);
    manager.publish('replacement', 9);
    await ctx.settle();
    assert.equal(consumer.state, FiberState.ACTIVE);
    assert.deepEqual(seen, [1, 1, 9]);
    assert.equal(ctx.typedDynamicValue.read(), 9);
    } finally { block = false; gate.resolve(); }
  });
  test(`${profile}: a committed consumer cannot await removal of its own typed service dependency`, async t => {
    const ctx = await environment(t);
    await ctx.rustPlugin('fixture.typedDynamic', { publishDuringSetup: 4 });
    await ctx.settle();
    const consumer = await ctx.plugin({
      inject: ['typedDynamicValue', 'typedDynamicManager'],
      async apply(c) {
        await assert.rejects(c.typedDynamicManager.join('initial'), /ReentrantServiceJoin/);
        assert.equal(c.typedDynamicValue.read(), 4);
      },
    });
    assert.equal(consumer.state, FiberState.ACTIVE);
    assert.equal(ctx.typedDynamicManager.status('initial').finished, false);
    await consumer.dispose();
    ctx.typedDynamicManager.dispose('initial');
    await ctx.typedDynamicManager.join('initial');
  });
  test(`${profile}: typed resource next, call and close inherit the actual consumer join guard`, async t => {
    const ctx = await environment(t);
    await ctx.rustPlugin('fixture.typedDynamic', { publishDuringSetup: 5 });
    await ctx.settle();
    const consumer = await ctx.plugin({
      inject: ['typedDynamicValue', 'typedDynamicManager'],
      async apply(c) {
        const stream = c.typedDynamicManager.joinStream('initial', true);
        await assert.rejects(stream.next(), /ReentrantServiceJoin/);
        await stream.return();
        const object = c.typedDynamicManager.joinObject('initial', true);
        await assert.rejects(object.call('join'), /ReentrantServiceJoin/);
        await object.close();
        assert.equal(c.typedDynamicValue.read(), 5);
      },
    });
    assert.equal(consumer.state, FiberState.ACTIVE);
    const events = ctx.typedControl.events();
    for (const kind of ['stream', 'object']) {
      assert.equal(events.filter(event => event.phase === 'dynamic-resource:close-join-rejected' && event.kind === kind).length, 1);
      assert.equal(events.filter(event => event.phase === 'dynamic-resource:closed' && event.kind === kind).length, 1);
    }
    assert.equal(ctx.typedDynamicManager.status('initial').finished, false);
    await consumer.dispose();
    ctx.typedDynamicManager.dispose('initial');
    await ctx.typedDynamicManager.join('initial');
  });
  test(`${profile}: async setup cannot await its own newly allocated publication and still restores its inverse`, async t => {
    const ctx = await environment(t);
    const failing = ctx.rustPlugin('fixture.typedDynamicSelfJoin');
    await assert.rejects(Promise.resolve(failing), /ReentrantServiceJoin/);
    assert.equal(ctx.typedControl.events().filter(event => event.phase === 'dynamic-self-join:cleanup').length, 1);
    assert.equal(ctx.get('typedDynamicValue'), undefined);
    await failing.dispose();
    await ctx.settle();
    assert.equal(ctx.snapshot().plugins.length, 2);
  });
  test(`${profile}: unknown publication uses its handle error while unknown child fails and restores the owner`, async t => {
    const ctx = await environment(t);
    const owner = await ctx.rustPlugin('fixture.typedDynamic');
    const manager = ctx.typedDynamicManager;
    manager.publishUnknown('unknown');
    await ctx.settle();
    assert.equal(owner.state, FiberState.ACTIVE);
    const rejected = manager.status('unknown');
    assert.equal(rejected.id, null);
    assert.equal(rejected.finished, true);
    assert.ok(rejected.errors.some(error => /UnknownTypedChildService/.test(error)));
    await assert.rejects(manager.join('unknown'), /UnknownTypedChildService/);
    let failure;
    try { manager.mountUnknown('unknown-child'); } catch (error) { failure = error; }
    await ctx.settle().catch(error => { failure ??= error; });
    assert.equal(owner.state, FiberState.FAILED);
    if (failure) assert.match(errorMessages(failure), /UnknownTypedChildService/);
    assert.equal(ctx.get('typedDynamicManager'), undefined);
    const events = ctx.typedControl.events();
    assert.equal(events.filter(event => event.phase === 'unknown-child:setup').length, 0);
    assert.equal(events.filter(event => event.phase === 'dynamic-owner:cleanup').length, 1);
    await owner.dispose();
    assert.equal(ctx.snapshot().plugins.length, 2);
  });
  test(`${profile}: checked dynamic publications recheck consumers and remain independent across realms`, async t => {
    const ctx = await environment(t);
    const left = ctx.isolate('typedDynamicValue').isolate('typedDynamicManager');
    const right = ctx.isolate('typedDynamicValue').isolate('typedDynamicManager');
    await left.rustPlugin('fixture.typedDynamic', { publishDuringSetup: 3, checked: true });
    await right.rustPlugin('fixture.typedDynamic', { publishDuringSetup: 20, checked: true });
    await ctx.settle();
    const low = await left.plugin({ inject: { typedDynamicValue: { minimum: 5 } }, apply() {} });
    const high = await right.plugin({ inject: { typedDynamicValue: { minimum: 5 } }, apply() {} });
    assert.equal(low.state, FiberState.PENDING);
    assert.equal(high.state, FiberState.ACTIVE);
    left.typedDynamicManager.set('initial', 9);
    await ctx.settle();
    assert.equal(low.state, FiberState.ACTIVE);
    assert.equal(right.typedDynamicValue.read(), 20);
    right.typedDynamicManager.dispose('initial');
    await right.typedDynamicManager.join('initial');
    await ctx.settle();
    assert.equal(high.state, FiberState.PENDING);
    assert.equal(low.state, FiberState.ACTIVE);
  });
  test(`${profile}: typed mount_in preserves two isolated nested child graphs and closes every inverse`, async t => {
    const ctx = await environment(t);
    const owner = await ctx.rustPlugin('fixture.typedDynamic');
    ctx.typedDynamicManager.mount('plain');
    ctx.typedDynamicManager.mountIsolated('left', 11);
    ctx.typedDynamicManager.mountIsolated('right', 23);
    await ctx.settle();
    const events = ctx.typedControl.events();
    assert.ok(events.some(event => event.phase === 'dynamic-child:setup' && event.label === 'plain'));
    assert.deepEqual(events.filter(event => event.phase === 'dynamic-nested:setup').map(({ label, value, sameArc }) => ({ label, value, sameArc })).sort((a, b) => a.label.localeCompare(b.label)), [
      { label: 'left', value: 11, sameArc: true }, { label: 'right', value: 23, sameArc: true },
    ]);
    assert.equal(ctx.get('typedDynamicValue'), undefined);
    assert.equal(ctx.get('typedDynamicReader'), undefined);
    assert.equal(ctx.snapshot().plugins.length, 8);
    await owner.dispose();
    assert.equal(ctx.snapshot().plugins.length, 2);
    assert.deepEqual(ctx.typedControl.events().filter(event => event.phase === 'dynamic-nested:cleanup').map(event => event.value).sort((a, b) => a - b), [11, 23]);
    assert.equal(ctx.typedControl.events().filter(event => event.phase === 'dynamic-child:cleanup' && event.label === 'plain').length, 1);
  });
  test(`${profile}: withdrawing an owner joins pending child setup and its late inverse`, async t => {
    const ctx = await environment(t);
    const owner = await ctx.rustPlugin('fixture.typedDynamic');
    const control = ctx.typedControl;
    ctx.typedDynamicManager.mountWaiting('pending');
    await waitFor(() => control.events().some(event => event.phase === 'dynamic-child:waiting'), 'child setup starts');
    let done = false;
    const shutdown = owner.dispose().then(() => { done = true; });
    await turn();
    assert.equal(done, false);
    assert.ok(ctx.snapshot().plugins.some(node => node.id === owner.id));
    control.release('dynamic:pending');
    await shutdown;
    const events = control.events();
    assert.deepEqual(events.find(event => event.phase === 'dynamic-child:landed'), { phase: 'dynamic-child:landed', label: 'pending', cancelled: true, lateRejected: true });
    assert.equal(events.filter(event => event.phase === 'dynamic-child:late-cleanup').length, 1);
    assert.ok(events.findIndex(event => event.phase === 'dynamic-child:late-cleanup') < events.findIndex(event => event.phase === 'dynamic-owner:cleanup'));
    assert.equal(ctx.snapshot().plugins.length, 2);
  });
}

test('typed child inverse failure keeps its actual node and owner resources; retry cannot replay FnOnce', () => {
  const index = new URL('../../packages/compat-cordis/index.js', import.meta.url).href;
  const script = `import assert from 'node:assert/strict';import {Context} from ${JSON.stringify(index)};
  const ctx=new Context({addon:${JSON.stringify(addon)}});await ctx.rustPlugin('fixture.typedControl');
  const owner=await ctx.rustPlugin('fixture.typedDynamic');const control=ctx.typedControl;
  ctx.typedDynamicManager.mountFailing('failed');await ctx.settle();
  const message=e=>[e?.message,...(e?.errors??[]).map(message),e?.cause?message(e.cause):''].join(' | ');
  await assert.rejects(owner.dispose(),e=>/dynamic child inverse failed/.test(message(e)));
  const failed=ctx.snapshot().plugins.find(n=>n.cleanupFailed);assert.ok(failed);
  const child=ctx.fiber._domain.fibers.get(failed.id);assert.ok(child);
  await assert.rejects(child.retryCleanup(),e=>/dynamic child inverse failed|CLEANUP_FAILED/.test(message(e)));
  const nodes=ctx.snapshot().plugins;assert.ok(nodes.some(n=>n.id===owner.id));assert.ok(nodes.some(n=>n.id===failed.id&&n.cleanupFailed));
  assert.equal(control.events().filter(e=>e.phase==='dynamic-child:cleanup').length,1);
  assert.equal(control.events().filter(e=>e.phase==='dynamic-owner:cleanup').length,0);console.log('retained');`;
  const result = spawnSync(process.execPath, ['--input-type=module', '--eval', script], { encoding: 'utf8', timeout: 15000 });
  assert.equal(result.status, 0, result.stderr || String(result.error));
  assert.equal(result.stdout.trim(), 'retained');
});
