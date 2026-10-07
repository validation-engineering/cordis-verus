import test from 'node:test';
import assert from 'node:assert/strict';
import { setImmediate as nextTurn } from 'node:timers/promises';
import { Context as CordisContext, domainMutation } from '../../packages/compat-cordis/index.js';
import { Context as HarnessContext } from '../../packages/compat-harness/index.js';

async function fixture(t, options = {}) {
  const ctx = new (options.Context ?? CordisContext)();
  t.after(() => ctx.dispose());
  const observations = [], cleanups = [], providerStarts = [];
  const provider = await ctx.plugin({
    ...(options.providerSchema && { Config: options.providerSchema }),
    apply(child, config) {
      providerStarts.push(config.value);
      child.provide('coordinatedValue', config.value);
      options.providerSetup?.(child, config);
    },
  }, { value: 1 });
  const consumer = await ctx.plugin({
    inject: ['coordinatedValue'],
    ...(options.consumerSchema && { Config: options.consumerSchema }),
    async apply(child, config) {
      const pair = [child.coordinatedValue, config.value];
      observations.push(pair);
      child.effect(() => async () => {
        cleanups.push(pair);
        await options.consumerCleanup?.(child, config);
      });
      await options.consumerSetup?.(child, config);
    },
  }, { value: 1 });
  return { ctx, provider, consumer, observations, cleanups, providerStarts };
}

const sequential = [[1, 1], [2, 1], [2, 2]];
const messageTree = error => [error?.message, ...(error instanceof AggregateError ? error.errors.flatMap(messageTree) : [])].join(' | ');

// These tests observe actual setup/cleanup callbacks. No coordinator internals
// determine whether the two public update calls share a lifecycle boundary.
test('cordis: same-stack provider and committed consumer updates avoid a setup with the old consumer config', async t => {
  const f = await fixture(t);
  const providerUpdate = f.provider.update({ value: 2 });
  const consumerUpdate = f.consumer.update({ value: 2 });
  assert.equal(typeof providerUpdate.then, 'function');
  assert.equal(typeof consumerUpdate.then, 'function');
  assert.deepEqual(await Promise.all([providerUpdate, consumerUpdate]), [undefined, undefined]);
  assert.deepEqual(f.observations, [[1, 1], [2, 2]]);
  assert.deepEqual(f.cleanups, [[1, 1]]);
  assert.deepEqual(f.providerStarts, [1, 2]);
});

test('cordis: coordinated results await asynchronous cleanup and the last setup', { timeout: 5000 }, async t => {
  const cleanupEntered = Promise.withResolvers(), cleanupRelease = Promise.withResolvers();
  const setupEntered = Promise.withResolvers(), setupRelease = Promise.withResolvers();
  const f = await fixture(t, {
    consumerCleanup: async (_child, config) => {
      if (config.value === 1) { cleanupEntered.resolve(); await cleanupRelease.promise; }
    },
    consumerSetup: async (_child, config) => {
      if (config.value === 2) { setupEntered.resolve(); await setupRelease.promise; }
    },
  });
  let providerLanded = false, consumerLanded = false, followingEntered = false;
  const first = f.provider.update({ value: 2 }).finally(() => { providerLanded = true; });
  const second = f.consumer.update({ value: 2 }).finally(() => { consumerLanded = true; });
  const following = domainMutation(f.ctx, () => { followingEntered = true; });
  try {
    await cleanupEntered.promise;
    await nextTurn();
    assert.equal(providerLanded, false);
    assert.equal(consumerLanded, false);
    cleanupRelease.resolve();
    await setupEntered.promise;
    await nextTurn();
    assert.equal(providerLanded, false, 'provider result must retain the shared lifecycle barrier');
    assert.equal(consumerLanded, false);
    assert.equal(followingEntered, false, 'the next transaction must wait for the same barrier');
    setupRelease.resolve();
    await Promise.all([first, second, following]);
    assert.equal(followingEntered, true);
    assert.deepEqual(f.observations, [[1, 1], [2, 2]]);
    assert.deepEqual(f.cleanups, [[1, 1]]);
  } finally {
    cleanupRelease.resolve(); setupRelease.resolve();
    await Promise.allSettled([first, second, following]);
  }
});

test('cordis: repeated updates of one fiber retain each intermediate revision', async t => {
  const f = await fixture(t);
  await Promise.all([f.provider.update({ value: 2 }), f.provider.update({ value: 3 })]);
  assert.deepEqual(f.observations, [[1, 1], [2, 1], [3, 1]]);
  assert.deepEqual(f.providerStarts, [1, 2, 3]);
  assert.equal(f.cleanups.length, 2);
});

test('cordis: an unrelated update separates provider and consumer revisions', async t => {
  const f = await fixture(t), unrelatedStarts = [];
  const unrelated = await f.ctx.plugin((_child, config) => { unrelatedStarts.push(config.value); }, { value: 1 });
  const first = f.provider.update({ value: 2 });
  const middle = unrelated.update({ value: 2 });
  const last = f.consumer.update({ value: 2 });
  await Promise.all([first, middle, last]);
  assert.deepEqual(f.observations, sequential);
  assert.deepEqual(unrelatedStarts, [1, 2]);
});

test('cordis: an explicit transaction separates provider and consumer revisions', async t => {
  const f = await fixture(t);
  const first = f.provider.update({ value: 2 });
  const middle = domainMutation(f.ctx, () => {
    assert.deepEqual(f.observations, [[1, 1], [2, 1]]);
    return 'transaction boundary';
  });
  const last = f.consumer.update({ value: 2 });
  const results = await Promise.all([first, middle, last]);
  assert.equal(results[1], 'transaction boundary');
  assert.deepEqual(f.observations, sequential);
});

test('cordis: an intervening restart retains its separate cleanup and setup', async t => {
  const f = await fixture(t);
  const first = f.provider.update({ value: 2 });
  const middle = f.consumer.restart();
  const last = f.consumer.update({ value: 2 });
  await Promise.all([first, middle, last]);
  assert.deepEqual(f.observations, [[1, 1], [2, 1], [2, 1], [2, 2]]);
  assert.equal(f.cleanups.length, 3);
});

test('cordis: an intervening disposal is not overtaken by the consumer update', async t => {
  const f = await fixture(t);
  let observedAtDisposal;
  const unrelated = await f.ctx.plugin(child => child.effect(() => () => {
    observedAtDisposal = f.observations.map(pair => [...pair]);
  }));
  const first = f.provider.update({ value: 2 });
  const middle = unrelated.dispose();
  const last = f.consumer.update({ value: 2 });
  await Promise.all([first, middle, last]);
  assert.deepEqual(observedAtDisposal, [[1, 1], [2, 1]]);
  assert.deepEqual(f.observations, sequential);
  assert.equal(unrelated.uid, null);
});

test('cordis: a microtask boundary closes the provider update admission window', async t => {
  const f = await fixture(t);
  const first = f.provider.update({ value: 2 });
  await Promise.resolve();
  const second = f.consumer.update({ value: 2 });
  await Promise.all([first, second]);
  assert.deepEqual(f.observations, sequential);
});

test('cordis: updates queued behind an existing transaction remain independent FIFO revisions', async t => {
  const f = await fixture(t), release = Promise.withResolvers();
  const preceding = domainMutation(f.ctx, () => release.promise);
  const first = f.provider.update({ value: 2 });
  const second = f.consumer.update({ value: 2 });
  try {
    await nextTurn();
    assert.deepEqual(f.observations, [[1, 1]]);
    release.resolve();
    await Promise.all([preceding, first, second]);
    assert.deepEqual(f.observations, sequential);
  } finally { release.resolve(); await Promise.allSettled([preceding, first, second]); }
});

for (const target of ['provider', 'consumer']) {
  test(`cordis: a custom ${target} Config validator preserves ordinary update ordering`, async t => {
    const values = [];
    const schema = { '~standard': { version: 1, vendor: 'coordinated-updates-test', validate(value) {
      values.push(value.value); return { value };
    } } };
    const f = await fixture(t, { [`${target}Schema`]: schema });
    await Promise.all([f.provider.update({ value: 2 }), f.consumer.update({ value: 2 })]);
    assert.deepEqual(f.observations, sequential);
    assert.deepEqual(values, [1, 2]);
  });

  test(`cordis: a user ${target} internal/update hook preserves ordinary update ordering`, async t => {
    const updates = [];
    const f = await fixture(t, { [`${target}Setup`]: child => child.on('internal/update', (config, noSave, next) => {
      updates.push([config.value, noSave]); return next();
    }) });
    await Promise.all([f.provider.update({ value: 2 }), f.consumer.update({ value: 2 })]);
    assert.deepEqual(f.observations, sequential);
    assert(updates.length > 0, 'the user update hook must still run');
    for (const update of updates) assert.deepEqual(update, [2, false]);
  });
}

test('cordis: a global user internal/update hook preserves ordinary update ordering', async t => {
  const f = await fixture(t), updates = [];
  f.ctx.on('internal/update', (config, noSave, next) => {
    updates.push([config.value, noSave]); return next();
  }, { global: true });
  await Promise.all([f.provider.update({ value: 2 }), f.consumer.update({ value: 2 })]);
  assert.deepEqual(f.observations, sequential);
  assert.deepEqual(updates, [[2, false], [2, false]]);
});

test('cordis: a consumer setup failure does not reject a successful coordinated provider update', async t => {
  const failure = new Error('consumer setup rejected its new config');
  const f = await fixture(t, { consumerSetup: (_child, config) => { if (config.value === 2) throw failure; } });
  const first = f.provider.update({ value: 2 });
  const second = f.consumer.update({ value: 2 });
  const [provider, consumer] = await Promise.allSettled([first, second]);
  assert.equal(provider.status, 'fulfilled');
  assert.equal(consumer.status, 'rejected');
  assert.equal(consumer.reason, failure);
  assert.deepEqual(f.observations, [[1, 1], [2, 2]]);
  assert.equal(f.ctx.get('coordinatedValue'), 2);
});

test('cordis: failed coordinated cleanup releases update results for an explicit retry', { timeout: 5000 }, async t => {
  let fail = true;
  const f = await fixture(t, { consumerCleanup: () => { if (fail) throw new Error('coordinated inverse requires retry'); } });
  try {
    const results = await Promise.allSettled([f.provider.update({ value: 2 }), f.consumer.update({ value: 2 })]);
    assert.deepEqual(results.map(result => result.status), ['rejected', 'rejected']);
    for (const result of results) assert.match(messageTree(result.reason), /cleanup|inverse/i);
    assert(f.ctx.snapshot().plugins.some(plugin => plugin.cleanupFailed));
    await f.ctx.settle().catch(error => assert.match(messageTree(error), /cleanup|inverse/i));
    fail = false;
    await f.consumer.retryCleanup();
    await f.provider.await();
    await f.consumer.update({ value: 2 });
    assert.deepEqual(f.observations.at(-1), [2, 2]);
    assert(!f.ctx.snapshot().plugins.some(plugin => plugin.cleanupFailed));
  } finally {
    fail = false;
    if (f.ctx.snapshot().plugins.some(plugin => plugin.id === f.consumer.id && plugin.cleanupFailed)) await f.consumer.retryCleanup();
  }
});

test('harness: same-stack updates retain void results and independent FIFO revisions', async t => {
  const f = await fixture(t, { Context: HarnessContext });
  assert.equal(f.provider.update({ value: 2 }), undefined);
  assert.equal(f.consumer.update({ value: 2 }), undefined);
  await f.consumer.await();
  assert.deepEqual(f.observations, sequential);
  assert.equal(f.cleanups.length, 2);
});

async function completesWithoutReleasing(promise) {
  let timer;
  try {
    return await Promise.race([promise, new Promise((_resolve, reject) => {
      timer = setTimeout(() => reject(new Error('update waited for an unrelated or permanently unavailable setup')), 2000);
    })]);
  } finally { clearTimeout(timer); }
}

test('cordis: joined consumer readiness waits for delayed provider publication', { timeout: 5000 }, async t => {
  const ctx = new CordisContext(), entered = Promise.withResolvers(), release = Promise.withResolvers();
  t.after(() => ctx.dispose());
  const observations = [];
  const provider = await ctx.plugin(async (child, config) => {
    if (config.value === 2) { entered.resolve(); await release.promise; }
    child.provide('delayedValue', config.value);
  }, { value: 1 });
  const consumer = await ctx.plugin({ inject: ['delayedValue'], apply(child, config) {
    observations.push([child.delayedValue, config.value]);
  } }, { value: 1 });
  let providerLanded = false, consumerLanded = false;
  const first = provider.update({ value: 2 }).finally(() => { providerLanded = true; });
  const second = consumer.update({ value: 2 }).finally(() => { consumerLanded = true; });
  try {
    await entered.promise;
    await nextTurn();
    assert.equal(providerLanded, false);
    assert.equal(consumerLanded, false, 'the temporary absence of the new publication is not readiness');
    assert.deepEqual(observations, [[1, 1]]);
    release.resolve();
    await Promise.all([first, second]);
    assert.deepEqual(observations, [[1, 1], [2, 2]]);
  } finally { release.resolve(); await Promise.allSettled([first, second]); }
});

test('cordis: a provider which stops publishing leaves its updated consumer legally pending', { timeout: 5000 }, async t => {
  const ctx = new CordisContext(), observations = [];
  t.after(() => ctx.dispose());
  const provider = await ctx.plugin((child, config) => {
    if (config.enabled) child.provide('optionalPublication', config.value);
  }, { enabled: true, value: 1 });
  const consumer = await ctx.plugin({ inject: ['optionalPublication'], apply(child, config) {
    observations.push([child.optionalPublication, config.value]);
  } }, { value: 1 });
  const updates = [provider.update({ enabled: false, value: 2 }), consumer.update({ value: 2 })];
  assert.deepEqual(await completesWithoutReleasing(Promise.all(updates)), [undefined, undefined]);
  assert.deepEqual(observations, [[1, 1]]);
  assert.equal(ctx.snapshot().plugins.find(plugin => plugin.id === consumer.id).state, 'Pending');
  assert.equal(consumer.config.value, 2);
  await provider.update({ enabled: true, value: 3 });
  await consumer.await();
  assert.deepEqual(observations, [[1, 1], [3, 2]]);
});

for (const topology of ['chain', 'diamond']) {
  test(`cordis: a ${topology} dependency path preserves ordinary FIFO update ordering`, async t => {
    const ctx = new CordisContext(), observations = [];
    t.after(() => ctx.dispose());
    const provider = await ctx.plugin((child, config) => { child.provide('sourceValue', config.value); }, { value: 1 });
    await ctx.plugin({ inject: ['sourceValue'], apply(child) { child.provide('derivedValue', child.sourceValue); } });
    const consumer = await ctx.plugin({
      inject: topology === 'chain' ? ['derivedValue'] : ['sourceValue', 'derivedValue'],
      apply(child, config) {
        if (topology === 'diamond') assert.equal(child.sourceValue, child.derivedValue);
        observations.push([child.derivedValue, config.value]);
      },
    }, { value: 1 });
    await Promise.all([provider.update({ value: 2 }), consumer.update({ value: 2 })]);
    assert.deepEqual(observations, sequential);
  });
}

for (const failureOrder of ['first', 'last']) {
  test(`cordis: an independent consumer failing ${failureOrder} does not reject successful update siblings`, async t => {
    const f = await fixture(t), failedObservations = [];
    const failure = new Error('only the failing consumer rejects its config');
    const failing = await f.ctx.plugin({ inject: ['coordinatedValue'], apply(child, config) {
      failedObservations.push([child.coordinatedValue, config.value]);
      if (config.value === 2) throw failure;
    } }, { value: 1 });
    const first = f.provider.update({ value: 2 });
    const consumers = failureOrder === 'first' ? [failing, f.consumer] : [f.consumer, failing];
    const requested = consumers.map(consumer => consumer.update({ value: 2 }));
    const [provider, ...outcomes] = await Promise.allSettled([first, ...requested]);
    assert.equal(provider.status, 'fulfilled');
    for (let index = 0; index < consumers.length; index++) {
      const outcome = outcomes[index];
      assert.equal(outcome.status, consumers[index] === failing ? 'rejected' : 'fulfilled');
      if (consumers[index] === failing) assert.equal(outcome.reason, failure);
    }
    assert.deepEqual(f.observations, [[1, 1], [2, 2]]);
    assert.deepEqual(failedObservations, [[1, 1], [2, 2]]);
    assert.equal(f.ctx.get('coordinatedValue'), 2);
  });
}

test('cordis: an unrelated suspended setup does not become part of the update barrier', { timeout: 5000 }, async t => {
  const f = await fixture(t), entered = Promise.withResolvers(), release = Promise.withResolvers();
  let unrelatedReady = false;
  const unrelated = Promise.resolve(f.ctx.plugin(async () => {
    entered.resolve(); await release.promise;
    unrelatedReady = true;
  }));
  try {
    await entered.promise;
    const first = f.provider.update({ value: 2 });
    const second = f.consumer.update({ value: 2 });
    await completesWithoutReleasing(Promise.all([first, second]));
    assert.equal(unrelatedReady, false);
    assert.deepEqual(f.observations, [[1, 1], [2, 2]]);
  } finally { release.resolve(); await unrelated; }
});

test('cordis: completed plugin continuations preserve ordinary FIFO update ordering', async t => {
  const f = await fixture(t), release = Promise.withResolvers();
  let continuation;
  await f.ctx.plugin(() => {
    continuation = release.promise.then(() => Promise.all([
      f.provider.update({ value: 2 }), f.consumer.update({ value: 2 }),
    ]));
  });
  release.resolve();
  await continuation;
  assert.deepEqual(f.observations, sequential);
});

test('cordis: a provider setup failure leaves its updated consumer pending without sharing the error', async t => {
  const ctx = new CordisContext(), observations = [];
  const failure = new Error('provider setup failed before publication');
  t.after(() => ctx.dispose());
  const provider = await ctx.plugin((child, config) => {
    if (config.value === 2) throw failure;
    child.provide('recoverablePublication', config.value);
  }, { value: 1 });
  const consumer = await ctx.plugin({ inject: ['recoverablePublication'], apply(child, config) {
    observations.push([child.recoverablePublication, config.value]);
  } }, { value: 1 });
  const results = await Promise.allSettled([provider.update({ value: 2 }), consumer.update({ value: 2 })]);
  assert.equal(results[0].status, 'rejected');
  assert.equal(results[0].reason, failure);
  assert.deepEqual(results[1], { status: 'fulfilled', value: undefined });
  assert.equal(ctx.snapshot().plugins.find(plugin => plugin.id === consumer.id).state, 'Pending');
  assert.equal(consumer.config.value, 2);
  assert.deepEqual(observations, [[1, 1]]);
  await provider.update({ value: 3 });
  await consumer.await();
  assert.deepEqual(observations, [[1, 1], [3, 2]]);
});
