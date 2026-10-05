import test from 'node:test';
import assert from 'node:assert/strict';
import {setImmediate as nextTurn} from 'node:timers/promises';
import {Context as CordisContext, FiberState} from '../../packages/compat-cordis/index.js';
import {Context as HarnessContext} from '../../packages/compat-harness/index.js';

async function until(predicate) {
  const deadline = Date.now() + 2000;
  while (!predicate()) {
    assert(Date.now() < deadline, 'lifecycle observation did not arrive');
    await nextTurn();
  }
}

// The official Loader joins each entry's current transition and repeats until
// none remain. It does not call whole-domain settlement from an Include setup.
async function loaderJoin(...fibers) {
  while (true) {
    const tasks = fibers.map(fiber => fiber.inertia).filter(Boolean);
    if (!tasks.length) return;
    await Promise.allSettled(tasks);
  }
}

for (const [profile, Context] of [['cordis', CordisContext], ['harness', HarnessContext]]) {
  test(`${profile} exposes actual async startup before loading observers run`, async () => {
    const ctx = new Context(), gate = Promise.withResolvers();
    let started = false, settled = false;
    const observed = [];
    ctx.on('internal/status', fiber => {
      if (fiber.state === FiberState.LOADING) observed.push(fiber.inertia instanceof Promise);
    });
    const fiber = ctx.plugin(async () => { started = true; await gate.promise; });
    try {
      assert(fiber.inertia instanceof Promise);
      const join = loaderJoin(fiber).then(() => { settled = true; });
      await until(() => started);
      assert.equal(settled, false);
      assert.deepEqual(observed, [true]);
      gate.resolve();
      await join;
      assert.equal(fiber.inertia, undefined);
      assert.equal(fiber.state, FiberState.ACTIVE);
    } finally { gate.resolve(); await ctx.dispose(); }
  });

  test(`${profile} loader join follows cleanup and replacement startup during restart`, async () => {
    const ctx = new Context(), cleanup = Promise.withResolvers(), startup = Promise.withResolvers();
    let setups = 0, cleaning = false, settled = false;
    const fiber = ctx.plugin(async () => {
      if (++setups === 2) await startup.promise;
      return async () => { cleaning = true; await cleanup.promise; };
    });
    try {
      await fiber;
      const restart = fiber.restart();
      await until(() => cleaning);
      const previous = fiber.inertia;
      const join = loaderJoin(fiber).then(() => { settled = true; });
      assert(previous instanceof Promise);
      assert.equal(settled, false);
      cleanup.resolve();
      await until(() => setups === 2);
      assert.equal(settled, false);
      assert(fiber.inertia instanceof Promise);
      assert.notEqual(fiber.inertia, previous);
      startup.resolve();
      await Promise.all([restart, join]);
      assert.equal(fiber.inertia, undefined);
      assert.equal(fiber.state, FiberState.ACTIVE);
    } finally { cleanup.resolve(); startup.resolve(); await ctx.dispose(); }
  });

  test(`${profile} startup failure inertia drains cleanup without rejecting its observer`, async () => {
    const ctx = new Context(), cleanup = Promise.withResolvers();
    let cleaning = false, settled = false;
    const fiber = ctx.plugin(child => {
      child.effect(() => async () => { cleaning = true; await cleanup.promise; });
      throw new Error('startup fixture failed');
    });
    try {
      const first = fiber.inertia;
      assert(first instanceof Promise);
      const join = loaderJoin(fiber).then(() => { settled = true; });
      await until(() => cleaning);
      assert.equal(settled, false);
      cleanup.resolve();
      await first;
      await join;
      assert.equal(fiber.inertia, undefined);
      await assert.rejects(fiber.await(), /startup fixture failed/);
    } finally { cleanup.resolve(); await ctx.dispose(); }
  });

  test(`${profile} cleanup failure finishes inertia while explicit disposal retains failure`, async () => {
    const ctx = new Context();
    let allow = false, cleaning = false;
    const fiber = ctx.plugin(child => {
      child.effect(() => () => { cleaning = true; if (!allow) throw new Error('cleanup fixture failed'); });
    });
    try {
      await fiber;
      const disposing = fiber.dispose();
      disposing.catch(() => {});
      await until(() => cleaning);
      await loaderJoin(fiber);
      assert.equal(fiber.inertia, undefined);
      await assert.rejects(disposing, /cleanup/i);
      assert(ctx.snapshot().plugins.some(node => node.id === fiber.id && node.cleanupFailed));
      allow = true;
      await fiber.retryCleanup();
      await fiber.dispose();
      assert.equal(fiber.inertia, undefined);
    } finally { allow = true; await ctx.dispose(); }
  });

  test(`${profile} an initializing parent joins children without waiting for its own or unrelated work`, async () => {
    const ctx = new Context(), unrelated = Promise.withResolvers();
    const blocker = ctx.plugin(async () => { await unrelated.promise; });
    let childReady = false, parentReady = false;
    const parent = ctx.plugin(async child => {
      const nested = child.plugin(async () => { await nextTurn(); childReady = true; });
      await loaderJoin(nested);
      assert(childReady);
      parentReady = true;
    });
    try {
      await until(() => parentReady);
      await parent;
      assert.equal(parent.inertia, undefined);
      assert(blocker.inertia instanceof Promise);
    } finally { unrelated.resolve(); await ctx.dispose(); }
  });
}
