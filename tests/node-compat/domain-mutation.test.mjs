import test from 'node:test';
import assert from 'node:assert/strict';
import { setImmediate as nextTurn } from 'node:timers/promises';
import { Context as CordisContext, domainMutation } from '../../packages/compat-cordis/index.js';
import { Context as HarnessContext } from '../../packages/compat-harness/index.js';

const reentrant = error => error.code === 'REENTRANT_MUTATION';
const stale = error => error.code === 'STALE_EPISODE';
const foreign = error => error.code === 'FOREIGN_DOMAIN';

for (const [profile, Context] of [['cordis', CordisContext], ['harness', HarnessContext]]) {
  test(`${profile} direct updates and restarts preserve domain FIFO and await observes queued updates`, async () => {
    const ctx = new Context(), events = [];
    const entered = Promise.withResolvers(), release = Promise.withResolvers();
    const fiber = await ctx.plugin((child, config) => {
      events.push(`setup:${config.value}`);
      child.effect(() => () => events.push(`cleanup:${config.value}`));
    }, { value: 0 });
    const blocker = domainMutation(ctx, async () => { entered.resolve(); await release.promise; });
    try {
      await entered.promise;
      const first = fiber.update({ value: 1 });
      const restart = fiber.restart();
      const last = fiber.update({ value: 2 });
      if (profile === 'harness') {
        assert.equal(first, undefined);
        assert.equal(last, undefined);
      } else {
        assert.equal(typeof first.then, 'function');
        assert.equal(typeof last.then, 'function');
      }
      let ready = false;
      const observed = fiber.await().then(() => { ready = true; events.push(`observed:${fiber.config.value}`); });
      await nextTurn();
      assert.equal(ready, false);
      assert.deepEqual(events, ['setup:0']);
      release.resolve();
      await Promise.all([blocker, first, restart, last, observed]);
      assert.deepEqual(events, ['setup:0', 'cleanup:0', 'setup:1', 'cleanup:1', 'setup:1', 'cleanup:1', 'setup:2', 'observed:2']);
    } finally { release.resolve(); await ctx.dispose(); }
  });

  test(`${profile} transaction steps reject foreign domains and escaped continuations`, async () => {
    const ctx = new Context(), other = new Context();
    const local = await ctx.plugin(() => {}), remote = await other.plugin(() => {});
    const release = Promise.withResolvers();
    let saved, detached;
    try {
      await domainMutation(ctx, steps => {
        assert(Object.isFrozen(steps));
        assert.throws(() => steps.dispose(remote), foreign);
        saved = steps;
        detached = release.promise.then(() => {
          assert.throws(() => steps.restart(local), reentrant);
        });
      });
      assert.throws(() => saved.dispose(local), reentrant);
      release.resolve();
      await detached;
      assert.notEqual(local.uid, null);
      assert.notEqual(remote.uid, null);
    } finally { release.resolve(); await ctx.dispose(); await other.dispose(); }
  });

  test(`${profile} active plugins cannot borrow the parent transaction's lifecycle steps`, async () => {
    const ctx = new Context();
    const target = await ctx.plugin(() => {});
    let checked = false;
    try {
      await domainMutation(ctx, async steps => {
        await ctx.plugin(async child => {
          assert.throws(() => steps.dispose(target), reentrant);
          assert.throws(() => steps.restart(target), reentrant);
          assert.throws(() => steps.retryCleanup(target), reentrant);
          assert.throws(() => steps.update(target, {}), reentrant);
          await assert.rejects(domainMutation(ctx, () => {}), reentrant);
          await child.plugin(() => {});
          checked = true;
        });
      });
      assert(checked);
      assert.notEqual(target.uid, null);
    } finally { await ctx.dispose(); }
  });

  test(`${profile} an active transaction cannot join domain shutdown queued behind it`, async () => {
    const ctx = new Context();
    const entered = Promise.withResolvers(), release = Promise.withResolvers();
    let checked = false;
    const transaction = domainMutation(ctx, async () => {
      entered.resolve(); await release.promise;
      await assert.rejects(ctx.dispose(), reentrant);
      checked = true;
    });
    try {
      await entered.promise;
      const closing = ctx.dispose();
      release.resolve();
      await Promise.all([transaction, closing]);
      assert(checked);
      assert.equal(ctx.snapshot().plugins.length, 0);
    } finally { release.resolve(); await ctx.dispose(); }
  });

  test(`${profile} admitted setup may create children during closing while external mounts are rejected`, async () => {
    const ctx = new Context(), events = [];
    const entered = Promise.withResolvers(), release = Promise.withResolvers();
    const transaction = domainMutation(ctx, async () => {
      await ctx.plugin(async owner => {
        entered.resolve(); await release.promise;
        await owner.plugin(child => {
          events.push('child setup');
          child.effect(() => () => events.push('child cleanup'));
        });
        events.push('parent ready');
      });
    });
    try {
      await entered.promise;
      const closing = ctx.dispose();
      assert.throws(() => ctx.plugin(() => events.push('forbidden')), error => error.code === 'DOMAIN_CLOSED');
      release.resolve();
      await Promise.all([transaction, closing]);
      assert.deepEqual(events, ['child setup', 'parent ready', 'child cleanup']);
      assert.equal(ctx.snapshot().plugins.length, 0);
    } finally { release.resolve(); await ctx.dispose(); }
  });

  test(`${profile} a completed continuation cannot execute a queued revision after its episode changes`, async () => {
    const ctx = new Context();
    const trigger = Promise.withResolvers(), admitted = Promise.withResolvers(), release = Promise.withResolvers();
    let continuation, executed = false;
    const owner = await ctx.plugin(() => {
      continuation ??= trigger.promise.then(() => {
        const request = domainMutation(ctx, () => { executed = true; });
        admitted.resolve();
        return request;
      });
    });
    const rejected = assert.rejects(continuation, stale);
    const previous = owner._generation;
    const blocker = domainMutation(ctx, async steps => {
      await release.promise;
      await steps.restart(owner);
    });
    try {
      trigger.resolve();
      await admitted.promise;
      release.resolve();
      await blocker;
      await rejected;
      assert.notEqual(owner._generation, previous);
      assert.equal(executed, false);
    } finally { trigger.resolve(); release.resolve(); await ctx.dispose(); }
  });

  test(`${profile} falsy Promise rejection values remain transaction failures`, async () => {
    const ctx = new Context();
    try {
      for (const reason of [undefined, null, 0, false, '']) {
        const outcome = await domainMutation(ctx, async () => { throw reason; }).then(
          value => ({ resolved: true, value }),
          error => ({ resolved: false, error }),
        );
        assert.equal(outcome.resolved, false);
        assert.equal(outcome.error, reason);
      }
    } finally { await ctx.dispose(); }
  });

  for (const completion of ['return', 'throw', 'throw-zero']) {
    test(`${profile} callback ${completion} waits for already issued lifecycle steps`, async () => {
      const ctx = new Context(), events = [];
      const entered = Promise.withResolvers(), release = Promise.withResolvers();
      const failure = completion === 'throw-zero' ? 0 : new Error('callback failed after disposal began');
      const target = await ctx.plugin(child => {
        child.effect(() => async () => { entered.resolve(); await release.promise; events.push('cleanup landed'); });
      });
      let landed = false;
      const transaction = domainMutation(ctx, steps => {
        steps.dispose(target);
        if (completion !== 'return') throw failure;
        return 42;
      });
      const outcome = completion !== 'return'
        ? assert.rejects(transaction, error => error === failure)
        : transaction.then(value => assert.equal(value, 42));
      const finished = () => { landed = true; };
      outcome.then(finished, finished);
      try {
        await entered.promise;
        const after = domainMutation(ctx, () => events.push('next revision'));
        await nextTurn();
        assert.equal(landed, false);
        assert.deepEqual(events, []);
        release.resolve();
        await Promise.all([outcome, after]);
        assert.deepEqual(events, ['cleanup landed', 'next revision']);
        assert.equal(target.uid, null);
      } finally { release.resolve(); await ctx.dispose(); }
    });
  }

  test(`${profile} a lifecycle step failure remains recorded after it lands before its callback`, async () => {
    const ctx = new Context();
    const failed = Promise.withResolvers(), release = Promise.withResolvers();
    const failure = new Error('cleanup failed before callback returned');
    let shouldFail = true;
    const target = await ctx.plugin(child => {
      child.effect(() => () => { if (shouldFail) throw failure; });
    });
    let stepFailure;
    const transaction = domainMutation(ctx, async steps => {
      steps.dispose(target).catch(error => { stepFailure = error; failed.resolve(); });
      await release.promise;
      return 'must not commit';
    });
    try {
      await failed.promise;
      const outcome = assert.rejects(transaction, error => error === stepFailure);
      release.resolve();
      await outcome;
      shouldFail = false;
      await target.retryCleanup();
    } finally { release.resolve(); shouldFail = false; if (target._error) await target.retryCleanup(); await ctx.dispose(); }
  });
}
