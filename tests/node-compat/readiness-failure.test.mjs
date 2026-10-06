import test from 'node:test';
import assert from 'node:assert/strict';
import { Context as CordisContext, domainMutation } from '../../packages/compat-cordis/index.js';
import { Context as HarnessContext } from '../../packages/compat-harness/index.js';

const messages = error => [error?.message, ...(error instanceof AggregateError ? error.errors.flatMap(messages) : [])].join(' | ');
const cleanupFailure = error => /inverse must retry|Native cleanup failed/.test(messages(error));

for (const [profile, Context] of [['cordis', CordisContext], ['harness', HarnessContext]]) {
  test(`${profile}: rollback restart rejects an unresolved cleanup within the same transaction`, async () => {
    const ctx = new Context();
    let fail = true, inverses = 0, starts = 0;
    const fiber = await ctx.plugin(c => {
      starts++;
      c.effect(() => () => { inverses++; if (fail) throw new Error('inverse must retry'); });
    });
    try {
      await assert.rejects(domainMutation(ctx, async steps => {
        await assert.rejects(steps.restart(fiber), cleanupFailure);
        const first = fiber._error;
        await assert.rejects(steps.restart(fiber), cleanupFailure);
        assert.equal(fiber._error, first, 'rollback must retain the failed cleanup diagnostic');
      }), cleanupFailure);
      assert.equal(inverses, 1, 'a rollback must not implicitly retry an inverse');
      assert.equal(starts, 1);
      await ctx.settle().catch(error => assert.ok(cleanupFailure(error)));
      await assert.rejects(domainMutation(ctx, steps => steps.restart(fiber)), error => error.code === 'CLEANUP_BLOCKED');
      fail = false;
      await fiber.retryCleanup();
      assert.equal(starts, 1, 'failed owner stays Failed after its inverse is recovered');
      await fiber.restart();
      assert.equal(starts, 2, 'an explicit revision can restart the recovered owner');
    } finally { fail = false; if (ctx.snapshot().plugins.some(n => n.cleanupFailed)) await fiber.retryCleanup(); await ctx.dispose(); }
  });

  test(`${profile}: readiness rejects even after the JavaScript cleanup diagnostic was consumed`, async () => {
    const ctx = new Context();
    let fail = true;
    const fiber = await ctx.plugin(c => c.effect(() => () => { if (fail) throw new Error('inverse must retry'); }));
    try {
      await assert.rejects(fiber.restart(), cleanupFailure);
      await ctx.settle().catch(() => {});
      // Model an observer which has already consumed the transient JS diagnostic.
      fiber._error = undefined;
      await assert.rejects(fiber.await(), cleanupFailure);
      assert.equal(ctx.snapshot().plugins.find(n => n.id === fiber.id).cleanupFailed, true);
      fail = false;
      await fiber.retryCleanup();
      await fiber.await();
    } finally { fail = false; if (ctx.snapshot().plugins.some(n => n.cleanupFailed)) await fiber.retryCleanup(); await ctx.dispose(); }
  });

  test(`${profile}: provider readiness reports a failed committed consumer`, async () => {
    const ctx = new Context();
    let fail = true, starts = 0, observerCalls = 0;
    const blocked = error => error.code === 'CLEANUP_BLOCKED';
    ctx.on('recovery-start', () => {
      observerCalls++;
      assert.throws(() => ctx.effect(() => {}), blocked);
      assert.throws(() => ctx.provide('forbidden', 1), blocked);
    });
    const provider = await ctx.plugin(c => {
      starts++;
      if (starts === 2) c.emit('recovery-start');
      c.effect(() => { c.provide('resource', { answer: 42, starts }); });
    });
    const consumer = await ctx.inject(['resource'], c => {
      c.effect(() => () => {
        if (fail) throw new Error('inverse must retry');
        assert.throws(() => ctx.effect(() => {}), blocked);
      });
    });
    try {
      await assert.rejects(provider.restart(), cleanupFailure);
      await ctx.settle().catch(() => {});
      assert.equal(provider._error, undefined);
      await assert.rejects(provider.await(), cleanupFailure);
      fail = false;
      await consumer.retryCleanup();
      await provider.await();
      assert.equal(starts, 2);
      assert.equal(observerCalls, 1);
      assert.equal(ctx.get('resource').starts, 2);
      assert.equal(ctx.get('forbidden'), undefined);
    } finally { fail = false; if (ctx.snapshot().plugins.some(n => n.cleanupFailed)) await consumer.retryCleanup(); await ctx.dispose(); }
  });
}
