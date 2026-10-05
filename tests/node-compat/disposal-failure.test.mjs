import test from 'node:test';
import assert from 'node:assert/strict';
import { Context as CordisContext } from '../../packages/compat-cordis/index.js';
import { Context as HarnessContext } from '../../packages/compat-harness/index.js';

const messages = error => [error.message, ...(error instanceof AggregateError ? error.errors.flatMap(messages) : []), ...(error.cause instanceof Error ? [messages(error.cause)] : [])].join(' | ');
const inverseFailure = error => /inverse must retry/.test(messages(error));

for (const [profile, Context] of [['cordis', CordisContext], ['harness', HarnessContext]]) {
  test(`${profile}: observed automatic cleanup failure still rejects disposal and repeated disposal`, async () => {
    const ctx = new Context();
    let fail = true, inverses = 0;
    const fiber = ctx.plugin(c => {
      c.effect(() => () => { inverses++; if (fail) throw new Error('inverse must retry'); });
      throw new Error('setup failed');
    });
    await assert.rejects(fiber.await(), error => /setup failed|inverse must retry/.test(messages(error)));
    await assert.rejects(ctx.settle(), inverseFailure);
    assert.equal(ctx.snapshot().plugins.find(node => node.id === fiber.id).cleanupFailed, true);
    const disposal = fiber.dispose();
    await assert.rejects(disposal, error => inverseFailure(error) && /setup failed/.test(messages(error)));
    assert.equal(fiber.dispose(), disposal);
    await assert.rejects(fiber.dispose(), inverseFailure);
    assert.equal(inverses, 1, 'disposal must not silently retry a failed inverse');
    fail = false;
    await fiber.retryCleanup();
    assert.equal(inverses, 2);
    assert.equal(ctx.snapshot().plugins.some(node => node.id === fiber.id), false);
    await fiber.dispose();
    await ctx.dispose();
  });

  test(`${profile}: a drained setup error is not a cleanup failure`, async () => {
    const ctx = new Context();
    let cleaned = 0;
    const fiber = ctx.plugin(c => {
      c.effect(() => () => { cleaned++; });
      throw new Error('historical setup error');
    });
    await assert.rejects(fiber.await(), /historical setup error/);
    await ctx.settle();
    assert.equal(cleaned, 1);
    await fiber.dispose();
    assert.equal(ctx.snapshot().plugins.some(node => node.id === fiber.id), false);
    await ctx.dispose();
  });

  test(`${profile}: parent and root disposal report an already observed failed descendant`, async () => {
    const ctx = new Context();
    let child, fail = true;
    const parent = ctx.plugin(c => {
      child = c.plugin(inner => {
        inner.effect(() => () => { if (fail) throw new Error('inverse must retry'); });
        throw new Error('descendant setup failed');
      });
    });
    await parent;
    await assert.rejects(ctx.settle(), inverseFailure);
    await assert.rejects(parent.dispose(), inverseFailure);
    await assert.rejects(ctx.dispose(), inverseFailure);
    // Structural parent inverses also observe the failed child; each failed
    // journal needs its own explicit retry rather than an implicit success.
    await assert.rejects(ctx.settle(), inverseFailure);
    fail = false;
    await child.retryCleanup();
    await parent.retryCleanup();
    await ctx.fiber.retryCleanup();
    await parent.dispose();
    await ctx.dispose();
    assert.equal(ctx.snapshot().plugins.length, 0);
  });

  test(`${profile}: failed committed consumer remains visible to provider disposal after settlement`, async () => {
    const ctx = new Context();
    let fail = true, providerCleaned = 0;
    const provider = ctx.plugin(c => {
      c.provide('resource', { answer: 42 });
      return () => { providerCleaned++; };
    });
    await provider;
    const consumer = ctx.inject(['resource'], c => {
      c.effect(() => () => { if (fail) throw new Error('inverse must retry'); });
      throw new Error('consumer setup failed');
    });
    await assert.rejects(ctx.settle(), inverseFailure);
    assert.equal(providerCleaned, 0);
    await assert.rejects(provider.dispose(), inverseFailure);
    assert.equal(providerCleaned, 0, 'failed consumer must keep the committed provider alive');
    fail = false;
    await consumer.retryCleanup();
    await provider.dispose();
    assert.equal(providerCleaned, 1);
    await ctx.dispose();
  });

  test(`${profile}: an unrelated drained error does not prevent independent disposal`, async () => {
    const ctx = new Context();
    let fail = true, cleaned = false;
    const failed = ctx.plugin(c => {
      c.effect(() => () => { if (fail) throw new Error('inverse must retry'); });
      throw new Error('unrelated setup failed');
    });
    await assert.rejects(ctx.settle(), inverseFailure);
    const independent = ctx.plugin(() => () => { cleaned = true; });
    await independent;
    await independent.dispose();
    assert.equal(cleaned, true);
    assert.equal(ctx.snapshot().plugins.find(node => node.id === failed.id).cleanupFailed, true);
    fail = false;
    await failed.retryCleanup();
    await ctx.dispose();
  });
}
