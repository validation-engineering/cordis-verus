import test from 'node:test';
import assert from 'node:assert/strict';
import { setImmediate as nextTurn } from 'node:timers/promises';
import { Context as CordisContext, domainMutation } from '../../packages/compat-cordis/index.js';
import { Context as HarnessContext } from '../../packages/compat-harness/index.js';

const reentrant = error => error.code === 'REENTRANT_MUTATION';

for (const [profile, Context] of [['cordis', CordisContext], ['harness', HarnessContext]]) {
  test(`${profile} capture preserves results and releases its frame on return or throw`, async () => {
    const ctx = new Context(), error = new Error('adapter failed');
    const fiber = await ctx.plugin(() => {});
    let escaped;
    try {
      const result = await domainMutation(ctx, steps => {
        escaped = steps;
        assert(Object.isFrozen(steps));
        assert.equal(steps.capture(() => steps.capture(() => 42)), 42);
        const promised = Promise.resolve('adapter result');
        assert.equal(steps.capture(() => promised), promised);
        assert.throws(() => steps.capture(null), TypeError);
        assert.throws(() => steps.capture(() => { throw error; }), caught => caught === error);
        // A completed/throwing capture must not authorize ordinary operations
        // in the remainder of the transaction callback.
        assert.throws(() => fiber.update({}), reentrant);
        assert.throws(() => fiber.dispose(), reentrant);
        return 'committed';
      });
      assert.equal(result, 'committed');
      assert.throws(() => escaped.capture(() => {}), reentrant);
      await assert.rejects(domainMutation(ctx, steps => steps.capture(() => { throw error; })), caught => caught === error);
      await fiber.restart();
    } finally { await ctx.dispose(); }
  });

  test(`${profile} capture joins an unreturned disposal before advancing the domain queue`, { timeout: 5000 }, async () => {
    const ctx = new Context(), events = [], release = Promise.withResolvers();
    const started = Promise.withResolvers();
    const fiber = await ctx.plugin(child => {
      child.effect(() => async () => {
        events.push('cleanup started'); started.resolve();
        await release.promise;
        events.push('cleanup landed');
      });
    });
    let mutation, after;
    try {
      mutation = domainMutation(ctx, steps => steps.capture(() => {
        fiber.dispose();
        return 42;
      }));
      let settled = false;
      mutation.then(() => { settled = true; });
      after = domainMutation(ctx, () => events.push('next revision'));
      await started.promise;
      await nextTurn();
      assert.equal(settled, false);
      assert.deepEqual(events, ['cleanup started']);
      release.resolve();
      assert.equal(await mutation, 42);
      await after;
      assert.deepEqual(events, ['cleanup started', 'cleanup landed', 'next revision']);
      assert.equal(fiber.uid, null);
    } finally {
      release.resolve();
      await Promise.allSettled([mutation, after]);
      await ctx.dispose();
    }
  });

  test(`${profile} capture drains issued lifecycle work before reporting an adapter exception`, { timeout: 5000 }, async () => {
    const ctx = new Context(), release = Promise.withResolvers(), started = Promise.withResolvers();
    const error = new Error('adapter failed after issuing disposal');
    const events = [];
    const fiber = await ctx.plugin(child => child.effect(() => async () => {
      started.resolve();
      await release.promise;
      events.push('cleanup');
    }));
    let failed, after;
    try {
      const mutation = domainMutation(ctx, steps => steps.capture(() => {
        fiber.dispose();
        throw error;
      }));
      let reported = false;
      failed = assert.rejects(mutation, caught => caught === error).then(() => { reported = true; });
      after = domainMutation(ctx, () => events.push('next revision'));
      await started.promise;
      assert.equal(reported, false);
      assert.deepEqual(events, []);
      release.resolve();
      await Promise.all([failed, after]);
      assert.deepEqual(events, ['cleanup', 'next revision']);
      assert.equal(fiber.uid, null);
    } finally {
      release.resolve();
      await Promise.allSettled([failed, after]);
      await ctx.dispose();
    }
  });

  test(`${profile} capture keeps rejected lifecycle steps even when the adapter catches them`, { timeout: 5000 }, async () => {
    const ctx = new Context();
    let fail = true, caught;
    const fiber = await ctx.plugin(child => {
      child.effect(() => () => { if (fail) throw new Error('captured cleanup failed'); });
    });
    try {
      await assert.rejects(domainMutation(ctx, steps => steps.capture(() => {
        fiber.dispose().catch(error => { caught = error; });
        return 'must not commit';
      })), error => error === caught && /cleanup failed/i.test(error.message));
      assert(ctx.snapshot().plugins.some(item => item.cleanupFailed));
      fail = false;
      await domainMutation(ctx, steps => steps.capture(() => {
        fiber.retryCleanup();
      }), { recovery: true });
      assert(!ctx.snapshot().plugins.some(item => item.cleanupFailed));
    } finally {
      fail = false;
      if (ctx.snapshot().plugins.some(item => item.cleanupFailed)) await fiber.retryCleanup();
      await ctx.dispose();
    }
  });

  test(`${profile} capture authority ends before the callback's async continuation`, { timeout: 5000 }, async () => {
    const ctx = new Context(), release = Promise.withResolvers();
    let activations = 0;
    const fiber = await ctx.plugin(() => { activations++; });
    let mutation;
    try {
      mutation = domainMutation(ctx, async steps => {
        const continuation = steps.capture(async () => {
          fiber.restart();
          await release.promise;
          assert.throws(() => fiber.update({}), reentrant);
          assert.throws(() => fiber.dispose(), reentrant);
          await assert.rejects(fiber.restart(), reentrant);
          await assert.rejects(fiber.retryCleanup(), reentrant);
          await assert.rejects(domainMutation(ctx, () => {}), reentrant);
          return 'continued';
        });
        assert.throws(() => fiber.update({}), reentrant);
        return await continuation;
      });
      release.resolve();
      assert.equal(await mutation, 'continued');
      assert.equal(activations, 2);
      await fiber.restart();
      assert.equal(activations, 3);
    } finally {
      release.resolve();
      await Promise.allSettled([mutation]);
      await ctx.dispose();
    }
  });

  test(`${profile} plugin setup and synchronous effect callbacks cannot borrow capture authority`, async () => {
    const ctx = new Context(), checks = [];
    const target = await ctx.plugin(() => {});
    let setupChecked = false;
    try {
      await domainMutation(ctx, async steps => {
        steps.capture(() => ctx.effect(() => {
          assert.throws(() => steps.capture(() => {}), reentrant);
          assert.throws(() => target.dispose(), reentrant);
          assert.throws(() => target.update({}), reentrant);
          checks.push(assert.rejects(target.restart(), reentrant));
          checks.push(assert.rejects(target.retryCleanup(), reentrant));
        }));
        await ctx.plugin(async child => {
          assert.throws(() => steps.capture(() => {}), reentrant);
          await child.plugin(() => {});
          setupChecked = true;
        });
      });
      await Promise.all(checks);
      assert(setupChecked);
      assert.notEqual(target.uid, null);
    } finally { await ctx.dispose(); }
  });

  test(`${profile} captured updates retain self, ancestor and committed-provider wait guards`, { timeout: 5000 }, async () => {
    const ctx = new Context(), checks = [];
    const provider = await ctx.plugin(child => child.provide('dependency', 1));
    let owner, saved, checked = false;
    const ancestor = await ctx.plugin(async parent => {
      owner = await parent.plugin({
        inject: ['dependency'],
        apply(child) {
          assert.equal(child.dependency, 1);
          child.on('internal/update', () => {
            assert.throws(() => saved.capture(() => {}), reentrant);
            for (const target of [owner, ancestor, provider]) {
              assert.throws(() => target.dispose(), reentrant);
              assert.throws(() => target.update({}), reentrant);
              checks.push(assert.rejects(target.restart(), reentrant));
              checks.push(assert.rejects(target.retryCleanup(), reentrant));
              checks.push(assert.rejects(target.await(), reentrant));
            }
            checked = true;
          });
        },
      });
    });
    try {
      await domainMutation(ctx, steps => {
        saved = steps;
        const result = steps.capture(() => owner.update({ enabled: true }));
        if (profile === 'harness') assert.equal(result, undefined);
        return result;
      });
      await Promise.all(checks);
      assert(checked);
      for (const fiber of [owner, ancestor, provider]) assert.notEqual(fiber.uid, null);
    } finally { await ctx.dispose(); }
  });

  test(`${profile} async update observers cannot borrow leaked coordinator steps`, { timeout: 5000 }, async () => {
    const ctx = new Context();
    let saved, checked = false, activations = 0, cleanups = 0;
    const target = await ctx.plugin(child => {
      activations++;
      child.effect(() => () => { cleanups++; });
    });
    const owner = await ctx.plugin(child => {
      child.on('internal/update', async () => {
        // The update frame has exited while the enclosing revision remains
        // active, so a frame-stack-only guard would authorize every call below.
        await nextTurn();
        assert.throws(() => saved.capture(() => target.dispose()), reentrant);
        for (const operation of ['dispose', 'update', 'restart', 'retryCleanup']) {
          assert.throws(() => saved[operation](target, {}), reentrant);
        }
        assert.throws(() => target.dispose(), reentrant);
        assert.throws(() => target.update({}), reentrant);
        await assert.rejects(target.restart(), reentrant);
        await assert.rejects(target.retryCleanup(), reentrant);
        assert.equal(activations, 1);
        assert.equal(cleanups, 0);
        checked = true;
      });
    });
    try {
      await domainMutation(ctx, steps => {
        saved = steps;
        return steps.update(owner, {});
      });
      assert(checked);
      assert.notEqual(target.uid, null);
      assert.equal(activations, 1);
      assert.equal(cleanups, 0);
      await target.restart();
      assert.equal(activations, 2);
      assert.equal(cleanups, 1);
    } finally { await ctx.dispose(); }
  });

  test(`${profile} failed updates recover without attributing host transitions to retired observers`, async () => {
    const ctx = new Context();
    const effects = new Set();
    let target, serial = 0;
    const owner = await ctx.plugin(async (child, config) => {
      if (config.fail) throw new Error('candidate setup failed');
      const id = ++serial;
      child.effect(() => { effects.add(id); return () => { effects.delete(id); }; });
      target = await child.plugin(() => {});
      child.on('internal/update', (config, noSave, next) => {
        // A legitimate synchronous child revision may schedule native work
        // just before the updater itself advances to another generation.
        if (target.uid !== null) target.update(config);
        return next();
      });
    }, { fail: false });
    try {
      await assert.rejects(domainMutation(ctx, steps => steps.update(owner, { fail: true })), /candidate setup failed/);
      assert.equal(effects.size, 0);
      await domainMutation(ctx, steps => steps.update(owner, { fail: false }));
      assert.equal(effects.size, 1);
      await ctx.settle();
    } finally { await ctx.dispose(); }
    assert.equal(effects.size, 0);
    assert.equal(ctx.snapshot().plugins.length, 0);
  });

  test(`${profile} host status callbacks cannot borrow saved coordinator steps`, async () => {
    const ctx = new Context();
    let saved, checked = 0;
    const target = await ctx.plugin(() => {});
    const owner = await ctx.plugin(() => {});
    const unlisten = ctx.on('internal/status', changed => {
      if (!saved || changed !== owner) return;
      assert.throws(() => saved.capture(() => target.dispose()), reentrant);
      for (const operation of ['dispose', 'update', 'restart', 'retryCleanup']) {
        assert.throws(() => saved[operation](target, {}), reentrant);
      }
      checked++;
    }, { global: true });
    try {
      await domainMutation(ctx, steps => {
        saved = steps;
        return steps.update(owner, {});
      });
      assert(checked > 0);
      assert.notEqual(target.uid, null);
    } finally { unlisten(); await ctx.dispose(); }
  });

  test(`${profile} host callbacks retain recovery admission without retaining it forever`, async () => {
    const ctx = new Context(), release = Promise.withResolvers();
    let statuses = 0, cleaned = false, detached;
    const blocked = error => error.code === 'CLEANUP_BLOCKED';
    const owner = await ctx.plugin(child => child.effect(() => () => {
      assert.throws(() => ctx.effect(() => {}), blocked);
      assert.throws(() => ctx.plugin(() => {}), blocked);
      cleaned = true;
    }));
    const unlisten = ctx.on('internal/status', changed => {
      if (changed !== owner) return;
      assert.throws(() => ctx.effect(() => {}), blocked);
      assert.throws(() => ctx.plugin(() => {}), blocked);
      detached ??= release.promise.then(() => {
        const remove = ctx.effect(() => {});
        remove();
      });
      statuses++;
    }, { global: true });
    try {
      await domainMutation(ctx, steps => steps.dispose(owner), { recovery: true });
      assert(statuses > 0);
      assert(cleaned);
      release.resolve();
      await detached;
    } finally {
      release.resolve();
      await Promise.allSettled([detached]);
      unlisten();
      await ctx.dispose();
    }
  });

  test(`${profile} default update continuation remains scoped after asynchronous observers`, async () => {
    const ctx = new Context();
    let savedNext;
    const owner = await ctx.plugin((child, config) => {
      child.on('internal/update', async (config, noSave, next) => {
        if (config.mode === 'save') { savedNext = next; return; }
        if (config.mode === 'effect') {
          child.effect(() => { assert.throws(() => next(), reentrant); });
          return;
        }
        await nextTurn();
        return next();
      });
    }, { mode: 'initial' });
    try {
      await domainMutation(ctx, steps => steps.update(owner, { mode: 'save' }));
      assert.throws(() => savedNext(), reentrant);
      assert.equal(owner.config.mode, 'initial');
      await domainMutation(ctx, steps => steps.update(owner, { mode: 'effect' }));
      assert.equal(owner.config.mode, 'initial');
      await domainMutation(ctx, steps => steps.update(owner, { mode: 'async' }));
      assert.equal(owner.config.mode, 'async');
    } finally { await ctx.dispose(); }
  });

  test(`${profile} recovery capture cannot restart or update a fiber`, async () => {
    const ctx = new Context();
    const fiber = await ctx.plugin(() => {});
    try {
      await domainMutation(ctx, steps => steps.capture(() => {
        assert.throws(() => fiber.update({}), error => error.code === 'CLEANUP_BLOCKED');
      }), { recovery: true });
      await assert.rejects(domainMutation(ctx, steps => steps.capture(() => fiber.restart()), { recovery: true }), error => error.code === 'CLEANUP_BLOCKED');
      assert.notEqual(fiber.uid, null);
    } finally { await ctx.dispose(); }
  });
}
