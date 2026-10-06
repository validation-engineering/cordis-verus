import test from 'node:test';
import assert from 'node:assert/strict';
import { setImmediate as nextTurn } from 'node:timers/promises';
import { Context as CordisContext, domainMutation } from '../../packages/compat-cordis/index.js';
import { Context as HarnessContext } from '../../packages/compat-harness/index.js';
const reentrant = error => error.code === 'REENTRANT_MUTATION';

for (const [profile, Context] of [['cordis', CordisContext], ['harness', HarnessContext]]) {
  test(`${profile} explicit observers preserve results without borrowing coordinator authority`, async () => {
    const ctx = new Context(), foreign = new Context();
    const target = await ctx.plugin(() => {});
    const object = {};
    let escaped;
    try {
      await domainMutation(ctx, async steps => {
        escaped = steps;
        assert.equal(steps.isCurrent(), true);
        assert.equal(steps.observe(target, function () {
          assert.equal(arguments.length, 0);
          assert.equal(steps.isCurrent(), false);
          assert.throws(() => steps.capture(() => target.dispose()), reentrant);
          return object;
        }), object);
        assert.throws(() => steps.observe(foreign.fiber, () => {}), error => error.code === 'FOREIGN_DOMAIN');
        await steps.observe(target, async () => {
          await nextTurn();
          assert.equal(steps.isCurrent(), false);
          assert.throws(() => steps.dispose(target), reentrant);
          assert.throws(() => target.dispose(), reentrant);
        });
        assert.equal(steps.isCurrent(), true);
      });
      assert.equal(escaped.isCurrent(), false);
      assert.throws(() => escaped.observe(target, () => {}), reentrant);
    } finally { await ctx.dispose(); await foreign.dispose(); }
  });

  test(`${profile} observer thenable getters and assimilation retain observer identity`, async () => {
    const ctx = new Context();
    const target = await ctx.plugin(() => {});
    let getterCalls = 0, thenCalls = 0;
    try {
      await domainMutation(ctx, async steps => {
        const returned = steps.observe(target, () => ({
          get then() {
            getterCalls++;
            assert.equal(steps.isCurrent(), false);
            assert.throws(() => steps.capture(() => target.dispose()), reentrant);
            return resolve => {
              thenCalls++;
              assert.equal(steps.isCurrent(), false);
              assert.throws(() => steps.dispose(target), reentrant);
              resolve(42);
            };
          },
        }));
        assert(returned instanceof Promise);
        assert.equal(await returned, 42);
        assert.equal(steps.isCurrent(), true);
      });
      assert(getterCalls > 0);
      assert.equal(thenCalls, 1);
      assert.notEqual(target.uid, null);
    } finally { await ctx.dispose(); }
  });

  test(`${profile} event dispatch cannot promote listeners into a captured adapter`, async () => {
    const ctx = new Context(), calls = [];
    const target = await ctx.plugin(() => {});
    let saved;
    for (const event of ['sync', 'bail', 'serial', 'parallel']) ctx.on(event, () => {
      assert.equal(saved.isCurrent(), false);
      assert.throws(() => saved.capture(() => {}), reentrant);
      assert.throws(() => target.dispose(), reentrant);
      calls.push(event);
      return event === 'bail' ? 7 : undefined;
    });
    try {
      await domainMutation(ctx, async steps => {
        saved = steps;
        steps.capture(() => ctx.emit('sync'));
        assert.equal(steps.capture(() => ctx.bail('bail')), 7);
        await steps.capture(() => ctx.serial('serial'));
        await steps.capture(() => ctx.parallel('parallel'));
      });
      assert.deepEqual(calls, ['sync', 'bail', 'serial', 'parallel']);
      assert.notEqual(target.uid, null);
    } finally { await ctx.dispose(); }
  });

  test(`${profile} asynchronous waterfall resumes only its trusted continuation and joins cleanup`, async () => {
    const ctx = new Context(), started = Promise.withResolvers(), release = Promise.withResolvers();
    const target = await ctx.plugin(child => child.effect(() => async () => {
      started.resolve(); await release.promise;
    }));
    let saved, task, complete = false;
    ctx.on('pipeline', async next => {
      assert.equal(saved.isCurrent(), false);
      await nextTurn();
      assert.throws(() => saved.capture(() => {}), reentrant);
      return 1 + await next();
    });
    try {
      task = domainMutation(ctx, steps => {
        saved = steps;
        return steps.capture(() => ctx.waterfall('pipeline', () => {
          assert.equal(steps.isCurrent(), true);
          target.dispose();
          return 41;
        }));
      });
      task.then(() => { complete = true; }, () => {});
      await started.promise;
      assert.equal(complete, false);
      release.resolve();
      assert.equal(await task, 42);
      assert.equal(target.uid, null);
    } finally { release.resolve(); await Promise.allSettled([task]); await ctx.dispose(); }
  });

  test(`${profile} saved waterfall continuations reject delayed and nested callback reuse`, async () => {
    const ctx = new Context();
    let savedNext, calls = 0;
    const stop = ctx.on('pipeline', next => {
      savedNext = next;
      ctx.effect(() => { assert.throws(() => next(), reentrant); });
      return 'deferred';
    });
    try {
      assert.equal(await domainMutation(ctx, steps => steps.capture(() => ctx.waterfall('pipeline', () => { calls++; }))), 'deferred');
      assert.throws(() => savedNext(), reentrant);
      assert.equal(calls, 0);
      stop();
      ctx.on('pipeline', next => { const result = next(); assert.throws(() => next(), /multiple times/); return result; });
      assert.equal(await domainMutation(ctx, steps => steps.capture(() => ctx.waterfall('pipeline', () => 3))), 3);
    } finally { await ctx.dispose(); }
  });

  test(`${profile} detached event listeners retain their original owner episode`, async () => {
    const ctx = new Context(), release = Promise.withResolvers();
    let continuation;
    const owner = await ctx.plugin(child => child.on('observe', () => {
      continuation = release.promise.then(() => {
        assert.throws(() => child.get('anything'), error => error.code === 'STALE_EPISODE');
      });
    }));
    try {
      await domainMutation(ctx, async steps => {
        steps.capture(() => ctx.emit('observe'));
        await steps.restart(owner);
        release.resolve();
        await continuation;
      });
    } finally { release.resolve(); await Promise.allSettled([continuation]); await ctx.dispose(); }
  });
}
