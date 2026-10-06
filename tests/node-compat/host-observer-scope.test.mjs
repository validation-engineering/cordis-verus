import test from 'node:test';
import assert from 'node:assert/strict';
import { Context as CordisContext, domainMutation } from '../../packages/compat-cordis/index.js';
import { Context as HarnessContext } from '../../packages/compat-harness/index.js';

for (const [profile, Context] of [['cordis', CordisContext], ['harness', HarnessContext]]) {
  test(`${profile} host pumping masks a retired observer origin across multiple status listeners`, async () => {
    const ctx = new Context(), release = Promise.withResolvers();
    const domain = ctx.fiber._domain;
    const seen = [];
    let pumping, savedSteps;
    for (const listener of [1, 2]) ctx.on('internal/status', fiber => {
      if (savedSteps) {
        assert.equal(savedSteps.isCurrent(), false);
        assert.throws(() => savedSteps.capture(() => {}), { code: 'REENTRANT_MUTATION' });
      }
      seen.push([listener, fiber.id, fiber.state]);
    }, { global: true });
    const owner = await ctx.plugin(child => child.on('schedule-host-work', () => {
      pumping = release.promise.then(() => {
        // Model a host flush already queued by an observer whose episode is
        // removed before the callback runs. The host boundary clears its scope.
        domain.pump();
        // Clearing it for host work must not revive the original plugin scope.
        assert.throws(() => child.get('anything'), { code: 'STALE_EPISODE' });
      });
    }));
    const target = await ctx.plugin(() => {});
    try {
      await domainMutation(ctx, async steps => {
        savedSteps = steps;
        steps.capture(() => ctx.emit('schedule-host-work'));
        await steps.dispose(owner);
        assert.equal(owner.uid, null);
        // Queue a real native lifecycle transition without letting an earlier
        // host pump consume it; the controlled old callback performs the drive.
        domain.command({ op: 'restart', id: target.id });
        release.resolve();
        await pumping;
        await ctx.settle();
      });
      await ctx.dispose();
      assert.equal(ctx.snapshot().plugins.length, 0);
      const first = seen.filter(([listener]) => listener === 1).map(([, ...state]) => state);
      const second = seen.filter(([listener]) => listener === 2).map(([, ...state]) => state);
      assert.deepEqual(second, first);
      assert.ok(first.some(([id, state]) => id === target.id && state === 5));
    } finally {
      release.resolve();
      await Promise.allSettled([pumping]);
      await ctx.dispose().catch(() => {});
    }
  });
}
