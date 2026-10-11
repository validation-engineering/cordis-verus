import test from 'node:test';
import assert from 'node:assert/strict';
import { Context as CordisContext } from '../../packages/compat-cordis/index.js';
import { Context as HarnessContext } from '../../packages/compat-harness/index.js';

for (const [profile, Context] of [['cordis', CordisContext], ['harness', HarnessContext]]) {
  test(`${profile}: verified wait admission names the retained provider during setup and failed cleanup`, async () => {
    const ctx = new Context();
    let provider, fail = true, checks = 0;
    try {
      const branch = await ctx.plugin(async child => {
        provider = await child.plugin(p => { p.provide('source', { value: 42 }); });
      });
      const middle = await ctx.plugin({ inject: ['source'], apply(child) {
        child.provide('relay', { read: () => child.source.value });
      } });
      const consumer = await ctx.plugin({ inject: ['relay'], async apply(child) {
        const check = async () => {
          assert.equal(child.relay.read(), 42);
          for (const target of [provider, branch]) {
            await assert.rejects(async () => await target.dispose(), error => {
              assert.equal(error.code, 'REENTRANT_MUTATION');
              assert.deepEqual(error.details, { operation: 'disposal', owner: child.fiber.id,
                generation: child.fiber._generation, target: target.id, retained: provider.id });
              return true;
            });
            checks++;
          }
        };
        await check();
        child.effect(() => async () => {
          await check();
          if (fail) throw new Error('intentional cleanup failure');
        });
      } });
      await assert.rejects(consumer.dispose());
      assert.equal(ctx.source.value, 42);
      assert.equal(ctx.relay.read(), 42);
      fail = false;
      await consumer.retryCleanup();
      assert.equal(checks, 6);
      await middle.dispose();
      await branch.dispose();
      assert.equal(ctx.source, undefined);
    } finally { fail = false; await ctx.dispose(); }
  });

  test(`${profile}: unrelated and foreign-domain waits remain admitted`, async () => {
    const left = new Context(), right = new Context();
    try {
      const local = await left.plugin(() => {});
      await right.plugin(() => {});
      const foreign = await right.plugin(() => {});
      const caller = await left.plugin(async child => {
        // The same numeric ID is the caller here and an unrelated target there.
        assert.equal(child.fiber.id, foreign.id);
        await local.dispose();
        await foreign.dispose();
      });
      assert.equal(local.uid, null);
      assert.equal(foreign.uid, null);
      await caller.dispose();
    } finally { await left.dispose(); await right.dispose(); }
  });
}
