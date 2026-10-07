import test from 'node:test';
import assert from 'node:assert/strict';
import { Context as CordisContext, domainMutation } from '../../packages/compat-cordis/index.js';
import { Context as HarnessContext } from '../../packages/compat-harness/index.js';

const event = 'cleanup-admission-probe';
const registrations = {
  plugin: (ctx, callback) => ctx.plugin(callback),
  effect: (ctx, callback) => ctx.effect(callback),
  on: (ctx, callback) => ctx.on(event, callback),
};

for (const [profile, Context] of [['cordis', CordisContext], ['harness', HarnessContext]]) {
  for (const [operation, register] of Object.entries(registrations)) {
    test(`${profile}: direct disposal rejects ${operation} registration with an inactive context diagnostic`, async t => {
      const ctx = new Context();
      t.after(() => ctx.dispose());
      let error, entered = 0, cleanupRuns = 0;
      const owner = await ctx.plugin(child => child.effect(() => () => {
        cleanupRuns++;
        const before = ctx.snapshot();
        const disposables = [...child.fiber._disposables];
        try { register(child, () => { entered++; }); } catch (caught) { error = caught; }
        assert.deepEqual(ctx.snapshot(), before, 'rejected registration must not allocate a native resource');
        assert.deepEqual([...child.fiber._disposables], disposables, 'rejected registration must not add a cleanup obligation');
        ctx.emit(event);
        assert.equal(entered, 0, 'rejected registration must not invoke or install the callback');
      }));

      await owner.dispose();
      assert.equal(cleanupRuns, 1);
      assert.equal(entered, 0);
      assert.equal(ctx.snapshot().plugins.length, 1, 'only the root remains after disposal');
      assert.deepEqual(ctx.events._hooks[event] ?? [], [], 'no listener survives the rejected registration');
      assert.equal(error?.code, 'CLEANUP_BLOCKED');
      // Upstream Cordis checks this wording. Keep our structured recovery code
      // while preserving the diagnostic fragment expected by existing plugins.
      assert.match(error.message, /inactive context/);
    });
  }

  test(`${profile}: retired setup continuations retain STALE_EPISODE resource errors during recovery`, async t => {
    const ctx = new Context(), release = Promise.withResolvers();
    t.after(() => ctx.dispose());
    let continuation, entered = 0;
    const owner = await ctx.plugin(child => {
      if (continuation) return;
      const captured = Object.values(registrations).map(register => () => register(child, () => { entered++; }));
      continuation = release.promise.then(() => {
        for (const register of captured) assert.throws(register, { code: 'STALE_EPISODE' });
      });
    });
    await owner.restart();
    const before = ctx.snapshot();
    await domainMutation(ctx, async () => {
      release.resolve();
      await continuation;
    }, { recovery: true });
    assert.deepEqual(ctx.snapshot(), before);
    ctx.emit(event);
    assert.equal(entered, 0);
    assert.deepEqual(ctx.events._hooks[event] ?? [], []);
  });
}
