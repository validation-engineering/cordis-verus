import test from 'node:test';
import assert from 'node:assert/strict';
import {createRequire} from 'node:module';
import {fileURLToPath} from 'node:url';
import {Context as CordisContext} from '../../packages/compat-cordis/index.js';
import {Context as HarnessContext} from '../../packages/compat-deepseek/index.js';

const require = createRequire(import.meta.url);
const {NativeDriver} = require('../../packages/compat-cordis/native/cordis.node');
const reentrant = error => error.code === 'REENTRANT_MUTATION';
function observe() {
  const original = NativeDriver.prototype.command, calls = [];
  NativeDriver.prototype.command = function (encoded) {
    const command = JSON.parse(encoded);
    const result = original.call(this, encoded);
    calls.push({command,reply:JSON.parse(result)});
    return result;
  };
  return {calls,restore() { NativeDriver.prototype.command = original; }};
}

for (const [profile, Context] of [['cordis',CordisContext],['harness',HarnessContext]]) {
  test(`${profile} real scope receipts survive cancellation and settle only their own task`, async () => {
    const monitor = observe(), ctx = new Context();
    const a = Promise.withResolvers(), b = Promise.withResolvers();
    let first, second;
    try {
      const baseline = ctx.snapshot().storage.invocationScopes;
      first = ctx.task(async () => { await a.promise; await assert.rejects(ctx.dispose(), reentrant); });
      second = ctx.task(async () => { await b.promise; await assert.rejects(ctx.dispose(), reentrant); throw new Error('expected task failure'); });
      second.promise.catch(() => {});
      assert.equal(ctx.snapshot().storage.invocationScopes, baseline + 2);
      first.cancel(); second.cancel();
      assert.equal(ctx.snapshot().storage.invocationScopes, baseline + 2, 'abort cannot acknowledge callback completion');
      b.resolve();
      await assert.rejects(second.join(), /expected task failure/);
      assert.equal(ctx.snapshot().storage.invocationScopes, baseline + 1);
      a.resolve(); await first.join();
      assert.equal(ctx.snapshot().storage.invocationScopes, baseline);
      const issued = monitor.calls.filter(({command}) => command.op === 'begin_scope').map(({reply}) => reply.scope);
      const finished = monitor.calls.filter(({command}) => command.op === 'finish_scope').map(({command}) => command.scope);
      assert.equal(new Set(issued.map(scope => scope.scope)).size, issued.length);
      assert.deepEqual(new Set(finished.map(scope => JSON.stringify(scope))), new Set(issued.map(scope => JSON.stringify(scope))));
      assert(monitor.calls.some(({command}) => command.op === 'check_scope_wait'));
      assert(!monitor.calls.some(({command}) => command.op === 'check_wait'), 'JS never supplies a holding boolean');
    } finally {
      a.resolve(); b.resolve();
      await Promise.allSettled([first?.promise,second?.promise]);
      await ctx.dispose(); monitor.restore();
    }
  });

  test(`${profile} native ancestry scan sees a live setup beyond completed nested effects`, async () => {
    const monitor = observe(), ctx = new Context(), release = Promise.withResolvers();
    let detached;
    try {
      await ctx.plugin(async child => {
        child.effect(() => {
          child.effect(() => {
            detached = release.promise.then(() => ctx.settle());
          });
        });
        // Both effect initializers have completed. Their ALS tokens still lead
        // to the live setup, and the native scan must not stop at an inactive ID.
        let checked;
        child.effect(() => { checked = Promise.resolve().then(() => assert.rejects(ctx.dispose(), reentrant)); });
        await checked;
      });
      const blocked = monitor.calls.filter(({command,reply}) => command.op === 'check_scope_wait' && reply.blocked);
      assert(blocked.some(({command}) => command.scopes.length >= 2));
      assert.equal(ctx.snapshot().storage.invocationScopes, 0);
      release.resolve(); await detached;
      for (let i = 0; i < 32; i++) await ctx.effect(() => () => {});
      assert.equal(ctx.snapshot().storage.invocationScopes, 0, 'completed callbacks do not accumulate ledger tombstones');
    } finally { release.resolve(); await ctx.dispose(); monitor.restore(); }
  });
}

test('addons must advertise the invocation scope protocol before creating a driver', () => {
  const addon = fileURLToPath(new URL('./fixtures/no-scope-protocol.cjs',import.meta.url));
  assert.throws(() => new CordisContext({addon}), /invocation scope protocol 1/);
});
