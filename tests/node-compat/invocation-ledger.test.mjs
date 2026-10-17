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
  const calls = [], originals = new Map();
  for (const method of ['command','beginInvocation','finishInvocation','invocationLive','invocationOwnLive','checkInvocationWait']) {
    const original = NativeDriver.prototype[method];
    originals.set(method,original);
    NativeDriver.prototype[method] = function (...args) {
      const result = original.apply(this,args);
      calls.push(method === 'command'
        ? {method,args,command:JSON.parse(args[0]),reply:JSON.parse(result)}
        : {method,args,reply:method === 'checkInvocationWait' ? JSON.parse(result) : result});
      return result;
    };
  }
  return {calls,restore() {
    for (const [method,original] of originals) NativeDriver.prototype[method] = original;
  }};
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
      const issued = monitor.calls.filter(({method}) => method === 'beginInvocation').map(({reply}) => reply);
      const finished = monitor.calls.filter(({method}) => method === 'finishInvocation').map(({args}) => args[0]);
      assert(issued.length >= 2);
      assert.equal(new Set(issued).size, issued.length);
      assert.deepEqual(new Set(finished), new Set(issued), 'each opaque path completes only its own callback');
      assert(monitor.calls.some(({method}) => method === 'checkInvocationWait'));
      assert(!monitor.calls.some(({command}) => ['begin_scope','finish_scope','scopes_live','check_scope_wait','check_wait'].includes(command?.op)),
        'production JS does not reconstruct handle lists or supply a holding boolean');
    } finally {
      a.resolve(); b.resolve();
      await Promise.allSettled([first?.promise,second?.promise]);
      await ctx.dispose(); monitor.restore();
    }
  });

  test(`${profile} native ancestry scan sees a live setup beyond completed nested effects`, async () => {
    const monitor = observe(), ctx = new Context(), release = Promise.withResolvers();
    let detached, checked;
    try {
      await ctx.plugin(async child => {
        child.effect(() => {
          child.effect(() => {
            detached = release.promise.then(() => ctx.settle());
            checked = Promise.resolve().then(() => assert.rejects(ctx.dispose(), reentrant));
          });
        });
        // Both effect initializers have completed. Their ALS tokens still lead
        // to the live setup, and the native scan must not stop at an inactive ID.
        await checked;
      });
      const blocked = monitor.calls.findIndex(({method,reply}) => method === 'checkInvocationWait' && reply.blocked);
      assert(blocked >= 0);
      const path = monitor.calls[blocked].args[0];
      assert(monitor.calls.slice(0,blocked).some(({method,args}) => method === 'finishInvocation' && args[0] === path),
        'the checked path belongs to an already completed nested callback; only its captured ancestor is live');
      assert.equal(ctx.snapshot().storage.invocationScopes, 0);
      release.resolve(); await detached;
      for (let i = 0; i < 32; i++) await ctx.effect(() => () => {});
      assert.equal(ctx.snapshot().storage.invocationScopes, 0, 'completed callbacks do not accumulate ledger tombstones');
    } finally { release.resolve(); await ctx.dispose(); monitor.restore(); }
  });
}

test('addons must advertise the invocation scope protocol before creating a driver', () => {
  const addon = fileURLToPath(new URL('./fixtures/no-scope-protocol.cjs',import.meta.url));
  assert.throws(() => new CordisContext({addon}), /invocation scope protocol 2/);
});

test('native callback paths reject forged and foreign objects without issuing a receipt', async () => {
  const ctx = new CordisContext(), other = new CordisContext();
  const driver = ctx.fiber._domain.driver, foreignDriver = other.fiber._domain.driver;
  const path = driver.beginInvocation(ctx.fiber.id,ctx.fiber._generation);
  const foreign = foreignDriver.beginInvocation(other.fiber.id,other.fiber._generation);
  try {
    assert.deepEqual(Object.keys(path), [], 'the native path exposes no mutable handle list');
    const before = ctx.snapshot().storage.invocationScopes;
    for (const invalid of [{}, Object.create(Object.getPrototypeOf(path)), driver, foreign]) {
      assert.throws(() => driver.beginInvocation(ctx.fiber.id,ctx.fiber._generation,invalid));
      assert.throws(() => driver.checkInvocationWait(invalid,ctx.fiber.id));
      assert.equal(ctx.snapshot().storage.invocationScopes,before);
    }
    assert.equal(driver.invocationOwnLive(path),true);
    assert.equal(JSON.parse(driver.checkInvocationWait(path,ctx.fiber.id)).blocked,true);
  } finally {
    driver.finishInvocation(path); foreignDriver.finishInvocation(foreign);
    await ctx.dispose(); await other.dispose();
  }
});
