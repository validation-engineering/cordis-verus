import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { setImmediate as nextTurn } from 'node:timers/promises';
import { Context as CordisContext, domainMutation, FiberState } from '../../packages/compat-cordis/index.js';
import { Context as HarnessContext } from '../../packages/compat-harness/index.js';

const reentrant = error => error.code === 'REENTRANT_MUTATION';
const stale = error => error.code === 'STALE_EPISODE';
const blocked = error => error.code === 'CLEANUP_BLOCKED';

for (const [profile, Context] of [['cordis', CordisContext], ['harness', HarnessContext]]) {
  test(`${profile} Fiber.await includes a disposal admitted behind another transaction`, { timeout: 5000 }, async () => {
    const ctx = new Context(), release = Promise.withResolvers();
    const target = await ctx.plugin(() => {});
    const preceding = domainMutation(ctx, () => release.promise);
    const disposal = target.dispose();
    let ready = false;
    const readiness = target.await().then(() => { ready = true; });
    try {
      await nextTurn();
      assert.equal(target.state, FiberState.ACTIVE);
      assert.equal(ready, false, 'queued disposal must participate in the public readiness join');
      release.resolve();
      await Promise.all([preceding, disposal, readiness]);
      assert.equal(target.uid, null);
      assert.equal(target.state, FiberState.DISPOSED);
    } finally {
      release.resolve();
      await Promise.allSettled([preceding, disposal, readiness]);
      await ctx.dispose();
    }
  });

  test(`${profile} a rejected queued disposal does not poison a still active target`, { timeout: 5000 }, async () => {
    const ctx = new Context(), trigger = Promise.withResolvers(), advance = Promise.withResolvers();
    const target = await ctx.plugin(() => {});
    let requested;
    const caller = await ctx.plugin(() => {
      if (requested) return;
      requested = trigger.promise.then(() => target.dispose());
      requested.catch(() => {});
    });
    const preceding = domainMutation(ctx, async steps => {
      await advance.promise;
      await steps.restart(caller);
    });
    try {
      trigger.resolve();
      await nextTurn();
      advance.resolve();
      await preceding;
      await assert.rejects(requested, stale);
      assert.equal(target.state, FiberState.ACTIVE, 'the rejected request never withdrew its target');
      assert.notEqual(target.uid, null);
      await target.dispose();
      assert.equal(target.state, FiberState.DISPOSED, 'a fresh caller can make a new disposal request');
    } finally {
      trigger.resolve(); advance.resolve();
      await Promise.allSettled([preceding, requested]);
      await ctx.dispose();
    }
  });

  test(`${profile} completed plugin continuations cannot inherit transaction step authority`, { timeout: 5000 }, async () => {
    const ctx = new Context(), trigger = Promise.withResolvers();
    let activations = 0, continuation;
    const target = await ctx.plugin(() => { activations += 1; });
    try {
      await domainMutation(ctx, async steps => {
        await ctx.plugin(() => {
          continuation = trigger.promise.then(() => steps.restart(target));
          continuation.catch(() => {});
        });
        trigger.resolve();
        await assert.rejects(continuation, reentrant);
        assert.equal(activations, 1, 'the plugin continuation did not issue a restart');
        // The coordinator itself still owns its capability after awaiting the plugin.
        await steps.restart(target);
        assert.equal(activations, 2);
      });
    } finally { trigger.resolve(); await Promise.allSettled([continuation]); await ctx.dispose(); }
  });

  test(`${profile} recovery transactions cannot acquire resources through ordinary Context APIs`, { timeout: 5000 }, async () => {
    const ctx = new Context();
    let fail = true, entered = false;
    const target = await ctx.plugin(child => {
      child.effect(() => () => { if (fail) throw new Error('retained inverse failure'); });
    });
    try {
      await assert.rejects(target.dispose(), /cleanup failed/i);
      assert(ctx.snapshot().plugins.some(fiber => fiber.cleanupFailed));
      await domainMutation(ctx, () => {
        assert.throws(() => ctx.plugin(() => { entered = true; }), blocked);
        assert.throws(() => ctx.provide('forbiddenRecoveryService', 1), blocked);
        assert.throws(() => ctx.effect(() => { entered = true; }), blocked);
        assert.throws(() => ctx.task(async () => { entered = true; }), blocked);
      }, { recovery: true });
      assert.equal(entered, false);
      assert.equal(ctx.get('forbiddenRecoveryService'), undefined);
      fail = false;
      await domainMutation(ctx, steps => steps.retryCleanup(target), { recovery: true });
      assert(!ctx.snapshot().plugins.some(fiber => fiber.cleanupFailed));
    } finally {
      fail = false;
      if (ctx.snapshot().plugins.some(fiber => fiber.id === target.id && fiber.cleanupFailed)) await target.retryCleanup();
      await ctx.dispose();
    }
  });

  test(`${profile} JS consumers cannot wait for their committed provider from setup or cleanup`, { timeout: 7000 }, () => {
    const moduleURL = new URL(`../../packages/compat-${profile === 'harness' ? 'harness' : 'cordis'}/index.js`, import.meta.url).href;
    // Run the actual waits in a disposable process: a missing guard otherwise
    // makes the native lease and the callback wait for each other indefinitely.
    const source = `
      import assert from 'node:assert/strict';
      import { Context } from ${JSON.stringify(moduleURL)};
      const ctx = new Context();
      const provider = await ctx.plugin(child => { child.provide('dependency', 1); });
      let setupChecked = false, cleanupChecked = false;
      const reentrant = error => error.code === 'REENTRANT_MUTATION';
      const consumer = await ctx.plugin({
        inject: ['dependency'],
        async apply(child) {
          assert.equal(child.dependency, 1);
          await assert.rejects(async () => await provider.dispose(), reentrant);
          setupChecked = true;
          child.effect(() => async () => {
            assert.equal(child.dependency, 1);
            await assert.rejects(async () => await provider.dispose(), reentrant);
            cleanupChecked = true;
          });
        },
      });
      await consumer.dispose();
      assert(setupChecked && cleanupChecked);
      await ctx.dispose();
      assert.equal(ctx.snapshot().plugins.length, 0);
      console.log('committed provider waits rejected and native graph removed');
    `;
    const env = { ...process.env };
    for (const name of ['NODE_OPTIONS', 'NODE_PATH', 'CORDIS_NATIVE_BINDING']) delete env[name];
    const result = spawnSync(process.execPath, ['--input-type=module', '-e', source], {
      env, encoding: 'utf8', timeout: 3000, killSignal: 'SIGKILL', maxBuffer: 1024 * 1024,
    });
    assert.equal(result.error, undefined, `Consumer/provider wait did not terminate: ${result.error?.message}`);
    assert.equal(result.status, 0, result.stderr);
    assert.match(result.stdout, /committed provider waits rejected and native graph removed/);
  });
}
