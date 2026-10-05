import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { setImmediate as nextTurn } from 'node:timers/promises';
import { Context as CordisContext, domainMutation, FiberState } from '../../packages/compat-cordis/index.js';
import { Context as HarnessContext } from '../../packages/compat-harness/index.js';

const reentrant = error => error.code === 'REENTRANT_MUTATION';

for (const [profile, Context] of [['cordis', CordisContext], ['harness', HarnessContext]]) {
  for (const completion of ['return', 'throw']) {
    test(`${profile} internal/update ${completion} joins an unreturned child disposal before the next revision`, { timeout: 5000 }, async () => {
      const ctx = new Context(), events = [], swallowed = [];
      const release = Promise.withResolvers();
      const failure = new Error('update callback failed after issuing child disposal');
      let target;
      const owner = await ctx.plugin(async child => {
        target = await child.plugin(inner => {
          inner.effect(() => async () => {
            events.push('cleanup started');
            await release.promise;
            events.push('cleanup landed');
          });
        });
        child.on('internal/update', () => {
          // Official Include/Group do not return their asynchronous tree update;
          // Entry.update also does not await the disabled entry's disposal.
          (async () => { target.dispose(); })().catch(error => swallowed.push(error));
          if (completion === 'throw') throw failure;
        });
      });
      let update, ready, after;
      try {
        update = owner.update({ disabled: true });
        update?.catch(() => {});
        if (profile === 'harness') assert.equal(update, undefined);
        else assert.equal(typeof update.then, 'function');
        let landed = false;
        ready = completion === 'throw'
          ? assert.rejects(owner.await(), error => error === failure)
          : owner.await();
        ready.then(() => { landed = true; }, () => { landed = true; });
        after = domainMutation(ctx, () => events.push('next revision'));
        await nextTurn();
        assert.deepEqual(swallowed, [], 'the Loader-style catch must not hide a rejected child disposal');
        assert.deepEqual(events, ['cleanup started']);
        assert.equal(landed, false, 'public readiness must include the unreturned child step');
        release.resolve();
        await Promise.all([ready, after]);
        assert.deepEqual(events, ['cleanup started', 'cleanup landed', 'next revision']);
        assert.equal(target.uid, null);
        assert.equal(target.state, FiberState.DISPOSED);
      } finally {
        release.resolve();
        await Promise.allSettled([update, ready, after]);
        await ctx.dispose();
      }
    });
  }

  test(`${profile} nested group updates and sibling restarts share the current revision`, { timeout: 5000 }, async () => {
    const ctx = new Context(), events = [], release = Promise.withResolvers();
    let middle, leaf, sibling, restarted;
    const owner = await ctx.plugin(async child => {
      middle = await child.plugin(async group => {
        leaf = await group.plugin(async (inner, config) => {
          events.push(`leaf setup:${config.value}`);
          if (config.value === 1) await release.promise;
          inner.effect(() => () => events.push(`leaf cleanup:${config.value}`));
        }, { value: 0 });
        group.on('internal/update', config => { leaf.update(config); });
      });
      sibling = await child.plugin(inner => {
        events.push('sibling setup');
        inner.effect(() => () => events.push('sibling cleanup'));
      });
      child.on('internal/update', config => {
        middle.update(config);
        restarted = sibling.restart();
      });
    });
    events.length = 0;
    let update, ready, after;
    try {
      update = owner.update({ value: 1 });
      update?.catch(() => {});
      let landed = false;
      ready = owner.await().then(() => { landed = true; });
      after = domainMutation(ctx, () => events.push('next revision'));
      await nextTurn();
      assert.equal(landed, false);
      assert(events.includes('leaf setup:1'));
      assert(!events.includes('next revision'));
      release.resolve();
      await Promise.all([update, ready, restarted, after]);
      assert.equal(leaf.config.value, 1);
      assert.equal(leaf.state, FiberState.ACTIVE);
      assert.equal(sibling.state, FiberState.ACTIVE);
      assert.equal(events.filter(event => event === 'sibling setup').length, 1);
      assert.equal(events.filter(event => event === 'sibling cleanup').length, 1);
      assert.equal(events.at(-1), 'next revision');
    } finally {
      release.resolve();
      await Promise.allSettled([update, ready, restarted, after]);
      await ctx.dispose();
    }
  });

  test(`${profile} explicit steps and async update continuations cannot inherit coordinator authority`, { timeout: 5000 }, async () => {
    const ctx = new Context(), release = Promise.withResolvers(), trigger = Promise.withResolvers();
    let nested, escaped, capturedSteps, scopedChecked = false, activations = 0;
    const target = await ctx.plugin(() => { activations += 1; });
    const owner = await ctx.plugin(child => {
      child.on('internal/update', () => {
        if (capturedSteps) {
          // A hook runs with the coordinator's synchronous invocation origin,
          // but may not borrow its explicit capability to bypass frame guards.
          for (const operation of ['dispose', 'restart', 'update', 'retryCleanup']) {
            assert.throws(() => capturedSteps[operation](owner, {}), reentrant);
          }
          target.restart(); // Ordinary child/sibling API delegation still works.
          scopedChecked = true;
          return;
        }
        nested = domainMutation(ctx, () => target.restart());
        nested.catch(() => {});
        escaped = trigger.promise.then(() => target.restart());
        escaped.catch(() => {});
        return release.promise;
      });
    });
    let update;
    try {
      update = owner.update({});
      update?.catch(() => {});
      await assert.rejects(nested, reentrant);
      trigger.resolve();
      await assert.rejects(escaped, reentrant);
      assert.equal(activations, 1);
      release.resolve();
      await Promise.all([update, owner.await()]);
      // The synchronous compatibility capability must not become a permanent
      // restriction on a fresh external mutation after the revision lands.
      await target.restart();
      assert.equal(activations, 2);
      await domainMutation(ctx, steps => {
        capturedSteps = steps;
        return steps.update(owner, {});
      });
      assert(scopedChecked);
      assert.equal(owner.state, FiberState.ACTIVE);
      assert.equal(activations, 3);
    } finally {
      trigger.resolve(); release.resolve();
      await Promise.allSettled([update, nested, escaped]);
      await ctx.dispose();
    }
  });

  test(`${profile} synchronous effect callbacks cannot borrow the surrounding update frame`, { timeout: 5000 }, async () => {
    const ctx = new Context(), checks = [];
    const target = await ctx.plugin(() => {});
    const owner = await ctx.plugin(child => {
      child.on('internal/update', () => {
        child.effect(() => {
          assert.throws(() => target.dispose(), reentrant);
          assert.throws(() => target.update({}), reentrant);
          checks.push(assert.rejects(target.restart(), reentrant));
        });
        // A root-owned effect is not a descendant of the updater. Its own
        // lifetime token alone cannot detect a wait for the surrounding frame.
        ctx.effect(() => { checks.push(assert.rejects(owner.await(), reentrant)); });
      });
    });
    try {
      await owner.update({});
      await owner.await();
      await Promise.all(checks);
      assert.equal(target.state, FiberState.ACTIVE);
      assert.notEqual(target.uid, null);
    } finally { await ctx.dispose(); }
  });

  test(`${profile} a caught nested cleanup failure still fails the enclosing update`, { timeout: 5000 }, async () => {
    const ctx = new Context(), release = Promise.withResolvers();
    let shouldFail = true, caught;
    const target = await ctx.plugin(child => {
      child.effect(() => async () => {
        await release.promise;
        if (shouldFail) throw new Error('nested cleanup failed');
      });
    });
    const owner = await ctx.plugin(child => {
      child.on('internal/update', () => {
        target.dispose().catch(error => { caught = error; });
      });
    });
    let update, readiness;
    try {
      update = owner.update({});
      update?.catch(() => {});
      readiness = assert.rejects(owner.await(), error => {
        assert.equal(error, caught, 'a Loader catch cannot turn a failed native child step into success');
        return /cleanup failed/i.test(error.message);
      });
      await nextTurn();
      release.resolve();
      await readiness;
      assert(ctx.snapshot().plugins.some(fiber => fiber.cleanupFailed));
      shouldFail = false;
      await target.retryCleanup();
    } finally {
      shouldFail = false;
      release.resolve();
      await Promise.allSettled([update, readiness]);
      if (ctx.snapshot().plugins.some(fiber => fiber.id === target.id && fiber.cleanupFailed)) await target.retryCleanup();
      await ctx.dispose();
    }
  });

  test(`${profile} every update frame rejects self, ancestor, and committed-provider waits`, { timeout: 7000 }, () => {
    const moduleURL = new URL(`../../packages/compat-${profile === 'harness' ? 'harness' : 'cordis'}/index.js`, import.meta.url).href;
    // Missing one of these guards can withdraw a currently executing frame or
    // create a cycle. Bound the process as well as the node:test timeout.
    const source = `
      import assert from 'node:assert/strict';
      import { Context } from ${JSON.stringify(moduleURL)};
      const ctx = new Context(), checks = [];
      const reentrant = error => error.code === 'REENTRANT_MUTATION';
      const provider = await ctx.plugin(child => { child.provide('dependency', 1); });
      let updating;
      const ancestor = await ctx.plugin(async parent => {
        updating = await parent.plugin({
          inject: ['dependency'],
          apply(child) {
            assert.equal(child.dependency, 1);
            child.on('internal/update', () => {
              for (const target of [updating, ancestor, provider]) {
                assert.throws(() => target.update({}), reentrant);
                assert.throws(() => target.dispose(), reentrant);
                checks.push(assert.rejects(target.restart(), reentrant));
                checks.push(assert.rejects(target.await(), reentrant));
              }
            });
          },
        });
      });
      await updating.update({});
      await updating.await();
      await Promise.all(checks);
      assert.notEqual(provider.uid, null);
      // Retain all frames, including an outer updater which is not an owner
      // of the nested updater. Looking only at the top frame is insufficient.
      let outer;
      const nested = await ctx.plugin(child => {
        child.on('internal/update', () => {
          assert.throws(() => outer.dispose(), reentrant);
          assert.throws(() => outer.update({}), reentrant);
          checks.push(assert.rejects(outer.restart(), reentrant));
          checks.push(assert.rejects(outer.await(), reentrant));
        });
      });
      outer = await ctx.plugin(child => {
        child.on('internal/update', config => { nested.update(config); });
      });
      await outer.update({});
      await outer.await();
      await Promise.all(checks);
      assert.notEqual(outer.uid, null);
      await ctx.dispose();
      assert.equal(ctx.snapshot().plugins.length, 0);
      console.log('update frame waits rejected and native graph removed');
    `;
    const env = { ...process.env };
    for (const name of ['NODE_OPTIONS', 'NODE_PATH', 'CORDIS_NATIVE_BINDING']) delete env[name];
    const result = spawnSync(process.execPath, ['--input-type=module', '-e', source], {
      env, encoding: 'utf8', timeout: 3000, killSignal: 'SIGKILL', maxBuffer: 1024 * 1024,
    });
    assert.equal(result.error, undefined, `Update frame wait did not terminate: ${result.error?.message}`);
    assert.equal(result.status, 0, result.stderr);
    assert.match(result.stdout, /update frame waits rejected and native graph removed/);
  });
}
