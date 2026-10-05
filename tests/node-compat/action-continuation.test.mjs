import test from 'node:test';
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {Context as CordisContext, FiberState} from '../../packages/compat-cordis/index.js';
import {Context as HarnessContext} from '../../packages/compat-harness/index.js';

const reentrant = error => error.code === 'REENTRANT_MUTATION';
const stale = error => error.code === 'STALE_EPISODE';
const addon = fileURLToPath(new URL('../../target/node-compat/interop-fixture.node', import.meta.url));

for (const [profile, Context] of [['cordis', CordisContext], ['harness', HarnessContext]]) {
  test(`${profile} a completed setup continuation can settle and request official root cleanup`, async () => {
    const ctx = new Context(), gate = Promise.withResolvers();
    let shutdown, restored = false;
    const owner = ctx.plugin(child => {
      child.effect(() => () => { restored = true; });
      // Official headless starts void run() in apply(), and calls appExit only
      // after that setup callback and the user turn have completed.
      shutdown = gate.promise.then(async () => {
        await ctx.settle();
        await ctx.fiber.dispose();
      });
    });
    try {
      await owner;
      assert.equal(owner.state, FiberState.ACTIVE);
      gate.resolve();
      await shutdown;
      assert(restored);
      assert.equal(owner.uid, null);
      assert.equal(ctx.snapshot().plugins.length, 1);
    } finally { gate.resolve(); await ctx.dispose(); }
  });

  test(`${profile} a completed setup continuation can close the native domain`, async () => {
    const ctx = new Context(), gate = Promise.withResolvers();
    let shutdown;
    await ctx.plugin(() => { shutdown = gate.promise.then(() => ctx.dispose()); });
    gate.resolve();
    await shutdown;
    assert.equal(ctx.snapshot().plugins.length, 0);
  });

  test(`${profile} live setup and cleanup callbacks still reject ancestor and domain waits`, async () => {
    const ctx = new Context();
    let cleanupChecked = false;
    const owner = ctx.plugin(async child => {
      await assert.rejects(ctx.dispose(), reentrant);
      await assert.rejects(ctx.fiber.dispose(), reentrant);
      await assert.rejects(ctx.settle(), reentrant);
      await assert.rejects(child.fiber.await(), reentrant);
      child.effect(() => async () => {
        await assert.rejects(ctx.dispose(), reentrant);
        await assert.rejects(ctx.fiber.dispose(), reentrant);
        await assert.rejects(ctx.settle(), reentrant);
        await assert.rejects(child.fiber.await(), reentrant);
        cleanupChecked = true;
      });
    });
    try {
      await owner;
      await owner.dispose();
      assert(cleanupChecked);
    } finally { await ctx.dispose(); }
  });

  test(`${profile} live owned tasks still reject waits and their completed continuations may settle`, async () => {
    const ctx = new Context(), gate = Promise.withResolvers();
    let continuation, task;
    task = ctx.task(async () => {
      assert.throws(() => task.join(), reentrant);
      await assert.rejects(ctx.dispose(), reentrant);
      await assert.rejects(ctx.fiber.dispose(), reentrant);
      await assert.rejects(ctx.settle(), reentrant);
      continuation = gate.promise.then(async () => { await ctx.settle(); await ctx.dispose(); });
    });
    await task.join();
    gate.resolve();
    await continuation;
    assert.equal(ctx.snapshot().plugins.length, 0);
  });

  test(`${profile} nested effect scopes cannot conceal an owned task self join`, async () => {
    const ctx = new Context();
    let task;
    task = ctx.task(async () => {
      await ctx.effect(async () => {
        await Promise.resolve();
        assert.throws(() => task.join(), reentrant);
      });
    });
    await task.join();
    await ctx.dispose();
  });

  test(`${profile} unawaited async effects retain their own wait scope after setup lands`, async () => {
    const ctx = new Context(), gate = Promise.withResolvers(), after = Promise.withResolvers();
    let effect, detached, restored = false;
    const owner = await ctx.plugin(child => {
      effect = child.effect(async () => {
        await gate.promise;
        await assert.rejects(ctx.dispose(), reentrant);
        await assert.rejects(ctx.fiber.dispose(), reentrant);
        await assert.rejects(ctx.settle(), reentrant);
        assert.throws(() => child.fiber.dispose(), reentrant);
        detached = after.promise.then(async () => { await ctx.settle(); await ctx.dispose(); });
        return () => { restored = true; };
      });
    });
    assert.equal(owner.state, FiberState.ACTIVE);
    gate.resolve();
    await effect;
    after.resolve();
    await detached;
    assert(restored);
    assert.equal(ctx.snapshot().plugins.length, 0);
  });

  test(`${profile} manual async effect inverses retain an independent wait scope`, async () => {
    const ctx = new Context(), gate = Promise.withResolvers();
    let dispose, checked = false;
    const owner = await ctx.plugin(child => {
      dispose = child.effect(() => async () => {
        await gate.promise;
        await assert.rejects(ctx.dispose(), reentrant);
        await assert.rejects(ctx.fiber.dispose(), reentrant);
        await assert.rejects(ctx.settle(), reentrant);
        assert.throws(() => child.fiber.dispose(), reentrant);
        checked = true;
      });
    });
    const cleanup = dispose();
    gate.resolve();
    await cleanup;
    assert(checked);
    assert.equal(owner.state, FiberState.ACTIVE);
    await ctx.dispose();
  });

  test(`${profile} async effect iterators remain owned through next and return`, async () => {
    const ctx = new Context(), gate = Promise.withResolvers();
    let effect, nextChecked = false, returnChecked = false;
    await ctx.plugin(child => {
      effect = child.effect(async function* () {
        try {
          await gate.promise;
          await assert.rejects(ctx.dispose(), reentrant);
          nextChecked = true;
          yield () => {};
        } finally {
          await assert.rejects(ctx.settle(), reentrant);
          returnChecked = true;
        }
      });
    });
    // Cancellation requests iterator.return only after its in-flight next lands.
    const cleanup = effect();
    gate.resolve();
    await cleanup;
    assert(nextChecked && returnChecked);
    await ctx.dispose();
  });

  test(`${profile} a completed nested effect cannot hide a still live parent setup`, async () => {
    const ctx = new Context();
    await ctx.plugin(async child => {
      let continuation;
      child.effect(() => {
        continuation = Promise.resolve().then(async () => {
          await assert.rejects(ctx.dispose(), reentrant);
          await assert.rejects(ctx.settle(), reentrant);
        });
      });
      await continuation;
    });
    await ctx.dispose();
  });

  test(`${profile} rejected effect initializers release only their live wait scope`, async () => {
    const ctx = new Context(), gate = Promise.withResolvers(), after = Promise.withResolvers();
    let effect, continuation;
    await ctx.plugin(child => {
      effect = child.effect(async () => {
        await gate.promise;
        continuation = after.promise.then(async () => { await ctx.settle(); await ctx.dispose(); });
        throw new Error('effect startup failed');
      });
    });
    gate.resolve();
    await assert.rejects(effect, /effect startup failed/);
    after.resolve();
    await continuation;
    assert.equal(ctx.snapshot().plugins.length, 0);
  });

  test(`${profile} effect and task descendants retain an old caller episode`, async () => {
    const ctx = new Context(), gate = Promise.withResolvers();
    const get = ctx.get.bind(ctx);
    let fromEffect, fromTask;
    ctx.provide('value', 1);
    const owner = await ctx.plugin(child => {
      if (fromEffect) return;
      // Both bodies belong to root, so only the parent invocation identifies
      // the child episode that must not regain authority after its restart.
      ctx.effect(() => { fromEffect = gate.promise.then(() => assert.throws(() => get('value'), stale)); });
      const task = ctx.task(() => { fromTask = gate.promise.then(() => assert.throws(() => get('value'), stale)); });
      return task.join().then(() => undefined);
    });
    await owner.restart();
    gate.resolve();
    await Promise.all([fromEffect, fromTask]);
    await ctx.dispose();
  });

  test(`${profile} completed setup continuations keep their original generation for every wait`, async () => {
    const ctx = new Context(), gate = Promise.withResolvers();
    const settle = ctx.settle.bind(ctx), dispose = ctx.dispose.bind(ctx);
    let continuation;
    const owner = ctx.plugin(child => {
      const awaitFiber = child.fiber.await.bind(child.fiber);
      const restart = child.fiber.restart.bind(child.fiber);
      continuation ??= gate.promise.then(async () => {
        await assert.rejects(settle(), stale);
        await assert.rejects(dispose(), stale);
        await assert.rejects(awaitFiber(), stale);
        await assert.rejects(restart(), stale);
      });
    });
    try {
      await owner;
      await owner.restart();
      gate.resolve();
      await continuation;
      assert.equal(owner.state, FiberState.ACTIVE);
    } finally { gate.resolve(); await ctx.dispose(); }
  });

  for (const retirement of ['restart', 'dispose']) {
    test(`${profile} late ${retirement} diagnostics retain stale service and resource rejection`, async () => {
      const ctx = new Context(), gate = Promise.withResolvers();
      const messages = [];
      ctx.provide('value', 42);
      let continuation, deniedFromExporter = false;
      const owner = ctx.plugin(child => {
        if (continuation) return;
        const get = child.get.bind(child), effect = child.effect.bind(child);
        const task = child.task.bind(child), provide = child.provide.bind(child);
        const rootFiber = ctx.fiber;
        ctx.logger.exporter({export(message) {
          messages.push(message);
          // Logging preserves the caller's token even inside an exporter.
          assert.throws(() => get('value'), stale);
          assert.throws(() => effect(() => () => {}), stale);
          deniedFromExporter = true;
        }});
        continuation = gate.promise.then(() => {
          child.logger.warn('late checkpoint failed');
          assert.throws(() => child.logger.exporter({export() {}}), stale);
          assert.throws(() => child.value, stale);
          assert.throws(() => get('value'), stale);
          assert.throws(() => effect(() => () => {}), stale);
          assert.throws(() => task(async () => {}), stale);
          assert.throws(() => provide('late', 1), stale);
          // extend() only constructs metadata. Even a view borrowing a live
          // root fiber cannot grant this old continuation new authority.
          const derived = child.extend({fiber: rootFiber});
          assert.throws(() => derived.value, stale);
          assert.throws(() => derived.get('value'), stale);
          assert.throws(() => derived.effect(() => () => {}), stale);
          assert.throws(() => derived.task(async () => {}), stale);
          assert.throws(() => derived.provide('late', 1), stale);
        });
      });
      try {
        await owner;
        await owner[retirement]();
        gate.resolve();
        await continuation;
        assert(deniedFromExporter);
        assert.equal(messages.length, 1);
        assert.equal(messages[0].name, 'root');
        assert.deepEqual(messages[0].args, ['late checkpoint failed']);
        assert.equal(ctx.get('late'), undefined);
      } finally { gate.resolve(); await ctx.dispose(); }
    });
  }

  test(`${profile} reverse Rust calls retain their wait authority after factory setup completes`, async () => {
    const ctx = new Context({addon});
    let rust, checked = false;
    ctx.provide('jsSource', {
      read: () => 7,
      record: () => null,
      query: async () => {
        await assert.rejects(ctx.dispose(), reentrant);
        await assert.rejects(ctx.fiber.dispose(), reentrant);
        await assert.rejects(ctx.settle(), reentrant);
        assert.throws(() => rust.dispose(), reentrant);
        checked = true;
        return 'retained Rust authority';
      },
    });
    try {
      rust = await ctx.rustPlugin('fixture.counter');
      assert.equal(rust.state, FiberState.ACTIVE);
      assert.equal(await ctx.rustCounter.request(), 'retained Rust authority');
      assert(checked);
    } finally { await ctx.dispose(); }
  });
}
