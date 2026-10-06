import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { Context, adaptObject, adaptCallback } from '../../packages/compat-cordis/index.js';
import { loadRustModule } from '../../packages/compat-loader/rust-module.js';

const extension = process.platform === 'darwin' ? 'dylib' : process.platform === 'win32' ? 'dll' : 'so';
const artifact = version => {
  const path = fileURLToPath(new URL(`../../target/node-compat/dynamic-fixture-${version}.${extension}`, import.meta.url));
  return { path, sha256: createHash('sha256').update(readFileSync(path)).digest('hex') };
};
const options = (version = 'v1', config = {}) => ({ ...artifact(version), plugins: [{ id: 'consumer', factory: 'native-js-resources', config }] });
const turn = () => new Promise(resolve => setImmediate(resolve));
const awaitEntry = (entered, ...operations) => Promise.race([entered, ...operations.map(operation => operation.then(() => {
  throw new Error('Native operation ended before reaching its test gate');
}))]);
const phases = (trace, phase) => trace.filter(item => item.phase === phase);
function noForeignResources(ctx) {
  assert.equal(ctx.fiber._domain.rust.streams.resources.size, 0);
  assert.equal(ctx.fiber._domain.rust.objects.resources.size, 0);
}
function zeroResources(ctx) {
  noForeignResources(ctx);
  for (const module of ctx.fiber._domain.rust.command({ op: 'module_info' }).modules) {
    for (const [kind, count] of Object.entries(module.resources)) assert.equal(count, 0, `${module.buildId}: ${kind}`);
  }
}
function provider(trace, revision = 'old', hooks = {}) {
  const record = event => { trace.push({ ...event, provider: revision }); return null; };
  return {
    record,
    async stream(config = {}) {
      await hooks.open?.('stream');
      record({ phase: 'stream-open' });
      const values = config.values ?? ['hello', null, { n: 3 }];
      let index = 0, attempts = 0;
      return {
        async next() {
          const at = index++;
          record({ phase: 'stream-next', index: at });
          await hooks.next?.(at);
          record({ phase: 'stream-landed', index: at });
          return at < values.length ? { done: false, value: values[at] } : { done: true };
        },
        async return() {
          record({ phase: 'stream-close', attempt: ++attempts });
          await hooks.close?.('stream');
          if (config.failCloseOnce && attempts === 1) throw new Error('stream-close-retry');
          return { done: true };
        },
      };
    },
    async object(config = {}) {
      await hooks.open?.('object');
      record({ phase: 'object-open' });
      let value = config.start ?? 0, attempts = 0;
      const target = {
        async read() { record({ phase: 'object-call' }); await hooks.call?.(); record({ phase: 'object-landed' }); return { value, provider: revision }; },
        add(delta) { value += delta; return value; },
        hidden() { throw new Error('must not call hidden method'); },
      };
      const ownership = config.ownership ?? 'owned';
      return adaptObject(target, { typeName: 'JsCounter', methods: ['read', 'add'], ownership,
        ...(ownership === 'owned' ? { dispose: async () => {
          record({ phase: 'object-close', attempt: ++attempts });
          await hooks.close?.('object');
          if (config.failCloseOnce && attempts === 1) throw new Error('object-close-retry');
        } } : {}),
      });
    },
    async callback() {
      await hooks.open?.('callback');
      record({ phase: 'callback-open' });
      return adaptCallback((a, b) => ({ sum: a + b, provider: revision }));
    },
  };
}
async function fixture(profile, hooks) {
  const ctx = new Context({ profile }), trace = [];
  try {
    ctx.provide('jsHost', provider(trace, 'old', hooks));
    const controller = await loadRustModule(ctx, options());
    return { ctx, trace, controller };
  } catch (error) { await ctx.dispose(); throw error; }
}

for (const profile of ['cordis', 'harness']) {
  test(`independent Rust consumes JS streams on demand and closes idle, partial and exhausted streams (${profile})`, async () => {
    const { ctx, trace, controller } = await fixture(profile);
    try {
      assert.deepEqual((await ctx.nativeJsResources.stream({ limit: 0 })).values, []);
      assert.equal(phases(trace, 'stream-next').length, 0);
      assert.equal(phases(trace, 'stream-close').length, 1);
      assert.deepEqual((await ctx.nativeJsResources.stream({ limit: 1 })).values, ['hello']);
      assert.equal(phases(trace, 'stream-next').length, 1);
      assert.deepEqual((await ctx.nativeJsResources.stream({})).values, ['hello', null, { n: 3 }]);
      assert.equal(phases(trace, 'stream-next').length, 5);
      assert.equal(phases(trace, 'stream-close').length, 3);
      noForeignResources(ctx);
      await controller.dispose(); zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });

  test(`independent Rust uses explicit JS object and callback interfaces with owned and borrowed release (${profile})`, async () => {
    const { ctx, trace, controller } = await fixture(profile);
    try {
      const result = await ctx.nativeJsResources.object({ args: [{ start: 4 }], calls: [{ method: 'add', args: [3] }, { method: 'read', args: [] }] });
      assert.deepEqual(result.descriptor, { typeName: 'JsCounter', methods: ['read', 'add'], ownership: 'owned' });
      assert.deepEqual(result.results, [7, { value: 7, provider: 'old' }]);
      assert.equal(phases(trace, 'object-close').length, 1);
      const borrowed = await ctx.nativeJsResources.object({ args: [{ ownership: 'borrowed', start: 9 }] });
      assert.equal(borrowed.descriptor.ownership, 'borrowed');
      assert.deepEqual(borrowed.results, [{ value: 9, provider: 'old' }]);
      assert.equal(phases(trace, 'object-close').length, 1);
      const callback = await ctx.nativeJsResources.callback({ calls: [[2, 3], [4, 5]] });
      assert.deepEqual(callback.results, [{ sum: 5, provider: 'old' }, { sum: 9, provider: 'old' }]);
      await assert.rejects(ctx.nativeJsResources.object({ calls: [{ method: 'hidden', args: [] }] }), /UndeclaredObjectMethod/);
      await assert.rejects(ctx.nativeJsResources.callback({ method: 'object' }), /InvalidCallbackDescriptor/);
      noForeignResources(ctx);
      await controller.dispose(); zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });

  test(`reverse resource admission rejects undeclared services, plain object lookalikes and non-JSON elements (${profile})`, async () => {
    const ctx = new Context({ profile }), trace = [];
    try {
      const host = provider(trace);
      ctx.provide('jsHost', { ...host, plain: () => ({ read: () => 1 }), invalid: () => ({ next: () => ({ done: false, value: 1n }), return: () => ({ done: true }) }) });
      const controller = await loadRustModule(ctx, options());
      for (const method of ['stream', 'object', 'callback']) {
        await assert.rejects(ctx.nativeJsResources[method]({ service: 'notDeclared' }), /UndeclaredInjection/);
      }
      await assert.rejects(ctx.nativeJsResources.object({ method: 'plain' }), /adaptObject|adaptCallback/);
      await assert.rejects(ctx.nativeJsResources.stream({ method: 'invalid' }), /finite JSON/);
      noForeignResources(ctx);
      await controller.dispose(); zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });

  test(`reverse close can retry and escaped SDK clones cannot outlive their opening action (${profile})`, async () => {
    const { ctx, trace, controller } = await fixture(profile);
    try {
      for (const kind of ['stream', 'object']) {
        const result = await ctx.nativeJsResources[kind]({ args: [{ failCloseOnce: true }], close: true, retryClose: true, escape: true });
        assert.match(result.closeError, new RegExp(`${kind}-close-retry`));
        assert.deepEqual(phases(trace, `${kind}-close`).map(event => event.attempt), [1, 2]);
        await assert.rejects(ctx.nativeJsResources[`stale_${kind}`](), /ActionClosed/);
      }
      noForeignResources(ctx);
      await controller.dispose(); zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });

  for (const kind of ['stream', 'object', 'callback']) {
    test(`dropped native ${kind} acquisition still joins the late JS result and releases it (${profile})`, { timeout: 15000 }, async () => {
      const entered = Promise.withResolvers(), release = Promise.withResolvers();
      const { ctx, trace, controller } = await fixture(profile, { open: async () => { entered.resolve(); await release.promise; } });
      let call;
      try {
        let completed = false;
        call = ctx.nativeJsResources.dropped_open({ kind, method: kind }).then(value => { completed = true; return value; }); call.catch(() => {});
        await awaitEntry(entered.promise, call); await turn();
        assert.equal(completed, false);
        release.resolve(); await call;
        noForeignResources(ctx);
        assert.equal(phases(trace, `${kind}-open`).length, 1);
        if (kind !== 'callback') assert.equal(phases(trace, `${kind}-close`).length, 1);
        await controller.dispose(); zeroResources(ctx);
      } finally { release.resolve(); await Promise.allSettled([call]); await ctx.dispose(); }
    });
  }

  for (const [method, kind, hook] of [['dropped_next', 'stream', 'next'], ['dropped_call', 'object', 'call'], ['stream_busy', 'stream', 'next'], ['object_busy', 'object', 'call']]) {
    test(`${method} preserves in-flight reverse work until its real JS completion (${profile})`, { timeout: 15000 }, async () => {
      const entered = Promise.withResolvers(), release = Promise.withResolvers();
      const { ctx, trace, controller } = await fixture(profile, { [hook]: async () => { entered.resolve(); await release.promise; } });
      let call;
      try {
        let completed = false;
        call = ctx.nativeJsResources[method]({}).then(value => { completed = true; return value; }); call.catch(() => {});
        await awaitEntry(entered.promise, call); await turn();
        assert.equal(completed, false);
        if (kind === 'object') assert.equal(phases(trace, 'object-close').length, 0);
        release.resolve(); const result = await call;
        if (method.endsWith('_busy')) {
          assert.match(result.closeError, /Busy/);
          if (kind === 'stream') assert.match(result.nextError, /Busy/);
        }
        const landed = phases(trace, `${kind}-landed`)[0], close = phases(trace, `${kind}-close`)[0];
        assert(landed && close);
        if (kind === 'object') assert(trace.indexOf(landed) < trace.indexOf(close));
        noForeignResources(ctx);
        await controller.dispose(); zeroResources(ctx);
      } finally { release.resolve(); await Promise.allSettled([call]); await ctx.dispose(); }
    });
  }

  test(`a dropped next awaiter triggers automatic return without needing cancellation (${profile})`, { timeout: 15000 }, async () => {
    const entered = Promise.withResolvers(), next = Promise.withResolvers(), closing = Promise.withResolvers();
    const { ctx, trace, controller } = await fixture(profile, {
      next: async () => { entered.resolve(); await next.promise; },
      close: async () => { next.resolve(); closing.resolve(); },
    });
    let call;
    try {
      call = ctx.nativeJsResources.dropped_next({}); call.catch(() => {});
      await awaitEntry(entered.promise, call);
      await awaitEntry(closing.promise, call);
      assert.equal((await call).dropped, 'next');
      assert.equal(phases(trace, 'stream-next').length, 1);
      assert.equal(phases(trace, 'stream-close').length, 1);
      noForeignResources(ctx);
      await controller.dispose(); zeroResources(ctx);
    } finally { next.resolve(); await Promise.allSettled([call]); await ctx.dispose(); }
  });

  test(`native cancellation starts JS return to unblock next and waits for both outcomes (${profile})`, { timeout: 15000 }, async () => {
    const entered = Promise.withResolvers(), next = Promise.withResolvers(), returning = Promise.withResolvers(), close = Promise.withResolvers();
    const { ctx, trace, controller } = await fixture(profile, {
      next: async () => { entered.resolve(); await next.promise; },
      close: async () => { next.resolve(); returning.resolve(); await close.promise; },
    });
    let call, disposing;
    try {
      call = ctx.nativeJsResources.stream({ limit: 1 }); call.catch(() => {});
      await awaitEntry(entered.promise, call);
      let disposed = false;
      disposing = controller.dispose().then(() => { disposed = true; }); disposing.catch(() => {});
      await awaitEntry(returning.promise, disposing); await turn();
      assert.equal(disposed, false);
      assert.equal(phases(trace, 'js-resources-cleanup').length, 0);
      close.resolve(); await Promise.allSettled([call]); await disposing;
      assert.equal(phases(trace, 'stream-close').length, 1);
      zeroResources(ctx);
    } finally { next.resolve(); close.resolve(); await Promise.allSettled([call, disposing]); await ctx.dispose(); }
  });

  test(`reverse objects drain into their old JS provider before native code replacement (${profile})`, { timeout: 15000 }, async () => {
    const entered = Promise.withResolvers(), release = Promise.withResolvers();
    const { ctx, trace, controller } = await fixture(profile, { call: async () => { entered.resolve(); await release.promise; } });
    let call, reloading;
    try {
      const driver = ctx.fiber._domain.driver, pid = process.pid;
      call = ctx.nativeJsResources.object({}); call.catch(() => {});
      await awaitEntry(entered.promise, call);
      let replaced = false;
      reloading = controller.reload(artifact('v2')).then(() => { replaced = true; }); reloading.catch(() => {});
      await turn(); assert.equal(replaced, false);
      assert.equal(phases(trace, 'object-close').length, 0);
      release.resolve(); await Promise.allSettled([call]); await reloading;
      const close = phases(trace, 'object-close')[0], cleanup = phases(trace, 'js-resources-cleanup')[0];
      assert(close && cleanup); assert(trace.indexOf(close) < trace.indexOf(cleanup));
      assert.equal(cleanup.version, 'v1');
      assert.equal((await ctx.nativeJsResources.object({})).version, 'v2');
      assert.equal(ctx.fiber._domain.driver, driver); assert.equal(process.pid, pid);
      await controller.dispose(); zeroResources(ctx);
    } finally { release.resolve(); await Promise.allSettled([call, reloading]); await ctx.dispose(); }
  });

  test(`failed automatic reverse close remains visible until lifecycle cleanup retries it (${profile})`, async () => {
    const { ctx, trace, controller } = await fixture(profile);
    try {
      await assert.rejects(ctx.nativeJsResources.object({ args: [{ failCloseOnce: true }] }), /object-close-retry/);
      assert.equal(ctx.fiber._domain.rust.objects.resources.size, 1);
      assert.deepEqual(phases(trace, 'object-close').map(event => event.attempt), [1]);
      await controller.dispose();
      assert.deepEqual(phases(trace, 'object-close').map(event => event.attempt), [1, 2]);
      zeroResources(ctx);
    } finally { await ctx.dispose(); }
  });

  for (const kind of ['stream', 'object']) {
    test(`native ${kind} close retries imported JS object cleanup with its original action (${profile})`, async () => {
      const ctx = new Context({ profile }), trace = [];
      try {
        ctx.provide('jsHost', provider(trace));
        const controller = await loadRustModule(ctx, { ...artifact('v1'), plugins: [{ id: 'exporter', factory: 'native-resource-consumer' }] });
        const resource = ctx.nativeResources[kind]({ closeObjectArgs: [{ failCloseOnce: true }] });
        const close = () => kind === 'stream' ? resource.return() : resource.close();
        await assert.rejects(close(), /object-close-retry/);
        assert.equal(ctx.fiber._domain.rust.objects.resources.size, 1);
        const nativeCloses = () => phases(trace, `${kind}-close`).filter(event => event.version === 'v1');
        assert.equal(nativeCloses().length, 1);
        await close();
        assert.equal(nativeCloses().length, 1, 'retry must not rerun the successful native hook');
        assert.deepEqual(phases(trace, 'object-close').filter(event => !event.version).map(event => event.attempt), [1, 2]);
        noForeignResources(ctx);
        await controller.dispose(); zeroResources(ctx);
      } finally { await ctx.dispose(); }
    });
  }

  for (const kind of ['stream', 'object']) {
    test(`native cleanup retains its instance until a newly acquired JS ${kind} closes, without rerunning its hook (${profile})`, async () => {
      const ctx = new Context({ profile }), trace = [];
      let controller;
      try {
        ctx.provide('jsHost', provider(trace));
        const key = kind === 'stream' ? 'cleanupStreamArgs' : 'cleanupObjectArgs';
        controller = await loadRustModule(ctx, options('v1', { [key]: [{ failCloseOnce: true }] }));
        await assert.rejects(controller.dispose(), error => error.code === 'NATIVE_MODULE_CLEANUP_BLOCKED');
        assert.equal(controller.state, 'blocked');
        assert.equal(phases(trace, 'js-resources-cleanup').length, 1);
        assert.deepEqual(phases(trace, `${kind}-close`).map(event => event.attempt), [1]);
        assert.equal(ctx.fiber._domain.rust[kind === 'stream' ? 'streams' : 'objects'].resources.size, 1);
        const modules = ctx.fiber._domain.rust.command({ op: 'module_info' }).modules;
        assert.equal(modules.reduce((sum, module) => sum + module.resources.instances, 0), 1);
        await controller.retryCleanup(); await controller.dispose();
        assert.equal(phases(trace, 'js-resources-cleanup').length, 1);
        assert.deepEqual(phases(trace, `${kind}-close`).map(event => event.attempt), [1, 2]);
        zeroResources(ctx);
      } finally {
        try {
          if (controller?.state === 'blocked') await controller.retryCleanup();
          await controller?.dispose();
        } finally { await ctx.dispose(); }
      }
    });
  }

  test(`JS provider updates close reverse resources before old provider cleanup and keep the native factory (${profile})`, { timeout: 15000 }, async () => {
    const ctx = new Context({ profile }), trace = [];
    const entered = Promise.withResolvers(), release = Promise.withResolvers();
    let call, updating;
    try {
      const source = await ctx.plugin((child, config) => {
        child.provide('jsHost', provider(trace, config.revision, config.revision === 'old' ? { call: async () => { entered.resolve(); await release.promise; } } : {}));
        return () => trace.push({ phase: 'provider-cleanup', provider: config.revision });
      }, { revision: 'old' });
      const controller = await loadRustModule(ctx, options());
      const factoryRef = controller.snapshot().entries[0].factoryRef;
      call = ctx.nativeJsResources.object({}); call.catch(() => {});
      await awaitEntry(entered.promise, call);
      let updated = false;
      updating = (async () => { await source.update({ revision: 'new' }, true); await ctx.settle(); updated = true; })(); updating.catch(() => {});
      await turn(); assert.equal(updated, false);
      release.resolve(); await Promise.allSettled([call]); await updating; await ctx.settle();
      for (const phase of ['object-close', 'js-resources-cleanup']) {
        const event = phases(trace, phase)[0]; assert.equal(event.provider, 'old');
        assert(trace.indexOf(event) < trace.indexOf(phases(trace, 'provider-cleanup')[0]));
      }
      assert.equal(controller.snapshot().entries[0].factoryRef, factoryRef);
      assert.deepEqual((await ctx.nativeJsResources.object({})).results, [{ value: 0, provider: 'new' }]);
      await controller.dispose(); await source.dispose(); zeroResources(ctx);
    } finally { release.resolve(); await Promise.allSettled([call, updating]); await ctx.dispose(); }
  });
}


test('reverse stream payload limits exclude the bridge envelope and rejected object descriptors still release', async () => {
  const ctx = new Context(), trace = [];
  let value, typeName = 'Counter', disposed = 0;
  const nested = depth => Array.from({ length: depth }).reduce(item => [item], null);
  try {
    ctx.provide('jsHost', {
      ...provider(trace),
      stream: () => ({ next: () => ({ done: false, value }), return: () => ({ done: true }) }),
      object: () => adaptObject({ read: () => 1 }, { typeName, methods: ['read'], ownership: 'owned', dispose: () => { disposed++; } }),
    });
    const controller = await loadRustModule(ctx, options());
    for (value of ['x'.repeat(512 * 1024 - 2), nested(64), null]) {
      const result = await ctx.nativeJsResources.stream({ probe: true, limit: 1 });
      assert.deepEqual(result.probeBytes, [Buffer.byteLength(JSON.stringify(value))]);
      noForeignResources(ctx);
    }
    for (const [bad, error] of [['x'.repeat(512 * 1024), /ResultTooLarge/], [nested(65), /ValueTooDeep/], ['\ud800', /InvalidUnicode/]]) {
      value = bad;
      await assert.rejects(ctx.nativeJsResources.stream({ probe: true, limit: 1 }), error);
      noForeignResources(ctx);
    }
    for (const [name, error] of [['x'.repeat(512 * 1024), /ResultTooLarge/], ['\ud800', /InvalidUnicode/]]) {
      typeName = name;
      const before = disposed;
      await assert.rejects(ctx.nativeJsResources.object({}), error);
      assert.equal(disposed, before + 1);
      noForeignResources(ctx);
    }
    await controller.dispose(); zeroResources(ctx);
  } finally { await ctx.dispose(); }
});


test('a rejected descriptor and failed disposal retain an orphan for real lifecycle cleanup', async () => {
  const ctx = new Context(), trace = [];
  let attempts = 0;
  try {
    ctx.provide('jsHost', { ...provider(trace), object: () => adaptObject({ read: () => null }, {
      typeName: '\ud800', methods: ['read'], ownership: 'owned', dispose() {
        if (++attempts === 1) throw new Error('orphan-close-retry');
      },
    }) });
    const controller = await loadRustModule(ctx, options());
    await assert.rejects(ctx.nativeJsResources.object({}), /Invalid JS object and failed disposal/);
    assert.equal(attempts, 1);
    assert.equal(ctx.fiber._domain.rust.objects.resources.size, 1);
    assert.equal([...ctx.fiber._domain.rust.objects.resources.values()][0].orphan, true);
    await controller.dispose();
    assert.equal(attempts, 2);
    zeroResources(ctx);
  } finally { await ctx.dispose(); }
});
