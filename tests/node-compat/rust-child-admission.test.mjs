import test from 'node:test';
import assert from 'node:assert/strict';
import { fileURLToPath } from 'node:url';
import { setImmediate as turn } from 'node:timers/promises';
import { Context as CordisContext, domainMutation } from '../../packages/compat-cordis/index.js';
import { Context as HarnessContext } from '../../packages/compat-harness/index.js';
const addon = fileURLToPath(new URL('../../target/node-compat/interop-fixture.node', import.meta.url));

for (const [profile, Context] of [['cordis', CordisContext], ['harness', HarnessContext]]) {
  async function fixture(t, config = {}) {
    const ctx = new Context({addon});
    t.after(() => ctx.dispose());
    await ctx.rustPlugin('fixture.typedControl');
    const pending = ctx.rustPlugin('fixture.typedCounter', config);
    const host = ctx.fiber._domain.rust;
    const session = () => [...host.sessions.values()].find(item => item.token.fiber.id === pending.id);
    return {ctx, pending, host, session};
  }
  test(`${profile}: Rust child dispatch cannot lend the mutation coordinator to status observers or child setup`, async t => {
    const f = await fixture(t);
    const parent = await f.pending;
    const target = await f.ctx.plugin(() => {});
    let observed = 0, entered = 0;
    await domainMutation(f.ctx, async steps => {
      const unlisten = f.ctx.on('internal/plugin', () => {
        observed++;
        assert.throws(() => steps.dispose(target), {code:'REENTRANT_MUTATION'});
      });
      try {
        const child = f.host.hooks.child(f.session(), () => {
          assert.equal(f.host.hooks.invocation().kind, 'rust-child');
          return parent.ctx.plugin(async () => {
            await Promise.resolve();
            assert.throws(() => steps.dispose(target), {code:'REENTRANT_MUTATION'});
            entered++;
          });
        });
        await child;
      } finally { await unlisten(); }
    });
    assert.equal(observed, 1); assert.equal(entered, 1);
    assert.ok(f.ctx.snapshot().plugins.some(item => item.id === target.id));
  });
  test(`${profile}: a background Rust child sees the active recovery restriction without inheriting its ALS`, async t => {
    const f = await fixture(t); await f.pending;
    const release = Promise.withResolvers();
    const recovery = domainMutation(f.ctx, () => release.promise, {recovery:true});
    try {
      let allocated = false;
      assert.equal(f.host.hooks.invocation(), undefined);
      assert.throws(() => f.host.hooks.child(f.session(), () => { allocated = true; }), {code:'CLEANUP_BLOCKED'});
      assert.equal(allocated, false);
    } finally { release.resolve(); await recovery; }
    await f.host.hooks.child(f.session(), () => f.pending.ctx.plugin(() => {}));
  });
  test(`${profile}: only a still-running original Rust setup admits children during recovery`, async t => {
    const label = `child-admission-${profile}`;
    const f = await fixture(t, {label, asyncSetup:true});
    const mounting = Promise.resolve(f.pending); mounting.catch(() => {});
    try {
      for (let i = 0; !f.ctx.typedControl.events().some(event => event.phase === 'counter:waiting' && event.label === label); i++) {
        assert.ok(i < 200, 'typed setup must reach its explicit gate'); await turn();
      }
      const current = f.session();
      assert.equal(current.setupToken.active, true);
      await domainMutation(f.ctx, async () => {
        await f.host.hooks.child(current, () => f.pending.ctx.plugin(() => {}));
      }, {recovery:true});
      f.ctx.typedControl.release(`setup:${label}`); await mounting;
      assert.equal(current.setupToken.active, false);
      await domainMutation(f.ctx, () => {
        assert.throws(() => f.host.hooks.child(current, () => f.pending.ctx.plugin(() => {})), {code:'CLEANUP_BLOCKED'});
      }, {recovery:true});
    } finally { f.ctx.typedControl.release(`setup:${label}`); await mounting; }
  });
  test(`${profile}: Rust child dispatch rejects an old session and isolates a current request from stale poll ancestry`, async t => {
    const f = await fixture(t); const parent = await f.pending;
    const old = f.session(), oldOrigin = {...old.token, active:false};
    await parent.restart();
    assert.throws(() => f.host.hooks.child(old, () => {}), {code:'STALE_EPISODE'});
    assert.throws(() => f.host.hooks.childRetire(old, () => {}), {code:'STALE_EPISODE'});
    const current = f.session();
    const child = f.host.hooks.run(oldOrigin, () => f.host.hooks.child(current, () => parent.ctx.plugin(() => {})));
    await child;
    await f.host.hooks.childRetire(current, () => child._dispose());
    assert.equal(f.ctx.snapshot().plugins.some(item => item.id === child.id), false);
  });
}
