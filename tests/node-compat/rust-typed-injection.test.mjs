import test from 'node:test';
import assert from 'node:assert/strict';
import { fileURLToPath } from 'node:url';
import { Context as CordisContext, FiberState } from '../../packages/compat-cordis/index.js';
import { Context as HarnessContext } from '../../packages/compat-harness/index.js';
const addon=fileURLToPath(new URL('../../target/node-compat/interop-fixture.node',import.meta.url));
const messages=error=>[error?.message,...(error instanceof AggregateError?error.errors.flatMap(messages):[])].join(' | ');

for(const [profile,Context] of [['cordis',CordisContext],['harness',HarnessContext]]) {
  async function environment(t) {
    const ctx=new Context({addon});t.after(()=>ctx.dispose());
    await ctx.rustPlugin('fixture.typedControl');return ctx;
  }
  test(`${profile}: original configured typed dependency gates Pending before constructing the consumer`,async t=>{
    const ctx=await environment(t);
    const provider=await ctx.rustPlugin('fixture.typedLive',{initial:5});
    const host=provider._domain.rust, command=host.command.bind(host), seen=[];
    host.command=request=>{if(request.op==='typed_check')seen.push(structuredClone(request));return command(request);};
    try {
      const consumer=await ctx.intercept('typedLiveValue',{minimum:0}).rustPlugin('fixture.typedConfiguredReader',{minimum:0});
      assert.equal(consumer.state,FiberState.PENDING);
      assert.equal(ctx.get('typedLiveReader'),undefined);
      assert.deepEqual(seen.at(-1).config,{minimum:10,policy:{levels:[1,2]}});
      assert.equal(seen.at(-1).ticket.consumer,consumer.id);
      ctx.typedLiveControl.set(12);await ctx.settle();
      assert.equal(consumer.state,FiberState.ACTIVE);
      assert.deepEqual(ctx.typedLiveReader.read(),{current:12,original:12,sameArc:true});
      ctx.typedLiveControl.set(9);await ctx.settle();
      assert.equal(consumer.state,FiberState.PENDING);
      assert.ok(ctx.typedControl.events().some(event=>event.phase==='live-reader:cleanup'&&event.current===9));
    } finally {host.command=command;}
  });
  test(`${profile}: explicit typed null overrides inherited injection while plain requires inherits`,async t=>{
    const ctx=await environment(t);await ctx.rustPlugin('fixture.typedLive',{initial:5});
    const configured=ctx.isolate('typedLiveReader').intercept('typedLiveValue',{minimum:100});
    const inherited=ctx.isolate('typedLiveReader').intercept('typedLiveValue',{minimum:100});
    const a=await configured.rustPlugin('fixture.typedNullReader');
    const b=await inherited.rustPlugin('fixture.typedLiveReader');
    assert.equal(a.state,FiberState.ACTIVE);assert.equal(b.state,FiberState.PENDING);
    assert.equal(configured.typedLiveReader.read().current,5);
    ctx.typedLiveControl.set(101);await ctx.settle();
    assert.equal(b.state,FiberState.ACTIVE);assert.equal(inherited.typedLiveReader.read().current,101);
  });
  test(`${profile}: real Plugin and factory injection declaration mismatches fail before publishing`,async t=>{
    const ctx=await environment(t);await ctx.rustPlugin('fixture.typedLive',{initial:5});
    for(const [name,error] of [
      ['fixture.typedWrongConfigReader',/StaticInjectionConfigurationMismatch/],
      ['fixture.typedMissingConfigReader',/StaticInjectionConfigurationMismatch/],
      ['fixture.typedUndeclaredConfigReader',/UnsupportedStaticFeature: requires_with_config/],
    ]) {
      const consumer=ctx.rustPlugin(name);
      await assert.rejects(Promise.resolve(consumer),error);
      assert.equal(ctx.get('typedLiveReader'),undefined);
      await consumer.dispose();
    }
    assert.equal(ctx.typedControl.events().some(event=>event.phase==='live-reader:cleanup'),false);
  });
  test(`${profile}: invalid typed injection schema stays unavailable and cannot be overridden by interception`,async t=>{
    const ctx=await environment(t);await ctx.rustPlugin('fixture.typedLive',{initial:5});
    const consumer=await ctx.intercept('typedLiveValue',{minimum:0}).rustPlugin('fixture.typedSchemaReader');
    assert.equal(consumer.state,FiberState.PENDING);
    ctx.typedLiveControl.set(100);await ctx.settle();
    assert.equal(consumer.state,FiberState.PENDING);
    assert.equal(ctx.get('typedLiveReader'),undefined);
  });
  test(`${profile}: configured typed dependencies keep their own realm and shared slot`,async t=>{
    const ctx=await environment(t);
    const branch=()=>ctx.isolate('typedLiveValue').isolate('typedLiveControl').isolate('typedLiveReader');
    const left=branch(),right=branch();
    await left.rustPlugin('fixture.typedLive',{initial:5,label:'left'});
    await right.rustPlugin('fixture.typedLive',{initial:20,label:'right'});
    const a=await left.rustPlugin('fixture.typedConfiguredReader');
    const b=await right.rustPlugin('fixture.typedConfiguredReader');
    assert.equal(a.state,FiberState.PENDING);assert.equal(b.state,FiberState.ACTIVE);
    left.typedLiveControl.set(12);await ctx.settle();
    assert.equal(a.state,FiberState.ACTIVE);
    assert.equal(left.typedLiveReader.read().current,12);assert.equal(right.typedLiveReader.read().current,20);
  });
  test(`${profile}: configured typed consumer retains cleanup and restores after explicit recovery`,async()=>{
    const ctx=new Context({addon});let fail=true, leaf, expected=12;
    try {
      await ctx.rustPlugin('fixture.typedControl');
      const provider=await ctx.rustPlugin('fixture.typedLive',{initial:12});
      const consumer=await ctx.rustPlugin('fixture.typedConfiguredReader');
      const old=ctx.typedLiveReader;
      leaf=await ctx.inject(['typedLiveReader'],c=>()=>{
        assert.equal(c.typedLiveReader.read().current,expected);
        if(fail)throw new Error('configured consumer inverse must retry');
      });
      await assert.rejects(provider.restart(),error=>/configured consumer inverse must retry/.test(messages(error)));
      await ctx.settle().catch(()=>{});
      assert.equal(ctx.typedControl.events().some(event=>event.phase==='live-reader:cleanup'),false);
      fail=false;await leaf.retryCleanup();await provider.await();await ctx.settle();
      assert.equal(consumer.state,FiberState.ACTIVE);
      assert.equal(ctx.typedLiveReader.read().current,12);
      assert.throws(()=>old.read(),/STALE|no longer admitted/);
      expected=9;ctx.typedLiveControl.set(9);await ctx.settle();assert.equal(consumer.state,FiberState.PENDING);
    } finally {
      fail=false;
      if(leaf&&ctx.snapshot().plugins.some(node=>node.id===leaf.id&&node.cleanupFailed))await leaf.retryCleanup();
      await ctx.dispose();
    }
  });
}
