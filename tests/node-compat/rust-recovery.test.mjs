import test from 'node:test';
import assert from 'node:assert/strict';
import { fileURLToPath } from 'node:url';
import { Context as CordisContext, domainMutation } from '../../packages/compat-cordis/index.js';
import { Context as HarnessContext } from '../../packages/compat-harness/index.js';
const addon=fileURLToPath(new URL('../../target/node-compat/interop-fixture.node',import.meta.url));
const messages = error => [error?.message, ...(error instanceof AggregateError ? error.errors.flatMap(messages) : [])].join(' | ');

for(const [profile,Context] of [['cordis',CordisContext],['harness',HarnessContext]]) {
  test(`${profile}: explicit native Rust cleanup recovery admits the pending setup and publication`,async()=>{
    const ctx=new Context({addon}), trace=[];
    let reads=0, provider, consumer, fail=true, recoverySetup;
    ctx.provide('jsSource',{
      read(){
        if(++reads===2) {
          recoverySetup=ctx.fiber._domain.rust.hooks.invocation();
          assert.equal(recoverySetup.kind,'setup');
          assert.equal(recoverySetup.active,false);
          assert.equal(recoverySetup.parentInvocation.active,true);
        }
        return reads;
      },
      query(){
        assert.equal(ctx.fiber._domain.rust.hooks.invocation().kind,'rust-call');
        return 'ordinary call';
      },
      record(...args){trace.push(args);return null;},
    });
    try {
      provider=await ctx.rustPlugin('fixture.counter');
      consumer=await ctx.inject(['rustCounter'],()=>()=>{if(fail)throw new Error('consumer cleanup failure');});
      const original=ctx.rustCounter;
      assert.equal(original.read(),1);
      await assert.rejects(provider.restart(),error=>/consumer cleanup failure/.test(messages(error)));
      await ctx.settle().catch(()=>{}); // Consume the earlier error, not the failed inverse.
      assert.equal(ctx.snapshot().plugins.find(node=>node.id===consumer.id)?.cleanupFailed,true);
      fail=false;
      await consumer.retryCleanup();
      await provider.await();
      assert.equal(reads,2,'the retried inverse must permit a real new native setup');
      assert.equal(ctx.rustCounter.read(),2,'reverse Rust provide must publish in the recovery transaction');
      assert.throws(()=>original.read(),/STALE|no longer admitted/);
      assert.deepEqual(trace,[['cleanup',1]]);
      assert.equal(recoverySetup.parentInvocation.active,false,'setup authority must close with the actual callback');
      assert.equal(await ctx.rustCounter.request(),'ordinary call');
      await domainMutation(ctx,()=>{
        assert.throws(()=>ctx.provide('forbiddenRecovery',{}),error=>error.code==='CLEANUP_BLOCKED');
      },{recovery:true});
    } finally {
      fail=false;
      if(consumer && ctx.snapshot().plugins.some(node=>node.id===consumer.id&&node.cleanupFailed))await consumer.retryCleanup();
      await ctx.dispose();
    }
  });
}
