import test from 'node:test';
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {Context as CordisContext, FiberState} from '../../packages/compat-cordis/index.js';
import {Context as HarnessContext} from '../../packages/compat-harness/index.js';
const addon=fileURLToPath(new URL('../../target/node-compat/interop-fixture.node',import.meta.url));
const turn=()=>new Promise(resolve=>setImmediate(resolve));
const message=error=>[error?.message,...(error?.errors??[]).map(message),error?.cause?message(error.cause):''].join(' | ');
for(const [profile,Context] of [['cordis',CordisContext],['harness',HarnessContext]]) {
  test(`${profile}: failed allocation observer retains its typed publication handle until actual reserved cleanup`,async t=>{
    const ctx=new Context({addon});
    t.after(()=>ctx.dispose());
    await ctx.rustPlugin('fixture.typedControl');
    const owner=await ctx.rustPlugin('fixture.typedDynamic');
    const manager=ctx.typedDynamicManager;
    const gate=Promise.withResolvers();
    let entered=false,finished=false,child;
    ctx.on('internal/plugin',fiber=>{
      if(!fiber.name.startsWith('rust:@cordis-child:'))return;
      child=fiber;
      fiber.effect(()=>async()=>{entered=true;await gate.promise;finished=true;});
      throw new Error('typed observer acquired then failed');
    });
    let joined;
    try {
      manager.publish('observer',8);
      const deadline=Date.now()+5000;
      while(!entered && Date.now()<deadline)await turn();
      assert.equal(entered,true);
      assert.ok(child);
      assert.equal(manager.status('observer').id,child.id);
      assert.equal(manager.status('observer').initialized,false);
      assert.equal(manager.status('observer').finished,false);
      assert.ok(ctx.snapshot().plugins.some(node=>node.id===child.id));
      joined=manager.join('observer');
      joined.catch(()=>{});
      let landed=false;joined.then(()=>{landed=true;},()=>{landed=true;});
      await turn();assert.equal(landed,false);
      gate.resolve();
      await assert.rejects(joined,error=>/typed observer acquired then failed/.test(message(error)));
      await assert.rejects(ctx.settle(),error=>/typed observer acquired then failed/.test(message(error)));
      assert.equal(finished,true);
      assert.equal(manager.status('observer').finished,true);
      assert.equal(ctx.snapshot().plugins.some(node=>node.id===child.id),false);
      assert.equal(owner.state,FiberState.ACTIVE);
    } finally {
      gate.resolve();
      if(joined)await joined.catch(()=>{});
      await ctx.settle().catch(()=>{});
    }
  });
}
