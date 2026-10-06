import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { Context } from '../../packages/compat-cordis/index.js';
import { loadRustModule } from '../../packages/compat-loader/rust-module.js';

const extension = process.platform === 'darwin' ? 'dylib' : process.platform === 'win32' ? 'dll' : 'so';
function artifact(version) {
  const path = fileURLToPath(new URL(`../../target/node-compat/dynamic-fixture-${version}.${extension}`,import.meta.url));
  return {path,sha256:createHash('sha256').update(readFileSync(path)).digest('hex')};
}
const options = (version,config) => ({...artifact(version),plugins:[{id:'text',factory:'native-text-analysis',...(config?{config}:{})}]});
const analyze = (ctx,version) => assert.deepEqual(ctx.nativeText.analyze({text:'native code update'}),{version,words:3,characters:18,text:'native code update'});

for (const profile of ['cordis','harness']) {
  test(`real cdylib swap retains the native Driver and rejects old handles (${profile})`,async()=>{
    const ctx=new Context({profile});
    try {
      const driver=ctx.fiber._domain.driver;
      const controller=await loadRustModule(ctx,options('v1',{setup_pending:true,cleanup_pending:true}));
      const before=controller.snapshot(),old=ctx.nativeText;
      analyze(ctx,'v1');
      await controller.reload(artifact('v2'));
      analyze(ctx,'v2');
      assert.equal(ctx.fiber._domain.driver,driver);
      assert.notEqual(controller.snapshot().entries[0].factoryRef,before.entries[0].factoryRef);
      assert.equal(controller.snapshot().module.unloadSupported,false);
      const inventory=controller.inspect().images;
      assert.equal(inventory.retainedImageLimit,128);
      assert.ok(inventory.retainedImageCount>=2);
      assert.equal(inventory.modules.filter(module=>module.resources.instances>0).length,1);
      assert.throws(()=>old.analyze({text:'retired'}),error=>error.code==='STALE_EPISODE');
      const result=await ctx.nativeText.delayed({text:'async native'});
      assert.equal(result.version,'v2');
      await controller.dispose();
      assert.equal(ctx.snapshot().plugins.length,1);
      assert.ok(controller.inspect().images.modules.every(module=>Object.values(module.resources).every(count=>count===0)));
    }finally{await ctx.dispose();}
  });

  test(`loaded newer native code never retargets an old logical Fiber restart (${profile})`,async()=>{
    const ctx=new Context({profile});
    try {
      const left=ctx.isolate('nativeText'),right=ctx.isolate('nativeText');
      const first=await loadRustModule(left,options('v1'));
      const second=await loadRustModule(right,options('v2'));
      const before=first.snapshot();
      const fiber=ctx.fiber._domain.fibers.get(before.entries[0].fiberId);
      await fiber.restart();
      analyze(left,'v1');analyze(right,'v2');
      assert.equal(first.snapshot().entries[0].factoryRef,before.entries[0].factoryRef);
      await first.dispose();await second.dispose();
    }finally{await ctx.dispose();}
  });

  test(`real candidate setup failure reconstructs the old code and config (${profile})`,async()=>{
    const ctx=new Context({profile});
    try {
      const controller=await loadRustModule(ctx,options('v1'));
      const before=controller.snapshot();
      await assert.rejects(controller.reload(artifact('fail')),error=>error.code==='NATIVE_MODULE_RELOAD_FAILED'&&error.details.restored);
      analyze(ctx,'v1');
      assert.equal(controller.snapshot().entries[0].factoryRef,before.entries[0].factoryRef);
      assert.notEqual(controller.snapshot().entries[0].fiberId,before.entries[0].fiberId);
      await controller.reload(artifact('v2'));analyze(ctx,'v2');
      await controller.dispose();
    }finally{await ctx.dispose();}
  });

  test(`real asynchronous call is cancelled and drained before native replacement (${profile})`,async()=>{
    const ctx=new Context({profile});
    try {
      const controller=await loadRustModule(ctx,options('v1'));
      const call=ctx.nativeText.delayed({text:'pending',wait_for_cancel:true});
      const rejected=assert.rejects(call,/Cancelled|cancel/i);
      await controller.reload(artifact('v2'));await rejected;
      analyze(ctx,'v2');
      await controller.dispose();
    }finally{await ctx.dispose();}
  });

  test(`real failed cleanup blocks candidate until explicitly retried (${profile})`,async()=>{
    const ctx=new Context({profile});
    let controller;
    try {
      controller=await loadRustModule(ctx,options('v1',{fail_cleanup_once:true}));
      await assert.rejects(controller.reload(artifact('v2')),error=>error.code==='NATIVE_MODULE_CLEANUP_BLOCKED');
      assert.equal(controller.state,'blocked');
      assert.ok(ctx.snapshot().plugins.some(node=>node.cleanupFailed));
      await assert.rejects(controller.reload(artifact('v2')),error=>error.code==='CLEANUP_BLOCKED');
      await controller.retryCleanup();
      assert.equal(ctx.snapshot().plugins.length,1);
      await controller.reload(artifact('v2'));analyze(ctx,'v2');
      // The new instance has the same explicit cleanup config too.
      await assert.rejects(controller.dispose(),error=>error.code==='NATIVE_MODULE_CLEANUP_BLOCKED');
      await controller.retryCleanup();
      await controller.dispose();
      assert.equal(ctx.snapshot().plugins.length,1);
      assert.ok(controller.inspect().images.modules.every(module=>Object.values(module.resources).every(count=>count===0)));
    }finally{
      if(controller?.state==='blocked')await controller.retryCleanup();
      await controller?.dispose();await ctx.dispose();
    }
  });
}

test('native artifact digest rejection preserves the exact active Fiber',async()=>{
  const ctx=new Context();
  try {
    const controller=await loadRustModule(ctx,options('v1')),before=controller.snapshot();
    await assert.rejects(controller.reload({...artifact('v2'),sha256:'0'.repeat(64)}),/digest|sha|mismatch/i);
    assert.equal(controller.snapshot().entries[0].fiberId,before.entries[0].fiberId);
    analyze(ctx,'v1');await controller.dispose();
  }finally{await ctx.dispose();}
});

test('native values near the wire limit retain ready completion and release every job',async()=>{
  const ctx=new Context();
  try {
    const controller=await loadRustModule(ctx,options('v1'));
    const text='a'.repeat(512*1024-60);
    const expected={version:'v1',words:1,characters:text.length,text};
    assert.ok(Buffer.byteLength(JSON.stringify(expected))<=512*1024);
    assert.deepEqual(ctx.nativeText.analyze({text}),expected);
    assert.deepEqual(await ctx.nativeText.delayed({text}),expected);
    // Oversized application data is still a real Ready(Err) result. The host
    // must receive that state and drop the job rather than lose completion in
    // an outer protocol error after the SDK has marked the result consumed.
    await assert.rejects(ctx.nativeText.delayed({text:text+'a'.repeat(128)}),/ResultTooLarge/);
    const nested=Array.from({length:64}).reduce(value=>[value],null);
    assert.deepEqual(ctx.nativeText.analyze({nestedDepth:64}),nested);
    assert.deepEqual(await ctx.nativeText.delayed({nestedDepth:64}),nested);
    assert.throws(()=>ctx.nativeText.analyze({nestedDepth:65}),/ValueTooDeep/);
    await assert.rejects(ctx.nativeText.delayed({nestedDepth:65}),/ValueTooDeep/);
    await assert.rejects(ctx.nativeText.delayed({nestedDepth:130}),/ValueTooDeep/);
    assert.ok(controller.inspect().images.modules.every(module=>module.resources.jobs===0&&module.resources.retainedJobs===0));
    await controller.dispose();
    assert.equal(ctx.snapshot().plugins.length,1);
    assert.ok(controller.inspect().images.modules.every(module=>Object.values(module.resources).every(count=>count===0)));
  }finally{await ctx.dispose();}
});
