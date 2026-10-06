import test from 'node:test';
import assert from 'node:assert/strict';
import { Context, domainMutation } from '../../packages/compat-cordis/index.js';
import { RustModuleController, loadRustModule } from '../../packages/compat-loader/rust-module.js';

const digest = '1'.repeat(64);
const artifact = version => ({path:`/fixture-${version}.dylib`,sha256:digest});

// Native Driver lifecycle remains real; only executable module loading is
// substituted here. The independent native suite loads actual cdylib images.
function fixture(profile = 'cordis', options = {}) {
  const ctx = new Context({profile}), events = [], loaded = [], factories = new Map();
  const host = ctx.fiber._domain.rust;
  const original = host.loadModule;
  host.loadModule = request => {
    const version = /fixture-(.+)\.dylib$/.exec(request.path)[1];
    loaded.push(version);
    if (version === 'missing') throw new Error('DigestMismatch');
    const name = 'native-text-analysis', ref = `image:${version}:${name}`;
    if (!factories.has(version)) factories.set(version, {name:`mock-native:${version}`, apply: async (child, config) => {
      events.push(`start:${version}`);
      child.effect(() => async () => {
        events.push(`stop:${version}`);
        await options.cleanup?.(version, child, config);
      });
      await options.setup?.(version, child, config);
      if (version === 'fail') throw new Error('CandidateSetupFailed');
      child.provide(config?.service ?? 'nativeText',{analyze:()=>({version,config})});
    }});
    return { descriptor: {abi:1,module:version,pluginId:version === 'foreign'?'foreign':'text',buildId:version,path:request.path,sha256:request.sha256,retained:true,unloadSupported:false,
      factories:[{name,ref,inject:[],services:[{name:'nativeText',methods:[{name:'analyze',kind:'sync'}]}]}]},factories:new Map([[name,factories.get(version)]]) };
  };
  const create = parent => new RustModuleController(parent ?? ctx,{plugins:[{id:'text',factory:'native-text-analysis'}]});
  const dispose = async () => { host.loadModule = original; await ctx.dispose(); };
  return {ctx,events,loaded,create,dispose};
}

for (const profile of ['cordis','harness']) {
  test(`native module transactions replace one owned group on the same Driver (${profile})`, async () => {
    const f = fixture(profile), driver = f.ctx.fiber._domain.driver, controller = f.create();
    try {
      await controller.reload(artifact('v1'));
      const first = controller.snapshot();
      assert.equal(f.ctx.nativeText.analyze().version,'v1');
      await controller.retryCleanup(); // Healthy instances are not retired.
      assert.equal(f.ctx.nativeText.analyze().version,'v1');
      await controller.reload(artifact('v2'));
      assert.equal(f.ctx.nativeText.analyze().version,'v2');
      assert.equal(f.ctx.fiber._domain.driver,driver);
      assert.notEqual(controller.snapshot().entries[0].factoryRef, first.entries[0].factoryRef);
      assert.deepEqual(f.events,['start:v1','stop:v1','start:v2']);
      assert.equal(controller.revision,2);
      assert.equal(Object.isFrozen(controller.snapshot().module.factories[0]),true);
      await controller.dispose();
      assert.equal(f.ctx.snapshot().plugins.length,1);
    } finally { await f.dispose(); }
  });

  test(`candidate failure drains candidate then recreates old code (${profile})`, async () => {
    const f = fixture(profile), controller = f.create();
    try {
      await controller.reload(artifact('v1'));
      const old = controller.snapshot();
      await assert.rejects(controller.reload(artifact('fail')), error => error.code === 'NATIVE_MODULE_RELOAD_FAILED' && error.details.restored);
      assert.equal(f.ctx.nativeText.analyze().version,'v1');
      assert.equal(controller.snapshot().entries[0].factoryRef,old.entries[0].factoryRef);
      assert.notEqual(controller.snapshot().entries[0].fiberId,old.entries[0].fiberId);
      assert.deepEqual(f.events,['start:v1','stop:v1','start:fail','stop:fail','start:v1']);
      assert.equal(controller.revision,1);
      assert.equal(controller.lastReloadFailure.code,'NATIVE_MODULE_RELOAD_FAILED');
      await controller.dispose();
    } finally { await f.dispose(); }
  });

  test(`candidate cleanup failure retains journal until explicit retry (${profile})`, async () => {
    let once = true;
    const f = fixture(profile,{cleanup:version=>{ if(version==='fail' && once){once=false;throw new Error('RetainedCandidate');} }}), controller=f.create();
    try {
      await controller.reload(artifact('v1'));
      await assert.rejects(controller.reload(artifact('fail')), error=>error.code==='NATIVE_MODULE_RECOVERY_BLOCKED');
      assert.equal(controller.state,'blocked');
      assert.equal(f.events.filter(x=>x==='start:v1').length,1);
      await assert.rejects(controller.reload(artifact('v2')), error=>error.code==='CLEANUP_BLOCKED');
      await controller.retryCleanup();
      assert.equal(f.events.filter(x=>x.startsWith('start:')).length,2,'recovery creates no resources');
      await controller.reload(artifact('v2'));
      assert.equal(f.ctx.nativeText.analyze().version,'v2');
      assert.deepEqual(f.events.slice(-4),['stop:fail','start:v1','stop:v1','start:v2']);
      await controller.dispose();
    } finally { await f.dispose(); }
  });

  test(`old cleanup failure never starts candidate until explicit retry (${profile})`, async () => {
    let once = true;
    const f = fixture(profile,{cleanup:version=>{if(version==='v1'&&once){once=false;throw new Error('RetainedOld');}}}),controller=f.create();
    try {
      await controller.reload(artifact('v1'));
      await assert.rejects(controller.reload(artifact('v2')), error=>error.code==='NATIVE_MODULE_CLEANUP_BLOCKED');
      assert.equal(f.events.includes('start:v2'),false);
      await controller.retryCleanup();
      await controller.reload(artifact('v2'));
      assert.equal(f.events.filter(item=>item==='start:v1').length,1,'retirement resumes without creating a new old instance');
      assert.equal(f.ctx.nativeText.analyze().version,'v2');
      await controller.dispose();
    } finally { await f.dispose(); }
  });
}

test('artifact validation and descriptor mismatch preserve active identities',async()=>{
  const f=fixture(),controller=f.create();
  try {
    await controller.reload(artifact('v1')); const before=controller.snapshot();
    await assert.rejects(controller.reload({path:'/next',sha256:'invalid'}),error=>error.code==='NATIVE_MODULE_DIGEST');
    await assert.rejects(controller.reload({path:'relative.dylib',sha256:digest}),error=>error.code==='NATIVE_MODULE_PATH');
    await assert.rejects(controller.reload(artifact('missing')),/DigestMismatch/);
    await assert.rejects(controller.reload(artifact('foreign')),error=>error.code==='NATIVE_MODULE_IDENTITY');
    assert.equal(controller.snapshot().entries[0].fiberId,before.entries[0].fiberId);
    assert.equal(controller.lastReloadFailure.code,'NATIVE_MODULE_IDENTITY');
    assert.deepEqual(f.events,['start:v1']);
    await controller.dispose();
  } finally {await f.dispose();}
});

test('consumer inverse finishes before old native teardown and candidate setup',async()=>{
  const gate=Promise.withResolvers(),entered=Promise.withResolvers(),f=fixture(),controller=f.create();
  try {
    await controller.reload(artifact('v1'));
    const consumer=f.ctx.plugin({inject:['nativeText'],apply:child=>{
      const version=child.nativeText.analyze().version;
      child.effect(()=>async()=>{if(version==='v1'){entered.resolve();await gate.promise;}});
    }});
    await consumer.await();
    const reload=controller.reload(artifact('v2'));
    await entered.promise;
    assert.deepEqual(f.events,['start:v1']);
    gate.resolve(); await reload;
    assert.equal(f.ctx.nativeText.analyze().version,'v2');
    await consumer.dispose(); await controller.dispose();
  } finally {gate.resolve();await f.dispose();}
});

test('queued reload captures artifact input and orders with domain shutdown',async()=>{
  const gate=Promise.withResolvers(),f=fixture(),controller=f.create();
  try {
    await controller.reload(artifact('v1'));
    const blocker=domainMutation(f.ctx,()=>gate.promise);
    const input=artifact('v2'),reload=controller.reload(input);input.path='/fixture-foreign.dylib';
    const closing=f.ctx.dispose();
    await assert.rejects(controller.reload(artifact('v1')),error=>error.code==='DOMAIN_CLOSED');
    gate.resolve(); await blocker; await reload; await closing;
    assert.deepEqual(f.loaded,['v1','v2']);
    assert.equal(f.ctx.snapshot().plugins.length,0);
  } finally {gate.resolve();await f.dispose();}
});

test('previous owner generation and managed callbacks cannot mutate controller',async()=>{
  const f=fixture();
  try {
    const owner=f.ctx.plugin(()=>{});await owner.await();
    const controller=f.create(owner.ctx);await controller.reload(artifact('v1'));
    const probe=f.ctx.plugin(async()=>{
      await assert.rejects(controller.reload(artifact('v2')),error=>error.code==='REENTRANT_MUTATION');
      await assert.rejects(controller.reconcile({...artifact('v2'),plugins:[]}),error=>error.code==='REENTRANT_MUTATION');
      await assert.rejects(controller.dispose(),error=>error.code==='REENTRANT_MUTATION');
    });await probe.await();
    assert.equal(controller.state,'active');
    await owner.restart();
    await assert.rejects(controller.reload(artifact('v2')),error=>error.code==='NATIVE_MODULE_OWNER_REMOVED');
    await assert.rejects(controller.reconcile({...artifact('v2'),plugins:[]}),error=>error.code==='NATIVE_MODULE_OWNER_REMOVED');
    await controller.dispose();await probe.dispose();await owner.dispose();
  }finally{await f.dispose();}
});

test('initial failure returns a controller retaining cleanup access',async()=>{
  let once=true;
  const f=fixture('cordis',{cleanup:version=>{if(version==='fail'&&once){once=false;throw new Error('CleanupFailure');}}});
  try {
    let controller;
    await assert.rejects(loadRustModule(f.ctx,{...artifact('fail'),plugins:[{id:'text',factory:'native-text-analysis'}]}),error=>{
      controller=error.controller;return error.code==='NATIVE_MODULE_RECOVERY_BLOCKED';
    });
    assert.ok(controller instanceof RustModuleController);
    await controller.retryCleanup();await controller.dispose();
    assert.equal(f.ctx.snapshot().plugins.length,1);
  }finally{await f.dispose();}
});

test('post-allocation observer failures retain and remove actual candidate fibers',async()=>{
  const f=fixture(),controller=f.create();
  try {
    await controller.reload(artifact('v1'));
    let once=true;
    const remove=f.ctx.on('internal/plugin',fiber=>{if(once&&fiber.name==='mock-native:v2'){once=false;throw new Error('ObserverFailure');}});
    await assert.rejects(controller.reload(artifact('v2')),error=>error.code==='NATIVE_MODULE_RELOAD_FAILED'&&error.details.restored);
    remove();
    assert.equal(f.ctx.nativeText.analyze().version,'v1');
    assert.equal(f.ctx.snapshot().plugins.length,3);
    await controller.dispose();
  }finally{await f.dispose();}
});

test('old activation failure stays recoverable without losing the factory recipe',async()=>{
  let starts=0, blockOld=false;
  const f=fixture('cordis',{setup:version=>{if(version==='v1'){starts++;if(blockOld)throw new Error('OldSetupUnavailable');}}}),controller=f.create();
  try {
    await controller.reload(artifact('v1'));blockOld=true;
    await assert.rejects(controller.reload(artifact('fail')),error=>error.code==='NATIVE_MODULE_RESTORE_FAILED');
    assert.equal(controller.state,'blocked');assert.equal(starts,2);
    await controller.retryCleanup();assert.equal(starts,2);
    blockOld=false;await controller.reload(artifact('v2'));
    assert.equal(starts,3);assert.equal(f.ctx.nativeText.analyze().version,'v2');
    await controller.dispose();
  }finally{await f.dispose();}
});

test('queued native replacements use the same FIFO as direct Fiber revisions',async()=>{
  const f=fixture(),controller=f.create(),order=[];
  try {
    await controller.reload(artifact('v1'));
    const direct=f.ctx.plugin(child=>{order.push('setup');child.effect(()=>()=>order.push('cleanup'));});
    await direct.await();
    const gate=Promise.withResolvers(),entered=Promise.withResolvers();
    const first=domainMutation(f.ctx,async()=>{entered.resolve();await gate.promise;});await entered.promise;
    const second=controller.reload(artifact('v2')).then(()=>order.push('native'));
    const third=direct.restart().then(()=>order.push('direct'));
    gate.resolve();await Promise.all([first,second,third]);
    assert.ok(order.indexOf('native')<order.indexOf('direct'));
    await direct.dispose();await controller.dispose();
  }finally{await f.dispose();}
});

test('controller commits its configured entries while external consumer failures stay visible',async()=>{
  const f=fixture(),controller=f.create();
  try {
    await controller.reload(artifact('v1'));
    const consumer=f.ctx.plugin({inject:['nativeText'],apply:child=>{
      if(child.nativeText.analyze().version==='v2')throw new Error('ExternalConsumerRejectedV2');
    }});
    await consumer.await();
    await controller.reload(artifact('v2'));
    assert.equal(controller.state,'active');
    assert.equal(controller.revision,2);
    assert.equal(f.ctx.nativeText.analyze().version,'v2');
    await assert.rejects(consumer.await(),/ExternalConsumerRejectedV2/);
    const failed=f.ctx.snapshot().plugins.find(node=>node.id===consumer.id);
    assert.equal(failed.state.toLowerCase(),'failed');
    await consumer.dispose();await controller.dispose();
  }finally{await f.dispose();}
});


const recipe = (id = 'text', config = {}) => ({id,factory:'native-text-analysis',config});
for (const profile of ['cordis','harness']) {
  test(`reconcile commits changed configuration and the complete owned entry set (${profile})`, async () => {
    const f=fixture(profile),controller=f.create();
    try {
      await controller.reconcile({...artifact('v1'),plugins:[recipe('first',{service:'firstText',value:1})]});
      const previous=controller.snapshot().entries[0].fiberId;
      await controller.reconcile({...artifact('v1'),plugins:[recipe('first',{service:'firstText',value:2}),recipe('second',{service:'secondText',value:3})]});
      assert.equal(f.ctx.firstText.analyze().config.value,2);
      assert.equal(f.ctx.secondText.analyze().config.value,3);
      assert.notEqual(controller.snapshot().entries[0].fiberId,previous);
      assert.deepEqual(controller.snapshot().entries.map(entry=>entry.id),['first','second']);
      await controller.reconcile({...artifact('v2'),plugins:[recipe('second',{service:'secondText',value:4})]});
      assert.equal(f.ctx.get('firstText'),undefined);
      assert.equal(f.ctx.secondText.analyze().config.value,4);
      assert.deepEqual(controller.snapshot().entries.map(entry=>entry.id),['second']);
      await controller.reload(artifact('v1'));
      assert.equal(f.ctx.secondText.analyze().config.value,4,'reload keeps the successfully committed config');
      assert.equal(controller.revision,4);
      await controller.dispose();
    } finally {await f.dispose();}
  });

  test(`failed reconcile restores the old immutable recipes and committed revision (${profile})`, async () => {
    const f=fixture(profile),controller=f.create(),old=recipe('original',{nested:{value:'original'}});
    try {
      await controller.reconcile({...artifact('v1'),plugins:[old]});
      old.config.nested.value='caller mutation';
      f.ctx.nativeText.analyze().config.nested.value='plugin mutation';
      const before=controller.snapshot();
      await assert.rejects(controller.reconcile({...artifact('fail'),plugins:[recipe('candidate',{nested:{value:'candidate'}})]}),error=>error.code==='NATIVE_MODULE_RELOAD_FAILED'&&error.details.restored);
      assert.equal(f.ctx.nativeText.analyze().config.nested.value,'original');
      assert.deepEqual(controller.snapshot().entries.map(entry=>entry.id),['original']);
      assert.notEqual(controller.snapshot().entries[0].fiberId,before.entries[0].fiberId);
      assert.equal(controller.revision,1);
      await controller.reload(artifact('v2'));
      assert.equal(f.ctx.nativeText.analyze().config.nested.value,'original');
      await controller.dispose();
    } finally {await f.dispose();}
  });

  test(`empty reconciliation disables and later re-enables a validated module (${profile})`, async () => {
    const f=fixture(profile),controller=f.create();
    try {
      await controller.reload(artifact('v1'));
      await controller.reconcile({...artifact('v1'),plugins:[]});
      assert.equal(controller.state,'active');
      assert.equal(controller.snapshot().module.buildId,'v1');
      assert.deepEqual(controller.snapshot().entries,[]);
      assert.equal(f.ctx.get('nativeText'),undefined);
      assert.equal(f.ctx.snapshot().plugins.length,1,'a disabled generation owns no group Fiber');
      await controller.reload(artifact('v2'));
      assert.deepEqual(f.events,['start:v1','stop:v1'],'reload preserves the disabled recipe');
      await assert.rejects(controller.reconcile({...artifact('fail'),plugins:[recipe('new')]}),error=>error.code==='NATIVE_MODULE_RELOAD_FAILED'&&error.details.restored);
      assert.equal(controller.snapshot().module.buildId,'v2');
      assert.deepEqual(controller.snapshot().entries,[]);
      assert.equal(controller.revision,3);
      await controller.reconcile({...artifact('v1'),plugins:[recipe('enabled',{value:5})]});
      assert.equal(f.ctx.nativeText.analyze().config.value,5);
      await controller.dispose();
    } finally {await f.dispose();}
  });
}

test('reconcile captures queued recipes while queued reload observes the preceding successful commit',async()=>{
  const gate=Promise.withResolvers(),f=fixture(),controller=f.create();
  try {
    await controller.reload(artifact('v1'));
    const blocker=domainMutation(f.ctx,()=>gate.promise);
    const input={...artifact('v2'),plugins:[recipe('captured',{nested:{value:7}})]};
    const changed=controller.reconcile(input),reload=controller.reload(artifact('v1'));
    input.path='/fixture-foreign.dylib';input.plugins[0].config.nested.value=99;input.plugins[0].id='mutated';input.plugins.push(recipe('extra'));
    gate.resolve();await Promise.all([blocker,changed,reload]);
    assert.equal(f.ctx.nativeText.analyze().version,'v1');
    assert.equal(f.ctx.nativeText.analyze().config.nested.value,7);
    assert.deepEqual(controller.snapshot().entries.map(entry=>entry.id),['captured']);
    assert.deepEqual(f.loaded,['v1','v2','v1']);
    await controller.dispose();
  } finally {gate.resolve();await f.dispose();}
});

test('invalid reconcile recipes and missing candidate factories never retire the active group',async()=>{
  const f=fixture(),controller=f.create();
  try {
    await controller.reload(artifact('v1'));const before=controller.snapshot();
    for (const plugins of [undefined,{},[recipe(),recipe()], [{id:'bad',factory:'missing'}], [recipe('invalid',()=>{})]]) {
      await assert.rejects(controller.reconcile({...artifact('v2'),plugins}));
    }
    assert.equal(controller.snapshot().entries[0].fiberId,before.entries[0].fiberId);
    assert.deepEqual(f.events,['start:v1']);
    await controller.reload(artifact('v2'));
    assert.deepEqual(controller.snapshot().entries.map(entry=>entry.id),['text']);
    await controller.dispose();
  } finally {await f.dispose();}
});

test('retained candidate cleanup and failed restoration keep the original config through recovery',async()=>{
  let cleanupFails=true,restoreFails=false;
  const restored=[];
  const f=fixture('cordis',{
    cleanup:version=>{if(version==='fail'&&cleanupFails){cleanupFails=false;throw new Error('CandidateCleanupFailed');}},
    setup:(version,child,config)=>{if(version==='v1'){restored.push(config.value);if(restoreFails)throw new Error('RestoreFailed');}},
  }),controller=f.create();
  try {
    await controller.reconcile({...artifact('v1'),plugins:[recipe('old',{value:'old'})]});
    await assert.rejects(controller.reconcile({...artifact('fail'),plugins:[recipe('failed',{value:'failed'})]}),error=>error.code==='NATIVE_MODULE_RECOVERY_BLOCKED');
    await controller.retryCleanup();
    restoreFails=true;
    await assert.rejects(controller.reconcile({...artifact('v2'),plugins:[recipe('next',{value:'next'})]}),error=>error.code==='NATIVE_MODULE_RESTORE_FAILED');
    assert.deepEqual(restored,['old','old']);
    await controller.retryCleanup();restoreFails=false;
    await controller.reload(artifact('v2'));
    assert.deepEqual(restored,['old','old','old']);
    assert.equal(f.ctx.nativeText.analyze().config.value,'old');
    assert.deepEqual(controller.snapshot().entries.map(entry=>entry.id),['old']);
    assert.equal(controller.revision,2);
    await controller.dispose();
  } finally {restoreFails=false;await f.dispose();}
});

test('failed retirement keeps old config as rollback after cleanup-only recovery',async()=>{
  let once=true;
  const f=fixture('cordis',{cleanup:version=>{if(version==='v1'&&once){once=false;throw new Error('OldCleanupFailed');}}}),controller=f.create();
  try {
    await controller.reconcile({...artifact('v1'),plugins:[recipe('old',{value:'old'})]});
    await assert.rejects(controller.reconcile({...artifact('v2'),plugins:[recipe('uncommitted',{value:'new'})]}),error=>error.code==='NATIVE_MODULE_CLEANUP_BLOCKED');
    await controller.retryCleanup();
    await assert.rejects(controller.reconcile({...artifact('fail'),plugins:[recipe('failed',{value:'failed'})]}),error=>error.code==='NATIVE_MODULE_RELOAD_FAILED'&&error.details.restored);
    assert.equal(f.ctx.nativeText.analyze().config.value,'old');
    assert.deepEqual(controller.snapshot().entries.map(entry=>entry.id),['old']);
    assert.equal(controller.revision,1);
    await controller.dispose();
  } finally {await f.dispose();}
});

test('loadRustModule accepts a disabled initial generation without allocating Fibers',async()=>{
  const f=fixture();
  try {
    const controller=await loadRustModule(f.ctx,{...artifact('v1'),plugins:[]});
    assert.equal(controller.state,'active');
    assert.deepEqual(controller.snapshot().entries,[]);
    assert.equal(f.ctx.snapshot().plugins.length,1);
    await controller.reconcile({...artifact('v2'),plugins:[recipe('first')]});
    assert.equal(f.ctx.nativeText.analyze().version,'v2');
    await controller.dispose();
  } finally {await f.dispose();}
});
