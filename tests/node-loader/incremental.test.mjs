import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, mkdir, writeFile, rm } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { Context, FiberState } from '../../packages/compat-cordis/index.js';
import { Loader, ModuleHost } from '../../packages/compat-loader/index.js';

const fixture = name => new URL(`./fixtures/${name}.mjs`, import.meta.url).href;
const tracked = (id, label = id) => ({ id, name: fixture('tracked'), config: { label } });
const provider = (value, extra = {}) => ({ id: 'provider', name: fixture('provider'), config: { value, ...extra } });
const consumer = { id: 'consumer', name: fixture('consumer') };
const host = options => { const ctx = new Context(), audit = []; ctx.provide('audit', audit); return { ctx, audit, loader: new Loader(ctx, options) }; };

test('no-op and sibling reorder preserve all instances and normalize JSON object key order', async () => {
  const { ctx, audit, loader } = host();
  try {
    await loader.apply([tracked('a'), { id:'group', group:true, entries:[tracked('b')] }]);
    const fibers = new Map([...loader.entries()].map(entry => [entry.id, entry.fiber]));
    await loader.apply([{ entries:[{ config:{label:'b'}, name:fixture('tracked'), id:'b' }], group:true, id:'group' }, tracked('a')]);
    await loader.reload();
    for (const entry of loader.entries()) assert.equal(entry.fiber, fibers.get(entry.id));
    assert.deepEqual(audit, ['tracked:start:a', 'tracked:start:b']);
    await loader.dispose();
    assert.equal(audit.filter(item => item.startsWith('tracked:stop:')).length, 2);
  } finally { await ctx.dispose(); }
});

test('only changed provider is replaced; dependent consumer restarts in the same fiber and unrelated siblings survive', async () => {
  const { ctx, audit, loader } = host();
  try {
    await loader.apply([provider('old'), consumer, tracked('unrelated')]);
    const oldProvider = loader.resolve('provider').fiber;
    const oldConsumer = loader.resolve('consumer').fiber;
    const oldEpisode = oldConsumer._generation;
    const unrelated = loader.resolve('unrelated').fiber;
    await loader.update('provider', { config:{value:'new'} });
    assert.notEqual(loader.resolve('provider').fiber, oldProvider);
    assert.equal(loader.resolve('consumer').fiber, oldConsumer);
    assert.notEqual(oldConsumer._generation, oldEpisode);
    assert.equal(loader.resolve('unrelated').fiber, unrelated);
    assert.equal(audit.filter(item => item==='tracked:start:unrelated').length, 1);
    assert.equal(audit.includes('tracked:stop:unrelated'), false);
    assert.ok(audit.indexOf('release:old') < audit.indexOf('stop:old'));
    assert.ok(audit.indexOf('stop:old') < audit.indexOf('start:new'));
    await loader.dispose();
  } finally { await ctx.dispose(); }
});

test('children can be added and removed under a retained parent without losing ownership cleanup', async () => {
  const { ctx, audit, loader } = host();
  const tree = children => [{ id:'group', group:true, entries:children }];
  try {
    await loader.apply(tree([tracked('a')]));
    const parent = loader.resolve('group').fiber, a = loader.resolve('group/a').fiber;
    await loader.apply(tree([tracked('a'), tracked('b')]));
    assert.equal(loader.resolve('group').fiber, parent);
    assert.equal(loader.resolve('group/a').fiber, a);
    await loader.apply(tree([tracked('b')]));
    assert.equal(loader.resolve('group').fiber, parent);
    assert.equal(a.uid, null);
    assert.equal(audit.filter(item => item==='tracked:stop:a').length, 1);
    await loader.dispose();
    assert.equal(audit.filter(item => item==='tracked:stop:b').length, 1);
    assert.equal(ctx.snapshot().plugins.length, 1);
  } finally { await ctx.dispose(); }
});

test('failed child replacement preserves parent and sibling, restores old controller for later dependency restart', async () => {
  const { ctx, audit, loader } = host();
  let revoke = ctx.provide('gate', 1);
  const tree = (value, extra) => [{ id:'group', group:true, inject:['gate'], entries:[provider(value, extra), tracked('sibling')] }];
  try {
    await loader.apply(tree('old'));
    const parent = loader.resolve('group').fiber, sibling = loader.resolve('group/sibling').fiber;
    const entry = loader.resolve('group/provider');
    await assert.rejects(loader.apply(tree('candidate', {fail:true})), error => error.code==='RELOAD_FAILED' && error.details.restored);
    assert.equal(loader.resolve('group').fiber, parent);
    assert.equal(loader.resolve('group/sibling').fiber, sibling);
    assert.equal(loader.resolve('group/provider'), entry);
    assert.equal(entry.options.config.value, 'old');
    assert.ok(audit.indexOf('stop:candidate') < audit.lastIndexOf('start:old'));
    assert.equal(audit.includes('tracked:stop:sibling'), false);
    await revoke(); await ctx.settle();
    assert.equal(parent.state, FiberState.PENDING);
    revoke = ctx.provide('gate', 2); await ctx.settle();
    assert.equal(parent.state, FiberState.ACTIVE);
    assert.equal(ctx.message.value, 'old');
    assert.equal(entry.fiber.state, FiberState.ACTIVE);
    assert.equal(audit.filter(item => item==='start:candidate').length, 1);
    await loader.dispose(); await revoke();
  } finally { await ctx.dispose(); }
});

test('changing group isolation replaces descendants but retains independent groups', async () => {
  const { ctx, loader } = host();
  const group = (id, label) => ({ id, group:true, isolate:{message:label}, entries:[provider(id), consumer] });
  try {
    await loader.apply([group('left','old'), group('right','right')]);
    const left = loader.resolve('left/provider').fiber, right = loader.resolve('right/provider').fiber;
    await loader.update('left', { isolate:{message:'new'} });
    assert.notEqual(loader.resolve('left/provider').fiber, left);
    assert.equal(loader.resolve('right/provider').fiber, right);
    await loader.dispose();
  } finally { await ctx.dispose(); }
});

test('include child updates retain source base URL and unchanged group identity', async () => {
  const { ctx, loader } = host();
  const directory = await mkdtemp(join(tmpdir(), 'cordis-loader-origins-'));
  try {
    await mkdir(join(directory, 'nested'));
    await writeFile(join(directory, 'nested/plugin.mjs'), "export default (ctx, config) => ctx.provide('origin', { base:ctx.baseUrl, value:config.value });");
    await writeFile(join(directory, 'nested/tree.json'), JSON.stringify([{id:'child',name:'./plugin.mjs',config:{value:1}}]));
    await writeFile(join(directory, 'root.json'), JSON.stringify([{id:'group',include:'./nested/tree.json'}]));
    await loader.loadFile(join(directory, 'root.json'));
    const group = loader.resolve('group').fiber, base = ctx.origin.base;
    await loader.update('group/child', {config:{value:2}});
    assert.equal(loader.resolve('group').fiber, group);
    assert.equal(ctx.origin.base, base);
    assert.equal(ctx.origin.value, 2);
    await loader.update('group/child', {name:'./plugin.mjs'});
    assert.equal(ctx.origin.base, base);
    await loader.dispose();
  } finally { await ctx.dispose(); await rm(directory, {recursive:true,force:true}); }
});

test('prepared module adapter revisions replace only their entries and rollback retains old factory', async () => {
  let revision=1, broken=false;
  const first = c => { c.provide('version', 1); };
  const second = c => { c.provide('version', 2); if (broken) throw new Error('factory failed'); };
  const moduleHost = new ModuleHost({loadModule:async url => url===fixture('provider')
    ? {plugin:revision===1?first:second,revision}
    : {plugin:await import(url),revision:'fixed'}});
  const {ctx,audit,loader}=host({moduleHost});
  try {
    const tree=[{id:'version',name:fixture('provider')},tracked('keep')];
    await loader.apply(tree);
    const original=loader.resolve('version').fiber, keep=loader.resolve('keep').fiber;
    await loader.apply(tree); assert.equal(loader.resolve('version').fiber,original);
    revision=2; broken=true;
    await assert.rejects(loader.apply(tree),error=>error.code==='RELOAD_FAILED');
    assert.equal(ctx.version,1); assert.equal(loader.resolve('keep').fiber,keep);
    broken=false; await loader.apply(tree);
    assert.equal(ctx.version,2); assert.equal(loader.resolve('keep').fiber,keep);
    const secondFiber=loader.resolve('version').fiber;
    revision=3; await loader.reload();
    assert.notEqual(loader.resolve('version').fiber,secondFiber); // Same factory, explicit new revision.
    assert.equal(loader.resolve('keep').fiber,keep);
    assert.deepEqual(audit,['tracked:start:keep']);
    assert.throws(()=>moduleHost.reset(),error=>error.code==='DOMAIN_RESTART_REQUIRED');
    await loader.dispose();
  } finally {await ctx.dispose();}
});

test('failed candidate child cleanup blocks restoration while retained siblings remain owned', async () => {
  const {ctx,audit,loader}=host();
  const tree=(value,extra)=>[{id:'group',group:true,entries:[provider(value,extra),tracked('keep')]}];
  try {
    await loader.apply(tree('old'));
    const parent=loader.resolve('group').fiber, keep=loader.resolve('group/keep').fiber;
    await assert.rejects(loader.apply(tree('candidate',{fail:true,cleanupFailure:true})),error=>error.code==='CLEANUP_BLOCKED');
    assert.equal(loader.state,'blocked');
    assert.equal(parent.uid!==null,true); assert.equal(keep.uid!==null,true);
    assert.equal(audit.filter(value=>value==='start:old').length,1);
    const failed=[...ctx.registry.values()].flatMap(runtime=>[...runtime.fibers]).find(fiber=>fiber.config?.cleanupFailure);
    failed.config.cleanupFailure=false;
    await loader.retryCleanup();
    assert.equal(loader.state,'empty');
    assert.equal(parent.uid,null);assert.equal(keep.uid,null);
    assert.equal(audit.filter(value=>value==='tracked:stop:keep').length,1);
    await loader.dispose();
  } finally {await ctx.dispose();}
});

test('retained consumer setup failure during replacement recovers its old committed dependencies',async()=>{
  const checkedConsumer={inject:['message'],apply:c=>{if(c.message.value==='candidate')throw new Error('cannot consume candidate');}};
  const moduleHost=new ModuleHost({loadModule:async url=>({plugin:url===fixture('consumer')?checkedConsumer:await import(url)})});
  const {ctx,loader}=host({moduleHost});
  try {
    await loader.apply([provider('old'),consumer]);
    const retained=loader.resolve('consumer').fiber;
    await assert.rejects(loader.update('provider',{config:{value:'candidate'}}),error=>error.code==='RELOAD_FAILED');
    assert.equal(loader.resolve('consumer').fiber,retained);
    assert.equal(retained.state,FiberState.ACTIVE);
    assert.equal(ctx.message.value,'old');
    await loader.dispose();
  } finally {await ctx.dispose();}
});

test('synchronous observer failure after candidate allocation retains cleanup ownership',async()=>{
  const {ctx,audit,loader}=host();
  let fail=true;
  try {
    await loader.apply([tracked('keep')]);
    const keep=loader.resolve('keep').fiber;
    const off=ctx.on('internal/plugin',fiber=>{
      if(fiber.config?.label!=='candidate' || fiber.uid===null)return;
      fiber.ctx.effect(()=>()=>{audit.push('observer cleanup');if(fail)throw new Error('observer inverse failed');});
      throw new Error('observer failed after allocation');
    });
    await assert.rejects(loader.apply([tracked('keep'),tracked('new','candidate')]),error=>error.code==='CLEANUP_BLOCKED');
    assert.equal(loader.state,'blocked');assert.equal(keep.uid!==null,true);
    fail=false;off();await loader.retryCleanup();
    assert.equal(loader.state,'empty');assert.equal(ctx.snapshot().plugins.length,1);
    await loader.dispose();
  } finally {await ctx.dispose();}
});


test('omitted and explicit null configuration remain distinct replacement recipes',async()=>{
  const observed=[];
  const plugin=(_ctx,config='default')=>{observed.push(config);};
  const {ctx,loader}=host({moduleHost:new ModuleHost({loadModule:()=>({plugin})})});
  try {
    await loader.apply([{id:'config',name:fixture('tracked')}]);
    const first=loader.resolve('config').fiber;
    await loader.update('config',{config:null});
    assert.notEqual(loader.resolve('config').fiber,first);
    assert.deepEqual(observed,['default',null]);
    await loader.dispose();
  } finally {await ctx.dispose();}
});
