import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { Context, domainMutation } from '../../packages/compat-cordis/index.js';
import { loadRustModule } from '../../packages/compat-loader/rust-module.js';
import { createRustModulePlugin, beginRustModuleMigration } from '../../packages/compat-loader/rust-module-plugin.js';

const extension = process.platform === 'darwin' ? 'dylib' : process.platform === 'win32' ? 'dll' : 'so';
const artifact = version => {
  const path = fileURLToPath(new URL(`../../target/node-compat/dynamic-fixture-${version}.${extension}`, import.meta.url));
  return { path, sha256: createHash('sha256').update(readFileSync(path)).digest('hex') };
};
const revision = (version = 'v1', config = {}, state = 'migrate') => ({ ...artifact(version), plugins: [{ id: 'counter', factory: 'native-checkpoint', config, ...(state ? {state} : {}) }] });
const messages = e => [e?.message, ...(e?.errors ?? []).map(messages), ...(e?.cause ? [messages(e.cause)] : [])].join(' | ');
const inventory = ctx => ctx.fiber._domain.rust.command({op:'module_info'});
const read = ctx => ctx.nativeCheckpoint.read();
const turn = () => new Promise(resolve => setImmediate(resolve));
function environment(profile, gate) {
  const ctx = new Context({ profile }), trace = [];
  ctx.provide('jsHost', { record(event) { trace.push(event); return null; }, gate: gate ?? (() => null) });
  return {ctx,trace};
}
function zero(ctx) {
  const info = inventory(ctx);
  assert.equal(info.checkpoints.tokens, 0); assert.equal(info.checkpoints.bytes, 0);
  for (const module of info.modules) for (const count of Object.values(module.resources)) assert.equal(count, 0);
}
async function close(controller) {
  try { await controller.dispose(); }
  catch (error) { if (!/FixtureCleanupFailed/.test(messages(error))) throw error; await controller.retryCleanup(); await controller.dispose(); }
}
export function registerCheckpointTests(profile) {
  test(`checkpoint migrates logical data across native schema versions (${profile})`, async () => {
    const {ctx} = environment(profile);
    try {
      const controller = await loadRustModule(ctx, revision('v1', {initial:7})), driver = ctx.fiber._domain.driver, old = ctx.nativeCheckpoint;
      old.mutate(30);
      await controller.reload(artifact('v2'));
      assert.deepEqual(read(ctx), {version:'v2',value:37,restoredFrom:1});
      assert.equal(ctx.fiber._domain.driver,driver);
      assert.throws(()=>old.read(), /STALE|no longer admitted/);
      assert.equal(inventory(ctx).checkpoints.tokens,1);
      await controller.dispose(); zero(ctx);
    } finally { await ctx.dispose(); }
  });
  test(`checkpoint opt-in is required and mismatched schemas reject before retirement (${profile})`, async () => {
    const {ctx,trace} = environment(profile);
    try {
      const controller = await loadRustModule(ctx, revision()); ctx.nativeCheckpoint.mutate(12);
      const old = controller.snapshot().entries[0].fiberId;
      await assert.rejects(controller.reload(artifact('fail')), /schema/i);
      assert.equal(controller.snapshot().entries[0].fiberId, old); assert.equal(read(ctx).value,12);
      assert.equal(trace.filter(e=>e.phase==='checkpoint-cleanup').length,0);
      await controller.reconcile(revision('v2',{},undefined)); // default is migrate
      await controller.reconcile(revision('v1',{},null));
      assert.equal(read(ctx).value,0); assert.equal(read(ctx).restoredFrom,null);
      assert.equal(inventory(ctx).checkpoints.tokens,0);
      await controller.dispose(); zero(ctx);
    } finally { await ctx.dispose(); }
  });
  test(`capture follows actual in-flight completion and consumer cleanup writes (${profile})`, {timeout:15000}, async () => {
    const entered=Promise.withResolvers(), release=Promise.withResolvers();
    const {ctx,trace}=environment(profile, async()=>{entered.resolve();await release.promise;return null;});
    let operation,reload;
    try {
      const controller=await loadRustModule(ctx,revision());
      const consumer=await ctx.plugin({inject:['nativeCheckpoint'],apply(c){return ()=>c.nativeCheckpoint.mutate(10);}});
      operation=ctx.nativeCheckpoint.add({delta:5,gate:true});operation.catch(()=>{});
      await entered.promise;
      reload=controller.reload(artifact('v2'));reload.catch(()=>{});
      await turn(); await turn();
      assert(!trace.some(e=>e.phase==='checkpoint-setup'&&e.version==='v2'));
      release.resolve(); await Promise.allSettled([operation]); await reload;
      assert.equal(read(ctx).value,15);
      assert.equal(trace.find(e=>e.phase==='checkpoint-cleanup'&&e.version==='v1').value,15);
      await consumer.dispose(); await controller.dispose(); zero(ctx);
    } finally {release.resolve();await Promise.allSettled([operation,reload]);await ctx.dispose();}
  });
  for (const flag of ['failCaptureOnce','failCleanupOnce']) test(`checkpoint ${flag} retains old state until explicit cleanup retry (${profile})`, async () => {
    const {ctx,trace}=environment(profile); let controller;
    try {
      controller=await loadRustModule(ctx,revision('v1',{[flag]:true}));ctx.nativeCheckpoint.mutate(21);
      await assert.rejects(controller.reconcile(revision('v2')),e=>e.code==='NATIVE_MODULE_CLEANUP_BLOCKED');
      assert(!trace.some(e=>e.phase==='checkpoint-setup'&&e.version==='v2'));
      const token=[...controller._journal.tokens][0];
      const first=ctx.fiber._domain.rust.command({op:'checkpoint_read',token});
      assert.equal(first.state,flag==='failCaptureOnce'?'failed':'captured'); assert.equal(first.retired,false);
      await controller.retryCleanup();
      const captured=ctx.fiber._domain.rust.command({op:'checkpoint_read',token});
      assert.equal(captured.state,'captured');assert.equal(captured.retired,true);assert.equal(captured.value.data.value,21);
      await controller.reconcile(revision('v2'));
      assert.equal(read(ctx).value,21);assert.equal(read(ctx).restoredFrom,1);
      assert.equal(trace.filter(e=>e.phase==='checkpoint-setup'&&e.version==='v1').length,1);
      await close(controller);zero(ctx);
    } finally {if(controller)await close(controller);await ctx.dispose();}
  });
  for (const flag of ['failRestore','failSetup']) test(`candidate ${flag} restores the same pre-update checkpoint (${profile})`, async () => {
    const {ctx,trace}=environment(profile);
    try {
      const controller=await loadRustModule(ctx,revision());ctx.nativeCheckpoint.mutate(33);
      await assert.rejects(controller.reconcile(revision('v2',{[flag]:true})),e=>e.code==='NATIVE_MODULE_RELOAD_FAILED'&&e.details.restored);
      assert.deepEqual(read(ctx),{version:'v1',value:33,restoredFrom:1});
      assert(trace.some(e=>e.phase==='checkpoint-cleanup'&&e.version==='v2'),'Failed new instance actually cleaned up');
      if(flag==='failRestore')assert(!trace.some(e=>e.phase==='checkpoint-setup'&&e.version==='v2'),'Restore precedes setup');
      assert.equal(inventory(ctx).checkpoints.tokens,1);
      await controller.dispose();zero(ctx);
    } finally {await ctx.dispose();}
  });
  test(`candidate cleanup failure preserves rollback checkpoints across recovery (${profile})`, async () => {
    const {ctx}=environment(profile);let controller;
    try {
      controller=await loadRustModule(ctx,revision());ctx.nativeCheckpoint.mutate(44);
      await assert.rejects(controller.reconcile(revision('v2',{failSetup:true,failCleanupOnce:true})),e=>e.code==='NATIVE_MODULE_RECOVERY_BLOCKED');
      assert.equal(inventory(ctx).checkpoints.tokens,1);
      await controller.retryCleanup();
      await controller.reconcile(revision('v2'));
      assert.equal(read(ctx).value,44);await controller.dispose();zero(ctx);
    } finally {if(controller)await close(controller);await ctx.dispose();}
  });
  test(`ordinary Loader restarts transfer state and recycle episode receipts (${profile})`, async () => {
    const {ctx}=environment(profile);
    try {
      const plugin=createRustModulePlugin(ctx), fiber=await ctx.plugin(plugin,revision());ctx.nativeCheckpoint.mutate(19);
      for(let index=0;index<4;index++) {
        await domainMutation(ctx,steps=>steps.restart(fiber));
        assert.equal(read(ctx).value,19);assert.equal(inventory(ctx).checkpoints.tokens,1);
      }
      await assert.rejects(domainMutation(ctx,steps=>steps.update(fiber,revision('fail'),true)),/schema/i);
      assert.equal(read(ctx).value,19);
      await domainMutation(ctx,steps=>steps.update(fiber,revision('v2'),true));
      assert.equal(read(ctx).restoredFrom,1);assert.equal(read(ctx).value,19);
      await fiber.dispose();zero(ctx);
    } finally {await ctx.dispose();}
  });
  test(`host migration transaction pins state through consumer acceptance and rollback (${profile})`, async () => {
    const {ctx}=environment(profile);
    try {
      const fiber=await ctx.plugin(createRustModulePlugin(ctx),revision());ctx.nativeCheckpoint.mutate(8);
      await domainMutation(ctx,async steps=>{
        const migration=beginRustModuleMigration(ctx,fiber);
        try {
          await steps.update(fiber,revision('v2'),true);
          ctx.nativeCheckpoint.mutate(900);
          assert.equal(inventory(ctx).checkpoints.tokens,2);
          migration.rollback();
          await steps.update(fiber,revision('v1'),true);
          assert.deepEqual(read(ctx),{version:'v1',value:8,restoredFrom:1});
          migration.commit();
        } finally {migration.release();}
      });
      assert.equal(inventory(ctx).checkpoints.tokens,1);
      await domainMutation(ctx,async steps=>{
        const migration=beginRustModuleMigration(ctx,fiber);
        try {await steps.update(fiber,revision('v2'),true);migration.commit();}
        finally {migration.release();}
      });
      assert.equal(read(ctx).value,8);assert.equal(inventory(ctx).checkpoints.tokens,1);
      await fiber.dispose();zero(ctx);
    } finally {await ctx.dispose();}
  });
  test(`ordinary failed setup retains the old checkpoint for explicit restoration (${profile})`, async () => {
    const {ctx}=environment(profile);
    try {
      const fiber=await ctx.plugin(createRustModulePlugin(ctx),revision());ctx.nativeCheckpoint.mutate(51);
      await assert.rejects(domainMutation(ctx,steps=>steps.update(fiber,revision('v2',{failSetup:true}),true)),/CandidateSetupFailed/);
      await domainMutation(ctx,steps=>steps.update(fiber,revision(),true));
      assert.equal(read(ctx).value,51);await fiber.dispose();zero(ctx);
    } finally {await ctx.dispose();}
  });
  test(`failed restoration retains its source identity until a later successful recovery (${profile})`, async () => {
    const {ctx}=environment(profile);let oldSetups=0;
    ctx.jsHost.record=event=>{if(event.phase==='checkpoint-setup'&&event.version==='v1'&&++oldSetups===2)throw new Error('OldRestoreSetupFailed');return null;};
    try {
      const fiber=await ctx.plugin(createRustModulePlugin(ctx),revision());ctx.nativeCheckpoint.mutate(61);
      await assert.rejects(domainMutation(ctx,async steps=>{
        const migration=beginRustModuleMigration(ctx,fiber);
        try {
          await steps.update(fiber,revision('v2'),true);ctx.nativeCheckpoint.mutate(900);
          migration.rollback();
          await assert.rejects(steps.update(fiber,revision(),true),/OldRestoreSetupFailed/);
        } finally {migration.release();}
      }), /OldRestoreSetupFailed/);
      await domainMutation(ctx,async steps=>{
        const migration=beginRustModuleMigration(ctx,fiber);
        try {migration.rollback();await steps.update(fiber,revision(),true);migration.commit();}
        finally {migration.release();}
      });
      assert.equal(read(ctx).value,61);assert.equal(inventory(ctx).checkpoints.tokens,1);
      ctx.nativeCheckpoint.mutate(17);
      await domainMutation(ctx,steps=>steps.restart(fiber));
      assert.equal(read(ctx).value,78,'Recovered state must replace the older recovery checkpoint');
      await fiber.dispose();zero(ctx);
    } finally {await ctx.dispose();}
  });
  test(`consumer restoration failure retains original data after the native provider is Active (${profile})`, async () => {
    const {ctx}=environment(profile);
    try {
      const fiber=await ctx.plugin(createRustModulePlugin(ctx),revision());ctx.nativeCheckpoint.mutate(5);
      await assert.rejects(domainMutation(ctx,async steps=>{
        const migration=beginRustModuleMigration(ctx,fiber);
        try {
          await steps.update(fiber,revision('v2'),true);ctx.nativeCheckpoint.mutate(900);
          migration.rollback();await steps.update(fiber,revision(),true);
          ctx.nativeCheckpoint.mutate(7);
          throw new Error('RequiredConsumerRestoreFailed');
        } finally {migration.release();}
      }), /RequiredConsumerRestoreFailed/);
      assert.equal(read(ctx).value,12);assert.equal(inventory(ctx).checkpoints.tokens,2);
      await domainMutation(ctx,async steps=>{
        const migration=beginRustModuleMigration(ctx,fiber);
        try {await steps.update(fiber,revision('v2'),true);assert.equal(read(ctx).value,5);migration.commit();}
        finally {migration.release();}
      });
      assert.equal(inventory(ctx).checkpoints.tokens,1);await fiber.dispose();zero(ctx);
    } finally {await ctx.dispose();}
  });
  test(`a later failed attempt cannot commit an earlier intermediate restoration (${profile})`, async () => {
    const {ctx}=environment(profile);
    try {
      const fiber=await ctx.plugin(createRustModulePlugin(ctx),revision());ctx.nativeCheckpoint.mutate(5);
      await assert.rejects(domainMutation(ctx,async steps=>{
        const migration=beginRustModuleMigration(ctx,fiber);
        try {
          await steps.update(fiber,revision(),true);ctx.nativeCheckpoint.mutate(7);
          await assert.rejects(steps.update(fiber,revision('v2',{failSetup:true}),true),/CandidateSetupFailed/);
        } finally {migration.release();}
      }), /CandidateSetupFailed/);
      await domainMutation(ctx,steps=>steps.update(fiber,revision(),true));
      assert.equal(read(ctx).value,5,'An uncommitted transaction keeps its original state');
      ctx.nativeCheckpoint.mutate(9);
      await domainMutation(ctx,steps=>steps.restart(fiber));
      assert.equal(read(ctx).value,14);await fiber.dispose();zero(ctx);
    } finally {await ctx.dispose();}
  });
  test(`checkpoint transaction rejects managed reentry and closes after acceptance (${profile})`, async () => {
    const {ctx}=environment(profile);
    try {
      const fiber=await ctx.plugin(createRustModulePlugin(ctx),revision());
      await ctx.plugin(()=>{assert.throws(()=>beginRustModuleMigration(ctx,fiber),e=>e.code==='REENTRANT_MUTATION');});
      let transaction;
      await domainMutation(ctx,async()=>{
        transaction=beginRustModuleMigration(ctx,fiber);
        assert.throws(()=>beginRustModuleMigration(ctx,fiber),e=>e.code==='NATIVE_MODULE_MIGRATION_BUSY');
        await ctx.plugin(()=>{assert.throws(()=>transaction.rollback(),e=>e.code==='REENTRANT_MUTATION');});
        transaction.commit();transaction.release();
      });
      assert.throws(()=>transaction.rollback(),e=>e.code==='NATIVE_MODULE_MIGRATION_CLOSED');
      await assert.rejects(domainMutation(ctx,()=>beginRustModuleMigration(ctx,fiber),{recovery:true}),e=>e.code==='CLEANUP_BLOCKED');
      await fiber.dispose();zero(ctx);
    } finally {await ctx.dispose();}
  });
}
