// The same source runs against either pinned upstream or the selected native
// profile. Results preserve differences rather than normalizing their traces.
import {Context} from 'cordis';

export async function observeProfile(options = {}) {
  const root = new Context(options);
  const trace = [];
  const plugin = {
    name: 'profile-fixture',
    inject: ['profileService'],
    Config: {
      '~standard': {
        version: 1,
        vendor: 'cordis-verus-profile-fixture',
        validate(config) { trace.push(`schema:${config.value}`); return {value: config}; },
      },
    },
    apply(ctx, config) {
      trace.push(`setup:${config.value}:${ctx.profileService}`);
      return () => trace.push('cleanup');
    },
  };
  root.on('internal/config', (config, next) => { trace.push(`config:${config.value}`); return next(); });
  const application = root.plugin(plugin, {value: 1});
  trace.push('mounted');
  const fiber = await application;
  trace.push('pending');
  const update = fiber.update({value: 2});
  trace.push(update === undefined ? 'update:void' : 'update:awaitable');
  await update;
  const revoke = root.provide('profileService', 7);
  await fiber.await();
  trace.push('active');
  await revoke();
  await new Promise(resolve => setTimeout(resolve, 0));
  const restore = root.provide('profileService', 8);
  await fiber.await();
  trace.push('reactivated');
  await fiber.dispose();
  await restore();
  if (root.dispose) await root.dispose();
  return trace;
}

if (process.env.CORDIS_PROFILE_FIXTURE_RUN === '1') {
  process.stdout.write(JSON.stringify(await observeProfileSuite(process.env.CORDIS_PROFILE ?? 'cordis')) + '\n');
}

export async function observeFailureRecovery(options = {}) {
  const root=new Context(options), trace=[];
  let attempts=0;
  const revoke=root.provide('retryService',1);
  const application=root.inject(['retryService'],()=>{
    trace.push(`setup:${++attempts}`);
    if(attempts===1)throw new Error('first attempt fails');
    return()=>trace.push('cleanup');
  });
  try { await application; } catch { trace.push('initial:failed'); }
  await revoke();
  const restore=root.provide('retryService',2);
  try { await application.await(); trace.push('replacement:active'); }
  catch { trace.push('replacement:failed'); }
  await application.dispose();
  await restore();
  if(root.dispose)await root.dispose();
  return trace;
}

export async function observeReentrantPublication(options = {}) {
  const root=new Context(options), trace=[];
  let disposal;
  const plugin={name:'observed-pending',inject:['missing'],apply(){trace.push('unexpected:setup');}};
  root.on('internal/plugin',fiber=>{
    if(fiber.runtime?.name!==plugin.name || fiber.uid===null)return;
    trace.push('observer');
    fiber.ctx.effect(()=>{trace.push('effect');return async()=>{await Promise.resolve();trace.push('inverse');};});
    disposal=fiber.dispose();
    trace.push('dispose:requested');
  });
  const application=root.plugin(plugin);
  await disposal;
  trace.push('dispose:finished',application.uid===null,root.registry.has(plugin));
  if(root.dispose)await root.dispose();
  return trace;
}

export async function observeProfileSuite(profile) {
  const options={profile};
  const result={configuration:await observeProfile(options),failureRecovery:await observeFailureRecovery(options)};
  if(profile==='harness')result.reentrantPublication=await observeReentrantPublication(options);
  return result;
}
