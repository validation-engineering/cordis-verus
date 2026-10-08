import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, writeFile, readFile, rm, copyFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { inspect } from 'node:util';
import { waitForMarker, waitForCallMarker, observeOperation, completedValues } from './process-test-support.mjs';
import { ProcessDomain } from '../../packages/compat-loader/process.js';
import { WorkerDomain } from '../../packages/compat-loader/worker.js';
import { releaseLaunch } from '../../packages/compat-loader/artifact.js';

async function fixture(options = {}) {
  const directory = await mkdtemp(join(tmpdir(), 'cordis-process-source-'));
  const external = await mkdtemp(join(tmpdir(), 'cordis-process-state-'));
  const trace = join(external, 'trace');
  await writeFile(trace, '');
  await writeFile(join(directory, 'plugin.mjs'), `
import { Service } from 'cordis';
import { appendFileSync, existsSync, readFileSync, writeFileSync } from 'node:fs';
import { label } from './dependency.mjs';
export default class Probe extends Service {
 constructor(ctx, config) {
  super(ctx, 'probe'); this.config = config;
  appendFileSync(config.trace, 'start:' + label + ':' + process.pid + '\\n');
  if (config.leak) setInterval(() => {}, 1000);
  ctx.effect(() => () => {
   appendFileSync(config.trace, 'stop:' + label + ':' + process.pid + '\\n');
   if (config.exitZero) process.exit(0);
   if (config.cleanupFailure) throw new Error('cleanup failed');
  });
  if (config.failOnSecond) { if (existsSync(config.failOnSecond)) throw new Error('old restoration failed'); writeFileSync(config.failOnSecond, 'started'); }
  if (config.fail) throw new Error('candidate failed');
 }
 info() { return { label, pid: process.pid, cwd: process.cwd(), env: process.env.PROCESS_FIXTURE_ENV ?? null }; }
 echo(value) { return value; }
 crash() { process.exit(23); }
 malformed() {
  process.send(null); process.send('noise'); process.send([]);
  process.send({type:'startup-error'}); process.send({type:'startup-error',error:null});
  let error={message:'leaf'}; for(let i=0;i<1000;i++) error={message:'nested',cause:error};
  process.send({type:'startup-error',error});
  return 'alive';
 }
 hang() { return new Promise(() => {}); }
 async wait() {
  writeFileSync(this.config.waiting, 'ready');
  const deadline = Date.now() + 5000;
  let previous;
  for (;;) {
   try {
    const value = readFileSync(this.config.release, 'utf8');
    if (value !== previous) { writeFileSync(this.config.observedRelease, value); previous = value; }
    if (value === 'go') break;
   }
   catch (error) { if (error.code !== 'ENOENT') throw error; }
   if (Date.now() >= deadline) throw new Error('Process fixture release was not received');
   await new Promise(resolve => setTimeout(resolve, 10));
  }
  appendFileSync(this.config.trace, 'call:done\\n');
  return 'done';
 }
}
`);
  const write = async (label, config = {}) => {
    await writeFile(join(directory, 'dependency.mjs'), `export const label = ${JSON.stringify(label)};`);
    await writeFile(join(directory, 'cordis.json'), JSON.stringify([{ id: 'probe', name: './plugin.mjs', config: { trace, external, waiting: join(external, 'waiting'), observedRelease: join(external, 'observed-release'), release: join(external, 'release'), ...config } }]));
  };
  await write('old');
  const domain = new ProcessDomain({ timeout: 5000, stdio: 'ignore', ...options });
  return { directory, external, trace, domain, write,
    lines: async () => (await readFile(trace, 'utf8')).trim().split('\n'),
    cleanup: async () => { if (domain.state !== 'closed') await domain.abandon(); await rm(directory, {recursive:true, force:true}); await rm(external, {recursive:true, force:true}); },
  };
}

async function finishProcessFixture(t, p, operations, failure) {
  // Observed operations always resolve to result objects, so settling them
  // cannot replace an earlier assertion. Attempt every remaining cleanup step.
  const cleanupErrors = [];
  try { await writeFile(join(p.external, 'release'), 'go'); } catch (error) { cleanupErrors.push(error); }
  await Promise.all(operations);
  try { await p.cleanup(); } catch (error) { cleanupErrors.push(error); }
  if (cleanupErrors.length) {
    if (failure) t.diagnostic(`Cleanup also failed: ${inspect(cleanupErrors, { depth: 8 })}`);
    else throw new AggregateError(cleanupErrors, 'Process test cleanup failed', { cause: cleanupErrors[0] });
  }
}

test('ProcessDomain replaces real OS processes and refreshes captured transitive modules', async () => {
  const p = await fixture({ env: { PROCESS_FIXTURE_ENV: 'inherited-override' } });
  try {
    const first = await p.domain.load(p.directory), pid = p.domain.pid;
    assert.notEqual(pid, process.pid);
    assert.equal(first.plan.strategy, 'process-restart');
    assert.equal((await p.domain.call('probe', 'info')).pid, pid);
    assert.equal((await p.domain.call('probe', 'info')).env, 'inherited-override');
    assert.notEqual((await p.domain.call('probe', 'info')).cwd, p.directory);
    await p.write('new');
    const plan = await p.domain.planReload();
    assert.deepEqual(plan.affectedModules, ['dependency.mjs', 'plugin.mjs']);
    await p.domain.reload();
    assert.notEqual(p.domain.pid, pid);
    assert.equal((await p.domain.call('probe', 'info')).label, 'new');
    await p.domain.dispose();
    assert.equal(p.domain.pid, undefined);
    assert.equal((await p.lines()).length, 4);
  } finally { await p.cleanup(); }
});

test('ProcessDomain loads a real application native addon that WorkerDomain rejects', async () => {
  const p = await fixture();
  const worker = new WorkerDomain();
  try {
    await copyFile(new URL('../../packages/compat-cordis/native/cordis.node', import.meta.url), join(p.directory, 'application.node'));
    await writeFile(join(p.directory, 'dependency.mjs'), "import {createRequire} from 'node:module'; const addon = createRequire(import.meta.url)('./application.node'); export const label = JSON.parse(addon.bindingInfo()).package;");
    await assert.rejects(worker.load(p.directory), {code:'PROCESS_RESTART_REQUIRED'});
    const result = await p.domain.load(p.directory);
    assert.deepEqual(result.plan.nativeAddons, ['application.node']);
    assert.equal((await p.domain.call('probe', 'info')).label, 'cordis-node');
    assert.ok((await p.domain.moduleGraph()).modules.some(node => node.path === 'application.node'));
    const old = p.domain.pid;
    await p.domain.reload();
    assert.notEqual(p.domain.pid, old);
  } finally { await worker.dispose(); await p.cleanup(); }
});

test('failed process candidate confirms cleanup and restores captured old bytes in another PID', async () => {
  const p = await fixture();
  try {
    const first = await p.domain.load(p.directory), pid = p.domain.pid;
    await p.write('broken', { fail: true });
    await assert.rejects(p.domain.reload(), error => error.code === 'RELOAD_FAILED' && error.details.restored);
    assert.equal(p.domain.lastRecovery.digest, first.digest);
    assert.notEqual(p.domain.pid, pid);
    assert.equal((await p.domain.call('probe', 'info')).label, 'old');
    assert.deepEqual((await p.lines()).map(line => line.split(':').slice(0,2).join(':')), ['start:old','stop:old','start:broken','stop:broken','start:old']);
  } finally { await p.cleanup(); }
});

test('process shutdown drains already accepted JSON calls before lifecycle cleanup', async t => {
  let output = '';
  const p = await fixture({ onOutput: chunk => { output += `[${chunk.stream}] ${chunk.data}`; } });
  const operations = [];
  let failure;
  try {
    await p.domain.load(p.directory);
    operations.push(observeOperation('accepted call', p.domain.call('probe', 'wait')));
    await waitForCallMarker(join(p.external, 'waiting'), operations[0]);
    let closed = false;
    operations.push(observeOperation('domain cleanup', p.domain.dispose().then(() => { closed = true; })));
    await assert.rejects(p.domain.call('probe', 'info'), {code:'DOMAIN_NOT_READY'});
    assert.equal(closed, false);
    await writeFile(join(p.external, 'release'), 'go');
    const [value] = await completedValues(operations);
    assert.equal(value, 'done');
    assert.match((await p.lines()).at(-2), /^call:done$/);
    assert.match((await p.lines()).at(-1), /^stop:old:/);
  } catch (error) {
    failure = error;
    t.diagnostic(inspect(error, { depth: 8 }));
    const trace = await readFile(p.trace, 'utf8').catch(error => `Trace unavailable: ${inspect(error)}`);
    t.diagnostic(`Child output:\n${output}\nTrace:\n${trace}`);
    throw error;
  } finally { await finishProcessFixture(t, p, operations, failure); }
});

test('process release persists when it arrives before the call without a later notification', async t => {
  const p = await fixture();
  const operations = [];
  let failure;
  try {
    await p.domain.load(p.directory);
    await writeFile(join(p.external, 'release'), 'go');
    // No file writes or output callbacks follow admission. An edge-triggered
    // watcher would miss this release, whereas the child must observe its state.
    operations.push(observeOperation('pre-released call', p.domain.call('probe', 'wait')));
    assert.deepEqual(await completedValues(operations), ['done']);
    assert.match((await p.lines()).at(-1), /^call:done$/);
    await p.domain.dispose();
  } catch (error) { failure = error; throw error; }
  finally { await finishProcessFixture(t, p, operations, failure); }
});

test('process release gate observes incomplete contents without releasing the accepted call', async t => {
  const p = await fixture();
  const operations = [];
  let failure;
  try {
    await p.domain.load(p.directory);
    await writeFile(join(p.external, 'release'), 'g');
    let settled = false;
    const call = observeOperation('partially released call', p.domain.call('probe', 'wait'));
    operations.push(call);
    call.then(() => { settled = true; });
    await waitForMarker(join(p.external, 'observed-release'), 'g');
    assert.equal(settled, false);
    assert.equal((await p.lines()).includes('call:done'), false);
    await writeFile(join(p.external, 'release'), 'go');
    assert.deepEqual(await completedValues([call]), ['done']);
    await p.domain.dispose();
  } catch (error) { failure = error; throw error; }
  finally { await finishProcessFixture(t, p, operations, failure); }
});

test('process readiness polling preserves an early call failure instead of hiding it behind a timeout', async () => {
  const directory = await mkdtemp(join(tmpdir(), 'cordis-process-early-error-'));
  const failure = new Error('injected admission failure', { cause: new Error('original cause') });
  try {
    const observed = observeOperation('accepted call', Promise.reject(failure));
    await assert.rejects(waitForCallMarker(join(directory, 'missing-ready'), observed), error => error === failure);
  } finally { await rm(directory, {recursive:true, force:true}); }
});

test('process test operation collection preserves early peer rejections and their causes', async t => {
  for (const first of ['accepted call', 'domain cleanup']) {
    await t.test(`${first} rejects before its peer settles`, async () => {
      const call = Promise.withResolvers(), close = Promise.withResolvers();
      const underlying = new Error('injected original failure');
      const failure = Object.assign(new Error('injected peer failure', { cause: underlying }), { code: 'INJECTED_FAILURE' });
      const observed = [observeOperation('accepted call', call.promise), observeOperation('domain cleanup', close.promise)];
      const [failed, pending] = first === 'accepted call' ? [call, close] : [close, call];
      failed.reject(failure);
      // Cross a whole event-loop turn before awaiting either result: missing
      // eager rejection handling would be reported by node:test here.
      await new Promise(resolve => setImmediate(resolve));
      pending.resolve('done');
      await assert.rejects(completedValues(observed), error => {
        assert.ok(error instanceof AggregateError);
        assert.equal(error.errors[0], failure);
        assert.equal(error.cause, failure);
        assert.equal(error.cause.cause, underlying);
        assert.match(error.message, new RegExp(first));
        assert.match(error.message, /injected original failure/);
        return true;
      });
    });
  }
});

test('failed candidate cleanup blocks replacement and explicit abandon is not normal cleanup', async () => {
  const p = await fixture();
  try {
    await p.domain.load(p.directory);
    await p.write('broken', {fail:true,cleanupFailure:true});
    await assert.rejects(p.domain.reload(), {code:'CLEANUP_BLOCKED'});
    assert.equal(p.domain.state,'blocked');
    await assert.rejects(p.domain.reload(), {code:'DOMAIN_BLOCKED'});
    assert.equal((await p.lines()).filter(line=>line.startsWith('start:old:')).length,1);
    assert.deepEqual(await p.domain.abandon(), {abandoned:true,cleanupConfirmed:false});
  } finally { await p.cleanup(); }
});

test('abnormal exit and exit zero without cleanup acknowledgement remain abandonment', async () => {
  for (const exitZero of [false,true]) {
    const p = await fixture();
    try {
      await p.write('crash',{exitZero}); await p.domain.load(p.directory);
      await assert.rejects(exitZero ? p.domain.dispose() : p.domain.call('probe','crash'), {code:'DOMAIN_ABANDONED'});
      assert.equal(p.domain.state,'abandoned');
      await assert.rejects(p.domain.reload(), error=>['DOMAIN_CLOSED','DOMAIN_BLOCKED'].includes(error.code));
    } finally { await p.cleanup(); }
  }
});

test('unsettled accepted call times out, blocks new work, and needs explicit process abandonment', async () => {
  const p = await fixture({timeout:1000});
  try {
    await p.domain.load(p.directory);
    await assert.rejects(p.domain.call('probe','hang'), {code:'DOMAIN_TIMEOUT'});
    assert.equal(p.domain.state,'blocked');
    await assert.rejects(p.domain.reload(), {code:'DOMAIN_BLOCKED'});
    await assert.rejects(p.domain.dispose(), {code:'CLEANUP_BLOCKED'});
    assert.deepEqual(await p.domain.abandon(), {abandoned:true,cleanupConfirmed:false});
  } finally { await p.cleanup(); }
});

test('cleanup acknowledgement without process exit does not activate a replacement', async () => {
  const p = await fixture({timeout:1000});
  try {
    await p.write('leaked',{leak:true}); await p.domain.load(p.directory);
    await p.write('new');
    await assert.rejects(p.domain.reload(), {code:'CLEANUP_BLOCKED'});
    assert.equal(p.domain.state,'blocked');
    assert.equal((await p.lines()).some(line=>line.startsWith('start:new:')),false);
    await p.domain.abandon();
  } finally { await p.cleanup(); }
});

test('startup that never settles blocks cleanup and requires explicit abandonment', async () => {
  const p = await fixture({timeout:1000});
  try {
    await writeFile(join(p.directory,'dependency.mjs'), "await new Promise(() => {}); export const label='never';");
    await assert.rejects(p.domain.load(p.directory), {code:'CLEANUP_BLOCKED'});
    assert.equal(p.domain.state,'blocked');
    await p.domain.abandon();
  } finally { await p.cleanup(); }
});

test('process IPC preserves JSON boundaries and never deletes application source or persistent cwd', async () => {
  const p = await fixture();
  try {
    await assert.rejects(releaseLaunch(p.directory), {code:'ARTIFACT_CLEANUP_TARGET'});
    await p.domain.load(p.directory);
    const value={text:'ok',values:[true,null,4]};
    assert.deepEqual(await p.domain.call('probe','echo',value),value);
    await assert.rejects(p.domain.call('probe','echo',()=>{}), {code:'INVALID_CONFIG'});
    await assert.rejects(p.domain.call('probe','constructor'), {code:'SERVICE_METHOD'});
    await p.domain.dispose();
    assert.ok((await readFile(join(p.directory,'plugin.mjs'),'utf8')).includes('class Probe'));
    assert.ok((await readFile(p.trace,'utf8')).includes('stop:old:'));
  } finally { await p.cleanup(); }
});

test('trusted host exposes cleanup before ready and pins its external source across reloads', async () => {
  const p=await fixture();
  const hostModule=join(p.external,'host.mjs');
  await writeFile(hostModule, `import {readFile,appendFile} from 'node:fs/promises'; import {join} from 'node:path';
export function createHost({directory}) {
 let value;
 const ready=readFile(join(directory,'host.json'),'utf8').then(JSON.parse).then(config=>{value=config; if(config.fail)throw new Error('host failed');});
 return {ready,call:()=>({value:value.value,pid:process.pid,cwd:process.cwd()}),diagnostics:()=>({pid:process.pid}),close:()=>appendFile(${JSON.stringify(p.trace)},'host:closed\\n')};
}`);
  const domain=new ProcessDomain({hostModule,cwd:p.external,timeout:5000,stdio:'ignore'});
  try {
    await writeFile(join(p.directory,'host.json'),JSON.stringify({value:'first'}));
    const loaded=await domain.load(p.directory);
    assert.equal(loaded.plan.host.sha256,domain.hostProvenance.sha256);
    assert.equal((await domain.call('host','info')).cwd,await import('node:fs/promises').then(fs=>fs.realpath(p.external)));
    await writeFile(join(p.directory,'host.json'),JSON.stringify({value:'bad',fail:true}));
    await assert.rejects(domain.reload(),{code:'RELOAD_FAILED'});
    assert.equal((await domain.call('host','info')).value,'first');
    const pid=domain.pid;
    await writeFile(hostModule,'export function createHost() {throw new Error("changed")}');
    await assert.rejects(domain.reload(),{code:'HOST_CHANGED'});
    assert.equal(domain.pid,pid);
    await domain.dispose();
    assert.equal((await p.lines()).filter(line=>line==='host:closed').length,3);
  } finally {if(domain.state!=='closed')await domain.abandon();await p.cleanup();}
});

test('malformed IPC messages cannot crash the supervising process', async () => {
  const p=await fixture();
  try {
    await p.domain.load(p.directory);
    assert.equal(await p.domain.call('probe','malformed'),'alive');
    assert.equal((await p.domain.call('probe','info')).label,'old');
    p.domain._current.client.process.send(null);
    assert.equal(await p.domain.call('probe','echo',42),42);
  } finally {await p.cleanup();}
});

test('a failed spawn with no PID can be abandoned and only its temporary launch is released', async () => {
  const p=await fixture();
  const cwd=await mkdtemp(join(p.external,'cwd-'));
  const domain=new ProcessDomain({cwd,timeout:300,stdio:'ignore'});
  try {
    assert.throws(()=>new ProcessDomain({cwd:p.trace}),/directory/);
    await rm(cwd,{recursive:true,force:true});
    await assert.rejects(domain.load(p.directory),{code:'DOMAIN_ABANDONED'});
    assert.equal(domain.state,'abandoned');
    assert.deepEqual(await domain.abandon(),{abandoned:true,cleanupConfirmed:false});
    assert.ok((await readFile(join(p.directory,'plugin.mjs'),'utf8')).includes('class Probe'));
  } finally {await domain.abandon();await p.cleanup();}
});

test('old cleanup failure keeps its process blocked and candidate code never starts', async () => {
  const p=await fixture();
  try {
    await p.write('old',{cleanupFailure:true}); await p.domain.load(p.directory);
    const pid=p.domain.pid;
    await p.write('new');
    await assert.rejects(p.domain.reload(),{code:'CLEANUP_BLOCKED'});
    assert.equal(p.domain.state,'blocked');assert.equal(p.domain.pid,pid);
    assert.equal((await p.lines()).some(line=>line.startsWith('start:new:')),false);
  } finally {await p.cleanup();}
});

test('failed old-artifact restoration is reported distinctly after candidate cleanup', async () => {
  const p=await fixture();
  try {
    await p.write('old',{failOnSecond:join(p.external,'once')}); await p.domain.load(p.directory);
    await p.write('candidate',{fail:true});
    await assert.rejects(p.domain.reload(),{code:'RESTORE_FAILED'});
    assert.equal(p.domain.state,'empty');
    assert.equal(p.domain.lastRecovery,undefined);
    assert.equal((await p.lines()).filter(line=>line.startsWith('stop:')).length,3);
    await p.domain.dispose();
  } finally {await p.cleanup();}
});

test('trusted-host construction failure cannot pretend partial startup was cleanly drained', async () => {
  const p=await fixture();
  const hostModule=join(p.external,'broken-host.mjs');
  await writeFile(hostModule,'export function createHost(){setInterval(()=>{},1000);throw new Error("partial setup")};');
  const domain=new ProcessDomain({hostModule,timeout:500,stdio:'ignore'});
  try {
    await assert.rejects(domain.load(p.directory),{code:'CLEANUP_BLOCKED'});
    assert.equal(domain.state,'blocked');
    assert.deepEqual(await domain.abandon(),{abandoned:true,cleanupConfirmed:false});
  } finally {await domain.abandon();await p.cleanup();}
});
