// Identical plugin code is bundled for every backend. Only the `cordis` import changes.
import { Context, Service } from 'cordis';
import { createWriteStream } from 'node:fs';
import { readFile } from 'node:fs/promises';
import path from 'node:path';

export async function disposalOrder(output) {
  const trace = [], writes = [], errors = [];
  const filename = path.join(output, 'logger.txt');
  let provider, consumer, closed;
  class CaseLogger extends Service {
    constructor(ctx) { super(ctx, 'caseLogger'); }
    *[Service.init]() {
      this.handle = createWriteStream(filename);
      this.handle.on('error', error => { errors.push(error.code ?? error.message); });
      closed = new Promise(resolve => this.handle.once('close', () => { trace.push('provider:closed'); resolve(); }));
      trace.push('provider:opened');
      yield () => { trace.push('provider:close-requested'); this.handle.close(); };
    }
    log(message) {
      trace.push(`write:${message}:requested`);
      writes.push(new Promise(resolve => this.handle.write(`${message}\n`, error => {
        trace.push(`write:${message}:${error ? 'failed' : 'ok'}`);
        resolve({ message, ok: !error, error: error?.code ?? null });
      })));
    }
  }
  const root = new Context();
  const parent = await root.plugin(ctx => {
    provider = ctx.plugin(CaseLogger);
    consumer = ctx.inject(['caseLogger'], ctx => {
      ctx.effect(() => {
        ctx.caseLogger.log('start');
        return async () => {
          trace.push('consumer:cleanup-started');
          await new Promise(resolve => setTimeout(resolve, 30));
          ctx.caseLogger.log('end');
          trace.push('consumer:cleanup-returned');
        };
      });
    });
  });
  await Promise.all([provider, consumer]);
  // Join the initial write before disposing; the final write remains in cleanup.
  await Promise.all(writes);
  trace.push('parent:dispose-requested');
  let disposal = { status: 'fulfilled' };
  try { await parent.dispose(); }
  catch (error) { disposal = { status: 'rejected', message: error.message }; }
  trace.push(`parent:dispose-${disposal.status}`);
  const writeResults = await Promise.all(writes);
  await closed;
  const contents = await readFile(filename, 'utf8');
  const closeIndex = trace.indexOf('provider:close-requested');
  const endIndex = trace.indexOf('write:end:requested');
  const result = {
    trace, disposal, writes: writeResults, streamErrors: errors, contents,
    finalWriteBeforeProviderClose: endIndex >= 0 && closeIndex > endIndex,
    finalWriteSucceeded: writeResults.some(write => write.message === 'end' && write.ok),
    bothLinesPersisted: contents === 'start\nend\n',
  };
  // Root cleanup is outside the reported parent-disposal workload.
  await root.fiber.dispose();
  return result;
}

export async function cleanupFailure() {
  const root = new Context(), trace = [];
  let rejectCleanup = true, attempts = 0;
  const fiber = await root.plugin(ctx => {
    ctx.effect(() => () => {
      trace.push(`cleanup:attempt-${++attempts}`);
      if (rejectCleanup) throw new Error('case cleanup must retry');
      trace.push('cleanup:completed');
    });
  });
  let firstDisposal;
  try { await fiber.dispose(); firstDisposal = 'fulfilled'; }
  catch { firstDisposal = 'rejected'; }
  const attemptsAfterFirstDisposal = attempts;
  const explicitRetryAvailable = typeof fiber.retryCleanup === 'function';
  let retry = 'unsupported';
  if (explicitRetryAvailable) {
    rejectCleanup = false;
    try { await fiber.retryCleanup(); retry = 'fulfilled'; }
    catch { retry = 'rejected'; }
  }
  const result = { trace, firstDisposal, attemptsAfterFirstDisposal, explicitRetryAvailable, retry, attempts };
  try { await root.fiber.dispose(); } catch { /* Root error is separate from the observed plugin call. */ }
  return result;
}

const result = {
  disposalOrder: await disposalOrder(process.env.CORDIS_CASE_OUTPUT),
  cleanupFailure: await cleanupFailure(),
};
process.stdout.write(`${JSON.stringify(result)}\n`);
