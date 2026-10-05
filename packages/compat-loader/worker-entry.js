import '@cordis-verus/compat-cordis/register';
import { parentPort, workerData } from 'node:worker_threads';
import { join } from 'node:path';
import { Context } from '@cordis-verus/compat-cordis';
import { Loader, ModuleHost, LoaderError } from './index.js';
import { jsonValue } from './config.js';

const serialize = error => ({ name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code, details: error?.details });
const ctx = new Context();
const loader = new Loader(ctx, { moduleHost: new ModuleHost({ rootDirectory: workerData.directory }), allowPending: workerData.allowPending });
let closing = false;
let startupError;
const calls = new Set();
const startup = loader.loadFile(join(workerData.directory, workerData.entry)).then(
  () => parentPort.postMessage({ type: 'ready', diagnostics: loader.diagnostics() }),
  error => { startupError = error; parentPort.postMessage({ type: 'startup-error', error: serialize(error) }); },
);

parentPort.on('message', request => {
  const execute = async () => {
    if (request.method === 'shutdown') {
      closing = true;
      await startup;
      await Promise.allSettled([...calls]);
      await loader.dispose();
      await ctx.dispose();
      return { disposed: true };
    }
    if (closing) throw new LoaderError('DOMAIN_CLOSING', 'The domain is closing');
    await startup;
    if (startupError) throw startupError;
    if (request.method === 'diagnostics') return loader.diagnostics();
    if (request.method !== 'call') throw new LoaderError('WORKER_METHOD', 'Unsupported Worker request');
    const { service, member, args } = request;
    if (['constructor', '__proto__', 'prototype'].includes(member)) throw new LoaderError('SERVICE_METHOD', 'Reserved service method');
    const value = ctx.get(service);
    if (value === undefined || typeof value[member] !== 'function') throw new LoaderError('SERVICE_METHOD', `Missing service method ${service}.${member}`);
    return jsonValue(await Reflect.apply(value[member], value, args));
  };
  const task = execute();
  if (request.method !== 'shutdown') calls.add(task);
  task.then(result => {
    parentPort.postMessage({ type: 'reply', id: request.id, result });
    if (request.method === 'shutdown') parentPort.close();
  }, error => parentPort.postMessage({ type: 'reply', id: request.id, error: serialize(error) }))
    .finally(() => calls.delete(task));
});
