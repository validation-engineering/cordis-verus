import { join } from 'node:path';
import { readFile } from 'node:fs/promises';
import { createHash } from 'node:crypto';
import { LoaderError, jsonValue } from './config.js';
import { ModuleGraph } from './module-graph.js';

const serialize = (error, depth = 0) => ({ name: error?.name ?? 'Error', message: error?.message ?? String(error), code: error?.code, details: error?.details, cause: depth < 8 && error?.cause ? serialize(error.cause, depth + 1) : undefined });

/** One runtime per child. The transport has no lifecycle scheduler of its own. */
export function startEndpoint(channel, launch, options = {}) {
  let graph;
  let host, startupError, closing = false, shutdown;
  const calls = new Set();
  const startup = (async () => {
    if (options.hostModule) {
      const { url, sha256 } = options.hostModule;
      const verify = async () => {
        if (createHash('sha256').update(await readFile(new URL(url))).digest('hex') !== sha256) throw new LoaderError('HOST_CHANGED', 'The trusted host module changed after it was pinned');
      };
      await verify();
      const module = await import(url);
      await verify();
      if (typeof module.createHost !== 'function') throw new LoaderError('HOST_CONTRACT', 'Trusted host must export synchronous createHost(options)');
      graph = new ModuleGraph(launch.directory, options).install();
      const candidate = module.createHost({ directory: launch.directory, entry: launch.entry, allowPending: launch.allowPending });
      if (!candidate || typeof candidate.then === 'function' || typeof candidate.ready?.then !== 'function' || ['call', 'diagnostics', 'close'].some(key => typeof candidate[key] !== 'function')) throw new LoaderError('HOST_CONTRACT', 'createHost must immediately expose call(), diagnostics(), close(), and a ready Promise');
      host = candidate;
      await host.ready;
    } else {
      await import('@cordis-verus/compat-cordis/register');
      graph = new ModuleGraph(launch.directory, options).install();
      const { Context } = await import('@cordis-verus/compat-cordis');
      const { Loader, ModuleHost } = await import('./index.js');
      const ctx = new Context();
      const loader = new Loader(ctx, { moduleHost: new ModuleHost({ rootDirectory: launch.directory }), allowPending: launch.allowPending });
      host = {
        diagnostics: () => JSON.parse(JSON.stringify(loader.diagnostics())),
        call: async (service, member, args) => {
          const value = ctx.get(service);
          if (value === undefined || typeof value[member] !== 'function') throw new LoaderError('SERVICE_METHOD', `Missing service method ${service}.${member}`);
          return Reflect.apply(value[member], value, args);
        },
        close: async () => { await loader.dispose(); await ctx.dispose(); },
      };
      await loader.loadFile(join(launch.directory, launch.entry));
    }
    await channel.send({ type: 'ready', diagnostics: jsonValue(await host.diagnostics()) });
  })().catch(async error => {
    startupError = error;
    await channel.send({ type: 'startup-error', error: serialize(error) });
  });
  startup.catch(() => {});
  channel.listen(request => {
    if (!request || typeof request !== 'object' || Array.isArray(request) || !Number.isSafeInteger(request.id) || typeof request.method !== 'string') return;
    const execute = async () => {
      if (request.method === 'shutdown') {
        closing = true;
        shutdown ??= (async () => {
          await startup;
          await Promise.allSettled([...calls]);
          if (!host) throw new LoaderError('CLEANUP_BLOCKED', 'Startup did not expose a host cleanup controller; explicit abandonment is required', {}, startupError);
          await host.close();
          return { disposed: true };
        })();
        try { return await shutdown; } catch (error) { shutdown = undefined; throw error; }
      }
      if (closing) throw new LoaderError('DOMAIN_CLOSING', 'The isolated domain is closing');
      await startup;
      if (startupError) throw startupError;
      if (request.method === 'diagnostics') return jsonValue(await host.diagnostics());
      if (request.method === 'moduleGraph') return graph.snapshot();
      if (request.method !== 'call') throw new LoaderError('DOMAIN_METHOD', 'Unsupported isolated domain request');
      const { service, member, args } = request;
      if (['constructor', '__proto__', 'prototype'].includes(member)) throw new LoaderError('SERVICE_METHOD', 'Reserved service method');
      return jsonValue(await host.call(service, member, args));
    };
    const task = execute();
    if (request.method !== 'shutdown') calls.add(task);
    task.then(async result => {
      await channel.send({ type: 'reply', id: request.id, result });
      if (request.method === 'shutdown') channel.close();
    }, error => channel.send({ type: 'reply', id: request.id, error: serialize(error) }))
      .catch(() => {}).finally(() => calls.delete(task));
  });
}
