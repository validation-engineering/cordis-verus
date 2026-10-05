import { Worker } from 'node:worker_threads';
import { rm } from 'node:fs/promises';
import { Artifact } from './artifact.js';
import { LoaderError, jsonValue } from './config.js';
export { Artifact };

function decode(error) { return new LoaderError(error.code ?? 'WORKER_ERROR', error.message, error.details ?? {}); }
function timed(promise, timeout, label) {
  let timer;
  const elapsed = new Promise((_, reject) => { timer = setTimeout(() => reject(new LoaderError('DOMAIN_TIMEOUT', `${label} exceeded ${timeout} ms; cleanup is not confirmed`)), timeout); });
  return Promise.race([promise, elapsed]).finally(() => clearTimeout(timer));
}
class WorkerClient {
  constructor(launch, options, onCrash) {
    this.directory = launch.directory;
    this.timeout = options.timeout ?? 30000;
    this.pending = new Map();
    this.counter = 0;
    this.exited = false;
    this.crashed = false;
    this.closed = false;
    this.ready = Promise.withResolvers();
    this.exit = Promise.withResolvers();
    this.ready.promise.catch(() => {});
    this.exit.promise.catch(() => {});
    this.worker = new Worker(new URL('./worker-entry.js', import.meta.url), {
      workerData: { ...launch, allowPending: options.allowPending ?? false }, execArgv: [],
    });
    this.worker.on('message', message => {
      if (message.type === 'ready') { this.ready.resolve(message.diagnostics); return; }
      if (message.type === 'startup-error') { this.ready.reject(decode(message.error)); return; }
      if (message.type !== 'reply') return;
      const pending = this.pending.get(message.id);
      if (!pending) return;
      this.pending.delete(message.id);
      if (message.error) pending.reject(decode(message.error));
      else {
        if (pending.method === 'shutdown' && message.result?.disposed === true) this.shutdownAcknowledged = true;
        pending.resolve(message.result);
      }
    });
    const failed = cause => {
      this.crashed = true;
      const error = new LoaderError('DOMAIN_ABANDONED', 'Worker exited without confirmed normal cleanup', {}, cause);
      this.ready.reject(error);
      for (const item of this.pending.values()) item.reject(error);
      this.pending.clear();
      onCrash(error);
      return error;
    };
    this.worker.on('error', error => { this.failure = failed(error); });
    this.worker.on('exit', code => {
      this.exited = true;
      if (this.closing && this.shutdownAcknowledged && code === 0 && !this.crashed) this.exit.resolve();
      else this.exit.reject(this.failure ?? failed(new Error(`Worker exit ${code}`)));
    });
  }
  start() { return timed(this.ready.promise, this.timeout, 'Worker startup'); }
  request(method, fields = {}) {
    if (this.exited) return Promise.reject(new LoaderError('DOMAIN_ABANDONED', 'Worker is no longer running'));
    const id = ++this.counter;
    const pending = { ...Promise.withResolvers(), method };
    this.pending.set(id, pending);
    this.worker.postMessage({ id, method, ...fields });
    return timed(pending.promise, this.timeout, `Worker ${method}`).finally(() => this.pending.delete(id));
  }
  async close() {
    if (this.closed) return;
    if (this.crashed) throw this.failure ?? new LoaderError('DOMAIN_ABANDONED', 'Worker was abandoned');
    this.closing = true;
    await this.request('shutdown');
    await timed(this.exit.promise, this.timeout, 'Worker exit after cleanup');
    this.closed = true;
    await rm(this.directory, { recursive: true, force: true });
  }
  async abandon() {
    if (!this.exited) await this.worker.terminate();
    await rm(this.directory, { recursive: true, force: true });
    this.closed = true;
  }
}

/** Entire Node environment replacement; inter-environment messages are JSON. */
export class WorkerDomain {
  constructor(options = {}) {
    this.options = { ...options, entry: options.entry ?? 'cordis.json' };
    this.state = 'empty';
    this.lastRecovery = undefined;
    this._queue = Promise.resolve();
    this._artifacts = new Set();
    this._clients = new Set();
    this._accepting = true;
  }
  _serialize(task, closing = false) {
    if (!this._accepting && !closing) return Promise.reject(new LoaderError('DOMAIN_CLOSED', 'WorkerDomain is closing or closed'));
    const result = this._queue.then(async () => {
      if (['blocked', 'abandoned'].includes(this.state) && !closing) throw new LoaderError('DOMAIN_BLOCKED', 'The prior domain did not confirm cleanup; dispose or explicitly abandon it');
      return task();
    });
    this._queue = result.catch(() => {});
    return result;
  }
  async _client(artifact) {
    const launch = await artifact.launch(this.options.entry);
    let client;
    try {
      client = new WorkerClient(launch, this.options, error => { this.state = 'abandoned'; this.failure = error; });
    } catch (error) { await rm(launch.directory, { recursive: true, force: true }); throw error; }
    this._clients.add(client);
    return client;
  }
  async _close(client) {
    if (!client) return;
    try { await client.close(); this._clients.delete(client); }
    catch (cause) {
      this.state = client.crashed ? 'abandoned' : 'blocked';
      throw new LoaderError(client.crashed ? 'DOMAIN_ABANDONED' : 'CLEANUP_BLOCKED', 'Worker cleanup was not confirmed; no replacement was activated', {}, cause);
    }
  }
  load(directory) {
    return this._serialize(async () => {
      const artifact = await Artifact.capture(directory, this.options);
      this._artifacts.add(artifact);
      return this._replace(artifact);
    });
  }
  reload(directory) {
    if (directory === undefined) directory = this._current?.artifact.source;
    if (!directory) return Promise.reject(new LoaderError('NO_RECIPE', 'load() an artifact before reload()'));
    return this.load(directory);
  }
  async _replace(artifact) {
    const previous = this._current;
    this.lastRecovery = undefined;
    this.state = 'reloading';
    await this._close(previous?.client);
    this._current = undefined;
    let candidate;
    try {
      candidate = await this._client(artifact);
      const diagnostics = await candidate.start();
      this._current = { artifact, client: candidate, diagnostics };
      this.state = 'active';
      if (previous) { await previous.artifact.dispose(); this._artifacts.delete(previous.artifact); }
      return { digest: artifact.digest, diagnostics };
    } catch (cause) {
      await this._close(candidate);
      await artifact.dispose(); this._artifacts.delete(artifact);
      if (previous) {
        let restored;
        try {
          restored = await this._client(previous.artifact);
          const diagnostics = await restored.start();
          this._current = { artifact: previous.artifact, client: restored, diagnostics };
          this.state = 'active';
          this.lastRecovery = { restored: true, digest: previous.artifact.digest, cause };
        } catch (recoveryError) {
          await this._close(restored);
          this.state = 'empty';
          throw new LoaderError('RESTORE_FAILED', 'Old captured artifact could not restart after candidate failure', {}, new AggregateError([cause, recoveryError]));
        }
        throw new LoaderError('RELOAD_FAILED', 'Candidate Worker was drained; the retained old artifact restarted in a new Worker', { restored: true, digest: previous.artifact.digest }, cause);
      }
      this.state = 'empty';
      throw cause;
    }
  }
  call(service, method, ...args) {
    if (!this._accepting || this.state !== 'active' || !this._current) return Promise.reject(new LoaderError('DOMAIN_NOT_READY', `WorkerDomain is ${this._accepting ? this.state : 'closing'}`));
    if (typeof service !== 'string' || typeof method !== 'string') return Promise.reject(new LoaderError('SERVICE_METHOD', 'service and method must be strings'));
    let values;
    try { values = jsonValue(args); } catch (error) { return Promise.reject(error); }
    return this._current.client.request('call', { service, member: method, args: values });
  }
  diagnostics() {
    if (!this._accepting || this.state !== 'active' || !this._current) return Promise.reject(new LoaderError('DOMAIN_NOT_READY', `WorkerDomain is ${this._accepting ? this.state : 'closing'}`));
    return this._current.client.request('diagnostics');
  }
  dispose() {
    this._accepting = false;
    return this._serialize(async () => {
      for (const client of [...this._clients]) await this._close(client);
      for (const artifact of this._artifacts) await artifact.dispose();
      this._artifacts.clear();
      this._current = undefined;
      this.state = 'closed';
    }, true);
  }
  /** Forced fault recovery never counts as confirmed normal cleanup. */
  abandon() {
    this._accepting = false;
    return this._serialize(async () => {
      for (const client of this._clients) await client.abandon();
      for (const artifact of this._artifacts) await artifact.dispose();
      this._clients.clear(); this._artifacts.clear(); this._current = undefined;
      this.state = 'abandoned';
      return { abandoned: true, cleanupConfirmed: false };
    }, true);
  }
}
