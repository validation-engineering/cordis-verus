import { fork } from 'node:child_process';
import { readFileSync, realpathSync, statSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { resolve } from 'node:path';
import { WorkerDomain } from './worker.js';
import { releaseLaunch } from './artifact.js';
import { LoaderError } from './config.js';

function decode(error, depth = 0) {
  if (!error || typeof error !== 'object' || Array.isArray(error) || typeof error.message !== 'string') return new LoaderError('PROCESS_PROTOCOL', 'Child returned a malformed error payload');
  return new LoaderError(typeof error.code === 'string' ? error.code : 'PROCESS_ERROR', error.message,
    error.details && typeof error.details === 'object' ? error.details : {}, depth < 8 && error.cause ? decode(error.cause, depth + 1) : undefined);
}
const digest = url => createHash('sha256').update(readFileSync(new URL(url))).digest('hex');

class ProcessClient {
  constructor(launch, options, hostModule, onFault) {
    this.directory = launch.directory;
    this.timeout = options.timeout ?? 30000;
    this.pending = new Map();
    this.counter = 0;
    this.ready = Promise.withResolvers();
    this.exit = Promise.withResolvers();
    this.terminated = Promise.withResolvers();
    this.ready.promise.catch(() => {});
    this.exit.promise.catch(() => {});
    this.onFault = onFault;
    const env = { ...process.env, ...options.env };
    delete env.NODE_OPTIONS;
    delete env.NODE_PATH;
    this.process = fork(fileURLToPath(new URL('./process-entry.js', import.meta.url)), [], {
      cwd: options.cwd ?? launch.directory, env, execArgv: [], serialization: 'json', stdio: ['ignore', options.onOutput ? 'pipe' : options.stdio ?? 'inherit', options.onOutput ? 'pipe' : options.stdio ?? 'inherit', 'ipc'],
    });
    this.pid = this.process.pid;
    if (options.onOutput) for (const stream of ['stdout', 'stderr']) {
      this.process[stream].setEncoding('utf8');
      this.process[stream].on('data', data => { try { options.onOutput({ stream, data }); } catch { /* Observational output must not interrupt lifecycle cleanup. */ } });
    }
    const fail = cause => {
      if (this.crashed) return this.failure;
      this.crashed = true;
      this.failure = new LoaderError('DOMAIN_ABANDONED', 'Process exited without confirmed normal cleanup', {}, cause);
      this.ready.reject(this.failure);
      for (const pending of this.pending.values()) pending.reject(this.failure);
      this.pending.clear();
      onFault(this.failure);
      return this.failure;
    };
    this.process.on('message', message => {
      if (!message || typeof message !== 'object' || Array.isArray(message)) return;
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
    this.process.on('error', error => {
      fail(error);
      if (this.process.pid === undefined) { this.exited = true; this.terminated.resolve(); this.exit.reject(this.failure); }
    });
    this.process.on('close', () => { this.terminated.resolve(); });
    this.process.on('disconnect', () => {
      if (!this.closing || !this.shutdownAcknowledged) fail(new Error('Process disconnected before acknowledging cleanup'));
    });
    this.process.on('exit', (code, signal) => {
      this.exited = true;
      this.terminated.resolve();
      if (this.closing && this.shutdownAcknowledged && code === 0 && !signal && !this.crashed) this.exit.resolve();
      else this.exit.reject(fail(new Error(`Process exit ${code}, signal ${signal}`)));
    });
    try { this.process.send({ type: 'initialize', launch: { ...launch, allowPending: options.allowPending ?? false }, hostModule }, error => { if (error) fail(error); }); }
    catch (error) { fail(error); }
  }
  async timed(promise, label) {
    let timer;
    try {
      return await Promise.race([promise, new Promise((_, reject) => {
        timer = setTimeout(() => {
          const error = new LoaderError('DOMAIN_TIMEOUT', `${label} exceeded ${this.timeout} ms; cleanup is not confirmed`);
          this.onFault(error, 'blocked');
          reject(error);
        }, this.timeout);
      })]);
    } finally { clearTimeout(timer); }
  }
  start() { return this.timed(this.ready.promise, 'Process startup'); }
  request(method, fields = {}) {
    if (this.exited || !this.process.connected) return Promise.reject(this.failure ?? new LoaderError('DOMAIN_ABANDONED', 'Process IPC is unavailable'));
    const id = ++this.counter;
    const pending = { ...Promise.withResolvers(), method };
    this.pending.set(id, pending);
    try { this.process.send({ id, method, ...fields }, error => { if (error) pending.reject(error); }); }
    catch (error) { pending.reject(error); }
    return this.timed(pending.promise, `Process ${method}`).finally(() => this.pending.delete(id));
  }
  async close() {
    if (this.closed) return;
    if (this.crashed) throw this.failure;
    this.closing = true;
    if (!this.shutdownAcknowledged) await this.request('shutdown');
    await this.timed(this.exit.promise, 'Process exit after cleanup');
    await releaseLaunch(this.directory);
    this.closed = true;
  }
  async abandon() {
    if (!this.exited) {
      this.process.kill('SIGKILL');
      await this.timed(this.terminated.promise, 'Process forced termination');
    }
    await releaseLaunch(this.directory);
    this.closed = true;
  }
}

/** A real OS process boundary, including for application native addons. */
export class ProcessDomain extends WorkerDomain {
  constructor(options = {}) {
    super(options);
    this.boundary = 'Process';
    if (options.env !== undefined) this.options.env = Object.freeze({ ...options.env });
    if (options.timeout !== undefined && (!Number.isFinite(options.timeout) || options.timeout <= 0 || options.timeout > 2147483647)) throw new TypeError('timeout must be a positive finite timer duration');
    if (options.stdio !== undefined && !['inherit', 'ignore'].includes(options.stdio)) throw new TypeError('stdio must be inherit or ignore');
    if (options.onOutput !== undefined && typeof options.onOutput !== 'function') throw new TypeError('onOutput must be a function');
    if (options.cwd !== undefined) {
      this.options.cwd = realpathSync(options.cwd);
      if (!statSync(this.options.cwd).isDirectory()) throw new TypeError('cwd must be a directory');
    }
    if (options.hostModule !== undefined) {
      const filename = options.hostModule instanceof URL ? fileURLToPath(options.hostModule) : String(options.hostModule).startsWith('file:') ? fileURLToPath(options.hostModule) : resolve(options.hostModule);
      const url = pathToFileURL(realpathSync(filename)).href;
      this._hostModule = Object.freeze({ url, sha256: digest(url) });
    }
  }
  get pid() { return this._current?.client.pid; }
  get hostProvenance() { return this._hostModule; }
  _verifyHost() {
    if (this._hostModule && digest(this._hostModule.url) !== this._hostModule.sha256) throw new LoaderError('HOST_CHANGED', 'The trusted host module changed; construct a new supervisor after reviewing its provenance');
  }
  _plan(artifact, graph) {
    this._verifyHost();
    return { ...super._plan(artifact, graph), strategy: 'process-restart', ...(this._hostModule ? { host: this._hostModule } : {}) };
  }
  _assertPlan() {}
  _createClient(launch, onFault) {
    this._verifyHost();
    return new ProcessClient(launch, this.options, this._hostModule, onFault);
  }
}
