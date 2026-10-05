import { AsyncLocalStorage } from 'node:async_hooks';
import { pathToFileURL } from 'node:url';
import { Context, FiberState, Inject } from '@cordis-verus/compat-cordis';
import { isConstructor } from '@cordis-verus/compat-cordis/utils';
import { LoaderError, fileURL, jsonValue, readTree } from './config.js';
import { ModuleHost } from './module-host.js';

export { LoaderError, ModuleHost, readTree as readConfig };
const operation = new AsyncLocalStorage();
const reentrant = loader => operation.getStore()?.loader === loader && operation.getStore().active;
const names = ['pending', 'loading', 'active', 'failed', 'disposed', 'unloading'];
const orderedJSON = value => value && typeof value === 'object'
  ? Array.isArray(value) ? value.map(orderedJSON)
    : Object.fromEntries(Object.keys(value).sort().map(key => [key, orderedJSON(value[key])])) : value;
const canonical = value => JSON.stringify(orderedJSON(value));
const localOptions = node => ({
  group: node.group, disabled: !!node.disabled, baseURL: node.baseURL,
  hasConfig: Object.hasOwn(node.options, 'config'), config: node.options.config ?? null, inject: Inject.resolve(node.options.inject),
  isolate: Array.isArray(node.options.isolate) ? Object.fromEntries(node.options.isolate.map(name => [name, true])) : node.options.isolate ?? {},
  intercept: node.options.intercept ?? {},
});
const sameNode = (left, right) => canonical(localOptions(left)) === canonical(localOptions(right))
  && left.module?.url === right.module?.url && left.module?.plugin === right.module?.plugin
  && Object.is(left.module?.revision, right.module?.revision);

export class Entry {
  constructor(id) { this.id = id; }
  get state() { return this.disabled ? 'disabled' : this.fiber ? names[this.fiber.state] : 'pending'; }
}

/** This package's JSON Include format; not the upstream YAML Include class. */
export class Include {
  static read(filename, options) { return readTree(filename, options); }
}

function injectedPlugin(plugin, inject) {
  if (!inject || !Object.keys(inject).length) return plugin;
  const callback = typeof plugin === 'function' ? plugin : plugin.apply;
  const forward = isConstructor(callback)
    ? function Forward(ctx, config) { return Reflect.construct(callback, [ctx, config]); }
    : (ctx, config) => callback(ctx, config);
  Object.defineProperties(forward, {
    name: { value: plugin.name ?? callback.name, configurable: true },
    inject: { value: { ...Inject.resolve(plugin.inject), ...Inject.resolve(inject) } },
    Config: { value: plugin.Config },
  });
  return forward;
}

/** One managed entry tree, over an existing native-backed Context. */
export class Loader {
  constructor(context = new Context(), options = {}) {
    this.ctx = context;
    this.moduleHost = options.moduleHost ?? new ModuleHost();
    this.baseURL = options.baseURL ?? pathToFileURL(`${process.cwd()}/`).href;
    this.allowPending = options.allowPending ?? false;
    this.state = 'empty';
    this.revision = 0;
    this.lastRecovery = undefined;
    this._entries = new Map();
    this._labels = new Map();
    this._queue = Promise.resolve();
    this._accepting = true;
  }
  entries() { return this._entries.values(); }
  resolve(id) {
    const entry = this._entries.get(id);
    if (!entry) throw new LoaderError('ENTRY_NOT_FOUND', `Unknown entry ${id}`);
    return entry;
  }
  _serialize(task, closing = false) {
    if (reentrant(this)) return Promise.reject(new LoaderError('REENTRANT_MUTATION', 'Loader mutations cannot be awaited from their own setup, cleanup or mutation operation; mount children with ctx.plugin()'));
    if (!this._accepting && !closing) return Promise.reject(new LoaderError('LOADER_CLOSED', 'Loader is closing or closed'));
    if (this.state === 'blocked' && !closing) return Promise.reject(new LoaderError('CLEANUP_BLOCKED', 'Unfinished cleanup prevents another activation; retryCleanup() first'));
    const result = this._queue.then(() => {
      if (this.state === 'blocked' && !closing) throw new LoaderError('CLEANUP_BLOCKED', 'Unfinished cleanup prevents activation');
      const token = { loader: this, active: true };
      return operation.run(token, async () => { try { return await task(); } finally { token.active = false; } });
    });
    this._queue = result.catch(() => {});
    return result;
  }
  apply(tree, options = {}) {
    // Capture caller input at admission, before it can change while queued.
    let input;
    try { input = jsonValue(tree); } catch (error) { return Promise.reject(error); }
    return this._serialize(async () => {
      const recipe = await this.moduleHost.prepare(await readTree(input, { baseURL: options.baseURL ?? this.baseURL, rootDirectory: this.moduleHost.rootDirectory }));
      return this._replace(recipe, undefined);
    });
  }
  loadFile(filename) {
    const source = fileURL(filename, this.baseURL).href;
    return this._serialize(async () => this._replace(await this.moduleHost.prepare(await readTree(source, { rootDirectory: this.moduleHost.rootDirectory })), source));
  }
  reload() {
    return this._serialize(async () => {
      if (!this._active) throw new LoaderError('NO_RECIPE', 'Load a configuration before reloading');
      const recipe = this._source ? await this.moduleHost.prepare(await readTree(this._source, { rootDirectory: this.moduleHost.rootDirectory })) : await this.moduleHost.prepare(this._active.recipe);
      return this._replace(recipe, this._source);
    });
  }
  update(id, patch) {
    let change;
    try { change = jsonValue(patch); if (!change || Array.isArray(change) || typeof change !== 'object') throw new LoaderError('INVALID_UPDATE', 'patch must be an object'); } catch (error) { return Promise.reject(error); }
    return this._serialize(async () => {
      this.resolve(id);
      if ('id' in change || 'entries' in change || 'include' in change || 'group' in change) throw new LoaderError('INVALID_UPDATE', 'update() cannot change entry identity or group structure; use apply()');
      const convert = nodes => nodes.map(node => {
        const item = { ...node.options };
        delete item.include;
        if (node.group) { item.group = true; item.entries = convert(node.children); }
        else item.name = fileURL(item.name, node.baseURL).href;
        if (node.id === id) { Object.assign(item, change); if (change.name !== undefined) item.name = fileURL(change.name, node.baseURL).href; }
        return item;
      });
      const input = await readTree(convert(this._active.recipe.tree), { baseURL: this.baseURL, rootDirectory: this.moduleHost.rootDirectory });
      const origins = new Map([...this._active.records].map(([id, record]) => [id, record.node.baseURL]));
      const preserveOrigins = nodes => { for (const node of nodes) { node.baseURL = origins.get(node.id) ?? node.baseURL; preserveOrigins(node.children); } };
      preserveOrigins(input.tree);
      const recipe = await this.moduleHost.prepare(input);
      return this._replace(recipe, undefined);
    });
  }
  setEnabled(id, enabled) {
    if (typeof enabled !== 'boolean') return Promise.reject(new LoaderError('INVALID_UPDATE', 'enabled must be boolean'));
    return this.update(id, { disabled: !enabled });
  }
  _context(parent, node) {
    let ctx = parent.extend({ baseUrl: node.baseURL });
    const isolate = Array.isArray(node.options.isolate) ? Object.fromEntries(node.options.isolate.map(name => [name, true])) : node.options.isolate ?? {};
    for (const [name, label] of Object.entries(isolate)) {
      const identity = label === true ? `entry:${node.id}:${name}` : `label:${label}`;
      if (!this._labels.has(identity)) this._labels.set(identity, Symbol(identity));
      ctx = ctx.isolate(name, this._labels.get(identity));
    }
    for (const [name, config] of Object.entries(node.options.intercept ?? {})) ctx = ctx.intercept(name, jsonValue(config));
    return ctx;
  }
  _generation(recipe, previous, retained = new Set()) {
    const generation = { recipe, records: new Map(), root: previous?.root };
    const register = (nodes, parentId) => {
      for (const node of nodes) {
        const old = retained.has(node.id) ? previous.records.get(node.id) : undefined;
        generation.records.set(node.id, {
          id: node.id, parentId, node, options: node.options, disabled: node.disabled,
          moduleURL: node.module?.url, fiber: old?.fiber, context: old?.context, control: old?.control,
        });
        register(node.children, node.id);
      }
    };
    register(recipe.tree);
    return generation;
  }
  _retarget(generation, suspended) {
    for (const record of generation.records.values()) if (record.control) {
      Object.assign(record.control, { generation, node: record.node, enabled: true, suspended });
    }
  }
  _install(ctx, plugin, config, record) {
    const known = new Set(ctx.registry.get(plugin)?.fibers ?? []);
    try {
      const mounted = ctx.plugin(plugin, config);
      record.fiber = mounted.ctx.fiber;
      record.context = record.fiber.ctx;
      return mounted;
    } catch (error) {
      // Synchronous observers may throw after native ownership was allocated.
      // Keep that fiber in the transaction so failed inverses cannot be orphaned.
      record.fiber = [...(ctx.registry.get(plugin)?.fibers ?? [])].find(fiber => !known.has(fiber) && fiber.parent.fiber === ctx.fiber);
      record.context = record.fiber?.ctx;
      throw error;
    }
  }
  _mount(nodes, parent, generation) {
    const pending = [];
    for (const node of nodes) {
      if (node.disabled) continue;
      const record = generation.records.get(node.id);
      if (record.fiber && !record.fiber._removedFlag && record.fiber.uid !== null) {
        // Pending groups create children when their own dependencies become ready.
        if (node.group && record.fiber.state === FiberState.ACTIVE) pending.push(...this._mount(node.children, record.context, generation));
        continue;
      }
      const ctx = this._context(parent, node);
      const control = node.group ? { generation, node, enabled: true, suspended: false } : undefined;
      const plugin = control
        ? { name: `group:${node.id}`, inject: node.options.inject, apply: async child => {
          if (control.enabled && !control.suspended) await Promise.all(this._mount(control.node.children, child, control.generation));
        } }
        : injectedPlugin(node.module.plugin, node.options.inject === undefined ? undefined : jsonValue(node.options.inject));
      record.control = control;
      const mounted = this._install(ctx, plugin, node.options.config === undefined ? undefined : jsonValue(node.options.config), record);
      if (this._active === generation) this._assignEntry(this._entries.get(node.id), record);
      const task = mounted.await();
      task.catch(() => {});
      pending.push(task);
    }
    return pending;
  }
  _mountRoot(generation) {
    const record = {};
    try { this._install(this.ctx, { name: 'loader-tree', apply: async ctx => { await Promise.all(this._mount(generation.recipe.tree, ctx, generation)); } }, undefined, record); }
    finally { generation.root = record.fiber; }
  }
  _retained(previous, recipe) {
    const result = new Set();
    const visit = (nodes, parentRetained = true) => {
      for (const node of nodes) {
        const old = previous.records.get(node.id);
        const retained = parentRetained && old && sameNode(old.node, node)
          && (!old.fiber || (!old.fiber._removedFlag && old.fiber.uid !== null));
        if (retained) result.add(node.id);
        visit(node.children, retained);
      }
    };
    visit(recipe.tree);
    return result;
  }
  _roots(records, select) {
    const selected = [...records.values()].filter(record => record.fiber && !record.fiber._removedFlag && select(record));
    const ids = new Set(selected.map(record => record.id));
    return selected.filter(record => !ids.has(record.parentId)).map(record => record.fiber);
  }
  async _drainRoots(generation, roots) {
    let failure;
    const disposals = roots.map(fiber => {
      try { const task = fiber.dispose(); task.catch(error => { failure ??= error; }); return task; }
      catch (error) { failure ??= error; return Promise.resolve(); }
    });
    try { await this.ctx.settle(); } catch (error) { failure ??= error; }
    const remaining = new Set(this.ctx.snapshot().plugins.map(fiber => fiber.id));
    if (roots.some(fiber => remaining.has(fiber.id))) {
      this._blocked = generation;
      this.state = 'blocked';
      throw new LoaderError('CLEANUP_BLOCKED', 'Changed fibers still own native resources; no replacement or old recipe has been activated', { fiberIds: roots.filter(fiber => remaining.has(fiber.id)).map(fiber => fiber.id) }, failure);
    }
    await Promise.allSettled(disposals);
  }
  async _start(generation) {
    let error;
    try { await generation.root.await(); } catch (cause) { error = cause; }
    try { await this.ctx.settle(); } catch (cause) { error ??= cause; }
    for (const record of generation.records.values()) if (record.fiber && !record.disabled) {
      try { await record.fiber.await(); } catch (cause) { error ??= cause; }
    }
    if (error) throw error;
    const pending = this._diagnostics(generation).filter(entry => entry.state !== 'active' && entry.state !== 'disabled');
    if (!this.allowPending && pending.length) throw new LoaderError('DEPENDENCIES_UNAVAILABLE', `Required entries are not ready: ${pending.map(entry => `${entry.id} (${entry.unavailableServices.join(', ') || entry.state})`).join('; ')}`, { entries: pending });
  }
  _diagnostics(generation) {
    if (!generation) return [];
    return [...generation.records.values()].map(record => ({
      id: record.id, parentId: record.parentId ?? null, moduleURL: record.moduleURL ?? null,
      state: record.disabled ? 'disabled' : record.fiber ? names[record.fiber.state] : 'pending',
      unavailableServices: record.fiber ? Object.keys(record.fiber.inject).filter(name => !record.context.reflect._getImpl(name, true)) : [],
      ...(record.fiber ? { fiberId: record.fiber.id } : {}),
    }));
  }
  diagnostics() { return this._diagnostics(this._active ?? this._blocked); }
  async _drain(generation) {
    if (!generation?.root) return;
    for (const record of generation.records.values()) if (record.control) record.control.enabled = false;
    await this._drainRoots(generation, [generation.root]);
  }
  _assignEntry(entry, record) {
    if (entry) Object.assign(entry, Object.fromEntries(['id', 'parentId', 'options', 'disabled', 'moduleURL', 'fiber', 'context'].map(key => [key, record[key]])));
  }
  _commit(generation, source) {
    const next = new Map();
    for (const [id, record] of generation.records) {
      const entry = this._entries.get(id) ?? new Entry(id);
      this._assignEntry(entry, record);
      next.set(id, entry);
    }
    this._entries = next;
    this._active = generation;
    this._source = source;
    this.state = 'active';
  }
  async _replace(recipe, source) {
    const previous = this._active;
    const previousSource = this._source;
    this.lastRecovery = undefined;
    this.state = 'reloading';
    if (previous && (previous.root._removedFlag || previous.root.uid === null)) {
      this.state = 'blocked'; this._blocked = previous;
      throw new LoaderError('OWNER_REMOVED', 'The Loader owner was disposed outside the Loader; drain it before loading again');
    }
    const retained = previous ? this._retained(previous, recipe) : new Set();
    const candidate = this._generation(recipe, previous, retained);
    if (previous) {
      for (const record of previous.records.values()) if (record.control && !retained.has(record.id)) record.control.enabled = false;
      this._retarget(candidate, true);
      await this._drainRoots(candidate, this._roots(previous.records, record => !retained.has(record.id)));
    }
    try {
      this._retarget(candidate, false);
      if (previous) this._mount(recipe.tree, candidate.root.ctx, candidate);
      else this._mountRoot(candidate);
      await this._start(candidate);
      this._commit(candidate, source);
      this.revision++;
      return this.diagnostics();
    } catch (cause) {
      this._retarget(candidate, true);
      if (!previous) {
        await this._drain(candidate);
        this.state = 'empty'; this._entries.clear(); throw cause;
      }
      // Drain every candidate-created fiber, including children recreated by a
      // retained group's dependency restart, before restoring old declarations.
      const preserved = new Set([...candidate.records.values()].filter(record => retained.has(record.id)
        && record.fiber === previous.records.get(record.id)?.fiber && !record.fiber?._removedFlag).map(record => record.id));
      for (const record of candidate.records.values()) if (record.control && !preserved.has(record.id)) record.control.enabled = false;
      await this._drainRoots(candidate, this._roots(candidate.records, record => !preserved.has(record.id)));
      const restored = this._generation(previous.recipe, candidate, preserved);
      try {
        this._retarget(restored, false);
        this._mount(restored.recipe.tree, restored.root.ctx, restored);
        // A retained consumer may have failed while observing the candidate.
        // Restore its old recipe without manufacturing a successful completion.
        for (const record of restored.records.values()) if (record.fiber?.state === FiberState.FAILED) {
          const task = record.fiber.restart(); task.catch(() => {});
        }
        await this._start(restored);
        this._commit(restored, previousSource);
      } catch (recoveryError) {
        await this._drain(restored);
        this._active = undefined; this.state = 'empty'; this._entries.clear();
        throw new LoaderError('RESTORE_FAILED', 'Candidate failed and the retained old recipe could not be restored', {}, new AggregateError([cause, recoveryError]));
      }
      this.lastRecovery = { restored: true, cause };
      throw new LoaderError('RELOAD_FAILED', 'Candidate changes were drained and the previous recipe was restored', { restored: true }, cause);
    }
  }
  retryCleanup() {
    return this._serialize(async () => {
      if (!this._blocked) return;
      // Retry failed descendants first; successful cleanup is not repeated.
      const nodes = this.ctx.snapshot().plugins;
      const root = this._blocked.root;
      const owned = new Set([root.id]);
      for (let changed = true; changed;) {
        changed = false;
        for (const node of nodes) if (owned.has(node.parent) && !owned.has(node.id)) { owned.add(node.id); changed = true; }
      }
      const fibers = [...this.ctx.registry.values()].flatMap(runtime => [...runtime.fibers]);
      for (const node of nodes.filter(node => owned.has(node.id) && node.cleanupFailed).reverse()) {
        const fiber = fibers.find(item => item.id === node.id);
        if (fiber) await fiber.retryCleanup();
      }
      await this._drain(this._blocked);
      this._blocked = undefined;
      this._active = undefined;
      this._entries.clear();
      this.state = this._accepting ? 'empty' : 'closed';
    }, true);
  }
  dispose() {
    if (reentrant(this)) return Promise.reject(new LoaderError('REENTRANT_MUTATION', 'Cannot dispose Loader from its own callback'));
    this._accepting = false;
    return this._serialize(async () => {
      await this._drain(this._active ?? this._blocked);
      this._active = undefined;
      this._blocked = undefined;
      this._entries.clear();
      this.state = 'closed';
    }, true);
  }
}
