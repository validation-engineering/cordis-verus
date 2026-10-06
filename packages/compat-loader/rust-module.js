import { isAbsolute } from 'node:path';
import { FiberState, assertDomainMutation, domainMutation } from '@cordis-verus/compat-cordis';
import { LoaderError, jsonValue } from './config.js';

const fail = (code, message, details = {}, cause) => new LoaderError(code, message, details, cause);
const freeze = value => {
  if (value && typeof value === 'object') { for (const item of Object.values(value)) freeze(item); Object.freeze(value); }
  return value;
};
function artifactOf(value) {
  const { path, sha256 } = value ?? {};
  if (typeof path !== 'string' || !isAbsolute(path) || path.includes('\0')) throw fail('NATIVE_MODULE_PATH', 'Native modules require an absolute artifact path');
  if (typeof sha256 !== 'string' || !/^[a-f0-9]{64}$/.test(sha256)) throw fail('NATIVE_MODULE_DIGEST', 'Native modules require an expected lowercase SHA-256 digest');
  return Object.freeze({ path, sha256 });
}
function recipesOf(value) {
  if (!Array.isArray(value) || !value.length) throw fail('NATIVE_MODULE_RECIPE', 'At least one managed plugin entry is required');
  const recipes = jsonValue(value), ids = new Set();
  for (const item of recipes) {
    if (!item || typeof item !== 'object' || Array.isArray(item) || typeof item.id !== 'string' || !item.id
      || ids.has(item.id) || typeof item.factory !== 'string' || !item.factory
      || Object.keys(item).some(key => !['id','factory','config'].includes(key))) throw fail('NATIVE_MODULE_RECIPE', 'Entries require unique ids, factory names, and optional JSON config');
    ids.add(item.id);
  }
  return freeze(recipes);
}

/** One owned group in the existing native domain. Code images are retained. */
export class RustModuleController {
  constructor(ctx, options) {
    assertDomainMutation(ctx);
    ctx.fiber.assertActive();
    this.ctx = ctx;
    this._domain = ctx.fiber._domain;
    this._owner = ctx.fiber;
    this._ownerGeneration = ctx.fiber._generation;
    this._recipes = recipesOf(options?.plugins);
    this._accepting = true;
    this.state = 'empty';
    this.revision = 0;
    this.lastReloadFailure = undefined;
  }
  _check() {
    const owner = this._owner;
    if (owner._removedFlag || owner.uid === null || owner._generation !== this._ownerGeneration
      || [FiberState.DISPOSED,FiberState.UNLOADING].includes(owner.state)) throw fail('NATIVE_MODULE_OWNER_REMOVED', 'Native module controller belongs to a previous or removed owner activation');
  }
  _submit(task, recovery = false) {
    try {
      assertDomainMutation(this.ctx, { recovery });
      if (!this._accepting && !recovery) throw fail('NATIVE_MODULE_CLOSED', 'Native module controller is closing or closed');
      if (!recovery) this._check();
    } catch (error) { return Promise.reject(error); }
    return domainMutation(this.ctx, async steps => {
      if (!recovery) this._check();
      return task(steps);
    }, { recovery });
  }
  _prepare(artifact) {
    const module = this._domain.rust.loadModule(artifact);
    for (const recipe of this._recipes) if (!module.factories.has(recipe.factory)) {
      throw fail('NATIVE_MODULE_FACTORY', `Candidate does not export ${recipe.factory}`, { factory: recipe.factory });
    }
    const previous = this._active?.module ?? this._pending?.previous;
    if (previous && module.descriptor.pluginId !== previous.descriptor.pluginId) {
      throw fail('NATIVE_MODULE_IDENTITY', 'Candidate plugin identity differs from the active module');
    }
    return module;
  }
  _install(ctx, plugin, config, record) {
    const known = new Set(ctx.registry.get(plugin)?.fibers ?? []);
    try { record.fiber = ctx.plugin(plugin, config).ctx.fiber; }
    catch (error) {
      // An internal/plugin observer can throw after native allocation.
      record.fiber = [...ctx.registry.get(plugin)?.fibers ?? []].find(fiber => !known.has(fiber) && fiber.parent.fiber === ctx.fiber);
      throw error;
    }
  }
  async _activate(module, state) {
    this._check();
    state.module = module;
    state.entries = new Map();
    const plugin = { name: `native-module:${module.descriptor.pluginId}`, apply: async ctx => {
      const tasks = [];
      for (const recipe of this._recipes) {
        const record = { recipe };
        state.entries.set(recipe.id, record);
        this._install(ctx, module.factories.get(recipe.factory), recipe.config === undefined ? undefined : jsonValue(recipe.config), record);
        const task = record.fiber.await();
        task.catch(() => {});
        tasks.push(task);
      }
      await Promise.all(tasks);
    } };
    let failure;
    try {
      this._install(this.ctx, plugin, undefined, state);
      await state.fiber.await();
    } catch (error) { failure = error; }
    try { await this.ctx.settle(); } catch (error) { failure ??= error; }
    if (failure) throw failure;
    if ([state.fiber,...[...state.entries.values()].map(item => item.fiber)].some(fiber => fiber?.state !== FiberState.ACTIVE)) {
      throw fail('NATIVE_MODULE_NOT_ACTIVE', 'Native module entries did not all reach Active');
    }
  }
  async _drain(steps, states) {
    const roots = [...new Set(states.map(state => state?.fiber).filter(fiber => fiber && !fiber._removedFlag))];
    let failure;
    const tasks = roots.map(fiber => {
      try { return Promise.resolve(steps.dispose(fiber)).catch(error => { failure ??= error; }); }
      catch (error) { failure ??= error; return Promise.resolve(); }
    });
    try { await this.ctx.settle(); } catch (error) { failure ??= error; }
    const remaining = new Set(this.ctx.snapshot().plugins.map(fiber => fiber.id));
    const blocked = roots.filter(fiber => remaining.has(fiber.id));
    if (blocked.length) throw fail('NATIVE_MODULE_CLEANUP_BLOCKED', 'Native resources remain; explicitly retry failed cleanup before replacement', { fiberIds: blocked.map(fiber => fiber.id) }, failure);
    await Promise.all(tasks);
  }
  async _recover(steps, resumeRetirement = false) {
    const pending = this._pending;
    if (!pending) return;
    try { await this._drain(steps, pending.retained); }
    catch (cause) {
      this.state = 'blocked';
      throw this.lastReloadFailure = fail('NATIVE_MODULE_RECOVERY_BLOCKED', 'Retained generation cleanup remains unconfirmed', { restored: false }, new AggregateError([pending.cause,cause]));
    }
    this._active = undefined;
    pending.retained = [];
    if (resumeRetirement && pending.stage === 'retiring') {
      // No candidate ever ran. Resume replacement from confirmed retirement;
      // briefly reconstructing the old instance would needlessly repeat its
      // cleanup failure. Keep its immutable recipe as candidate rollback.
      this._pending = undefined;
      this.state = 'empty';
      return pending.previous;
    }
    if (pending.previous) {
      const restored = {};
      pending.retained = [restored];
      try { await this._activate(pending.previous, restored); }
      catch (cause) {
        this.state = 'blocked';
        throw this.lastReloadFailure = fail('NATIVE_MODULE_RESTORE_FAILED', 'Old code is retained but its new activation failed', { restored: false }, new AggregateError([pending.cause,cause]));
      }
      this._active = restored;
    }
    this._pending = undefined;
    this.state = this._active ? 'active' : 'empty';
  }
  reload(artifact) {
    let captured;
    try { captured = artifactOf(artifact); } catch (error) { this.lastReloadFailure = error; return Promise.reject(error); }
    return this._submit(async steps => {
      // Recovery is an ordinary admitted transaction after explicit cleanup
      // retry, so it never borrows permission to create from a recovery token.
      const module = this._prepare(captured);
      const retired = await this._recover(steps, true), previous = this._active;
      const rollback = previous?.module ?? retired;
      this.state = 'reloading';
      if (previous) {
        try { await this._drain(steps, [previous]); }
        catch (cause) {
          this._pending = { previous: previous.module, retained: [previous], cause, stage: 'retiring' };
          this.state = 'blocked';
          throw this.lastReloadFailure = fail('NATIVE_MODULE_CLEANUP_BLOCKED', 'Old generation cleanup is unconfirmed; candidate setup has not run', { restored: false }, cause);
        }
      }
      const candidate = {};
      try { await this._activate(module, candidate); }
      catch (cause) {
        this._pending = { previous: rollback, retained: [candidate], cause };
        await this._recover(steps);
        throw this.lastReloadFailure = fail('NATIVE_MODULE_RELOAD_FAILED', rollback ? 'Candidate failed; old code and config were reactivated' : 'Initial activation failed and was cleaned up', { restored: !!rollback }, cause);
      }
      this._active = candidate;
      this.state = 'active';
      this.revision++;
      this.lastReloadFailure = undefined;
      return this.snapshot();
    }).catch(error => { this.lastReloadFailure = error; throw error; });
  }
  retryCleanup() {
    return this._submit(async steps => {
      if (!this._pending && this.state !== 'blocked') return this.snapshot();
      const roots = new Set([this._active,...this._pending?.retained ?? []].map(state => state?.fiber?.id).filter(Boolean));
      const nodes = this.ctx.snapshot().plugins;
      for (let changed = true; changed;) {
        changed = false;
        for (const node of nodes) if (roots.has(node.parent) && !roots.has(node.id)) { roots.add(node.id); changed = true; }
      }
      for (const node of nodes.filter(node => roots.has(node.id) && node.cleanupFailed).reverse()) {
        const fiber = this._domain.fibers.get(node.id);
        if (fiber && !fiber._removedFlag) await steps.retryCleanup(fiber);
      }
      await this._drain(steps, [this._active,...this._pending?.retained ?? []]);
      // Do not reactivate here: recovery transactions only release resources.
      if (!this._pending) { this._active = undefined; this.state = this._accepting ? 'empty' : 'closed'; }
      return this.snapshot();
    }, true);
  }
  dispose() {
    // Validate before closing admission: a managed callback cannot sabotage
    // a live controller by making a rejected reentrant disposal request.
    try { assertDomainMutation(this.ctx, { recovery: true }); } catch (error) { return Promise.reject(error); }
    if (this.state === 'closed') return Promise.resolve();
    if (this._disposal) return this._disposal;
    this._accepting = false;
    const task = this._submit(async steps => {
      await this._drain(steps, [this._active,...this._pending?.retained ?? []]);
      this._active = undefined;
      this._pending = undefined;
      this.state = 'closed';
    }, true);
    this._disposal = task;
    task.catch(error => { this.state = 'blocked'; this.lastReloadFailure = error; this._disposal = undefined; });
    return task;
  }
  inspect() {
    return freeze({...this.snapshot(),images:this._domain.rust.command({op:'module_info'})});
  }
  snapshot() {
    const current = this._active;
    return freeze({ state: this.state, revision: this.revision, retained: true, unloadSupported: false,
      module: current ? structuredClone(current.module.descriptor) : null,
      entries: [...current?.entries ?? []].map(([id,record]) => ({ id, factory: record.recipe.factory,
        factoryRef: current.module.descriptor.factories.find(factory => factory.name === record.recipe.factory).ref,
        fiberId: record.fiber?.id ?? null, state: record.fiber?.state ?? null })),
      retainedFiberIds: [...this._pending?.retained ?? []].map(state => state.fiber?.id).filter(Boolean),
    });
  }
}

export async function loadRustModule(ctx, options) {
  const controller = new RustModuleController(ctx, options);
  try { await controller.reload(options); return controller; }
  catch (error) { error.controller = controller; throw error; }
}
