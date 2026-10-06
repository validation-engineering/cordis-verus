import { isAbsolute } from 'node:path';
import { FiberState } from '@cordis-verus/compat-cordis';
import { LoaderError } from './config.js';
import { StateJournal, checkpointsOf, sourceOf, validateStateRecipe, validateStateTransfer } from './rust-module-state.js';

const fail = (code, message) => new LoaderError(code, message);
const freeze = value => {
  if (value && typeof value === 'object') {
    for (const child of Object.values(value)) freeze(child);
    Object.freeze(value);
  }
  return value;
};

// State lives in the same outer Fiber across episodes. It never enters the
// serializable config or changes service/child capability identities.
const ledgers = new WeakMap();
const prune = ledger => ledger.journal.retain(checkpointsOf(ledger.current), ledger.recovery?.checkpoints);

/** Pin the pre-update state until the host has checked every required consumer.
 * Invoke inside the host's existing domain transaction. rollback selects the
 * same pre-update bundle; it does not itself mutate the official Loader. */
export function beginRustModuleMigration(ctx, fiber) {
  const checkTransaction = ctx.fiber._domain.transactionGuard();
  fiber = fiber?.ctx?.fiber ?? fiber;
  if (fiber?._domain !== ctx.fiber._domain || fiber._removedFlag || fiber.uid === null) {
    throw fail('NATIVE_MODULE_CONTEXT', 'A live native entry in this Context domain is required');
  }
  const ledger = ledgers.get(fiber);
  if (!ledger) throw fail('NATIVE_MODULE_UNPREPARED', 'Native module entry has not activated');
  if (ledger.transaction) throw fail('NATIVE_MODULE_MIGRATION_BUSY', 'This entry already has a migration transaction');
  const source = ledger.recovery ?? sourceOf(ledger.current);
  const transaction = { source };
  ledger.transaction = transaction;
  const unpin = ledger.journal.pin(source?.checkpoints);
  let released = false;
  const check = () => {
    if (released || ledger.transaction !== transaction || fiber._removedFlag) throw fail('NATIVE_MODULE_MIGRATION_CLOSED', 'Migration transaction has ended');
    checkTransaction();
  };
  const finish = () => {
    released = true; unpin(); ledger.transaction = undefined; prune(ledger);
  };
  return Object.freeze({
    commit() {
      check();
      if (fiber.state !== FiberState.ACTIVE || [...ledger.current?.entries.values() ?? []].some(record => record.fiber?.state !== FiberState.ACTIVE)) {
        throw fail('NATIVE_MODULE_NOT_ACTIVE', 'A migration can only accept an active native group');
      }
      ledger.recovery = undefined; finish();
    },
    rollback() { check(); ledger.recovery = source; },
    release() {
      if (released) return;
      checkTransaction();
      if (ledger.transaction !== transaction) throw fail('NATIVE_MODULE_MIGRATION_CLOSED', 'Migration transaction has ended');
      // Only the host can confirm that all required consumers were restored.
      // Reaching Active in this native group never implies application success.
      ledger.recovery = fiber._removedFlag ? undefined : source;
      finish();
    },
  });
}

/** A normal owned plugin, suitable for an official Loader entry.
 * Config validation loads and checks the candidate before Fiber.update retires
 * the old episode. apply only mounts prepared factories: it never enters a host
 * transaction or lends coordinator authority to a managed callback.
 */
export function createRustModulePlugin(ctx, options = {}) {
  const owner = ctx?.fiber, domain = owner?._domain;
  if (!domain?.rust || !owner || owner.uid === null || owner._removedFlag) {
    throw fail('NATIVE_MODULE_CONTEXT', 'A live native Cordis Context is required');
  }
  const generation = owner._generation;
  if (options.pluginId !== undefined && (typeof options.pluginId !== 'string' || !options.pluginId)) {
    throw fail('NATIVE_MODULE_IDENTITY', 'pluginId must be a nonempty string');
  }
  const name = options.name ?? 'native-rust-module';
  if (typeof name !== 'string' || !name) throw fail('NATIVE_MODULE_NAME', 'Plugin name must be nonempty');
  const prepared = new WeakMap();
  let identity = options.pluginId;
  const check = () => {
    if (owner.uid === null || owner._removedFlag || owner._generation !== generation
      || [FiberState.DISPOSED, FiberState.UNLOADING].includes(owner.state)) {
      throw fail('NATIVE_MODULE_OWNER_REMOVED', 'Native module plugin belongs to a removed or previous owner activation');
    }
  };
  const Config = Object.freeze({ '~standard': Object.freeze({
    version: 1,
    vendor: '@cordis-verus/compat-loader',
    validate(raw) {
      try {
        check();
        // The Rust transport's copier rejects accessors, proxies, cycles and
        // executable coercions before native code is loaded.
        const config = domain.rust.jsonValue(raw);
        if (!config || typeof config !== 'object' || Array.isArray(config)
          || Object.keys(config).some(key => !['path', 'sha256', 'plugins'].includes(key))) {
          throw fail('NATIVE_MODULE_CONFIG', 'Expected path, sha256, and plugins');
        }
        if (typeof config.path !== 'string' || !isAbsolute(config.path) || config.path.includes('\0')) {
          throw fail('NATIVE_MODULE_PATH', 'Native modules require an absolute artifact path');
        }
        if (typeof config.sha256 !== 'string' || !/^[a-f0-9]{64}$/.test(config.sha256)) {
          throw fail('NATIVE_MODULE_DIGEST', 'Native modules require an expected lowercase SHA-256 digest');
        }
        if (!Array.isArray(config.plugins)) throw fail('NATIVE_MODULE_RECIPE', 'plugins must be an array');
        const ids = new Set();
        for (const recipe of config.plugins) {
          if (!recipe || typeof recipe !== 'object' || Array.isArray(recipe)
            || typeof recipe.id !== 'string' || !recipe.id || ids.has(recipe.id)
            || typeof recipe.factory !== 'string' || !recipe.factory
            || Object.keys(recipe).some(key => !['id', 'factory', 'config', 'state'].includes(key))) {
            throw fail('NATIVE_MODULE_RECIPE', 'Entries require unique ids, factory names, and optional JSON config');
          }
          ids.add(recipe.id);
        }
        const module = domain.rust.loadModule({ path: config.path, sha256: config.sha256 });
        if (identity !== undefined && module.descriptor.pluginId !== identity) {
          throw fail('NATIVE_MODULE_IDENTITY', 'Candidate plugin identity differs from this native entry');
        }
        for (const recipe of config.plugins) {
          if (!module.factories.has(recipe.factory)) throw fail('NATIVE_MODULE_FACTORY', `Candidate does not export ${recipe.factory}`);
          validateStateRecipe(module, recipe);
        }
        identity ??= module.descriptor.pluginId;
        freeze(config);
        prepared.set(config, module);
        return { value: config };
      } catch (error) {
        return { issues: [{ message: error instanceof Error ? error.message : String(error) }] };
      }
    },
  }) });
  return Object.freeze({ name, Config,
    async apply(child, config) {
      check();
      if (child?.fiber?._domain !== domain) throw fail('FOREIGN_DOMAIN', 'Prepared native plugin belongs to a different Context domain');
      const module = prepared.get(config);
      if (!module) throw fail('NATIVE_MODULE_UNPREPARED', 'Keep the exact value returned by the native module Config validator');
      let ledger = ledgers.get(child.fiber);
      if (!ledger) {
        ledger = { journal: new StateJournal(domain.rust) };
        ledgers.set(child.fiber, ledger);
        domain.rust.onRemoved(child.fiber, () => { ledger.journal.clear(); ledgers.delete(child.fiber); });
      }
      const source = ledger.transaction?.source ?? ledger.recovery ?? sourceOf(ledger.current);
      const state = { module, recipes: config.plugins, entries: new Map() };
      validateStateTransfer(source, state);
      child.on('internal/update', (next, noSave, proceed) => {
        const nextModule = prepared.get(next);
        if (!nextModule) throw fail('NATIVE_MODULE_UNPREPARED', 'Native update must use prepared config');
        validateStateTransfer(ledger.transaction?.source ?? ledger.recovery ?? sourceOf(ledger.current), { module: nextModule, recipes: next.plugins });
        return proceed();
      });
      const fibers = [], tasks = [];
      let failure;
      try {
        for (const recipe of config.plugins) {
          const record = { recipe };
          state.entries.set(recipe.id, record);
          const plugin = ledger.journal.plugin(module, recipe, record, source);
          const known = new Set(child.registry.get(plugin)?.fibers ?? []);
          let fiber;
          try { fiber = child.plugin(plugin, recipe.config).ctx.fiber; }
          catch (error) {
            record.fiber = [...child.registry.get(plugin)?.fibers ?? []].find(fiber => !known.has(fiber) && fiber.parent.fiber === child.fiber);
            throw error;
          }
          record.fiber = fiber;
          fibers.push(fiber);
          const task = fiber.await();
          task.catch(() => {});
          tasks.push(task);
        }
      } catch (error) { failure = error; }
      const results = await Promise.allSettled(tasks);
      failure ??= results.find(result => result.status === 'rejected')?.reason;
      if (failure) {
        // Captures belonging to a partly started candidate are not a replacement
        // for the committed source. They remain owned until real removal.
        for (const record of state.entries.values()) if (record.fiber) domain.rust.onRemoved(record.fiber, () => ledger.journal.drop(record.checkpoint));
        throw failure;
      }
      if (fibers.some(fiber => fiber.state !== FiberState.ACTIVE)) {
        for (const record of state.entries.values()) if (record.fiber) domain.rust.onRemoved(record.fiber, () => ledger.journal.drop(record.checkpoint));
        throw fail('NATIVE_MODULE_NOT_ACTIVE', 'Native module children did not all reach Active');
      }
      ledger.current = state;
      if (!ledger.transaction) ledger.recovery = undefined;
      prune(ledger);
    },
  });
}
