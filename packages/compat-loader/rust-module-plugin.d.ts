import type { Context, Fiber, Plugin } from '@cordis-verus/compat-cordis';
import type { RustModuleRevision } from './rust-module.js';

export interface RustModulePlugin extends Plugin.Object<RustModuleRevision> {
  readonly name: string;
  readonly Config: {
    readonly '~standard': {
      readonly version: 1;
      readonly vendor: string;
      /** Synchronous native artifact preflight; returns a frozen JSON snapshot. */
      validate(value: unknown): { value: RustModuleRevision } | { issues: readonly { message: string }[] };
    };
  };
}
/** Create one entry factory bound to this Context domain and owner activation.
 * The first successful validation pins module identity unless pluginId is given.
 * Config accepts path, sha256 and plugins; an empty list mounts no children.
 * Preserve Config's returned object when composing an outer schema. Activation
 * consumes that prepared value and cannot begin a host reload transaction.
 * Loader/config-editor code owns failed-update restoration; this ordinary plugin
 * does not independently roll back a failed setup or coordinate its consumers.
 * Keep artifacts immutable so a later restart can revalidate the same bytes.
 */
export function createRustModulePlugin(context: Context, options?: { name?: string; pluginId?: string }): RustModulePlugin;

/** In an existing host domain transaction, retain the original state until the
 * native entry and all required consumers are accepted. Payloads stay in memory.
 * rollback selects that original state for the host's subsequent config restore.
 * Commit only after all new or restored consumers pass acceptance. Always release
 * in finally; without commit the original checkpoint remains available for recovery. */
export function beginRustModuleMigration(context: Context, fiber: Fiber): {
  commit(): void;
  rollback(): void;
  release(): void;
};
