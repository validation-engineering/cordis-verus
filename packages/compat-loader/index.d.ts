import type { Context, Fiber, Plugin } from '@cordis-verus/compat-cordis';
export type JSONValue = null | boolean | number | string | JSONValue[] | { [key: string]: JSONValue };
export type Injection = string[] | Record<string, JSONValue>;
export type Isolation = string[] | Record<string, true | string>;
export interface EntryOptions {
  id: string;
  name?: string;
  config?: JSONValue;
  inject?: Injection;
  isolate?: Isolation;
  intercept?: Record<string, JSONValue>;
  disabled?: boolean;
  group?: boolean;
  entries?: EntryOptions[];
  include?: string;
}
export type ConfigTree = EntryOptions[] | { entries: EntryOptions[] };
export type EntryState = 'pending' | 'loading' | 'active' | 'failed' | 'disposed' | 'unloading' | 'disabled';
export interface EntryDiagnostic {
  id: string;
  parentId: string | null;
  moduleURL: string | null;
  state: EntryState;
  unavailableServices: string[];
  fiberId?: string;
}
/** Already prepared executable factory; this does not invalidate Node module caches. */
export interface PreparedModule { plugin: Plugin; namespace?: unknown; revision?: string | number; }
export interface LoadedModule extends PreparedModule { url: string; directory: string; }
export interface EntryNode {
  id: string;
  options: EntryOptions;
  baseURL: string;
  group: boolean;
  children: EntryNode[];
  disabled?: boolean;
  module?: LoadedModule;
}
export interface Recipe { tree: EntryNode[]; files: string[]; }
export class LoaderError extends Error {
  readonly code: string;
  readonly details: Record<string, unknown>;
  constructor(code: string, message: string, details?: Record<string, unknown>, cause?: unknown);
}
export class ModuleHost {
  constructor(options?: { rootDirectory?: string; loadModule?: (canonicalURL: string) => PreparedModule | Promise<PreparedModule> });
  resolve(specifier: string, baseURL: string): Promise<string>;
  load(specifier: string, baseURL: string): Promise<LoadedModule>;
  prepare(input: Recipe): Promise<Recipe>;
  reset(): never;
}
export function readConfig(input: string | URL | ConfigTree, options?: { baseURL?: string; rootDirectory?: string }): Promise<Recipe>;
export class Include {
  static read(filename: string | URL, options?: { baseURL?: string; rootDirectory?: string }): Promise<Recipe>;
}
export class Entry {
  readonly id: string;
  readonly parentId?: string;
  readonly options: Readonly<EntryOptions>;
  readonly disabled: boolean;
  readonly moduleURL?: string;
  readonly fiber?: Fiber;
  readonly context?: Context;
  readonly state: EntryState;
}
export class Loader {
  constructor(context?: Context, options?: { moduleHost?: ModuleHost; baseURL?: string; allowPending?: boolean });
  readonly ctx: Context;
  readonly moduleHost: ModuleHost;
  readonly state: 'empty' | 'reloading' | 'active' | 'blocked' | 'closed';
  readonly revision: number;
  readonly lastRecovery?: { restored: true; cause: unknown };
  entries(): IterableIterator<Entry>;
  resolve(id: string): Entry;
  apply(tree: ConfigTree, options?: { baseURL?: string }): Promise<EntryDiagnostic[]>;
  loadFile(filename: string | URL): Promise<EntryDiagnostic[]>;
  reload(): Promise<EntryDiagnostic[]>;
  update(id: string, patch: Partial<Pick<EntryOptions, 'name' | 'config' | 'inject' | 'isolate' | 'intercept' | 'disabled'>>): Promise<EntryDiagnostic[]>;
  setEnabled(id: string, enabled: boolean): Promise<EntryDiagnostic[]>;
  diagnostics(): EntryDiagnostic[];
  retryCleanup(): Promise<void>;
  dispose(): Promise<void>;
}
