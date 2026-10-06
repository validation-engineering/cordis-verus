import type { JSONValue } from './index.js';
import type { WorkerDomainOptions, ModuleGraphSnapshot, ModuleReloadPlan } from './worker.js';
export interface ProcessHostOptions { directory: string; entry: string; allowPending: boolean; }
/** Expose cleanup immediately, before starting asynchronous application initialization. */
export interface ProcessHost {
  ready: PromiseLike<void>;
  call(service: string, method: string, args: JSONValue[]): JSONValue | Promise<JSONValue>;
  diagnostics(): JSONValue | Promise<JSONValue>;
  close(): void | Promise<void>;
}
export interface HostProvenance { readonly url: string; readonly sha256: string; }
export interface ProcessDomainOptions extends WorkerDomainOptions {
  /** Trusted external adapter exporting synchronous createHost(): ProcessHost. */
  hostModule?: string | URL;
  /** Persistent application working directory. Default: private captured artifact copy. */
  cwd?: string;
  /** Overrides inherited environment. NODE_OPTIONS and NODE_PATH are always removed. */
  env?: Record<string, string | undefined>;
  stdio?: 'inherit' | 'ignore';
  /** Receives child output chunks instead of inheriting streams; contents are never retained by the supervisor. */
  onOutput?: (chunk: { stream: 'stdout' | 'stderr'; data: string }) => void;
}
export interface ProcessReloadPlan extends Omit<ModuleReloadPlan, 'strategy'> {
  strategy: 'process-restart';
  host?: HostProvenance;
}
export interface ProcessLoadResult { digest: string; diagnostics: JSONValue; plan: ProcessReloadPlan; }
export class ProcessDomain {
  constructor(options?: ProcessDomainOptions);
  readonly state: 'empty' | 'reloading' | 'active' | 'blocked' | 'closed' | 'abandoned';
  readonly pid?: number;
  readonly hostProvenance?: HostProvenance;
  readonly lastRecovery?: { restored: true; digest: string; cause: unknown };
  load(directory: string): Promise<ProcessLoadResult>;
  reload(directory?: string): Promise<ProcessLoadResult>;
  planReload(directory?: string): Promise<ProcessReloadPlan>;
  moduleGraph(): Promise<ModuleGraphSnapshot>;
  call(service: string, method: string, ...args: JSONValue[]): Promise<JSONValue>;
  diagnostics(): Promise<JSONValue>;
  dispose(): Promise<void>;
  abandon(): Promise<{ abandoned: true; cleanupConfirmed: false }>;
}
