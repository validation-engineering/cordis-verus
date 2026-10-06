import type { EntryDiagnostic, JSONValue } from './index.js';
export interface ArtifactOptions { maxBytes?: number; maxFiles?: number; }
export class Artifact {
  static capture(directory: string, options?: ArtifactOptions): Promise<Artifact>;
  readonly source: string;
  readonly root: string;
  readonly digest: string;
  readonly closed: boolean;
  readonly manifest: readonly { readonly name: string; readonly mode: number; readonly bytes: number; readonly sha256: string }[];
  launch(entry: string): Promise<{ directory: string; entry: string }>;
  dispose(): Promise<void>;
}
export interface WorkerDomainOptions extends ArtifactOptions {
  entry?: string;
  /** Timeout detects an unknown outcome; it never confirms cleanup. Default 30000 ms. */
  timeout?: number;
  allowPending?: boolean;
}
/** Runtime observations only; unexecuted dynamic imports are not enumerated. */
export interface ModuleGraphSnapshot {
  coverage: 'observed';
  modules: { id: string; path: string; format: string }[];
  edges: { from: string; to: string; specifier: string | null; source: 'resolution' | 'require-cache'; kind: 'import' | 'require' }[];
  roots: string[];
}
export interface ModuleReloadPlan {
  strategy: 'worker-restart' | 'process-restart-required';
  coverage: 'observed';
  currentDigest: string | null;
  candidateDigest: string;
  /** reload() still requests an explicit restart when bytes are identical. */
  identical: boolean;
  changedFiles: { path: string; change: 'added' | 'removed' | 'modified'; kind: 'module' | 'native-addon' | 'metadata' | 'resource' }[];
  changedDirectories: string[];
  affectedModules: string[];
  unobservedChanges: string[];
  nativeAddons: string[];
}
export interface WorkerLoadResult { digest: string; diagnostics: EntryDiagnostic[]; plan: ModuleReloadPlan; }
export class WorkerDomain {
  constructor(options?: WorkerDomainOptions);
  readonly state: 'empty' | 'reloading' | 'active' | 'blocked' | 'closed' | 'abandoned';
  readonly lastRecovery?: { restored: true; digest: string; cause: unknown };
  load(directory: string): Promise<WorkerLoadResult>;
  reload(directory?: string): Promise<WorkerLoadResult>;
  /** Does not execute candidate modules. A later reload captures the source again. */
  planReload(directory?: string): Promise<ModuleReloadPlan>;
  moduleGraph(): Promise<ModuleGraphSnapshot>;
  call(service: string, method: string, ...args: JSONValue[]): Promise<JSONValue>;
  diagnostics(): Promise<EntryDiagnostic[]>;
  dispose(): Promise<void>;
  abandon(): Promise<{ abandoned: true; cleanupConfirmed: false }>;
}
