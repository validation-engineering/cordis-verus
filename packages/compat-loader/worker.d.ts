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
export class WorkerDomain {
  constructor(options?: WorkerDomainOptions);
  readonly state: 'empty' | 'reloading' | 'active' | 'blocked' | 'closed' | 'abandoned';
  readonly lastRecovery?: { restored: true; digest: string; cause: unknown };
  load(directory: string): Promise<{ digest: string; diagnostics: EntryDiagnostic[] }>;
  reload(directory?: string): Promise<{ digest: string; diagnostics: EntryDiagnostic[] }>;
  call(service: string, method: string, ...args: JSONValue[]): Promise<JSONValue>;
  diagnostics(): Promise<EntryDiagnostic[]>;
  dispose(): Promise<void>;
  abandon(): Promise<{ abandoned: true; cleanupConfirmed: false }>;
}
