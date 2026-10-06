import type { Context } from '@cordis-verus/compat-cordis';
import type { JSONValue } from './index.js';
export interface RustModuleArtifact { path: string; sha256: string; }
export interface RustModuleEntry { id: string; factory: string; config?: JSONValue; state?: 'migrate'; }
export interface RustModuleRevision extends RustModuleArtifact { plugins: RustModuleEntry[]; }
export interface RustModuleDescriptor {
  readonly abi: 1;
  readonly module: string;
  readonly pluginId: string;
  readonly buildId: string;
  readonly path: string;
  readonly sha256: string;
  readonly retained: true;
  readonly unloadSupported: false;
  readonly factories: readonly {
    readonly name: string;
    readonly ref: string;
    readonly inject: readonly string[];
    readonly checkpointSchema?: { readonly schema: string; readonly version: number; readonly accepts: readonly number[] } | null;
    readonly services: readonly { readonly name: string; readonly methods: readonly { readonly name: string; readonly kind: 'sync' | 'async' | 'stream' | 'object' }[] }[];
  }[];
}
export interface RustModuleSnapshot {
  readonly state: 'empty' | 'reloading' | 'active' | 'blocked' | 'closed';
  readonly revision: number;
  readonly retained: true;
  readonly unloadSupported: false;
  readonly module: RustModuleDescriptor | null;
  readonly entries: readonly { readonly id: string; readonly factory: string; readonly factoryRef: string; readonly fiberId: string | null; readonly state: number | null }[];
  readonly retainedFiberIds: readonly string[];
}
export interface RustModuleResources {
  readonly instances: number;
  readonly jobs: number;
  readonly retainedInstances: number;
  readonly retainedJobs: number;
  readonly reverseCalls: number;
  readonly retainedReverseCalls: number;
  readonly streams: number;
  readonly objects: number;
  readonly retainedStreams: number;
  readonly retainedObjects: number;
}
export interface RustModuleInventory {
  readonly retained: true;
  readonly unloadSupported: false;
  /** Shared by environments using the same resident addon image. */
  readonly retainedImageCount: number;
  readonly retainedImageLimit: number;
  /** Modules registered in this Context's native Driver. */
  readonly checkpoints: { readonly tokens: number; readonly bytes: number; readonly tokenLimit: number; readonly byteLimit: number };
  readonly modules: readonly (RustModuleDescriptor & { readonly resources: RustModuleResources })[];
}
export interface RustModuleInspection extends RustModuleSnapshot { readonly images: RustModuleInventory; }
/** Reloads trusted cdylib code in one resident native Driver; old images remain mapped. */
export class RustModuleController {
  constructor(context: Context, options: { plugins: RustModuleEntry[] });
  readonly ctx: Context;
  readonly state: RustModuleSnapshot['state'];
  readonly revision: number;
  readonly lastReloadFailure: Error | undefined;
  /** Replace code, preserving the latest successfully committed recipes in FIFO order. */
  reload(artifact: RustModuleArtifact): Promise<RustModuleSnapshot>;
  /** Reconcile code and captured recipes with rollback. Empty plugins disables the owned group. */
  reconcile(revision: RustModuleRevision): Promise<RustModuleSnapshot>;
  /** Explicit cleanup retry only. The next reload or reconcile performs restoration. */
  retryCleanup(): Promise<RustModuleSnapshot>;
  dispose(): Promise<void>;
  snapshot(): RustModuleSnapshot;
  /** Query current native resource counts and the shared resident-image budget. */
  inspect(): RustModuleInspection;
}
/** On activation failure, the rejected Error.controller retains cleanup/recovery access. */
export function loadRustModule(context: Context, options: RustModuleRevision): Promise<RustModuleController>;
