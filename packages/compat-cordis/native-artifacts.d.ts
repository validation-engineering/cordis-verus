export interface NativeTarget { platform: string; architecture: string; libc?: string | null; nodeApi: number }
export interface DeclaredNativeTarget extends NativeTarget { readonly id: string }
export interface NativeArtifactEntry extends NativeTarget { target: string; kind: 'default-core'; file: string; sha256: string; bytes: number; provenance: string; provenanceSha256: string }
export interface NativeManifest { schema: 'cordis-verus.native-manifest/v1'; package: string; version: string; driverAbi: 1; artifacts: NativeArtifactEntry[] }
export interface VerifiedNativeArtifact { path: string; entry: NativeArtifactEntry; provenance: Record<string, unknown>; provenancePath: string }
export class NativeArtifactError extends Error { readonly code: string; constructor(code: string, message: string, cause?: unknown) }
export const nativeTargets: readonly DeclaredNativeTarget[];
export function sourceDigest(hashes: Record<string, string>): string;
export function currentNativeTarget(): NativeTarget;
export function nativeTargetFor(target?: NativeTarget): DeclaredNativeTarget;
export function verifyNativeManifest(directory?: string): { directory: string; manifest: NativeManifest; manifestPath: string; manifestSha256: string; artifacts: VerifiedNativeArtifact[] };
export function selectNativeArtifact(options?: { directory?: string; target?: NativeTarget }): VerifiedNativeArtifact & { manifest: NativeManifest; manifestSha256: string };
