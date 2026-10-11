import assert from 'node:assert/strict';
import { test } from 'node:test';
import { validateRegistry } from '../../scripts/check-npm-registry.mjs';
import { validateReceipts } from '../../scripts/publish-npm-registry.mjs';

const hash = 'a'.repeat(64);
function record() {
  return {schema:'cordis-verus.npm-registry/v1', sourceCommit:'b'.repeat(40), nativeManifestSha256:hash,
    targets:Object.fromEntries(['darwin-arm64-napi8','darwin-x64-napi8','linux-x64-gnu-napi8','win32-x64-napi8'].map(target => [target,{sha256:hash,sourceDigest:hash}])),
    packages:['cordis','cordis-harness','cordis-loader'].map(name => ({name:'@validation-engineering/'+name, version:'0.1.0', file:name+'.tgz',sha256:hash,integrity:'sha512-YQ==',bytes:42}))};
}
function receipts(source) {
  return Object.keys(source.targets).map(target => ({schema:'cordis-verus.npm-registry-install/v1',status:'passed',target,
    sourceCommit:source.sourceCommit, nativeManifestSha256:source.nativeManifestSha256, packages:structuredClone(source.packages),offlineReinstall:'passed'}));
}
test('universal registry candidates require every platform and safe unique archives', () => {
  validateRegistry(record());
  for (const change of [r=>delete r.targets['win32-x64-napi8'], r=>r.packages[0].file='../escape.tgz',
    r=>r.packages[1].file=r.packages[0].file, r=>r.packages[0].version='9.0.0', r=>r.targets['win32-x64-napi8'].sha256='forged']) {
    const altered=record(); change(altered); assert.throws(()=>validateRegistry(altered));
  }
});
test('publishing rejects missing, stale, changed and failed installation evidence', () => {
  const source=record(); validateReceipts(source,receipts(source));
  for (const change of [r=>r.pop(), r=>r[0].target=r[1].target, r=>r[0].sourceCommit='c'.repeat(40),
    r=>r[0].packages[0].sha256='c'.repeat(64), r=>r[0].status='failed', r=>r[0].offlineReinstall='not_run']) {
    const altered=receipts(source); change(altered); assert.throws(()=>validateReceipts(source,altered));
  }
});
