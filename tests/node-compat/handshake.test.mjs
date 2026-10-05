import test from 'node:test';
import assert from 'node:assert/strict';
import { fileURLToPath } from 'node:url';
import { Context } from '../../packages/compat-cordis/index.js';

for (const fixture of ['wrong-abi', 'wrong-profile', 'missing-driver']) {
  test(`native addon handshake rejects ${fixture} before constructing a driver`, () => {
    const addon = fileURLToPath(new URL(`./fixtures/${fixture}.cjs`, import.meta.url));
    assert.throws(() => new Context({addon}), /Incompatible Cordis addon/);
  });
}
