import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdtempSync, mkdirSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';

const register = fileURLToPath(new URL('../../packages/compat-cordis/register.js', import.meta.url));
const entry = new URL('../../packages/compat-cordis/index.js', import.meta.url).href;

function run(source, { commonJS = false, cwd } = {}) {
  const result = spawnSync(process.execPath, [
    '--import', register,
    `--input-type=${commonJS ? 'commonjs' : 'module'}`,
    '--eval', source,
  ], { cwd, encoding: 'utf8', timeout: 15_000 });
  assert.ifError(result.error);
  assert.equal(result.status, 0, result.stderr);
  return JSON.parse(result.stdout.trim());
}

function sandbox(t) {
  const path = mkdtempSync(join(tmpdir(), 'cordis-native-resolve-'));
  t.after(() => rmSync(path, { recursive: true, force: true }));
  return path;
}

function write(path, relative, text) {
  const destination = join(path, relative);
  mkdirSync(join(destination, '..'), { recursive: true });
  writeFileSync(destination, text);
}

test('preload maps ESM, dynamic import and createRequire to one constructor set', () => {
  assert.deepEqual(run(`
    import assert from 'node:assert/strict';
    import { createRequire } from 'node:module';
    import { Context, Service } from 'cordis';
    import * as direct from ${JSON.stringify(entry)};
    const dynamic = await import('cordis');
    const cjs = createRequire(import.meta.url)('cordis');
    assert.equal(Context, direct.Context);
    assert.equal(Context, dynamic.Context);
    assert.equal(Context, cjs.Context);
    assert.equal(Service, cjs.Service);
    const ctx = new Context();
    await ctx.plugin(c => { c.provide('answer', 42); });
    assert.equal(ctx.answer, 42);
    await ctx.dispose();
    console.log(JSON.stringify({ shared: true }));
  `), { shared: true });
});

test('ordinary CommonJS require and ESM import share the same facade', () => {
  assert.deepEqual(run(`
    const assert = require('node:assert/strict');
    const { Context, Service } = require('cordis');
    import('cordis').then(async esm => {
      assert.equal(Context, esm.Context);
      assert.equal(Service, esm.Service);
      const ctx = new Context();
      await ctx.dispose();
      console.log(JSON.stringify({ shared: true }));
    });
  `, { commonJS: true }), { shared: true });
});

test('nested plugin dependencies cannot select their own bare Cordis implementation', (t) => {
  const path = sandbox(t);
  write(path, 'package.json', '{"type":"module"}');
  write(path, 'node_modules/legacy-plugin/package.json', '{"name":"legacy-plugin","type":"module","exports":"./index.js"}');
  write(path, 'node_modules/legacy-plugin/index.js', `
    import { Service } from 'cordis';
    export default class Greeting extends Service {
      constructor(ctx) { super(ctx, 'greeting'); }
      hello() { return 'loaded unchanged'; }
    }
  `);
  write(path, 'node_modules/legacy-plugin/node_modules/cordis/package.json', '{"name":"cordis","type":"module","exports":"./index.js"}');
  write(path, 'node_modules/legacy-plugin/node_modules/cordis/index.js', 'throw new Error("original scheduler must not load");');
  assert.deepEqual(run(`
    import { Context } from 'cordis';
    const { default: Greeting } = await import('legacy-plugin');
    const ctx = new Context();
    await ctx.plugin(Greeting);
    const greeting = ctx.greeting.hello();
    await ctx.dispose();
    console.log(JSON.stringify({ greeting }));
  `, { cwd: path }), { greeting: 'loaded unchanged' });
});

test('unsupported deep imports and Harness/core identities fail with importer diagnostics', () => {
  for (const specifier of ['cordis/utils', 'cordis/src/fiber', '@cordisjs/core', '@deepseek-ai/cordis', '@deepseek-ai/cordis/utils']) {
    assert.deepEqual(run(`
      import assert from 'node:assert/strict';
      import { createRequire } from 'node:module';
      const specifier = ${JSON.stringify(specifier)};
      await assert.rejects(import(specifier), error => error.code === 'ERR_CORDIS_UNSUPPORTED_IMPORT' && error.message.includes(specifier));
      assert.throws(() => createRequire(import.meta.url)(specifier), { code: 'ERR_CORDIS_UNSUPPORTED_IMPORT' });
      console.log(JSON.stringify({ rejected: true }));
    `), { rejected: true });
  }
});

test('hook preserves unrelated module resolution and allows a duplicate explicit preload', (t) => {
  const path = sandbox(t);
  write(path, 'package.json', '{"type":"module"}');
  write(path, 'value.mjs', 'export const value = 7;');
  assert.deepEqual(run(`
    import assert from 'node:assert/strict';
    import { createRequire } from 'node:module';
    import { readFileSync } from 'node:fs';
    import { value } from './value.mjs';
    const { registration } = await import(${JSON.stringify(new URL('../../packages/compat-cordis/register.js', import.meta.url).href + '?again')});
    assert.equal(readFileSync, createRequire(import.meta.url)('node:fs').readFileSync);
    assert.equal(registration.profile, 'cordis');
    console.log(JSON.stringify({ value }));
  `, { cwd: path }), { value: 7 });
});

test('native Cordis example loads an external module and cleans consumers before its provider', () => {
  const path = fileURLToPath(new URL('../../examples/node/basic.mjs', import.meta.url));
  const result = spawnSync(process.execPath, ['--import', register, path], { encoding: 'utf8', timeout: 15_000 });
  assert.ifError(result.error);
  assert.equal(result.status, 0, result.stderr);
  const lines = result.stdout.trim().split('\n').map(line => JSON.parse(line));
  assert.equal(typeof lines[0].domain, 'string');
  assert.deepEqual(lines[1].trace, ['Hello, Cordis!', 'consumer cleanup: Hello, again!', 'greeter disposed']);
});
