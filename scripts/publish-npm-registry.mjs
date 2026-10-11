#!/usr/bin/env node
/** Publish only the exact universal archives installed successfully on every host. */
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { lstat, readFile, readdir } from 'node:fs/promises';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { npmCommand } from './install-cordis.mjs';
import { validateRegistry } from './check-npm-registry.mjs';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
export function validateReceipts(record, receipts) {
  assert.equal(receipts.length, 4, 'All four installation receipts are required');
  assert.deepEqual(receipts.map(item => item.target).sort(), Object.keys(record.targets).sort());
  for (const receipt of receipts) {
    assert.equal(receipt.schema, 'cordis-verus.npm-registry-install/v1');
    assert.equal(receipt.status, 'passed');
    assert.equal(receipt.offlineReinstall, 'passed');
    assert.equal(receipt.sourceCommit, record.sourceCommit);
    assert.equal(receipt.nativeManifestSha256, record.nativeManifestSha256);
    assert.deepEqual(receipt.packages, record.packages, 'Installation receipts must bind the exact registry archives');
  }
}
async function receiptsUnder(directory) {
  const result = [];
  for (const entry of await readdir(directory, {withFileTypes:true})) {
    assert(!entry.isSymbolicLink(), 'Receipt paths must not be symlinks');
    const path = join(directory, entry.name);
    if (entry.isDirectory()) result.push(...await receiptsUnder(path));
    else if (entry.name.endsWith('.json')) result.push(JSON.parse(await readFile(path, 'utf8')));
  }
  return result;
}
function capture(command) {
  const result = spawnSync(command[0], command.slice(1), {cwd:root, encoding:'utf8', timeout:120000});
  if (result.error) throw result.error;
  assert.equal(result.status, 0, `${command[0]} failed:\n${result.stderr}`);
  return result.stdout.trim();
}
async function main() {
  const args = process.argv.slice(2), options = {};
  while (args.length) {
    const key = args.shift();
    if (key === '--publish') { options.publish = true; continue; }
    assert(['--from-directory','--receipts'].includes(key) && args.length,
      'Usage: publish-npm-registry.mjs --from-directory ASSETS --receipts RECEIPTS [--publish]');
    assert(!(key in options), 'Duplicate argument'); options[key] = args.shift();
  }
  assert(options['--from-directory'] && options['--receipts'], 'Candidates and installation receipts are required');
  const directory = resolve(options['--from-directory']);
  const record = validateRegistry(JSON.parse(await readFile(join(directory, 'npm-registry.json'), 'utf8')));
  assert.equal(capture(['git','rev-parse','HEAD']), record.sourceCommit, 'Check out the exact release source commit');
  assert.equal(capture(['git','status','--porcelain']), '', 'Publication requires a clean checkout');
  validateReceipts(record, await receiptsUnder(resolve(options['--receipts'])));
  const npm = npmCommand();
  // Validate every byte before the first irreversible registry upload.
  for (const item of record.packages) {
    const path = join(directory, item.file), info = await lstat(path);
    assert(info.isFile() && !info.isSymbolicLink());
    const bytes = await readFile(path);
    assert.equal(bytes.length, item.bytes);
    assert.equal(createHash('sha256').update(bytes).digest('hex'), item.sha256);
    assert.equal('sha512-'+createHash('sha512').update(bytes).digest('base64'), item.integrity);
  }
  const missing = [];
  for (const item of record.packages) {
    const query = spawnSync(npm[0], [...npm.slice(1),'view',`${item.name}@${item.version}`,'dist.integrity','--json','--registry=https://registry.npmjs.org/'], {encoding:'utf8',timeout:60000});
    if (query.error) throw query.error;
    if (query.status === 0) {
      assert.equal(JSON.parse(query.stdout), item.integrity, 'An existing registry version has different bytes');
      console.log(`Already published with identical integrity: ${item.name}@${item.version}`);
    } else {
      let error; try { error = JSON.parse(query.stdout).error; } catch { /* Fail closed below. */ }
      assert.equal(error?.code, 'E404', `Cannot establish registry availability: ${query.stderr}`);
      missing.push(item);
    }
  }
  for (const item of missing) {
    const command = [...npm, 'publish', join(directory,item.file), '--ignore-scripts','--access','public','--registry=https://registry.npmjs.org/', ...(options.publish ? [] : ['--dry-run'])];
    const result = spawnSync(command[0], command.slice(1), {cwd:root,stdio:'inherit'});
    if (result.error) throw result.error;
    assert.equal(result.status, 0, 'npm publication failed; accepted archive hashes are retained for retry');
  }
  console.log(options.publish ? 'Registry upload complete. Run the clean registry consumer check next.' : 'Dry run complete; no package uploaded. Use --publish to upload these exact archives.');
}
if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) await main();
