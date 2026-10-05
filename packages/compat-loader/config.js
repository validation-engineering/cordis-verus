import { readFile, realpath } from 'node:fs/promises';
import { isAbsolute, resolve, relative } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

export class LoaderError extends Error {
  constructor(code, message, details = {}, cause) {
    super(message, cause === undefined ? undefined : { cause });
    this.name = 'LoaderError';
    this.code = code;
    this.details = details;
  }
}

export function jsonValue(value, path = '$', seen = new Set()) {
  if (value === null || typeof value === 'string' || typeof value === 'boolean') return value;
  if (typeof value === 'number' && Number.isFinite(value)) return value;
  if (typeof value !== 'object' || seen.has(value)) throw new LoaderError('INVALID_CONFIG', `${path} must contain finite JSON values only`);
  if (!Array.isArray(value) && Object.getPrototypeOf(value) !== Object.prototype && Object.getPrototypeOf(value) !== null) {
    throw new LoaderError('INVALID_CONFIG', `${path} must be a plain JSON object`);
  }
  seen.add(value);
  const result = Array.isArray(value) ? value.map((item, index) => jsonValue(item, `${path}[${index}]`, seen)) : Object.fromEntries(Object.entries(value).map(([key, item]) => [key, jsonValue(item, `${path}.${key}`, seen)]));
  seen.delete(value);
  return result;
}

function freezeJSON(value) {
  if (value && typeof value === 'object') { for (const item of Object.values(value)) freezeJSON(item); Object.freeze(value); }
  return value;
}

export function fileURL(input, baseURL = pathToFileURL(`${process.cwd()}/`).href) {
  if (input instanceof URL) input = input.href;
  if (typeof input !== 'string' || !input) throw new LoaderError('INVALID_PATH', 'Expected a file path or file URL');
  const url = input.startsWith('file:') ? new URL(input) : isAbsolute(input) ? pathToFileURL(input) : new URL(input, baseURL);
  if (url.protocol !== 'file:' || url.search || url.hash) throw new LoaderError('INVALID_PATH', 'Only ordinary file paths without query or fragment are supported');
  return url;
}

function object(value, at) {
  if (!value || typeof value !== 'object' || Array.isArray(value)) throw new LoaderError('INVALID_CONFIG', `${at} must be an object`);
}

export async function readTree(input, options = {}) {
  const baseURL = options.baseURL ?? pathToFileURL(`${resolve('.')}/`).href;
  const root = options.rootDirectory ? await realpath(options.rootDirectory) : undefined;
  const files = new Set();
  const ids = new Set();
  const stack = [];
  async function fromFile(filename, parent, base) {
    const url = fileURL(filename, base);
    const canonicalPath = await realpath(fileURLToPath(url));
    if (root) {
      const location = relative(root, canonicalPath);
      if (location === '..' || location.startsWith(`..${process.platform === 'win32' ? '\\' : '/'}`) || isAbsolute(location)) throw new LoaderError('CONFIG_OUTSIDE_ARTIFACT', `${canonicalPath} is outside artifact ${root}`);
    }
    const canonical = pathToFileURL(canonicalPath).href;
    if (stack.includes(canonical)) throw new LoaderError('INCLUDE_CYCLE', `Include cycle: ${[...stack, canonical].join(' -> ')}`);
    if (stack.length >= 64) throw new LoaderError('INCLUDE_DEPTH', 'Include nesting exceeds 64 files');
    stack.push(canonical);
    files.add(canonical);
    let raw;
    try { raw = JSON.parse(await readFile(new URL(canonical), 'utf8')); }
    catch (cause) { throw new LoaderError('CONFIG_READ', `Cannot read JSON configuration ${canonical}`, { file: canonical }, cause); }
    try { return await entries(raw, parent, canonical); } finally { stack.pop(); }
  }
  async function entries(tree, parent, base) {
    if (!Array.isArray(tree)) {
      object(tree, 'configuration');
      if (Object.keys(tree).some(key => key !== 'entries')) throw new LoaderError('INVALID_CONFIG', 'The config object supports only entries');
      tree = tree.entries;
    }
    if (!Array.isArray(tree)) throw new LoaderError('INVALID_CONFIG', 'Configuration must be an entries array');
    const result = [];
    for (const raw of tree) {
      object(raw, 'entry');
      const item = freezeJSON(jsonValue(raw));
      const allowed = ['id', 'name', 'config', 'inject', 'isolate', 'intercept', 'disabled', 'group', 'entries', 'include'];
      const unknown = Object.keys(item).filter(key => !allowed.includes(key));
      if (unknown.length) throw new LoaderError('INVALID_CONFIG', `Unknown entry fields: ${unknown.join(', ')}`);
      if (typeof item.id !== 'string' || !/^[A-Za-z0-9_.-]+$/.test(item.id)) throw new LoaderError('INVALID_CONFIG', 'Every entry needs a stable id containing letters, digits, _, - or .');
      const id = parent ? `${parent}/${item.id}` : item.id;
      if (ids.has(id)) throw new LoaderError('DUPLICATE_ENTRY', `Duplicate entry id ${id}`);
      ids.add(id);
      if (item.disabled !== undefined && typeof item.disabled !== 'boolean') throw new LoaderError('INVALID_CONFIG', `${id}.disabled must be boolean`);
      if (item.group !== undefined && typeof item.group !== 'boolean') throw new LoaderError('INVALID_CONFIG', `${id}.group must be boolean`);
      if (item.inject !== undefined && !(Array.isArray(item.inject) ? item.inject.every(name => typeof name === 'string' && name.length) : item.inject && typeof item.inject === 'object')) throw new LoaderError('INVALID_CONFIG', `${id}.inject must be service names or a config object`);
      if (item.intercept !== undefined) object(item.intercept, `${id}.intercept`);
      if (item.isolate !== undefined && !(Array.isArray(item.isolate) ? item.isolate.every(name => typeof name === 'string' && name.length) : item.isolate && typeof item.isolate === 'object' && Object.values(item.isolate).every(label => label === true || typeof label === 'string'))) throw new LoaderError('INVALID_CONFIG', `${id}.isolate must be service names or name-to-label mapping`);
      const group = item.group === true || item.include !== undefined;
      if (group) {
        if (item.name !== undefined || item.config !== undefined) throw new LoaderError('INVALID_CONFIG', `${id}: a group cannot have name or config`);
        if (item.include !== undefined && item.entries !== undefined) throw new LoaderError('INVALID_CONFIG', `${id}: include and entries are mutually exclusive`);
      } else if (typeof item.name !== 'string' || !item.name || item.entries !== undefined) throw new LoaderError('INVALID_CONFIG', `${id}: a plugin requires name; children require group: true`);
      const children = group ? item.include !== undefined ? await fromFile(item.include, id, base) : await entries(item.entries ?? [], id, base) : [];
      result.push({ id, options: item, baseURL: base, group, children });
    }
    return result;
  }
  const tree = typeof input === 'string' || input instanceof URL ? await fromFile(input, '', baseURL) : await entries(jsonValue(input), '', baseURL);
  return { tree, files: [...files] };
}
