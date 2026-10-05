import { realpath } from 'node:fs/promises';
import { dirname, relative, isAbsolute } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { LoaderError, fileURL } from './config.js';

// A canonical import host, deliberately not a fake ESM cache invalidator.
export class ModuleHost {
  constructor(options = {}) {
    if (options.loadModule !== undefined && typeof options.loadModule !== 'function') throw new TypeError('loadModule must be a function');
    this.rootDirectory = options.rootDirectory;
    this.loadModule = options.loadModule;
  }
  async resolve(specifier, baseURL) {
    if (!specifier.startsWith('.') && !specifier.startsWith('/') && !specifier.startsWith('file:')) {
      throw new LoaderError('MODULE_SPECIFIER', `Use an explicit relative, absolute or file: module path: ${specifier}`);
    }
    const url = fileURL(specifier, baseURL);
    const filename = await realpath(fileURLToPath(url));
    if (this.rootDirectory) {
      const root = await realpath(this.rootDirectory);
      const location = relative(root, filename);
      if (location === '..' || location.startsWith(`..${process.platform === 'win32' ? '\\' : '/'}`) || isAbsolute(location)) throw new LoaderError('MODULE_OUTSIDE_ARTIFACT', `${filename} is outside artifact ${root}`);
    }
    return pathToFileURL(filename).href;
  }
  async load(specifier, baseURL) {
    const url = await this.resolve(specifier, baseURL);
    let namespace, prepared;
    try {
      if (this.loadModule) { prepared = await this.loadModule(url); namespace = prepared?.namespace; }
      else namespace = await import(url);
    }
    catch (cause) { throw new LoaderError('MODULE_IMPORT', `Cannot import ${url}`, { url }, cause); }
    let plugin = this.loadModule ? prepared?.plugin : namespace.default ?? namespace;
    if (plugin?.__esModule) plugin = plugin.default ?? plugin;
    if (!(typeof plugin === 'function' || (plugin && typeof plugin.apply === 'function'))) throw new LoaderError('INVALID_PLUGIN', `${url} must export a function, class, or apply object`, { url });
    const revision = prepared?.revision;
    if (revision !== undefined && typeof revision !== 'string' && !(typeof revision === 'number' && Number.isFinite(revision))) throw new LoaderError('MODULE_REVISION', 'Prepared module revisions must be strings or finite numbers', { url });
    return { plugin, namespace, url, directory: dirname(fileURLToPath(url)), revision };
  }
  async prepare(input) {
    async function visit(nodes, inheritedDisabled = false) {
      return await Promise.all(nodes.map(async node => {
        const disabled = inheritedDisabled || node.options.disabled === true;
        return { ...node, disabled, module: !node.group && !disabled ? await this.load(node.options.name, node.baseURL) : undefined, children: await visit.call(this, node.children, disabled) };
      }));
    }
    return { ...input, tree: await visit.call(this, input.tree) };
  }
  reset() { throw new LoaderError('DOMAIN_RESTART_REQUIRED', 'Native ESM modules cannot be reset in place; use WorkerDomain.reload() with a captured artifact'); }
}
