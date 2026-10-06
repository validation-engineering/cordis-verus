import { registerHooks, isBuiltin, createRequire } from 'node:module';
import { realpathSync } from 'node:fs';
import { relative, isAbsolute, extname } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { LoaderError } from './config.js';

const posix = path => path.replaceAll('\\', '/');
const require = createRequire(import.meta.url);
const facadeURLs = new Set([
  import.meta.resolve('@cordis-verus/compat-cordis'),
  pathToFileURL(require.resolve('@cordis-verus/compat-cordis')).href,
]);

/** Observed Node module edges in one Worker, not a static parser or cache reset. */
export class ModuleGraph {
  constructor(directory) {
    this.root = realpathSync(directory);
    this.modules = new Map();
    this.edges = new Map();
    this.roots = new Set();
  }
  location(url) {
    if (!url?.startsWith('file:')) return undefined;
    const parsed = new URL(url);
    const path = relative(this.root, fileURLToPath(parsed));
    if (!path || path === '..' || path.startsWith(`..${process.platform === 'win32' ? '\\' : '/'}`) || isAbsolute(path)) return undefined;
    return { id: posix(path) + parsed.search + parsed.hash, path: posix(path) };
  }
  observe(url, format) {
    const location = this.location(url);
    if (!location) return undefined;
    const previous = this.modules.get(location.id);
    this.modules.set(location.id, { ...location, format: format ?? previous?.format ?? 'unknown' });
    return location;
  }
  install() {
    this.hooks = registerHooks({
      resolve: (specifier, context, nextResolve) => {
        const result = nextResolve(specifier, context);
        const parent = this.location(context.parentURL);
        const child = this.location(result.url);
        if (parent) {
          let target;
          if (child) target = child.id;
          else if (isBuiltin(result.url)) target = result.url.startsWith('node:') ? result.url : `node:${result.url}`;
          else if (specifier === 'cordis' && facadeURLs.has(result.url)) target = 'host:cordis';
          else throw new LoaderError('MODULE_OUTSIDE_ARTIFACT', `Project dependency ${specifier} resolves outside its captured artifact`, { parent: parent.id, url: result.url });
          if (child?.path.endsWith('.node')) throw new LoaderError('PROCESS_RESTART_REQUIRED', 'Application native addons require a separately certified process restart boundary', { file: child.path });
          this.observe(context.parentURL);
          const edge = { from: parent.id, to: target, specifier, source: 'resolution', kind: context.conditions.includes('require') ? 'require' : 'import' };
          this.edges.set(JSON.stringify(edge), edge);
        } else if (child) this.roots.add(child.id);
        this.observe(result.url, result.format);
        return result;
      },
      load: (url, context, nextLoad) => {
        const result = nextLoad(url, context);
        this.observe(url, result.format);
        return result;
      },
    });
    return this;
  }
  snapshot() {
    // Node can satisfy a CommonJS cache hit without invoking resolve hooks.
    // Inspect its public child records without changing cache or factory identity.
    const resolvedPairs = new Set([...this.edges.values()].map(edge => JSON.stringify([edge.from, edge.to, edge.kind])));
    for (const module of Object.values(require.cache)) {
      if (!module?.filename) continue;
      const parent = this.location(pathToFileURL(module.filename).href);
      if (!parent) continue;
      for (const child of module.children ?? []) {
        if (!child.filename) continue;
        const childURL = pathToFileURL(child.filename).href;
        const target = this.location(childURL)?.id ?? (facadeURLs.has(childURL) ? 'host:cordis' : undefined);
        if (!target || resolvedPairs.has(JSON.stringify([parent.id, target, 'require']))) continue;
        this.observe(pathToFileURL(module.filename).href);
        this.observe(childURL);
        const edge = { from: parent.id, to: target, specifier: null, source: 'require-cache', kind: 'require' };
        this.edges.set(JSON.stringify(edge), edge);
        resolvedPairs.add(JSON.stringify([parent.id, target, 'require']));
      }
    }
    return {
      coverage: 'observed',
      modules: [...this.modules.values()].sort((a, b) => a.id.localeCompare(b.id)),
      edges: [...this.edges.values()].sort((a, b) => JSON.stringify(a).localeCompare(JSON.stringify(b))),
      roots: [...this.roots].sort(),
    };
  }
}

function kind(path) {
  if (path.endsWith('.node')) return 'native-addon';
  if (['.js', '.mjs', '.cjs', '.ts', '.mts', '.cts', '.wasm'].includes(extname(path))) return 'module';
  if (/(^|\/)(package\.json|package-lock\.json|npm-shrinkwrap\.json|pnpm-lock\.yaml|yarn\.lock)$/.test(path)) return 'metadata';
  return 'resource';
}

/** Compare captured bytes without evaluating candidate modules. */
export function planReplacement(previous, candidate, graph = { coverage: 'observed', modules: [], edges: [], roots: [] }) {
  const before = new Map((previous?.manifest ?? []).map(item => [posix(item.name), item]));
  const after = new Map(candidate.manifest.map(item => [posix(item.name), item]));
  const changedFiles = [];
  for (const path of [...new Set([...before.keys(), ...after.keys()])].sort()) {
    const left = before.get(path), right = after.get(path);
    if (left && right && left.sha256 === right.sha256 && left.mode === right.mode) continue;
    changedFiles.push({ path, change: !left ? 'added' : !right ? 'removed' : 'modified', kind: kind(path) });
  }
  const oldDirectories = new Set((previous?.directories ?? []).map(posix));
  const newDirectories = new Set(candidate.directories.map(posix));
  const changedDirectories = [...new Set([...oldDirectories, ...newDirectories])].filter(path => oldDirectories.has(path) !== newDirectories.has(path)).sort();
  const changedPaths = new Set(changedFiles.map(item => item.path));
  const affected = new Set(graph.modules.filter(item => changedPaths.has(item.path)).map(item => item.id));
  const dependents = new Map();
  for (const edge of graph.edges) {
    if (!dependents.has(edge.to)) dependents.set(edge.to, new Set());
    dependents.get(edge.to).add(edge.from);
  }
  const queue = [...affected];
  for (let cursor = 0; cursor < queue.length; cursor++) {
    for (const id of dependents.get(queue[cursor]) ?? []) {
      if (!affected.has(id)) { affected.add(id); queue.push(id); }
    }
  }
  const observedPaths = new Set(graph.modules.map(item => item.path));
  const nativeAddons = [...after.keys()].filter(path => kind(path) === 'native-addon').sort();
  return {
    strategy: nativeAddons.length ? 'process-restart-required' : 'worker-restart',
    coverage: 'observed',
    currentDigest: previous?.digest ?? null,
    candidateDigest: candidate.digest,
    identical: previous?.digest === candidate.digest,
    changedFiles,
    changedDirectories,
    affectedModules: [...affected].sort(),
    unobservedChanges: changedFiles.filter(item => !observedPaths.has(item.path)).map(item => item.path),
    nativeAddons,
  };
}
