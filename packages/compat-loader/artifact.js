import { createHash } from 'node:crypto';
import { lstat, mkdir, mkdtemp, readdir, readFile, rm, writeFile, chmod } from 'node:fs/promises';
import { join, resolve, relative, isAbsolute } from 'node:path';
import { tmpdir } from 'node:os';
import { LoaderError } from './config.js';

const managedLaunches = new Set();
/** Release only a private directory allocated by Artifact.launch in this process. */
export async function releaseLaunch(directory) {
  if (!managedLaunches.has(directory)) throw new LoaderError('ARTIFACT_CLEANUP_TARGET', 'Only a registered private artifact launch may be released');
  await rm(directory, { recursive: true, force: true });
  managedLaunches.delete(directory);
}

/** Each isolated environment gets a private copy, never the retained restoration recipe. */
export class Artifact {
  static async capture(directory, options = {}) {
    const source = resolve(directory);
    if (!(await lstat(source)).isDirectory()) throw new LoaderError('ARTIFACT_DIRECTORY', 'Artifact source must be a directory');
    const storage = await mkdtemp(join(tmpdir(), 'cordis-artifact-'));
    const root = join(storage, 'project');
    await mkdir(root);
    const manifest = [];
    const directories = [];
    let bytes = 0;
    const maxBytes = options.maxBytes ?? 256 * 1024 * 1024;
    const maxFiles = options.maxFiles ?? 20000;
    async function copy(folder = '') {
      const entries = (await readdir(join(source, folder), { withFileTypes: true })).sort((a, b) => a.name.localeCompare(b.name));
      for (const entry of entries) {
        if (entry.name === '.git') continue;
        const name = join(folder, entry.name);
        const stat = await lstat(join(source, name));
        if (stat.isSymbolicLink()) throw new LoaderError('ARTIFACT_SYMLINK', `Artifact symlinks are not supported: ${name}; materialize dependencies first`);
        if (stat.isDirectory()) { directories.push(name); await mkdir(join(root, name)); await copy(name); continue; }
        if (!stat.isFile()) throw new LoaderError('ARTIFACT_FILE_TYPE', `Unsupported artifact file ${name}`);
        if (bytes + stat.size > maxBytes || manifest.length >= maxFiles) throw new LoaderError('ARTIFACT_LIMIT', 'Artifact exceeds configured byte/file limit');
        const content = await readFile(join(source, name));
        bytes += content.length;
        if (bytes > maxBytes) throw new LoaderError('ARTIFACT_LIMIT', 'Artifact changed beyond its byte limit during capture');
        const mode = stat.mode & 0o777;
        await writeFile(join(root, name), content);
        await chmod(join(root, name), mode);
        manifest.push({ name, mode, bytes: content.length, sha256: createHash('sha256').update(content).digest('hex') });
      }
    }
    try {
      await copy();
      const digest = createHash('sha256').update(JSON.stringify({ files: manifest, directories })).digest('hex');
      return new Artifact(storage, root, source, manifest, directories, digest);
    } catch (error) { await rm(storage, { recursive: true, force: true }); throw error; }
  }
  constructor(storage, root, source, manifest, directories, digest) {
    this.storage = storage; this.root = root; this.source = source;
    this.manifest = Object.freeze(manifest.map(item => Object.freeze(item)));
    this.directories = Object.freeze(directories);
    this.digest = digest; this.closed = false;
  }
  async launch(entry) {
    if (this.closed) throw new LoaderError('ARTIFACT_CLOSED', 'The retained artifact has been released');
    const location = relative(this.root, resolve(this.root, entry));
    if (!location || location === '..' || location.startsWith(`..${process.platform === 'win32' ? '\\' : '/'}`) || isAbsolute(location)) throw new LoaderError('ARTIFACT_ENTRY', 'entry must be a file inside the artifact');
    const directory = await mkdtemp(join(tmpdir(), 'cordis-worker-'));
    managedLaunches.add(directory);
    try {
      // Only captured entries are copied; later additions to retained storage
      // cannot enter an artifact under its original digest.
      for (const name of this.directories) await mkdir(join(directory, name));
      for (const item of this.manifest) {
        const content = await readFile(join(this.root, item.name));
        if (createHash('sha256').update(content).digest('hex') !== item.sha256) throw new LoaderError('ARTIFACT_CHANGED', `Retained artifact changed: ${item.name}`);
        await writeFile(join(directory, item.name), content);
        await chmod(join(directory, item.name), item.mode);
      }
      return { directory, entry: location };
    } catch (error) { await releaseLaunch(directory); throw error; }
  }

  async dispose() { if (!this.closed) { await rm(this.storage, { recursive: true, force: true }); this.closed = true; } }
}
