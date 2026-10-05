// The locked upstream test files execute unchanged. Only their public Cordis
// entry point is selected; native runs never import upstream Fiber or Registry.
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';

const root = fileURLToPath(new URL('../../', import.meta.url));
const lock = JSON.parse(fs.readFileSync(path.join(root, 'upstream.lock.json'), 'utf8'));
const backend = process.env.CORDIS_CORE_BACKEND;
if (!['upstream', 'native'].includes(backend)) throw new Error('Set CORDIS_CORE_BACKEND=upstream|native');
const upstream = path.join(root, lock.repositories.cordis.path, 'packages/core');
const entry = backend === 'upstream' ? path.join(upstream, 'src/index.ts') : path.join(root, 'packages/compat-cordis/index.js');

export default {
  root,
  cacheDir: path.join(root, 'target/upstream-core/vite-cache', backend),
  plugins: [{
    name: 'locked-cordis-core-entry',
    enforce: 'pre',
    resolveId(source, importer) {
      if (source === 'cordis' || (source === '../src' && importer?.startsWith(path.join(upstream, 'tests')))) {
        return {id: entry, external: backend === 'native'};
      }
      if (backend === 'native' && importer?.startsWith(path.join(upstream, 'tests')) && source.startsWith('../src/')) {
        throw new Error(`Native tests must not import upstream runtime internals: ${source}`);
      }
    },
  }],
  test: {
    include: [path.join(upstream, 'tests/*.spec.ts')],
    pool: 'forks',
    maxWorkers: 2,
    execArgv: [],
    testTimeout: 5000,
    hookTimeout: 10000,
    allowOnly: false,
  },
};
