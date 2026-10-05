import { fileURLToPath } from 'node:url';
import { WorkerDomain } from '../../packages/compat-loader/worker.js';
const domain = new WorkerDomain();
try {
  await domain.load(fileURLToPath(new URL('.', import.meta.url)));
  console.log(await domain.call('greeting', 'hello', 'Worker'));
} finally {
  await domain.dispose();
}
