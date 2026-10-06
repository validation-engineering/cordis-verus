import { parentPort, workerData } from 'node:worker_threads';
import { startEndpoint } from './domain-entry.js';
startEndpoint({
  send: message => { parentPort.postMessage(message); },
  listen: callback => parentPort.on('message', callback),
  close: () => parentPort.close(),
}, workerData);
