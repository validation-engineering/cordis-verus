import { startEndpoint } from './domain-entry.js';
if (!process.send) throw new Error('ProcessDomain entry requires an IPC channel');
process.once('message', message => {
  if (message?.type !== 'initialize') throw new Error('ProcessDomain initialization was missing');
  startEndpoint({
    send: value => new Promise((resolve, reject) => process.send(value, error => error ? reject(error) : resolve())),
    listen: callback => process.on('message', callback),
    close: () => { if (process.connected) process.disconnect(); },
  }, message.launch, { allowNativeAddons: true, hostModule: message.hostModule });
});
