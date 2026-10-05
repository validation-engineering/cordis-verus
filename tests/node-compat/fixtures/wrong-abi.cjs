// Handshake rejection fixture only; no lifecycle behavior is simulated.
exports.bindingInfo = () => JSON.stringify({
  abi: 999,
  package: 'cordis-node',
  profile: 'cordis-4.0.0-rc.10-experimental',
  values: 'javascript-object-table',
});
exports.NativeDriver = class { constructor() { throw new Error('Rejected addons must not be instantiated'); } };
