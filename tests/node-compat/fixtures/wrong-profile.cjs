// Handshake rejection fixture only; no lifecycle behavior is simulated.
exports.bindingInfo = () => JSON.stringify({
  abi: 1,
  package: 'cordis-node',
  profile: 'harness-not-supported',
  values: 'javascript-object-table',
});
exports.NativeDriver = class { constructor() { throw new Error('Rejected addons must not be instantiated'); } };
