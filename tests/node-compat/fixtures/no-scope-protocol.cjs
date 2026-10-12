exports.bindingInfo = () => JSON.stringify({abi:1,package:'cordis-node',
  profile:'cordis-4.0.0-rc.10-experimental',values:'javascript-object-table'});
exports.NativeDriver = class { constructor() { throw new Error('must reject before construction'); } };
