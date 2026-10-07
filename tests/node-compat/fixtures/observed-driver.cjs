// Record command kinds at the real N-API boundary; no simulated scheduler.
const native = require('../../../packages/compat-cordis/native/cordis.node');
const commands = [];
module.exports = {...native,
  bindingInfo: native.bindingInfo,
  NativeDriver: native.NativeDriver,
  takeCommands() { return commands.splice(0); },
  createDriver() {
    const driver = native.createDriver ? native.createDriver() : new native.NativeDriver();
    return {command(input) {
      commands.push(JSON.parse(input).op);
      return driver.command(input);
    }};
  },
};
