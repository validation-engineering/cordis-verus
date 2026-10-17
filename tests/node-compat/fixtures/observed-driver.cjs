// Record command kinds at the real N-API boundary; no simulated scheduler.
const native = require('../../../packages/compat-cordis/native/cordis.node');
const commands = [];
module.exports = {...native,
  bindingInfo: native.bindingInfo,
  NativeDriver: native.NativeDriver,
  takeCommands() { return commands.splice(0); },
  createDriver() {
    const driver = native.createDriver ? native.createDriver() : new native.NativeDriver();
    return new Proxy(driver, {get(target, key) {
      if (key === 'command') return input => {
        commands.push(JSON.parse(input).op);
        return target.command(input);
      };
      // Preserve the native receiver for every current and future binding
      // method, including opaque invocation paths; observe only JSON commands.
      const value = Reflect.get(target,key,target);
      return typeof value === 'function' ? value.bind(target) : value;
    }});
  },
};
