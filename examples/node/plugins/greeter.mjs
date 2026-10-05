// This plugin uses the original Cordis import and Service API.
import { Service } from 'cordis';

export default class Greeter extends Service {
  constructor(ctx, config) {
    super(ctx, 'greeter');
    this.prefix = config.prefix;
    ctx.effect(() => () => config.onDispose());
  }

  greet(name) {
    return `${this.prefix}, ${name}!`;
  }
}
