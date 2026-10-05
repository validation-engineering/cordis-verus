import { Service } from 'cordis';

export default class Greeting extends Service {
  constructor(ctx, config) {
    super(ctx, 'greeting');
    this.prefix = config.prefix;
  }
  hello(name) { return `${this.prefix}, ${name}!`; }
}
