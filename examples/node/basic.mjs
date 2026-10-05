// Run from the repository after `npm run build:native`:
// node --import ./packages/compat-cordis/register.js examples/node/basic.mjs
import { Context } from 'cordis';

const { default: Greeter } = await import('./plugins/greeter.mjs');
const ctx = new Context();
const trace = [];
try {
  // Config contains a real JS function; only lifecycle identities cross N-API.
  await ctx.plugin(Greeter, {
    prefix: 'Hello',
    onDispose: () => trace.push('greeter disposed'),
  });
  await ctx.inject(['greeter'], (consumer) => {
    trace.push(consumer.greeter.greet('Cordis'));
    return () => trace.push(`consumer cleanup: ${consumer.greeter.greet('again')}`);
  });
  console.log(JSON.stringify({ domain: ctx.snapshot().domain, trace }));
} finally {
  await ctx.dispose();
}
console.log(JSON.stringify({ trace }));
