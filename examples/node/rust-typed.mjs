// Build the user addon first: npm run build:native
// Run: node examples/node/rust-typed.mjs
import assert from 'node:assert/strict';
import { fileURLToPath } from 'node:url';
import { Context } from '../../packages/compat-cordis/index.js';
const addon=fileURLToPath(new URL('../../target/node-compat/interop-fixture.node',import.meta.url));
const ctx=new Context({addon});
try {
  await ctx.rustPlugin('fixture.typedControl');
  const counter=await ctx.rustPlugin('fixture.typedCounter',{label:'example',initial:10});
  await ctx.rustPlugin('fixture.typedConsumer');
  assert.equal(ctx.typedConsumer.read().sameInstance,true);
  ctx.typedCounter.add(5);
  console.log('Shared original Rust Arc:',ctx.typedConsumer.read());
  console.log('Async typed adapter:',await ctx.typedCounter.readAsync());
  await counter.restart();
  assert.equal(ctx.typedCounter.read().activation,2);
  console.log('Original FnMut definition after restart:',ctx.typedCounter.read());
  await counter.dispose();
  console.log('Consumer-before-provider cleanup:',ctx.typedControl.events().filter(event=>event.phase.endsWith(':cleanup')));
} finally { await ctx.dispose(); }
