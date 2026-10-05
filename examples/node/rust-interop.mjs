import {fileURLToPath} from 'node:url';
import {Context,adaptObject,adaptCallback} from '../../packages/compat-cordis/index.js';
const ctx=new Context({addon:fileURLToPath(new URL('../../target/node-compat/interop-fixture.node',import.meta.url))});
ctx.provide('jsSource',{
  read:()=>40,
  query:async value=>({echo:value,language:'JavaScript'}),
  object:()=>adaptObject({read:()=>({language:'JavaScript',value:42})},{typeName:'Example',methods:['read'],ownership:'borrowed'}),
  callback:()=>adaptCallback(value=>({doubled:value*2})),
  async *stream() { yield 'first'; yield 'second'; },
  record:(phase,value)=>{console.log(`${phase}: ${value}`);return null;},
});
try {
  await ctx.rustPlugin('fixture.counter');
  await ctx.inject(['rustCounter'],async consumer=>{
    console.log('Rust sync:',consumer.rustCounter.add(2));
    console.log('Rust → JS:',await consumer.rustCounter.request('hello'));
    console.log('Rust Future:',await consumer.rustCounter.delay(5,'awake'));
    for await (const value of consumer.rustCounter.stream({count:3})) console.log('Rust stream:',value);
    console.log('JS stream → Rust:',await consumer.rustCounter.consumeStream());
    const object=consumer.rustCounter.object();
    console.log('Rust object:',await object.call('read'));
    await object.close();
    const callback=consumer.rustCounter.callback();
    console.log('Rust callback:',await callback.invoke('hello'));
    await callback.close();
    console.log('JS object → Rust:',await consumer.rustCounter.useObject());
    console.log('JS callback → Rust:',await consumer.rustCounter.useCallback(21));
  });
} finally { await ctx.dispose(); }
