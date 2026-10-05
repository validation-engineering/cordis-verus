// The same observable fixture is run in isolated upstream and native processes.
// No ID, event or microtask sorting is permitted in differential results.
export async function coreFixture({Context,Service},settle=async()=>{}) {
  const ctx=new Context();
  const trace=[];
  const rootEffect=ctx.effect(()=>{trace.push('effect body');return()=>trace.push('effect inverse');});
  trace.push('effect returned');
  await rootEffect();
  class Text extends Service { constructor(c){super(c,'text');this.value='hello';} }
  const provider=ctx.plugin(Text);
  await provider;
  const child=ctx.inject(['text'],c=>{trace.push(c.text.value);c.on('event',()=>trace.push('event'));return()=>trace.push('child inverse');});
  await child;
  ctx.emit('event');
  await child.dispose();
  ctx.emit('event');
  await provider.dispose();
  await settle(ctx);
  return trace;
}
