export const inject = ['message', 'audit'];
export const apply = (ctx) => {
  ctx.audit.push(`consume:${ctx.message.value}`);
  return () => { ctx.audit.push(`release:${ctx.message.value}`); };
}
