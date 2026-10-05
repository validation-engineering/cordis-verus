export const inject = ['audit'];
export async function apply(ctx) {
  await ctx.plugin(child => {
    child.audit.push('child started');
    return () => { child.audit.push('child stopped'); };
  });
  ctx.audit.push('parent ready');
}
