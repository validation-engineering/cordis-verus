export const inject = ['audit'];
export function apply(ctx, config = {}) {
  ctx.audit.push(`start:${config.value}`);
  ctx.provide('message', { value: config.value });
  ctx.effect(() => async () => {
    if (config.cleanupWait) await ctx.audit.cleanupWait;
    ctx.audit.push(`stop:${config.value}`);
    if (config.cleanupFailure) throw new Error('cleanup failed');
  });
  if (config.fail) throw new Error('candidate setup failed');
}
