export const inject = ['audit'];
export const apply = (ctx, config) => {
  ctx.audit.push(`tracked:start:${config.label}`);
  ctx.effect(() => () => ctx.audit.push(`tracked:stop:${config.label}`));
};
