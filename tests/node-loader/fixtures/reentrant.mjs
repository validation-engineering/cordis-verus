export const inject = ['audit'];
export const apply = async ctx => {
  await ctx.audit.loader.apply([]);
};
