import { Context, Service, type Fiber, type OwnedTask } from '@deepseek-ai/cordis';
import { Context as Standalone } from 'cordis';
declare module '@deepseek-ai/cordis' { interface Context { harnessService: HarnessService; } }
class HarnessService extends Service {
  constructor(ctx: Context) { super(ctx, 'harnessService'); }
  answer(): number { return 42; }
}
async function app() {
  const ctx = new Context();
  const provider: Fiber = await ctx.plugin(HarnessService);
  const returned: void = provider.update({});
  const number: number = ctx.harnessService.answer();
  const task: OwnedTask<string> = ctx.task(async signal => { if(signal.aborted) return 'aborted';return 'done'; });
  const text: string = await task.join();
  // @ts-expect-error Profile-specific augmentation must not leak into standalone.
  new Standalone().harnessService;
  // @ts-expect-error Tasks retain their result type.
  const wrong: number = await task.promise;
  void [number,returned,text,wrong];
  await ctx.dispose();
}
void app;
