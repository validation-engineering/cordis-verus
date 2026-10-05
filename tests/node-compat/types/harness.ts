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


import { domainMutation, assertDomainMutation, type MutationSteps } from '@deepseek-ai/cordis';
async function coordinated(ctx: Context, fiber: Fiber): Promise<number> {
  assertDomainMutation(ctx, { recovery: true });
  const value: number = await domainMutation(ctx, async (steps: Readonly<MutationSteps>) => {
    const captured: number = steps.capture(() => 42);
    const promised: Promise<number> = steps.capture(async () => captured);
    await promised;
    // @ts-expect-error Capture preserves the callback result type.
    const wrongCapture: string = steps.capture(() => 42);
    // @ts-expect-error Capture requires a callback.
    steps.capture(42);
    void wrongCapture;
    await steps.update(fiber, { enabled: true });
    await steps.restart(fiber);
    // @ts-expect-error Steps are scoped readonly authority.
    steps.dispose = async () => {};
    // @ts-expect-error Lifecycle steps require a Fiber, not a Context.
    await steps.dispose(ctx);
    return 42;
  });
  await domainMutation(ctx, async steps => {
    await steps.retryCleanup(fiber);
    await steps.dispose(fiber);
  }, { recovery: true });
  // @ts-expect-error A transaction result retains its inferred value type.
  const invalid: string = await domainMutation(ctx, () => 42);
  void invalid;
  return value;
}
void coordinated;
