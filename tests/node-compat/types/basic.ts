import { Context, Service, type Plugin, type Fiber, type AsyncDisposable, type OwnedTask, adaptObject, adaptCallback, type JavaScriptObjectAdapter, type RustObject, type RustCallback, type JsonValue } from 'cordis';

declare module 'cordis' {
  interface Context {
    greeter: Greeter;
  }
  interface Events {
    'greeting': (name: string, count: number) => void;
  }
}

interface Config { prefix: string; }

class Greeter extends Service<Config> {
  static provide = 'greeter';
  constructor(ctx: Context, readonly config: Config) {
    super(ctx, 'greeter');
  }
  greet(name: string): string {
    return `${this.config.prefix}, ${name}`;
  }
  [Service.init](): void {
    this.ctx.effect(() => () => undefined);
  }
  merge(config: Config): Config {
    return this[Service.resolveConfig](this.config, config);
  }
}

const plugin: Plugin<Config> = (ctx, config) => {
  ctx.provide('greeting', config.prefix);
  return () => undefined;
};
const object: Plugin.Object<Config> = {
  inject: ['greeter'],
  apply(ctx, config) {
    const result: string = ctx.greeter.greet(config.prefix);
    ctx.emit('greeting', result, 1);
    return () => undefined;
  },
};

async function application(): Promise<void> {
  const ctx = new Context();
  const provider: Fiber = await ctx.plugin(Greeter, { prefix: 'Hello' });
  await ctx.plugin(plugin, { prefix: 'Hello' });
  await ctx.plugin(object, { prefix: 'Hello' });
  await ctx.inject(['greeter'], current => {
    const greeting: string = current.greeter.greet('Alice');
    const effect: AsyncDisposable = current.effect(function* () {
      yield () => undefined;
      yield async () => undefined;
    });
    current.on('greeting', (name, count) => {
      const text: string = name;
      const repetitions: number = count;
      void [text, repetitions];
    });
    void [greeting, effect];
    // @ts-expect-error An augmented service method rejects invalid arguments.
    current.greeter.greet(42);
    // @ts-expect-error Explicit service members are not erased to any.
    const invalid: number = current.greeter;
    void invalid;
    // @ts-expect-error Undeclared Context properties are not implicitly any.
    current.notAnInstalledService;
    // @ts-expect-error Augmented events preserve their argument types.
    current.emit('greeting', 42, 1);
  });
  const task: OwnedTask<number> = ctx.task(async signal => signal.aborted ? 0 : 42);
  const answer: number = await task.join();
  const fiberTask: OwnedTask<string> = provider.task(() => 'finished');
  const text: string = await fiberTask.promise;
  task.cancel('application closing');
  // @ts-expect-error Owned task results retain their inferred value type.
  const invalidTask: OwnedTask<string> = ctx.task(() => 42);
  void [answer, text, invalidTask];
  const native = ctx.rustPlugin('my.factory', { name: 'model', limits: [1, 2], enabled: true });
  // @ts-expect-error Rust plugin configuration is explicit JSON data.
  ctx.rustPlugin('my.factory', { callback: () => undefined });
  void native;
  const isolated: Context = ctx.isolate('greeter', Symbol('separate'));
  await isolated.settle();
  await provider.dispose();
  await ctx.dispose();
}
void application;


async function objectContracts(object: RustObject, callback: RustCallback): Promise<void> {
  const target={read:()=>42};
  const borrowed: JavaScriptObjectAdapter=adaptObject(target,{typeName:'Counter',methods:['read'],ownership:'borrowed'});
  const owned: JavaScriptObjectAdapter=adaptObject(target,{typeName:'Counter',methods:['read'],ownership:'owned',dispose:async value=>{value.read();}});
  const jsCallback: JavaScriptObjectAdapter=adaptCallback((value:number)=>({answer:value*2}));
  const result: JsonValue=await object.call('read');
  const callbackResult: JsonValue=await callback.invoke(21);
  await object.close();
  await callback.close();
  // @ts-expect-error Owned adapters require an explicit disposer.
  adaptObject(target,{typeName:'Counter',methods:['read'],ownership:'owned'});
  // @ts-expect-error Borrowed adapters never receive a disposer.
  adaptObject(target,{typeName:'Counter',methods:['read'],ownership:'borrowed',dispose:()=>{}});
  // @ts-expect-error Callback results obey the JSON DTO contract.
  adaptCallback(()=>new Date());
  // @ts-expect-error Adapters cannot be forged from a public structural object.
  const forged: JavaScriptObjectAdapter={};
  // @ts-expect-error Opaque handles are not ordinary JSON arguments.
  await object.call('echo',borrowed);
  // @ts-expect-error Callback arguments must remain plain JSON.
  await callback.invoke(()=>42);
  void [borrowed,owned,jsCallback,result,callbackResult,forged];
}
void objectContracts;


import { domainMutation, assertDomainMutation, type MutationSteps } from 'cordis';
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
