export type JsonValue = null | boolean | number | string | JsonValue[] | { [key: string]: JsonValue };
/** Pull-driven Rust resource. At most one next() may be outstanding. */
export interface RustStream<T extends JsonValue = JsonValue> extends AsyncIterableIterator<T> {
  next(): Promise<IteratorResult<T, undefined>>;
  return(): Promise<IteratorResult<T, undefined>>;
  throw(error: unknown): Promise<IteratorResult<T, undefined>>;
}
declare const objectAdapterBrand: unique symbol;
/** Explicit factory return value; cannot be encoded in ordinary JSON arguments. */
export interface JavaScriptObjectAdapter { readonly [objectAdapterBrand]: true; }
export type ObjectAdapterOptions<T extends object> = {
  readonly typeName: string;
  readonly methods: readonly string[];
} & ({readonly ownership: 'borrowed'; readonly dispose?: never} | {
  readonly ownership: 'owned'; readonly dispose: (target: T) => Awaitable<void>;
});
export function adaptObject<T extends object>(target: T, options: ObjectAdapterOptions<T>): JavaScriptObjectAdapter;
export function adaptCallback<T extends (...args: any[]) => Awaitable<JsonValue | void>>(callback: T, options?: {
  readonly typeName?: string;
} & ({readonly ownership?: 'borrowed'; readonly dispose?: never} | {
  readonly ownership: 'owned'; readonly dispose: (callback: T) => Awaitable<void>;
})): JavaScriptObjectAdapter;
export interface RustObject {
  readonly typeName: string;
  readonly ownership: 'borrowed' | 'owned';
  readonly methods: readonly string[];
  call(method: string, ...args: JsonValue[]): Promise<JsonValue>;
  close(): Promise<void>;
}
export interface RustCallback extends RustObject {
  invoke(...args: JsonValue[]): Promise<JsonValue>;
}
export type Awaitable<T> = T | PromiseLike<T>;
export type Disposable = () => Awaitable<void>;
export type Effect = void | Disposable | PromiseLike<void | Disposable> | Iterable<void | Disposable> | AsyncIterable<void | Disposable>;
export interface AsyncDisposable extends Disposable { then<TResult1 = Disposable, TResult2 = never>(onfulfilled?: ((value: Disposable) => TResult1 | PromiseLike<TResult1>) | null, onrejected?: ((reason: any) => TResult2 | PromiseLike<TResult2>) | null): Promise<TResult1 | TResult2>; }
export interface OwnedTask<T> { readonly promise: Promise<T>; readonly signal: AbortSignal; cancel(reason?: unknown): void; join(): Promise<T>; }
export type Inject = string[] | Record<string, unknown>;
export interface PluginOptions<T = any> { name?: string; inject?: Inject; provide?: string | string[]; Config?: { '~standard': { validate(value: unknown): { value: T } | { issues: readonly {message: string}[] } } }; }
export type Plugin<T = any> = Plugin.Function<T> | Plugin.Constructor<T> | Plugin.Object<T>;
export namespace Plugin {
  interface Function<T = any> extends PluginOptions<T> { (ctx: Context, config: T): Effect; }
  interface Constructor<T = any> extends PluginOptions<T> { new (ctx: Context, config: T): object; }
  interface Object<T = any> extends PluginOptions<T> { apply(ctx: Context, config: T): Effect; }
}
export interface Events { [name: string | symbol]: (...args: any[]) => any; }
export interface EventOptions { prepend?: boolean; global?: boolean; }
/** Record counts, not allocated bytes. Node/publication tombstones remain; released lease records are removed. */
export interface DriverStorageStats {
  registeredPlugins: number;
  identitySlots: number;
  declarationRecords: number;
  bindingRecords: number;
  liveBindings: number;
  publicationRecords: number;
  /** Actual stored lease records, including leases held by failed cleanup. */
  leaseRecords: number;
  /** Cumulative successful allocations; lease IDs never repeat. */
  leaseAllocations: number;
  liveLeases: number;
  publishedValues: number;
  pendingActions: number;
}
export class Context {
  static readonly effect: unique symbol;
  static readonly filter: unique symbol;
  static readonly isolate: unique symbol;
  static readonly intercept: unique symbol;
  static is(value: unknown): value is Context;
  constructor(options?: { addon?: string; profile?: 'cordis' | 'harness' });
  root: this;
  fiber: Fiber;
  registry: RegistryService;
  reflect: ReflectService;
  events: EventsService;
  logger: LoggerService;
  [Context.isolate]: Record<string, symbol>;
  [Context.intercept]: Record<string, any>;
  extend(meta?: object): this;
  isolate(name: string, label?: symbol): this;
  intercept(name: string, config: unknown): this;
  plugin<T>(plugin: Plugin<T>, config?: T): Fiber & PromiseLike<Fiber>;
  rustPlugin(name: string, config?: JsonValue): Fiber & PromiseLike<Fiber>;
  inject(deps: Inject, callback: (ctx: Context) => Effect): Fiber & PromiseLike<Fiber>;
  effect(execute: () => Effect, label?: string): AsyncDisposable;
  task<T>(execute: (signal: AbortSignal) => Awaitable<T>, label?: string): OwnedTask<Awaited<T>>;
  get(name: string, strict?: boolean): any;
  set(name: string, value: any): void;
  provide(name: string, value?: any, check?: () => boolean): AsyncDisposable;
  accessor(name: string, options: { get(this: Context, receiver: any, error: Error): any; set?(this: Context, value: any, receiver: any, error: Error): boolean }): AsyncDisposable;
  mixin(source: string | object, mixins: string[] | Record<string,string>): AsyncDisposable;
  on<K extends keyof Events>(name: K, listener: Events[K], options?: boolean | EventOptions): Disposable;
  once<K extends keyof Events>(name: K, listener: Events[K], options?: boolean | EventOptions): Disposable;
  emit<K extends keyof Events>(name: K, ...args: Parameters<Events[K]>): void;
  bail(name: keyof Events, ...args: any[]): any;
  serial(name: keyof Events, ...args: any[]): Promise<any>;
  parallel(name: keyof Events, ...args: any[]): Promise<void>;
  waterfall(name: keyof Events, ...args: any[]): any;
  settle(): Promise<void>;
  dispose(): Promise<void>;
  snapshot(): {domain: string; plugins: object[]; storage: DriverStorageStats};
}
export const FiberState: Readonly<{PENDING: 0; LOADING: 1; ACTIVE: 2; FAILED: 3; DISPOSED: 4; UNLOADING: 5}>;
export class Fiber {
  readonly id: string;
  uid: number | null;
  readonly ctx: Context;
  readonly parent: Context;
  state: number;
  /** Current native-admitted setup/cleanup transition; failure is reported by await(). */
  inertia: Promise<void> | undefined;
  config: any;
  inject: Record<string, any>;
  runtime: {name?: string; callback: Function; fibers: Iterable<Fiber>} | null;
  readonly name: string;
  dispose(): Promise<void>;
  await(): Promise<Fiber>;
  effect(execute: () => Effect, label?: string): AsyncDisposable;
  task<T>(execute: (signal: AbortSignal) => Awaitable<T>, label?: string): OwnedTask<Awaited<T>>;
  restart(): Promise<void>;
  retryCleanup(): Promise<void>;
  update(config: any, noSave?: boolean): Awaitable<void>;
  getEffects(): {label: string;children: unknown[]}[];
}
export abstract class Service<T = never> {
  static readonly init: unique symbol;
  static readonly check: unique symbol;
  static readonly config: unique symbol;
  static readonly invoke: unique symbol;
  static readonly extend: unique symbol;
  static readonly tracker: unique symbol;
  static readonly resolveConfig: unique symbol;
  protected ctx: Context;
  name: string;
  constructor(ctx: Context, name?: string);
  [Service.config]: T;
  protected [Service.extend](props?: object): this;
  [Service.resolveConfig](base?: T, head?: T): T;
}
export class RegistryService {
  readonly size: number;
  plugin<T>(plugin: Plugin<T>, config?: T): Fiber & PromiseLike<Fiber>;
  inject(deps: Inject, callback: (ctx: Context) => Effect): Fiber & PromiseLike<Fiber>;
  get(plugin: Plugin): object | undefined;
  has(plugin: Plugin): boolean;
  delete(plugin: Plugin): object | undefined;
  keys(): IterableIterator<Function>;
  values(): IterableIterator<any>;
}
export class ReflectService { get(name: string, strict?: boolean): any; set(name: string, value: any): boolean; provide(name: string, value?: any, check?: () => boolean): AsyncDisposable; notify(names: string[]): Fiber[]; trace<T>(value: T): T; bind<T extends Function>(callback: T): T; }
export class EventsService { }
export class CordisError extends Error { readonly code: string; }
export class ValidationError extends TypeError { }
export function Inject(name: string, config?: unknown): (value: any, decorator: ClassDecoratorContext | ClassMethodDecoratorContext) => void;
export namespace Inject { function resolve(inject?: Inject): Record<string,unknown>; }
export const symbols: Record<string,symbol>;

export type LoggerType = 'error' | 'info' | 'warn' | 'debug';
export const LoggerLevel: Readonly<{ERROR: 0; WARN: 1; INFO: 2; DEBUG: 3}>;
export interface Message { sn: number; ts: number; name: string; type: LoggerType; level: number; args: any[]; fiber?: WeakRef<Fiber>; }
export type Formatter = (value: any, exporter: Exporter, message: Message) => any;
export interface Exporter { colors?: number | false; maxLength?: number; levels?: Record<string, number>; formatters?: Record<string, Formatter>; export(message: Message): void; }
export interface LoggerOptions { name: string; meta?: Partial<Message>; level?: number; }
export class Logger {
  constructor(options: LoggerOptions, service: LoggerService);
  static color(exporter: Exporter, code: number, value: any, decoration?: string): string;
  static code(name: string, level?: false | number): number;
  static format(exporter: Exporter, message: Message): string;
  name: string;
  error(...args: any[]): void;
  warn(...args: any[]): void;
  info(...args: any[]): void;
  debug(...args: any[]): void;
}
export interface LoggerService { (name?: string): Logger; }
export class LoggerService {
  constructor(ctx: Context);
  bufferSize: number;
  buffer: Message[];
  exporters: Map<number, Exporter>;
  exporter(exporter: Exporter): AsyncDisposable;
  error(...args: any[]): void;
  warn(...args: any[]): void;
  info(...args: any[]): void;
  debug(...args: any[]): void;
}
export const defaultFormatters: Record<string, Formatter>;
export const c16: number[];
export const c256: number[];

/** Explicit external revision transaction; lifecycle callbacks cannot nest it. */
export interface MutationSteps {
  /** True only in this live coordinator callback, never in managed observers. */
  isCurrent(): boolean;
  /** Run a callback with its owner's episode identity and without transaction authority. */
  observe<T>(fiber: Fiber, execute: () => T): T extends PromiseLike<unknown> ? Promise<Awaited<T>> : T;
  /** Join synchronous adapter lifecycle calls; authority ends before async continuation. */
  capture<T>(execute: () => T): T;
  dispose(fiber: Fiber): Promise<void>;
  restart(fiber: Fiber): Promise<void>;
  retryCleanup(fiber: Fiber): Promise<void>;
  update(fiber: Fiber, config: any, noSave?: boolean): Awaitable<void>;
}
export function domainMutation<T>(ctx: Context, execute: (steps: Readonly<MutationSteps>) => Awaitable<T>, options?: { recovery?: boolean }): Promise<T>;

/** Check admission without queuing or changing domain state. */
export function assertDomainMutation(ctx: Context, options?: { recovery?: boolean }): void;
