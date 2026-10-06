// JS values and callbacks remain in this environment. All activation, invalidation,
// provider selection and cleanup admission are selected by the native Driver.
import { AsyncLocalStorage } from 'node:async_hooks';
import { createRequire } from 'node:module';
import { selectNativeArtifact } from './native-artifacts.js';
import { EventsService } from './events.js';
import { RustHost } from './rust-plugin.js';
import { LoggerService } from './logger.js';
import { DisposableList, getTraceable, isConstructor, symbols, withProps } from './utils.js';
import { defineProperty } from './support.js';

const require = createRequire(import.meta.url);
const invocation = new AsyncLocalStorage();
const mutation = new AsyncLocalStorage();
const kDomain = Symbol('cordis-verus.domain');
const kRetryCleanup = Symbol('cordis-verus.retry-cleanup');
export const FiberState = Object.freeze({ PENDING: 0, LOADING: 1, ACTIVE: 2, FAILED: 3, DISPOSED: 4, UNLOADING: 5 });
const states = { pending: 0, loading: 1, active: 2, failed: 3, disposed: 4, unloading: 5, removed: 4 };
export class CordisError extends Error {
  constructor(code, message = code) { super(message); this.code = code; }
}
export class ValidationError extends TypeError {
  constructor(issues) { super(`invalid config:\n${issues.map(issue => `  - ${issue.message}`).join('\n')}`); this.name = 'ValidationError'; }
}
export function resolveConfig(runtime, config) {
  if (!runtime?.Config) return config;
  const result = runtime.Config['~standard']?.validate(config);
  if (!result) throw new TypeError('Config must implement Standard Schema');
  if (result.then) { Promise.resolve(result).catch(() => {}); throw new TypeError('Async config validation is not supported'); }
  if (result.issues) throw new ValidationError(result.issues);
  return result.value;
}
function nativeDriver(options) {
  const addon = options.addon ?? process.env.CORDIS_NATIVE_BINDING ?? selectNativeArtifact().path;
  let binding;
  try { binding=require(addon); }
  catch (cause) { throw new Error(`Cannot load Cordis native driver at ${addon}; build it with node scripts/build-node.mjs`, { cause }); }
  if (typeof binding.NativeDriver !== 'function' || typeof binding.bindingInfo !== 'function') {
    throw new Error(`Incompatible Cordis addon at ${addon}: NativeDriver and bindingInfo exports are required`);
  }
  let info;
  try { info=JSON.parse(binding.bindingInfo()); }
  catch (cause) { throw new Error(`Incompatible Cordis addon at ${addon}: bindingInfo must return valid JSON`, {cause}); }
  if (info?.abi !== 1 || info?.profile !== 'cordis-4.0.0-rc.10-experimental' || info?.package !== 'cordis-node' || info?.values !== 'javascript-object-table') {
    throw new Error(`Incompatible Cordis addon at ${addon}: expected ABI 1 and profile cordis-4.0.0-rc.10-experimental with JavaScript object-table values`);
  }
  if (options.profile === 'harness' && !info.profiles?.includes('harness')) {
    throw new Error('Incompatible Cordis addon: Harness profile support is required');
  }
  return typeof binding.createDriver === 'function' ? binding.createDriver() : new binding.NativeDriver();
}

const serializableError = error => error instanceof Error ? `${error.name}: ${error.message}` : String(error);

function* invocationScopes(token = invocation.getStore()) {
  for (; token; token = token.parentInvocation) {
    yield token;
    if (token.effectScope) yield token.effectScope;
  }
}

function assertCurrentInvocation(domain) {
  for (const token of invocationScopes()) {
    if (token.fiber._domain !== domain) continue;
    if (token.generation !== token.fiber._generation || token.fiber._removedFlag) {
      throw new CordisError('STALE_EPISODE', 'managed continuation belongs to an old episode');
    }
  }
}

// Effects preserve the caller's cleanup/Rust authority, while their initializer
// or inverse independently keeps its owner busy until the actual result lands.
// Parent tokens remain shared so completing a nested synchronous callback cannot
// hide an in-flight setup, cleanup, task or reverse Rust call.
function runEffectInvocation(fiber, execute) {
  const parentInvocation = invocation.getStore();
  const effectScope = {fiber,generation:fiber._generation,active:true};
  const token = {...(parentInvocation ?? {fiber,generation:fiber._generation,kind:'effect'}),
    active:false,parentInvocation,effectScope};
  const finish = () => { effectScope.active = false; };
  try {
    const result = invocation.run(token,execute);
    if (result?.then) Promise.resolve(result).then(finish,finish);
    else finish();
    return result;
  } catch (error) { finish(); throw error; }
}

// AsyncLocalStorage also follows detached continuations after a callback has
// landed. Those continuations retain their episode, but no longer hold the
// action/task whose completion an ancestor shutdown would otherwise await.
// Reverse Rust calls keep their independently admitted lease authority.
function invocationBlocksWait(token) {
  return !!token && (token.active !== false || token.rustAuthority !== undefined);
}

function assertNotWaitingForAncestor(target, operation) {
  target = target.ctx.fiber;
  assertCurrentInvocation(target._domain);
  for (const token of invocationScopes()) {
    let invoking=invocationBlocksWait(token) ? token.fiber : undefined;
    while (invoking) {
      if (invoking === target) throw new CordisError('REENTRANT_MUTATION',`Cannot await ${operation} from the current fiber action or its ancestor`);
      const parent=invoking.parent.fiber;
      invoking=parent===invoking?undefined:parent;
    }
    // An active callback cannot wait for a provider whose committed lease it
    // keeps alive, including through intermediate JS services.
    if (invocationBlocksWait(token)) {
      const domain = token.fiber._domain;
      for (const provider of domain.fibers.values()) {
        let affected = false;
        for (let owner=provider; owner;) {
          if (owner === target) { affected=true; break; }
          const parent=owner.parent.fiber;
          owner=parent===owner?undefined:parent;
        }
        if (affected && domain.command({op:'committed_reaches',from:token.fiber.id,generation:token.generation,target:provider.id}).reachable) {
          throw new CordisError('REENTRANT_MUTATION',`Cannot await ${operation} of a provider retained by the current action`);
        }
      }
    }
  }
}

function liveInvocation(domain) {
  return [...invocationScopes()].some(token => token.fiber._domain === domain && invocationBlocksWait(token));
}

export function assertDomainMutation(ctx, options = {}) {
  ctx[kDomain].assertMutationAdmission({recovery:options.recovery === true});
}

/** Serialize external revisions in one execution domain. The callback's steps
 * are scoped authority for lifecycle work, not permission inherited by plugins. */
export function domainMutation(ctx, execute, options = {}) {
  try {
    if (typeof execute !== 'function') throw new TypeError('domainMutation requires a callback');
    return Promise.resolve(ctx[kDomain].enqueueMutation(execute, {recovery:options.recovery === true}));
  } catch (error) { return Promise.reject(error); }
}

class Domain {
  constructor(options) {
    this.profile = options.profile ?? 'cordis';
    if (!['cordis','harness'].includes(this.profile)) throw new TypeError('Unsupported Cordis compatibility profile');
    this.driver = nativeDriver(options);
    this.driverDirty = true;
    this.pumping = false;
    this.driver.command(JSON.stringify({op:'configure',profile:this.profile}));
    this.fibers = new Map();
    this.values = new Map();
    this.services = new Map();
    this.realms = new Map();
    this.props = Object.create(null);
    this.hooks = Object.create(null);
    this.tasks = new Set();
    this.counter = 0n;
    this.scheduled = false;
    this.closed = false;
    this.acceptingMutations = true;
    this.mutationQueue = [];
    this.currentMutation = undefined;
    this.updateFrames = [];
    this.captureFrames = [];
    this.errors = [];
    this.progress = 0;
    this.waiters = new Set();
    this.checks = new Map();
    this.checkQueue = [];
    this.checking = false;
    this.diagnostics = [];
    this.rust = new RustHost(this, {
      invocation:()=>invocation.getStore(), run:(token,callback)=>invocation.run(token,callback),
      child:(session,callback)=>this.rustChild(session,callback),
      childRetire:(session,callback)=>this.rustChild(session,callback,true),
      assertCurrent:assertCurrentInvocation,
      stale:()=>new CordisError('STALE_EPISODE','Rust service handle is no longer admitted'),
    });
  }
  // These callbacks are internal Rust child dispatch, never user callbacks.
  // The backend validates each request's session/episode and actual native
  // parent. Strip the poll's incidental ALS origin and expose only the current
  // recovery restriction, not its coordinator steps. Descendant setup/observers
  // establish their own authority in the ordinary Fiber path.
  rustChild(session, callback, retiring = false) {
    const fiber = session?.token?.fiber;
    if (this.rust.sessions.get(session?.id) !== session || session.closed
      || !fiber || fiber._domain !== this || this.fibers.get(fiber.id) !== fiber
      || fiber._generation !== session.token.generation || fiber._removedFlag) {
      throw new CordisError('STALE_EPISODE', 'Rust child request belongs to an old episode');
    }
    const coordinator = this.currentMutation;
    const admission = coordinator && {domain:this,
      get active() { return coordinator.active; }, get recovery() { return coordinator.recovery; }};
    // Retirement drains the recorded native child even after owner withdrawal;
    // it must not queue behind the revision whose cleanup is waiting for it.
    if (retiring) return invocation.run(undefined, () => mutation.run(admission, callback));
    if (session.cancelled || session.cleaning) throw new CordisError('INACTIVE_EFFECT', 'Rust owner no longer accepts child plugins');
    const setup = session.setupToken;
    const liveSetup = setup?.active === true && setup.kind === 'setup' && setup.ticket
      && setup.fiber === fiber && setup.generation === session.token.generation;
    const origin = {fiber,generation:session.token.generation,kind:liveSetup ? 'setup' : 'rust-child',active:false,
      ...(liveSetup ? {parentInvocation:setup} : {})};
    return invocation.run(origin, () => mutation.run(admission, () => {
      fiber.assertActive(); // Recheck native admission and recovery restrictions.
      return callback();
    }));
  }
  assertMutationAdmission({recovery = false, closing = false} = {}) {
    assertCurrentInvocation(this);
    if (liveInvocation(this) || mutation.getStore()?.domain === this && mutation.getStore().active) {
      throw new CordisError('REENTRANT_MUTATION', 'External mutations cannot wait inside a lifecycle action or another mutation; use the transaction steps');
    }
    if (this.closed || !this.acceptingMutations && !recovery && !closing) {
      throw new CordisError('DOMAIN_CLOSED', 'The domain no longer accepts external revisions');
    }
  }
  transactionGuard() {
    const token = mutation.getStore();
    const check = () => {
      if (!token || token !== this.currentMutation || !token.isCurrent?.()) {
        throw new CordisError('REENTRANT_MUTATION', 'State migration requires the active host transaction callback');
      }
      if (token.recovery) throw new CordisError('CLEANUP_BLOCKED', 'Recovery transactions cannot begin state migration');
    };
    check();
    return check;
  }
  enqueueMutation(execute, options = {}) {
    this.assertMutationAdmission(options);
    if (options.closing) this.acceptingMutations = false;
    if (!this.currentMutation && !this.mutationQueue.length) return this.executeMutation(execute, options);
    const pending = Promise.withResolvers();
    this.mutationQueue.push({execute, options, pending, origin:invocation.getStore()});
    pending.promise.catch(() => {});
    return pending.promise;
  }
  executeMutation(execute, options) {
    const token = {domain:this, active:true, recovery:!!options.recovery, origin:invocation.getStore(), steps:new Set(), failures:new Set()};
    this.currentMutation = token;
    const finish = () => {
      token.active = false;
      this.currentMutation = undefined;
      this.wake();
      if (this.mutationQueue.length) queueMicrotask(() => {
        if (this.currentMutation) return;
        const next = this.mutationQueue.shift();
        if (!next) return;
        try { next.pending.resolve(invocation.run(next.origin, () => this.executeMutation(next.execute, next.options))); }
        catch (error) { next.pending.reject(error); }
      });
    };
    const isCurrent = () => token.active && mutation.getStore() === token
      && invocation.getStore() === token.origin && !liveInvocation(this) && !this.updateFrames.length;
    token.isCurrent = isCurrent;
    const assertStep = () => {
      if (!isCurrent()) {
        throw new CordisError('REENTRANT_MUTATION', 'Transaction steps are only valid in their active coordinator callback');
      }
    };
    const step = (operation, target, ...args) => {
      assertStep();
      return token.performStep(operation, target, ...args);
    };
    token.performStep = (operation, target, ...args) => {
      const fiber = target?.ctx?.fiber;
      if (!fiber || fiber._domain !== this) throw new CordisError('FOREIGN_DOMAIN', 'Transaction steps require a fiber in this domain');
      if (token.recovery && !['dispose','retryCleanup'].includes(operation)) {
        throw new CordisError('CLEANUP_BLOCKED', 'Recovery transactions only dispose or retry cleanup');
      }
      let result;
      try { result = fiber[{'dispose':'_dispose','restart':'_restart','retryCleanup':'_retryCleanup','update':'_update'}[operation]](...args); }
      catch (error) { token.failures.add(error); throw error; }
      if (result?.then) {
        const promise = Promise.resolve(result);
        token.steps.add(promise);
        const landed = () => token.steps.delete(promise);
        promise.then(landed, error => { token.failures.add(error); landed(); });
      }
      return result;
    };
    const steps = Object.freeze({
      isCurrent,
      observe: (target, execute) => {
        assertStep();
        const fiber = target?.ctx?.fiber;
        if (!fiber || fiber._domain !== this) throw new CordisError('FOREIGN_DOMAIN', 'Observers require a fiber in this domain');
        fiber._assertRegistered();
        if (typeof execute !== 'function') throw new TypeError('observe requires a callback');
        return this.invokeObserver(fiber, () => execute());
      },
      ...Object.fromEntries(['dispose','restart','retryCleanup','update'].map(name => [name,(fiber,...args) => step(name,fiber,...args)])),
      capture: execute => {
        assertStep();
        if (typeof execute !== 'function') throw new TypeError('capture requires a callback');
        // Trusted adapters can invoke upstream methods which discard lifecycle
        // promises. Only their synchronous prefix may delegate to this token;
        // returning a Promise never extends the frame across an await.
        const frame = {token,origin:invocation.getStore()};
        this.captureFrames.push(frame);
        try { return execute(); }
        finally { this.captureFrames.pop(); }
      },
    });
    try {
      assertCurrentInvocation(this);
      if (this.closed) throw new CordisError('DOMAIN_CLOSED', 'The domain is closed');
      if (!options.recovery && this.command({op:'snapshot'}).plugins.some(fiber => fiber.cleanupFailed)) {
        throw new CordisError('CLEANUP_BLOCKED', 'Unconfirmed cleanup blocks external revisions; retry cleanup first');
      }
      const land = async (value, failure, failed = false) => {
        try {
          if (failed) token.failures.add(failure);
          while (token.steps.size) {
            await Promise.allSettled([...token.steps]);
          }
          // Preserve the callback's public error contract (including LoaderError
          // code/details and primitive rejection values). Step failures still
          // prevent a successful callback from committing, and remain diagnostic
          // when the callback has already supplied its recovery-specific error.
          if (failed) {
            for (const error of token.failures) if (error !== failure) this.diagnostics.push({kind:'mutation-step',error:serializableError(error)});
            throw failure;
          }
          const errors = [...token.failures];
          if (errors.length === 1) throw errors[0];
          if (errors.length) throw new AggregateError(errors, 'Mutation and lifecycle steps failed');
          return value;
        } finally { finish(); }
      };
      let result;
      try { result = mutation.run(token, () => execute(steps)); }
      catch (error) {
        if (!token.steps.size) throw error;
        result = Promise.reject(error);
      }
      if (result?.then || token.steps.size || token.failures.size) {
        const promise = Promise.resolve(result).then(value => land(value), error => land(undefined,error,true));
        token.promise = promise;
        promise.catch(() => {});
        return promise;
      }
      finish();
      return result;
    } catch (error) { finish(); throw error; }
  }

  currentUpdateFrame() {
    const frame = this.updateFrames.at(-1);
    return frame?.token?.active && frame.token === this.currentMutation
      && mutation.getStore() === frame.token && invocation.getStore() === frame.origin
      && !liveInvocation(this) ? frame : undefined;
  }
  assertUpdateWait(target, operation) {
    if (!this.currentUpdateFrame()) {
      if (this.updateFrames.length) throw new CordisError('REENTRANT_MUTATION', 'Plugin actions cannot borrow a configuration update frame');
      return;
    }
    for (const frame of this.updateFrames) {
      // A config observer may revise children or unrelated fibers, but must not
      // wait for itself, its owners, or a provider retained by its own episode.
      invocation.run({fiber:frame.fiber,generation:frame.fiber._generation,
        kind:'update',active:true,parentInvocation:frame.origin}, () => assertNotWaitingForAncestor(target, operation));
    }
  }
  delegateUpdateMutation(fiber, operation, ...args) {
    const frame = this.currentUpdateFrame();
    if (!frame) {
      if (this.updateFrames.length) throw new CordisError('REENTRANT_MUTATION', 'Plugin actions cannot borrow a configuration update frame');
      const capture = this.captureFrames.at(-1);
      if (!capture) return;
      if (!capture.token.active || capture.token !== this.currentMutation || mutation.getStore() !== capture.token
        || invocation.getStore() !== capture.origin || liveInvocation(this)) {
        throw new CordisError('REENTRANT_MUTATION', 'Plugin actions cannot borrow a captured adapter frame');
      }
      return {result:capture.token.performStep(operation, fiber, ...args)};
    }
    this.assertUpdateWait(fiber, operation);
    return {result:frame.token.performStep(operation, fiber, ...args)};
  }
  updateHook(fiber, execute) {
    // Legacy Include/Group hooks synchronously issue child lifecycle operations
    // and may return void. Join those operations to the current revision without
    // letting asynchronous continuations or plugin actions borrow its authority.
    // Give observers their own episode origin even after the synchronous frame
    // exits. They may delegate child work while the frame is present, but an
    // asynchronous observer cannot borrow the outer coordinator's saved steps.
    const origin = {fiber,generation:fiber._generation,kind:'update',active:false,
      parentInvocation:invocation.getStore()};
    const frame = {fiber,token:this.currentMutation,origin};
    this.updateFrames.push(frame);
    try { return invocation.run(origin, execute); }
    finally { this.updateFrames.pop(); }
  }

  // Callback identity is separate from the coordinator, including after await.
  // Only waterfall's checked continuation can resume the original caller scope.
  invokeObserver(fiber, execute, continuation) {
    assertCurrentInvocation(this);
    const origin = invocation.getStore(), token = mutation.getStore();
    const observer = {fiber,generation:fiber._generation,kind:'observer',active:false,parentInvocation:origin};
    const update = continuation && this.currentUpdateFrame();
    const frame = update && {...update,origin:observer};
    const capture = continuation && this.captureFrames.at(-1);
    let active = true;
    const resume = continuation && (() => {
      if (!active || !token?.active || mutation.getStore() !== token || invocation.getStore() !== observer) {
        throw new CordisError('REENTRANT_MUTATION', 'Event continuation is only valid in its active callback');
      }
      assertCurrentInvocation(this);
      const suspended = frame && this.updateFrames.at(-1) === frame;
      if (suspended) this.updateFrames.pop();
      const restoring = capture && capture.token === token && capture.origin === origin
        && this.captureFrames.at(-1) !== capture;
      if (restoring) this.captureFrames.push(capture);
      try { return invocation.run(origin, continuation); }
      finally {
        if (restoring) this.captureFrames.pop();
        if (suspended) this.updateFrames.push(frame);
      }
    });
    if (frame) this.updateFrames.push(frame);
    try {
      return invocation.run(observer, () => {
        const result = execute(resume);
        // Reading then and assimilating a thenable can execute user callbacks.
        // Keep both in observer scope and return the adopted native Promise so
        // a trusted caller's await does not assimilate the user thenable again.
        if (typeof result?.then === 'function') {
          const settled = Promise.resolve(result);
          settled.then(() => { active = false; }, () => { active = false; });
          return settled;
        }
        active = false;
        return result;
      });
    } catch (error) { active = false; throw error; }
    finally { if (frame) this.updateFrames.pop(); }
  }
  invokeEvent(fiber, callback, receiver, args, waterfall = false) {
    const token = mutation.getStore();
    if (!token?.active || token.domain !== this) return Reflect.apply(callback, receiver, args);
    const continuation = waterfall ? args.at(-1) : undefined;
    return this.invokeObserver(fiber, resume => Reflect.apply(callback, receiver,
      waterfall ? [...args.slice(0,-1), resume] : args), continuation);
  }

  assertResourceAdmission() {
    if (mutation.getStore()?.domain === this && mutation.getStore().active && mutation.getStore().recovery) {
      // A successful inverse retry can unblock a previously requested restart.
      // Only a live native-admitted setup may acquire resources here, including
      // its synchronous effect wrappers. Cleanup, observers and the recovery
      // coordinator itself retain the no-new-resources rule.
      const setup = invocation.getStore()?.kind === 'setup' && [...invocationScopes()].some(token =>
        token.fiber._domain === this && token.kind === 'setup' && token.ticket && token.active !== false);
      if (!setup) throw new CordisError('CLEANUP_BLOCKED', 'Recovery transactions cannot acquire new resources');
    }
    if (this.closed || !this.acceptingMutations && !(mutation.getStore()?.domain === this && mutation.getStore().active) && !liveInvocation(this)) {
      throw new CordisError('DOMAIN_CLOSED', 'The domain is closing or closed');
    }
  }
  command(command) {
    // Checks/reclamation can change admission even when their public result looks
    // like a read. Unknown commands are writers by default. Drive is accounted
    // for by pump(), except the explicit constructor/root drive.
    if (!['snapshot','resolve','validate','validate_check','committed_reaches'].includes(command.op)
      && !(command.op === 'drive' && this.pumping)) this.driverDirty = true;
    try {
      const result = this.driver.command(JSON.stringify(command));
      const reply = typeof result === 'string' ? JSON.parse(result) : result;
      if (reply?.error) throw new CordisError(reply.code ?? 'NATIVE_DRIVER', typeof reply.error === 'string' ? reply.error : JSON.stringify(reply.error));
      if (!['snapshot','resolve','validate','drive','reclaim','checks','validate_check','committed_reaches'].includes(command.op)) this.wake();
      return reply;
    } catch (error) {
      // Even a rejected read may report a faulted native domain. Never let a
      // previously clean pump hide that fault on a later readiness join.
      this.driverDirty = true;
      throw error;
    }
  }
  refreshChecks(ports) {
    const reply = this.command(ports ? {op:'notify',ports} : {op:'checks'});
    this.checkQueue.push(...reply.checks);
    if (this.checking) return;
    this.checking = true;
    let budget = 256;
    try {
      while (this.checkQueue.length) {
        const action = this.checkQueue.shift();
        const current = this.command({op:'validate_check',ticket:action.ticket}).current;
        let available = false, error;
        if (current) {
          if (!budget--) error = new CordisError('REENTRANT_AVAILABILITY_CYCLE','Service.check notification chain exceeded 256 calls');
          else {
            try {
              const checker = this.checks.get(action.publication);
              const consumer = this.fibers.get(action.consumer);
              if (checker && consumer) {
                const result = this.rust.check(checker,getTraceable(consumer.ctx,this.values.get(action.value)),action);
                if (result?.then) { Promise.resolve(result).catch(() => {}); throw new TypeError('Service.check must return synchronously'); }
                available = !!result;
              }
            } catch (cause) { error = cause; }
          }
        }
        this.command({op:'complete_check',ticket:action.ticket,available,...(error?{error:serializableError(error)}:{})});
        if (error) this.diagnostics.push({kind:'service-check',consumer:action.consumer,error:serializableError(error)});
        if (budget < 0) {
          // Consume every already-issued ticket, without running another callback.
          for (const pending of this.checkQueue.splice(0)) this.command({op:'complete_check',ticket:pending.ticket,available:false,error:'availability cycle stopped'});
          throw error;
        }
      }
    } finally { this.checking = false; this.schedule(); }
  }
  async drainPublication(fiber, publication) {
    while (true) {
      const revision = this.progress;
      if (this.command({op:'reclaim',id:fiber.id,generation:fiber._generation,publication}).drained) break;
      this.pump();
      await this.changed(revision);
    }
    this.checks.delete(publication);
    this.schedule();
  }
  wake() {
    this.progress++;
    for (const resolve of this.waiters) resolve();
    this.waiters.clear();
  }
  changed(revision) {
    if (revision !== this.progress) return Promise.resolve();
    return new Promise(resolve => this.waiters.add(resolve));
  }
  intern(map, key) { if (!map.has(key)) map.set(key, String(++this.counter)); return map.get(key); }
  port(ctx, name) {
    ctx.root[symbols.isolate][name] ??= Symbol(name);
    return {key: this.intern(this.services, name), realm: this.intern(this.realms, ctx[symbols.isolate][name])};
  }
  schedule() {
    if (this.scheduled) return;
    this.scheduled = true;
    queueMicrotask(() => { this.scheduled = false; try { this.pump(); } catch (error) { this.errors.push(error); } });
  }
  track(task) {
    this.tasks.add(task);
    task.finally(() => { this.tasks.delete(task); this.wake(); this.schedule(); }).catch(error => this.errors.push(error));
  }
  pump() {
    if (!this.driverDirty) return;
    // Driving native transitions is host work, including when an observer
    // schedules it before its own episode restarts. Callback setup/cleanup
    // establish their own origins; status observers receive neither an old
    // episode nor the coordinator's scoped mutation authority.
    const token = mutation.getStore();
    const admission = token && {domain:token.domain,
      get active() { return token.active; }, get recovery() { return token.recovery; }};
    // exit() disables the ALS globally; a nested observer run() can re-enable it
    // and reveal the resource's old store. An explicit empty store stays empty
    // after nested callbacks restore their parent scope.
    return invocation.run(undefined, () => mutation.run(admission, () => this._pump()));
  }
  _pump() {
    const outerPump = this.pumping;
    this.pumping = true;
    // Clear before callbacks, so every command they issue invalidates this scan.
    this.driverDirty = false;
    try {
      // Driver calls contain no callbacks. JS executes only after the native borrow ends.
      const reply = this.command({op: 'drive'});
      const { actions = [], released = [] } = reply;
      for (const handle of released) this.values.delete(handle);
      this.dispatch(actions);
      this.sync();
      // Only an explicit empty completed drive establishes quiescence. Native
      // progress without an action is withdrawal closure; it reaches a fixed
      // point before returning an empty batch, within the driver's loop budget.
      if (!Array.isArray(reply.actions) || !Array.isArray(reply.released) || actions.length || released.length) this.driverDirty = true;
      if (actions.length) this.wake();
    } catch (error) { this.driverDirty = true; throw error; }
    finally {
      this.pumping = outerPump;
      // A synchronous status hook may pump recursively and then resume an older
      // snapshot. Its inner scan cannot certify the still-running outer scan.
      if (outerPump) this.driverDirty = true;
    }
  }
  dispatch(actions) {
    for (const action of [...actions.filter(action => action.kind === 'removed'), ...actions.filter(action => action.kind !== 'removed')]) {
      try {
      const fiber = this.fibers.get(action.id);
      if (!fiber) throw new Error(`Native action has no JS owner: ${action.id}`);
      if (action.kind === 'removed') {
        // The graph has already removed this node. A failed native definition
        // finalizer must retain its own journal, but cannot undo that fact or
        // make JS miss the one Removed acknowledgement.
        try { this.rust.removed(fiber); } catch (error) { this.errors.push(error); }
        fiber._removed();
        continue;
      }
      if (action.kind === 'setup' || action.kind === 'cleanup') {
        // Official Loader observes inertia, including from status/service hooks
        // fired before the callback's promise can be assigned to _task. Publish
        // its join handle before entering the native-admitted transition.
        const transition = Promise.withResolvers();
        fiber.inertia = transition.promise;
        let task;
        try { task = action.kind === 'setup' ? fiber._activate(action.ticket) : fiber._cleanup(action.ticket); }
        catch (error) {
          if (fiber.inertia === transition.promise) fiber.inertia = undefined;
          transition.resolve();
          throw error;
        }
        fiber._task = task;
        task.finally(() => {
          if (fiber._task === task) fiber._task = undefined;
          // Native completion may already have admitted the next transition.
          // Never erase its join handle when this earlier callback lands.
          if (fiber.inertia === transition.promise) fiber.inertia = undefined;
          transition.resolve();
        }).catch(() => {});
        this.track(task);
      }
      else throw new Error(`Unsupported native action: ${action.kind}`);
      } catch(error) {this.errors.push(error);}
    }
  }
  sync() {
    const snapshot = this.command({op:'snapshot'});
    for (const item of snapshot.plugins ?? snapshot.nodes ?? snapshot.fibers ?? []) {
      this.rust.sync(item);
      const fiber = this.fibers.get(item.id);
      if (!fiber) continue;
      const state = states[String(item.state ?? item.phase).toLowerCase()];
      if (state !== undefined) {
        const next = item.pendingAction?.kind === 'setup' ? FiberState.LOADING : state;
        // State observers run arbitrary synchronous code outside native borrows.
        if (fiber.state !== next) this.driverDirty = true;
        try { fiber._setState(next); } catch (error) { this.driverDirty = true; this.errors.push(error); }
      }
    }
  }
  async settle() {
    assertCurrentInvocation(this);
    if ([...invocationScopes()].some(token => token.fiber._domain === this && invocationBlocksWait(token))) throw new CordisError('REENTRANT_MUTATION','Cannot await domain settlement from its own action');
    if (!(mutation.getStore()?.domain === this && mutation.getStore().active)) {
      while (this.currentMutation || this.mutationQueue.length) {
        const revision = this.progress;
        await this.changed(revision);
      }
    }
    // A blocked dependency is settled Pending, not falsely reported ready.
    while (true) {
      this.pump();
      if (!this.tasks.size) { await Promise.resolve(); this.pump(); if (!this.tasks.size) break; }
      await Promise.allSettled([...this.tasks]);
    }
    if (this.errors.length) throw new AggregateError(this.errors.splice(0), 'Cordis native executor failed');
  }
}

// Normalize only effects, never service values. Synchronous effect bodies and
// iterators execute inline; asynchronous inverses are retained before completion.
function collectEffect(value, collect, active) {
  if (value == null) return;
  if (typeof value === 'function') { collect(value); return; }
  if (typeof value !== 'object') throw new TypeError('Invalid effect');
  if (typeof value.then === 'function') return Promise.resolve(value).then(result => {
    if (result != null && typeof result !== 'function') throw new TypeError('Invalid effect');
    if (result) collect(result);
  });
  if (value[Symbol.iterator]) {
    const iterator = value[Symbol.iterator]();
    while (true) { const result = iterator.next(); collectEffect(result.value, collect, active); if (result.done) return; }
  }
  if (value[Symbol.asyncIterator]) return (async () => {
    await Promise.resolve();
    const iterator = value[Symbol.asyncIterator]();
    while (active()) {
      const result = await iterator.next();
      if (result.value != null && typeof result.value !== 'function') throw new TypeError('Invalid effect');
      if (result.value) collect(result.value);
      if (result.done) return;
    }
    if (iterator.return) { const result = await iterator.return(); if (typeof result.value === 'function') collect(result.value); }
  })();
  throw new TypeError('Invalid effect');
}

export class Fiber {
  constructor(parent, runtime, config, inject, id) {
    this.parent = parent;
    // Naming is diagnostic metadata and must not resolve services on a retired context.
    this._parentFiber = runtime ? parent.fiber : undefined;
    this.runtime = runtime;
    this.config = config;
    this._config = config;
    this.inject = inject;
    this.id = id;
    this.uid = Number(id);
    if (!Number.isSafeInteger(this.uid)) throw new RangeError('Cordis public fiber uid exceeds Number.MAX_SAFE_INTEGER');
    this.state = FiberState.PENDING;
    this.inertia = undefined;
    this._hooks = Object.create(null);
    this._disposables = new DisposableList();
    this._ownedTasks = new Set();
    this._generation = undefined;
    this._error = undefined;
    this._removedFlag = false;
    this._publications = new Map();
    this.ctx = runtime ? parent.extend({fiber:this}) : parent;
    this._mutations = new Set();
    this.dispose = () => {
      if (this._removedFlag) return Promise.resolve();
      assertNotWaitingForAncestor(this, 'disposal');
      const delegated = this._domain.delegateUpdateMutation(this, 'dispose');
      if (delegated) return this._trackMutation(delegated.result);
      // Owned structural inverses cannot wait behind their own outer revision.
      if (liveInvocation(this._domain)) return this._dispose();
      // Teardown observers may join the already-issued native withdrawal.
      if (this._disposing && mutation.getStore()?.domain === this._domain && mutation.getStore().active) return this._disposing;
      this._domain.assertMutationAdmission({recovery:true});
      if (this._disposalRequest) return this._disposalRequest;
      if (this._disposing) return this._disposing;
      const result = this._domain.enqueueMutation(() => this._dispose(), {recovery:true});
      this._disposalRequest = this._trackMutation(Promise.resolve(result));
      const request = this._disposalRequest;
      request.catch(() => {
        // A queued request can lose episode admission before native withdrawal.
        // Such a rejected request must not poison future external disposal.
        if (!this._disposing && this._disposalRequest === request) this._disposalRequest = undefined;
      });
      return this._disposalRequest;
    };
  }
  get name() { return this.runtime?.name || this._parentFiber?.name || 'root'; }
  get _domain() { return this.ctx[kDomain]; }
  assertActive() {
    assertCurrentInvocation(this._domain);
    this._domain.assertResourceAdmission();
    if (this.uid === null || this._domain.closed) throw new CordisError('INACTIVE_EFFECT', 'cannot create effect on inactive context');
    const token = invocation.getStore();
    if (token?.fiber === this && token.generation !== this._generation) throw new CordisError('STALE_EPISODE', 'cannot create effect from an old episode');
    if (token?.fiber === this && token.kind === 'cleanup') throw new CordisError('INACTIVE_EFFECT', 'cannot create effect during cleanup');
    if (this._generation === undefined || this._generation === '0') {
      this._generation = this._domain.command({op:'prepare',id:this.id}).generation;
    } else this._domain.command({op:'validate', id:this.id, generation:this._generation});
  }
  _setState(state) {
    if (this.state === state) return;
    const previous = this.state;
    this.state = state;
    try { this._domain.events?.emit('internal/status', this, previous); }
    finally {
      if (previous === FiberState.ACTIVE || state === FiberState.ACTIVE) {
        const names = [...this._publications.values()].map(entry => entry.name);
        if (names.length) this.ctx.reflect.notify(names);
      }
    }
  }
  async _activate(ticket) {
    this._generation = ticket.generation;
    this._error = undefined;
    const token = {fiber:this, generation:ticket.generation, kind:'setup',ticket,active:true};
    let success = true;
    try {
      this._setState(FiberState.LOADING);
      await Promise.resolve();
      // Harness cancels a queued activation at its documented microtask checkpoint.
      if (this._domain.profile === 'harness') {
        this._domain.pump();
        try { this._domain.command({op:'validate',id:this.id,generation:ticket.generation}); }
        catch (error) {
          if (/AdmissionClosed|StaleEpisode/.test(error.message)) {
            this._domain.command({op:'complete',ticket,success:true});
            this._domain.schedule();
            return;
          }
          throw error;
        }
      }
      await invocation.run(token, () => {
        if (this._domain.profile === 'harness') this.config = this._resolveConfig(this._config);
        if (!this.runtime) return;
        const callback = this.runtime.callback;
        let result;
        if (isConstructor(callback)) {
          const instance = new callback(this.ctx, this.config);
          for (const hook of instance?.[symbols.initHooks] ?? []) hook();
          result = instance?.[symbols.init]?.();
        } else result = callback(this.ctx, this.config);
        return collectEffect(result, inverse => this._disposables.push(inverse), () => this.uid !== null);
      });
    } catch (error) {
      success = false; this._error = error;
      try { this.ctx.logger.error(error); } catch (loggingError) { this._domain.errors.push(loggingError); }
    } finally { token.active = false; }
    this._domain.command({op:'complete', ticket, success, ...(success ? {} : {error:serializableError(this._error)})});
    this._domain.schedule();
  }
  async _cleanup(ticket) {
    const errors = [];
    try { this._setState(FiberState.UNLOADING); } catch(error) { errors.push(error); }
    const token = {fiber:this, generation:ticket.generation, kind:'cleanup',ticket,active:true};
    try { await invocation.run(token, async () => {
      // Task admission closed with native withdrawal. Every owned task must
      // land before any resource inverse, regardless of registration order.
      const tasks = [...this._ownedTasks];
      const rustCalls = [...(this._rustCalls ?? [])];
      for (const task of [...tasks,...rustCalls]) task.cancel();
      // Start resource close before joining calls: close may wake a blocked pull.
      try { await this._domain.rust.closeResources(this._rustResources); } catch (error) { errors.push(error); }
      await Promise.allSettled([...tasks,...rustCalls].map(task => task.promise));
      if (this._rustResources?.size) {
        if (!errors.length) errors.push(new Error('Stream resources are still owned by the retiring episode'));
        return; // Retain dependencies and inverses for close retry.
      }
      for (const dispose of [...this._disposables].reverse()) {
        try { await dispose(); this._disposables.delete(dispose); } catch (error) { errors.push(error); }
      }
      // Cleanup may start legitimate committed-service calls without awaiting
      // them. They still land before this consumer releases its native leases.
      while (this._rustCalls?.size) {
        await Promise.allSettled([...this._rustCalls].map(call => call.promise));
      }
      if (this._rustResources?.size) {
        try { await this._domain.rust.closeResources(this._rustResources); } catch (error) { errors.push(error); }
        if (this._rustResources.size && !errors.length) errors.push(new Error('Stream resources remain after cleanup'));
      }
      // Ordinary and nested effect inverses may need these handles on retry.
      // Object disposal is a separate late phase, never interleaved ahead of them.
      if (!errors.length) {
        try { await this._domain.rust.closeObjects(this._rustObjects); } catch (error) { errors.push(error); }
        if (this._rustObjects?.size && !errors.length) errors.push(new Error('Object resources remain after cleanup'));
      }
      if (!errors.length) {
        try { await this._domain.rust.closeSessions(this); } catch (error) { errors.push(error); }
      }
    }); } finally { token.active = false; }
    this._domain.command({op:'complete',ticket,success:errors.length === 0,...(errors.length ? {error:errors.map(serializableError).join('; ')} : {})});
    if (!errors.length) this._publications.clear();
    if (errors.length) { this._error = new AggregateError(errors, `Cleanup failed for ${this.name}`, this._error ? {cause:this._error} : undefined); this._domain.errors.push(this._error); }
    this._domain.schedule();
  }
  _removed() {
    this.uid = null;
    this._removedFlag = true;
    try { this._setState(FiberState.DISPOSED); } catch(error) { this._domain.errors.push(error); }
    this._domain.fibers.delete(this.id);
    this._releaseParent?.();
    if (this.runtime) {
      this.runtime.fibers.delete(this);
      if (!this.runtime.fibers.length) this._domain.registry._internal.delete(this.runtime.callback);
    }
  }
  _cleanupFailure() {
    const nodes = this._domain.command({op:'snapshot'}).plugins;
    if (!nodes.some(node => node.cleanupFailed)) return;
    const children = new Map();
    for (const node of nodes) {
      if (!children.has(node.parent)) children.set(node.parent,[]);
      children.get(node.parent).push(node.id);
    }
    const owned = new Set(), pending = [this.id];
    while (pending.length) {
      const id = pending.pop();
      if (owned.has(id)) continue;
      owned.add(id); pending.push(...(children.get(id) ?? []));
    }
    const failed = nodes.filter(node => node.cleanupFailed && (owned.has(node.id)
      || [...owned].some(target => this._domain.command({op:'committed_reaches',from:node.id,generation:node.generation,target}).reachable)));
    if (failed.length) return new AggregateError(failed.flatMap(node => {
      const error = new CordisError('CLEANUP_FAILED', `Cleanup failed for fiber ${node.id}: ${node.error ?? 'native inverse failure'}`);
      const callbackError = this._domain.fibers.get(node.id)?._error;
      return callbackError ? [error,callbackError] : [error];
    }), 'Native cleanup failed');
  }
  _dispose() {
    if (this._removedFlag) return Promise.resolve();
    assertNotWaitingForAncestor(this,'disposal');
    if (this._disposing) return this._disposing;
    this.uid = null;
    this._domain.command({op:'retire',id:this.id});
    // Install the join handle before notifying observers, which may dispose again.
    const completion = Promise.withResolvers();
    this._disposing = completion.promise;
    this._disposing.catch(() => {});
    let observerError;
    if (this.runtime) {
      if (this._domain.profile === 'harness') {
        const args = ['internal/plugin',this];
        const report = error => {
          try { this.ctx.logger.error(error); } catch (failure) { this._domain.errors.push(failure); }
        };
        try {
          for (const callback of this.ctx.events.dispatch('emit',args)) {
            try { Promise.resolve(callback(...args)).catch(report); } catch (error) { report(error); }
          }
        } catch (error) { report(error); }
      } else {
        try { this.ctx.emit('internal/plugin',this); } catch (error) { observerError = error; }
      }
    }
    this._domain.schedule();
    (async () => {
      while (!this._removedFlag) {
        const revision=this._domain.progress;
        this._domain.pump();
        if (this._domain.errors.length) throw new AggregateError(this._domain.errors.splice(0), 'Native cleanup failed');
        if (!this._removedFlag) {
          // Settlement/readiness observers may already have consumed the event
          // error queue. A failed inverse remains a native barrier until an
          // explicit retry succeeds; waiting for a new event would never finish.
          const failure = this._cleanupFailure();
          if (failure) throw failure;
          await this._domain.changed(revision);
        }
      }
      if (observerError) throw observerError;
      // Disposal reports cleanup; await/update report a drained startup failure.
    })().then(completion.resolve,completion.reject);
    return this._disposing;
  }
  async await() {
    assertNotWaitingForAncestor(this, 'fiber readiness');
    this._domain.assertUpdateWait(this, 'fiber readiness');
    if (!(mutation.getStore()?.domain === this._domain && mutation.getStore().active)) {
      while (this._mutations.size) await Promise.all([...this._mutations]);
    }
    return this._awaitReady();
  }
  async _awaitReady() {
    assertNotWaitingForAncestor(this,'fiber readiness');
    // Await only this fiber's native readiness, not unrelated setup actions.
    while (true) {
      const revision=this._domain.progress;
      this._domain.pump();
      const own = this._task;
      if (own) await own;
      else {
        await Promise.resolve();
        this._domain.pump();
        if (this.state === FiberState.LOADING || this.state === FiberState.UNLOADING) {
          if (this._error) throw this._error;
          const failure = this._cleanupFailure();
          if (failure) throw failure;
          await this._domain.changed(revision);
          continue;
        }
        break;
      }
    }
    if (this._error) throw this._error;
    return this;
  }
  effect(execute, label = 'anonymous') {
    this.assertActive();
    const fiber = this.ctx.fiber;
    let active = true, task, cleanup, remove, retry = false;
    const inverses = [];
    const dispose = () => {
      if (!active && !retry) return cleanup;
      retry = false;
      active = false;
      const run = () => {
        let chain;
        const errors=[];
        for (const inverse of [...inverses].reverse()) {
          const execute=()=>{
            const release=()=>{const index=inverses.indexOf(inverse);if(index>=0)inverses.splice(index,1);};
            try {
              const result=inverse();
              if (result?.then) return Promise.resolve(result).then(release,error=>errors.push(error));
              release();
            } catch(error) {errors.push(error);}
          };
          if (chain) chain=chain.then(execute);
          else { const result=execute(); if(result?.then)chain=result; }
        }
        const finish=()=>{if(errors.length)throw new AggregateError(errors,'Effect cleanup failed');remove?.();};
        return chain?chain.then(finish):finish();
      };
      const runOwned = () => runEffectInvocation(fiber,run);
      try { cleanup = task ? Promise.resolve(task).then(runOwned, async error => {
        await runOwned();
        if (invocation.getStore()?.kind !== 'cleanup') throw error;
      }) : runOwned(); }
      catch(error) {cleanup=Promise.reject(error);cleanup.catch(()=>{});throw error;}
      return cleanup;
    };
    defineProperty(dispose, symbols.effect, {label,children:[]});
    defineProperty(dispose,kRetryCleanup,()=>{retry=true;});
    // Install ownership before invoking arbitrary synchronous user code.
    remove = this._disposables.push(dispose);
    const collect = inverse => {
      this._disposables.delete(inverse); inverses.push(inverse);
      if (inverse[symbols.effect]) dispose[symbols.effect].children.push(inverse[symbols.effect]);
    };
    try { task = runEffectInvocation(fiber,() => collectEffect(execute(), collect, () => active)); }
    catch (error) { try { dispose(); } catch {} throw error; }
    if (task) {
      let setupError;
      Promise.resolve(task).catch(error => { setupError = error; return dispose(); }).catch(error => {
        if (error !== setupError) this._domain.errors.push(error);
      });
    }
    dispose.then = (resolve,reject) => Promise.resolve(task).then(() => () => dispose()).then(resolve,reject);
    return dispose;
  }
  task(execute, label = 'owned task') {
    const fiber = this.ctx.fiber;
    fiber.assertActive();
    if (fiber._generation === '0') throw new CordisError('INACTIVE_EFFECT','owned tasks require an admitted activation');
    if (typeof execute !== 'function') throw new TypeError('task requires a function');
    const controller = new AbortController();
    const token = {fiber,generation:fiber._generation,kind:'task',active:true,parentInvocation:invocation.getStore()};
    let promise;
    const dispose = () => { controller.abort(); return promise.then(() => {}, () => {}); };
    defineProperty(dispose,symbols.effect,{label,children:[]});
    // A task is owned before its body can execute. Cancellation only requests
    // cooperation; cleanup waits for the actual promise, including rejection.
    const remove = fiber._disposables.push(dispose);
    promise = Promise.resolve().then(() => invocation.run(token,() => execute(controller.signal)));
    const owned = {promise,cancel:reason => controller.abort(reason)};
    fiber._ownedTasks.add(owned);
    const finish = () => { token.active = false; remove(); fiber._ownedTasks.delete(owned); fiber._domain.wake(); };
    promise.then(finish,finish);
    return Object.freeze({
      promise, signal:controller.signal, cancel:reason => controller.abort(reason),
      join() {
        if (token.active && [...invocationScopes()].includes(token)) throw new CordisError('REENTRANT_MUTATION','A task cannot join itself');
        return promise;
      },
    });
  }
  async retryCleanup() {
    assertNotWaitingForAncestor(this, 'cleanup retry');
    const delegated = this._domain.delegateUpdateMutation(this, 'retryCleanup');
    return this._trackMutation(delegated ? delegated.result : this._domain.enqueueMutation(() => this._retryCleanup(), {recovery:true}));
  }
  async _retryCleanup() {
    assertNotWaitingForAncestor(this,'cleanup retry');
    const reply=this._domain.command({op:'retry_cleanup',id:this.id});
    for (const inverse of this._disposables) inverse[kRetryCleanup]?.();
    this._error=undefined;
    this._domain.dispatch(reply.actions);
    await this._domain.settle();
    if (this._error) throw this._error;
    this._disposing=undefined;
    this._disposalRequest=undefined;
  }
  getEffects() { return [...this._disposables].map(value => value[symbols.effect]).filter(Boolean); }
  _assertRegistered() {
    if (this.uid === null || this._domain.closed) throw new CordisError('INACTIVE_EFFECT','cannot create effect on inactive context');
  }
  _resolveConfig(config) {
    config = this.ctx.waterfall(this,'internal/config',config,() => config);
    return resolveConfig(this.runtime,config);
  }
  _trackMutation(result) {
    if (!result?.then) return result;
    const promise = Promise.resolve(result);
    this._mutations.add(promise);
    const finish = () => this._mutations.delete(promise);
    promise.then(finish, finish);
    return promise;
  }
  async restart() {
    const fiber = this.ctx.fiber;
    assertNotWaitingForAncestor(fiber, 'restart');
    const delegated = fiber._domain.delegateUpdateMutation(fiber, 'restart');
    return fiber._trackMutation(delegated ? delegated.result : fiber._domain.enqueueMutation(() => fiber._restart()));
  }
  async _restart() {
    const fiber = this.ctx.fiber;
    fiber._assertRegistered();
    assertNotWaitingForAncestor(fiber,'restart');
    // Rollback may restart inside an already admitted transaction. Do not erase
    // the cleanup error or wait forever on a native inverse awaiting explicit retry.
    const failure = fiber._cleanupFailure();
    if (failure) throw failure;
    fiber._domain.command({op:'restart',id:fiber.id});
    fiber._error = undefined;
    fiber._domain.schedule();
    await fiber._awaitReady();
  }
  update(config,noSave=false) {
    const fiber = this.ctx.fiber;
    fiber._assertRegistered();
    assertNotWaitingForAncestor(fiber, 'update');
    const delegated = fiber._domain.delegateUpdateMutation(fiber, 'update', config, noSave);
    const result = fiber._trackMutation(delegated ? delegated.result : fiber._domain.enqueueMutation(() => fiber._update(config,noSave)));
    if (fiber._domain.profile === 'harness') {
      result?.catch(error => fiber.ctx.logger.error(error));
      return;
    }
    return result;
  }
  _update(config,noSave=false) {
    const fiber = this.ctx.fiber;
    fiber._assertRegistered();
    if (fiber._domain.profile === 'harness') {
      fiber._config = config;
      if (fiber.state !== FiberState.ACTIVE) {
        return fiber._restart();
      }
      config = fiber._resolveConfig(config);
    } else config = resolveConfig(fiber.runtime,config);
    const origin = invocation.getStore(), token = fiber._domain.currentMutation;
    const result = fiber._domain.updateHook(fiber, () => {
      const observer = invocation.getStore();
      return fiber.ctx.waterfall(fiber,'internal/update',config,noSave,() => {
        // The default continuation is coordinator work, but a retained next()
        // is not permission to restart after its revision or episode has ended.
        if (!token?.active || mutation.getStore() !== token || invocation.getStore() !== observer) {
          throw new CordisError('REENTRANT_MUTATION', 'Update continuation is only valid in its active observer');
        }
        assertCurrentInvocation(fiber._domain);
        return invocation.run(origin, () => {
          fiber.config = config; fiber._error = undefined; return fiber._restart();
        });
      });
    });
    if (result === undefined) return;
    const task = Promise.resolve(result);
    task.catch(() => {});
    return task;
  }
}

export const Inject = Object.assign(function Inject(name, config) {
  return (value, decorator) => {
    if (decorator.kind === 'class') {
      if (!Object.hasOwn(value,'inject')) {
        defineProperty(value,'inject',Object.create(Object.getPrototypeOf(value).inject ?? null));
        defineProperty(value.inject,symbols.checkProto,true);
      }
      value.inject[name]=config;
    } else if (decorator.kind === 'method') {
      const inject=(value[symbols.metadata] ??= {}).inject ??= Object.create(null);
      inject[name]=config;
      decorator.addInitializer(function () {
        const property=this[symbols.tracker]?.property;
        (this[symbols.initHooks] ??= []).push(() => this.ctx.inject(inject,ctx => value.call(property?withProps(this,{[property]:ctx}):this)));
      });
    } else throw new TypeError('@Inject() can only be used on class or class methods');
  };
}, {resolve(inject,result=Object.create(null)) {
  if (!inject) return result;
  if (Array.isArray(inject)) for(const name of inject) result[name]=null;
  else {
    if (Reflect.has(inject,symbols.checkProto)) Inject.resolve(Object.getPrototypeOf(inject),result);
    for(const name of Object.keys(inject)) result[name]=inject[name] ?? null;
  }
  return result;
}});

export class RegistryService {
  constructor(ctx) { this.ctx=ctx; this._internal=new Map(); defineProperty(this,symbols.tracker,{property:'ctx',noShadow:true}); }
  get size() { return this._internal.size; }
  resolve(plugin) { try { return typeof plugin === 'function' ? plugin : typeof plugin?.apply === 'function' ? plugin.apply : undefined; } catch {} }
  get(plugin) { return this._internal.get(this.resolve(plugin)); }
  has(plugin) { return this._internal.has(this.resolve(plugin)); }
  delete(plugin) { const runtime=this.get(plugin); if (!runtime) return; for (const fiber of [...runtime.fibers]) fiber.dispose(); return runtime; }
  keys() { return this._internal.keys(); }
  values() { return this._internal.values(); }
  entries() { return this._internal.entries(); }
  forEach(callback) { return this._internal.forEach(callback); }
  inject(inject, callback) { return this.plugin({inject,apply:callback,name:callback.name}); }
  plugin(plugin, config) {
    this.ctx.fiber.assertActive();
    const callback=this.resolve(plugin);
    if (!callback) throw new TypeError('invalid plugin, expect function or object with an apply method');
    let runtime=this._internal.get(callback);
    if (!runtime) { runtime={callback,name:plugin.name,Config:plugin.Config,fibers:new DisposableList()}; this._internal.set(callback,runtime); }
    if (this.ctx[kDomain].profile === 'cordis') config=resolveConfig(runtime,config);
    const inject=Inject.resolve(plugin.inject);
    const domain=this.ctx[kDomain];
    const {id}=domain.command({op:'mount',parent:this.ctx.fiber.id,dependencies:[],provisions:[],sealed:false});
    const fiber=new Fiber(this.ctx,runtime,config,inject,id);
    domain.fibers.set(id,fiber);
    runtime.fibers.push(fiber);
    // Keep the real structural inverse in the parent's effect journal as well
    // as the native ownership edge; both join the same disposal promise.
    const disposeChild = fiber.dispose;
    const ownedChild = this.ctx.fiber.effect(() => async () => {
      try { await disposeChild(); }
      catch (error) { if (!fiber._removedFlag) throw error; }
    }, 'ctx.plugin()');
    defineProperty(fiber.dispose,symbols.effect,ownedChild[symbols.effect]);
    fiber._releaseParent = () => fiber.parent.fiber._disposables.delete(ownedChild);
    try {
      // Bind a typed request to the real node before synchronous observers can
      // throw or withdraw it. Allocation failure and cleanup are distinct.
      domain.rust.allocated(callback,fiber);
      this.ctx.emit('internal/plugin',fiber);
      if (!fiber._removedFlag && fiber.uid !== null) {
        fiber.inject = Inject.resolve(fiber.inject);
        if (Object.keys(fiber.inject).length) {
          fiber.ctx[symbols.intercept]=Object.create(this.ctx[symbols.intercept]);
          for(const [name,value] of Object.entries(fiber.inject)) if(value!=null) fiber.ctx[symbols.intercept][name]=value;
        }
        // Original typed children inherit exact committed dependency ports in
        // addition to their named declarations, including another realm of the
        // same service. Resolve them before native admission, never afterward.
        const dependencies = domain.rust.dependencies(callback,fiber,Object.keys(fiber.inject).map(name=>domain.port(fiber.ctx,name)));
        domain.command({op:'seal',id,dependencies});
        domain.refreshChecks();
      }
    } catch(error) { fiber.dispose(); throw error; }
    // Register ready setup before returning; bodies retain their microtask checkpoint.
    domain.pump();
    domain.schedule();
    const wrapped=Object.create(fiber);
    wrapped.then=(resolve,reject)=>fiber.await().then(resolve,reject);
    return wrapped;
  }
}

function special(prop) { return typeof prop === 'symbol' || prop === 'then' || prop === 'prototype' || prop.startsWith('_') || String(parseInt(prop)) === prop; }
const contextHandler = {
  get(target,prop,ctx) {
    if (special(prop)) return Reflect.get(target,prop,ctx);
    // Diagnostic logging must remain available to report rejected late work.
    // Its traceable counter updates use the intrinsic extend() metadata view.
    // Neither access clears the token: exporters, services and effects retain
    // their ordinary episode admission checks, including on a derived view.
    const diagnostic = prop === 'logger' || prop === 'extend' && Reflect.get(target,prop,ctx) === Context.prototype.extend;
    if (!diagnostic) assertCurrentInvocation(target[kDomain]);
    if (Reflect.has(target,prop)) return getTraceable(ctx,Reflect.get(target,prop,ctx));
    const error=new Error(`cannot get property "${prop}" without inject`);
    const def=target[kDomain].props[prop];
    if (def?.type==='accessor') return def.get.call(ctx,ctx[symbols.receiver],error);
    const defSite=ctx[symbols.shadow] ?? ctx;
    if (!defSite.fiber.runtime) return ctx.reflect.get(prop,false);
    return ctx.events.waterfall('internal/get',ctx,prop,error,()=>{
      const realm=ctx[symbols.isolate][prop];
      let fiber=defSite.fiber;
      while (true) {
        if (fiber._publications.has(JSON.stringify(ctx[kDomain].port(ctx,prop))) || prop in fiber.inject) {
          if (fiber._removedFlag && prop in fiber.inject) throw new Error(`cannot get required service "${prop}" in inactive context`);
          // A shadowed Service method keeps the definition fiber's committed
          // injection realm, even when its caller uses a different realm.
          const port=ctx[kDomain].port(prop in fiber.inject ? fiber.ctx : ctx,prop);
          const result=ctx[kDomain].command({op:'resolve',...port,consumer:fiber.id,generation:fiber._generation});
          if (result) return getTraceable(ctx,ctx[kDomain].values.get(result.value));
          if (prop in fiber.inject) throw new Error(`cannot get required service "${prop}" in inactive context`);
        }
        if (!fiber.runtime || fiber.parent[symbols.isolate][prop]!==realm) throw error;
        fiber=fiber.parent.fiber;
      }
    });
  },
  set(target,prop,value,ctx) {
    if (special(prop)) return Reflect.set(target,prop,value,ctx);
    const def=target[kDomain].props[prop];
    if (!def) {
      if (!ctx.fiber.runtime) return Reflect.set(target,prop,value,ctx);
      throw new Error(`cannot set property "${prop}" without provide`);
    }
    const error=new Error(`cannot set property "${prop}" without provide`);
    if (def.type==='accessor') return def.set?.call(ctx,value,ctx[symbols.receiver],error) ?? false;
    return ctx.events.waterfall('internal/set',ctx,prop,value,error,()=>ctx.reflect.set(prop,value));
  },
  has(target,prop) { return Reflect.has(target,prop) || (!special(prop) && !!target[kDomain].props[prop]); },
};

export class ReflectService {
  constructor(ctx) { this.ctx=ctx; defineProperty(this,symbols.tracker,{property:'ctx',noShadow:true}); }
  get props() { return this.ctx[kDomain].props; }
  get store() {
    const result=Object.create(null);
    for (const name of Object.keys(this.props)) {
      const impl=this._getImpl(name,false);
      if (impl) result[this.ctx[symbols.isolate][name]]=impl;
    }
    return result;
  }
  get(name,strict=true) { return getTraceable(this.ctx,this._getImpl(name,strict)?.value); }
  _getImpl(name,strict=true) {
    const domain=this.ctx[kDomain];
    assertCurrentInvocation(domain);
    const reply=domain.command({op:'resolve',...domain.port(this.ctx,name)});
    if (!reply) return;
    const fiber=domain.fibers.get(reply.owner);
    if (strict && fiber?.state!==FiberState.ACTIVE) return;
    return {name,fiber,value:domain.values.get(reply.value),publication:reply.publication};
  }
  provide(name,value,check) {
    if (check != null && typeof check !== 'function') throw new TypeError('Service.check must be a function');
    const ctx=this.ctx, domain=ctx[kDomain], fiber=ctx.fiber;
    if (this.props[name] && this.props[name].type!=='service') throw new Error(`property "${name}" is already declared as ${this.props[name].type}`);
    fiber.assertActive();
    const generation = fiber._generation;
    const publicationGeneration = () => generation === '0' && fiber._generation === '1' ? '1' : generation;
    let publication, released = false;
    const assertCanDispose = () => {
      if (released) return;
      const token = invocation.getStore();
      if (!token || token.fiber._domain !== domain || token.fiber === fiber) return;
      // Awaiting the release of one's own committed lease would prevent this
      // action from completing, which is exactly what that release requires.
      const binding = domain.command({op:'resolve',...domain.port(ctx,name),consumer:token.fiber.id,generation:token.generation});
      if (binding?.publication === publication) throw new CordisError('REENTRANT_MUTATION','Cannot dispose a publication from its committed consumer action');
    };
    const dispose = fiber.effect(()=>{
      const handle=String(++domain.counter);
      domain.values.set(handle,value);
      try { ({publication}=domain.command({op:'publish',id:fiber.id,generation,...domain.port(ctx,name),value:handle,check:!!check})); }
      catch (error) {
        domain.values.delete(handle);
        if (error.message==='Publication: Conflict' || (error.code==='Publication' && error.message==='Conflict')) {
          const port=JSON.stringify(domain.port(ctx,name));
          const owner=this._getImpl(name,false)?.fiber ?? [...domain.fibers.values()].find(candidate=>candidate._publications.has(port));
          throw new Error(`service "${name}" has been registered at <${owner?.name ?? 'root'}>`);
        }
        throw error;
      }
      this.props[name]={type:'service'};
      fiber._publications.set(JSON.stringify(domain.port(ctx,name)),{name,publication});
      if (check) domain.checks.set(publication,check);
      domain.schedule();
      return async ()=>{
        const token = invocation.getStore();
        const restoringOwner = token?.kind === 'cleanup' && token.fiber === fiber && token.generation === publicationGeneration();
        if (restoringOwner) {
          // Other inverses and retry attempts retain the owner's service view.
          // The native cleanup completion reclaims every remaining publication.
          this.notify([name]);
          domain.checks.delete(publication);
          released = true;
          return;
        }
        domain.command({op:'revoke',id:fiber.id,generation:publicationGeneration(),publication});
        this.notify([name]);
        await domain.drainPublication(fiber,publication);
        released = true;
        const port=JSON.stringify(domain.port(ctx,name));
        if (fiber._publications.get(port)?.publication===publication) fiber._publications.delete(port);
      };
    },`ctx.provide(${JSON.stringify(name)})`);
    try { if(fiber.state===FiberState.ACTIVE)this.notify([name]); } catch(error) { dispose(); throw error; }
    const guardedDispose = () => { assertCanDispose(); return dispose(); };
    defineProperty(guardedDispose,symbols.effect,dispose[symbols.effect]);
    guardedDispose.then = (resolve,reject) => dispose.then(cleanup => {
      const guardedCleanup = () => { assertCanDispose(); return cleanup(); };
      return resolve ? resolve(guardedCleanup) : guardedCleanup;
    },reject);
    return guardedDispose;
  }
  set(name,value) {
    const ctx=this.ctx, fiber=ctx.fiber, domain=ctx[kDomain];
    fiber.assertActive();
    const entry=fiber._publications.get(JSON.stringify(domain.port(ctx,name)));
    if (!entry) {
      if (this._getImpl(name,false)) throw new Error(`cannot set property "${name}" in multiple fibers`);
      throw new Error(`cannot set property "${name}" without provide`);
    }
    const handle=String(++domain.counter);
    domain.command({op:'set',id:fiber.id,generation:fiber._generation,publication:entry.publication,value:handle});
    domain.values.set(handle,value);
    domain.schedule();
    return true;
  }
  notify(names) {
    const ctx=this.ctx;
    ctx[kDomain].refreshChecks(names.map(name=>ctx[kDomain].port(ctx,name)));
    for (const name of names) ctx.emit('internal/service',name,this.get(name,false));
    ctx[kDomain].schedule();
    return [];
  }
  accessor(name,options) {
    return this.ctx.fiber.effect(()=>{
      if (name in this.props) throw new Error(`property "${name}" is already declared as ${this.props[name].type}`);
      this.props[name]={type:'accessor',...options};
      return ()=>delete this.props[name];
    },`ctx.accessor(${JSON.stringify(name)})`);
  }
  mixin(source,mixins) {
    const self=this;
    return this.ctx.fiber.effect(function* () {
      const entries=Array.isArray(mixins)?mixins.map(name=>[name,name]):Object.entries(mixins);
      for (const [from,to] of entries) yield self.accessor(to,{
        get(receiver) {
          const service=this[source];
          if (service==null) return service;
          const target=receiver?withProps(receiver,service):service;
          const value=Reflect.get(service,from,target);
          return typeof value==='function'?value.bind(target):value;
        },
        set(value,receiver) {
          const service=this[source];
          return Reflect.set(service,from,value,receiver?withProps(receiver,service):service);
        },
      });
    },`ctx.mixin(${JSON.stringify(source)})`);
  }
  trace(value) { return getTraceable(this.ctx,value); }
  bind(callback) { return new Proxy(callback,{apply:(target,self,args)=>Reflect.apply(target,this.trace(self),args.map(arg=>this.trace(arg))),construct:(target,args,newTarget)=>Reflect.construct(target,args.map(arg=>this.trace(arg)),newTarget)}); }
}

export class Context {
  static effect=symbols.effect;
  static filter=symbols.filter;
  static isolate=symbols.isolate;
  static intercept=symbols.intercept;
  static is(value) { return !!value?.[Symbol.for('cordis.is')]; }
  constructor(options={}) {
    const domain=new Domain(options);
    Object.defineProperty(this,kDomain,{value:domain});
    this[symbols.isolate]=Object.create(null);
    this[symbols.intercept]=Object.create(null);
    const self=new Proxy(this,contextHandler);
    this.root=self;
    this.baseUrl=undefined;
    const {id}=domain.command({op:'mount',dependencies:[],provisions:[]});
    this.fiber=new Fiber(self,null,{},Object.create(null),id);
    this.fiber.dispose = () => this.fiber.restart();
    domain.fibers.set(id,this.fiber);
    const {actions}=domain.command({op:'drive'});
    const action=actions.find(action=>action.id===id && action.kind==='setup');
    if (!action) throw new Error('Native root setup was not admitted');
    this.fiber._generation=action.ticket.generation;
    domain.command({op:'complete',ticket:action.ticket,success:true});
    this.fiber.state=FiberState.ACTIVE;
    this.reflect=new ReflectService(self);
    this.registry=new RegistryService(self);
    domain.registry=this.registry;
    this.events=new EventsService(self);
    domain.events=this.events;
    this.reflect.mixin('reflect',['get','set','provide','accessor','mixin']);
    this.reflect.mixin('registry',['plugin','inject']);
    this.reflect.mixin('fiber',['effect','task']);
    this.reflect.mixin('events',['on','once','emit','parallel','serial','bail','waterfall']);
    this.logger=new LoggerService(self);
    // Infrastructure accessors remain available during every user cleanup, as in upstream.
    this.fiber._disposables.clear();
    return self;
  }
  [Symbol.for('cordis.is')]=true;
  [Symbol.for('nodejs.util.inspect.custom')]() { return `Context <${this.fiber.name}>`; }
  extend(meta={}) {
    const shadow=Reflect.getOwnPropertyDescriptor(this,symbols.shadow)?.value;
    const self=Object.create(getTraceable(this,this));
    for (const key of Reflect.ownKeys(meta)) Object.defineProperty(self,key,Object.getOwnPropertyDescriptor(meta,key));
    return shadow?Object.assign(Object.create(self),{[symbols.shadow]:shadow}):self;
  }
  isolate(name,label=Symbol(name)) { return this.extend({[symbols.isolate]:Object.assign(Object.create(this[symbols.isolate]),{[name]:label})}); }
  intercept(name,config) { return this.extend({[symbols.intercept]:Object.assign(Object.create(this[symbols.intercept]),{[name]:config})}); }
  rustPlugin(name, config) { return this.plugin(this[kDomain].rust.plugin(name),config); }
  async settle() { await this[kDomain].settle(); }
  snapshot() { return {...this[kDomain].command({op:'snapshot'}),diagnostics:[...this[kDomain].diagnostics]}; }
  async dispose() {
    assertNotWaitingForAncestor(this.root.fiber,'domain disposal');
    const domain=this[kDomain];
    if (domain.closed) return domain.closing;
    domain.assertMutationAdmission({closing:true,recovery:true});
    if (domain.closing) return domain.closing;
    domain.closing=Promise.resolve(domain.enqueueMutation(() => this.root.fiber._dispose().then(() => {
      domain.rust.close(); domain.closed=true;
    }), {closing:true,recovery:true})).catch(error=>{domain.closing=undefined;throw error;});
    return domain.closing;
  }
}
