// Explicit JSON service adapters for user-compiled Rust factories. Rust owns
// Futures and values; the ordinary Fiber journal owns their graph lifetime.
import { symbols } from './utils.js';
import { types } from 'node:util';
import { randomUUID } from 'node:crypto';
import { JavaScriptStreams, rustStream } from './rust-streams.js';
import { JavaScriptObjects, isOpaqueValue, rustObject } from './rust-objects.js';

// Root a domain only while Rust work is actually outstanding. An idle N-API
// callback must not retain Host → Domain → NativeDriver → callback forever.
const activeHosts = new Set();

function errorText(error) {
  try { return String(error); } catch { return 'JavaScript service threw an unprintable value'; }
}

export function jsonValue(value) {
  // Reject lossy or executable coercions rather than silently JSON-roundtripping
  // arbitrary JS values (Date, BigInt, toJSON, undefined, cycles, etc.).
  const seen = new Set();
  const visit = item => {
    if (item === null || typeof item === 'string' || typeof item === 'boolean') return item;
    if (typeof item === 'number' && Number.isFinite(item)) return item;
    if (typeof item !== 'object' || item === null) throw new TypeError('Rust service values must be finite JSON data');
    if (isOpaqueValue(item)) throw new TypeError('Opaque capabilities cannot be passed as JSON data');
    if (types.isProxy(item)) throw new TypeError('Rust service values cannot contain proxies');
    if (seen.has(item)) throw new TypeError('Rust service values cannot contain cycles');
    if (!Array.isArray(item) && ![Object.prototype, null].includes(Object.getPrototypeOf(item))) throw new TypeError('Rust service values must be plain JSON objects');
    if (Reflect.ownKeys(item).some(key => typeof key === 'symbol')) throw new TypeError('Rust service values cannot contain symbol keys');
    seen.add(item);
    const result = Array.isArray(item) ? [] : Object.create(null);
    const keys = Array.isArray(item) ? Array.from({length:item.length},(_,i)=>String(i)) : Object.keys(item);
    const allowed = new Set(Array.isArray(item) ? [...keys,'length'] : keys);
    if (Reflect.ownKeys(item).some(key => !allowed.has(key))) throw new TypeError('Rust service values cannot contain hidden or extra properties');
    for (const key of keys) {
      const descriptor = Object.getOwnPropertyDescriptor(item,key);
      if (!descriptor || !('value' in descriptor)) throw new TypeError('Rust service values cannot contain holes or accessors');
      result[key] = visit(descriptor.value);
    }
    seen.delete(item);
    return result;
  };
  return visit(value);
}

export class RustHost {
  constructor(domain, hooks) {
    this.domain = domain;
    this.hooks = hooks;
    this.sessions = new Map();
    this.jobs = new Map();
    this.results = new Map();
    this.factories = new Map();
    this.moduleFactories = new Map();
    this.typedChecks = new WeakMap();
    this.typedChildPlugins = new WeakMap();
    this.typedChildren = new Map();
    this.typedRealms = new Map();
    this.typedInjectionConfigs = new WeakMap();
    this.scheduled = false;
    this.streams = new JavaScriptStreams(this, jsonValue);
    this.objects = new JavaScriptObjects(this, jsonValue);
    this.jsonValue = jsonValue;
    const driver = domain.driver;
    if (typeof driver.rustInfo !== 'function') return;
    const info = JSON.parse(driver.rustInfo());
    if (info.abi !== 1) throw new Error('Unsupported Rust plugin ABI');
    for (const factory of info.factories) {
      if (this.factories.has(factory.name)) throw new Error('Duplicate Rust factory');
      this.factories.set(factory.name,{...factory,plugin:undefined});
    }
    if (this.factories.size) this.ensureWake();
  }
  ensureWake() {
    if (this.wakeInstalled) return;
    const weak = new WeakRef(this);
    this.domain.driver.rustWake(() => weak.deref()?.schedule());
    this.wakeInstalled = true;
  }
  loadModule(artifact) {
    const descriptor = this.command({op:'load_module',...artifact});
    if (descriptor.abi !== 1 || !Array.isArray(descriptor.factories)) throw new Error('Unsupported native module descriptor');
    this.ensureWake();
    const factories = new Map();
    for (const factory of descriptor.factories) {
      if (typeof factory.ref !== 'string' || !factory.ref || factories.has(factory.name)) throw new Error('Invalid native module factory identity');
      let known = this.moduleFactories.get(factory.ref);
      if (!known) {
        known = {...structuredClone(factory),plugin:undefined};
        this.moduleFactories.set(factory.ref,known);
      } else if (JSON.stringify({...known,plugin:undefined}) !== JSON.stringify({...factory,plugin:undefined})) {
        throw new Error('Native module changed an immutable factory reference');
      }
      factories.set(factory.name,known.plugin ?? this.makePlugin(known));
    }
    // Resource counts are live diagnostics, not immutable artifact metadata.
    const {resources:_resources,...metadata} = descriptor;
    return {descriptor:structuredClone(metadata),factories};
  }
  command(command) {
    // Interop can complete work, publish through reverse calls, or fault the
    // shared domain. Treat every operation as a writer, including future ones.
    this.domain.driverDirty = true;
    if (this.fault) throw this.fault;
    try {
      const reply = JSON.parse(this.domain.driver.rustCommand(JSON.stringify(command)));
      if (reply?.error) throw new Error(reply.error);
      return reply;
    } catch (error) {
      if (/DomainFaulted/.test(errorText(error))) this.fail(error);
      throw error;
    }
  }
  fail(error) {
    if (this.fault) return;
    this.fault = error;
    for (const waiter of this.jobs.values()) waiter.reject(error);
    this.jobs.clear();
    activeHosts.delete(this);
    this.results.clear();
    this.domain.diagnostics?.push({kind:'rust-domain-fault',cleanup:'unconfirmed',error:errorText(error)});
    this.domain.errors.push(error);
    this.domain.wake();
  }
  schedule() {
    if (this.scheduled || this.fault) return;
    this.scheduled = true;
    queueMicrotask(() => {
      this.scheduled = false;
      try { this.poll(); } catch (error) { this.fail(error); }
    });
  }
  poll() {
    const reply = this.command({op:'poll'});
    for (const request of reply.calls ?? []) {
      // This promise boundary releases all Rust borrows before arbitrary JS.
      Promise.resolve().then(() => this.dispatch(request)).then(
        value => this.command({op:'reply',request:request.request,success:true,value:jsonValue(value ?? null)}),
        error => this.command({op:'reply',request:request.request,success:false,error:errorText(error)}),
      ).then(() => this.schedule(),error => { if (!this.fault) { this.domain.errors.push(error); this.domain.wake(); } });
    }
    for (const result of reply.jobs ?? []) {
      const waiter = this.jobs.get(result.job);
      if (waiter) { this.jobs.delete(result.job); this.finish(waiter,result); }
      else this.results.set(result.job,result);
    }
    this.childActions(reply.children);
    this.notifyServices(reply.serviceNotifications);
    this.domain.wake();
  }
  notifyServices(notifications) {
    for (const notice of notifications ?? []) {
      const session = this.sessions.get(notice.session);
      if (!session || session.closed || session.cancelled || session.token.generation !== notice.generation
        || session.token.fiber._generation !== notice.generation) continue;
      if (notice.ports.length) this.domain.refreshChecks(notice.ports);
    }
  }
  // Ordinary JS Service.check keeps its zero-argument contract. Native typed
  // checks receive the exact pending ticket, never an unowned root lookup.
  check(checker,receiver,action) {
    const typed = this.typedChecks.get(checker);
    if (!typed) return Reflect.apply(checker,receiver,[]);
    const {session,service} = typed;
    if (session.closed || session.cancelled) return false;
    const ctx = receiver[symbols.caller] ?? receiver.ctx;
    const names = session.factory.ports ?? [...session.factory.inject,...session.factory.services.map(item=>item.name)];
    const realms = Object.fromEntries(names.map(name=>[name,this.domain.port(ctx,name)]));
    const declared = this.typedInjectionConfigs.get(ctx.fiber.runtime?.callback);
    const config = declared && Object.hasOwn(declared,service)
      ? declared[service] : ctx[symbols.intercept]?.[service] ?? null;
    return this.command({op:'typed_check',session:session.id,service,ticket:action.ticket,
      realms,config:jsonValue(config)}).available;
  }
  finish(waiter,result) {
    if (result.success) waiter.resolve(result.value);
    else waiter.reject(new Error(result.error ?? 'Rust job failed'));
  }
  wait(job, session, kind, caller, resource) {
    if (this.fault) return Promise.reject(this.fault);
    const waiter = Promise.withResolvers();
    const result = this.results.get(job);
    if (result) { this.results.delete(job); this.finish(waiter,result); }
    else { this.jobs.set(job,waiter); activeHosts.add(this); }
    const token = this.hooks.invocation();
    const ancestors = token?.rustResources ?? (token?.rustResource ? [token.rustResource] : []);
    const record = {job,kind,resource,ancestors,promise:waiter.promise,cancel:()=>['stream-close','object-close'].includes(kind) ? undefined : this.command({op:'cancel_job',job})};
    session.jobs.add(record);
    if (caller) (caller._rustCalls ??= new Set()).add(record);
    const finish = () => {session.jobs.delete(record); caller?._rustCalls?.delete(record); if (!this.jobs.size) activeHosts.delete(this); this.domain.wake();};
    waiter.promise.then(finish,finish);
    this.schedule();
    return waiter.promise;
  }
  plugin(name) {
    const factory = this.factories.get(name);
    if (!factory) throw new Error(`Rust factory is not registered in this addon: ${name}`);
    if (factory.plugin) return factory.plugin;
    return this.makePlugin(factory);
  }
  makePlugin(factory) {
    const name = factory.name;
    const plugin = {
      name:`rust:${name}`, inject:factory.injectConfig
        ? Object.fromEntries(factory.inject.map(service=>[service,structuredClone(factory.injectConfig[service] ?? null)]))
        : [...factory.inject],
      apply:async (ctx,config) => {
        const token = this.hooks.invocation();
        const activeFactory = this.anchorFactory(factory,token.fiber);
        if (activeFactory.anchor) ctx = ctx.isolate(activeFactory.anchor.name,activeFactory.anchor.realm);
        const ports = this.ports(ctx,activeFactory);
        // A rejected start can still have created a persistent typed definition.
        token.fiber._rustDefinition = true;
        const reply = this.command({op:'start',ticket:token.ticket,factory:factory.ref ?? name,config:jsonValue(config ?? null),ports});
        const session = {id:reply.session,ctx,factory:activeFactory,token:{...token},setupToken:token,jobs:new Set(),services:new Map(),resources:new Set(),objects:new Set(),cancelled:false,closed:false,cleaning:false};
        this.sessions.set(session.id,session);
        token.fiber._typedRealmKeys=reply.realms;
        for (const realm of reply.realms ?? []) this.typedRealms.set(`${realm.key}:${realm.realm}`,ctx[symbols.isolate][realm.name]);
        // Own teardown before polling setup, including partially failing setup.
        // Rust instances remain available through every ordinary JS inverse and
        // object release. Failed inverses must not destroy a retry dependency.
        (token.fiber._rustSessions ??= new Set()).add(session);
        session.close = async () => {
          this.cancel(session);
          await this.closeResources(session.resources);
          await this.closeObjects(session.objects);
          await Promise.allSettled([...session.jobs].map(job => job.promise));
          session.cleaning = true;
          session.cleanupToken = {...this.hooks.invocation()};
          const ticket = session.cleanupToken.ticket;
          if (!session.cleanupDone) {
            const cleanup = this.command({op:'cleanup',session:session.id,ticket});
            await this.wait(cleanup.job,session,'cleanup');
            session.cleanupDone = true;
          }
          this.command({op:'release',session:session.id});
          session.closed = true;
          this.sessions.delete(session.id);
          token.fiber._rustSessions.delete(session);
        };
        await this.wait(reply.job,session,'setup');
      },
    };
    // Pending consumers have no Rust session yet. Tie their fixed declaration
    // to this actual callback, preserving explicit null over inherited config.
    if (factory.injectConfig) this.typedInjectionConfigs.set(plugin.apply,structuredClone(factory.injectConfig));
    factory.plugin = plugin;
    return plugin;
  }
  ports(ctx,factory) {
    return Object.fromEntries((factory.ports ?? [...factory.inject,...factory.services.map(service=>service.name)]).map(name=>[name,this.domain.port(ctx,name)]));
  }
  anchorFactory(factory,fiber) {
    if (!factory.dynamic || factory.anchor) return factory;
    const anchor = fiber._typedAnchor ??= {name:`__cordis_typed_anchor_${randomUUID()}`,realm:Symbol('typed owner anchor')};
    return {...factory,anchor,ports:[...factory.ports,anchor.name],services:[...factory.services,{name:anchor.name,methods:[]}]};
  }
  allocated(callback,fiber) {
    this.typedChildPlugins.get(callback)?.allocated(fiber);
  }
  dependencies(callback,fiber,ports) {
    const child = this.typedChildPlugins.get(callback);
    if (!child) return ports;
    const result = [...ports];
    for (const port of child.inherited) if (!result.some(item=>item.key===port.key && item.realm===port.realm)) result.push(port);
    return result;
  }
  childActions(actions) {
    for (const action of actions ?? []) {
      const parent = this.sessions.get(action.session);
      if (action.kind==='error') { this.domain.errors.push(new Error(action.error)); this.domain.schedule(); continue; }
      if (action.kind==='retire') {
        const child=this.typedChildren.get(action.child);
        if (!child || child.parent!==parent || child.fiber.id!==action.id) throw new Error('Typed child retirement identity mismatch');
        try {
          const result=this.hooks.childRetire(parent,()=>child.fiber._dispose());
          Promise.resolve(result).catch(error=>{ if (!child.fiber._removedFlag) this.domain.errors.push(error); }).finally(()=>this.schedule());
        } catch(error) { this.domain.errors.push(error); }
        continue;
      }
      if (action.kind!=='mount') throw new Error('Unknown typed child action');
      let fiber;
      try {
        this.hooks.child(parent,()=>{
          let ctx=parent.ctx;
          for(const realm of action.factory.realms) {
            const key=`${realm.key}:${realm.realm}`;
            if(!this.typedRealms.has(key)) this.typedRealms.set(key,Symbol(`typed realm:${key}`));
            ctx=ctx.isolate(realm.name,this.typedRealms.get(key));
          }
          const plugin=this.makePlugin(action.factory);
          this.typedChildPlugins.set(plugin.apply,{inherited:action.factory.inherited,allocated:created=>{
            fiber=created;
            const factory=this.anchorFactory(action.factory,fiber);
            const childCtx=fiber.ctx.isolate(factory.anchor.name,factory.anchor.realm);
            fiber._rustDefinition=true;
            fiber._typedChild=action.child;
            this.typedChildren.set(action.child,{parent,fiber,factory});
            this.command({op:'typed_child_mounted',child:action.child,id:fiber.id,ports:this.ports(childCtx,factory)});
          }});
          ctx.plugin(plugin);
          if(!fiber) throw new Error('Typed native allocation was not acknowledged');
        });
      } catch(error) {
        if(!fiber) this.command({op:'typed_child_rejected',child:action.child,error:errorText(error)});
        else {
          // Allocation has happened; never report it as an unallocated rejection.
          this.domain.errors.push(error);
          if (!fiber._removedFlag) {
            this.command({op:'typed_child_aborted',child:action.child,error:errorText(error)});
            this.hooks.childRetire(parent,()=>fiber._dispose()).catch(error=>this.domain.errors.push(error));
          }
        }
      }
    }
  }
  removed(fiber) {
    if (fiber._rustDefinition) {
      this.command({op:'forget',id:fiber.id});
      fiber._rustDefinition = false;
      if (fiber._typedChild) this.typedChildren.delete(fiber._typedChild);
      if (fiber._typedAnchor) {
        const {name,realm}=fiber._typedAnchor;
        for(const entry of fiber._typedRealmKeys ?? []) if(entry.name===name) this.typedRealms.delete(`${entry.key}:${entry.realm}`);
        this.domain.services.delete(name);
        this.domain.realms.delete(realm);
        delete fiber.ctx.root[symbols.isolate][name];
      }
    }
  }
  close() {
    if (typeof this.domain.driver.rustCommand !== 'function') return;
    this.command({op:'close'});
    activeHosts.delete(this);
  }
  cancel(session) {
    if (session.cancelled || session.closed) return;
    session.cancelled = true;
    this.command({op:'cancel',session:session.id});
    for (const resource of session.resources ?? []) resource.close().catch(() => {});
    this.schedule();
  }
  sync(item) {
    const fiber=this.domain.fibers.get(item.id);
    if(fiber?._typedChild) {
      const state=JSON.stringify([item.generation,item.state,item.cleanupFailed,item.error]);
      if(state!==fiber._typedObserved) { fiber._typedObserved=state;this.command({op:'typed_child_observed',child:fiber._typedChild}); }
    }
    if (item.retired || String(item.state).toLowerCase() === 'unloading') {
      for (const session of this.sessions.values()) if (session.token.fiber.id === item.id) this.cancel(session);
      for (const resource of this.domain.fibers?.get(item.id)?._rustResources ?? []) {
        if (!resource.closing) resource.close().catch(() => {});
      }
    }
  }
  dispatch(request) {
    const session = this.sessions.get(request.session);
    if (!session || session.closed) throw new Error('Rust session is closed');
    const job = [...session.jobs].find(job => job.job === request.job);
    if (!job) throw new Error('Rust request belongs to an unknown or completed job');
    // A setup reverse call may publish after recovery admits a pending restart.
    // Keep the original invocation reference: its active flag closes when the
    // real setup lands. A copied active:true flag must not become lasting setup
    // authority for detached reverse-call continuations or ordinary methods.
    const scope = job.kind === 'setup'
      ? {...session.token,kind:'setup',active:false,parentInvocation:session.setupToken}
      : job.kind === 'cleanup' ? session.cleanupToken : {...session.token,kind:'rust-call'};
    const token = {...scope,rustAuthority:{session:session.id,job:job.job,request:request.request},rustResource:job.resource,rustResources:[...new Set([...(job.ancestors ?? []),...(job.resource ? [job.resource] : [])])]};
    return this.hooks.run(token,() => {
      if (request.kind === 'provide') {
        const descriptor = session.factory.services.find(service => service.name === request.service);
        if (!descriptor) throw new Error(`Undeclared Rust service: ${request.service}`);
        const host = this;
        const service = Object.create(null);
        Object.defineProperty(service,'ctx',{value:session.ctx,configurable:true});
        Object.defineProperty(service,symbols.tracker,{value:{property:'ctx',associate:descriptor.name}});
        for (const method of descriptor.methods) {
          if (['ctx','then','__proto__','constructor'].includes(method.name)) throw new Error(`Reserved Rust method name: ${method.name}`);
          Object.defineProperty(service,method.name,{enumerable:true,get() {
            const ctx = this[symbols.caller] ?? this.ctx;
            const fiber = ctx.fiber;
            const generation = fiber._generation;
            return (...args) => host.call(session,service,descriptor,method,ctx,fiber,generation,args);
          }});
        }
        let checker;
        if (request.args?.checked) {
          checker = () => { throw new Error('Typed check requires its native availability ticket'); };
          this.typedChecks.set(checker,{session,service:descriptor.name});
        }
        session.ctx.provide(descriptor.name,service,checker);
        session.services.set(descriptor.name,service);
        const port = this.domain.port(session.ctx,descriptor.name);
        const publication = session.ctx.fiber._publications.get(JSON.stringify(port)).publication;
        return {publication,port};
      }
      if (request.kind === 'close_orphans') return this.streams.closeOrphans(session).then(()=>this.objects.closeOrphans(session));
      if (request.kind === 'stream_next') return this.streams.next(this.streams.get(session,request));
      if (request.kind === 'stream_close') return this.streams.close(this.streams.get(session,request,true));
      if (request.kind === 'object_call') return this.objects.call(this.objects.get(session,request),request.method,request.args);
      if (request.kind === 'object_close') return this.objects.close(this.objects.get(session,request,true));
      if (!['call','stream_open','object_open'].includes(request.kind)) throw new Error(`Unsupported Rust host operation: ${request.kind}`);
      if (!session.factory.inject.includes(request.service)) throw new Error('Rust call requires a declared dependency');
      if (!Array.isArray(request.args)) throw new TypeError('Rust call arguments must be a JSON array');
      const service = session.ctx[request.service];
      const method = service?.[request.method];
      if (typeof method !== 'function') throw new TypeError(`Unknown JS method: ${request.service}.${request.method}`);
      if (request.kind === 'stream_open') return this.streams.open(session,request,service,method);
      if (request.kind === 'object_open') return this.objects.open(session,request,service,method);
      return Promise.resolve(Reflect.apply(method,service,request.args)).then(value => jsonValue(value ?? null));
    });
  }
  caller(fiber,generation) {
    const token = this.hooks.invocation();
    const authority = token?.fiber?._domain === this.domain ? token.rustAuthority : undefined;
    return {id:fiber.id,generation,...(authority ? {authority} : {}),...(token?.fiber === fiber && token.kind === 'cleanup' ? {ticket:token.ticket} : {})};
  }
  async closeResources(resources) {
    const results = await Promise.allSettled([...(resources ?? [])].map(resource => resource.close()));
    const errors = results.filter(result => result.status === 'rejected').map(result => result.reason);
    if (errors.length) throw new AggregateError(errors,'Rust stream cleanup failed');
  }
  async closeSessions(fiber) {
    for (const session of [...(fiber._rustSessions ?? [])].reverse()) await session.close();
  }
  async closeObjects(objects) {
    // Retain earlier objects when a later acquisition cannot be released yet.
    for (const object of [...(objects ?? [])].reverse()) await object.close();
  }
  call(session,service,descriptor,method,ctx,fiber,generation,args) {
    this.hooks.assertCurrent(this.domain);
    if (session.closed || session.cleaning || fiber._removedFlag || fiber._generation !== generation) throw this.hooks.stale();
    const current = ctx[descriptor.name];
    if ((current?.[symbols.original] ?? current) !== service) throw this.hooks.stale();
    if (['stream','object'].includes(method.kind) && (session.cancelled || fiber.state === 5 || this.hooks.invocation()?.kind === 'cleanup')) throw new Error(method.kind === 'stream' ? 'StreamAdmissionClosed' : 'ObjectAdmissionClosed');
    const caller = this.caller(fiber,generation);
    const reply = this.command({op:'call',session:session.id,service:descriptor.name,method:method.name,args:jsonValue(args),caller});
    if (method.kind === 'sync') {
      this.childActions(reply.children);
      this.notifyServices(reply.serviceNotifications);
      if (!Object.hasOwn(reply,'value')) throw new Error('Rust sync method returned no value');
      return reply.value;
    }
    if (method.kind === 'stream') {
      if (typeof reply.stream !== 'string') throw new Error('Rust stream method returned no resource');
      return rustStream(this,session,reply.stream,fiber,generation);
    }
    if (method.kind === 'object') {
      if (typeof reply.object !== 'string' || !reply.descriptor) throw new Error('Rust object method returned no capability');
      return rustObject(this,session,reply.object,reply.descriptor,fiber,generation);
    }
    return this.wait(reply.job,session,'call',fiber);
  }
}
