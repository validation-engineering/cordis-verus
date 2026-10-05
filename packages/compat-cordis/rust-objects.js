// Capabilities never travel as user JSON. Adapters and public Rust handles have
// private brands; only the declared JSON method interface crosses the boundary.
const adapters = new WeakMap();
const handles = new WeakSet();
const targets = new WeakMap();

export const isOpaqueValue = value => adapters.has(value) || handles.has(value);

function descriptor(options) {
  if (!options) throw new TypeError('Object adapter requires options');
  const {typeName,methods,ownership,dispose} = options;
  const names = Array.isArray(methods) ? Array.from(methods) : [];
  if (typeof typeName !== 'string' || !typeName.length) throw new TypeError('Object adapter requires a typeName');
  if (!names.length || names.some(name => typeof name !== 'string' || !name.length) || new Set(names).size !== names.length) throw new TypeError('Object adapter requires distinct method names');
  if (!['borrowed','owned'].includes(ownership)) throw new TypeError('Object adapter requires explicit borrowed or owned ownership');
  if (ownership === 'owned' && typeof dispose !== 'function') throw new TypeError('Owned object adapter requires an explicit dispose function');
  if (ownership === 'borrowed' && dispose !== undefined) throw new TypeError('Borrowed object adapter cannot declare a disposer');
  return {descriptor:Object.freeze({typeName,methods:Object.freeze(names),ownership}),dispose};
}
export function adaptObject(target, options) {
  if (!target || !['object','function'].includes(typeof target)) throw new TypeError('Object adapter target must be an object');
  const source = descriptor(options);
  const adapter = Object.freeze(Object.create(null));
  adapters.set(adapter,{target,...source});
  return adapter;
}
export function adaptCallback(callback, options = {}) {
  if (typeof callback !== 'function') throw new TypeError('Callback adapter requires a function');
  const config = {...options};
  const adapter = adaptObject(callback,{...config,typeName:config.typeName ?? 'callback',methods:['call'],ownership:config.ownership ?? 'borrowed'});
  adapters.get(adapter).callback = true;
  return adapter;
}

export class JavaScriptObjects {
  constructor(host, jsonValue) {
    this.host = host;
    this.jsonValue = jsonValue;
    this.nextId = 0n;
    this.resources = new Map();
  }
  async open(session, request, service, method) {
    const adapter = await Reflect.apply(method,service,request.args);
    const source = adapters.get(adapter);
    if (!source) throw new TypeError('JS object method must return an explicit adaptObject/adaptCallback capability');
    const state = targets.get(source.target) ?? {borrowed:new Set(),owned:false};
    if (state.owned || (source.descriptor.ownership === 'owned' && state.borrowed.size)) throw new Error('ObjectOwnershipConflict');
    const id = String(++this.nextId);
    const record = {id,session:session.id,job:request.job,source,methods:new Map(),pending:new Set(),closing:false,attempt:undefined,state};
    if (source.descriptor.ownership === 'owned') state.owned = true;
    else state.borrowed.add(record);
    targets.set(source.target,state);
    this.resources.set(id,record);
    try {
      for (const name of source.descriptor.methods) {
        const callback = source.callback ? source.target : source.target[name];
        if (typeof callback !== 'function') throw new TypeError(`Unknown object method: ${name}`);
        record.methods.set(name,callback);
      }
    } catch (error) {
      record.orphan = true;
      try { await this.close(record); } catch (cleanupError) { throw new AggregateError([error,cleanupError],'Invalid JS object and failed disposal'); }
      throw error;
    }
    return {object:id,descriptor:source.descriptor};
  }
  get(session, request, close = false) {
    const record = this.resources.get(request.object);
    if (!record || record.session !== session.id) throw new Error('StaleObject');
    const job = [...session.jobs].find(job => job.job === request.job);
    if (record.job !== request.job && !(close && job?.kind === 'cleanup')) throw new Error('StaleObjectAuthority');
    return record;
  }
  call(record, method, args) {
    if (record.closing) throw new Error('ObjectClosing');
    if (!Array.isArray(args)) throw new TypeError('Object arguments must be a JSON array');
    const callback = record.methods.get(method);
    if (!callback) throw new Error(`UndeclaredObjectMethod: ${method}`);
    const completion = Promise.withResolvers();
    record.pending.add(completion.promise);
    Promise.resolve().then(() => Reflect.apply(callback,record.source.callback ? undefined : record.source.target,args)).then(value => this.jsonValue(value ?? null)).then(completion.resolve,completion.reject);
    const finish = () => record.pending.delete(completion.promise);
    completion.promise.then(finish,finish);
    return completion.promise;
  }
  close(record) {
    if (!this.resources.has(record.id)) return Promise.resolve({closed:true});
    if (record.attempt) return record.attempt;
    record.closing = true;
    const completion = Promise.withResolvers();
    record.attempt = completion.promise;
    // Unlike stream.return, object disposal cannot safely run before methods
    // finish using the object. Closing rejects new calls and joins all issued ones.
    Promise.allSettled([...record.pending]).then(async () => {
      if (record.source.descriptor.ownership === 'owned') await Reflect.apply(record.source.dispose,undefined,[record.source.target]);
      this.resources.delete(record.id);
      record.state.borrowed.delete(record);
      if (!record.state.owned && !record.state.borrowed.size) targets.delete(record.source.target);
      return {closed:true};
    }).then(completion.resolve,completion.reject);
    const finish = () => { if (record.attempt === completion.promise) record.attempt = undefined; };
    completion.promise.then(finish,finish);
    return completion.promise;
  }
  async closeOrphans(session) {
    for (const record of [...this.resources.values()].reverse()) {
      if (record.session === session.id && record.orphan) await this.close(record);
    }
  }
}

export function rustObject(host,session,id,description,caller,generation) {
  const resource = {id,session,caller,generation,closing:false,closed:false,attempt:undefined};
  const methods = Object.freeze([...description.methods]);
  const allowed = new Set(methods);
  const call = (method,...args) => {
    try {
      host.hooks.assertCurrent(host.domain);
      if (resource.closed || resource.closing || session.closed || session.cleaning || caller._removedFlag || caller._generation !== generation) throw host.hooks.stale();
      const token = host.hooks.invocation();
      if (token?.fiber && token.fiber !== caller && (!token.rustAuthority || token.fiber._domain !== host.domain)) throw new Error('ObjectOwnerMismatch');
      if (!allowed.has(method)) throw new Error(`UndeclaredObjectMethod: ${method}`);
      const reply = host.command({op:'object_call',session:session.id,object:id,method,args:host.jsonValue(args),caller:host.caller(caller,generation)});
      return host.wait(reply.job,session,'object-call',caller,resource);
    } catch (error) { return Promise.reject(error); }
  };
  const close = () => {
    const token = host.hooks.invocation();
    if (token?.rustResource === resource || token?.rustResources?.includes(resource)) return Promise.reject(new Error('ReentrantObjectClose: cannot await an ancestor object operation'));
    if (resource.closed) return Promise.resolve();
    if (resource.attempt) return resource.attempt;
    resource.closing = true;
    const completion = Promise.withResolvers();
    resource.attempt = completion.promise;
    try {
      const reply = host.command({op:'object_close',session:session.id,object:id});
      const closed = reply.job ? host.wait(reply.job,session,'object-close',caller,resource) : Promise.resolve();
      closed.then(() => {
        resource.closed = true;
        session.objects.delete(resource);
        caller._rustObjects?.delete(resource);
        completion.resolve();
      },completion.reject);
    } catch (error) { completion.reject(error); }
    const finish = () => { if (resource.attempt === completion.promise) resource.attempt = undefined; host.domain.wake(); };
    completion.promise.then(finish,finish);
    return completion.promise;
  };
  resource.close = close;
  const handle = {typeName:description.typeName,ownership:description.ownership,methods,call,close};
  if (methods.length === 1 && allowed.has('call')) handle.invoke = (...args) => call('call',...args);
  Object.freeze(handle);
  handles.add(handle);
  (session.objects ??= new Set()).add(resource);
  (caller._rustObjects ??= new Set()).add(resource);
  return handle;
}
