// JS iterator values stay in this environment. Only private, monotonic resource
// identities and finite JSON elements cross the native boundary.
export class JavaScriptStreams {
  constructor(host, jsonValue) {
    this.host = host;
    this.jsonValue = jsonValue;
    this.nextId = 0n;
    this.resources = new Map();
  }
  async open(session, request, service, method) {
    const source = await Reflect.apply(method, service, request.args);
    if (!source || !['object', 'function'].includes(typeof source)) throw new TypeError('JS stream must return an AsyncIterator');
    const iterate = source[Symbol.asyncIterator];
    const iterator = typeof iterate === 'function' ? Reflect.apply(iterate, source, []) : source;
    if (!iterator || !['object', 'function'].includes(typeof iterator)) throw new TypeError('JS stream must return an AsyncIterator');
    // Cache arbitrary getters exactly once. An explicit return method is part
    // of this adapter contract; absence is not evidence of resource release.
    const close = iterator.return;
    if (typeof close !== 'function') throw new TypeError('JS stream requires an explicit return method');
    const id = String(++this.nextId);
    const record = {id, session:session.id, job:request.job, iterator, close, closing:false, pending:undefined, attempt:undefined};
    this.resources.set(id, record);
    try {
      record.next = iterator.next;
      if (typeof record.next !== 'function') throw new TypeError('JS stream requires a next method');
    } catch (error) {
      // Keep malformed acquisitions discoverable for the session's cleanup if
      // their return also fails; never pretend a throwing destructor succeeded.
      record.orphan = true;
      try { await this.close(record); } catch (cleanupError) { throw new AggregateError([error, cleanupError], 'Invalid JS stream and failed close'); }
      throw error;
    }
    return {stream:id};
  }
  get(session, request, close = false) {
    const record = this.resources.get(request.stream);
    if (!record || record.session !== session.id) throw new Error('StaleStream');
    if (!close && record.job !== request.job) throw new Error('StaleStreamAuthority');
    return record;
  }
  result(value) {
    if (!value || typeof value !== 'object') throw new TypeError('JS iterator result must be an object');
    const done = value.done;
    if (typeof done !== 'boolean') throw new TypeError('JS iterator result requires boolean done');
    const item = value.value;
    return {done, value:this.jsonValue(item ?? null)};
  }
  next(record) {
    if (record.closing) throw new Error('StreamClosing');
    if (record.pending) throw new Error('StreamBusy');
    // Set the in-flight marker before invoking arbitrary JS (including a
    // synchronous iterator), so reentry cannot start another pull.
    const completion = Promise.withResolvers();
    record.pending = completion.promise;
    Promise.resolve().then(() => Reflect.apply(record.next, record.iterator, [])).then(value => this.result(value)).then(completion.resolve, completion.reject);
    const finish = () => { if (record.pending === completion.promise) record.pending = undefined; };
    completion.promise.then(finish, finish);
    return completion.promise;
  }
  close(record) {
    if (!this.resources.has(record.id)) return Promise.resolve({done:true, value:null});
    if (record.attempt) return record.attempt;
    record.closing = true;
    const completion = Promise.withResolvers();
    record.attempt = completion.promise;
    const pending = record.pending;
    // return may be the only operation that can wake next. Issue it first,
    // then join both real outcomes, even when return itself rejects.
    const returned = Promise.resolve().then(() => Reflect.apply(record.close, record.iterator, [])).then(value => {
      const result = this.result(value);
      if (!result.done) throw new Error('IncompleteStreamClose: return yielded done:false');
    });
    Promise.allSettled([returned, ...(pending ? [pending] : [])]).then(results => {
      if (results[0].status === 'rejected') throw results[0].reason;
      this.resources.delete(record.id);
      return {done:true, value:null};
    }).then(completion.resolve, completion.reject);
    const finish = () => { if (record.attempt === completion.promise) record.attempt = undefined; };
    completion.promise.then(finish, finish);
    return completion.promise;
  }
  async closeOrphans(session) {
    const results = await Promise.allSettled([...this.resources.values()].filter(record => record.session === session.id && record.orphan).map(record => this.close(record)));
    const errors = results.filter(result => result.status === 'rejected').map(result => result.reason);
    if (errors.length) throw new AggregateError(errors, 'JS stream acquisition cleanup failed');
  }
}

export function rustStream(host, session, id, caller, generation) {
  const resource = {id, session, caller, generation, closing:false, closed:false, pending:undefined, attempt:undefined};
  const validate = () => {
    host.hooks.assertCurrent(host.domain);
    if (session.closed || session.cleaning || caller._removedFlag || caller.state === 5 || caller._generation !== generation) throw host.hooks.stale();
    const token = host.hooks.invocation();
    if (token?.fiber && token.fiber !== caller && (!token.rustAuthority || token.fiber._domain !== host.domain)) throw new Error('StreamOwnerMismatch');
  };
  const close = () => {
    const token = host.hooks.invocation();
    if (token?.rustResource === resource || token?.rustResources?.includes(resource)) return Promise.reject(new Error('ReentrantStreamClose: cannot await the current stream operation'));
    if (resource.closed) return Promise.resolve({done:true, value:undefined});
    if (resource.attempt) return resource.attempt;
    resource.closing = true;
    // Native close immediately cancels the active pull, retains its exact
    // publication, and only completes after every issued reverse call lands.
    const completion = Promise.withResolvers();
    resource.attempt = completion.promise;
    try {
      const reply = host.command({op:'stream_close', session:session.id, stream:id});
      const closed = reply.job ? host.wait(reply.job,session,'stream-close',caller,resource) : Promise.resolve();
      closed.then(() => {
        resource.closed = true;
        session.resources.delete(resource);
        caller._rustResources?.delete(resource);
        completion.resolve({done:true, value:undefined});
      }, completion.reject);
    } catch (error) { completion.reject(error); }
    const finish = () => { if (resource.attempt === completion.promise) resource.attempt = undefined; host.domain.wake(); };
    completion.promise.then(finish,finish);
    return completion.promise;
  };
  resource.close = close;
  const next = async () => {
    validate();
    if (resource.closed) return {done:true,value:undefined};
    if (resource.closing) throw host.hooks.stale();
    if (resource.pending) throw new Error('StreamBusy');
    const reply = host.command({op:'stream_next', session:session.id, stream:id, caller:host.caller(caller,generation)});
    const pending = host.wait(reply.job,session,'stream-next',caller,resource);
    resource.pending = pending;
    let result;
    try { result = await pending; }
    catch (error) {
      try { await close(); } catch (cleanupError) {
        if (cleanupError === error) throw error;
        throw new AggregateError([error,cleanupError],'Rust stream pull and close failed');
      }
      throw error;
    } finally { if (resource.pending === pending) resource.pending = undefined; }
    if (result.done) await close();
    return {done:result.done, value:result.done ? undefined : result.value};
  };
  const iterator = Object.freeze({next, return:close, async throw(error) { await close(); throw error; }, [Symbol.asyncIterator]() { return this; }});
  (session.resources ??= new Set()).add(resource);
  (caller._rustResources ??= new Set()).add(resource);
  // A reentrant withdrawal during open never leaves an unowned idle stream.
  if (session.cancelled || caller._removedFlag || caller._generation !== generation) close().catch(() => {});
  return iterator;
}
