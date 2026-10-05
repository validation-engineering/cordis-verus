import test from 'node:test';
import assert from 'node:assert/strict';
import { AsyncLocalStorage } from 'node:async_hooks';
import { RustHost } from '../../packages/compat-cordis/rust-plugin.js';

const turn = () => new Promise(resolve => setImmediate(resolve));

// This wire only supplies admitted reverse requests and captures their replies.
// It does not simulate the native scheduler or make lifecycle decisions.
function bridge(service) {
  const invocation = new AsyncLocalStorage();
  const batches = [], replies = [], errors = [];
  const pending = new Map();
  let requestId = 0;
  const factory = { name: 'stream-fixture', inject: ['js'], services: [] };
  const domain = {
    errors, diagnostics: [], wake() {},
    driver: {
      rustInfo: () => JSON.stringify({ abi: 1, factories: [factory] }),
      rustWake() {},
      rustCommand(encoded) {
        const command = JSON.parse(encoded);
        if (command.op === 'poll') return JSON.stringify(batches.shift() ?? { calls: [], jobs: [] });
        if (command.op === 'reply') {
          replies.push(command);
          const waiter = pending.get(command.request);
          assert.ok(waiter, 'each reverse request must receive exactly one reply');
          pending.delete(command.request);
          waiter.resolve(command);
        }
        return '{}';
      },
    },
  };
  const host = new RustHost(domain, {
    invocation: () => invocation.getStore(),
    run: (token, callback) => invocation.run(token, callback),
    assertCurrent() {},
    stale: () => new Error('STALE_EPISODE'),
  });
  function session(id = '5', fiberId = '41') {
    const fiber = { id: fiberId, _generation: '7' };
    const token = { fiber, generation: '7', kind: 'setup', ticket: { domain: '9', id: fiberId, generation: '7', action: '11', kind: 'setup' } };
    const value = {
      id, ctx: { js: service, fiber }, factory, token,
      jobs: new Set(), services: new Map(), cancelled: false, closed: false, cleaning: false,
      cleanupToken: { ...token, kind: 'cleanup', ticket: { ...token.ticket, action: '99', kind: 'cleanup' } },
    };
    host.sessions.set(id, value);
    return value;
  }
  const owner = session();
  function admit(job = '21', kind = 'call', target = owner) {
    const record = { job, kind, promise: Promise.resolve() };
    target.jobs.add(record);
    return record;
  }
  const original = admit();
  function send(kind, fields = {}) {
    const request = String(++requestId);
    const waiter = Promise.withResolvers();
    pending.set(request, waiter);
    batches.push({ calls: [{ session: owner.id, job: '21', restoring: false, service: 'js', method: 'open', args: [], ...fields, request, kind }], jobs: [] });
    host.poll();
    return waiter.promise.then(reply => {
      if (!reply.success) throw new Error(reply.error);
      return reply.value;
    });
  }
  return { host, owner, original, invocation, errors, replies, pending, session, admit, send,
    open: fields => send('stream_open', fields),
    next: (stream, fields) => send('stream_next', { stream, ...fields }),
    close: (stream, fields) => send('stream_close', { stream, ...fields }),
  };
}

const closable = next => ({ next, return: () => ({ done: true, value: undefined }) });

test('reverse streams are pull driven and method getters are evaluated once', async () => {
  const reads = { method: 0, iterator: 0, next: 0, close: 0 };
  let pulls = 0, closes = 0;
  const iterator = {
    get next() {
      reads.next++;
      return function () { assert.equal(this, iterator); return { done: false, value: ++pulls }; };
    },
    get return() {
      reads.close++;
      return function () { assert.equal(this, iterator); closes++; return { done: true }; };
    },
  };
  const iterable = {
    get [Symbol.asyncIterator]() {
      reads.iterator++;
      return function () { assert.equal(this, iterable); return iterator; };
    },
  };
  const service = {
    get open() {
      reads.method++;
      return function (argument) { assert.equal(this, service); assert.equal(argument, 'input'); return iterable; };
    },
  };
  const wire = bridge(service);
  const { stream } = await wire.open({ args: ['input'] });
  assert.equal(typeof stream, 'string');
  await turn();
  assert.equal(pulls, 0, 'opening a stream must not prefetch an item');
  assert.deepEqual(await wire.next(stream), { done: false, value: 1 });
  await turn();
  assert.equal(pulls, 1, 'one pull must not start the next pull');
  assert.deepEqual(await wire.next(stream), { done: false, value: 2 });
  assert.deepEqual(await wire.close(stream), { done: true, value: null });
  assert.deepEqual(reads, { method: 1, iterator: 1, next: 1, close: 1 });
  assert.equal(closes, 1);
  assert.deepEqual(wire.errors, []);
});

for (const firstToLand of ['next', 'return']) {
  test(`stream close starts return before waiting for next and waits for ${firstToLand === 'next' ? 'return' : 'next'} too`, async () => {
    const nextGate = Promise.withResolvers(), closeGate = Promise.withResolvers();
    const nextEntered = Promise.withResolvers(), closeEntered = Promise.withResolvers();
    let returns = 0;
    const wire = bridge({ open: () => ({
      next() { nextEntered.resolve(); return nextGate.promise; },
      return() {
        returns++;
        closeEntered.resolve();
        if (firstToLand === 'next') nextGate.resolve({ done: true });
        else closeGate.resolve({ done: true });
        return closeGate.promise;
      },
    }) });
    const { stream } = await wire.open();
    const pull = wire.next(stream);
    await nextEntered.promise;
    let closed = false;
    const close = wire.close(stream).then(value => { closed = true; return value; });
    await closeEntered.promise;
    await turn();
    assert.equal(closed, false, 'one settled operation is not a closed stream');
    nextGate.resolve({ done: true });
    closeGate.resolve({ done: true });
    await pull;
    assert.deepEqual(await close, { done: true, value: null });
    assert.equal(returns, 1);
    assert.deepEqual(wire.errors, []);
  });
}

test('an idle stream is closed without fetching an item', async () => {
  let pulls = 0, closes = 0;
  const wire = bridge({ open: () => ({
    next() { pulls++; return { done: false, value: 'unused' }; },
    return() { closes++; return { done: true }; },
  }) });
  const { stream } = await wire.open();
  assert.deepEqual(await wire.close(stream), { done: true, value: null });
  assert.equal(pulls, 0);
  assert.equal(closes, 1);
});

for (const firstFailure of ['throw', 'incomplete']) {
  test(`a ${firstFailure === 'throw' ? 'failed' : 'done:false'} return retains the stream for a cleanup job retry`, async () => {
    let attempts = 0, cleanupInvocation;
    const wire = bridge({ open: () => ({
      next: () => ({ done: false, value: 1 }),
      async return() {
        attempts++;
        if (attempts === 1) {
          if (firstFailure === 'throw') throw new Error('retry this close');
          return { done: false, value: 'cleanup has not finished' };
        }
        await Promise.resolve();
        cleanupInvocation = wire.invocation.getStore();
        return { done: true };
      },
    }) });
    const { stream } = await wire.open();
    await assert.rejects(wire.close(stream));
    assert.equal(attempts, 1);
    wire.owner.jobs.delete(wire.original);
    wire.admit('31', 'cleanup');
    assert.deepEqual(await wire.close(stream, { job: '31', restoring: true }), { done: true, value: null });
    assert.equal(attempts, 2, 'cleanup must retry the retained iterator');
    assert.equal(cleanupInvocation.ticket, wire.owner.cleanupToken.ticket);
    assert.equal(cleanupInvocation.kind, 'cleanup');
    assert.deepEqual(cleanupInvocation.rustAuthority, { session: wire.owner.id, job: '31', request: wire.replies.at(-1).request });
    assert.deepEqual(wire.errors, []);
  });
}

test('concurrent return requests share one close attempt', async () => {
  const gate = Promise.withResolvers(), entered = Promise.withResolvers();
  let closes = 0;
  const wire = bridge({ open: () => ({
    next: () => ({ done: false, value: 1 }),
    return() { closes++; entered.resolve(); return gate.promise; },
  }) });
  const { stream } = await wire.open();
  const first = wire.close(stream), second = wire.close(stream);
  await entered.promise;
  await turn();
  assert.equal(closes, 1);
  gate.resolve({ done: true });
  assert.deepEqual(await first, { done: true, value: null });
  assert.deepEqual(await second, { done: true, value: null });
});

test('concurrent next rejects StreamBusy without pulling the iterator again', async () => {
  const gate = Promise.withResolvers(), entered = Promise.withResolvers();
  let pulls = 0;
  const wire = bridge({ open: () => closable(() => { pulls++; entered.resolve(); return gate.promise; }) });
  const { stream } = await wire.open();
  const first = wire.next(stream);
  await entered.promise;
  await assert.rejects(wire.next(stream), /StreamBusy/);
  assert.equal(pulls, 1);
  gate.resolve({ done: false, value: 8 });
  assert.deepEqual(await first, { done: false, value: 8 });
  await wire.close(stream);
});

test('unknown jobs, a different session, and another job cannot consume an owned stream', async () => {
  let opens = 0, pulls = 0, closes = 0;
  const wire = bridge({ open() {
    opens++;
    return { next() { pulls++; return { done: false, value: 1 }; }, return() { closes++; return { done: true }; } };
  } });
  await assert.rejects(wire.open({ job: 'missing' }));
  await assert.rejects(wire.open({ service: 'undeclared' }));
  assert.equal(opens, 0);
  const { stream } = await wire.open();
  const other = wire.session('6', '42');
  wire.admit('21', 'call', other);
  wire.admit('22', 'call');
  wire.admit('31', 'cleanup');
  await assert.rejects(wire.next(stream, { session: other.id }));
  await assert.rejects(wire.close(stream, { session: other.id }));
  await assert.rejects(wire.next(stream, { job: '22' }));
  await assert.rejects(wire.next(stream, { job: '31' }));
  await assert.rejects(wire.next(stream, { job: 'missing' }));
  assert.equal(pulls, 0);
  assert.equal(closes, 0);
  assert.deepEqual(await wire.next(stream), { done: false, value: 1 });
  await wire.close(stream);
  assert.equal(closes, 1);
});

test('open rejects iterators without explicit next and return methods', async () => {
  const values = [
    null,
    {},
    { next() { return { done: true }; } },
    { next: 3, return() { return { done: true }; } },
    { next() { return { done: true }; }, return: 3 },
    { [Symbol.asyncIterator]() { return null; } },
  ];
  for (const value of values) {
    const wire = bridge({ open: () => value });
    await assert.rejects(wire.open());
    assert.equal(wire.replies.length, 1);
    assert.equal(wire.replies[0].success, false);
    assert.equal(wire.pending.size, 0);
  }
});

test('bad yield data and iterator-result getter failures reply as errors without losing close ownership', async () => {
  let dataGetterCalled = false;
  const scenarios = [
    () => ({ done: false, value: new Date() }),
    () => ({ done: false, value: { get field() { dataGetterCalled = true; return 1; } } }),
    () => ({ get done() { throw new Error('done getter failed'); }, value: 1 }),
    () => ({ done: false, get value() { throw new Error('value getter failed'); } }),
    () => { throw Object.create(null); },
  ];
  for (const next of scenarios) {
    let closes = 0;
    const wire = bridge({ open: () => ({ next, return() { closes++; return { done: true }; } }) });
    const { stream } = await wire.open();
    await assert.rejects(wire.next(stream));
    assert.equal(wire.replies.length, 2);
    assert.equal(wire.replies[1].success, false);
    assert.equal(typeof wire.replies[1].error, 'string');
    assert.equal(wire.pending.size, 0, 'an exceptional result must not strand its request');
    await wire.close(stream);
    assert.equal(closes, 1);
    assert.deepEqual(wire.errors, []);
  }
  assert.equal(dataGetterCalled, false, 'JSON data accessors must not execute');
});

test('throwing stream method getters produce one error reply', async () => {
  const services = [
    { get open() { throw new Error('open getter failed'); } },
    { open: () => ({ get [Symbol.asyncIterator]() { throw new Error('iterator getter failed'); } }) },
    { open: () => ({ get next() { throw new Error('next getter failed'); }, return() { return { done: true }; } }) },
    { open: () => ({ next() { return { done: true }; }, get return() { throw new Error('return getter failed'); } }) },
  ];
  for (const service of services) {
    const wire = bridge(service);
    await assert.rejects(wire.open());
    assert.equal(wire.replies.length, 1);
    assert.equal(wire.replies[0].success, false);
    assert.equal(wire.pending.size, 0);
    assert.deepEqual(wire.errors, []);
  }
});

test('undefined yielded and final values become explicit null JSON values', async () => {
  const wire = bridge({ open: () => closable(() => ({ done: false, value: undefined })) });
  const { stream } = await wire.open();
  assert.deepEqual(await wire.next(stream), { done: false, value: null });
  assert.deepEqual(await wire.close(stream), { done: true, value: null });
});

test('natural JS EOF still requires an explicit return confirmation', async () => {
  let closes = 0;
  const wire = bridge({ open: () => ({
    next: () => ({ done: true }),
    return() { closes++; return { done: true }; },
  }) });
  const { stream } = await wire.open();
  assert.deepEqual(await wire.next(stream), { done: true, value: null });
  assert.equal(closes, 0, 'the native owner must explicitly request resource closure');
  assert.deepEqual(await wire.close(stream), { done: true, value: null });
  assert.equal(closes, 1);
});

test('malformed acquisitions retain failed return work for the owning session cleanup', async () => {
  let attempts = 0, cleanupInvocation;
  const wire = bridge({ open: () => ({
    get next() { throw new Error('cannot obtain next'); },
    async return() {
      attempts++;
      if (attempts === 1) throw new Error('close needs retry');
      await Promise.resolve();
      cleanupInvocation = wire.invocation.getStore();
      return { done: true };
    },
  }) });
  await assert.rejects(wire.open());
  assert.equal(attempts, 1, 'a malformed acquired iterator must be returned immediately');
  wire.owner.jobs.delete(wire.original);
  wire.admit('31', 'cleanup');
  // The failed acquisition exposed no id, so native requests cleanup of the
  // session's orphan journal under a live cleanup request capability.
  await wire.send('close_orphans', { job: '31', restoring: true });
  assert.equal(attempts, 2);
  assert.equal(cleanupInvocation.ticket, wire.owner.cleanupToken.ticket);
  assert.equal(cleanupInvocation.kind, 'cleanup');
  assert.deepEqual(cleanupInvocation.rustAuthority, { session: wire.owner.id, job: '31', request: wire.replies.at(-1).request });
  await wire.send('close_orphans', { job: '31', restoring: true });
  assert.equal(attempts, 2, 'successfully closed orphans must not be closed again');
});
