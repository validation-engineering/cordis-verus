import test from 'node:test';
import assert from 'node:assert/strict';
import { AsyncLocalStorage } from 'node:async_hooks';
import { RustHost } from '../../packages/compat-cordis/rust-plugin.js';
import { adaptObject, adaptCallback } from '../../packages/compat-cordis/rust-objects.js';

const turn = () => new Promise(resolve => setImmediate(resolve));

// Only admitted reverse requests and actual replies are supplied here. Native
// ownership, action completion and the Driver are tested by the real addon suite.
function bridge(service) {
  const invocation = new AsyncLocalStorage();
  const batches = [], replies = [], errors = [];
  const pending = new Map();
  let requestId = 0;
  const factory = { name: 'object-fixture', inject: ['js'], services: [] };
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
          assert.ok(waiter, 'each reverse request receives exactly one reply');
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
    const fiber = { id: fiberId, _generation: '7', _domain: domain };
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
    open: fields => send('object_open', fields),
    call: (object, method, args = [], fields) => send('object_call', { object, method, args, ...fields }),
    close: (object, fields) => send('object_close', { object, ...fields }),
  };
}

const borrowed = (target, methods = ['read']) => adaptObject(target, { typeName: 'fixture', methods, ownership: 'borrowed' });
const owned = (target, dispose, methods = ['read']) => adaptObject(target, { typeName: 'fixture', methods, ownership: 'owned', dispose });

test('object acquisition snapshots its allowlist, method getters and receiver once', async () => {
  let reads = 0, opens = 0;
  const methods = ['read'];
  const target = {
    marker: 'target',
    get read() {
      reads++;
      return function (suffix) { assert.equal(this, target); return this.marker + suffix; };
    },
    hidden() { throw new Error('not exported'); },
  };
  const adapter = adaptObject(target, { typeName: 'example.Record', methods, ownership: 'borrowed' });
  methods.push('hidden');
  const service = {
    get open() {
      opens++;
      return function (input) { assert.equal(this, service); assert.equal(input, 4); return adapter; };
    },
  };
  const wire = bridge(service);
  const reply = await wire.open({ args: [4] });
  assert.equal(typeof reply.object, 'string');
  assert.deepEqual(reply.descriptor, { typeName: 'example.Record', methods: ['read'], ownership: 'borrowed' });
  assert.equal(reads, 1);
  Object.defineProperty(target, 'read', { value() { throw new Error('replacement must not run'); } });
  assert.equal(await wire.call(reply.object, 'read', ['!']), 'target!');
  assert.equal(await wire.call(reply.object, 'read', ['?']), 'target?');
  await assert.rejects(wire.call(reply.object, 'hidden'));
  await assert.rejects(wire.call(reply.object, 'toString'));
  assert.deepEqual(await wire.close(reply.object), { closed: true });
  assert.equal(opens, 1);
  assert.equal(reads, 1);
  assert.deepEqual(wire.errors, []);
});

test('callback adapters expose only call with JSON arguments and default metadata', async () => {
  const calls = [];
  const callback = adaptCallback((...args) => { calls.push(args); return { total: args[0] + args[1] }; });
  const wire = bridge({ open: () => callback });
  const { object, descriptor } = await wire.open();
  assert.deepEqual(descriptor, { typeName: 'callback', methods: ['call'], ownership: 'borrowed' });
  assert.deepEqual(await wire.call(object, 'call', [2, 3]), { total: 5 });
  await assert.rejects(wire.call(object, 'apply'));
  await assert.rejects(wire.call(object, 'bind'));
  assert.deepEqual(calls, [[2, 3]]);
  await wire.close(object);
});

test('plain lookalikes and proxies cannot manufacture an adapter brand', async () => {
  let invoked = 0;
  const values = [
    null, {},
    { typeName: 'fixture', methods: ['read'], ownership: 'borrowed', read() { invoked++; } },
    { descriptor: { typeName: 'fixture', methods: ['read'], ownership: 'borrowed' }, target: { read() { invoked++; } } },
    new Proxy(borrowed({ read: () => 1 }), {}),
  ];
  for (const value of values) {
    const wire = bridge({ open: () => value });
    await assert.rejects(wire.open());
    assert.equal(wire.replies.length, 1);
    assert.equal(wire.pending.size, 0);
  }
  assert.equal(invoked, 0);
});

test('helper rejects contradictory ownership and invalid method descriptors', () => {
  const target = { read() {} };
  for (const options of [
    { typeName: 'fixture', methods: ['read'], ownership: 'owned' },
    { typeName: 'fixture', methods: ['read'], ownership: 'borrowed', dispose() {} },
    { typeName: 'fixture', methods: ['read'], ownership: 'shared' },
    { typeName: '', methods: ['read'], ownership: 'borrowed' },
    { typeName: 'fixture', methods: ['read', 'read'], ownership: 'borrowed' },
    { typeName: 'fixture', methods: [''], ownership: 'borrowed' },
    { typeName: 'fixture', methods: 'read', ownership: 'borrowed' },
  ]) assert.throws(() => adaptObject(target, options));
  assert.throws(() => adaptCallback(42));
});

test('borrowed acquisitions are separate leases and never invoke an object destructor', async () => {
  let disposals = 0;
  const target = { read: () => 'still alive', dispose() { disposals++; } };
  const adapter = borrowed(target);
  const wire = bridge({ open: () => adapter });
  const first = await wire.open(), second = await wire.open();
  assert.notEqual(first.object, second.object);
  await wire.close(first.object);
  await assert.rejects(wire.call(first.object, 'read'));
  assert.equal(await wire.call(second.object, 'read'), 'still alive');
  await wire.close(second.object);
  assert.equal(disposals, 0);
});

test('owned targets cannot be acquired twice even through a different adapter', async () => {
  let disposals = 0;
  const target = { read: () => 1 };
  const firstAdapter = owned(target, value => { assert.equal(value, target); disposals++; });
  const secondAdapter = owned(target, () => { disposals++; });
  let current = firstAdapter;
  const wire = bridge({ open: () => current });
  const { object } = await wire.open();
  await assert.rejects(wire.open());
  current = secondAdapter;
  await assert.rejects(wire.open());
  assert.equal(disposals, 0, 'rejecting another acquisition must not dispose the current owner');
  await wire.close(object);
  assert.equal(disposals, 1);
  await assert.rejects(wire.open(), 'ownership transfer is consumed after successful disposal');
  current = borrowed(target);
  await assert.rejects(wire.open(), 'a disposed owned target cannot become borrowed again');
  assert.equal(disposals, 1);
});

test('active borrowed leases block ownership transfer until every lease has closed', async () => {
  let disposals = 0;
  const target = { read: () => 3 };
  let current = borrowed(target);
  const wire = bridge({ open: () => current });
  const first = await wire.open(), second = await wire.open();
  current = owned(target, () => { disposals++; });
  await assert.rejects(wire.open());
  await wire.close(first.object);
  await assert.rejects(wire.open());
  assert.equal(await wire.call(second.object, 'read'), 3);
  await wire.close(second.object);
  const transferred = await wire.open();
  current = borrowed(target);
  await assert.rejects(wire.open());
  await wire.close(transferred.object);
  assert.equal(disposals, 1);
});

for (const ownership of ['borrowed', 'owned']) {
  test(`${ownership} close joins all pending methods and closes new admission before disposal`, async () => {
    const gates = [Promise.withResolvers(), Promise.withResolvers()];
    const entered = [Promise.withResolvers(), Promise.withResolvers()];
    let calls = 0, disposals = 0;
    const target = { read(index) { calls++; entered[index].resolve(); return gates[index].promise; } };
    const adapter = ownership === 'owned' ? owned(target, () => { disposals++; }) : borrowed(target);
    const wire = bridge({ open: () => adapter });
    const { object } = await wire.open();
    const first = wire.call(object, 'read', [0]), second = wire.call(object, 'read', [1]);
    await Promise.all(entered.map(item => item.promise));
    let closed = false;
    const close = wire.close(object).then(value => { closed = true; return value; });
    await turn();
    assert.equal(closed, false);
    assert.equal(disposals, 0, 'a destructor cannot run while a method is still in flight');
    await assert.rejects(wire.call(object, 'read', [0]));
    assert.equal(calls, 2);
    gates[0].resolve('first');
    assert.equal(await first, 'first');
    await turn();
    assert.equal(closed, false, 'every pending method must land');
    assert.equal(disposals, 0);
    gates[1].resolve('second');
    assert.equal(await second, 'second');
    assert.deepEqual(await close, { closed: true });
    assert.equal(disposals, ownership === 'owned' ? 1 : 0);
  });
}

test('concurrent close requests share the same awaited disposal attempt', async () => {
  const entered = Promise.withResolvers(), gate = Promise.withResolvers();
  let disposals = 0;
  const target = { read: () => 1 };
  const wire = bridge({ open: () => owned(target, async value => {
    assert.equal(value, target); disposals++; entered.resolve(); await gate.promise;
  }) });
  const { object } = await wire.open();
  const first = wire.close(object), second = wire.close(object);
  await entered.promise;
  await turn();
  assert.equal(disposals, 1);
  let settled = false;
  first.then(() => { settled = true; });
  await turn();
  assert.equal(settled, false);
  gate.resolve();
  assert.deepEqual(await first, { closed: true });
  assert.deepEqual(await second, { closed: true });
});

test('failed owned disposal retains a closed-to-business lease for cleanup retry with exact authority', async () => {
  let attempts = 0, cleanupInvocation;
  const target = { read: () => 1 };
  const adapter = owned(target, async () => {
    attempts++;
    if (attempts === 1) throw new Error('dispose must retry');
    await Promise.resolve();
    cleanupInvocation = wire.invocation.getStore();
  });
  const wire = bridge({ open: () => adapter });
  const { object } = await wire.open();
  await assert.rejects(wire.close(object), /dispose must retry/);
  await assert.rejects(wire.call(object, 'read'));
  await assert.rejects(wire.open(), 'failed release still owns the target');
  wire.owner.jobs.delete(wire.original);
  wire.admit('31', 'cleanup');
  assert.deepEqual(await wire.close(object, { job: '31', restoring: true }), { closed: true });
  assert.equal(attempts, 2);
  assert.equal(cleanupInvocation.ticket, wire.owner.cleanupToken.ticket);
  assert.equal(cleanupInvocation.kind, 'cleanup');
  assert.deepEqual(cleanupInvocation.rustAuthority, { session: wire.owner.id, job: '31', request: wire.replies.at(-1).request });
});

test('unknown jobs, other sessions and another ordinary job cannot consume or release an object', async () => {
  let calls = 0, disposals = 0, opens = 0;
  const target = { read() { calls++; return 1; } };
  const wire = bridge({ open() { opens++; return owned(target, () => { disposals++; }); } });
  await assert.rejects(wire.open({ job: 'missing' }));
  await assert.rejects(wire.open({ service: 'undeclared' }));
  assert.equal(opens, 0);
  const { object } = await wire.open();
  const other = wire.session('6', '42');
  wire.admit('21', 'call', other);
  wire.admit('22', 'call');
  wire.admit('31', 'cleanup');
  for (const fields of [{ session: other.id }, { job: '22' }, { job: '31', restoring: true }, { job: 'missing' }]) {
    await assert.rejects(wire.call(object, 'read', [], fields));
  }
  for (const fields of [{ session: other.id }, { job: '22' }, { job: 'missing' }]) {
    await assert.rejects(wire.close(object, fields));
  }
  assert.equal(calls, 0);
  assert.equal(disposals, 0);
  assert.equal(await wire.call(object, 'read'), 1);
  await wire.close(object, { job: '31', restoring: true });
  assert.equal(disposals, 1);
});

test('method rejection and invalid JSON results do not implicitly dispose a live object', async () => {
  let accessorRan = false;
  const badResults = [
    () => new Date(),
    () => ({ get field() { accessorRan = true; return 1; } }),
    () => new Proxy({}, {}),
    () => { throw Object.create(null); },
    () => { const value = {}; value.self = value; return value; },
  ];
  for (const bad of badResults) {
    let disposals = 0;
    const target = { bad, read: () => 'usable' };
    const wire = bridge({ open: () => owned(target, () => { disposals++; }, ['bad', 'read']) });
    const { object } = await wire.open();
    await assert.rejects(wire.call(object, 'bad'));
    assert.equal(wire.pending.size, 0);
    assert.equal(wire.replies.length, 2);
    assert.equal(typeof wire.replies[1].error, 'string');
    assert.equal(disposals, 0);
    assert.equal(await wire.call(object, 'read'), 'usable');
    await wire.close(object);
    assert.equal(disposals, 1);
    assert.deepEqual(wire.errors, []);
  }
  assert.equal(accessorRan, false);
});

test('undefined method results normalize to null', async () => {
  const wire = bridge({ open: () => borrowed({ read() {} }) });
  const { object } = await wire.open();
  assert.equal(await wire.call(object, 'read'), null);
  await wire.close(object);
});

test('a throwing acquisition getter preserves failed owned disposal as a cleanup orphan', async () => {
  let getterReads = 0, attempts = 0, cleanupInvocation;
  const target = { get read() { getterReads++; throw new Error('method getter failed'); } };
  const adapter = owned(target, async () => {
    attempts++;
    if (attempts === 1) throw new Error('orphan dispose must retry');
    await Promise.resolve();
    cleanupInvocation = wire.invocation.getStore();
  });
  const wire = bridge({ open: () => adapter });
  await assert.rejects(wire.open());
  assert.equal(getterReads, 1);
  assert.equal(attempts, 1, 'malformed acquisition must attempt owned disposal');
  assert.equal(wire.pending.size, 0);
  wire.owner.jobs.delete(wire.original);
  wire.admit('31', 'cleanup');
  await wire.send('close_orphans', { job: '31', restoring: true });
  assert.equal(attempts, 2);
  assert.equal(cleanupInvocation.ticket, wire.owner.cleanupToken.ticket);
  assert.deepEqual(cleanupInvocation.rustAuthority, { session: wire.owner.id, job: '31', request: wire.replies.at(-1).request });
  await wire.send('close_orphans', { job: '31', restoring: true });
  assert.equal(attempts, 2, 'completed disposal must not be replayed');
});

test('a rejected acquisition releases its borrowed lease without executing a destructor', async () => {
  const target = { read: 42 };
  let current = borrowed(target), disposals = 0;
  const wire = bridge({ open: () => current });
  await assert.rejects(wire.open());
  target.read = () => 'fixed';
  current = owned(target, () => { disposals++; });
  const { object } = await wire.open();
  assert.equal(await wire.call(object, 'read'), 'fixed');
  await wire.close(object);
  assert.equal(disposals, 1, 'invalid borrowed metadata must not leave a phantom borrow');
});

test('object and callback adapters cannot be smuggled through ordinary JSON results', async () => {
  const values = [borrowed({ read: () => 1 }), adaptCallback(() => 2)];
  for (const value of values) {
    const wire = bridge({ open: () => borrowed({ read: () => ({ nested: value }) }) });
    const { object } = await wire.open();
    await assert.rejects(wire.call(object, 'read'));
    assert.equal(wire.pending.size, 0);
    await wire.close(object);
    assert.deepEqual(wire.errors, []);
  }
});

test('sparse method lists are rejected before an owned target can be transferred', async () => {
  let disposals = 0;
  // A hole used to become a callable target[undefined] while JSON encoded its
  // descriptor as null, causing native descriptor validation to lose the lease.
  const target = { read: () => 1, undefined: () => 2 };
  for (const methods of [Array(1), [, 'read'], ['read', ,]]) {
    assert.throws(() => adaptObject(target, { typeName: 'fixture', methods, ownership: 'owned', dispose() { disposals++; } }));
  }
  assert.equal(disposals, 0, 'invalid metadata is rejected before acquisition');
  const wire = bridge({ open: () => owned(target, () => { disposals++; }) });
  const { object, descriptor } = await wire.open();
  assert.deepEqual(descriptor.methods, ['read']);
  await wire.close(object);
  assert.equal(disposals, 1);
});

test('object options are snapshotted once so validated ownership and actual disposer agree', async () => {
  const reads = { typeName: 0, methods: 0, ownership: 0, dispose: 0 };
  let disposed;
  const target = { read: () => 'value' };
  const values = { typeName: 'one.snapshot', methods: ['read'], ownership: 'owned', dispose(value) { disposed = value; } };
  const options = {};
  for (const key of Object.keys(reads)) Object.defineProperty(options, key, {
    enumerable: true,
    get() { assert.equal(++reads[key], 1, `${key} must not be reread after validation`); return values[key]; },
  });
  const adapter = adaptObject(target, options);
  values.methods.push('not-exported');
  values.dispose = () => { throw new Error('later option mutation must not replace validated disposer'); };
  const wire = bridge({ open: () => adapter });
  const { object, descriptor } = await wire.open();
  assert.deepEqual(descriptor, { typeName: 'one.snapshot', methods: ['read'], ownership: 'owned' });
  assert.equal(await wire.call(object, 'read'), 'value');
  await wire.close(object);
  assert.equal(disposed, target);
  assert.deepEqual(reads, { typeName: 1, methods: 1, ownership: 1, dispose: 1 });
});

test('callback options are also snapshotted once before applying callback defaults', async () => {
  const reads = { typeName: 0, ownership: 0, dispose: 0 };
  let disposed;
  const callback = value => value + 1;
  const values = { typeName: 'one.callback', ownership: 'owned', dispose(value) { disposed = value; } };
  const options = {};
  for (const key of Object.keys(reads)) Object.defineProperty(options, key, {
    enumerable: true,
    get() { assert.equal(++reads[key], 1, `${key} must be read once`); return values[key]; },
  });
  const adapter = adaptCallback(callback, options);
  const wire = bridge({ open: () => adapter });
  const { object, descriptor } = await wire.open();
  assert.deepEqual(descriptor, { typeName: 'one.callback', methods: ['call'], ownership: 'owned' });
  assert.equal(await wire.call(object, 'call', [4]), 5);
  await wire.close(object);
  assert.equal(disposed, callback);
  assert.deepEqual(reads, { typeName: 1, ownership: 1, dispose: 1 });
});
