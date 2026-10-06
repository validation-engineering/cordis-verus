import test from 'node:test';
import assert from 'node:assert/strict';
import { AsyncLocalStorage } from 'node:async_hooks';
import { RustHost } from '../../packages/compat-cordis/rust-plugin.js';

const turn = () => new Promise(resolve => setImmediate(resolve));

// Exercise the JS executor's protocol independently of the real Rust executor.
// The wire has no lifecycle scheduler: tests supply already admitted jobs and
// inspect whether their arbitrary JS work produces one actual completion.
function bridge(service = {}) {
  const invocation = new AsyncLocalStorage();
  const commands = [];
  const batches = [];
  const replies = [];
  const errors = [];
  const diagnostics = [];
  let pollFailure;
  let rejectReply = false;
  let cancelResult;
  const factory = { name: 'external-fixture', inject: ['js'], services: [] };
  const domain = {
    errors, diagnostics, fibers: new Map(),
    wake() {},
    driver: {
      rustInfo: () => JSON.stringify({ abi: 1, factories: [factory] }),
      rustWake() {},
      rustCommand(encoded) {
        const command = JSON.parse(encoded);
        commands.push(command);
        if (command.op === 'poll') {
          if (pollFailure) throw pollFailure;
          return JSON.stringify(batches.shift() ?? { calls: [], jobs: [] });
        }
        if (command.op === 'reply') {
          if (rejectReply) throw new Error('StaleRequest');
          replies.push(command);
        }
        if (command.op === 'cancel' && cancelResult) batches.push({ calls: [], jobs: [cancelResult] });
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
  const fiber = { id: '41', _generation: '7' };
  const token = { fiber, generation: '7', kind: 'setup', ticket: { domain: '9', id: '41', generation: '7', action: '11', kind: 'setup' } };
  const session = {
    id: '5', ctx: { js: service }, factory, token,
    jobs: new Set(), services: new Map(), cancelled: false, closed: false, cleaning: false,
  };
  host.sessions.set(session.id, session);
  const request = (method, fields = {}) => ({ request: '18', session: session.id, job: '21', kind: 'call', restoring: false, service: 'js', method, args: [], ...fields });
  const admit = (kind = 'call', job = '21') => session.jobs.add({ job, kind, promise: Promise.resolve() });
  const enqueue = call => { batches.push({ calls: [call], jobs: [] }); host.poll(); };
  return { host, session, invocation, commands, replies, errors, diagnostics, request, admit, enqueue,
    failPolling(error) { pollFailure = error; },
    rejectReplies() { rejectReply = true; },
    cancellationCompletes(result) { cancelResult = result; },
  };
}

for (const state of ['Unloading', 'unloading']) {
  test(`withdrawal cancels pending Rust setup for ${state} without retirement`, async () => {
    const wire = bridge();
    wire.cancellationCompletes({ job: '21', session: '5', success: false, error: 'Cancelled', value: null });
    const setup = wire.host.wait('21', wire.session, 'setup');
    const rejected = assert.rejects(setup, /Cancelled/);
    wire.host.sync({ id: '41', state: 'Loading', retired: false });
    assert.equal(wire.commands.some(command => command.op === 'cancel'), false);
    // Restart or dependency withdrawal need not retire the logical fiber.
    wire.host.sync({ id: '41', state, retired: false });
    wire.host.sync({ id: '41', state, retired: false });
    await rejected;
    await turn();
    assert.equal(wire.commands.filter(command => command.op === 'cancel').length, 1);
    assert.equal(wire.session.jobs.size, 0);
    assert.deepEqual(wire.errors, []);
  });
}

test('retirement cancels its session while an unrelated owner remains admitted', async () => {
  const wire = bridge();
  const other = { ...wire.session, id: '6', token: { ...wire.session.token, fiber: { id: '42', _generation: '7' } } };
  wire.host.sessions.set(other.id, other);
  wire.host.sync({ id: '41', state: 'Loading', retired: true });
  wire.host.sync({ id: '41', state: 'Unloading', retired: true });
  await turn();
  assert.deepEqual(wire.commands.filter(command => command.op === 'cancel').map(command => command.session), ['5']);
  assert.equal(other.cancelled, false);
});

test('reverse call waits for the JS Promise and invokes a method getter exactly once', async () => {
  const gate = Promise.withResolvers();
  let reads = 0;
  let receiver;
  const service = {
    marker: 'original receiver',
    get method() {
      reads++;
      if (reads !== 1) throw new Error('method getter was evaluated again');
      return async function (value) { receiver = this; await gate.promise; return { value, marker: this.marker }; };
    },
  };
  const wire = bridge(service);
  wire.admit();
  wire.enqueue(wire.request('method', { args: [42] }));
  await turn();
  assert.equal(wire.replies.length, 0, 'a Promise is not a completed JS call');
  gate.resolve();
  await turn();
  assert.equal(reads, 1);
  assert.equal(receiver, service);
  assert.deepEqual(wire.replies, [{ op: 'reply', request: '18', success: true, value: { value: 42, marker: 'original receiver' } }]);
  assert.deepEqual(wire.errors, []);
});

test('cleanup reverse calls retain the actual cleanup invocation through await', async () => {
  let observed;
  const wire = bridge({ async method() { await Promise.resolve(); observed = wire.invocation.getStore(); return null; } });
  wire.session.cleanupToken = { ...wire.session.token, kind: 'cleanup', ticket: { ...wire.session.token.ticket, action: '99', kind: 'cleanup' } };
  wire.admit('cleanup');
  wire.enqueue(wire.request('method', { restoring: true }));
  await turn();
  assert.equal(observed.ticket, wire.session.cleanupToken.ticket);
  assert.equal(observed.fiber, wire.session.cleanupToken.fiber);
  assert.equal(observed.kind, 'cleanup');
  assert.equal(observed.generation, wire.session.cleanupToken.generation);
  assert.deepEqual(observed.rustAuthority, { session: '5', job: '21', request: '18' });
  assert.equal(observed.ticket.action, '99');
  assert.equal(wire.replies.length, 1);
  assert.equal(wire.replies[0].success, true);
});

test('invalid JSON results and arbitrary thrown JS values always complete as errors', async () => {
  const poison = Object.create(null);
  const hostile = { [Symbol.toPrimitive]() { throw new Error('coercion failed'); } };
  const scenarios = [
    () => new Date(),
    () => ({ get value() { throw new Error('must not evaluate DTO accessor'); } }),
    () => { throw poison; },
    async () => { throw hostile; },
  ];
  for (const method of scenarios) {
    const wire = bridge({ method });
    wire.admit();
    wire.enqueue(wire.request('method'));
    await turn();
    assert.equal(wire.replies.length, 1, 'a JS failure must not strand the Rust request');
    assert.equal(wire.replies[0].success, false);
    assert.equal(typeof wire.replies[0].error, 'string');
    assert.ok(wire.replies[0].error.length);
    assert.deepEqual(wire.errors, []);
  }
});

test('unknown jobs and undeclared dependencies cannot execute JS side effects', async () => {
  let invoked = 0;
  const wire = bridge({ method() { invoked++; return null; } });
  wire.enqueue(wire.request('method'));
  await turn();
  assert.equal(invoked, 0);
  assert.equal(wire.replies.length, 1);
  assert.equal(wire.replies[0].success, false);
  wire.admit();
  wire.enqueue(wire.request('method', { request: '19', service: 'undeclared' }));
  await turn();
  assert.equal(invoked, 0);
  assert.equal(wire.replies.length, 2);
  assert.equal(wire.replies[1].success, false);
});

test('a native rejection of a consumed reply is surfaced without replaying JS', async () => {
  let invoked = 0;
  const wire = bridge({ method() { invoked++; return null; } });
  wire.admit();
  wire.rejectReplies();
  wire.enqueue(wire.request('method'));
  await turn();
  assert.equal(invoked, 1);
  assert.equal(wire.commands.filter(command => command.op === 'reply').length, 1);
  assert.equal(wire.errors.length, 1);
  assert.match(wire.errors[0].message, /StaleRequest/);
});


test('a native domain fault rejects owned waiters and prevents further native work', async () => {
  const wire = bridge();
  const caller = {};
  const fault = new Error('DomainFaulted: Rust plugin panicked');
  wire.failPolling(fault);
  const setup = wire.host.wait('21', wire.session, 'setup');
  const call = wire.host.wait('22', wire.session, 'call', caller);
  await Promise.all([
    assert.rejects(setup, error => error === fault),
    assert.rejects(call, error => error === fault),
  ]);
  await turn();
  assert.equal(wire.session.jobs.size, 0);
  assert.equal(caller._rustCalls.size, 0);
  assert.equal(wire.host.jobs.size, 0);
  assert.deepEqual(wire.errors, [fault]);
  assert.equal(wire.diagnostics.length, 1);
  assert.equal(wire.diagnostics[0].kind, 'rust-domain-fault');
  assert.equal(wire.diagnostics[0].cleanup, 'unconfirmed');
  const admittedCommands = wire.commands.length;
  assert.throws(() => wire.host.command({ op: 'poll' }), error => error === fault);
  await assert.rejects(wire.host.wait('23', wire.session, 'call'), error => error === fault);
  await turn();
  assert.equal(wire.commands.length, admittedCommands, 'faulted hosts must not reenter the native executor');
});
