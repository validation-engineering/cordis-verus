import { readFile } from 'node:fs/promises';
import { setTimeout as delay } from 'node:timers/promises';
import { inspect } from 'node:util';

// A persistent state handshake does not depend on delivery of a filesystem or
// stdout event. Polling is bounded by the same timeout as the domain fixture.
export async function waitForMarker(path, expected, { timeout = 5000, signal } = {}) {
  const deadline = performance.now() + timeout;
  for (;;) {
    signal?.throwIfAborted();
    try { if (await readFile(path, 'utf8') === expected) return; }
    catch (error) { if (error.code !== 'ENOENT') throw error; }
    if (performance.now() >= deadline) throw new Error(`Timed out waiting for ${expected} at ${path}`);
    await delay(10, undefined, { signal });
  }
}

// Attach the rejection handler at operation creation, before waiting for its
// peer. The returned promise always settles with the original result or error.
export function observeOperation(label, promise) {
  return Promise.resolve(promise).then(
    value => ({ label, status: 'fulfilled', value }),
    reason => ({ label, status: 'rejected', reason }),
  );
}

export async function completedValues(observed) {
  const outcomes = await Promise.all(observed);
  const rejected = outcomes.filter(outcome => outcome.status === 'rejected');
  if (rejected.length) {
    throw new AggregateError(rejected.map(outcome => outcome.reason),
      rejected.map(outcome => `${outcome.label}: ${inspect(outcome.reason, { depth: 8 })}`).join('\n'),
      { cause: rejected[0].reason });
  }
  return outcomes.map(outcome => outcome.value);
}

// An early call error is more informative than a later readiness timeout. Abort
// the losing poll so a failed admission leaves no background test timer.
export async function waitForCallMarker(path, observed) {
  const controller = new AbortController();
  try {
    await Promise.race([
      waitForMarker(path, 'ready', { signal: controller.signal }),
      observed.then(outcome => {
        if (outcome.status === 'rejected') throw outcome.reason;
        throw new Error(`${outcome.label} completed before the fixture was released`);
      }),
    ]);
  } finally { controller.abort(); }
}
