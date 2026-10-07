// Host observations only. No callbacks, service values or scheduling authority
// are stored in the exported projection. Native admission remains in the Driver.
import { performance } from 'node:perf_hooks';
import { types } from 'node:util';
import { DisposableList } from './utils.js';

// Even recording a failure must not call a thrown object's getters/toString.
export function diagnosticError(error) {
  if (typeof error === 'string') return error;
  if (!types.isNativeError(error)) return 'Non-Error rejection';
  const message = Object.getOwnPropertyDescriptor(error, 'message')?.value;
  const name = Object.getOwnPropertyDescriptor(error, 'name')?.value;
  return `${typeof name === 'string' ? name : 'Error'}: ${typeof message === 'string' ? message : '(message unavailable)'}`;
}

const journals = new WeakMap();
export function hostDiagnostics(fiber) {
  let journal = journals.get(fiber);
  if (!journal) { journal = new HostDiagnostics(fiber); journals.set(fiber, journal); }
  return journal;
}

class HostDiagnostics {
  constructor(fiber) { this.fiber = fiber; this.counter = 0n; this.records = new Map(); }
  register(label, parent) {
    const record = {id: String(++this.counter), owner: this.fiber.id,
      generation: this.fiber._generation ?? null, registeredGeneration: this.fiber._generation ?? null, label: typeof label === 'string' ? label : 'anonymous',
      parent: parent?.id ?? null, parentRecord: parent, children: new Set(), state: 'registered', attempts: 0};
    parent?.children.add(record);
    this.records.set(record.id, record);
    return record;
  }
  begin(record, state = 'running') {
    record.state = state; record.attempts++; record.startedAt = performance.now();
    delete record.error;
  }
  fail(record, error) { record.state = 'failed'; record.error = error; }
  forget(record) {
    if (!record || !this.records.delete(record.id)) return;
    record.parentRecord?.children.delete(record);
    for (const child of [...record.children]) this.forget(child);
  }
  startAction(ticket) {
    // Prepared generation-zero effects are adopted by the real setup ticket.
    // Preserve where they were registered as a separate observation.
    if (ticket.kind === 'setup') for (const record of this.records.values()) {
      if (record.generation === '0') record.generation = ticket.generation;
    }
    this.action = {ticket: {...ticket}, stage: ticket.kind, startedAt: performance.now()};
  }
  stage(stage) { if (this.action) this.action.stage = stage; }
  endAction(ticket) {
    if (this.action?.ticket.action === ticket.action) this.action = undefined;
  }
  snapshot(includeTiming = false) {
    const now = includeTiming ? performance.now() : undefined;
    const elapsed = startedAt => Math.max(0, now - startedAt);
    const inverses = [...this.records.values()].map(record => ({
      id: record.id, owner: record.owner, generation: record.generation, registeredGeneration: record.registeredGeneration, parent: record.parent,
      label: record.label, state: record.state, attempts: record.attempts,
      ...(record.error === undefined ? {} : {error: record.error}),
      ...(includeTiming && ['waiting', 'running'].includes(record.state) ? {elapsedMs: elapsed(record.startedAt)} : {}),
    }));
    return {inverses, ...(this.action ? {action: {ticket: {...this.action.ticket}, stage: this.action.stage,
      ...(includeTiming ? {elapsedMs: elapsed(this.action.startedAt)} : {})}} : {})};
  }
}

// Preserve DisposableList identity/order semantics. Metadata belongs to an
// actual registration, including two registrations of the same function.
export class ObservedDisposables extends DisposableList {
  constructor(fiber) { super(); this.journal = hostDiagnostics(fiber); this.observations = new Map(); }
  push(value, label = 'plugin cleanup', manual = false) {
    const remove = super.push(value), sn = this.sn;
    const record = this.journal.register(label);
    this.observations.set(sn, {record, manual});
    return () => { const removed = remove(); if (removed) this.forget(sn); return removed; };
  }
  forget(sn) { this.journal.forget(this.observations.get(sn)?.record); this.observations.delete(sn); }
  delete(value) {
    const sn = this.weak.get(value), removed = super.delete(value);
    if (removed) this.forget(sn);
    return removed;
  }
  clear() {
    const values = super.clear();
    for (const sn of this.observations.keys()) this.forget(sn);
    return values;
  }
  detach(value, parent) {
    const sn = this.weak.get(value), observation = this.observations.get(sn);
    if (!super.delete(value)) return;
    this.observations.delete(sn);
    observation.record.parentRecord?.children.delete(observation.record);
    observation.record.parent = parent.id;
    observation.record.parentRecord = parent;
    parent.children.add(observation.record);
    return observation;
  }
  record(value) { return this.observations.get(this.weak.get(value))?.record; }
  removeRegistration(sn) {
    const removed = this.map.delete(sn);
    if (removed) this.forget(sn);
    return removed;
  }
  entriesForCleanup() {
    return [...this.map.entries()].map(([sn, value]) => ({sn, value, ...this.observations.get(sn)}));
  }
}
