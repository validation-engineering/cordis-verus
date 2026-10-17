// The only JS identity adapter. Payload contents are attached once to native
// boxes in a private WeakMap. Native storage returns the same box through a weak
// Node-API reference; JS retention roots keep it live until checked release.
// No payload getter, proxy or callback executes during native table operations.
const contents = new WeakMap();
const calls = new WeakMap();
function payload(box) {
  if (!box) return undefined;
  if (!contents.has(box)) throw new Error('HostBridge: unknown native object box');
  return contents.get(box);
}
export class HostBridge {
  #driver;
  #roots = new Map();
  #fibers = new Map();
  constructor(driver) { this.#driver = driver; driver.enableHostBridge(); }
  create(value) {
    const box = this.#driver.createObject();
    contents.set(box, value);
    this.#roots.set(box.id, box);
    return box;
  }
  get(id) { return payload(this.#driver.getObject(id)); }
  delete(id) {
    this.#driver.dropObject(id);
    return this.#roots.delete(id);
  }
  publish(command,value) {
    const box = this.create(value);
    try { return JSON.parse(this.#driver.objectCommand(JSON.stringify({...command,value:box.id}),box)); }
    catch (error) { this.delete(box.id); throw error; }
  }
  resolve(command) {
    const result = this.#driver.resolveObject(JSON.stringify(command));
    return result && {owner:result.owner,publication:result.publication,value:payload(result.object)};
  }
  bind(id,fiber) {
    const box = this.create(fiber);
    try { this.#driver.bindFiber(id,box); }
    catch (error) { this.delete(box.id); throw error; }
    this.#fibers.set(id,box);
  }
  fiber(id) { return payload(this.#driver.getFiber(id)); }
  hasFiber(id) { return this.#driver.getFiber(id) != null; }
  unbind(id) {
    const key = this.#driver.unbindFiber(id);
    if (key != null) this.delete(key);
    this.#fibers.delete(id);
  }
  *fibers() { for (const id of this.#fibers.keys()) yield this.fiber(id); }
  begin(ticket,fiber,recipe) {
    const owner = this.#driver.getFiber(ticket.id);
    if (payload(owner) !== fiber) throw new Error('HostBridge: callback Fiber mismatch');
    const box = this.create(Object.freeze(recipe));
    try {
      const call = this.#driver.beginAction(JSON.stringify(ticket),owner,box);
      calls.set(call,box.id);
      return call;
    } catch (error) { this.delete(box.id); throw error; }
  }
  recipe(call) { return payload(this.#driver.actionRecipe(call)); }
  complete(call,success,error) {
    try { this.#driver.completeAction(call,success,error); }
    finally {
      if (calls.has(call) && !this.#driver.actionLive(call)) {
        this.delete(calls.get(call));
        calls.delete(call);
      }
    }
  }
}
