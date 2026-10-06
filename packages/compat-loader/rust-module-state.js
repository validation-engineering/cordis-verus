import { LoaderError } from './config.js';

const fail = message => new LoaderError('NATIVE_MODULE_CHECKPOINT', message);
export const schemaOf = (module, recipe) => module.descriptor.factories.find(factory => factory.name === recipe.factory)?.checkpointSchema;
export function validateStateRecipe(module, recipe) {
  if (recipe.state !== undefined && recipe.state !== 'migrate') throw fail('state must be "migrate" when specified');
  if (recipe.state === 'migrate' && !schemaOf(module, recipe)) throw fail(`Factory ${recipe.factory} does not declare a checkpoint schema`);
}
/** Check metadata before withdrawing any live publication. Payload validation
 * remains the candidate's restore hook, which runs before its setup. */
export function validateStateTransfer(previous, next) {
  for (const recipe of next.recipes) {
    validateStateRecipe(next.module, recipe);
    const old = previous?.recipes.find(item => item.id === recipe.id && item.factory === recipe.factory);
    if (recipe.state !== 'migrate' || old?.state !== 'migrate') continue;
    const from = schemaOf(previous.module, old), to = schemaOf(next.module, recipe);
    if (!from || to.schema !== from.schema || !(to.version === from.version || to.accepts.includes(from.version))) {
      throw fail(`Factory ${recipe.factory} cannot restore checkpoint schema ${from?.schema} version ${from?.version}`);
    }
  }
}
export const checkpointsOf = state => new Map([...state?.entries ?? []].filter(([,record]) => record.checkpoint).map(([id, record]) => [id, record.checkpoint]));
export function sourceOf(state) {
  return state && { module: state.module, recipes: state.recipes, checkpoints: checkpointsOf(state) };
}
export class StateJournal {
  constructor(host) { this.host = host; this.tokens = new Set(); this.pins = new Map(); }
  plugin(module, recipe, record, source) {
    if (recipe.state !== 'migrate') return module.factories.get(recipe.factory);
    const metadata = module.descriptor.factories.find(factory => factory.name === recipe.factory);
    const matching = source?.recipes.find(item => item.id === recipe.id && item.factory === recipe.factory && item.state === 'migrate');
    return this.host.makePlugin({ ...metadata }, {
      restore: () => record.checkpoint ?? (matching ? source.checkpoints?.get(recipe.id) : undefined),
      armed: token => {
        const previous = record.checkpoint;
        this.tokens.add(token); record.checkpoint = token;
        // Ordinary dependency restarts replace one episode, not its entire
        // managed group. Recycle its prior receipt unless a transaction pins it.
        if (previous && !this.pins.has(previous)) this.drop(previous);
      },
    });
  }
  drop(token) {
    if (!this.tokens.has(token)) return;
    this.host.command({ op: 'checkpoint_drop', token });
    this.tokens.delete(token);
  }
  pin(map) {
    const tokens = new Set(map?.values());
    for (const token of tokens) this.pins.set(token, (this.pins.get(token) ?? 0) + 1);
    let released = false;
    return () => {
      if (released) return;
      released = true;
      for (const token of tokens) {
        const count = this.pins.get(token) - 1;
        if (count) this.pins.set(token, count); else this.pins.delete(token);
      }
    };
  }
  retain(...maps) {
    const retained = new Set(maps.flatMap(map => [...map?.values() ?? []]));
    for (const token of this.tokens) if (!retained.has(token) && !this.pins.has(token)) this.drop(token);
  }
  clear() { this.pins.clear(); this.retain(); }
}
