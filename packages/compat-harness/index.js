export * from '@cordis-verus/compat-cordis';
import { Context as CoreContext } from '@cordis-verus/compat-cordis';
export class Context extends CoreContext {
  constructor(options = {}) { super({...options, profile:'harness'}); }
}
