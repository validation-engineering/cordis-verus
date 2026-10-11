export * from '@validation-engineering/cordis';
import { Context as CoreContext } from '@validation-engineering/cordis';
export class Context extends CoreContext {
  constructor(options = {}) { super({...options, profile:'harness'}); }
}
