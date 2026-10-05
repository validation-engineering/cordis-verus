// Explicit per-environment routing; never silently fall back to another scheduler.
import * as module from 'node:module';
export function registerProfile(profile, esmURL, commonJSURL) {
  const [major,minor] = process.versions.node.split('.').map(Number);
  if (major < 22 || (major === 22 && minor < 22) || typeof module.registerHooks !== 'function') {
    throw new Error('Cordis native compatibility bootstrap requires Node 22.22 or newer with synchronous module hooks.');
  }
  const key = Symbol.for('cordis-verus.compat-cordis.bootstrap.v1');
  const existing = globalThis[key];
  if (existing && (existing.profile !== profile || existing.facade !== esmURL)) {
    throw new Error('A different Cordis compatibility bootstrap is already installed in this environment.');
  }
  const name = profile === 'harness' ? '@deepseek-ai/cordis' : 'cordis';
  if (!existing) {
    module.registerHooks({
      resolve(specifier, context, nextResolve) {
        if (specifier === name) {
          const commonJS = context.conditions.includes('require');
          return {url:commonJS ? commonJSURL : esmURL,format:commonJS?'commonjs':'module',shortCircuit:true};
        }
        if (specifier === 'cordis' || specifier.startsWith('cordis/') || specifier === '@cordisjs/core' || specifier.startsWith('@cordisjs/core/') || specifier === '@deepseek-ai/cordis' || specifier.startsWith('@deepseek-ai/cordis/')) {
          const error = new Error(`Unsupported Cordis compatibility import ${JSON.stringify(specifier)} from ${context.parentURL ?? '<entry>'}. Profile ${profile} supports only bare ${JSON.stringify(name)}; deep imports and mixed profiles are rejected.`);
          error.code = 'ERR_CORDIS_UNSUPPORTED_IMPORT';
          throw error;
        }
        return nextResolve(specifier,context);
      },
    });
    Object.defineProperty(globalThis,key,{value:Object.freeze({profile,abi:1,facade:esmURL}),configurable:false,writable:false});
  }
  return globalThis[key];
}
