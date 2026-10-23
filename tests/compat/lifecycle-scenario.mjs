// Shared public-API scenario. Neither backend receives expected observations.
import {Context} from 'cordis';
import {createInterface} from 'node:readline';

const backend = process.argv[2];
if (!['native', 'upstream'].includes(backend)) throw new Error('Expected native or upstream backend');
const errorTree = error => ({name: error?.name ?? 'Error', message: String(error?.message ?? error),
  ...(error?.cause ? {cause: errorTree(error.cause)} : {}),
  ...(error?.errors ? {errors: Array.from(error.errors, errorTree)} : {})});

async function execute(scenario) {
  if (scenario.profile !== 'plugin-lifecycle/v1') return {id:scenario.id,status:'unsupported',reason:'No public plugin API for this profile'};
  if (scenario.schema !== 'cordis-verus.lifecycle-scenario/v1' || !Array.isArray(scenario.commands)
      || scenario.commands.length > 128 || !Array.isArray(scenario.parameters.values)
      || !scenario.parameters.values.every(Number.isSafeInteger)) return {id:scenario.id,status:'invalid'};
  const ctx = new Context(), fibers = new Map(), identities = new Map(), episodes = [], events = [], steps = [];
  let resource = 0, birth = 0, fault = null;
  const register = (fiber, actor) => {
    if (!Number.isSafeInteger(fiber.uid)) throw new Error('Missing actual registration identity');
    if (!identities.has(fiber.uid)) identities.set(fiber.uid, {birth:++birth, actor, uid:fiber.uid});
    const identity=identities.get(fiber.uid);
    if(identity.actor!==actor) throw new Error('Registration identity was reused by another actor');
    return identity;
  };
  const emit = (kind, episode, detail = {}) => events.push({sequence:events.length,kind,birth:episode.birth,
    actor:episode.actor,episode:episode.episode,...detail});
  const begin = (c, actor, revision, bindings = []) => {
    const fiber = c.fiber, identity = register(fiber, actor);
    const episode = {...identity,episode:episodes.filter(e=>e.birth===identity.birth).length+1,
      revision,bindings,parent:actor==='child' ? (()=>{
        const parent=episodes.findLast(e=>e.actor==='consumer');
        return {birth:parent.birth,episode:parent.episode};
      })() : null,
      resource:++resource,live:true,attempts:0};
    episodes.push(episode); emit('setup',episode,{revision,bindings,resource:episode.resource,parent:episode.parent});
    c.effect(()=>async()=>{
      episode.attempts += 1;
      const reads = actor === 'provider' ? [] : [c.value.resource,...(actor === 'child' ? [c.marker.resource] : [])];
      emit('cleanup-attempt',episode,{attempt:episode.attempts,reads});
      if (fault === actor) {
        emit('cleanup-failed',episode,{attempt:episode.attempts});
        throw new Error(`campaign-cleanup:${actor}:${episode.revision}`);
      }
      episode.live = false;
      emit('cleanup-succeeded',episode,{attempt:episode.attempts});
    });
    return episode;
  };
  function Provider(c, config) {
    const episode = begin(c,'provider',config.revision);
    c.provide('value',{resource:episode.resource,revision:config.revision,amount:scenario.parameters.values[config.revision]});
  }
  function Child(c) {
    begin(c,'child',c.value.revision,[c.value.resource,c.marker.resource]);
  }
  Child.inject = ['value','marker'];
  function Consumer(c) {
    const episode=begin(c,'consumer',c.value.revision,[c.value.resource]);
    c.provide('marker',{resource:episode.resource,revision:c.value.revision});
    const child=c.plugin(Child); fibers.set('child',child); register(child,'child');
  }
  Consumer.inject = ['value'];
  const snapshot = () => ({
    registrations:Array.from(identities.values()),
    fibers:Array.from(fibers,([actor,fiber])=>({birth:fiber.uid===null ?
      Array.from(identities.values()).findLast(x=>x.actor===actor).birth : identities.get(fiber.uid).birth,
      actor,uid:fiber.uid,state:fiber.state})),
    episodes:structuredClone(episodes),
    publications:Object.fromEntries(['value','marker'].map(name=>{
      const value=ctx.get(name); return [name,value ? {resource:value.resource,revision:value.revision} : null];
    })),
    native:typeof ctx.snapshot==='function' ? ctx.snapshot() : null,
  });
  const settle=async()=>{
    if(typeof ctx.settle==='function') await ctx.settle();
    else for(const actor of ['provider','consumer','child']) if(fibers.has(actor)) await fibers.get(actor).await();
  };
  const initial=snapshot();
  for (const [index,step] of scenario.commands.entries()) {
    const action=step.action, first=events.length;
    let outcome;
    try {
      switch(action.op) {
        case 'mount': {
          if(!['provider','consumer'].includes(action.actor) || fibers.has(action.actor)) throw new Error('invalid mount');
          const fiber=ctx.plugin(action.actor==='provider' ? Provider : Consumer,
            action.actor==='provider' ? {revision:0} : undefined);
          fibers.set(action.actor,fiber); register(fiber,action.actor); break;
        }
        case 'settle': case 'settle_fault': await settle(); break;
        case 'update': await fibers.get('provider').update({revision:action.revision}); await settle(); break;
        case 'fault': fault=action.actor; break;
        case 'repair': fault=null; break;
        case 'retry': {
          const fiber=fibers.get(action.actor);
          if(typeof fiber?.retryCleanup!=='function') {outcome={status:'unsupported',reason:'No public retryCleanup API'}; break;}
          await fiber.retryCleanup(); await settle(); break;
        }
        case 'shutdown': await fibers.get('consumer').dispose(); await fibers.get('provider').dispose(); await settle(); break;
        case 'observe': break;
        default: outcome={status:'unsupported',reason:'Unknown profile operation'};
      }
      outcome ??= {status:'ok'};
    } catch(error) { outcome={status:'rejected',error:errorTree(error)}; }
    steps.push({index,action,outcome,state:snapshot(),events:events.slice(first)});
    if(outcome.status==='unsupported') return {id:scenario.id,status:'unsupported',initial,steps,events};
  }
  // Do not add backend-specific teardown to the comparison. Each request runs
  // in an isolated process; a fault-prefix intentionally retains its resources.
  return {id:scenario.id,status:'executed',initial,steps,events};
}

for await(const line of createInterface({input:process.stdin,crlfDelay:Infinity})) {
  const input=JSON.parse(line);
  if(!Array.isArray(input.cases) || input.cases.length!==1) throw new Error('One isolated case per process required');
  const results=[await execute(input.cases[0])];
  process.stdout.write(JSON.stringify({schema:'cordis-verus.lifecycle-execution/v1',backend,results})+'\n');
}
