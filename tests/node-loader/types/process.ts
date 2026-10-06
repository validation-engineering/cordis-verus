import { ProcessDomain, type ProcessHost, type ProcessReloadPlan } from '../../../packages/compat-loader/process.js';
const processDomain = new ProcessDomain({ hostModule: './host.mjs', cwd: './workspace', env: { EXAMPLE: 'value' }, onOutput: ({stream,data}) => { const channel: 'stdout'|'stderr'=stream; void channel; void data; } });
const plan: ProcessReloadPlan = await processDomain.planReload('./artifact');
const mode: 'process-restart' = plan.strategy;
const pid: number | undefined = processDomain.pid;
void mode; void pid;
const host: ProcessHost = {ready:Promise.resolve(),call:()=>null,diagnostics:()=>({live:1}),close:async()=>{}};
void host;
// @ts-expect-error Process calls accept JSON values only.
await processDomain.call('service','callback',()=>{});
// @ts-expect-error PID is an observation, not a configuration knob.
processDomain.pid=1;
