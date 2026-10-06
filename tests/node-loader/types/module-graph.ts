import { WorkerDomain, type ModuleGraphSnapshot, type ModuleReloadPlan } from '../../../packages/compat-loader/worker.js';
const domain = new WorkerDomain();
const plan: ModuleReloadPlan = await domain.planReload('./project');
const graph: ModuleGraphSnapshot = await domain.moduleGraph();
const observed: 'observed' = graph.coverage;
const candidates: string[] = plan.affectedModules;
const actualPlan: ModuleReloadPlan = (await domain.reload()).plan;
void observed; void candidates; void actualPlan;
// @ts-expect-error Graph planning takes an artifact directory, not an arbitrary object.
await domain.planReload({ directory: './project' });
