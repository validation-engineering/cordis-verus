// The application modules below are the unchanged, locked Harness sources.
// The fixture supplies requests and a minimal agent data carrier (id/session),
// as Harness's own tool-todo tests do; it does not replace service/tool plugins.
import assert from 'node:assert/strict';
import {Context} from '@deepseek-ai/cordis';
import SessionStore, {SessionId} from '@deepseek-ai/dsh-session';
import SystemPrompt from '@deepseek-ai/dsh-system-prompt';
import ToolRuntime from '@deepseek-ai/dsh-tools';
import SessionProjectionRegistry from '@deepseek-ai/dsh-session-projection';
import {ToolCallId} from '@deepseek-ai/dsh-llm';
import {createScope} from '@deepseek-ai/dsh-scope';
import * as ToolTodo from '@deepseek-ai/dsh-tool-todo';

const trace=[];
const record=(name,value)=>trace.push([name,JSON.parse(JSON.stringify(value))]);
const request=(agent,callId,todos,signal=new AbortController().signal)=>({
  signal,callId:ToolCallId(callId),name:'todo_write',arguments:{todos},agent,
});
const names=schemas=>schemas.map(item=>item.name);
const eventView=session=>session.snapshotEvents().map(({seq,type,data})=>({seq,type,data}));
const one=[{content:'  read the real code  ',status:'in_progress'},{content:'verify',status:'pending'}];

async function mount() {
  const ctx=new Context();
  for(const plugin of [SessionStore,SystemPrompt,ToolRuntime,SessionProjectionRegistry]) {
    const fiber=await ctx.plugin(plugin);
    record('mounted',fiber.name);
  }
  assert(ctx.sessions && ctx.systemPrompt && ctx.tools && ctx.sessionProjections);
  return ctx;
}

async function shutdown(ctx) {
  await ctx.fiber.dispose();
  const remaining=[SessionStore,SystemPrompt,ToolRuntime,SessionProjectionRegistry,ToolTodo]
    .map(plugin=>ctx.registry.has(plugin));
  assert.deepEqual(remaining,[false,false,false,false,false]);
  record('root-disposed',remaining);
}

async function globalGraph() {
  const ctx=await mount();
  const fiber=await ctx.plugin(ToolTodo,{allowParallelInProgress:false});
  const session=ctx.sessions.create(SessionId('harness-global'));
  const agent={id:session.id,session};
  record('schemas',ctx.tools.schemas());
  assert.deepEqual(names(ctx.tools.schemas()),['todo_write']);
  record('prompt-tools',names((await ctx.systemPrompt.assemble()).tools));
  record('initial-projection',ctx.sessionProjections.snapshot(session));
  assert.equal(ctx.sessionProjections.snapshot(session).values.todos,null);
  ctx.on('session/event',(subject,event)=>{
    assert.equal(subject,session);
    record('session-event',{seq:event.seq,type:event.type,data:event.data});
  });
  ctx.on('tools/result',(exec,result)=>record('result-observer',{callId:exec.callId,result}));
  const successful=await ctx.tools.execute(request(agent,'successful',one));
  assert.equal(successful.isError,false);
  assert.deepEqual(successful.value.counts,{pending:1,inProgress:1,completed:0});
  assert.equal(successful.value.todos[0].content,'read the real code');
  assert(Object.isFrozen(successful));
  record('successful',successful);
  record('projection',ctx.sessionProjections.snapshot(session));
  const before=session.seq;
  const malformed=await ctx.tools.execute(request(agent,'malformed',[{content:'bad',status:'doing'}]));
  assert.equal(malformed.isError,true);
  record('malformed',malformed);
  const parallel=await ctx.tools.execute(request(agent,'parallel',[
    {content:'a',status:'in_progress'},{content:'b',status:'in_progress'},
  ]));
  assert.equal(parallel.isError,true);
  assert.match(parallel.error.message,/at most one task/);
  record('parallel-rejected',parallel);
  const cancelled=new AbortController();
  cancelled.abort('fixture cancellation');
  const aborted=await ctx.tools.execute(request(agent,'aborted',one,cancelled.signal));
  assert.equal(aborted.error.info.code,'ABORTED_BEFORE_DISPATCH');
  record('aborted-before-dispatch',aborted);

  // Await an actual policy hook, cancel while it is pending, and verify the
  // real ToolRuntime never invokes the shipping tool body afterward.
  let entered,release;
  const enteredPromise=new Promise(resolve=>{entered=resolve;});
  const gate=new Promise(resolve=>{release=resolve;});
  const stopPolicy=ctx.on('tools/pre-execute',async(exec,next)=>{
    if(exec.callId==='awaited-cancel') {
      record('policy-entered',exec.callId);
      entered();
      await gate;
      record('policy-resumed',exec.signal.aborted);
    }
    return next();
  });
  const later=new AbortController();
  const pending=ctx.tools.execute(request(agent,'awaited-cancel',one,later.signal));
  await enteredPromise;
  later.abort('cancel during policy');
  release();
  const cancelledLater=await pending;
  assert.equal(cancelledLater.error.info.code,'ABORTED_BEFORE_DISPATCH');
  record('aborted-during-policy',cancelledLater);
  await stopPolicy();
  assert.equal(session.seq,before);
  record('rejections-left-log-unchanged',eventView(session));

  await fiber.dispose();
  assert.deepEqual(ctx.tools.schemas(),[]);
  assert.deepEqual(ctx.sessionProjections.snapshot(session).values,{});
  record('tool-unmounted',{schemas:ctx.tools.schemas(),projection:ctx.sessionProjections.snapshot(session)});
  const missing=await ctx.tools.execute(request(agent,'unmounted',one));
  assert.equal(missing.isError,true);
  assert.match(missing.error.message,/unknown tool/);
  record('call-after-unmount',missing);

  // Reload the actual same plugin after its registrations have drained.
  const reloaded=await ctx.plugin(ToolTodo,{allowParallelInProgress:true});
  const accepted=await ctx.tools.execute(request(agent,'reloaded',[
    {content:'a',status:'in_progress'},{content:'b',status:'in_progress'},
  ]));
  assert.equal(accepted.isError,false);
  record('reloaded-parallel',accepted);
  record('reloaded-projection',ctx.sessionProjections.snapshot(session));
  await reloaded.dispose();
  await shutdown(ctx);
}

async function scopedGraph() {
  const ctx=await mount();
  const session=ctx.sessions.create(SessionId('harness-scoped'));
  const agent={id:session.id,session};
  const outsider={id:SessionId('outside'),session};
  const scope=createScope(ctx,agent);
  // This registration is deliberately synchronous: the real scope backing
  // fiber is still pending. The Harness profile must own its prepare resource.
  const scopedResults=[];
  scope.ctx.on('tools/result',(exec,result)=>{
    scopedResults.push(exec.callId);
    record('scoped-result',{callId:exec.callId,result});
  });
  const fiber=await scope.ctx.plugin(ToolTodo,{allowParallelInProgress:true});
  assert.deepEqual(names(ctx.tools.schemas(agent)),['todo_write']);
  assert.deepEqual(ctx.tools.schemas(),[]);
  assert.deepEqual(ctx.tools.schemas(outsider),[]);
  record('scoped-visibility',{inside:names(ctx.tools.schemas(agent)),global:names(ctx.tools.schemas()),outside:names(ctx.tools.schemas(outsider))});
  record('scoped-prompt-tools',names((await ctx.systemPrompt.assemble({scope:agent})).tools));
  const visible=await ctx.tools.execute(request(agent,'inside',one));
  assert.equal(visible.isError,false);
  record('scoped-call',visible);
  const hidden=await ctx.tools.execute(request(outsider,'outside',one));
  assert.equal(hidden.isError,true);
  assert.match(hidden.error.message,/unknown tool/);
  record('outside-call',hidden);
  assert.deepEqual(scopedResults,['inside']);
  record('scoped-event-admission',scopedResults);
  record('scoped-projection',ctx.sessionProjections.snapshot(session));
  // Both calls must await the same real scope quiescence boundary.
  await Promise.all([scope.dispose(),scope.dispose()]);
  assert.equal(fiber.uid,null);
  assert.deepEqual(ctx.tools.schemas(agent),[]);
  assert.deepEqual(ctx.sessionProjections.snapshot(session).values,{});
  record('scope-disposed',{fiberRemoved:fiber.uid===null,schemas:ctx.tools.schemas(agent),projection:ctx.sessionProjections.snapshot(session)});
  const gone=await ctx.tools.execute(request(agent,'after-scope',one));
  assert.equal(gone.isError,true);
  assert.deepEqual(scopedResults,['inside']);
  record('after-scope-call',gone);
  await shutdown(ctx);
}

try {
  const scenario=process.env.CORDIS_HARNESS_SCENARIO;
  assert(['global','scoped'].includes(scenario));
  await (scenario==='global'?globalGraph():scopedGraph());
  process.stdout.write(JSON.stringify({status:'passed',trace})+'\n');
} catch(error) {
  process.stdout.write(JSON.stringify({status:'failed',trace,error:{name:error.name,message:error.message}})+'\n');
  process.stderr.write((error.stack??String(error))+'\n');
  process.exitCode=1;
}
