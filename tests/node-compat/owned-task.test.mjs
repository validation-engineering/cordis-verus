import test from 'node:test';
import assert from 'node:assert/strict';
import {Context} from '../../packages/compat-cordis/index.js';

const reentrant = error => error.code === 'REENTRANT_MUTATION';

test('owned tasks drain before any inverse and late effect admission is closed',async()=>{
  const ctx = new Context();
  const entered = Promise.withResolvers(), aborted = Promise.withResolvers(), gate = Promise.withResolvers();
  const trace = [];
  const owner = ctx.plugin(c=>{
    c.task(async signal=>{
      signal.addEventListener('abort',()=>aborted.resolve(),{once:true});
      entered.resolve();
      await gate.promise;
      assert.throws(()=>c.effect(()=>{}),/inactive|AdmissionClosed/);
      trace.push('task landed');
    });
    // Registered after the task: ordinary LIFO alone would restore this early.
    c.effect(()=>()=>trace.push('resource inverse'));
  });
  await owner;
  await entered.promise;
  const closing = owner.dispose();
  await aborted.promise;
  assert.deepEqual(trace,[]);
  gate.resolve();
  await closing;
  assert.deepEqual(trace,['task landed','resource inverse']);
  await ctx.dispose();
});

test('long lived tasks do not block graph settlement and cancellation is cooperative',async()=>{
  const ctx = new Context();
  const gate = Promise.withResolvers();
  const task = ctx.task(async signal=>{await gate.promise;return signal.reason;});
  await ctx.settle();
  task.cancel('requested');
  assert.equal(task.signal.aborted,true);
  let finished = false;
  task.promise.then(()=>finished=true);
  await Promise.resolve();
  assert.equal(finished,false);
  gate.resolve();
  assert.equal(await task.join(),'requested');
  await ctx.dispose();
});

test('owned task self join and self or domain disposal are rejected without deadlock',async()=>{
  const ctx = new Context();
  let task;
  task = ctx.task(async()=>{
    assert.throws(()=>task.join(),reentrant);
    await assert.rejects(ctx.dispose(),reentrant);
    await assert.rejects(ctx.fiber.dispose(),reentrant);
    await assert.rejects(ctx.settle(),reentrant);
    return 42;
  });
  assert.equal(await task.join(),42);
  await ctx.dispose();
});

test('ordinary asynchronous event handlers do not acquire task drain ownership',async()=>{
  const ctx = new Context();
  const entered = Promise.withResolvers(), gate = Promise.withResolvers(), done = Promise.withResolvers();
  let finished = false;
  ctx.on('ordinary',async()=>{entered.resolve();await gate.promise;finished=true;done.resolve();});
  ctx.emit('ordinary');
  await entered.promise;
  await ctx.dispose();
  assert.equal(finished,false);
  gate.resolve();
  await done.promise;
});

test('task rejection reaches join while shutdown still waits for real completion',async()=>{
  const ctx = new Context();
  const entered = Promise.withResolvers(), gate = Promise.withResolvers();
  const task = ctx.task(async()=>{entered.resolve();await gate.promise;throw new Error('job failed');});
  await entered.promise;
  const closing = ctx.dispose();
  let closed = false;
  closing.then(()=>closed=true);
  await Promise.resolve();
  assert.equal(closed,false);
  gate.resolve();
  await assert.rejects(task.join(),/job failed/);
  await closing;
});

test('continuations descended from a completed task retain their original episode',async()=>{
  const ctx = new Context();
  const gate = Promise.withResolvers();
  let task, continuation, original;
  const owner = ctx.plugin(c=>{
    original ??= c;
    assert.equal(c,original);
    task = c.task(()=>{
      continuation ??= gate.promise.then(()=>{
        assert.throws(()=>c.effect(()=>{}),error=>error.code==='STALE_EPISODE');
      });
    });
  });
  await owner;
  await task.join();
  await owner.restart();
  await task.join();
  gate.resolve();
  await continuation;
  await ctx.dispose();
});


test('old managed continuations cannot read a restarted episode through injected or reflective access',async()=>{
  const ctx = new Context();
  ctx.provide('value',{label:'old'});
  const gate = Promise.withResolvers();
  let continuation;
  const owner = await ctx.inject(['value'],c=>{
    const reflect = c.reflect;
    continuation ??= gate.promise.then(()=>{
      assert.throws(()=>c.value,error=>error.code==='STALE_EPISODE');
      assert.throws(()=>reflect.get('value'),error=>error.code==='STALE_EPISODE');
    });
  });
  ctx.set('value',{label:'new'});
  await owner.restart();
  assert.equal(ctx.value.label,'new');
  gate.resolve();
  await continuation;
  await ctx.dispose();
});

for (const transition of ['restart','dispose']) {
  test(`old managed continuations cannot acquire another owner's effects after ${transition}`,async()=>{
    const ctx = new Context();
    const gate = Promise.withResolvers();
    const effect = ctx.effect.bind(ctx);
    let continuation, task, acquired = 0;
    const owner = await ctx.plugin(c=>{
      task = c.task(()=>{
        continuation ??= gate.promise.then(()=>{
          assert.throws(()=>effect(()=>{acquired++;}),error=>error.code==='STALE_EPISODE');
        });
      });
    });
    await task.join();
    await owner[transition]();
    if (transition==='restart') await task.join();
    gate.resolve();
    await continuation;
    assert.equal(acquired,0);
    await ctx.dispose();
  });
}
