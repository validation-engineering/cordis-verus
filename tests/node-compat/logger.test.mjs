import test from 'node:test';
import assert from 'node:assert/strict';
import {inspect} from 'node:util';
import {Context, Logger, LoggerLevel} from '../../packages/compat-cordis/index.js';

test('logger formatting handles error causes, aggregate errors and exporter formatters', async () => {
  const root=new Context();
  root.logger.error(new Error('outer', {cause:new Error('inner')}));
  root.logger.error(new AggregateError([new Error('left'),new Error('right')], 'group'));
  assert.deepEqual(root.logger.buffer.map(message=>message.args[0].message), ['inner','outer','left','right']);
  assert.deepEqual(root.logger.buffer.map(message=>message.level), [LoggerLevel.ERROR,LoggerLevel.ERROR,LoggerLevel.ERROR,LoggerLevel.ERROR]);
  assert.equal(Logger.format({formatters:{x:value=>`<${value}>`}}, {name:'formatter',args:['%x %% %d',42,3.7],type:'info',level:2,sn:1,ts:0}), '<42> % 3');
  // User logging is an observation; it is not an executor failure.
  await root.settle();
  await root.dispose();
});

test('public names and service-access errors remain Cordis-facing', async () => {
  const root=new Context();
  assert.equal(inspect(root),'Context <root>');
  assert.equal(typeof root.fiber.uid,'number');
  const consumer=await root.plugin(ctx=>{
    assert.equal(inspect(ctx),'Context <root>');
    ctx.provide('publicService',42);
    assert.throws(()=>ctx.provide('publicService',43), /service "publicService" has been registered at <root>/);
  });
  const dependent=await root.inject(['publicService'], ctx=>{assert.equal(ctx.publicService,42);});
  await dependent.dispose();
  assert.throws(()=>dependent.ctx.publicService, /cannot get required service "publicService" in inactive context/);
  await consumer.dispose();
  await root.dispose();
});
