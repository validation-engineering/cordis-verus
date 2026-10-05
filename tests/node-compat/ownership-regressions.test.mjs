import test from 'node:test';
import assert from 'node:assert/strict';
import {Context} from '../../packages/compat-cordis/index.js';

const reentrant = error => error.code === 'REENTRANT_MUTATION';

test('owner cleanup retains its services after the publication inverse runs',async()=>{
  const ctx = new Context();
  const seen = [];
  const fiber = ctx.plugin(c=>{
    c.effect(()=>()=>seen.push(c.value.answer));
    c.provide('value',{answer:42});
  });
  await fiber;
  await fiber.dispose();
  assert.deepEqual(seen,[42]);
  await ctx.dispose();
});

test('failed owner cleanup keeps service access for a later retry',async()=>{
  const ctx = new Context();
  const seen = [];
  let fail = true;
  const fiber = ctx.plugin(c=>{
    c.effect(()=>()=>{
      if (fail) throw new Error('retry the inverse');
      seen.push(c.value.answer);
    });
    c.provide('value',{answer:42});
  });
  await fiber;
  await assert.rejects(fiber.dispose());
  fail = false;
  await fiber.retryCleanup();
  assert.deepEqual(seen,[42]);
  await ctx.dispose();
});

test('consumer action cannot await its own publication lease release',async()=>{
  const ctx = new Context();
  const revoke = ctx.provide('value',{answer:42});
  const fiber = ctx.inject(['value'],c=>{
    assert.throws(()=>revoke(),reentrant);
    assert.equal(c.value.answer,42);
    return()=>{
      assert.throws(()=>revoke(),reentrant);
      assert.equal(c.value.answer,42);
    };
  });
  await fiber;
  await fiber.dispose();
  await revoke();
  assert.equal(ctx.value,undefined);
  await ctx.dispose();
});

test('awaiting a publication handle preserves the consumer reentry guard',async()=>{
  const ctx = new Context();
  const cleanup = await ctx.provide('value',42);
  const fiber = ctx.inject(['value'],c=>{
    assert.throws(()=>cleanup(),reentrant);
    assert.equal(c.value,42);
  });
  await fiber;
  await fiber.dispose();
  await cleanup();
  await ctx.dispose();
});

test('an unrelated cleanup can revoke another active owner publication',async()=>{
  const ctx = new Context();
  const revoke = ctx.provide('value',42);
  const unrelated = ctx.plugin(()=>async()=>{await revoke();});
  await unrelated;
  await unrelated.dispose();
  assert.equal(ctx.value,undefined);
  await ctx.dispose();
});
