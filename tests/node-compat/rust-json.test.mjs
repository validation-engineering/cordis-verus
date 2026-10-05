import test from 'node:test';
import assert from 'node:assert/strict';
import {jsonValue} from '../../packages/compat-cordis/rust-plugin.js';

test('Rust JSON boundary copies data without running user serialization hooks',()=>{
  const source={list:[null,true,42,'value'],nested:{ok:false}};
  const value=jsonValue(source);
  assert.equal(JSON.stringify(value),JSON.stringify(source));
  assert.notEqual(value,source);
  assert.notEqual(value.list,source.list);
  let invoked=false;
  for(const bad of [new Date(),1n,NaN,Infinity,undefined,()=>{},[1,,3],{get field(){invoked=true;return 1;}},{toJSON(){invoked=true;return 'lossy';}}]) {
    assert.throws(()=>jsonValue(bad),TypeError);
  }
  assert.equal(invoked,false);
  const cycle={};cycle.self=cycle;
  assert.throws(()=>jsonValue(cycle),/cycles/);
  assert.throws(()=>jsonValue({[Symbol('opaque')]:1}),/symbol/);
  assert.throws(()=>jsonValue(Object.defineProperty({},'hidden',{value:42})),/hidden/);
  assert.throws(()=>jsonValue(Object.assign([1],{extra:42})),/extra/);
  const shared={answer:42};
  assert.equal(JSON.stringify(jsonValue([shared,shared])),JSON.stringify([shared,shared]));
});
