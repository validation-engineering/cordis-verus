//! Resolve, intercept, normalize and bind the actual registered module in one
//! checked operation. The resulting immutable recipe is used for mount/retry.
use crate::configuration_binding::Modules;
use crate::configuration_data::{self as data, Value};
#[cfg(verus_keep_ghost)]
use crate::configuration_schema as schema;
use crate::configuration_schema::{Failure, Schema};
use std::ops::Deref;
use std::sync::Arc;
use vstd::prelude::*;
verus! {
pub struct Definition<T> {body:Arc<T>,schema:Arc<Schema>}
impl<T> Definition<T> {
    pub closed spec fn body(&self)->T {*self.body}
    pub closed spec fn schema(&self)->Schema {*self.schema}
    pub fn new(body:T,schema:Arc<Schema>)->(out:Self) ensures out.body()==body,out.schema()==*schema,
    {Self {body:Arc::new(body),schema}}
}
impl<T> Deref for Definition<T> {type Target=T;fn deref(&self)->(out:&T) ensures *out==self.body(), {&self.body}}
#[derive(Debug)]
pub enum Error {Unknown,Schema(Failure)}
#[allow(dead_code)]
pub struct Prepared<T,S> {module:Option<Arc<Definition<T>>>,raw:Arc<Value>,config:Arc<Value>,scope:Arc<S>,patch:Ghost<Option<data::Data>>}
impl<T,S> Clone for Prepared<T,S> {
    fn clone(&self)->(out:Self) ensures out==*self,
    {Self {module:self.module.as_ref().map(|m:&Arc<Definition<T>>| -> (out:Arc<Definition<T>>) ensures out==*m, {m.clone()}),raw:self.raw.clone(),config:self.config.clone(),scope:self.scope.clone(),patch:self.patch}}
}
impl<T,S> Prepared<T,S> {
    pub closed spec fn selected_module(&self)->Option<Arc<Definition<T>>> {self.module}
    pub closed spec fn raw_value(&self)->data::Data {self.raw.model()}
    pub closed spec fn value(&self)->data::Data {self.config.model()}
    pub closed spec fn context(&self)->S {*self.scope}
    pub closed spec fn patch(&self)->Option<data::Data> {self.patch@}
    pub open spec fn wf(&self)->bool {
        match self.selected_module() {
            Some(module)=>schema::normalized(module.schema(),match self.patch() {Some(p)=>data::overlay(self.raw_value(),p),None=>self.raw_value()})==Some(self.value()),
            None=>self.value()==self.raw_value(),
        }
    }
    pub fn selected(&self)->(out:Option<&Arc<Definition<T>>>) ensures match out {None=>self.selected_module().is_none(),Some(m)=>self.selected_module()==Some(*m)}, {self.module.as_ref()}
    pub fn config(&self)->(out:&Value) ensures out.model()==self.value(), {&self.config}
    pub fn raw(&self)->(out:&Value) ensures out.model()==self.raw_value(), {&self.raw}
    pub fn scope(&self)->(out:&S) ensures *out==self.context(), {&self.scope}
    pub fn with_scope(self,scope:S)->(out:Self)
        ensures out.selected_module()==self.selected_module(),out.raw_value()==self.raw_value(),out.value()==self.value(),out.patch()==self.patch(),out.context()==scope,
            self.wf() ==> out.wf(),
    {Self {module:self.module,raw:self.raw,config:self.config,scope:Arc::new(scope),patch:self.patch}}
    /// Interpretation of the complete resolved record, including group roots.
    /// A None module is the built-in Unit group, not an invented external URL.
    pub fn entry<Id,I,J>(&self,id:Id,isolate:I,intercept:J,disabled:bool)->(out:crate::configuration_entry::Entry<Id,Option<Arc<Definition<T>>>,I,J,&Value>)
        ensures out.id==id,out.url==self.selected_module(),out.isolate==isolate,out.intercept==intercept,
            out.config.model()==self.raw_value(),out.disabled==disabled,
    {
        crate::configuration_entry::Entry::new(id,self.module.as_ref().map(|m:&Arc<Definition<T>>| -> (out:Arc<Definition<T>>) ensures out==*m, {m.clone()}),isolate,intercept,self.raw(),disabled)
    }
}
impl<T> Modules<Definition<T>> {
    pub fn prepare<S>(&self,name:Option<&str>,raw:Value,patch:Option<&Value>,scope:S)->(out:Result<Prepared<T,S>,Error>)
        requires self.wf(),
        ensures out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.raw_value()==raw.model() && out->Ok_0.context()==scope
            && out->Ok_0.patch()==data::optional(patch)
            && (name.is_none() ==> out->Ok_0.selected_module().is_none())
            && (name.is_some() ==> exists|i:int|0<=i<self.keys().len() && self.keys()[i]==name.unwrap()@ && out->Ok_0.selected_module()==Some(self.values()[i])),
    {
        let module=match name {Some(name)=>match self.get(name) {Some(module)=>Some(module.clone()),None=>return Err(Error::Unknown)},None=>None};
        let config=match &module {
            Some(module)=>{
                let intercepted=match patch {Some(patch)=>data::apply(&raw,patch),None=>raw.copy()};
                match module.schema.validate(&intercepted) {Ok(value)=>value,Err(error)=>return Err(Error::Schema(error))}
            },
            None=>raw.copy(),
        };
        Ok(Prepared {module,raw:Arc::new(raw),config:Arc::new(config),scope:Arc::new(scope),patch:Ghost(data::optional(patch))})
    }
}
}
