//! One paper-facing witness for a real closed-data invocation. Root/current
//! code, retained inverse words and physical allocation transport are selected
//! from the same actual reports and object projection.
#[cfg(verus_keep_ghost)]
use super::context::Input;
use super::{objects::Projection, Value};
use crate::reversible_value::{
    effect::ScalarEffect,
    managed::replay::{bank::Bank, session::Outcome, Source},
};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{managed::semantics as s, service_composition::Address};
use vstd::prelude::*;

verus! {
#[allow(dead_code)] // Finite function and inverse interpretations erase with proof code.
pub ghost struct Contract<E> {projection:Projection,bank:Bank<Value>,source:Source<E,Value>,outcome:Outcome<E,Value>}
impl<E:ScalarEffect> Contract<E> {
    pub closed spec fn wf(&self)->bool {
        self.bank.wf() && self.projection.wf(&self.bank) && self.source.wf()
            && self.source.closed_data(self.projection.source().schema()) && self.outcome.matches(&self.source,&self.bank)
            && self.outcome.run.report.is_ok() && self.outcome.run.report->Ok_0.result.is_ok() && self.source.original().result.is_ok()
    }
    pub closed spec fn source(&self)->Source<E,Value> {self.source}
    pub closed spec fn outcome(&self)->Outcome<E,Value> {self.outcome}
    pub closed spec fn projection(&self)->Projection {self.projection}
    pub open spec fn contexts(&self,a:Input,b:Input)->bool {self.projection().contexts(&self.outcome(),a,b)}
    pub proof fn functions(&self,pc:usize,a:Input,b:Input)
        requires self.wf(),self.contexts(a,b),
        ensures super::semantics::result(
            super::fresh::generated(self.source().program(),a.resolve(self.source().original().ports@),pc,a.values,a.clocks,b.clocks,self.projection().name_table(&self.outcome())),self.projection().source().schema(),
            a.run(self.source().program(),self.source().original().ports@,pc),b.run(self.outcome().run.report->Ok_0.function@,self.outcome().run.report->Ok_0.ports@,pc)),
    {self.projection.function_context(&self.bank,&self.source,&self.outcome,pc,a,b);}
    pub open spec fn heaps(&self,a:Map<Address,s::Value<Value>>,b:Map<Address,s::Value<Value>>)->bool {
        super::recovery::heap(self.projection().mapping(),|k:Address|self.projection().versions(|j:Address|self.outcome().versions(j),k),self.projection().source().schema(),a,b)
    }
    pub proof fn inverses(&self,a:Map<Address,s::Value<Value>>,b:Map<Address,s::Value<Value>>)
        requires self.wf(),self.heaps(a,b),
        ensures super::recovery::optional(self.projection().mapping(),|k:Address|self.projection().versions(|j:Address|self.outcome().versions(j),k),self.projection().source().schema(),
            s::undo(self.source().original().result->Ok_0.steps@,a),s::undo(self.outcome().run.report->Ok_0.result->Ok_0.steps@,b)),
    {self.projection.inverse_word(&self.bank,&self.source,&self.outcome,a,b);}
    /// The map covers live, retired and unvisited stored identities, and is
    /// injective. Different names can still select the same mapped allocation.
    pub proof fn allocations(&self)
        requires self.wf(),ensures super::recovery::injective(self.projection().mapping()),
    {self.projection.mapping_injective(&self.bank);}
    pub(crate) proof fn new(projection:Projection,bank:Bank<Value>,source:Source<E,Value>,outcome:Outcome<E,Value>)->(out:Self)
        requires projection.wf(&bank),bank.wf(),source.wf(),source.closed_data(projection.source().schema()),outcome.matches(&source,&bank),
            outcome.run.report.is_ok(),outcome.run.report->Ok_0.result.is_ok(),source.original().result.is_ok(),
        ensures out.wf(),out.source()==source,out.outcome()==outcome,out.projection()==projection,
    {Self {projection,bank,source,outcome}}
}
impl<P,E:ScalarEffect+Copy> super::replay::Session<P,E> {
    /// Invoke wrappers already establish the report relation required here.
    /// The caller supplies no source program, map, head names or inverse word.
    pub proof fn paper_contract(&self,outcome:Outcome<E,Value>)->(out:Contract<E>)
        requires self.wf(),outcome.source<self.inner().sources().len(),outcome.matches(&self.inner().source(outcome.source as int),&self.inner().bank()),
            outcome.run.report.is_ok(),outcome.run.report->Ok_0.result.is_ok(),
        ensures out.wf(),out.source()==self.inner().source(outcome.source as int),out.outcome()==outcome,out.projection()==self.projection(),
    {
        self.contract_inputs(outcome.source as int);
        outcome.facts(&self.inner().source(outcome.source as int),&self.inner().bank());
        Contract::new(self.projection(),self.inner().bank(),self.inner().source(outcome.source as int),outcome)
    }
}
}
