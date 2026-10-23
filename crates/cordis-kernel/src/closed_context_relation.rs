//! Full test-input interpretation for actual retained root/Child functions.
//! Bindings are part of the input context, not an extra resolver chosen by a
//! caller. Closed references have the same checked logical schema in the two
//! real object tables; their physical allocations are related by Projection.
use super::{objects::Projection, Reference, Value};
#[cfg(verus_keep_ghost)]
use crate::reversible_value::managed::replay::{
    bank::Bank, session::Outcome, typed, typed_correspondence::epochs, Source,
};
use crate::reversible_value::managed::semantics as s;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::{effect::ScalarEffect, managed};
use crate::Port;
use vstd::prelude::*;

verus! {
pub ghost struct Input {
    pub bindings:Map<Port,Reference>,pub values:Map<usize,s::Value<Value>>,pub clocks:Map<usize,u64>,
}
impl Input {
    pub open spec fn references(&self,table:super::objects::Table)->bool {
        forall|port:Port|self.bindings.contains_key(port) ==> table.admits(#[trigger] self.bindings[port])
    }
    pub open spec fn resolve(&self,ports:Seq<Port>)->spec_fn(usize)->usize {|pc:usize|self.bindings[ports[pc as int]].index}
    pub open spec fn run<E:ScalarEffect>(&self,program:managed::Function<E,Value>,ports:Seq<Port>,pc:usize)->Option<crate::iterators::PartialIteration<Map<usize,s::Value<Value>>,usize>> {
        if pc<program.code().len() && (pc>=ports.len() || !self.bindings.contains_key(ports[pc as int])) {None}
        else {super::fresh::run(program,self.resolve(ports),pc,self.values,self.clocks)}
    }
}
impl Projection {
    pub open spec fn name_table<E:ScalarEffect>(&self,outcome:&Outcome<E,Value>)->Map<usize,Map<u64,u64>> {
        Map::new(self.source().schema().map(|i:int,_:Reference|i as usize).to_set(),|i:usize|self.versions(|address|outcome.versions(address),self.source().address(i as int)))
    }
    pub open spec fn contexts<E:ScalarEffect>(&self,outcome:&Outcome<E,Value>,a:Input,b:Input)->bool {
        a.references(self.source()) && b.references(self.target()) && a.bindings==b.bindings
            && super::semantics::heap(self.name_table(outcome),self.source().schema(),a.values,b.values)
            && super::fresh::admission(a.values,b.values,a.clocks,b.clocks,self.name_table(outcome))
    }
    pub proof fn name_table_facts<E:ScalarEffect>(&self,bank:&Bank<Value>,source:&Source<E,Value>,outcome:&Outcome<E,Value>)
        requires self.wf(bank),bank.wf(),source.wf(),outcome.matches(source,bank),outcome.run.report.is_ok(),outcome.run.report->Ok_0.result.is_ok(),
        ensures super::semantics::maps(self.name_table(outcome)),
    {
        assert forall|i:usize|#[trigger] self.name_table(outcome).contains_key(i) implies typed::injective(self.name_table(outcome)[i]) && epochs::ordered(self.name_table(outcome)[i]) by {
            let address=self.source().address(i as int);outcome.version_facts(source,bank,address);
            self.version_facts(bank,|address|outcome.versions(address),address);
        }
    }
    /// At pc=0 this relates the actual roots. The same theorem holds for every
    /// current continuation, and for actual Child outcomes from invoke_next_shared.
    /// Only arbitrary test contexts are inputs; allocation and historical/future
    /// head transports are all constructed from the retained runtime evidence.
    pub proof fn function_context<E:ScalarEffect>(&self,bank:&Bank<Value>,source:&Source<E,Value>,outcome:&Outcome<E,Value>,pc:usize,a:Input,b:Input)
        requires self.wf(bank),bank.wf(),source.wf(),source.closed_data(self.source().schema()),outcome.matches(source,bank),
            outcome.run.report.is_ok(),outcome.run.report->Ok_0.result.is_ok(),self.contexts(outcome,a,b),
        ensures super::semantics::result(
            super::fresh::generated(source.program(),a.resolve(source.original().ports@),pc,a.values,a.clocks,b.clocks,self.name_table(outcome)),self.source().schema(),
            a.run(source.program(),source.original().ports@,pc),b.run(outcome.run.report->Ok_0.function@,outcome.run.report->Ok_0.ports@,pc)),
    {
        self.name_table_facts(bank,source,outcome);outcome.facts(source,bank);reveal(managed::replay::TargetRun::from_source);
        let ports=source.original().ports@;assert(a.resolve(ports) =~= b.resolve(ports));
        if !(pc<source.program().code().len() && (pc>=ports.len() || !a.bindings.contains_key(ports[pc as int]))) {
            outcome.function_at_fresh(source,bank,a.resolve(ports),pc,a.values,b.values,a.clocks,b.clocks,self.name_table(outcome),self.source().schema());
        }
    }
}
}
