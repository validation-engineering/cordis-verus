//! Validate actual scalar target observations against the retained source.
//! Validation is after invocation and before Finish, not an atomic pre-write
//! guard. On mismatch the original report and cleanup owner remain available.
#[cfg(verus_keep_ghost)]
use super::{super::Step, transport};
use super::{inputs::Operand, Source, TargetRun};
use crate::reversible_value::{effect::ScalarEffect, ValueState};
use vstd::prelude::*;

verus! {
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
#[allow(inconsistent_fields)]
pub enum Error {
    SourceIncomplete,TargetIncomplete,Length {expected:usize,observed:usize},
    ControlFlow {step:usize,expected:usize,observed:usize},Kind {step:usize},
    State {step:usize,expected:ValueState,observed:ValueState},
}
pub open spec fn same_scalar<T:?Sized>(source:Step<T>,target:Step<T>)->bool {
    source.pc==target.pc && source.before() is Scalar && source.before()==target.before()
        && source.after()==target.after() && source.outcome()==target.outcome() && source.next==target.next
}
impl<E:ScalarEffect,T:?Sized> Source<E,T> {
    pub closed spec fn scalar_program(&self)->bool {
        forall|i:int|0<=i<self.program().code().len() ==> (#[trigger] self.program().code()[i]).effect is Kernel
    }
    /// Inspect the whole retained body, including branches absent from the
    /// successful source path. No plugin callback executes during inspection.
    pub fn is_scalar_program(&self)->(out:bool)
        ensures out==self.scalar_program(),out ==> self.program().controlled(),
    {
        let mut i=0;
        while i<self.function.code.len()
            invariant i<=self.function.code.len(),
                forall|j:int|0<=j<i ==> (#[trigger] self.function.code@[j]).effect is Kernel,
            decreases self.function.code.len()-i,
        {
            if !matches!(&self.function.code[i].effect,super::super::Effect::Kernel(_)) {return false;}
            i+=1;
        }
        true
    }
}
impl<C,G,A,R,T:?Sized,M,X,E:ScalarEffect> TargetRun<C,G,A,R,T,M,X,E> {
    pub open spec fn scalar_observations_match(&self,source:&Source<E,T>)->bool {
        source.original().result.is_ok() && source.original().result->Ok_0.failure.is_none()
            && self.report.is_ok() && self.report->Ok_0.result.is_ok() && self.report->Ok_0.result->Ok_0.failure.is_none()
            && source.original().result->Ok_0.steps.len()==self.report->Ok_0.result->Ok_0.steps.len()
            && forall|i:int|0<=i<source.original().result->Ok_0.steps.len() ==>
                same_scalar(#[trigger] source.original().result->Ok_0.steps@[i],self.report->Ok_0.result->Ok_0.steps@[i])
    }
    /// Compare immutable operands captured from the actual retained inverses.
    /// No caller supplies a target input equality, expected outcome or inverse.
    pub fn check_scalar_observations(&self,source:&Source<E,T>)->(out:Result<(),Error>)
        requires source.wf(),self.from_source(source),
        ensures out.is_ok() ==> self.scalar_observations_match(source),
    {
        hide(crate::reversible_value::joint::valid);hide(crate::reversible_value::joint::step);
        if !source.succeeded() {return Err(Error::SourceIncomplete);}
        let report=match &self.report {Ok(report)=>report,Err(_)=>return Err(Error::TargetIncomplete)};
        let target=match &report.result {Ok(report)=>report,Err(_)=>return Err(Error::TargetIncomplete)};
        if !target.succeeded() {return Err(Error::TargetIncomplete);}
        if self.inputs.len()!=source.inputs.len() {return Err(Error::Length {expected:source.inputs.len(),observed:self.inputs.len()});}
        proof {source.facts();}
        let mut i=0;
        while i<self.inputs.len()
            invariant i<=self.inputs.len(),self.from_source(source),source.wf(),
                source.original().result.is_ok(),source.original().result->Ok_0.failure.is_none(),
                self.report.is_ok(),self.report->Ok_0.result.is_ok(),self.report->Ok_0.result->Ok_0.failure.is_none(),
                self.inputs.len()==source.inputs.len(),
                forall|j:int|0<=j<i ==> same_scalar(source.inputs@[j].source(),self.inputs@[j].source()),
            decreases self.inputs.len()-i,
        {
            let a=&source.inputs[i];let b=&self.inputs[i];
            if a.pc()!=b.pc() {return Err(Error::ControlFlow {step:i,expected:a.pc(),observed:b.pc()});}
            match (a.operand(),b.operand()) {
                (Operand::Scalar(expected),Operand::Scalar(observed))=>{
                    if expected.value!=observed.value || expected.depth!=observed.depth {
                        return Err(Error::State {step:i,expected:*expected,observed:*observed});
                    }
                },_=>return Err(Error::Kind {step:i}),
            }
            proof {transport::paired(source.program().code(),a.source(),b.source());}
            i+=1;
        }
        proof {
            assert forall|j:int|0<=j<source.original().result->Ok_0.steps.len() implies
                same_scalar(#[trigger] source.original().result->Ok_0.steps@[j],self.report->Ok_0.result->Ok_0.steps@[j]) by {
                assert(source.inputs@[j].source()==source.original().result->Ok_0.steps@[j]);
                assert(self.inputs@[j].source()==self.report->Ok_0.result->Ok_0.steps@[j]);
                assert(same_scalar(source.inputs@[j].source(),self.inputs@[j].source()));
            }
        }
        Ok(())
    }
    /// Equality includes the entire strict scalar inverse domain, while the
    /// inverse permissions and cleanup queues remain separately owned.
    pub proof fn scalar_inverse(&self,source:&Source<E,T>,i:int)
        requires source.wf(),self.from_source(source),self.scalar_observations_match(source),
            0<=i<source.original().result->Ok_0.steps.len(),
        ensures source.original().result->Ok_0.steps@[i].result is Scalar,
            self.report->Ok_0.result->Ok_0.steps@[i].result is Scalar,
            source.original().result->Ok_0.steps@[i].result->Scalar_inverse@.state()
                ==self.report->Ok_0.result->Ok_0.steps@[i].result->Scalar_inverse@.state(),
    { }
}
}
