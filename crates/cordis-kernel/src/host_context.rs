//! Immutable identity issued from the real Execution. The ordinary host checks
//! it after acquiring its Episode mutex and before exposing the locked state.
use crate::action_ledger::ActionTicket;
use crate::execution::Execution;
use crate::lifecycle_state::services::NativeContext;
use std::sync::Arc;
use vstd::prelude::*;
verus! {
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct Association {origin:Option<ActionTicket>,domain:u64}
impl Association {
    pub closed spec fn origin(&self)->Option<ActionTicket> {self.origin}
    pub closed spec fn work_domain(&self)->u64 {self.domain}
    pub open spec fn owns<V,C,G,I>(&self,execution:&Execution<V,C,G,I>)->bool {
        self.origin()==execution.origin() && self.work_domain()==execution.work_state().domain_id()
    }
    pub fn from_execution<V,C,G,I>(execution:&Execution<V,C,G,I>)->(out:Self)
        ensures out.owns(execution),
    {Self {origin:execution.lifecycle_ticket(),domain:execution.work().domain()}}
    pub fn matches<V,C,G,I>(&self,execution:&Execution<V,C,G,I>)->(out:bool)
        ensures out==self.owns(execution),
    {self.origin==execution.lifecycle_ticket() && self.domain==execution.work().domain()}
    pub fn native<V,C,G,I>(execution:&Execution<V,C,G,I>)->(out:Option<(Self,Arc<NativeContext>)>)
        requires execution.wf(),ensures out.is_some()==execution.capture().is_some(),
            out.is_some() ==> out.unwrap().0.owns(execution) && out.unwrap().1.describes(execution.capture().unwrap())
                && Some(out.unwrap().1.origin())==out.unwrap().0.origin() && out.unwrap().1.domain_id()==out.unwrap().0.work_domain(),
    {
        let context=execution.native_context()?;
        Some((Self::from_execution(execution),context))
    }
}
}
