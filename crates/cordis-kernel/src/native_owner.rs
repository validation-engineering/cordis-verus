//! Identity of the execution actually issued by native Begin. Stored in the
//! registry until successful Unload; escaped host contexts cannot replace it.
use crate::action_ledger::ActionTicket;
use crate::execution::Execution;
use crate::lifecycle_state::registration::RegisteredInvocation;
use vstd::prelude::*;
verus! {
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct EpisodeOwner {pub origin:ActionTicket,pub work_domain:u64}
impl EpisodeOwner {
    pub open spec fn owns<V,C,G,I>(&self,execution:&Execution<V,C,G,I>)->bool {
        execution.origin()==Some(self.origin) && execution.work_state().domain_id()==self.work_domain
    }
    pub fn matches<V,C,G,I>(&self,execution:&Execution<V,C,G,I>)->(out:bool)
        ensures out==self.owns(execution),
    {execution.lifecycle_ticket()==Some(self.origin) && execution.work().domain()==self.work_domain}
    pub open spec fn admits<A>(&self,invocation:&RegisteredInvocation<A>)->bool {
        invocation.lifecycle()==self.origin && invocation.work().origin().domain_id()==self.work_domain
    }
    pub fn matches_invocation<A>(&self,invocation:&RegisteredInvocation<A>)->(out:bool)
        ensures out==self.admits(invocation),
    {invocation.lifecycle_ticket()==self.origin && invocation.ticket().domain()==self.work_domain}
}
}
