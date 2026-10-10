//! Production cleanup commands and finite-history safety over those same calls.
//! Callback reports are inputs. No scheduler fairness or inverse effects are assumed.
use super::LifecycleState;
#[cfg(verus_keep_ghost)]
use crate::action_ledger::ActionKind;
use crate::action_ledger::{ActionError, ActionTicket};
use crate::lifecycle_actions::CleanupOutcome;
#[cfg(verus_keep_ghost)]
use crate::lifecycle_actions::LifecycleActions;
use crate::Error;
#[cfg(verus_keep_ghost)]
use crate::{Binding, Kernel, Phase};
use vstd::prelude::*;

verus! {
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum CleanupCommand {
    Request {id:usize,reservation:bool},
    Report {ticket:ActionTicket,outcome:CleanupOutcome},
    Retry {id:usize},
    Release {id:usize,reservation:bool},
    SettleSetup {ticket:ActionTicket},
    Withdraw {id:usize},
    Retire {id:usize},
    Remove {id:usize},
}
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum CleanupError { Control(Error), Reply(ActionError) }
pub type CleanupReply=Result<Option<ActionTicket>,CleanupError>;

/// Project managed release onto its control history; the original API keeps
/// the precise publication/lifecycle error and the exact released value slots.
pub open spec fn resource_reply<T>(result:Result<T,crate::lifecycle_actions::resources::CleanupReleaseError>)->CleanupReply {
    if result.is_ok() {Ok(None)} else {Err(CleanupError::Control(Error::InvalidState))}
}

pub open spec fn released(command:CleanupCommand,reply:CleanupReply)->Option<usize> {
    match command {
        CleanupCommand::Release {id,reservation:false} if reply.is_ok()=>Some(id),
        _=>None,
    }
}
pub open spec fn authorizes(command:CleanupCommand,reply:CleanupReply,id:usize,g:u64)->bool {
    match command {
        CleanupCommand::Report {ticket,outcome}=>reply.is_ok() && ticket.id==id
            && ticket.generation==g && outcome!=CleanupOutcome::Failed,
        _=>false,
    }
}

impl LifecycleState {
    /// Common contract shared by the executable dispatcher and managed release.
    pub open spec fn cleanup_step(&self,prior:&Self,command:CleanupCommand,reply:CleanupReply)->bool {
        &&& prior.wf() && self.wf()
        &&& self.protocol().history_preserved(&prior.protocol())
        &&& self.bindings_except(prior,released(command,reply))
        &&& reply.is_err() ==> self.same(prior)
        &&& forall|id:usize,g:u64| self.protocol().eligible(id,g) ==>
            prior.protocol().eligible(id,g) || authorizes(command,reply,id,g)
        &&& match command {
            CleanupCommand::Request {id,reservation}=> reply.is_ok() ==> {
                let ticket=reply.unwrap().unwrap();
                &&& reply.unwrap().is_some() && ticket.id==id && ticket.kind==ActionKind::Cleanup
                &&& ticket.domain==prior.protocol().domain_id() && ticket.action==prior.protocol().next_id()
                &&& self.protocol().cleanup_reply_enabled(ticket)
                &&& if reservation {ticket.generation==0 && LifecycleActions::reservation(&prior.control(),id)}
                    else {prior.control().cleanup_enabled(id) && self.control().restoration_guarded(id)
                        && self.control().generation_of(id)==Some(ticket.generation)}
            },
            CleanupCommand::Report {ticket,outcome}=> {
                &&& self.control().unchanged(&prior.control())
                &&& reply.is_ok() ==> reply.unwrap().is_none() && ticket.kind==ActionKind::Cleanup && prior.protocol().cleanup_reply_enabled(ticket)
                    && prior.protocol().recorded(ticket) && !self.protocol().outstanding(ticket.id) && !self.protocol().recorded(ticket)
                    && self.protocol().reported(ticket,outcome)
                    && self.protocol().eligible(ticket.id,ticket.generation)==(outcome!=CleanupOutcome::Failed)
            },
            CleanupCommand::Retry {id}=> {
                &&& self.control().unchanged(&prior.control())
                &&& reply.is_ok() ==> {
                    let ticket=reply.unwrap().unwrap();
                    &&& reply.unwrap().is_some() && ticket.id==id && ticket.kind==ActionKind::Cleanup
                    &&& ticket.domain==prior.protocol().domain_id() && ticket.action==prior.protocol().next_id()
                    &&& self.control().generation_of(id)==Some(ticket.generation)
                    &&& prior.protocol().failed(id,ticket.generation)
                    &&& !self.protocol().eligible(id,ticket.generation) && self.protocol().cleanup_reply_enabled(ticket)
                }
            },
            CleanupCommand::Release {id,reservation}=>reply.is_ok() ==> {
                &&& reply.unwrap().is_none() && prior.protocol().resource_finish_enabled(&prior.control(),id,reservation)
                &&& !self.protocol().blocked_spec(id)
                &&& if reservation {self.control().unchanged(&prior.control())} else {
                    self.control().no_committed(id) && self.control().phase_of(id)==Some(Phase::Inactive)
                        && crate::refinement::step(prior.control().paper(),self.control().paper(),id,crate::refinement::Rule::Unload)
                }
            },
            CleanupCommand::SettleSetup {ticket}=> {
                &&& self.control().unchanged(&prior.control())
                &&& reply.is_ok() ==> reply.unwrap().is_none() && ticket.kind==ActionKind::Setup
                    && prior.protocol().recorded(ticket) && !self.protocol().recorded(ticket)
            },
            CleanupCommand::Remove {id}=>reply.is_ok() ==> reply.unwrap().is_none()
                && !prior.protocol().blocked_spec(id) && !self.control().registered(id),
            _=>reply.is_ok() ==> reply.unwrap().is_none(),
        }
    }

    /// Rust and Node lifecycle adapters dispatch their real cleanup API here.
    pub fn execute_cleanup(&mut self,command:CleanupCommand)->(reply:CleanupReply)
        requires old(self).wf(),
        ensures final(self).cleanup_step(old(self),command,reply),
    {
        reveal(Kernel::unchanged);reveal(Kernel::same_bindings);reveal(Kernel::binding_recorded);
        let ghost prior=*self;
        let reply=match command {
            CleanupCommand::Request {id,reservation}=>issue_reply(if reservation {
                self.begin_reservation_cleanup(id)
            } else {self.begin_cleanup(id)}),
            CleanupCommand::Report {ticket,outcome}=>report_reply(self.complete_cleanup(ticket,outcome)),
            CleanupCommand::Retry {id}=>issue_reply(self.retry_cleanup(id)),
            CleanupCommand::Release {id,reservation}=>control_reply(if reservation {
                self.finish_reservation_cleanup(id)
            } else {self.finish_cleanup(id)}),
            CleanupCommand::SettleSetup {ticket}=>report_reply(self.complete_setup(ticket)),
            CleanupCommand::Withdraw {id}=>control_reply(self.leave(id)),
            CleanupCommand::Retire {id}=>control_reply(self.retire(id)),
            CleanupCommand::Remove {id}=>control_reply(self.remove(id)),
        };
        proof {
            match command {
                CleanupCommand::Withdraw {..}|CleanupCommand::Retire {..}|CleanupCommand::Remove {..}=>{
                    self.actions.same_observations(&prior.actions);
                },
                _=>{},
            }
            if reply.is_err() {self.same_observations(&prior);}
        }
        reply
    }

    /// A retained concrete binding protects its actual provider, including
    /// after retirement or a failed/retried consumer cleanup.
    pub proof fn binding_protects_provider(&self,consumer:usize,binding:Binding)
        requires self.wf(),self.control().binding_recorded(consumer,binding),
        ensures self.control().registered(binding.provider),
            self.control().phase_of(binding.provider)!=Some(Phase::Inactive),
            !self.control().is_restoring(binding.provider),!self.control().cleanup_enabled(binding.provider),
    {
        self.kernel.ordering(consumer,binding.provider);
        reveal(Kernel::resource_safe);reveal(Kernel::binding_recorded);reveal(Kernel::cleanup_enabled);
        reveal(Kernel::registered);reveal(Kernel::phase_of);reveal(Kernel::is_restoring);
        let i=choose|i:int| 0<=i<self.kernel.links.len() && self.kernel.links[i].live
            && self.kernel.links[i].consumer==consumer && self.kernel.links[i].binding==binding;
    }

    /// This executable loop constructs the proof history from actual dispatches.
    /// Its state snapshots are erased; only replies are retained at runtime.
    pub fn run_cleanup(&mut self,commands:&[CleanupCommand])->(out:CleanupRun)
        requires old(self).wf(),
        ensures final(self).wf(),execution(out.states@,commands@,out.replies@),
            out.states@[0]==*old(self),out.states@.last()==*final(self),
    {
        let mut replies=Vec::new();
        let ghost mut states=seq![*self];
        let mut i=0;
        while i<commands.len()
            invariant self.wf(),i<=commands.len(),replies.len()==i,states.len()==i+1,
                states[0]==*old(self),states.last()==*self,
                execution(states,commands@.subrange(0,i as int),replies@),
            decreases commands.len()-i,
        {
            let reply=self.execute_cleanup(commands[i]);
            replies.push(reply);
            proof {states=states.push(*self);}
            i+=1;
        }
        proof {assert(commands@.subrange(0,i as int)==commands@);}
        CleanupRun {replies,states:Ghost(states)}
    }
}

fn issue_reply(input:Result<ActionTicket,Error>)->(out:CleanupReply)
    ensures out==match input {Ok(ticket)=>Ok(Some(ticket)),Err(error)=>Err(CleanupError::Control(error))},
{match input {Ok(ticket)=>Ok(Some(ticket)),Err(error)=>Err(CleanupError::Control(error))}}
fn control_reply(input:Result<(),Error>)->(out:CleanupReply)
    ensures out==match input {Ok(())=>Ok(None),Err(error)=>Err(CleanupError::Control(error))},
{match input {Ok(())=>Ok(None),Err(error)=>Err(CleanupError::Control(error))}}
fn report_reply(input:Result<(),ActionError>)->(out:CleanupReply)
    ensures out==match input {Ok(())=>Ok(None),Err(error)=>Err(CleanupError::Reply(error))},
{match input {Ok(())=>Ok(None),Err(error)=>Err(CleanupError::Reply(error))}}

pub struct CleanupRun {
    pub replies:Vec<CleanupReply>,
    pub states:Ghost<Seq<LifecycleState>>,
}
pub open spec fn execution(states:Seq<LifecycleState>,commands:Seq<CleanupCommand>,replies:Seq<CleanupReply>)->bool {
    &&& states.len()==commands.len()+1 && replies.len()==commands.len() && states[0].wf()
    &&& forall|i:int| 0<=i<commands.len() ==> states[i+1].cleanup_step(&states[i],commands[i],replies[i])
}

pub proof fn history_between(states:Seq<LifecycleState>,commands:Seq<CleanupCommand>,replies:Seq<CleanupReply>,a:int,b:int)
    requires execution(states,commands,replies),0<=a<=b<states.len(),
    ensures states[b].wf(),states[b].protocol().history_preserved(&states[a].protocol()),
    decreases b-a,
{
    if b>0 {assert(states[b].cleanup_step(&states[b-1],commands[b-1],replies[b-1]));}
    if b>a {
        history_between(states,commands,replies,a,b-1);
        assert forall|ticket:ActionTicket| ticket.action<states[a].protocol().next_id()
            && !states[a].protocol().recorded(ticket) implies !states[b].protocol().recorded(ticket) by {
            assert(!states[b-1].protocol().recorded(ticket));
        }
    }
}

/// Arbitrarily many retries, foreign operations and rejected replies cannot
/// resurrect an identity already consumed by the real acknowledgement API.
pub proof fn consumed_ticket_never_returns(states:Seq<LifecycleState>,commands:Seq<CleanupCommand>,replies:Seq<CleanupReply>,
    i:int,ticket:ActionTicket,outcome:CleanupOutcome)
    requires execution(states,commands,replies),0<=i<commands.len(),
        commands[i]==(CleanupCommand::Report {ticket,outcome}),replies[i].is_ok(),
    ensures forall|j:int| i<j<states.len() ==> !states[j].protocol().recorded(ticket),
        forall|j:int,later:CleanupOutcome| i<j<commands.len() && commands[j]==(CleanupCommand::Report {ticket,outcome:later})
            ==> replies[j].is_err(),
{
    states[i].protocol().recorded_bounds(ticket);
    assert(!states[i+1].protocol().recorded(ticket));
    assert forall|j:int| i<j<states.len() implies !states[j].protocol().recorded(ticket) by {
        history_between(states,commands,replies,i+1,j);
    }
}

pub proof fn binding_at(states:Seq<LifecycleState>,commands:Seq<CleanupCommand>,replies:Seq<CleanupReply>,
    owner:usize,binding:Binding,n:int)
    requires execution(states,commands,replies),0<=n<states.len(),states[0].control().binding_recorded(owner,binding),
        forall|j:int| 0<=j<commands.len() ==> released(commands[j],replies[j])!=Some(owner),
    ensures states[n].control().binding_recorded(owner,binding),states[n].wf(),
        states[n].control().registered(binding.provider),!states[n].control().is_restoring(binding.provider),
        !states[n].control().cleanup_enabled(binding.provider),
    decreases n,
{
    if n>0 {
        assert(states[n].cleanup_step(&states[n-1],commands[n-1],replies[n-1]));
        binding_at(states,commands,replies,owner,binding,n-1);
    }
    states[n].binding_protects_provider(owner,binding);
}

/// Only an accepted Succeeded/Drained report can introduce release permission.
pub proof fn permission_origin(states:Seq<LifecycleState>,commands:Seq<CleanupCommand>,replies:Seq<CleanupReply>,
    owner:usize,g:u64,n:int)
    requires execution(states,commands,replies),0<=n<states.len(),states[n].protocol().eligible(owner,g),
    ensures states[0].protocol().eligible(owner,g)
        || exists|j:int| 0<=j<n && authorizes(commands[j],replies[j],owner,g),
    decreases n,
{
    if n>0 {
        assert(states[n].cleanup_step(&states[n-1],commands[n-1],replies[n-1]));
        if states[n-1].protocol().eligible(owner,g) {
            permission_origin(states,commands,replies,owner,g,n-1);
            if !states[0].protocol().eligible(owner,g) {
                let j=choose|j:int| 0<=j<n-1 && authorizes(commands[j],replies[j],owner,g);
                assert(0<=j<n);
            }
        } else {assert(authorizes(commands[n-1],replies[n-1],owner,g));}
    }
}

/// With no release permission at entry, a successful release has an earlier
/// accepted acknowledgement for exactly this owner and episode generation.
pub proof fn release_has_accepted_report(states:Seq<LifecycleState>,commands:Seq<CleanupCommand>,replies:Seq<CleanupReply>,
    i:int,owner:usize,reservation:bool)
    requires execution(states,commands,replies),0<=i<commands.len(),
        commands[i]==(CleanupCommand::Release {id:owner,reservation}),replies[i].is_ok(),
        forall|g:u64| !states[0].protocol().eligible(owner,g),
    ensures exists|j:int,g:u64| 0<=j<i && authorizes(commands[j],replies[j],owner,g)
        && states[i].control().generation_of(owner)==Some(g),
{
    assert(states[i+1].cleanup_step(&states[i],commands[i],replies[i]));
    let g=states[i].control().generation_of(owner).unwrap();
    assert(states[i].protocol().eligible(owner,g));
    permission_origin(states,commands,replies,owner,g,i);
    let j=choose|j:int| 0<=j<i && authorizes(commands[j],replies[j],owner,g);
}

/// From a failed receipt, every finite prefix without a new accepted success
/// (or explicit Drained policy report) retains the consumer's bindings.
pub proof fn failed_prefix_retains_dependencies(states:Seq<LifecycleState>,commands:Seq<CleanupCommand>,replies:Seq<CleanupReply>,
    owner:usize,g:u64,binding:Binding)
    requires execution(states,commands,replies),states[0].protocol().failed(owner,g),
        states[0].control().binding_recorded(owner,binding),
        forall|j:int,episode:u64| 0<=j<commands.len() ==> !authorizes(commands[j],replies[j],owner,episode),
    ensures forall|j:int| 0<=j<commands.len() ==> released(commands[j],replies[j])!=Some(owner),
        states.last().control().binding_recorded(owner,binding),
        states.last().control().registered(binding.provider),!states.last().control().is_restoring(binding.provider),
        !states.last().control().cleanup_enabled(binding.provider),
{
    states[0].protocol().failed_blocks_release(owner,g);
    assert forall|j:int| 0<=j<commands.len() implies released(commands[j],replies[j])!=Some(owner) by {
        if released(commands[j],replies[j])==Some(owner) {
            let episode=states[j].control().generation_of(owner).unwrap();
            permission_origin(states,commands,replies,owner,episode,j);
        }
    }
    binding_at(states,commands,replies,owner,binding,states.len() as int-1);
}
}
