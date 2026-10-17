//! One checked owner for the Node lifecycle, versioned publications and
//! availability protocol, callback scopes, cleanup lookup selections and actual
//! interfaces with dynamic declaration ownership.
//! Mutable access is only through recorded operations.
//! Its history is erased; production retains no old JS handles or snapshots.
use crate::action_ledger::{ActionKind, ActionTicket};
use crate::availability::admission::{Admission, AdmissionError};
use crate::availability::{Availability, CheckAction, CheckError, CheckTicket};
use crate::invocation_ledger::{InvocationLedger, ScopeBlock, ScopeError, ScopeHandle};
use crate::lifecycle_actions::resources::CleanupReleaseError;
use crate::lifecycle_actions::CleanupOutcome;
use crate::lifecycle_state::cleanup::{CleanupCommand, CleanupError, CleanupReply};
use crate::lifecycle_state::LifecycleState;
use crate::publication::values::{PublicationStore, RejectedValue, ReleasedValue};
use crate::publication::{PublicationError, PublicationId};
use crate::Phase;
use crate::{Error, Port};
use std::collections::{BTreeMap, BTreeSet};
use vstd::prelude::*;
#[path = "node_history.rs"]
pub mod history;
use history::History;
#[path = "node_policy.rs"]
pub mod policy;
use policy::{Policy, PolicyError, Profile};
#[path = "node_episode.rs"]
pub mod episode;
use episode::{Command as EpisodeCommand, Episode, EpisodeError};
#[path = "node_handles.rs"]
pub mod handles;
#[path = "node_interfaces.rs"]
pub mod interfaces;
use interfaces::Interface;
#[path = "node_scope_path.rs"]
pub mod paths;
#[path = "node_reads.rs"]
pub mod reads;
#[path = "node_resources.rs"]
pub mod resources;
#[path = "node_scopes.rs"]
pub mod scopes;
#[cfg(verus_keep_ghost)]
use history::{Event, Observation};

verus! {
#[allow(dead_code)] // History is ghost state, erased from executable Rust.
pub struct NodeRuntime {
    policy:Policy,control:LifecycleState,store:PublicationStore<u64>,checks:Availability,checked:BTreeSet<usize>,
    admissions:BTreeMap<usize,Admission>,episodes:BTreeMap<usize,Episode>,scopes:InvocationLedger,restoring:BTreeMap<usize,Vec<PublicationId>>,released:Vec<u64>,
    interfaces:BTreeMap<usize,Interface>,dynamic:BTreeMap<(u64,u64),usize>,
    history:Ghost<History>,
}
#[allow(dead_code)] // Certified history is erased.
pub struct Snapshot {history:Ghost<History>}
impl Snapshot {
    pub closed spec fn history(&self)->History {self.history@}
    pub open spec fn certified(&self)->bool {self.history().valid()}
}
impl NodeRuntime {
    pub closed spec fn observation(&self)->Observation {
        Observation {policy:self.policy,control:self.control,store:self.store,checks:self.checks,checked:self.checked@,admissions:self.admissions@,episodes:self.episodes@,scopes:self.scopes,restoring:self.restoring@,released:self.released@,interfaces:self.interfaces@,dynamic:self.dynamic@}
    }
    pub closed spec fn history(&self)->History {self.history@}
    pub open spec fn wf(&self)->bool {
        self.observation().wf() && self.history().valid() && self.history().states.last()==self.observation()
    }
    pub fn new(domain:u64)->(out:Self)
        ensures out.wf(),out.observation().control.protocol().domain_id()==domain,
    {
        let policy=Policy {profile:Profile::Cordis,configured:false};let control=LifecycleState::new(domain);let store=PublicationStore::for_domain(domain);
        let checks=Availability::new(domain);let checked=BTreeSet::new();
        let admissions=BTreeMap::new();let episodes=BTreeMap::new();let scopes=InvocationLedger::new(domain);let restoring=BTreeMap::new();let released=Vec::new();
        let interfaces=BTreeMap::new();let dynamic=BTreeMap::new();
        let ghost state=Observation {policy,control,store,checks,checked:checked@,admissions:admissions@,episodes:episodes@,scopes,restoring:restoring@,released:released@,interfaces:interfaces@,dynamic:dynamic@};
        Self {policy,control,store,checks,checked,admissions,episodes,scopes,restoring,released,interfaces,dynamic,history:Ghost(History {states:seq![state],events:Seq::empty()})}
    }
    pub fn state(&self)->(out:&LifecycleState) requires self.wf(),ensures *out==self.observation().control,out.wf(), {&self.control}
    pub fn store(&self)->(out:&PublicationStore<u64>) requires self.wf(),ensures *out==self.observation().store,out.wf(), {&self.store}
    pub fn checks(&self)->(out:&Availability) requires self.wf(),ensures *out==self.observation().checks,out.wf(), {&self.checks}
    pub fn checked(&self)->(out:&BTreeSet<usize>) ensures out@==self.observation().checked, {&self.checked}
    pub fn episode(&self,id:usize)->(out:Option<&Episode>)
        ensures out.is_some()==self.observation().episodes.contains_key(id),out.is_some() ==> *out.unwrap()==self.observation().episodes[id],
    {self.episodes.get(&id)}
    pub fn admission(&self,id:usize)->(out:Option<&Admission>)
        requires self.wf(),ensures out.is_some()==self.observation().admissions.contains_key(id),
            out.is_some() ==> *out.unwrap()==self.observation().admissions[id] && out.unwrap().wf() && out.unwrap().origin().id==id,
    {self.admissions.get(&id)}
    pub fn validate(&self,id:usize,generation:u64)->(out:Result<(),EpisodeError>)
        requires self.wf(),ensures out==episode::validation(self.observation(),id,generation),
    {
        if self.control.kernel().episode_generation(id)!=Some(generation) {return Err(EpisodeError::Stale);}
        let retired=self.control.kernel().retired(id);let phase=self.control.kernel().phase(id);
        if generation==0 && !retired && phase==Some(Phase::Inactive) {
            if let Some(e)=self.episodes.get(&id) {if e.prepared {return Ok(());}}
        }
        if retired || (phase!=Some(Phase::Loading) && phase!=Some(Phase::Active)) {Err(EpisodeError::Closed)} else {Ok(())}
    }
    pub fn ready(&self,consumer:usize)->(out:bool)
        requires self.wf(),ensures out==self.observation().checks.ready_spec(&self.observation().control,&self.observation().store,self.observation().checked,consumer),
    {self.checks.ready(&self.control,&self.store,&self.checked,consumer)}
    pub fn current_check(&self,ticket:CheckTicket)->(out:bool)
        requires self.wf(),ensures out==self.observation().checks.fresh(ticket,&self.observation().control,&self.observation().store),
    {self.checks.current(ticket,&self.control,&self.store)}
    pub fn snapshot(&self)->(out:Snapshot)
        requires self.wf(),ensures out.certified(),out.history()==self.history(),out.history().states.last()==self.observation(),
    {Snapshot {history:Ghost(self.history@)}}
    proof fn record(tracked &mut self,before:Observation,event:Event)
        requires old(self).observation().wf(),old(self).history().valid(),old(self).history().states.last()==before,
            history::step(before,old(self).observation(),event),
        ensures final(self).wf(),final(self).observation()==old(self).observation(),
            final(self).history()==old(self).history().append(old(self).observation(),event),
    {
        self.history@.extended(self.observation(),event);
        self.history=Ghost(self.history@.append(self.observation(),event));
    }
    pub fn insert(&mut self,parent:Option<usize>,dependencies:Vec<Port>,provisions:Vec<Port>)->(out:Result<usize,Error>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::Insert {parent,dependencies:dependencies@,provisions:provisions@,out}),
    {
        let ghost before=self.observation();let ghost saved_dependencies=dependencies@;let ghost saved_provisions=provisions@;
        proof {self.store.slot_count();self.scopes.unchanged_reflexive();self.control.same_reflexive();self.store.same_reflexive();self.control.same_observations(&self.control);}
        let descriptor=Interface {parent,dependencies:dependencies.clone(),provisions:provisions.clone()};
        let out=self.control.insert(parent,dependencies,provisions);
        if let Ok(id)=out {self.episodes.insert(id,Episode::new());self.interfaces.insert(id,descriptor);self.policy.configured=true;}
        proof {
            reveal(history::operation);if self.control.same(&before.control) {self.control.same_components(&before.control);}
            if self.store.same(&before.store) {self.store.same_observations(&before.store);}
            if self.control.protocol().same(&before.control.protocol()) {self.control.protocol().same_observations(&before.control.protocol());}
            if self.control.control().unchanged(&before.control.control()) {self.control.control().unchanged_observations(&before.control.control());}
            self.record(before,Event::Insert {parent,dependencies:saved_dependencies,provisions:saved_provisions,out});
        }
        out
    }
    pub fn declare_provision(&mut self,id:usize,port:Port)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::Declare {id,port,out}),
    {
        let ghost before=self.observation();
        proof {self.store.slot_count();self.scopes.unchanged_reflexive();self.control.same_reflexive();self.store.same_reflexive();self.control.same_observations(&self.control);}
        let out=self.control.declare_provision(id,port);
        if out.is_ok() && !self.initial_provision(id,port) {self.dynamic.insert((port.key,port.realm),id);}
        proof {
            reveal(history::operation);if self.control.same(&before.control) {self.control.same_components(&before.control);}
            if self.store.same(&before.store) {self.store.same_observations(&before.store);}
            if self.control.protocol().same(&before.control.protocol()) {self.control.protocol().same_observations(&before.control.protocol());}
            if self.control.control().unchanged(&before.control.control()) {self.control.control().unchanged_observations(&before.control.control());}
            self.record(before,Event::Declare {id,port,out});
        }
        out
    }
    pub fn configure_pending_dependencies(&mut self,id:usize,dependencies:Vec<Port>)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::Dependencies {id,dependencies:dependencies@,out}),
    {
        let ghost before=self.observation();let ghost saved_dependencies=dependencies@;
        proof {self.store.slot_count();self.scopes.unchanged_reflexive();self.control.same_reflexive();self.store.same_reflexive();self.control.same_observations(&self.control);}
        let replacement=dependencies.clone();
        let out=self.control.configure_pending_dependencies(id,dependencies);
        if out.is_ok() {
            proof {before.control.control_history_correspondence();self.control.control_history_correspondence();
                self.history@.interface_correspondence(self.history@.events.len() as int);}
            self.interfaces.get_mut(&id).unwrap().dependencies=replacement;
        }
        proof {
            reveal(history::operation);if self.control.same(&before.control) {self.control.same_components(&before.control);}
            if self.store.same(&before.store) {self.store.same_observations(&before.store);}
            if self.control.protocol().same(&before.control.protocol()) {self.control.protocol().same_observations(&before.control.protocol());}
            if self.control.control().unchanged(&before.control.control()) {self.control.control().unchanged_observations(&before.control.control());}
            self.record(before,Event::Dependencies {id,dependencies:saved_dependencies,out});
        }
        out
    }
    pub fn release_provision(&mut self,id:usize,port:Port)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::ReleaseProvision {id,port,out}),
    {
        let ghost before=self.observation();
        proof {self.store.slot_count();self.scopes.unchanged_reflexive();self.control.same_reflexive();self.store.same_reflexive();self.control.same_observations(&self.control);}
        let out=self.control.release_provision(id,port);
        if out.is_ok() && self.dynamic.get(&(port.key,port.realm))==Some(&id) {self.dynamic.remove(&(port.key,port.realm));}
        proof {
            reveal(history::operation);if self.control.same(&before.control) {self.control.same_components(&before.control);}
            if self.store.same(&before.store) {self.store.same_observations(&before.store);}
            if self.control.protocol().same(&before.control.protocol()) {self.control.protocol().same_observations(&before.control.protocol());}
            if self.control.control().unchanged(&before.control.control()) {self.control.control().unchanged_observations(&before.control.control());}
            self.record(before,Event::ReleaseProvision {id,port,out});
        }
        out
    }
    pub fn cleanup(&mut self,command:CleanupCommand)->(out:CleanupReply)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::Cleanup {command,error:None,out}),
    {self.cleanup_with_error(command,None)}
    /// Completion diagnostics are actual retained payloads. Failed or stale
    /// replies never detach an admission or alter another episode's status.
    pub fn complete(&mut self,ticket:ActionTicket,error:Option<String>)->(out:CleanupReply)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::Cleanup {
            command:episode::completion(ticket,error.is_none()),error,out}),
    {
        let command=match ticket.kind {
            ActionKind::Setup=>CleanupCommand::SettleSetup {ticket},
            ActionKind::Cleanup=>CleanupCommand::Report {ticket,outcome:if error.is_none() {CleanupOutcome::Succeeded} else {CleanupOutcome::Failed}},
        };
        self.cleanup_with_error(command,error)
    }
    fn cleanup_with_error(&mut self,command:CleanupCommand,error:Option<String>)->(out:CleanupReply)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::Cleanup {command,error,out}),
    {
        let ghost before=self.observation();let ghost saved_error=error;
        proof {self.store.slot_count();self.scopes.unchanged_reflexive();self.control.same_reflexive();self.store.same_reflexive();self.control.same_observations(&self.control);}
        proof {reveal(crate::Kernel::unchanged);reveal(crate::Kernel::binding_recorded);}
        let out=if !self.cleanup_allowed(command) {Err(CleanupError::Control(Error::InvalidState))}
            else {self.control.execute_cleanup(command)};
        if out.is_ok() {
            match command {
                CleanupCommand::Request {id,reservation:true}=>{self.episodes.get_mut(&id).unwrap().prepared_cleanup=true;},
                CleanupCommand::Report {ticket,outcome}=>{
                    if outcome==CleanupOutcome::Failed {
                        let state=self.episodes.get_mut(&ticket.id).unwrap();state.cleanup_failed=true;
                        if error.is_some() {state.failed=error;}
                    }
                },
                CleanupCommand::SettleSetup {ticket}=>{
                    if error.is_some() {self.episodes.get_mut(&ticket.id).unwrap().failed=error;}
                },
                CleanupCommand::Retry {id}=>{self.episodes.get_mut(&id).unwrap().cleanup_failed=false;},
                CleanupCommand::Remove {id}=>{self.episodes.remove(&id);self.restoring.remove(&id);self.interfaces.remove(&id);interfaces::remove_owner(&mut self.dynamic,id);},
                _=>{},
            }
        }
        proof {
            reveal(history::operation);if self.control.same(&before.control) {self.control.same_components(&before.control);}
            if self.store.same(&before.store) {self.store.same_observations(&before.store);}
            if self.control.protocol().same(&before.control.protocol()) {self.control.protocol().same_observations(&before.control.protocol());}
            if self.control.control().unchanged(&before.control.control()) {self.control.control().unchanged_observations(&before.control.control());}
            self.record(before,Event::Cleanup {command,error:saved_error,out});
        }
        out
    }
    pub fn finish(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::Finish {id,out}),
    {
        let ghost before=self.observation();
        proof {self.store.slot_count();self.scopes.unchanged_reflexive();self.control.same_reflexive();self.store.same_reflexive();self.control.same_observations(&self.control);}
        let out=if self.episode_open(id) {self.control.finish(id)} else {Err(Error::InvalidState)};
        proof {
            reveal(history::operation);if self.control.same(&before.control) {self.control.same_components(&before.control);}
            if self.store.same(&before.store) {self.store.same_observations(&before.store);}
            if self.control.protocol().same(&before.control.protocol()) {self.control.protocol().same_observations(&before.control.protocol());}
            if self.control.control().unchanged(&before.control.control()) {self.control.control().unchanged_observations(&before.control.control());}
            self.record(before,Event::Finish {id,out});
        }
        out
    }
    pub fn compact_bindings(&mut self)->(out:usize)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::CompactBindings {out}),
    {
        let ghost before=self.observation();
        proof {self.store.slot_count();self.scopes.unchanged_reflexive();self.control.same_reflexive();self.store.same_reflexive();self.control.same_observations(&self.control);}
        let out=self.control.compact_bindings();
        proof {
            reveal(history::operation);if self.control.same(&before.control) {self.control.same_components(&before.control);}
            if self.store.same(&before.store) {self.store.same_observations(&before.store);}
            if self.control.protocol().same(&before.control.protocol()) {self.control.protocol().same_observations(&before.control.protocol());}
            if self.control.control().unchanged(&before.control.control()) {self.control.control().unchanged_observations(&before.control.control());}
            self.record(before,Event::CompactBindings {out});
        }
        out
    }
    pub fn compact_declarations(&mut self)->(out:usize)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::CompactDeclarations {out}),
    {
        let ghost before=self.observation();
        proof {self.store.slot_count();self.scopes.unchanged_reflexive();self.control.same_reflexive();self.store.same_reflexive();self.control.same_observations(&self.control);}
        let out=self.control.compact_declarations();
        proof {
            reveal(history::operation);if self.control.same(&before.control) {self.control.same_components(&before.control);}
            if self.store.same(&before.store) {self.store.same_observations(&before.store);}
            if self.control.protocol().same(&before.control.protocol()) {self.control.protocol().same_observations(&before.control.protocol());}
            if self.control.control().unchanged(&before.control.control()) {self.control.control().unchanged_observations(&before.control.control());}
            self.record(before,Event::CompactDeclarations {out});
        }
        out
    }
    pub fn publish(&mut self,owner:usize,generation:u64,port:Port,value:u64)->(out:Result<PublicationId,RejectedValue<u64>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::Publish {owner,generation,port,value,out}),
    {
        let ghost before=self.observation();
        proof {self.store.slot_count();self.scopes.unchanged_reflexive();self.control.same_reflexive();self.store.same_reflexive();self.control.same_observations(&self.control);}
        let out=if self.validate(owner,generation).is_ok() {self.store.publish_checked(&self.control,owner,generation,port,value)}
            else {Err(RejectedValue {error:PublicationError::InvalidState,value})};
        proof {
            reveal(history::operation);if self.control.same(&before.control) {self.control.same_components(&before.control);}
            if self.store.same(&before.store) {self.store.same_observations(&before.store);}
            if self.control.protocol().same(&before.control.protocol()) {self.control.protocol().same_observations(&before.control.protocol());}
            if self.control.control().unchanged(&before.control.control()) {self.control.control().unchanged_observations(&before.control.control());}
            self.record(before,Event::Publish {owner,generation,port,value,out});
        }
        out
    }
    pub fn replace(&mut self,id:PublicationId,owner:usize,generation:u64,value:u64)->(out:Result<u64,RejectedValue<u64>>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::Replace {id,owner,generation,value,out}),
    {
        let ghost before=self.observation();
        proof {self.store.slot_count();self.scopes.unchanged_reflexive();self.control.same_reflexive();self.store.same_reflexive();self.control.same_observations(&self.control);}
        let out=if self.validate(owner,generation).is_ok() {self.store.replace_checked(&self.control,id,owner,generation,value)}
            else {Err(RejectedValue {error:PublicationError::InvalidState,value})};
        if let Ok(previous)=out {if previous!=value {self.released.push(previous);}}
        proof {
            reveal(history::operation);if self.control.same(&before.control) {self.control.same_components(&before.control);}
            if self.store.same(&before.store) {self.store.same_observations(&before.store);}
            if self.control.protocol().same(&before.control.protocol()) {self.control.protocol().same_observations(&before.control.protocol());}
            if self.control.control().unchanged(&before.control.control()) {self.control.control().unchanged_observations(&before.control.control());}
            assert(self.released@ =~= before.released+handles::added(Event::Replace {id,owner,generation,value,out}));
            self.record(before,Event::Replace {id,owner,generation,value,out});
        }
        out
    }
    pub fn revoke(&mut self,id:PublicationId)->(out:Result<(),PublicationError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::Revoke {id,restoring:false,out}),
    {self.revoke_with_restoring(id,false)}
    fn revoke_with_restoring(&mut self,id:PublicationId,restoring:bool)->(out:Result<(),PublicationError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::Revoke {id,restoring,out}),
            out.is_ok()==(id.0<old(self).store.values().len()),
            final(self).control==old(self).control,final(self).store.values()==old(self).store.values(),
            final(self).store.revisions()==old(self).store.revisions(),final(self).store.lease_frame(&old(self).store),
            restoring ==> final(self).restoring@==old(self).restoring@,
            out.is_ok() ==> final(self).store.registry_view().publications()==old(self).store.registry_view().publications().update(id.0 as int,
                crate::publication::Publication {visible:false,..old(self).store.registry_view().publications()[id.0 as int]}),
    {
        let ghost before=self.observation();
        proof {self.store.slot_count();self.scopes.unchanged_reflexive();self.control.same_reflexive();self.store.same_reflexive();self.control.same_observations(&self.control);}
        let out=self.store.revoke(id);
        if out.is_ok() && !restoring {self.forget_restoring(id);}
        proof {
            reveal(history::operation);if self.control.same(&before.control) {self.control.same_components(&before.control);}
            if self.store.same(&before.store) {self.store.same_observations(&before.store);}
            if self.control.protocol().same(&before.control.protocol()) {self.control.protocol().same_observations(&before.control.protocol());}
            if self.control.control().unchanged(&before.control.control()) {self.control.control().unchanged_observations(&before.control.control());}
            if out.is_ok() && !restoring {assert(resources::forgotten(before.restoring,self.observation().restoring,before.store.registry_view().publications()[id.0 as int].owner,id));}
            assert(self.observation().wf());assert(resources::step(before,self.observation(),Event::Revoke {id,restoring,out}));
            assert(history::operation(before,self.observation(),Event::Revoke {id,restoring,out}));
            self.record(before,Event::Revoke {id,restoring,out});
        }
        out
    }
    pub fn adopt(&mut self,id:PublicationId,owner:usize,generation:u64)->(out:Result<(),PublicationError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::Adopt {id,owner,generation,out}),
    {
        let ghost before=self.observation();
        proof {self.store.slot_count();self.scopes.unchanged_reflexive();self.control.same_reflexive();self.store.same_reflexive();self.control.same_observations(&self.control);}
        let out=self.store.adopt(id,owner,generation);
        proof {
            reveal(history::operation);if self.control.same(&before.control) {self.control.same_components(&before.control);}
            if self.store.same(&before.store) {self.store.same_observations(&before.store);}
            if self.control.protocol().same(&before.control.protocol()) {self.control.protocol().same_observations(&before.control.protocol());}
            if self.control.control().unchanged(&before.control.control()) {self.control.control().unchanged_observations(&before.control.control());}
            self.record(before,Event::Adopt {id,owner,generation,out});
        }
        out
    }
    pub fn reclaim(&mut self,id:PublicationId)->(out:Result<u64,PublicationError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::Reclaim {id,out}),
    {
        let ghost before=self.observation();
        proof {self.store.slot_count();self.scopes.unchanged_reflexive();self.control.same_reflexive();self.store.same_reflexive();self.control.same_observations(&self.control);}
        let out=self.store.reclaim(id);
        if let Ok(value)=out {self.forget_restoring(id);self.released.push(value);}
        proof {
            reveal(history::operation);if self.control.same(&before.control) {self.control.same_components(&before.control);}
            if self.store.same(&before.store) {self.store.same_observations(&before.store);}
            if self.control.protocol().same(&before.control.protocol()) {self.control.protocol().same_observations(&before.control.protocol());}
            if self.control.control().unchanged(&before.control.control()) {self.control.control().unchanged_observations(&before.control.control());}
            if out.is_ok() {assert(resources::forgotten(before.restoring,self.observation().restoring,before.store.registry_view().publications()[id.0 as int].owner,id));}
            assert(self.observation().wf());assert(resources::step(before,self.observation(),Event::Reclaim {id,out}));
            assert(self.released@ =~= before.released+handles::added(Event::Reclaim {id,out}));
            assert(history::operation(before,self.observation(),Event::Reclaim {id,out}));
            self.record(before,Event::Reclaim {id,out});
        }
        out
    }
    pub fn begin(&mut self,consumer:usize)->(out:Result<ActionTicket,AdmissionError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::Begin {consumer,out}),
            out.is_ok() ==> final(self).observation().admissions.contains_key(consumer) && final(self).observation().admissions[consumer].origin()==out->Ok_0,
    {
        let ghost before=self.observation();
        proof {self.store.slot_count();self.scopes.unchanged_reflexive();self.control.same_reflexive();self.store.same_reflexive();self.control.same_observations(&self.control);}
        let out=if !self.episode_open(consumer) || self.admissions.contains_key(&consumer) {
            Err(AdmissionError::Lifecycle(Error::InvalidState))
        } else {
            match self.checks.begin_setup(&mut self.control,&mut self.store,&self.checked,consumer) {
                Ok(admission)=>{
                    let ticket=admission.ticket();self.admissions.insert(consumer,admission);
                    self.episodes.get_mut(&consumer).unwrap().prepared=false;Ok(ticket)
                },
                Err(error)=>Err(error),
            }
        };
        proof {
            reveal(history::operation);if self.control.same(&before.control) {self.control.same_components(&before.control);}
            if self.store.same(&before.store) {self.store.same_observations(&before.store);}
            if self.control.protocol().same(&before.control.protocol()) {self.control.protocol().same_observations(&before.control.protocol());}
            if self.control.control().unchanged(&before.control.control()) {self.control.control().unchanged_observations(&before.control.control());}
            self.record(before,Event::Begin {consumer,out});
        }
        out
    }
    pub fn release(&mut self,id:usize,publications:&[PublicationId])->(out:Result<Vec<ReleasedValue<u64>>,CleanupReleaseError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::Release {id,publications:publications@,out}),
    {
        let ghost before=self.observation();let ghost saved_publications=publications@;
        proof {self.store.slot_count();self.scopes.unchanged_reflexive();self.control.same_reflexive();self.store.same_reflexive();self.control.same_observations(&self.control);}
        let out=match self.admissions.get(&id) {
            Some(admission)=>admission.finish(&mut self.control,&mut self.store,publications),
            None=>Err(CleanupReleaseError::Lifecycle(Error::InvalidState)),
        };
        if out.is_ok() {
            self.restoring.remove(&id);self.admissions.remove(&id);
            let state=self.episodes.get_mut(&id).unwrap();state.prepared=false;state.prepared_cleanup=false;
            state.restart=false;state.cleanup_failed=false;
        }
        if let Ok(values)=&out {self.queue_released(values.as_slice());}
        proof {
            reveal(history::operation);if self.control.same(&before.control) {self.control.same_components(&before.control);}
            if self.store.same(&before.store) {self.store.same_observations(&before.store);}
            if self.control.protocol().same(&before.control.protocol()) {self.control.protocol().same_observations(&before.control.protocol());}
            if self.control.control().unchanged(&before.control.control()) {self.control.control().unchanged_observations(&before.control.control());}
            self.record(before,Event::Release {id,publications:saved_publications,out});
        }
        out
    }
    pub fn release_reservation(&mut self,id:usize,publications:&[PublicationId])->(out:Result<Vec<ReleasedValue<u64>>,CleanupReleaseError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::ReleaseReservation {id,publications:publications@,out}),
    {
        let ghost before=self.observation();let ghost saved_publications=publications@;
        proof {self.store.slot_count();self.scopes.unchanged_reflexive();self.control.same_reflexive();self.store.same_reflexive();self.control.same_observations(&self.control);}
        let leases:Vec<crate::publication::LeaseId>=Vec::new();
        let allowed=match self.episodes.get(&id) {Some(e)=>e.prepared && e.prepared_cleanup && !self.admissions.contains_key(&id),None=>false};
        let out=if allowed {self.store.finish_resources(&mut self.control,id,true,leases.as_slice(),publications)}
            else {Err(CleanupReleaseError::Lifecycle(Error::InvalidState))};
        if out.is_ok() {
            self.restoring.remove(&id);
            let state=self.episodes.get_mut(&id).unwrap();state.prepared=false;state.prepared_cleanup=false;
            state.restart=false;state.cleanup_failed=false;state.failed=None;
        }
        if let Ok(values)=&out {self.queue_released(values.as_slice());}
        proof {
            reveal(history::operation);if self.control.same(&before.control) {self.control.same_components(&before.control);}
            if self.store.same(&before.store) {self.store.same_observations(&before.store);}
            if self.control.protocol().same(&before.control.protocol()) {self.control.protocol().same_observations(&before.control.protocol());}
            if self.control.control().unchanged(&before.control.control()) {self.control.control().unchanged_observations(&before.control.control());}
            self.record(before,Event::ReleaseReservation {id,publications:saved_publications,out});
        }
        out
    }
    fn episode_open(&self,id:usize)->(out:bool)
        ensures out==episode::open(self.observation(),id),
    {match self.episodes.get(&id) {Some(e)=>e.sealed && e.failed.is_none() && !e.restart && !e.cleanup_failed && !e.prepared_cleanup,None=>false}}
    fn cleanup_allowed(&self,command:CleanupCommand)->(out:bool)
        ensures out==episode::cleanup_allowed(self.observation(),command),
    {
        let id=match command {
            CleanupCommand::Report {ticket,..}|CleanupCommand::SettleSetup {ticket}=>ticket.id,
            CleanupCommand::Request {id,..}|CleanupCommand::Retry {id}|CleanupCommand::Release {id,..}|
            CleanupCommand::Withdraw {id}|CleanupCommand::Retire {id}|CleanupCommand::Remove {id}=>id,
        };
        let e=match self.episodes.get(&id) {Some(e)=>e,None=>return false};
        match command {
            CleanupCommand::Release {..}=>false,
            CleanupCommand::Request {reservation:true,..}=>e.prepared && !e.prepared_cleanup && !self.admissions.contains_key(&id),
            CleanupCommand::Request {reservation:false,..}=>self.admissions.contains_key(&id) && !e.cleanup_failed,
            CleanupCommand::Retry {..}=>e.cleanup_failed,
            CleanupCommand::Remove {..}=>!e.prepared && !e.prepared_cleanup && !self.admissions.contains_key(&id),
            _=>true,
        }
    }
    pub fn episode_command(&mut self,command:EpisodeCommand)->(out:Result<(),EpisodeError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::Episode {command,out}),
    {
        let ghost before=self.observation();let ghost saved=command;
        let out=self.apply_episode_command(command);
        proof {self.store.same_reflexive();reveal(history::operation);self.record(before,Event::Episode {command:saved,out});}
        out
    }
    fn apply_episode_command(&mut self,command:EpisodeCommand)->(out:Result<(),EpisodeError>)
        requires old(self).wf(),
        ensures final(self).observation().wf(),history::operation(old(self).observation(),final(self).observation(),Event::Episode {command,out}),
            final(self).history()==old(self).history(),final(self).control==old(self).control,final(self).store==old(self).store,
    {
        proof {self.scopes.unchanged_reflexive();reveal(history::operation);}
        let id=command.id();
        if !self.episodes.contains_key(&id) || !self.control.kernel().contains(id) {return Err(EpisodeError::Unknown);}
        let phase=self.control.kernel().phase(id);let retired=self.control.kernel().retired(id);
        let generation=self.control.kernel().episode_generation(id);
        match command {
            EpisodeCommand::Prepare {..}=>{
                if retired || phase!=Some(Phase::Inactive) || generation!=Some(0) {return Err(EpisodeError::Closed);}
                self.episodes.get_mut(&id).unwrap().prepared=true;
            },
            EpisodeCommand::Restart {..}=>{
                if retired {return Err(EpisodeError::Retired);}
                let e=self.episodes.get_mut(&id).unwrap();e.failed=None;e.restart=phase!=Some(Phase::Inactive);
            },
            EpisodeCommand::Fail {generation:expected,error,..}=>{
                if generation!=Some(expected) {return Err(EpisodeError::Stale);}
                if retired || (phase!=Some(Phase::Loading) && phase!=Some(Phase::Active)) {return Err(EpisodeError::Closed);}
                let e=self.episodes.get_mut(&id).unwrap();if e.failed.is_none() {e.failed=Some(error);}
            },
            EpisodeCommand::Seal {sealed,..}=>{
                if phase!=Some(Phase::Inactive) || generation!=Some(0) {return Err(EpisodeError::Closed);}
                self.episodes.get_mut(&id).unwrap().sealed=sealed;
            },
            EpisodeCommand::NotifyRetry {..}=>{
                if self.episodes.get(&id).unwrap().cleanup_failed {return Err(EpisodeError::Closed);}
                self.episodes.get_mut(&id).unwrap().failed=None;
            },
        }
        Ok(())
    }
    pub fn request_check(&mut self,consumer:usize,port:Port)->(out:Result<Option<CheckAction>,CheckError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::RequestCheck {consumer,port,out}),
    {
        let ghost before=self.observation();
        proof {self.store.slot_count();self.scopes.unchanged_reflexive();self.control.same_reflexive();self.store.same_reflexive();self.control.same_observations(&self.control);}
        let out=self.checks.request(&self.control,&self.store,consumer,port);
        proof {
            reveal(history::operation);if self.control.same(&before.control) {self.control.same_components(&before.control);}
            if self.store.same(&before.store) {self.store.same_observations(&before.store);}
            if self.control.protocol().same(&before.control.protocol()) {self.control.protocol().same_observations(&before.control.protocol());}
            if self.control.control().unchanged(&before.control.control()) {self.control.control().unchanged_observations(&before.control.control());}
            self.record(before,Event::RequestCheck {consumer,port,out});
        }
        out
    }
    pub fn complete_check(&mut self,ticket:CheckTicket,available:bool)->(out:Result<bool,CheckError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::CompleteCheck {ticket,available,out}),
    {
        let ghost before=self.observation();
        proof {self.store.slot_count();self.scopes.unchanged_reflexive();self.control.same_reflexive();self.store.same_reflexive();self.control.same_observations(&self.control);}
        let out=self.checks.complete(ticket,&self.control,&self.store,available);
        proof {
            reveal(history::operation);if self.control.same(&before.control) {self.control.same_components(&before.control);}
            if self.store.same(&before.store) {self.store.same_observations(&before.store);}
            if self.control.protocol().same(&before.control.protocol()) {self.control.protocol().same_observations(&before.control.protocol());}
            if self.control.control().unchanged(&before.control.control()) {self.control.control().unchanged_observations(&before.control.control());}
            self.record(before,Event::CompleteCheck {ticket,available,out});
        }
        out
    }
    pub fn notify(&mut self,ports:&[Port])->(out:Result<(),CheckError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::Notify {ports:ports@,out}),
    {
        let ghost before=self.observation();let ghost saved_ports=ports@;
        proof {self.store.slot_count();self.scopes.unchanged_reflexive();self.control.same_reflexive();self.store.same_reflexive();self.control.same_observations(&self.control);}
        let out=self.checks.notify(ports);
        if out.is_ok() && self.policy.profile==Profile::Harness {
            let ghost notified=self.observation();
            proof {assert(policy::retry_set(notified,ports@) =~= policy::retry_set(before,ports@));}
            self.retry_notified(ports);
        }
        proof {
            reveal(history::operation);if self.control.same(&before.control) {self.control.same_components(&before.control);}
            if self.store.same(&before.store) {self.store.same_observations(&before.store);}
            if self.control.protocol().same(&before.control.protocol()) {self.control.protocol().same_observations(&before.control.protocol());}
            if self.control.control().unchanged(&before.control.control()) {self.control.control().unchanged_observations(&before.control.control());}
            self.record(before,Event::Notify {ports:saved_ports,out});
        }
        out
    }
    pub fn forget_checks(&mut self,consumer:usize)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::ForgetChecks {consumer}),
    {
        let ghost before=self.observation();
        proof {self.store.slot_count();self.scopes.unchanged_reflexive();self.control.same_reflexive();self.store.same_reflexive();self.control.same_observations(&self.control);}
        self.checks.remove_consumer(consumer);
        proof {
            reveal(history::operation);if self.control.same(&before.control) {self.control.same_components(&before.control);}
            if self.store.same(&before.store) {self.store.same_observations(&before.store);}
            if self.control.protocol().same(&before.control.protocol()) {self.control.protocol().same_observations(&before.control.protocol());}
            if self.control.control().unchanged(&before.control.control()) {self.control.control().unchanged_observations(&before.control.control());}
            self.record(before,Event::ForgetChecks {consumer});
        }
    }
    pub fn set_checked(&mut self,publication:usize,enabled:bool)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).history()==old(self).history().append(final(self).observation(),Event::Checked {publication,enabled}),
    {
        let ghost before=self.observation();
        proof {self.store.slot_count();self.scopes.unchanged_reflexive();self.control.same_reflexive();self.store.same_reflexive();self.control.same_observations(&self.control);}
        if enabled {self.checked.insert(publication);} else {self.checked.remove(&publication);};
        proof {
            reveal(history::operation);if self.control.same(&before.control) {self.control.same_components(&before.control);}
            if self.store.same(&before.store) {self.store.same_observations(&before.store);}
            if self.control.protocol().same(&before.control.protocol()) {self.control.protocol().same_observations(&before.control.protocol());}
            if self.control.control().unchanged(&before.control.control()) {self.control.control().unchanged_observations(&before.control.control());}
            self.record(before,Event::Checked {publication,enabled});
        }
    }
}
}
