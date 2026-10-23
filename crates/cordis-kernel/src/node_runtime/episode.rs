//! Actual Node episode ownership and host status, in the protocol owner's history.
//! Error strings are retained values; callback truth remains a host input.
#[cfg(verus_keep_ghost)]
use super::history::Event;
use super::history::Observation;
use super::*;
verus! {
pub struct Episode {
    pub sealed:bool,pub prepared:bool,pub prepared_cleanup:bool,pub failed:Option<String>,
    pub cleanup_failed:bool,pub restart:bool,
}
impl Episode {
    pub open spec fn initial()->Self {Self {sealed:true,prepared:false,prepared_cleanup:false,failed:None,cleanup_failed:false,restart:false}}
    pub(super) fn new()->(out:Self) ensures out==Self::initial(),
    {Self {sealed:true,prepared:false,prepared_cleanup:false,failed:None,cleanup_failed:false,restart:false}}
}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum EpisodeError {Unknown,Retired,Stale,Closed}
#[allow(inconsistent_fields)]
pub enum Command {Prepare {id:usize},Restart {id:usize},Fail {id:usize,generation:u64,error:String},Seal {id:usize,sealed:bool},NotifyRetry {id:usize}}
impl Command {
    pub open spec fn owner(&self)->usize {match self {Self::Prepare {id}|Self::Restart {id}|Self::Fail {id,..}|Self::Seal {id,..}|Self::NotifyRetry {id}=>*id}}
    pub fn id(&self)->(out:usize) ensures out==self.owner(),
    {match self {Self::Prepare {id}|Self::Restart {id}|Self::Fail {id,..}|Self::Seal {id,..}|Self::NotifyRetry {id}=>*id}}
}
pub open spec fn completion(ticket:ActionTicket,success:bool)->CleanupCommand {
    match ticket.kind {ActionKind::Setup=>CleanupCommand::SettleSetup {ticket},ActionKind::Cleanup=>CleanupCommand::Report {
        ticket,outcome:if success {CleanupOutcome::Succeeded} else {CleanupOutcome::Failed}}}
}
pub open spec fn validation(a:Observation,id:usize,generation:u64)->Result<(),EpisodeError> {
    let k=a.control.control();
    if k.generation_of(id)!=Some(generation) {Err(EpisodeError::Stale)}
    else if generation==0 && !k.is_retired(id) && k.phase_of(id)==Some(Phase::Inactive) && a.episodes.contains_key(id) && a.episodes[id].prepared {Ok(())}
    else if k.is_retired(id) || (k.phase_of(id)!=Some(Phase::Loading) && k.phase_of(id)!=Some(Phase::Active)) {Err(EpisodeError::Closed)} else {Ok(())}
}
pub open spec fn open(a:Observation,id:usize)->bool {
    a.episodes.contains_key(id) && a.episodes[id].sealed && a.episodes[id].failed.is_none()
        && !a.episodes[id].restart && !a.episodes[id].cleanup_failed && !a.episodes[id].prepared_cleanup
}
pub open spec fn cleanup_owner(command:CleanupCommand)->usize {
    match command {CleanupCommand::Report {ticket,..}|CleanupCommand::SettleSetup {ticket}=>ticket.id,
        CleanupCommand::Request {id,..}|CleanupCommand::Retry {id}|CleanupCommand::Release {id,..}|
        CleanupCommand::Withdraw {id}|CleanupCommand::Retire {id}|CleanupCommand::Remove {id}=>id}
}
pub open spec fn cleanup_allowed(a:Observation,command:CleanupCommand)->bool {
    let id=cleanup_owner(command);
    a.episodes.contains_key(id) && match command {
        CleanupCommand::Release {..}=>false,
        CleanupCommand::Request {reservation:true,..}=>a.episodes[id].prepared && !a.episodes[id].prepared_cleanup && !a.admissions.contains_key(id),
        CleanupCommand::Request {reservation:false,..}=>a.admissions.contains_key(id) && !a.episodes[id].cleanup_failed,
        CleanupCommand::Retry {..}=>a.episodes[id].cleanup_failed,
        CleanupCommand::Remove {..}=>!a.episodes[id].prepared && !a.episodes[id].prepared_cleanup && !a.admissions.contains_key(id),
        _=>true,
    }
}
pub open spec fn command_result(a:Observation,command:Command)->Result<(),EpisodeError> {
    let id=command.owner();let k=a.control.control();
    if !a.episodes.contains_key(id) || !k.registered(id) {Err(EpisodeError::Unknown)} else {
        match command {
            Command::Prepare {..}=>if k.is_retired(id) || k.phase_of(id)!=Some(Phase::Inactive) || k.generation_of(id)!=Some(0) {Err(EpisodeError::Closed)} else {Ok(())},
            Command::Restart {..}=>if k.is_retired(id) {Err(EpisodeError::Retired)} else {Ok(())},
            Command::Fail {generation,..}=>if k.generation_of(id)!=Some(generation) {Err(EpisodeError::Stale)}
                else if k.is_retired(id) || (k.phase_of(id)!=Some(Phase::Loading) && k.phase_of(id)!=Some(Phase::Active)) {Err(EpisodeError::Closed)} else {Ok(())},
            Command::Seal {..}=>if k.phase_of(id)!=Some(Phase::Inactive) || k.generation_of(id)!=Some(0) {Err(EpisodeError::Closed)} else {Ok(())},
            Command::NotifyRetry {..}=>if a.episodes[id].cleanup_failed {Err(EpisodeError::Closed)} else {Ok(())},
        }
    }
}
pub open spec fn command_state(a:Observation,command:Command)->Episode {
    let id=command.owner();let e=a.episodes[id];
    match command {
        Command::Prepare {..}=>Episode {prepared:true,..e},
        Command::Restart {..}=>Episode {failed:None,restart:a.control.control().phase_of(id)!=Some(Phase::Inactive),..e},
        Command::Fail {error,..}=>Episode {failed:if e.failed.is_some() {e.failed} else {Some(error)},..e},
        Command::Seal {sealed,..}=>Episode {sealed,..e},Command::NotifyRetry {..}=>Episode {failed:None,..e},
    }
}
pub open spec fn after_cleanup(a:Observation,command:CleanupCommand,error:Option<String>)->Map<usize,Episode> {
    let id=cleanup_owner(command);let e=a.episodes[id];
    match command {
        CleanupCommand::Request {reservation:true,..}=>a.episodes.insert(id,Episode {prepared_cleanup:true,..e}),
        CleanupCommand::Report {outcome:CleanupOutcome::Failed,..}=>a.episodes.insert(id,Episode {cleanup_failed:true,failed:if error.is_some() {error} else {e.failed},..e}),
        CleanupCommand::SettleSetup {..} if error.is_some()=>a.episodes.insert(id,Episode {failed:error,..e}),
        CleanupCommand::Retry {..}=>a.episodes.insert(id,Episode {cleanup_failed:false,..e}),
        CleanupCommand::Remove {..}=>a.episodes.remove(id),_=>a.episodes,
    }
}
pub open spec fn reservation(a:Observation,id:usize)->bool {
    a.episodes.contains_key(id) && a.episodes[id].prepared && a.episodes[id].prepared_cleanup && !a.admissions.contains_key(id)
}
pub open spec fn released(e:Episode,reservation:bool)->Episode {
    Episode {prepared:false,prepared_cleanup:false,cleanup_failed:false,restart:false,failed:if reservation {None} else {e.failed},..e}
}
/// Every operation has an exact frame for the real admission/status maps.
pub open spec fn step(a:Observation,b:Observation,event:Event)->bool {
    match event {
        Event::Insert {out,..}=>b.admissions==a.admissions && b.episodes==if out.is_ok() {a.episodes.insert(out->Ok_0,Episode::initial())} else {a.episodes},
        Event::Begin {consumer,out}=>if out.is_ok() {
            !a.admissions.contains_key(consumer) && open(a,consumer) && b.admissions.contains_key(consumer)
                && b.admissions==a.admissions.insert(consumer,b.admissions[consumer]) && b.admissions[consumer].origin()==out->Ok_0
                && b.episodes==a.episodes.insert(consumer,Episode {prepared:false,..a.episodes[consumer]})
        } else {b.admissions==a.admissions && b.episodes==a.episodes},
        Event::Release {id,out,..}=>if out.is_ok() {
            a.admissions.contains_key(id) && b.admissions==a.admissions.remove(id) && b.episodes==a.episodes.insert(id,released(a.episodes[id],false))
        } else {b.admissions==a.admissions && b.episodes==a.episodes},
        Event::ReleaseReservation {id,out,..}=>b.admissions==a.admissions && b.episodes==if out.is_ok() {a.episodes.insert(id,released(a.episodes[id],true))} else {a.episodes},
        Event::Cleanup {command,error,out}=>b.admissions==a.admissions && (out.is_ok() ==> cleanup_allowed(a,command))
            && b.episodes==if out.is_ok() {after_cleanup(a,command,error)} else {a.episodes},
        Event::Notify {ports,out}=>b.admissions==a.admissions && b.episodes==
            if out.is_ok() && a.policy.profile==Profile::Harness {policy::cleared(a.episodes,policy::retry_set(a,ports))} else {a.episodes},
        Event::Episode {command,out}=>out==command_result(a,command) && b.admissions==a.admissions
            && b.episodes==if out.is_ok() {a.episodes.insert(command.owner(),command_state(a,command))} else {a.episodes},
        _=>b.admissions==a.admissions && b.episodes==a.episodes,
    }
}
/// Only the actual status map changes. Keeping its local transition separate
/// from the full protocol history avoids unfolding every protocol in each branch.
pub(super) fn apply(episodes:&mut BTreeMap<usize,Episode>,control:&LifecycleState,command:Command,Ghost(before):Ghost<Observation>)->(out:Result<(),EpisodeError>)
    requires control.wf(),*control==before.control,old(episodes)@==before.episodes,
    ensures out==command_result(before,command),
        final(episodes)@==if out.is_ok() {before.episodes.insert(command.owner(),command_state(before,command))} else {before.episodes},
    {
        let id=command.id();
        if !episodes.contains_key(&id) || !control.kernel().contains(id) {return Err(EpisodeError::Unknown);}
        let phase=control.kernel().phase(id);let retired=control.kernel().retired(id);
        let generation=control.kernel().episode_generation(id);
        match command {
            Command::Prepare {..}=>{
                if retired || phase!=Some(Phase::Inactive) || generation!=Some(0) {return Err(EpisodeError::Closed);}
                episodes.get_mut(&id).unwrap().prepared=true;
            },
            Command::Restart {..}=>{
                if retired {return Err(EpisodeError::Retired);}
                let e=episodes.get_mut(&id).unwrap();e.failed=None;e.restart=phase!=Some(Phase::Inactive);
            },
            Command::Fail {generation:expected,error,..}=>{
                if generation!=Some(expected) {return Err(EpisodeError::Stale);}
                if retired || (phase!=Some(Phase::Loading) && phase!=Some(Phase::Active)) {return Err(EpisodeError::Closed);}
                let e=episodes.get_mut(&id).unwrap();if e.failed.is_none() {e.failed=Some(error);}
            },
            Command::Seal {sealed,..}=>{
                if phase!=Some(Phase::Inactive) || generation!=Some(0) {return Err(EpisodeError::Closed);}
                episodes.get_mut(&id).unwrap().sealed=sealed;
            },
            Command::NotifyRetry {..}=>{
                if episodes.get(&id).unwrap().cleanup_failed {return Err(EpisodeError::Closed);}
                episodes.get_mut(&id).unwrap().failed=None;
            },
        }
        Ok(())
    }

}
