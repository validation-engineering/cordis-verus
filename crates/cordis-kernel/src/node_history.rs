//! Continuous execution history of the production Node protocol owner.
//! Opaque numbers name JS objects; this does not interpret their interiors or
//! claim that callback predicates, I/O, or JavaScript scheduling are verified.
use super::*;
#[cfg(verus_keep_ghost)]
use crate::availability::Record;
#[cfg(verus_keep_ghost)]
use crate::publication::{LeaseOwner, Publication};
#[cfg(verus_keep_ghost)]
use crate::refinement as r;

verus! {
pub struct Observation {
    pub policy:Policy,pub control:LifecycleState,pub store:PublicationStore<u64>,
    pub checks:Availability,pub checked:Set<usize>,
    pub admissions:Map<usize,Admission>,pub episodes:Map<usize,Episode>,pub scopes:InvocationLedger,pub restoring:Map<usize,Vec<PublicationId>>,pub released:Seq<u64>,
    pub interfaces:Map<usize,Interface>,pub dynamic:Map<(u64,u64),usize>,
}
impl Observation {
    pub open spec fn wf(&self)->bool {
        self.control.wf() && self.store.wf() && self.checks.wf() && self.scopes.wf()
            && self.scopes.domain_id()==self.control.protocol().domain_id()
            && self.store.registry_view().domain_id()==Some(self.control.protocol().domain_id())
            && self.checks.domain_id()==self.control.protocol().domain_id()
            && (forall|id:usize|self.admissions.contains_key(id) ==> self.admissions[id].wf()
                && self.admissions[id].origin().id==id && self.admissions[id].origin().domain==self.control.protocol().domain_id()
                && self.episodes.contains_key(id))
    }
    pub open spec fn same(&self,a:Self)->bool {
        self.policy==a.policy && self.control.same(&a.control) && self.store.same(&a.store) && self.checks==a.checks && self.checked==a.checked && self.admissions==a.admissions && self.episodes==a.episodes && self.scopes.unchanged(&a.scopes) && self.restoring==a.restoring && self.released==a.released && self.interfaces==a.interfaces && self.dynamic==a.dynamic
    }
}
pub open spec fn control_frame(a:Observation,b:Observation)->bool {
    b.store.same(&a.store) && b.checks==a.checks && b.checked==a.checked
}
pub open spec fn store_frame(a:Observation,b:Observation)->bool {
    b.control==a.control && b.checks==a.checks && b.checked==a.checked
}
pub open spec fn check_frame(a:Observation,b:Observation)->bool {
    b.control==a.control && b.store==a.store && b.checked==a.checked
}
pub open spec fn versions_advance(a:Observation,b:Observation)->bool {
    a.store.revisions().len()<=b.store.revisions().len()
        && forall|i:int|0<=i<a.store.revisions().len() ==> a.store.revisions()[i]<=b.store.revisions()[i]
}
#[allow(inconsistent_fields)]
pub enum Event {
    Configure {profile:Profile,out:Result<(),PolicyError>},
    Gate {gate:policy::Gate,out:Result<bool,PolicyError>},
    Insert {parent:Option<usize>,dependencies:Seq<Port>,provisions:Seq<Port>,out:Result<usize,Error>},
    Declare {id:usize,port:Port,out:Result<(),Error>},
    Dependencies {id:usize,dependencies:Seq<Port>,out:Result<(),Error>},
    ReleaseProvision {id:usize,port:Port,out:Result<(),Error>},
    Cleanup {command:CleanupCommand,error:Option<String>,out:CleanupReply},
    Finish {id:usize,out:Result<(),Error>},
    CompactBindings {out:usize},
    CompactDeclarations {out:usize},
    Publish {owner:usize,generation:u64,port:Port,value:u64,out:Result<PublicationId,RejectedValue<u64>>},
    Replace {id:PublicationId,owner:usize,generation:u64,value:u64,out:Result<u64,RejectedValue<u64>>},
    Revoke {id:PublicationId,restoring:bool,out:Result<(),PublicationError>},
    Adopt {id:PublicationId,owner:usize,generation:u64,out:Result<(),PublicationError>},
    Reclaim {id:PublicationId,out:Result<u64,PublicationError>},
    Begin {consumer:usize,out:Result<ActionTicket,AdmissionError>},
    Release {id:usize,publications:Seq<PublicationId>,out:Result<Vec<ReleasedValue<u64>>,CleanupReleaseError>},
    ReleaseReservation {id:usize,publications:Seq<PublicationId>,out:Result<Vec<ReleasedValue<u64>>,CleanupReleaseError>},
    RequestCheck {consumer:usize,port:Port,out:Result<Option<CheckAction>,CheckError>},
    CompleteCheck {ticket:CheckTicket,available:bool,out:Result<bool,CheckError>},
    Notify {ports:Seq<Port>,out:Result<(),CheckError>},
    ForgetChecks {consumer:usize},
    Checked {publication:usize,enabled:bool},
    Episode {command:EpisodeCommand,out:Result<(),EpisodeError>},
    Read {port:Port,consumer:Option<usize>,generation:Option<u64>,out:Result<Option<reads::Read>,reads::ReadError>},
    DrainReleased {out:Seq<u64>},
    RememberPublications {owner:usize,publications:Seq<PublicationId>},
    BeginScope {id:usize,generation:u64,out:Result<ScopeHandle,ScopeError>},
    FinishScope {handle:ScopeHandle,out:Result<(),ScopeError>},
    ScopesLive {handles:Seq<ScopeHandle>,out:Result<bool,ScopeError>},
    ScopeWait {handles:Seq<ScopeHandle>,target:usize,out:Result<Option<ScopeBlock>,ScopeError>},
}
#[verifier::opaque]
pub open spec fn operation(a:Observation,b:Observation,event:Event)->bool {
    policy::step(a,b,event) && interfaces::step(a,b,event) && episode::step(a,b,event) && scopes::step(a,b,event) && resources::step(a,b,event) && handles::step(a,b,event) && match event {
        Event::Insert {parent,dependencies,provisions,out}=>control_frame(a,b) && b.control.control_history().extends(a.control.control_history())
        && b.control.protocol().same(&a.control.protocol())
        && out.is_ok()==a.control.control().insert_enabled(parent,dependencies,provisions)
        && (out.is_err() ==> b.control.same(&a.control))
        && (out.is_ok() ==> out->Ok_0==a.control.control().next_id()
            && r::step(a.control.control().paper(),b.control.control().paper(),out->Ok_0,r::Rule::Insert)
            && b.control.control().paper().fibers[out->Ok_0].parent==parent
            && (forall|p:Port|b.control.control().paper().fibers[out->Ok_0].dependencies.contains(p)==dependencies.contains(p))
            && (forall|p:Port|b.control.control().paper().fibers[out->Ok_0].provisions.contains(p)==provisions.contains(p))),
        Event::Declare {id,port,out}=>b.control.control_history().labels.last()==(if out.is_ok() {crate::lifecycle_state::history::Label::Declare {actor:id,port}} else {crate::lifecycle_state::history::Label::Internal}) && control_frame(a,b) && b.control.control_history().extends(a.control.control_history())
        && b.control.protocol().same(&a.control.protocol()) && b.control.control().same_control(&a.control.control()) && b.control.control().same_bindings(&a.control.control())
        && (out.is_err() ==> b.control.same(&a.control)) && (out.is_ok() ==> b.control.control().declares_provision(id,port)),
        Event::Dependencies {id,dependencies,out}=>b.control.control_history().labels.last()==(if out.is_ok() {crate::lifecycle_state::history::Label::Dependencies {actor:id,ports:dependencies.to_set().to_iset()}} else {crate::lifecycle_state::history::Label::Internal}) && control_frame(a,b) && b.control.control_history().extends(a.control.control_history())
        && b.control.protocol().same(&a.control.protocol()) && b.control.control().same_control(&a.control.control()) && b.control.control().same_bindings(&a.control.control())
        && (out.is_err() ==> b.control.same(&a.control)) && (out.is_ok() ==> b.control.control().pending_dependencies_configured(&a.control.control(),id,dependencies)),
        Event::ReleaseProvision {id,port,out}=>b.control.control_history().labels.last()==(if out.is_ok() {crate::lifecycle_state::history::Label::Release {actor:id,port}} else {crate::lifecycle_state::history::Label::Internal}) && control_frame(a,b) && b.control.control_history().extends(a.control.control_history())
        && b.control.protocol().same(&a.control.protocol()) && b.control.control().same_control(&a.control.control()) && b.control.control().same_bindings(&a.control.control())
        && (out.is_err() ==> b.control.same(&a.control)) && (out.is_ok() ==> b.control.control().provision_released_from(&a.control.control(),id,port) && !b.control.control().declares_provision(id,port) && b.control.control().other_interfaces_preserved(&a.control.control(),id,port)),
        Event::Cleanup {command,error:_,out}=>control_frame(a,b) && b.control.cleanup_step(&a.control,command,out)
        && (command is Release ==> out==Err(CleanupError::Control(Error::InvalidState))),
        Event::Finish {id,out}=>control_frame(a,b) && (episode::open(a,id) ==> b.control.control_history().extends(a.control.control_history()))
        && b.control.protocol().same(&a.control.protocol())
        && out.is_ok()==(episode::open(a,id) && !a.control.protocol().blocked_spec(id) && a.control.control().iteration_enabled(id))
        && (out.is_err() ==> b.control.same(&a.control))
        && (out.is_ok() ==> r::step(a.control.control().paper(),b.control.control().paper(),id,r::Rule::Finish)),
        Event::CompactBindings {out}=>control_frame(a,b) && b.control.control_history().extends(a.control.control_history())
        && b.control.protocol().same(&a.control.protocol()) && b.control.control().paper()==a.control.control().paper(),
        Event::CompactDeclarations {out}=>control_frame(a,b) && b.control.control_history().extends(a.control.control_history())
        && b.control.protocol().same(&a.control.protocol()) && b.control.control().paper()==a.control.control().paper(),
        Event::Publish {owner,generation,port,value,out}=>store_frame(a,b) && b.store.lease_frame(&a.store) && (out.is_err() ==> b.store.same(&a.store) && out->Err_0.value==value)
        && (out.is_ok() ==> episode::validation(a,owner,generation).is_ok() && a.control.service_open(owner,generation)
            && a.store.registry_view().domain_id()==Some(a.control.protocol().domain_id())
            && a.store.lookup(port).is_none()
            && b.store.visible_table()==crate::coeffects::put(a.store.visible_table(),port,Some(value))
            && out->Ok_0.0==a.store.values().len() && b.store.values()==a.store.values().push(Some(value))
            && b.store.revisions()==a.store.revisions().push(0)
            && b.store.registry_view().publications()==a.store.registry_view().publications().push(
                Publication {owner,generation,port,slot:out->Ok_0.0,visible:true,retained:true})),
        Event::Replace {id,owner,generation,value,out}=>store_frame(a,b) && b.store.registry_view().unchanged(&a.store.registry_view())
        && (out.is_err() ==> b.store.same(&a.store) && out->Err_0.value==value)
        && (out.is_ok() ==> episode::validation(a,owner,generation).is_ok() && a.control.service_open(owner,generation)
            && a.store.registry_view().domain_id()==Some(a.control.protocol().domain_id())
            && id.0<a.store.values().len() && a.store.values()[id.0 as int]==Some(out->Ok_0)
            && a.store.registry_view().publications()[id.0 as int].visible
            && a.store.registry_view().publications()[id.0 as int].owner==owner
            && a.store.registry_view().publications()[id.0 as int].generation==generation
            && b.store.values()==a.store.values().update(id.0 as int,Some(value))
            && a.store.revisions()[id.0 as int]<u64::MAX
            && b.store.revisions()==a.store.revisions().update(id.0 as int,(a.store.revisions()[id.0 as int]+1) as u64)
            && b.store.visible_table()==crate::coeffects::put(a.store.visible_table(),a.store.registry_view().publications()[id.0 as int].port,Some(value))),
        Event::Revoke {id,out,..}=>out.is_ok()==(id.0<a.store.values().len()) && store_frame(a,b) && b.store.lease_frame(&a.store) && b.store.values()==a.store.values() && b.store.revisions()==a.store.revisions()
        && (out.is_err() ==> b.store.same(&a.store))
        && (out.is_ok() ==> id.0<a.store.values().len()
            && b.store.registry_view().publications()==a.store.registry_view().publications().update(id.0 as int,
                Publication {visible:false,..a.store.registry_view().publications()[id.0 as int]})
            && b.store.visible_table()==
            if a.store.registry_view().publications()[id.0 as int].visible {
                a.store.visible_table().remove(a.store.registry_view().publications()[id.0 as int].port)
            } else {a.store.visible_table()}),
        Event::Adopt {id,owner,generation,out}=>store_frame(a,b) && b.store.lease_frame(&a.store) && b.store.values()==a.store.values() && b.store.revisions()==a.store.revisions()
        && b.store.visible_table()==a.store.visible_table()
        && (out.is_err() ==> b.store.same(&a.store))
        && (out.is_ok() ==> id.0<a.store.values().len() && a.store.registry_view().publications()[id.0 as int].owner==owner
            && a.store.registry_view().publications()[id.0 as int].generation==0 && generation==1 && a.store.registry_view().unleased(id)
            && b.store.registry_view().publications()==a.store.registry_view().publications().update(id.0 as int,
                Publication {generation,..a.store.registry_view().publications()[id.0 as int]})),
        Event::Reclaim {id,out}=>store_frame(a,b) && b.store.lease_frame(&a.store) && b.store.visible_table()==a.store.visible_table() && b.store.revisions()==a.store.revisions()
        && (out.is_err() ==> b.store.same(&a.store))
        && (out.is_ok() ==> id.0<a.store.values().len() && a.store.values()[id.0 as int]==Some(out->Ok_0)
            && b.store.values()==a.store.values().update(id.0 as int,None)
            && b.store.registry_view().publications()==a.store.registry_view().publications().update(id.0 as int,
                Publication {retained:false,..a.store.registry_view().publications()[id.0 as int]}) && a.store.registry_view().unleased(id)
            && !a.store.registry_view().publications()[id.0 as int].visible),
        Event::Begin {consumer,out}=>b.checks==a.checks && b.checked==a.checked && b.store.values()==a.store.values() && b.store.revisions()==a.store.revisions()
        && b.store.registry_view().domain_id()==a.store.registry_view().domain_id()
        && b.store.registry_view().publications()==a.store.registry_view().publications()
        && out.is_ok()==(episode::open(a,consumer) && !a.admissions.contains_key(consumer) && a.checks.ready_spec(&a.control,&a.store,a.checked,consumer)
            && a.store.registry_view().lease_allocations()+a.control.control().target_count(consumer)<=usize::MAX
            && a.control.protocol().admission_enabled(consumer) && a.control.control().begin_enabled(consumer))
        && (out.is_err() ==> b.control.same(&a.control) && b.store.same(&a.store))
        && (out.is_ok() ==> {
            let admitted=b.admissions[consumer];let s=admitted.source();
            &&& admitted.wf() && s.control==a.control && s.store==a.store && s.checks==a.checks && s.checked==a.checked
            &&& admitted.origin().id==consumer && b.control.protocol().recorded(admitted.origin())
            &&& b.control.control().generation_of(consumer)==Some(admitted.origin().generation)
            &&& r::step(a.control.control().paper(),b.control.control().paper(),consumer,r::Rule::Begin)
            &&& crate::episode::binding_set(s.bindings)==b.control.control().paper().fibers[consumer].committed
            &&& b.store.registry_view().lease_records()==a.store.registry_view().lease_records()+admitted.leases()
            &&& b.store.registry_view().lease_allocations()==a.store.registry_view().lease_allocations()+admitted.resources_view().len()
            &&& forall|i:int|0<=i<admitted.resources_view().len() ==>
                b.store.registry_view().active_lease(admitted.resources_view()[i].lease)==Some(admitted.lease_record(i).lease)
        }),
        Event::Release {id,publications,out}=>{let admission=a.admissions[id];(out.is_ok() ==> b.store.released(&a.store,admission.lease_ids(),publications)) && b.checks==a.checks && b.checked==a.checked && b.store.revisions()==a.store.revisions()
        && b.store.visible_table()==a.store.visible_table()
        && out.is_ok()==(a.admissions.contains_key(id) && a.control.protocol().domain_id()==admission.origin().domain
            && a.control.control().generation_of(admission.origin().id)==Some(admission.origin().generation)
            && a.store.registry_view().domain_id()==Some(admission.origin().domain)
            && a.control.protocol().resource_finish_enabled(&a.control.control(),admission.origin().id,false)
            && a.store.registry_view().cleanup_batch_enabled(LeaseOwner {owner:admission.origin().id,generation:admission.origin().generation},admission.lease_ids(),publications))
        && (out.is_err() ==> b.store.same(&a.store) && b.control.control().unchanged(&a.control.control()) && b.control.protocol().same(&a.control.protocol()))
        && (out.is_ok() ==> b.store.registry_view().episode_resources_cleared(LeaseOwner {owner:admission.origin().id,generation:admission.origin().generation})
            && r::step(a.control.control().paper(),b.control.control().paper(),admission.origin().id,r::Rule::Unload)
            && out->Ok_0.len()==publications.len()
            && (forall|i:int|0<=i<publications.len() ==> out->Ok_0[i].publication==publications[i]
                && publications[i].0<a.store.values().len() && a.store.values()[publications[i].0 as int]==Some(out->Ok_0[i].value)))},
        Event::ReleaseReservation {id,publications,out}=>b.control.control().paper()==a.control.control().paper() && (out.is_ok() ==> b.store.released(&a.store,Seq::empty(),publications)) && b.checks==a.checks && b.checked==a.checked && b.store.revisions()==a.store.revisions()
        && b.store.visible_table()==a.store.visible_table()
        && out.is_ok()==(episode::reservation(a,id) && a.store.registry_view().domain_id()==Some(a.control.protocol().domain_id())
            && a.control.protocol().resource_finish_enabled(&a.control.control(),id,true)
            && a.store.registry_view().cleanup_batch_enabled(LeaseOwner {owner:id,generation:a.control.control().generation_of(id).unwrap()},Seq::empty(),publications))
        && (out.is_err() ==> b.store.same(&a.store) && b.control.control().unchanged(&a.control.control()) && b.control.protocol().same(&a.control.protocol()))
        && (out.is_ok() ==> !b.control.protocol().blocked_spec(id)
            && b.store.registry_view().episode_resources_cleared(LeaseOwner {owner:id,generation:a.control.control().generation_of(id).unwrap()})
            && out->Ok_0.len()==publications.len()
            && (forall|i:int|0<=i<publications.len() ==> out->Ok_0[i].publication==publications[i]
                && publications[i].0<a.store.values().len() && a.store.values()[publications[i].0 as int]==Some(out->Ok_0[i].value))),
        Event::RequestCheck {consumer,port,out}=>check_frame(a,b) && b.checks.domain_id()==a.checks.domain_id() && b.checks.notified()==a.checks.notified()
        && ((out.is_err() || out==Ok(None)) ==> b.checks==a.checks)
        && (out.is_ok() && out->Ok_0.is_some() ==> {
            let issued=out->Ok_0.unwrap();let t=issued.ticket;
            &&& t.consumer==consumer && t.port==port && t.domain==a.checks.domain_id()
            &&& t.action==a.checks.allocated() && b.checks.allocated()==a.checks.allocated()+1
            &&& b.checks.outstanding()==a.checks.outstanding().insert(t.action,issued)
            &&& b.checks.fresh(t,&a.control,&a.store)
            &&& a.store.values()[t.publication.0 as int]==Some(issued.value)
            &&& t.publication.0<a.store.revisions().len() && a.store.revisions()[t.publication.0 as int]==t.value_revision
            &&& b.checks.rows()==a.checks.rows().insert(t.key(),a.checks.requested_row(t.key(),t.publication))
        }),
        Event::CompleteCheck {ticket,available,out}=>check_frame(a,b) && b.checks.domain_id()==a.checks.domain_id() && b.checks.allocated()==a.checks.allocated() && b.checks.notified()==a.checks.notified()
        && out.is_ok()==a.checks.recorded(ticket)
        && (out.is_err() ==> b.checks==a.checks && out==Err(CheckError::Stale))
        && (out.is_ok() ==> out->Ok_0==a.checks.fresh(ticket,&a.control,&a.store)
            && b.checks.outstanding()==a.checks.outstanding().remove(ticket.action)
            && b.checks.rows()==if a.checks.completion_row(ticket) {
                a.checks.rows().insert(ticket.key(),Record {available:out->Ok_0 && available,last_current:Some(out->Ok_0),..a.checks.rows()[ticket.key()]})
            } else {a.checks.rows()}),
        Event::Notify {ports,out}=>check_frame(a,b) && b.checks.domain_id()==a.checks.domain_id() && b.checks.allocated()==a.checks.allocated() && b.checks.outstanding()==a.checks.outstanding()
        && out.is_ok()==(a.checks.notified()<u64::MAX) && (out.is_err() ==> b.checks==a.checks)
        && (out.is_ok() ==> b.checks.notified()==a.checks.notified()+1 && b.checks.rows().dom()==a.checks.rows().dom()
            && (forall|key:crate::availability::Key|a.checks.rows().contains_key(key) ==> b.checks.rows()[key]==if ports.contains(Port {key:key.1,realm:key.2}) {
                Record {notification:b.checks.notified(),dirty:true,..a.checks.rows()[key]}
            } else {a.checks.rows()[key]})),
        Event::ForgetChecks {consumer}=>check_frame(a,b) && b.checks.domain_id()==a.checks.domain_id() && b.checks.allocated()==a.checks.allocated() && b.checks.notified()==a.checks.notified() && b.checks.outstanding()==a.checks.outstanding()
        && b.checks.rows()==a.checks.rows().restrict(a.checks.rows().dom().filter(|key:crate::availability::Key|key.0!=consumer)),
        Event::Read {port,consumer,generation,out}=>b==a && out==reads::result(a,port,consumer,generation)
            && (out.is_ok() && out->Ok_0.is_some() ==> reads::valid_read(a,out->Ok_0.unwrap())),
        Event::Configure {..}|Event::Gate {..}|Event::DrainReleased {..}|Event::RememberPublications {..}|Event::BeginScope {..}|Event::FinishScope {..}|Event::ScopesLive {..}|Event::ScopeWait {..}|Event::Episode {..}=>b.control==a.control && b.store==a.store && b.checks==a.checks && b.checked==a.checked,
        Event::Checked {publication,enabled}=>b.control==a.control && b.store==a.store && b.checks==a.checks
        && b.checked==if enabled {a.checked.insert(publication)} else {a.checked.remove(publication)},
    }
}
pub open spec fn control_path(a:Observation,b:Observation)->bool {
    b.control.control().paper()==a.control.control().paper()
        || b.control.control_history().extends(a.control.control_history())
}
pub open spec fn step(a:Observation,b:Observation,event:Event)->bool {
    a.wf() && b.wf() && versions_advance(a,b) && control_path(a,b) && operation(a,b,event)
}
pub struct History {pub states:Seq<Observation>,pub events:Seq<Event>}
impl History {
    pub open spec fn valid(&self)->bool {
        self.states.len()==self.events.len()+1 && self.states[0].wf() && self.states[0].policy==Policy::initial()
            && self.states[0].control.control().paper().fibers.dom().is_empty()
            && self.states[0].admissions.is_empty() && self.states[0].episodes.is_empty()
            && self.states[0].interfaces.is_empty() && self.states[0].dynamic.is_empty()
            && self.states[0].restoring.is_empty() && self.states[0].released.len()==0
            && self.states[0].scopes.records().len()==0 && self.states[0].scopes.next_id()==1
            && self.states[0].control.protocol().next_id()==1
            && (forall|id:usize|!self.states[0].control.protocol().blocked_spec(id))
            && self.states[0].store.values().len()==0 && self.states[0].store.revisions().len()==0
            && self.states[0].store.registry_view().publications().len()==0
            && self.states[0].store.registry_view().lease_records().len()==0 && self.states[0].store.registry_view().lease_allocations()==0
            && self.states[0].checks.outstanding().is_empty() && self.states[0].checks.rows().is_empty()
            && self.states[0].checks.allocated()==0 && self.states[0].checks.notified()==0 && self.states[0].checked.is_empty()
            && forall|i:int|0<=i<self.events.len() ==> #[trigger] step(self.states[i],self.states[i+1],self.events[i])
    }
    pub open spec fn append(&self,after:Observation,event:Event)->Self {
        Self {states:self.states.push(after),events:self.events.push(event)}
    }
    pub open spec fn issued_at(&self,index:int,id:usize,admission:Admission)->bool {
        0<=index<self.events.len()
            && self.events[index]==(Event::Begin {consumer:id,out:Ok(admission.origin())})
            && self.states[index+1].admissions.contains_key(id) && self.states[index+1].admissions[id]==admission
            && admission.source().control==self.states[index].control && admission.source().store==self.states[index].store
            && admission.source().checks==self.states[index].checks && admission.source().checked==self.states[index].checked
    }
    /// Ownership comes from an actual successful Begin in this same history,
    /// including zero-dependency admissions. It is not supplied by the caller.
    pub proof fn admission_origin(&self,end:int,id:usize)
        requires self.valid(),0<=end<self.states.len(),self.states[end].admissions.contains_key(id),
        ensures exists|issued:int|0<=issued<end && self.issued_at(issued,id,self.states[end].admissions[id]),
        decreases end,
    {
        assert(end>0);let i=end-1;
        assert(step(self.states[i],self.states[i+1],self.events[i]));reveal(operation);
        match self.events[i] {
            Event::Begin {consumer,out} if consumer==id && out.is_ok()=>{
                assert(self.issued_at(i,id,self.states[end].admissions[id]));
            },
            _=>{
                assert(self.states[i].admissions.contains_key(id));
                assert(self.states[i].admissions[id]==self.states[end].admissions[id]);
                self.admission_origin(i,id);
            },
        }
    }
    pub open spec fn releases(&self,index:int,id:usize)->bool {
        match self.events[index] {Event::Release {id:owner,out,..}=>owner==id && out.is_ok(),_=>false}
    }
    /// All intermediate operations, including failure, restart and retry, keep
    /// the exact retained capture until its own successful managed release.
    pub proof fn admission_retained(&self,start:int,end:int,id:usize)
        requires self.valid(),0<=start<=end<self.states.len(),self.states[start].admissions.contains_key(id),
            forall|i:int|start<=i<end ==> !self.releases(i,id),
        ensures self.states[end].admissions.contains_key(id),self.states[end].admissions[id]==self.states[start].admissions[id],
        decreases end-start,
    {
        if start<end {
            self.admission_retained(start,end-1,id);
            let i=end-1;assert(step(self.states[i],self.states[i+1],self.events[i]));
            assert(!self.releases(end-1,id));reveal(operation);
        }
    }
    pub proof fn rejected_reply_preserves_episode(&self,index:int)
        requires self.valid(),0<=index<self.events.len(),self.events[index] is Cleanup,self.events[index]->Cleanup_out.is_err(),
        ensures self.states[index+1].admissions==self.states[index].admissions,self.states[index+1].episodes==self.states[index].episodes,
    {assert(step(self.states[index],self.states[index+1],self.events[index]));reveal(operation);}
    /// Release consumes the real owner previously created by Begin, with its
    /// original domain, generation and manifest, under the cleanup guard.
    pub proof fn release_has_origin(&self,index:int)
        requires self.valid(),0<=index<self.events.len(),self.events[index] is Release,self.events[index]->Release_out.is_ok(),
        ensures {
            let id=self.events[index]->Release_id;let admission=self.states[index].admissions[id];
            &&& self.states[index].admissions.contains_key(id) && !self.states[index+1].admissions.contains_key(id)
            &&& exists|issued:int|0<=issued<index && self.issued_at(issued,id,admission)
            &&& self.states[index].control.control().generation_of(id)==Some(admission.origin().generation)
            &&& self.states[index].control.protocol().resource_finish_enabled(&self.states[index].control.control(),id,false)
        },
    {
        assert(step(self.states[index],self.states[index+1],self.events[index]));reveal(operation);
        self.admission_origin(index,self.events[index]->Release_id);
    }
    pub proof fn extended(&self,after:Observation,event:Event)
        requires self.valid(),step(self.states.last(),after,event),
        ensures self.append(after,event).valid(),
    {
        let next=self.append(after,event);
        assert forall|i:int|0<=i<next.events.len() implies #[trigger] step(next.states[i],next.states[i+1],next.events[i]) by {
            if i<self.events.len() {assert(step(self.states[i],self.states[i+1],self.events[i]));}
        }
    }
    /// Only the control projection may stutter here; value/check mutations
    /// remain distinct events in the full observation.
    pub proof fn control_classified(&self,index:int)
        requires self.valid(),0<=index<self.events.len(),
        ensures self.states[index].control.control().paper()==self.states[index+1].control.control().paper()
            || crate::lifecycle_state::history::step(self.states[index].control.control().paper(),self.states[index+1].control.control().paper(),self.states[index+1].control.control_history().labels.last()),
    {
        assert(step(self.states[index],self.states[index+1],self.events[index]));
        self.states[index].control.control_history_correspondence();
        self.states[index+1].control.control_history_correspondence();
        if self.states[index].control.control().paper()!=self.states[index+1].control.control().paper() {
            let a=self.states[index].control.control_history();let b=self.states[index+1].control.control_history();
            assert(b.states.drop_last()==a.states);
            assert(b.states[b.labels.len()-1]==a.states.last());
            assert(crate::lifecycle_state::history::step(b.states[b.labels.len()-1],b.states[b.labels.len() as int],b.labels[b.labels.len()-1]));
        }
    }
    pub proof fn versions_monotone(&self,start:int,end:int,id:PublicationId)
        requires self.valid(),0<=start<=end<self.states.len(),id.0<self.states[start].store.revisions().len(),
        ensures id.0<self.states[end].store.revisions().len(),self.states[start].store.revisions()[id.0 as int]<=self.states[end].store.revisions()[id.0 as int],
        decreases end-start,
    {
        if start<end {
            let i=end-1;
            assert(0<=i<self.events.len());
            assert(step(self.states[i],self.states[i+1],self.events[i]));
            self.versions_monotone(start,i,id);
        }
    }
    /// Replacement invalidates an earlier check even if its opaque value later
    /// returns to the same number. The ordering is this owner's real call order.
    pub proof fn replacement_rejects_old_check(&self,issued:int,replaced:int,completed:int)
        requires self.valid(),0<=issued<replaced<completed<self.events.len(),
            self.events[issued] is RequestCheck,self.events[issued]->RequestCheck_out.is_ok(),
            self.events[issued]->RequestCheck_out->Ok_0.is_some(),
            self.events[replaced] is Replace,self.events[replaced]->Replace_out.is_ok(),
            self.events[completed] is CompleteCheck,
            self.events[replaced]->Replace_id==self.events[issued]->RequestCheck_out->Ok_0.unwrap().ticket.publication,
            self.events[completed]->CompleteCheck_ticket==self.events[issued]->RequestCheck_out->Ok_0.unwrap().ticket,
        ensures self.events[completed]->CompleteCheck_out!=Ok(true),
    {
        reveal(operation);
        assert(step(self.states[issued],self.states[issued+1],self.events[issued]));
        assert(step(self.states[replaced],self.states[replaced+1],self.events[replaced]));
        assert(step(self.states[completed],self.states[completed+1],self.events[completed]));
        let t=self.events[completed]->CompleteCheck_ticket;
        self.versions_monotone(issued,replaced,t.publication);
        self.versions_monotone(replaced+1,completed,t.publication);
        assert(self.states[completed].store.revisions()[t.publication.0 as int]>t.value_revision);
    }
}
}
