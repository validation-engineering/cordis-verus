//! Actual typed inverses share the production cleanup queue and ticket gate.
use super::CleanupGroups;
use crate::cleanup_journal::{RestoreError as QueueError, RestoreOutcome, RestoreTicket};
use crate::cleanup_queue::completion::{CleanupDispatch, CleanupReport};
use crate::cleanup_queue::{CleanupQueue, Insertion};
use crate::execution::Execution;
use crate::lifecycle_state::registration::shared_child::ChildCleanup;
use crate::reversible_value::joint;
use crate::reversible_value::payload::restoration::attempt::protocol::Evidence;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::restoration::issued;
use crate::reversible_value::{
    payload::{
        restoration::{Failure, Inverse, RestoreError, Restored},
        SharedPayload,
    },
    slot::ServiceSlot,
};
use crate::versioned_value::ReplaceError;
use std::sync::Arc;
use vstd::prelude::*;

verus! {
/// Host callbacks keep their existing policy; typed inverses have a dedicated
/// checked branch. Retention is returned after success for destruction outside
/// host locks. Production uses the actual `Arc<ServiceSlot>` here.
pub enum Cleanup<C,R,H,T:?Sized> {Once(C),Retryable(R),Payload {inverse:Inverse<T>,retained:H}}
pub type Action<C,R,H,T,X> = ChildCleanup<Cleanup<C,R,H,T>,X>;
pub type Report<C,R,H,T,X> = CleanupReport<RestoreError,Action<C,R,H,T,X>>;
pub type DispatchResult<C,R,H,T,X> = Result<Option<Dispatch<C,R,H,T,X>>,QueueError>;

#[allow(dead_code)]
pub struct Admission<T:?Sized> {pub token:usize,inverse:Ghost<Inverse<T>>,insertion:Ghost<Insertion>,witnesses:Tracked<crate::reversible_value::registration::ReceiptMap>}
impl<T:?Sized> Admission<T> {
    pub closed spec fn witnesses(&self)->crate::reversible_value::registration::ReceiptMap {self.witnesses@}
    pub open spec fn witnessed(&self)->bool {
        crate::reversible_value::registration::witnesses(self.witnesses())
            && self.witnesses().contains_key((0,false)) && self.witnesses()[(0,false)].same(&self.inverse().after().commit)
            && (self.registration_receipt().is_some() ==> self.witnesses().contains_key((0,true))
                && self.witnesses()[(0,true)].same(&self.registration_receipt().unwrap()))
    }
    pub(crate) proof fn retain(tracked &self,tracked receipts:&mut crate::reversible_value::registration::ReceiptMap,index:int)
        requires self.witnessed(),crate::reversible_value::registration::witnesses(*old(receipts)),
        ensures crate::reversible_value::registration::witnesses(*final(receipts)),
            final(receipts).contains_key((index,false)) && final(receipts)[(index,false)].same(&self.inverse().after().commit),
            self.registration_receipt().is_some() ==> final(receipts).contains_key((index,true)) && final(receipts)[(index,true)].same(&self.registration_receipt().unwrap()),
            *final(receipts)==if self.registration_receipt().is_some() {
                old(receipts).insert((index,false),final(receipts)[(index,false)]).insert((index,true),final(receipts)[(index,true)])
            } else {old(receipts).insert((index,false),final(receipts)[(index,false)])},
            forall|k:(int,bool)| k.0!=index ==> final(receipts).contains_key(k)==old(receipts).contains_key(k)
                && (old(receipts).contains_key(k) ==> #[trigger] final(receipts)[k]==old(receipts)[k]),
    {
        receipts.tracked_insert((index,false),self.witnesses.borrow().tracked_borrow((0,false)).duplicate());
        if self.registration_receipt().is_some() {receipts.tracked_insert((index,true),self.witnesses.borrow().tracked_borrow((0,true)).duplicate());}
    }
    pub closed spec fn inverse(&self)->Inverse<T> {self.inverse@}
    pub(crate) closed spec fn insertion(&self)->Insertion {self.insertion@}
    pub closed spec fn token_spec(&self)->usize {self.token}
    pub closed spec fn registered(&self,link:Option<(joint::Journal,nat)>,state:joint::episode::CleanupState)->bool {
        self.insertion().recorded(link,state,Some(self.inverse().after().commit),
            if joint::local(link,self.inverse().owner().journal_spec()) {Some(self.inverse().after().commit.at())} else {None})
    }
    pub open spec fn queued<C,R,H,X>(&self,queue:CleanupQueue<Action<C,R,H,T,X>>,retained:H)->bool {
        self.token_spec()<queue.slots().len() && queue.slots()[self.token_spec() as int]==Some(ChildCleanup::Callback(Cleanup::Payload {inverse:self.inverse(),retained}))
            && self.registered(queue.link(),queue.observation())
    }
    pub closed spec fn registration_receipt(&self)->Option<joint::Receipt> {self.insertion().trace@}
    pub proof fn pending_interval(&self,link:Option<(joint::Journal,nat)>,state:joint::episode::CleanupState)
        requires self.inverse().wf(),self.registered(link,state),joint::local(link,self.inverse().owner().journal_spec()),
        ensures self.registration_receipt().is_some(),self.registration_receipt().unwrap().wf(),
            self.registration_receipt().unwrap().follows(&self.inverse().after().commit),
            forall|n:nat|self.inverse().after().commit.at()<n<=self.registration_receipt().unwrap().at() ==>
                #[trigger] joint::pending_at(self.registration_receipt().unwrap().events(),n).contains_key(self.inverse().after().commit.at()),
            !self.registration_receipt().unwrap().events().last().pending.contains_key(self.inverse().after().commit.at()),
    {
        self.inverse().provenance();
        let receipt=self.registration_receipt().unwrap();
        joint::pending_since(receipt.events(),self.inverse().after().commit.at(),receipt.at());
        assert forall|n:nat|self.inverse().after().commit.at()<n<=receipt.at() implies
            #[trigger] joint::pending_at(receipt.events(),n).contains_key(self.inverse().after().commit.at()) by {
            assert(joint::pending_at(receipt.events(),n).contains_pair(self.inverse().after().commit.at(),receipt.events()[self.inverse().after().commit.at() as int].event.key));
        }
    }

}
impl<V,C,G,A,R,H,T:?Sized,X> Execution<V,C,G,Action<A,R,H,T,X>> {
    #[allow(clippy::type_complexity)]
    pub fn apply_payload(&mut self,id:usize,owner:&SharedPayload<T>,value:Arc<T>,retained:H)
        ->(out:Result<Admission<T>,(ReplaceError,Arc<T>,H)>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).execution_journal()==old(self).execution_journal(),
            final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),
            final(self).capture()==old(self).capture(),final(self).phase_spec()==old(self).phase_spec(),
            final(self).value_attempts()==old(self).value_attempts(),final(self).status_links()==old(self).status_links(),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0.1==value && out->Err_0.2==retained,
            out.is_ok() ==> {
                let a=out->Ok_0;let inv=a.inverse();let queue=final(self).cleanup_state().queues()[id];
                &&& final(self).cleanup_state().acquisition_open(id)==old(self).cleanup_state().acquisition_open(id)
                &&& final(self).cleanup_state().live(id)
                &&& a.witnessed() && inv.wf() && inv.owner()==*owner && inv.after().value==value
                &&& old(self).work_state().accepts() && old(self).cleanup_state().acquisition_open(id)
                &&& a.token_spec()==old(self).cleanup_state().queues()[id].slots().len()
                &&& queue.slots()==old(self).cleanup_state().queues()[id].slots().push(Some(ChildCleanup::Callback(Cleanup::Payload {inverse:inv,retained})))
                &&& queue.protocol().waiting()==old(self).cleanup_state().queues()[id].protocol().waiting().push(a.token_spec())
                &&& a.registered(queue.link(),queue.observation()) && a.queued(queue,retained)
            },
    {let tracked empty=Map::tracked_empty();match self.apply_payload_following(id,owner,value,retained,Tracked(&empty)) {Ok(a)=>Ok(a),Err((error,value,retained,_))=>Err((error,value,retained))}}
    #[allow(clippy::type_complexity)]
    pub(crate) fn apply_payload_following(&mut self,id:usize,owner:&SharedPayload<T>,value:Arc<T>,retained:H,Tracked(cause):Tracked<&crate::reversible_value::registration::ReceiptMap>)
        ->(out:Result<Admission<T>,(ReplaceError,Arc<T>,H,Ghost<Option<crate::reversible_value::payload::restoration::ForwardRejection<T>>>)>)
        requires old(self).wf(),crate::reversible_value::registration::witnesses(*cause),
        ensures out.is_err() ==> if old(self).work_state().accepts() && old(self).cleanup_state().acquisition_open(id) {
                out->Err_0.3@.is_some() && out->Err_0.3@.unwrap().owner()==*owner && out->Err_0.3@.unwrap().explains(out->Err_0.0)
            } else {out->Err_0.0==ReplaceError::Closed && out->Err_0.3@.is_none()},
            out.is_ok() ==> forall|k:(int,bool)|cause.contains_key(k) && #[trigger] cause[k].journal()==out->Ok_0.inverse().owner().journal_spec() ==> out->Ok_0.inverse().after().commit.follows(&cause[k]),
            final(self).wf(),final(self).execution_journal()==old(self).execution_journal(),
            final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),
            final(self).capture()==old(self).capture(),final(self).phase_spec()==old(self).phase_spec(),
            final(self).value_attempts()==old(self).value_attempts(),final(self).status_links()==old(self).status_links(),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0.1==value && out->Err_0.2==retained,
            out.is_ok() ==> {
                let a=out->Ok_0;let inv=a.inverse();let queue=final(self).cleanup_state().queues()[id];
                &&& final(self).cleanup_state().acquisition_open(id)==old(self).cleanup_state().acquisition_open(id)
                &&& final(self).cleanup_state().live(id)
                &&& a.witnessed() && inv.wf() && inv.owner()==*owner && inv.after().value==value
                &&& old(self).work_state().accepts() && old(self).cleanup_state().acquisition_open(id)
                &&& a.token_spec()==old(self).cleanup_state().queues()[id].slots().len()
                &&& queue.slots()==old(self).cleanup_state().queues()[id].slots().push(Some(ChildCleanup::Callback(Cleanup::Payload {inverse:inv,retained})))
                &&& queue.protocol().waiting()==old(self).cleanup_state().queues()[id].protocol().waiting().push(a.token_spec())
                &&& a.registered(queue.link(),queue.observation()) && a.queued(queue,retained)
            },
    {
        proof {self.representation();}
        if !self.accepts_acquisition(id) {return Err((ReplaceError::Closed,value,retained,Ghost(None)));}
        let (applied,rejection)=owner.apply_managed_following(value,Ghost(joint::local(self.cleanup_state().queues()[id].link(),owner.journal_spec())),Tracked(cause));
        let applied=match applied {
            Ok(applied)=>applied,Err(error)=>return Err((error.error,error.value,retained,rejection)),
        };
        let ghost inverse=applied.inverse;
        let tracked write=applied.inverse.receipt();
        let tracked write_cause=write.duplicate();
        let payload=ChildCleanup::Callback(Cleanup::Payload {inverse:applied.inverse,retained});
        let insertion=match self.groups.register_following(id,payload,Tracked(Some(write_cause)),applied.pending) {
            Ok(insertion)=>insertion,Err(_)=>{assert(false);panic!("admitted payload inverse");},
        };
        proof {self.representation();}
        let tracked mut witnesses=Map::tracked_empty();
        proof {witnesses.tracked_insert((0int,false),write);match insertion.trace.borrow() {Some(receipt)=>witnesses.tracked_insert((0int,true),receipt.duplicate()),None=>{}}}
        Ok(Admission {token:insertion.token,inverse:Ghost(inverse),insertion:Ghost(insertion),witnesses:Tracked(witnesses)})
    }
}

pub open spec fn selected<T:?Sized,M>(episode:crate::lifecycle_state::services::NativeEpisode<ServiceSlot<SharedPayload<T>,M>>,port:crate::Port,owner:SharedPayload<T>)->bool {
    !episode.closed() && if episode.provisions().contains(port) {
        episode.owned().contains_key((port.key,port.realm)) && episode.owned()[(port.key,port.realm)].opaque_spec()==Some(owner)
    } else {exists|provider:usize| episode.bindings().contains(crate::Binding {provider,key:port.key,realm:port.realm})
        && episode.imports().contains_key((provider,port.key,port.realm)) && #[trigger] episode.imports()[(provider,port.key,port.realm)].opaque_spec()==Some(owner)}
}
#[derive(Debug)]
pub enum AccessError {NoNative,Read(crate::lifecycle_state::services::NativeReadError),Scalar,Value(ReplaceError)}
pub open spec fn access_failed<T:?Sized,M>(episode:Option<crate::lifecycle_state::services::NativeEpisode<ServiceSlot<SharedPayload<T>,M>>>,open:bool,port:crate::Port,error:AccessError,rejection:Option<crate::reversible_value::payload::restoration::ForwardRejection<T>>)->bool {
    match error {
        AccessError::NoNative=>episode.is_none(),
        AccessError::Read(error)=>episode.is_some() && episode.unwrap().read_failed(port,error),
        AccessError::Scalar=>episode.is_some() && exists|provider:usize,slot:Arc<ServiceSlot<SharedPayload<T>,M>>| #[trigger] episode.unwrap().selects_value(provider,port,slot) && slot.opaque_spec().is_none(),
        AccessError::Value(error)=>if !open {error==ReplaceError::Closed && rejection.is_none()} else {
            episode.is_some() && rejection.is_some() && rejection.unwrap().explains(error) && selected(episode.unwrap(),port,rejection.unwrap().owner())
        },
    }
}
impl<C,G,A,R,T:?Sized,M,X> Execution<ServiceSlot<SharedPayload<T>,M>,C,G,ChildCleanup<Cleanup<A,R,Arc<ServiceSlot<SharedPayload<T>,M>>,T>,X>> {
    pub fn apply_native_payload(&mut self,id:usize,port:crate::Port,value:Arc<T>)->(out:Result<Admission<T>,(AccessError,Arc<T>)>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).execution_journal()==old(self).execution_journal(),
            final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),
            final(self).capture()==old(self).capture(),final(self).phase_spec()==old(self).phase_spec(),
            final(self).value_attempts()==old(self).value_attempts(),final(self).status_links()==old(self).status_links(),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0.1==value,
            out.is_ok() ==> out->Ok_0.witnessed() && out->Ok_0.inverse().wf() && out->Ok_0.inverse().after().value==value
                && old(self).value_state().is_some()
                && selected(old(self).value_state().unwrap(),port,out->Ok_0.inverse().owner())
                && final(self).cleanup_state().live(id) && final(self).cleanup_state().acquisition_open(id)==old(self).cleanup_state().acquisition_open(id)
                && out->Ok_0.token_spec()==old(self).cleanup_state().queues()[id].slots().len()
                && final(self).cleanup_state().queues()[id].slots().len()==old(self).cleanup_state().queues()[id].slots().len()+1
                && final(self).cleanup_state().queues()[id].slots().take(out->Ok_0.token_spec() as int)==old(self).cleanup_state().queues()[id].slots()
                && final(self).cleanup_state().queues()[id].protocol().waiting()==old(self).cleanup_state().queues()[id].protocol().waiting().push(out->Ok_0.token_spec())
                && exists|retained:Arc<ServiceSlot<SharedPayload<T>,M>>| #[trigger] out->Ok_0.queued(final(self).cleanup_state().queues()[id],retained)
                    && retained.opaque_spec()==Some(out->Ok_0.inverse().owner()),
    {let tracked empty=Map::tracked_empty();match self.apply_native_payload_following(id,port,value,Tracked(&empty)) {Ok(a)=>Ok(a),Err((error,value,_))=>Err((error,value))}}
    #[allow(clippy::type_complexity)]
    pub(crate) fn apply_native_payload_following(&mut self,id:usize,port:crate::Port,value:Arc<T>,Tracked(cause):Tracked<&crate::reversible_value::registration::ReceiptMap>)->(out:Result<Admission<T>,(AccessError,Arc<T>,Ghost<Option<crate::reversible_value::payload::restoration::ForwardRejection<T>>>)>)
        requires old(self).wf(),crate::reversible_value::registration::witnesses(*cause),
        ensures out.is_err() ==> access_failed(old(self).value_state(),old(self).work_state().accepts() && old(self).cleanup_state().acquisition_open(id),port,out->Err_0.0,out->Err_0.2@),
            out.is_ok() ==> forall|k:(int,bool)|cause.contains_key(k) && #[trigger] cause[k].journal()==out->Ok_0.inverse().owner().journal_spec() ==> out->Ok_0.inverse().after().commit.follows(&cause[k]),
            final(self).wf(),final(self).execution_journal()==old(self).execution_journal(),
            final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),
            final(self).capture()==old(self).capture(),final(self).phase_spec()==old(self).phase_spec(),
            final(self).value_attempts()==old(self).value_attempts(),final(self).status_links()==old(self).status_links(),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0.1==value,
            out.is_ok() ==> out->Ok_0.witnessed() && out->Ok_0.inverse().wf() && out->Ok_0.inverse().after().value==value
                && old(self).value_state().is_some()
                && selected(old(self).value_state().unwrap(),port,out->Ok_0.inverse().owner())
                && final(self).cleanup_state().live(id) && final(self).cleanup_state().acquisition_open(id)==old(self).cleanup_state().acquisition_open(id)
                && out->Ok_0.token_spec()==old(self).cleanup_state().queues()[id].slots().len()
                && final(self).cleanup_state().queues()[id].slots().len()==old(self).cleanup_state().queues()[id].slots().len()+1
                && final(self).cleanup_state().queues()[id].slots().take(out->Ok_0.token_spec() as int)==old(self).cleanup_state().queues()[id].slots()
                && final(self).cleanup_state().queues()[id].protocol().waiting()==old(self).cleanup_state().queues()[id].protocol().waiting().push(out->Ok_0.token_spec())
                && exists|retained:Arc<ServiceSlot<SharedPayload<T>,M>>| #[trigger] out->Ok_0.queued(final(self).cleanup_state().queues()[id],retained)
                    && retained.opaque_spec()==Some(out->Ok_0.inverse().owner()),
    {
        proof {self.representation();}
        let values=match &self.values {Some(values)=>values,None=>return Err((AccessError::NoNative,value,Ghost(None)))};
        let (_provider,slot)=match values.read(port) {Ok(pair)=>pair,Err(error)=>return Err((AccessError::Read(error),value,Ghost(None)))};
        let owner=match slot.opaque() {Some(owner)=>owner.clone(),None=>return Err((AccessError::Scalar,value,Ghost(None)))};
        proof {assert(selected(*values,port,owner)) by {
            if !values.provisions().contains(port) {assert(values.bindings().contains(crate::Binding {provider:_provider,key:port.key,realm:port.realm}));}
        }}
        let retained=slot.clone();
        match self.apply_payload_following(id,&owner,value,retained,Tracked(cause)) {Ok(a)=>{
            assert(a.queued(self.cleanup_state().queues()[id],retained));
            assert(retained.opaque_spec()==Some(a.inverse().owner()));
            assert(exists|slot:Arc<ServiceSlot<SharedPayload<T>,M>>| #[trigger] a.queued(self.cleanup_state().queues()[id],slot) && slot.opaque_spec()==Some(a.inverse().owner()));
            Ok(a)},Err((error,value,_retained,rejection))=>Err((AccessError::Value(error),value,rejection))}
    }
}

pub struct Completion<C,R,H,T:?Sized,X> {
    pub ticket:RestoreTicket,
    pub report:Report<C,R,H,T,X>,
    pub restored:Option<Restored<T>>,
    pub attempt:Ghost<Result<Restored<T>,Failure<T>>>,
    pub trace:Tracked<Evidence<T>>,
}
pub enum Dispatch<C,R,H,T:?Sized,X> {Other(CleanupDispatch<Cleanup<C,R,H,T>,X>),Payload(Completion<C,R,H,T,X>)}
impl<C,R,H,T:?Sized,X> Completion<C,R,H,T,X> {
    pub closed spec fn evidence(&self)->Evidence<T> {self.trace@}
    pub open spec fn corresponds(&self,inverse:Inverse<T>,retained:H)->bool {
        &&& self.evidence().certified() && self.evidence().inverse()==inverse && self.evidence().ticket()==self.ticket
        &&& self.evidence().attempt().result()==self.attempt@
        &&& self.attempt@.is_ok()==self.restored.is_some()
        &&& self.attempt@.is_ok() ==> self.restored==Some(self.attempt@->Ok_0) && self.attempt@->Ok_0.wf()
            && self.attempt@->Ok_0.before().state()==inverse.after().state()
            && self.attempt@->Ok_0.after().state()==inverse.before().state()
        &&& self.attempt@.is_err() ==> self.attempt@->Err_0.wf(&inverse)
        &&& self.report.result==match self.attempt@ {Ok(_)=>Ok(()),Err(error)=>Err(error.error_spec())}
        &&& self.report.outcome==if self.restored.is_some() {RestoreOutcome::Succeeded} else {RestoreOutcome::Failed}
        &&& self.report.discarded==if self.restored.is_some() {Some(ChildCleanup::Callback(Cleanup::Payload {inverse,retained}))} else {None}
    }
}
impl<C,R,H,T:?Sized,X> Dispatch<C,R,H,T,X> {
    pub open spec fn ticket(&self)->RestoreTicket {match self {Self::Other(d)=>d.ticket(),Self::Payload(c)=>c.ticket}}
    pub open spec fn selected_from(&self,selected:Option<RestoreTicket>,waiting:Seq<usize>)->bool {
        match selected {Some(ticket)=>self.ticket()==ticket,None=>waiting.len()>0 && self.ticket().token==waiting.last()}
    }
    pub open spec fn from_slot(&self,slots:Seq<Option<Action<C,R,H,T,X>>>)->bool {
        match self {
            Self::Other(d)=>d.from_slot(slots) && match d {
                CleanupDispatch::Host {action,..}=>match action {ChildCleanup::Callback(Cleanup::Payload {..})=>false,_=>true},_=>true,
            },
            Self::Payload(c)=>c.ticket.token<slots.len() && match slots[c.ticket.token as int] {
                Some(ChildCleanup::Callback(Cleanup::Payload {inverse,retained}))=>c.corresponds(inverse,retained),_=>false,
            },
        }
    }
}
impl<C,R,H,T:?Sized,X> CleanupQueue<Action<C,R,H,T,X>> {
    fn restore_payload(&mut self,ticket:RestoreTicket,inverse:Inverse<T>,retained:H,Tracked(issue):Tracked<Option<joint::Receipt>>)->(out:Completion<C,R,H,T,X>)
        requires old(self).wf(),old(self).issued(),old(self).protocol().selected()==Some(ticket),!old(self).protocol().failed_spec(),
            issued(issue,old(self).link(),ticket),issue.is_some() ==> issue.unwrap().events()==old(self).trace(),
        ensures final(self).wf(),final(self).link()==old(self).link(),final(self).protocol().domain_id()==old(self).protocol().domain_id(),
            out.ticket==ticket,out.corresponds(inverse,retained),out.report.result.is_ok()==out.restored.is_some(),
            out.evidence().records(inverse,ticket,old(self).link()),
            final(self).link().is_some() ==> out.evidence().acknowledgement().unwrap().events()==final(self).trace(),
            out.restored.is_some() ==> out.restored.unwrap().wf() && out.restored.unwrap().after().state()==inverse.before().state(),
            out.report.outcome==if out.restored.is_some() {RestoreOutcome::Succeeded} else {RestoreOutcome::Failed},
            out.report.discarded==if out.restored.is_some() {Some(ChildCleanup::Callback(Cleanup::Payload {inverse,retained}))} else {None},
            final(self).slots()==old(self).slots().update(ticket.token as int,if out.restored.is_some() {None} else {Some(ChildCleanup::Callback(Cleanup::Payload {inverse,retained}))}),
            !final(self).issued(),final(self).protocol().failed_spec()==out.restored.is_none(),
    {
        let tracked cause=match &issue {Some(receipt)=>Some(receipt.duplicate()),None=>None};
        let (attempt,trace)=inverse.restore_following(Tracked(cause));
        self.acknowledge_payload(ticket,inverse,retained,attempt,trace,Tracked(issue))
    }
    fn acknowledge_payload(&mut self,ticket:RestoreTicket,inverse:Inverse<T>,retained:H,
        attempt:Result<Restored<T>,Failure<T>>,Tracked(attempt_trace):Tracked<crate::reversible_value::payload::restoration::attempt::Attempt<T>>,
        Tracked(issue):Tracked<Option<joint::Receipt>>)->(out:Completion<C,R,H,T,X>)
        requires old(self).wf(),old(self).issued(),old(self).protocol().selected()==Some(ticket),!old(self).protocol().failed_spec(),
            issued(issue,old(self).link(),ticket),issue.is_some() ==> issue.unwrap().events()==old(self).trace(),
            attempt_trace.wf(),attempt_trace.inverse()==inverse,attempt_trace.result()==attempt,attempt_trace.follows_cause(issue),
            attempt.is_ok() ==> attempt->Ok_0.wf() && attempt->Ok_0.before().state()==inverse.after().state()
                && attempt->Ok_0.after().state()==inverse.before().state(),
            attempt.is_err() ==> attempt->Err_0.wf(&inverse),
        ensures final(self).wf(),final(self).link()==old(self).link(),final(self).protocol().domain_id()==old(self).protocol().domain_id(),
            out.ticket==ticket,out.corresponds(inverse,retained),out.report.result.is_ok()==out.restored.is_some(),
            out.evidence().records(inverse,ticket,old(self).link()),
            final(self).link().is_some() ==> out.evidence().acknowledgement().unwrap().events()==final(self).trace(),
            out.restored.is_some() ==> out.restored.unwrap().wf() && out.restored.unwrap().after().state()==inverse.before().state(),
            out.report.outcome==if out.restored.is_some() {RestoreOutcome::Succeeded} else {RestoreOutcome::Failed},
            out.report.discarded==if out.restored.is_some() {Some(ChildCleanup::Callback(Cleanup::Payload {inverse,retained}))} else {None},
            final(self).slots()==old(self).slots().update(ticket.token as int,if out.restored.is_some() {None} else {Some(ChildCleanup::Callback(Cleanup::Payload {inverse,retained}))}),
            !final(self).issued(),final(self).protocol().failed_spec()==out.restored.is_none(),
    {
        let ghost queue=self.link();let ghost observed=attempt;
        proof {self.issued_slot(ticket);attempt_trace.domain();}
        let tracked cause=Some(attempt_trace.completion_cause());
        let (result,restored)=match attempt {Ok(restored)=>(Ok(()),Some(restored)),Err(error)=>(Err(error.error()),None)};
        let payload=ChildCleanup::Callback(Cleanup::Payload {inverse,retained});
        let (retry,discarded)=if result.is_ok() {(None,Some(payload))} else {(Some(payload),None)};
        let outcome=if result.is_ok() {RestoreOutcome::Succeeded} else {RestoreOutcome::Failed};
        proof {self.completion_condition(ticket,outcome,retry);}
        let _accepted=self.complete_following(ticket,outcome,retry,Tracked(cause));assert(_accepted.is_ok());
        let tracked acknowledgement=self.latest_receipt();
        let tracked trace=Evidence {issue,attempt:attempt_trace,acknowledgement,queue,ticket};
        proof {
            trace.representation();
            assert(issued(trace.issue(),trace.queue(),trace.ticket()));
            assert(trace.attempt().wf() && trace.attempt().follows_cause(trace.issue()));
            assert(trace.acknowledgement().is_some()==trace.queue().is_some());
            if trace.acknowledgement().is_some() {
                let ack=trace.acknowledgement().unwrap();
                assert(ack.wf() && ack.journal()==queue.unwrap().0 && ack.event().key==queue.unwrap().1);
                assert(ack.event().change==(joint::Change::Cleanup {event:joint::episode::CleanupChange::Complete {ticket,outcome,retained:!result.is_ok()}}));
                assert(ack.event().after is Cleanup && !ack.event().after->Cleanup_state.issued);
                assert(ack.event().after->Cleanup_state.failed==!result.is_ok());
                assert(ack.event().after->Cleanup_state.occupied[ticket.token as int]==!result.is_ok());
                assert(ack.event().after->Cleanup_state.selected==if result.is_ok() {None} else {Some(ticket)});
                assert(ack.follows(&trace.issue().unwrap()));
            }
            assert(trace.same_domain() ==> trace.acknowledgement().unwrap().follows(&trace.attempt().endpoint()));
            trace.establish_interval();
        }
        Completion {ticket,report:CleanupReport {result,outcome,discarded},restored,attempt:Ghost(observed),trace:Tracked(trace)}
    }
    fn dispatch_payload(&mut self)->(out:DispatchResult<C,R,H,T,X>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).link()==old(self).link(),final(self).protocol().domain_id()==old(self).protocol().domain_id(),
            out.is_ok() && out->Ok_0.is_some() ==> out->Ok_0.unwrap().from_slot(old(self).slots())
                && out->Ok_0.unwrap().selected_from(old(self).protocol().selected(),old(self).protocol().waiting()),
            out.is_ok() && out->Ok_0.is_some() && out->Ok_0.unwrap() is Payload ==> {
                let c=out->Ok_0.unwrap()->Payload_0;let original=old(self).slots()[c.ticket.token as int].unwrap()->Callback_0;
                &&& c.ticket.token<old(self).slots().len() && old(self).slots()[c.ticket.token as int].is_some()
                &&& old(self).slots()[c.ticket.token as int].unwrap() is Callback && original is Payload
                &&& c.restored.is_some() ==> c.restored.unwrap().wf() && c.restored.unwrap().after().state()==original->Payload_inverse.before().state()
                &&& c.evidence().records(original->Payload_inverse,c.ticket,old(self).link())
                &&& final(self).link().is_some() ==> c.evidence().acknowledgement().unwrap().events()==final(self).trace()
                &&& c.report.result.is_ok()==c.restored.is_some()
                &&& c.report.outcome==if c.restored.is_some() {RestoreOutcome::Succeeded} else {RestoreOutcome::Failed}
                &&& final(self).slots()==old(self).slots().update(c.ticket.token as int,if c.restored.is_some() {None} else {old(self).slots()[c.ticket.token as int]})
                &&& final(self).protocol().failed_spec()==c.restored.is_none()
            },
    {
        let dispatch=match self.dispatch()? {None=>return Ok(None),Some(dispatch)=>dispatch};
        match dispatch {
            CleanupDispatch::Host {ticket,action:ChildCleanup::Callback(Cleanup::Payload {inverse,retained})}=>{
                let tracked issue=self.issue_receipt(ticket);
                Ok(Some(Dispatch::Payload(self.restore_payload(ticket,inverse,retained,Tracked(issue)))))
            },
            other=>Ok(Some(Dispatch::Other(other))),
        }
    }
}
impl<C,R,H,T:?Sized,X> CleanupGroups<Action<C,R,H,T,X>> {
    pub fn dispatch_payload(&mut self,id:usize)->(out:DispatchResult<C,R,H,T,X>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).execution_journal()==old(self).execution_journal(),final(self).link()==old(self).link(),
            final(self).origin()==old(self).origin(),final(self).domain_ids()==old(self).domain_ids(),final(self).queues().dom()==old(self).queues().dom(),
            final(self).drained_failure()==old(self).drained_failure(),final(self).frame(old(self),id),
            out.is_ok() && out->Ok_0.is_some() ==> old(self).live(id)
                && out->Ok_0.unwrap().from_slot(old(self).queues()[id].slots())
                && out->Ok_0.unwrap().selected_from(old(self).queues()[id].protocol().selected(),old(self).queues()[id].protocol().waiting()),
            out.is_ok() && out->Ok_0.is_some() && out->Ok_0.unwrap() is Payload ==> {
                let c=out->Ok_0.unwrap()->Payload_0;
                &&& c.evidence().queue()==old(self).queues()[id].link()
                &&& final(self).queues()[id].link().is_some() ==> c.evidence().acknowledgement().unwrap().events()==final(self).queues()[id].trace()
                &&& final(self).queues()[id].slots()==old(self).queues()[id].slots().update(c.ticket.token as int,if c.restored.is_some() {None} else {old(self).queues()[id].slots()[c.ticket.token as int]})
                &&& final(self).queues()[id].protocol().failed_spec()==c.restored.is_none()
            },
    {
        if !self.contains(id) {return Err(QueueError::InvalidState);}
        let mut queue=self.take(id);let out=queue.dispatch_payload();self.put(id,queue);out
    }
}
impl<V,C,G,A,R,H,T:?Sized,X> Execution<V,C,G,Action<A,R,H,T,X>> {
    pub fn dispatch_payload_cleanup(&mut self,id:usize)->(out:DispatchResult<A,R,H,T,X>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).execution_journal()==old(self).execution_journal(),
            final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),
            final(self).capture()==old(self).capture(),final(self).phase_spec()==old(self).phase_spec(),
            final(self).value_attempts()==old(self).value_attempts(),final(self).status_links()==old(self).status_links(),
            out.is_ok() && out->Ok_0.is_some() ==> old(self).cleanup_state().live(id)
                && out->Ok_0.unwrap().from_slot(old(self).cleanup_state().queues()[id].slots())
                && out->Ok_0.unwrap().selected_from(old(self).cleanup_state().queues()[id].protocol().selected(),old(self).cleanup_state().queues()[id].protocol().waiting()),
            out.is_ok() && out->Ok_0.is_some() && out->Ok_0.unwrap() is Payload ==> {
                let c=out->Ok_0.unwrap()->Payload_0;
                &&& c.evidence().queue()==old(self).cleanup_state().queues()[id].link()
                &&& final(self).cleanup_state().queues()[id].link().is_some() ==> c.evidence().acknowledgement().unwrap().events()==final(self).cleanup_state().queues()[id].trace()
                &&& final(self).cleanup_state().queues()[id].slots()==old(self).cleanup_state().queues()[id].slots().update(c.ticket.token as int,if c.restored.is_some() {None} else {old(self).cleanup_state().queues()[id].slots()[c.ticket.token as int]})
                &&& final(self).cleanup_state().queues()[id].protocol().failed_spec()==c.restored.is_none()
            },
    {proof {self.representation();}let out=self.groups.dispatch_payload(id);proof {self.representation();}out}
}
}
