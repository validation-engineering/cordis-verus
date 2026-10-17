//! Versioned availability checks used by the Node host. The ledger derives
//! issued values and reply freshness from the actual publication owner and
//! lifecycle graph. Predicate evaluation remains an external input.
use crate::publication::values::PublicationStore;
use crate::publication::PublicationId;
use crate::{lifecycle_state::LifecycleState, Phase, Port};
use std::collections::BTreeMap;
use vstd::prelude::*;
#[path = "node_admission.rs"]
pub mod admission;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::IteratorSpec;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub type Key=(usize,u64,u64);
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct CheckTicket {
    pub domain:u64,pub consumer:usize,pub port:Port,pub publication:PublicationId,
    pub value_revision:u64,pub notification:u64,pub action:u64,
}
impl CheckTicket {
    pub open spec fn key(&self)->Key {(self.consumer,self.port.key,self.port.realm)}
}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct CheckAction {pub ticket:CheckTicket,pub value:u64}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct Record {
    pub publication:PublicationId,pub notification:u64,pub dirty:bool,
    pub available:bool,pub last_current:Option<bool>,
}
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum CheckError {Capacity,Stale}

pub struct Availability {
    domain:u64,records:BTreeMap<Key,Record>,pending:BTreeMap<u64,CheckAction>,
    next_action:u64,notification:u64,
}
impl Availability {
    pub closed spec fn domain_id(&self)->u64 {self.domain}
    pub closed spec fn rows(&self)->Map<Key,Record> {self.records@}
    pub closed spec fn outstanding(&self)->Map<u64,CheckAction> {self.pending@}
    pub closed spec fn allocated(&self)->u64 {self.next_action}
    pub closed spec fn notified(&self)->u64 {self.notification}
    pub closed spec fn wf(&self)->bool {
        &&& forall|id:u64|self.outstanding().contains_key(id) ==> {
            let t=self.outstanding()[id].ticket;
            t.action==id && id<self.allocated() && t.domain==self.domain_id() && t.notification<=self.notified()
        }
        &&& forall|key:Key|self.rows().contains_key(key) ==> self.rows()[key].notification<=self.notified()
    }
    pub open spec fn eligible(&self,control:&LifecycleState,store:&PublicationStore<u64>,consumer:usize,port:Port,id:PublicationId)->bool {
        &&& control.protocol().domain_id()==self.domain_id()
        &&& store.registry_view().domain_id()==Some(self.domain_id())
        &&& control.control().registered(consumer) && !control.control().is_retired(consumer) && control.control().declares_dependency(consumer,port)
        &&& id.0<store.registry_view().publications().len()
        &&& store.registry_view().publications()[id.0 as int].visible
        &&& store.registry_view().publications()[id.0 as int].port==port
        &&& control.control().phase_of(store.registry_view().publications()[id.0 as int].owner)==Some(Phase::Active)
        &&& !control.control().is_retired(store.registry_view().publications()[id.0 as int].owner)
        &&& control.control().generation_of(store.registry_view().publications()[id.0 as int].owner)==Some(store.registry_view().publications()[id.0 as int].generation)
        &&& control.control().declares_provision(store.registry_view().publications()[id.0 as int].owner,port)
    }
    fn eligible_now(&self,control:&LifecycleState,store:&PublicationStore<u64>,consumer:usize,port:Port,id:PublicationId)->(out:bool)
        requires control.wf(),store.wf(),
        ensures out==self.eligible(control,store,consumer,port,id),
    {
        if control.domain()!=self.domain || store.registry().domain()!=Some(self.domain) || !control.kernel().contains(consumer) || control.kernel().retired(consumer) || !control.kernel().dependency_declared(consumer,port) {return false;}
        match store.registry().entry(id) {
            None=>false,
            Some(entry)=>entry.visible && entry.port==port && control.kernel().phase(entry.owner)==Some(Phase::Active) && !control.kernel().retired(entry.owner)
                && control.kernel().episode_generation(entry.owner)==Some(entry.generation) && control.kernel().provision_reserved(entry.owner,port),
        }
    }
    pub open spec fn recorded(&self,t:CheckTicket)->bool {
        self.outstanding().contains_key(t.action) && self.outstanding()[t.action].ticket==t
    }
    pub open spec fn fresh(&self,t:CheckTicket,control:&LifecycleState,store:&PublicationStore<u64>)->bool {
        &&& self.recorded(t)
        &&& self.eligible(control,store,t.consumer,t.port,t.publication)
        &&& t.publication.0<store.values().len() && store.values()[t.publication.0 as int].is_some()
        &&& store.revisions()[t.publication.0 as int]==t.value_revision
        &&& store.values()[t.publication.0 as int]==Some(self.outstanding()[t.action].value)
        &&& self.rows().contains_key(t.key())
        &&& self.rows()[t.key()].publication==t.publication
        &&& self.rows()[t.key()].notification==t.notification && !self.rows()[t.key()].dirty
    }
    pub fn new(domain:u64)->(out:Self)
        ensures out.wf(),out.domain_id()==domain,out.rows()==Map::<Key,Record>::empty(),out.outstanding()==Map::<u64,CheckAction>::empty(),out.allocated()==0,out.notified()==0,
    {Self {domain,records:BTreeMap::new(),pending:BTreeMap::new(),next_action:0,notification:0}}
    pub fn check_capacity(&self,count:u64)->(out:Result<(),CheckError>)
        ensures out.is_ok()==(self.allocated() as nat+count<=u64::MAX),
            out.is_err() ==> out==Err(CheckError::Capacity),
    {if count>u64::MAX-self.next_action {Err(CheckError::Capacity)} else {Ok(())}}
    pub fn record(&self,consumer:usize,port:Port)->(out:Option<&Record>)
        ensures out.is_some()==self.rows().contains_key((consumer,port.key,port.realm)),
            out.is_some() ==> *out.unwrap()==self.rows()[(consumer,port.key,port.realm)],
    {self.records.get(&(consumer,port.key,port.realm))}
    pub fn records(&self)->(out:&BTreeMap<Key,Record>) ensures out@==self.rows(), {&self.records}
    pub fn pending(&self)->(out:&BTreeMap<u64,CheckAction>) ensures out@==self.outstanding(), {&self.pending}
    pub fn available(&self,consumer:usize,port:Port,publication:PublicationId)->(out:bool)
        ensures out==(self.rows().contains_key((consumer,port.key,port.realm)) && self.rows()[(consumer,port.key,port.realm)].publication==publication && self.rows()[(consumer,port.key,port.realm)].available),
    {match self.record(consumer,port) {Some(r)=>r.publication==publication && r.available,None=>false}}

    pub open spec fn needs_request(&self,key:Key,id:PublicationId)->bool {
        !self.rows().contains_key(key) || self.rows()[key].publication!=id || self.rows()[key].dirty
    }
    pub open spec fn requested_row(&self,key:Key,id:PublicationId)->Record {
        Record {publication:id,dirty:false,
            notification:if self.rows().contains_key(key) {self.rows()[key].notification} else {self.notified()},
            available:self.rows().contains_key(key) && self.rows()[key].publication==id && self.rows()[key].available,
            last_current:if self.rows().contains_key(key) && self.rows()[key].publication==id {self.rows()[key].last_current} else {None}}
    }
    pub proof fn eligible_unique(&self,control:&LifecycleState,store:&PublicationStore<u64>,consumer:usize,port:Port,a:PublicationId,b:PublicationId)
        requires store.wf(),self.eligible(control,store,consumer,port,a),self.eligible(control,store,consumer,port,b),
        ensures a==b,
    {
        store.visible_unique(a,b);
    }

    /// The request value and version are read here, never supplied by a caller.
    pub fn request(&mut self,control:&LifecycleState,store:&PublicationStore<u64>,consumer:usize,port:Port)->(out:Result<Option<CheckAction>,CheckError>)
        requires old(self).wf(),control.wf(),store.wf(),
        ensures final(self).wf(),final(self).domain_id()==old(self).domain_id(),final(self).notified()==old(self).notified(),
            out.is_err() || out==Ok(None) ==> *final(self)==*old(self),
            out.is_err() ==> out==Err(CheckError::Capacity) && old(self).allocated()==u64::MAX,
            forall|id:PublicationId|old(self).eligible(control,store,consumer,port,id) && old(self).needs_request((consumer,port.key,port.realm),id) ==>
                if old(self).allocated()<u64::MAX {out.is_ok() && out->Ok_0.is_some() && out->Ok_0.unwrap().ticket.publication==id} else {out==Err(CheckError::Capacity)},
            out.is_ok() && out->Ok_0.is_some() ==> {
                let a=out->Ok_0.unwrap();let t=a.ticket;
                &&& t.consumer==consumer && t.port==port && t.domain==old(self).domain_id()
                &&& t.action==old(self).allocated() && final(self).allocated()==old(self).allocated()+1
                &&& final(self).outstanding()==old(self).outstanding().insert(t.action,a)
                &&& final(self).fresh(t,control,store)
                &&& store.values()[t.publication.0 as int]==Some(a.value)
                &&& t.publication.0<store.revisions().len()
                &&& store.revisions()[t.publication.0 as int]==t.value_revision
                &&& final(self).rows()==old(self).rows().insert(t.key(),old(self).requested_row(t.key(),t.publication))
            },
    {
        let ghost prior=*self;
        let id=match store.registry().resolve(port) {None=>return Ok(None),Some(id)=>id};
        proof {
            assert forall|other:PublicationId|self.eligible(control,store,consumer,port,other) implies other==id by {
                store.visible_unique(other,id);
            }
        }
        if !self.eligible_now(control,store,consumer,port,id) {return Ok(None);}
        proof {store.visible_value(id);}
        let (revision,value)=match store.observation(id) {None=>return Ok(None),Some(pair)=>pair};
        let key=(consumer,port.key,port.realm);
        let mut row=match self.records.get(&key) {
            Some(row)=>*row,
            None=>Record {publication:id,notification:self.notification,dirty:true,available:false,last_current:None},
        };
        if row.publication!=id {row.publication=id;row.dirty=true;row.available=false;row.last_current=None;}
        if !row.dirty {return Ok(None);}
        assert(row.notification<=self.notified());
        if self.next_action==u64::MAX {return Err(CheckError::Capacity);}
        row.dirty=false;
        let ticket=CheckTicket {domain:self.domain,consumer,port,publication:id,value_revision:revision,notification:row.notification,action:self.next_action};
        let action=CheckAction {ticket,value:*value};
        self.next_action+=1;
        self.records.insert(key,row);self.pending.insert(ticket.action,action);
        proof {
            assert forall|id:u64|self.outstanding().contains_key(id) implies {
                let t=self.outstanding()[id].ticket;
                t.action==id && id<self.allocated() && t.domain==self.domain_id() && t.notification<=self.notified()
            } by {if id!=ticket.action {assert(prior.outstanding().contains_key(id));}}
            assert forall|k:Key|self.rows().contains_key(k) implies self.rows()[k].notification<=self.notified() by {
                if k!=key {assert(prior.rows().contains_key(k));}
            }
            assert(self.rows().remove(key) =~= prior.rows().remove(key));
            assert(row==prior.requested_row(key,id));
            assert(self.fresh(ticket,control,store));
        }
        Ok(Some(action))
    }
    pub fn current(&self,t:CheckTicket,control:&LifecycleState,store:&PublicationStore<u64>)->(out:bool)
        requires self.wf(),control.wf(),store.wf(),
        ensures out==self.fresh(t,control,store),
    {
        let issued=match self.pending.get(&t.action) {None=>return false,Some(a)=>a};
        if issued.ticket!=t || !self.eligible_now(control,store,t.consumer,t.port,t.publication) {return false;}
        let (revision,value)=match store.observation(t.publication) {None=>return false,Some(pair)=>pair};
        if revision!=t.value_revision || *value!=issued.value {return false;}
        match self.record(t.consumer,t.port) {None=>false,Some(r)=>r.publication==t.publication && r.notification==t.notification && !r.dirty}
    }
    pub open spec fn completion_row(&self,t:CheckTicket)->bool {
        self.rows().contains_key(t.key()) && self.rows()[t.key()].publication==t.publication && self.rows()[t.key()].notification==t.notification
    }
    pub fn complete(&mut self,t:CheckTicket,control:&LifecycleState,store:&PublicationStore<u64>,available:bool)->(out:Result<bool,CheckError>)
        requires old(self).wf(),control.wf(),store.wf(),
        ensures final(self).wf(),final(self).domain_id()==old(self).domain_id(),final(self).allocated()==old(self).allocated(),final(self).notified()==old(self).notified(),
            out.is_ok()==old(self).recorded(t),
            out.is_err() ==> *final(self)==*old(self) && out==Err(CheckError::Stale),
            out.is_ok() ==> out->Ok_0==old(self).fresh(t,control,store)
                && final(self).outstanding()==old(self).outstanding().remove(t.action)
                && final(self).rows()==if old(self).completion_row(t) {
                    old(self).rows().insert(t.key(),Record {available:out->Ok_0 && available,last_current:Some(out->Ok_0),..old(self).rows()[t.key()]})
                } else {old(self).rows()},
    {
        match self.pending.get(&t.action) {Some(a) if a.ticket==t=>{},_=>return Err(CheckError::Stale)}
        let current=self.current(t,control,store);
        self.pending.remove(&t.action);
        let key=(t.consumer,t.port.key,t.port.realm);
        if let Some(row)=self.records.get(&key) {
            let mut row=*row;
            if row.publication==t.publication && row.notification==t.notification {
                row.last_current=Some(current);row.available=current && available;self.records.insert(key,row);
            }
        }
        Ok(current)
    }
    fn keys(&self)->(out:Vec<Key>) ensures out@.to_set()==self.rows().dom(),out@.no_duplicates(),
    {
        let mut out=Vec::new();let keys=self.records.keys();let ghost all=keys.remaining();let _count=self.records.len();
        proof {all.unref().unique_seq_to_set();assert(all.len()==_count);}
        for key in iter: keys
            invariant all==iter.seq(),_count==all.len(),out@==iter.seq().take(iter.index()).unref(),
            decreases _count as int-out.len() as int,
        {out.push(*key);}
        assert(out@==all.unref());out
    }
    fn selected(ports:&[Port],key:Key)->(out:bool)
        ensures out==ports@.contains(Port {key:key.1,realm:key.2}),
    {
        let mut i=0;
        while i<ports.len()
            invariant i<=ports.len(),forall|j:int|0<=j<i ==> ports[j]!=(Port {key:key.1,realm:key.2}),
            decreases ports.len()-i,
        {if ports[i].key==key.1 && ports[i].realm==key.2 {return true;}i+=1;}
        false
    }
    pub fn notify(&mut self,ports:&[Port])->(out:Result<(),CheckError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).domain_id()==old(self).domain_id(),final(self).allocated()==old(self).allocated(),final(self).outstanding()==old(self).outstanding(),
            out.is_ok()==(old(self).notified()<u64::MAX),out.is_err() ==> *final(self)==*old(self),
            out.is_err() ==> out==Err(CheckError::Capacity),
            out.is_ok() ==> final(self).notified()==old(self).notified()+1 && final(self).rows().dom()==old(self).rows().dom()
                && (forall|key:Key|old(self).rows().contains_key(key) ==> final(self).rows()[key]==if ports@.contains(Port {key:key.1,realm:key.2}) {
                    Record {notification:final(self).notified(),dirty:true,..old(self).rows()[key]}
                } else {old(self).rows()[key]}),
    {
        if self.notification==u64::MAX {return Err(CheckError::Capacity);}
        let ghost prior=self.rows();let keys=self.keys();let mut i=0;
        self.notification+=1;
        while i<keys.len()
            invariant i<=keys.len(),keys@.to_set()==prior.dom(),keys@.no_duplicates(),self.rows().dom()==prior.dom(),
                self.domain_id()==old(self).domain_id(),self.allocated()==old(self).allocated(),self.outstanding()==old(self).outstanding(),self.notified()==old(self).notified()+1,
                forall|key:Key|prior.contains_key(key) ==> self.rows()[key]==if keys@.take(i as int).contains(key) && ports@.contains(Port {key:key.1,realm:key.2}) {
                    Record {notification:self.notified(),dirty:true,..prior[key]}
                } else {prior[key]},
            decreases keys.len()-i,
        {
            let key=keys[i];
            assert(!keys@.take(i as int).contains(key));
            if Self::selected(ports,key) {let mut row=*self.records.get(&key).unwrap();row.notification=self.notification;row.dirty=true;self.records.insert(key,row);}
            proof {
                assert(keys@.take(i as int+1)==keys@.take(i as int).push(key));
                assert forall|k:Key|prior.contains_key(k) implies self.rows()[k]==if keys@.take(i as int+1).contains(k) && ports@.contains(Port {key:k.1,realm:k.2}) {
                    Record {notification:self.notified(),dirty:true,..prior[k]}
                } else {prior[k]} by {if k==key {} }
            }
            i+=1;
        }
        assert(keys@.take(i as int)==keys@);
        Ok(())
    }
    pub fn remove_consumer(&mut self,consumer:usize)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).domain_id()==old(self).domain_id(),final(self).allocated()==old(self).allocated(),final(self).notified()==old(self).notified(),final(self).outstanding()==old(self).outstanding(),
            final(self).rows()==old(self).rows().restrict(old(self).rows().dom().filter(|key:Key|key.0!=consumer)),
    {
        let ghost prior=self.rows();let keys=self.keys();let mut i=0;
        while i<keys.len()
            invariant i<=keys.len(),keys@.to_set()==prior.dom(),keys@.no_duplicates(),
                self.domain_id()==old(self).domain_id(),self.allocated()==old(self).allocated(),self.outstanding()==old(self).outstanding(),self.notified()==old(self).notified(),
                self.rows()==prior.restrict(prior.dom().filter(|key:Key|key.0!=consumer || !keys@.take(i as int).contains(key))),
            decreases keys.len()-i,
        {
            let key=keys[i];if key.0==consumer {self.records.remove(&key);}
            proof {
                assert(keys@.take(i as int+1)==keys@.take(i as int).push(key));
                assert(self.rows() =~= prior.restrict(prior.dom().filter(|k:Key|k.0!=consumer || !keys@.take(i as int+1).contains(k))));
            }
            i+=1;
        }
        assert(keys@.take(i as int)==keys@);
        assert(self.rows() =~= prior.restrict(prior.dom().filter(|key:Key|key.0!=consumer)));
    }
}
}
