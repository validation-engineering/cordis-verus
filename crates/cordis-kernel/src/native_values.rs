//! Native service snapshots are captured from actual committed providers.
//! Finish publishes the episode's actual slots; Unload closes and transfers
//! them only after the real work and cleanup owners drain. Arc referents remain
//! opaque: interior mutation, host mutexes and user availability predicates are
//! outside these sequential contracts.
#[path = "native_capture.rs"]
pub mod capture;
#[path = "native_slot_observation.rs"]
pub mod slots;
use super::{registration::RegisteredPlugin, LifecycleState};
#[cfg(verus_keep_ghost)]
use crate::action_ledger::ActionKind;
use crate::action_ledger::ActionTicket;
use crate::cleanup_groups::CleanupGroups;
use crate::lifecycle_actions::CleanupOutcome;
use crate::realm_context::RealmContext;
use crate::setup_work::SetupWork;
#[cfg(verus_keep_ghost)]
use crate::Phase;
use crate::{Binding, Error, Port};
use capture::Capture;
use std::collections::BTreeMap;
use std::sync::Arc;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;

#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum NativeValueError { Closed, Undeclared, Duplicate, Missing }
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub struct NativeReadError { pub reason:NativeValueError,pub provider:Option<usize> }

#[allow(dead_code)] // Begin provenance is erased from the executable.
pub struct NativePublication<T> { origin:ActionTicket,values:BTreeMap<(u64,u64),Arc<T>>,capture:Ghost<Capture<T>> }
impl<T> NativePublication<T> {
    pub closed spec fn capture(&self)->Capture<T> {self.capture@}
    pub closed spec fn origin(&self)->ActionTicket {self.origin}
    pub closed spec fn values(&self)->Map<(u64,u64),Arc<T>> {self.values@}
}
pub struct NativeServices<T> {domain:u64,entries:BTreeMap<usize,NativePublication<T>>}
impl<T> NativeServices<T> {
    pub closed spec fn domain_id(&self)->u64 {self.domain}
    pub closed spec fn entries(&self)->Map<usize,NativePublication<T>> {self.entries@}
    pub open spec fn wf(&self)->bool {
        forall|id:usize| #[trigger] self.entries().contains_key(id) ==>
            self.entries()[id].origin().domain==self.domain_id() && self.entries()[id].origin().id==id
                && self.entries()[id].origin().kind==ActionKind::Setup
                && self.entries()[id].capture().wf() && self.entries()[id].capture().origin==self.entries()[id].origin()
    }
    pub fn new(domain:u64)->(out:Self)
        ensures out.wf(),out.domain_id()==domain,out.entries()==Map::empty(),
    {Self {domain,entries:BTreeMap::new()}}
    pub fn value_count(&self)->(out:usize) {
        let mut count:usize=0;
        for key in self.entries.keys() {count=count.saturating_add(self.entries.get(key).unwrap().values.len());}
        count
    }
    pub fn has_publications(&self)->(out:bool) ensures out==!self.entries().is_empty(), {!self.entries.is_empty()}
    pub open spec fn available(&self,state:&LifecycleState,provider:usize,port:Port)->bool {
        self.domain_id()==state.protocol().domain_id() && self.entries().contains_key(provider)
            && state.control().generation_of(provider)==Some(self.entries()[provider].origin().generation)
            && self.entries()[provider].values().contains_key((port.key,port.realm))
    }
    fn retained<'a>(&'a self,state:&LifecycleState,provider:usize,port:Port)->(out:Option<&'a Arc<T>>)
        requires self.wf(),state.wf(),
        ensures out.is_some()==self.available(state,provider,port),
            out.is_some() ==> *out.unwrap()==self.entries()[provider].values()[(port.key,port.realm)],
    {
        if self.domain!=state.domain() {return None;}
        let entry=self.entries.get(&provider)?;
        if state.kernel().episode_generation(provider)!=Some(entry.origin.generation) {return None;}
        entry.values.get(&(port.key,port.realm))
    }
    pub fn visible<'a>(&'a self,state:&LifecycleState,port:Port)->(out:Option<&'a Arc<T>>)
        requires self.wf(),state.wf(),
        ensures out.is_some()==(exists|id:usize| state.control().resolves_to(port,id) && self.available(state,id,port)),
            out.is_some() ==> exists|id:usize| state.control().resolves_to(port,id)
            && self.available(state,id,port) && *out.unwrap()==self.entries()[id].values()[(port.key,port.realm)],
    {
        let provider=match state.kernel().resolve(port) {Some(provider)=>provider,None=>{
            proof {reveal(crate::Kernel::resolves_to);reveal(crate::Kernel::has_provider);}
            return None;
        }};
        let out=self.retained(state,provider,port);
        proof {assert forall|id:usize| state.control().resolves_to(port,id) && self.available(state,id,port)
            implies out.is_some() by {state.control().resolution_unique(port,id,provider);}}
        out
    }
}

/// Immutable metadata issued by the real native Begin capture. Sharing this
/// owner cannot retain a service payload or alter a committed provider.
pub struct NativeContext {
    origin:ActionTicket,work_domain:u64,realms:RealmContext,anchor:Port,provisions:Vec<Port>,bindings:Vec<Binding>,
}
impl NativeContext {
    pub closed spec fn origin(&self)->ActionTicket {self.origin}
    pub closed spec fn domain_id(&self)->u64 {self.work_domain}
    pub closed spec fn realms(&self)->Map<u64,u64> {self.realms.mapping()}
    pub closed spec fn anchor_port(&self)->Port {self.anchor}
    pub fn realm_context(&self)->(out:RealmContext) ensures out.mapping()==self.realms(), {self.realms.clone()}
    pub fn anchor(&self)->(out:Port) ensures out==self.anchor_port(), {self.anchor}
    pub closed spec fn provisions(&self)->Seq<Port> {self.provisions@}
    pub closed spec fn bindings(&self)->Seq<Binding> {self.bindings@}
    pub open spec fn describes<T>(&self,capture:Capture<T>)->bool {
        self.origin()==capture.origin && self.domain_id()==capture.work_domain
            && self.realms()==capture.realms && self.anchor_port()==capture.anchor
            && self.provisions()==capture.provisions && self.bindings()==capture.bindings
    }
    pub fn ticket(&self)->(out:ActionTicket) ensures out==self.origin(), {self.origin}
    pub fn owner(&self)->(out:usize) ensures out==self.origin().id, {self.origin.id}
    pub fn work_domain(&self)->(out:u64) ensures out==self.domain_id(), {self.work_domain}
    pub fn provision_ports(&self)->(out:&[Port]) ensures out@==self.provisions(), {self.provisions.as_slice()}
    pub fn committed(&self)->(out:&[Binding]) ensures out@==self.bindings(), {self.bindings.as_slice()}
    pub fn committed_vec(&self)->(out:Vec<Binding>) ensures out@==self.bindings(), {self.bindings.clone()}
}

#[allow(dead_code)] // The immutable Begin snapshot is proof data only.
pub struct NativeEpisode<T> {
    capture:Ghost<Capture<T>>,
    context:Arc<NativeContext>,
    owned:BTreeMap<(u64,u64),Arc<T>>,imports:BTreeMap<(usize,u64,u64),Arc<T>>,closed:bool,
}
impl<T> NativeEpisode<T> {
    pub closed spec fn domain_id(&self)->u64 {self.context.work_domain}
    pub fn cleanup_domain(&self)->(out:u64) ensures out==self.domain_id(), {self.context.work_domain}
    pub closed spec fn capture(&self)->Capture<T> {self.capture@}
    pub closed spec fn context_spec(&self)->NativeContext {*self.context}
    /// Clones only immutable identities and declarations; never retains slots.
    pub fn setup_context(&self)->(out:Arc<NativeContext>)
        requires self.wf(),
        ensures *out==self.context_spec(),out.describes(self.capture()),
    {self.context.clone()}
    pub closed spec fn origin(&self)->ActionTicket {self.context.origin}
    pub closed spec fn provisions(&self)->Seq<Port> {self.context.provisions@}
    pub closed spec fn bindings(&self)->Seq<Binding> {self.context.bindings@}
    pub closed spec fn owned(&self)->Map<(u64,u64),Arc<T>> {self.owned@}
    pub closed spec fn imports(&self)->Map<(usize,u64,u64),Arc<T>> {self.imports@}
    pub open spec fn owned_table(&self)->IMap<Port,Arc<T>> {
        IMap::new(|p:Port| self.owned().contains_key((p.key,p.realm)),|p:Port|self.owned()[(p.key,p.realm)])
    }
    pub closed spec fn closed(&self)->bool {self.closed}
    pub open spec fn wf(&self)->bool {
        &&& self.origin().kind==ActionKind::Setup
        &&& self.capture().wf() && self.capture().origin==self.origin() && self.capture().work_domain==self.domain_id()
        &&& self.capture().provisions==self.provisions() && self.capture().bindings==self.bindings()
        &&& self.context_spec().describes(self.capture())
        &&& !self.closed() ==> self.imports()==self.capture().imports
        &&& forall|key:(u64,u64)| #[trigger] self.owned().contains_key(key) ==> self.provisions().contains(Port {key:key.0,realm:key.1})
        &&& forall|key:(usize,u64,u64)| #[trigger] self.imports().contains_key(key) ==> self.bindings().contains(Binding {provider:key.0,key:key.1,realm:key.2})
        &&& self.closed() ==> self.owned().is_empty() && self.imports().is_empty()
    }
    pub open spec fn same_identity(&self,prior:&Self)->bool {
        self.context_spec()==prior.context_spec() && self.domain_id()==prior.domain_id() && self.capture()==prior.capture() && self.origin()==prior.origin() && self.provisions()==prior.provisions() && self.bindings()==prior.bindings()
    }
    /// Every live read still uses Begin's provider and shared slot. A closed
    /// owner keeps its proof origin, but no executable imported references.
    pub proof fn capture_correspondence(&self)
        requires self.wf(),
        ensures self.capture().wf(),self.origin()==self.capture().origin,
            self.provisions()==self.capture().provisions,self.bindings()==self.capture().bindings,
            !self.closed() ==> self.imports()==self.capture().imports,
            self.closed() ==> self.imports().is_empty() && self.owned().is_empty(),
    {}
    /// Validate the actual declaration sequence at the publication boundary.
    /// Even a separately constructed owner with colliding numeric origins must
    /// not publish a different interface into this registry.
    pub fn matches_provisions(&self,ports:&[Port])->(out:bool)
        ensures out==(self.provisions()==ports@),
    {
        if self.context.provisions.len()!=ports.len() {return false;}
        let mut i=0;
        while i<ports.len()
            invariant self.context.provisions.len()==ports.len(),i<=ports.len(),
                forall|j:int| 0<=j<i ==> self.context.provisions@[j]==ports@[j],
            decreases ports.len()-i,
        {if self.context.provisions[i]!=ports[i] {return false;}i+=1;}
        assert(self.provisions() =~= ports@);true
    }
    pub fn ticket(&self)->(out:ActionTicket) ensures out==self.origin(), {self.context.origin}
    pub fn is_closed(&self)->(out:bool) ensures out==self.closed(), {self.closed}
    fn declares(&self,port:Port)->(out:bool) ensures out==self.provisions().contains(port), {
        let mut i=0;
        while i<self.context.provisions.len()
            invariant i<=self.context.provisions.len(),forall|j:int| 0<=j<i ==> self.context.provisions@[j]!=port,
            decreases self.context.provisions.len()-i,
        {if self.context.provisions[i]==port {return true;}i+=1;}
        false
    }
    pub fn provide(&mut self,port:Port,value:Arc<T>)->(out:Result<(),(NativeValueError,Arc<T>)>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).same_identity(old(self)),final(self).closed()==old(self).closed(),
            final(self).imports()==old(self).imports(),
            out.is_ok()==(!old(self).closed() && old(self).provisions().contains(port) && !old(self).owned().contains_key((port.key,port.realm))),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0.1==value,
            out.is_ok() ==> final(self).owned()==old(self).owned().insert((port.key,port.realm),value)
                && final(self).owned_table()==crate::coeffects::put(old(self).owned_table(),port,Some(value)),
    {
        if self.closed {return Err((NativeValueError::Closed,value));}
        if !self.declares(port) {return Err((NativeValueError::Undeclared,value));}
        if self.owned.contains_key(&(port.key,port.realm)) {return Err((NativeValueError::Duplicate,value));}
        let ghost prior=*self;
        self.owned.insert((port.key,port.realm),value);
        proof {assert forall|key:(u64,u64)| #[trigger] self.owned().contains_key(key) implies self.provisions().contains(Port {key:key.0,realm:key.1}) by {
            if key==(port.key,port.realm) {assert(Port {key:key.0,realm:key.1}==port);}
            else {assert(prior.owned().contains_key(key));}
        }
        assert(self.origin().kind==ActionKind::Setup);
        assert(!self.closed());
        assert(self.owned_table() =~= prior.owned_table().insert(port,value)) by {
            assert forall|p:Port| self.owned_table().dom().contains(p)==prior.owned_table().insert(port,value).dom().contains(p) by {
                if (p.key,p.realm)==(port.key,port.realm) {assert(p==port);}
            }
            assert forall|p:Port| self.owned_table().dom().contains(p) implies self.owned_table()[p]==prior.owned_table().insert(port,value)[p] by {
                if p!=port {assert((p.key,p.realm)!=(port.key,port.realm));}
            }
        }
        assert forall|key:(usize,u64,u64)| #[trigger] self.imports().contains_key(key) implies self.bindings().contains(Binding {provider:key.0,key:key.1,realm:key.2}) by {
            assert(prior.imports().contains_key(key));
        }
        }
        Ok(())
    }
    /// Validate the whole finite body's access set before its first effect.
    /// This checks Begin declarations, independently of current slot contents.
    pub fn declares_service(&self,port:Port)->(out:bool)
        ensures out==(self.provisions().contains(port) || exists|b:Binding| self.bindings().contains(b) && b.key==port.key && b.realm==port.realm),
    {
        let mut i=0;
        while i<self.context.provisions.len()
            invariant i<=self.context.provisions.len(),forall|j:int| 0<=j<i ==> self.provisions()[j]!=port,
            decreases self.context.provisions.len()-i,
        {if self.context.provisions[i]==port {return true;}i+=1;}
        assert(!self.provisions().contains(port));
        let mut j=0;
        while j<self.context.bindings.len()
            invariant j<=self.context.bindings.len(),!self.provisions().contains(port),
                forall|k:int| 0<=k<j ==> self.bindings()[k].key!=port.key || self.bindings()[k].realm!=port.realm,
            decreases self.context.bindings.len()-j,
        {
            let b=self.context.bindings[j];
            if b.key==port.key && b.realm==port.realm {assert(self.bindings().contains(b));return true;}
            j+=1;
        }
        assert forall|b:Binding| self.bindings().contains(b) implies b.key!=port.key || b.realm!=port.realm by {
            let k=choose|k:int| 0<=k<self.bindings().len() && self.bindings()[k]==b;
        }
        false
    }
    pub fn own(&self,port:Port)->(out:Option<&Arc<T>>)
        ensures out.is_some()==(!self.closed() && self.owned().contains_key((port.key,port.realm))),
            out.is_some() ==> *out.unwrap()==self.owned()[(port.key,port.realm)],
    {if self.closed {None} else {self.owned.get(&(port.key,port.realm))}}
    pub open spec fn selects_value(&self,provider:usize,port:Port,value:Arc<T>)->bool {
        !self.closed() && if self.provisions().contains(port) {provider==self.origin().id && self.owned().contains_key((port.key,port.realm)) && self.owned()[(port.key,port.realm)]==value}
        else {self.bindings().contains(Binding {provider,key:port.key,realm:port.realm}) && self.imports().contains_key((provider,port.key,port.realm)) && self.imports()[(provider,port.key,port.realm)]==value}
    }
    pub open spec fn read_failed(&self,port:Port,error:NativeReadError)->bool {
        match error.reason {
            NativeValueError::Closed=>self.closed() && error.provider.is_none(),
            NativeValueError::Undeclared=>!self.closed() && error.provider.is_none() && !self.provisions().contains(port)
                && !exists|b:Binding|self.bindings().contains(b) && b.key==port.key && b.realm==port.realm,
            NativeValueError::Missing=>!self.closed() && error.provider.is_some() && if self.provisions().contains(port) {
                error.provider==Some(self.origin().id) && !self.owned().contains_key((port.key,port.realm))
            } else {self.bindings().contains(Binding {provider:error.provider.unwrap(),key:port.key,realm:port.realm}) && !self.imports().contains_key((error.provider.unwrap(),port.key,port.realm))},
            NativeValueError::Duplicate=>false,
        }
    }
    pub fn read(&self,port:Port)->(out:Result<(usize,&Arc<T>),NativeReadError>)
        requires self.wf(),
        ensures out.is_err() ==> self.read_failed(port,out->Err_0),
            out.is_ok() ==> self.selects_value(out->Ok_0.0,port,*out->Ok_0.1),
            out.is_ok() ==> !self.closed() && (
            (self.provisions().contains(port) && out->Ok_0.0==self.origin().id
                && self.owned().contains_key((port.key,port.realm)) && *out->Ok_0.1==self.owned()[(port.key,port.realm)])
            || (!self.provisions().contains(port) && self.bindings().contains(Binding {provider:out->Ok_0.0,key:port.key,realm:port.realm})
                && self.imports().contains_key((out->Ok_0.0,port.key,port.realm)) && *out->Ok_0.1==self.imports()[(out->Ok_0.0,port.key,port.realm)])),
            out.is_ok() && !self.provisions().contains(port) ==> self.capture().imports.contains_key((out->Ok_0.0,port.key,port.realm))
                && *out->Ok_0.1==self.capture().sources[out->Ok_0.0].values[(port.key,port.realm)],
            self.closed() ==> out==Err(NativeReadError {reason:NativeValueError::Closed,provider:None}),
    {
        if self.closed {return Err(NativeReadError {reason:NativeValueError::Closed,provider:None});}
        if self.declares(port) {
            return match self.owned.get(&(port.key,port.realm)) {
                Some(value)=>Ok((self.context.origin.id,value)),
                None=>Err(NativeReadError {reason:NativeValueError::Missing,provider:Some(self.context.origin.id)}),
            };
        }
        let mut i=0;
        while i<self.context.bindings.len()
            invariant i<=self.context.bindings.len(),forall|j:int|0<=j<i ==> (#[trigger] self.bindings()[j]).key!=port.key || self.bindings()[j].realm!=port.realm,!self.closed(),!self.provisions().contains(port),self.wf(),
            decreases self.context.bindings.len()-i,
        {
            let b=self.context.bindings[i];
            if b.key==port.key && b.realm==port.realm {
                assert(self.bindings().contains(b));
                return match self.imports.get(&(b.provider,port.key,port.realm)) {
                    Some(value)=>Ok((b.provider,value)),
                    None=>Err(NativeReadError {reason:NativeValueError::Missing,provider:Some(b.provider)}),
                };
            }
            i+=1;
        }
        assert forall|b:Binding|self.bindings().contains(b) implies b.key!=port.key || b.realm!=port.realm by {
            let j=choose|j:int|0<=j<self.bindings().len() && self.bindings()[j]==b;
        }
        Err(NativeReadError {reason:NativeValueError::Undeclared,provider:None})
    }
    pub open spec fn complete(&self)->bool {
        forall|p:Port| self.provisions().contains(p) ==> self.owned().contains_key((p.key,p.realm))
    }
    pub fn missing(&self)->(out:Option<Port>)
        ensures out.is_none()==self.complete(),out.is_some() ==> self.provisions().contains(out.unwrap())
            && !self.owned().contains_key((out.unwrap().key,out.unwrap().realm)),
    {
        let mut i=0;
        while i<self.context.provisions.len()
            invariant i<=self.context.provisions.len(),forall|j:int| 0<=j<i ==> self.owned().contains_key((self.context.provisions@[j].key,self.context.provisions@[j].realm)),
            decreases self.context.provisions.len()-i,
        {
            let p=self.context.provisions[i];
            if !self.owned.contains_key(&(p.key,p.realm)) {assert(self.provisions().contains(p));return Some(p);}
            i+=1;
        }
        None
    }
}

/// Move these values outside host bookkeeping locks before destruction.
pub struct ReleasedNativeValues<T> {
    pub owned:BTreeMap<(u64,u64),Arc<T>>,pub imports:BTreeMap<(usize,u64,u64),Arc<T>>,pub published:Option<NativePublication<T>>,
}
impl<T> ReleasedNativeValues<T> {
    pub closed spec fn owned(&self)->Map<(u64,u64),Arc<T>> {self.owned@}
    pub closed spec fn imports(&self)->Map<(usize,u64,u64),Arc<T>> {self.imports@}
    pub closed spec fn published(&self)->Option<NativePublication<T>> {self.published}
}

impl LifecycleState {
    /// This is the only public constructor of a native value owner. A second
    /// owner cannot be captured from an already admitted work ticket.
    #[allow(clippy::type_complexity)]
    pub fn begin_native_execution<T,C,G,I,R>(&mut self,store:&NativeServices<T>,registration:&RegisteredPlugin<R>,cleanup_domain:u64)
        ->(out:Result<(SetupWork<C,G>,CleanupGroups<I>,NativeEpisode<T>),Error>)
        requires old(self).wf(),store.wf(),
        ensures out.is_ok() ==> out->Ok_0.0.link().is_none() && out->Ok_0.1.execution_journal().is_none() && out->Ok_0.1.queues().dom()==set![0usize],(forall|n:usize| n!=registration.owner() ==> final(self).control().generation_of(n)==old(self).control().generation_of(n)), out.is_ok() ==> out->Ok_0.0.accepts(), out.is_ok() ==> !out->Ok_0.0.is_closed() && !out->Ok_0.1.closed(), final(self).wf(),final(self).protocol().domain_id()==old(self).protocol().domain_id(),
            out.is_ok()==(store.domain_id()==old(self).protocol().domain_id() && registration.domain_id()==old(self).protocol().domain_id()
                && !store.entries().contains_key(registration.owner())
                && old(self).protocol().admission_enabled(registration.owner()) && old(self).control().begin_enabled(registration.owner())),
            out.is_err() ==> final(self).same(old(self)),
            out.is_ok() ==> out->Ok_0.0.wf() && out->Ok_0.0.domain_id()==cleanup_domain && out->Ok_0.1.wf() && out->Ok_0.2.wf()
                && !out->Ok_0.2.closed() && out->Ok_0.2.owned()==Map::empty()
                && Some(out->Ok_0.2.origin())==out->Ok_0.0.origin()
                && final(self).execution_matches(registration.owner(),&out->Ok_0.0,&out->Ok_0.1)
                && final(self).protocol().recorded(out->Ok_0.2.origin())
                && out->Ok_0.2.capture().control==final(self).control()
                && out->Ok_0.2.capture().sources==capture::sources(store.entries()) && out->Ok_0.2.capture().work_domain==cleanup_domain
                && out->Ok_0.2.provisions()==registration.provisions_spec()
                && out->Ok_0.2.capture().realms==registration.realms() && out->Ok_0.2.capture().anchor==registration.anchor_port()
                && (forall|b:Binding| out->Ok_0.2.bindings().contains(b)==final(self).control().binding_recorded(registration.owner(),b))
                && (forall|key:(usize,u64,u64)| #[trigger] out->Ok_0.2.imports().contains_key(key)==(out->Ok_0.2.bindings().contains(Binding {provider:key.0,key:key.1,realm:key.2})
                    && store.available(final(self),key.0,Port {key:key.1,realm:key.2})))
                && (forall|key:(usize,u64,u64)| #[trigger] out->Ok_0.2.imports().contains_key(key) ==>
                    out->Ok_0.2.imports()[key]==store.entries()[key.0].values()[(key.1,key.2)])
                && crate::refinement::step(old(self).control().paper(),final(self).control().paper(),registration.owner(),crate::refinement::Rule::Begin),
    {
        proof {reveal(crate::Kernel::unchanged);self.actions.same_reflexive();}
        if store.domain!=self.domain() || registration.domain_id_exec()!=self.domain() || store.entries.contains_key(&registration.id()) {return Err(Error::InvalidState);}
        let ticket=self.begin(registration.id())?;
        let work=SetupWork::for_lifecycle(ticket,cleanup_domain);
        let groups=CleanupGroups::for_lifecycle(ticket,cleanup_domain);
        let values=self.capture_native_values(store,&work,registration);
        Ok((work,groups,values))
    }
    fn capture_native_values<T,C,G,R>(&self,store:&NativeServices<T>,work:&SetupWork<C,G>,registration:&RegisteredPlugin<R>)
        ->(out:NativeEpisode<T>)
        requires self.wf(),store.wf(),store.domain_id()==self.protocol().domain_id(),work.wf(),work.origin().is_some(),
            work.origin().unwrap().domain==self.protocol().domain_id(),work.origin().unwrap().id==registration.owner(),
            self.control().generation_of(registration.owner())==Some(work.origin().unwrap().generation),
        ensures out.wf() && !out.closed() && out.owned()==Map::empty()
            && Some(out.origin())==work.origin() && out.origin().domain==self.protocol().domain_id()
            && out.origin().id==registration.owner() && self.control().generation_of(registration.owner())==Some(out.origin().generation)
            && out.capture().control==self.control() && out.capture().sources==capture::sources(store.entries())
            && out.capture().work_domain==work.domain_id()
            && out.provisions()==registration.provisions_spec()
            && out.capture().realms==registration.realms() && out.capture().anchor==registration.anchor_port()
            && (forall|b:Binding| out.bindings().contains(b)==self.control().binding_recorded(registration.owner(),b))
            && (forall|key:(usize,u64,u64)| #[trigger] out.imports().contains_key(key)==(out.bindings().contains(Binding {provider:key.0,key:key.1,realm:key.2})
                && store.available(self,key.0,Port {key:key.1,realm:key.2})))
            && (forall|key:(usize,u64,u64)| #[trigger] out.imports().contains_key(key) ==>
                store.available(self,key.0,Port {key:key.1,realm:key.2}) && out.imports()[key]==store.entries()[key.0].values()[(key.1,key.2)]),
    {
        let ticket=work.lifecycle_ticket().unwrap();
        let bindings=self.kernel.committed(ticket.id);
        let mut imports=BTreeMap::new();let mut i=0;
        while i<bindings.len()
            invariant i<=bindings.len(),self.wf(),store.wf(),
                forall|j:int| 0<=j<i && store.available(self,bindings@[j].provider,Port {key:bindings@[j].key,realm:bindings@[j].realm}) ==>
                    imports@.contains_key((bindings@[j].provider,bindings@[j].key,bindings@[j].realm)),
                forall|key:(usize,u64,u64)| #[trigger] imports@.contains_key(key) ==> bindings@.contains(Binding {provider:key.0,key:key.1,realm:key.2})
                    && store.available(self,key.0,Port {key:key.1,realm:key.2}) && imports@[key]==store.entries()[key.0].values()[(key.1,key.2)],
            decreases bindings.len()-i,
        {
            let b=bindings[i];
            if let Some(value)=store.retained(self,b.provider,Port {key:b.key,realm:b.realm}) {
                assert(bindings@.contains(b));imports.insert((b.provider,b.key,b.realm),value.clone());
            }
            i+=1;
        }
        proof {assert forall|key:(usize,u64,u64)| #[trigger] imports@.contains_key(key)==(bindings@.contains(Binding {provider:key.0,key:key.1,realm:key.2})
            && store.available(self,key.0,Port {key:key.1,realm:key.2})) by {
            if bindings@.contains(Binding {provider:key.0,key:key.1,realm:key.2}) {
                let j=choose|j:int| 0<=j<bindings.len() && bindings@[j]==(Binding {provider:key.0,key:key.1,realm:key.2});
                assert(bindings@[j].provider==key.0 && bindings@[j].key==key.1 && bindings@[j].realm==key.2);
            }
        }}
        let provisions=registration.provisions_vec();let realms=registration.realm_context();let anchor=registration.anchor();
        let ghost capture=Capture {origin:ticket,work_domain:work.domain_id(),realms:realms.mapping(),anchor,control:self.control(),
            provisions:provisions@,bindings:bindings@,imports:imports@,sources:capture::sources(store.entries())};
        proof {
            assert forall|key:(usize,u64,u64)| #[trigger] capture.imports.contains_key(key) implies
                capture.imports[key]==capture.sources[key.0].values[(key.1,key.2)] by {
                assert(imports@[key]==store.entries()[key.0].values()[(key.1,key.2)]);
            }
            assert(capture.wf());
        }
        NativeEpisode {context:Arc::new(NativeContext {origin:ticket,work_domain:work.domain(),realms,anchor,provisions,bindings}),owned:BTreeMap::new(),imports,closed:false,capture:Ghost(capture)}
    }
    fn native_values_match<T,C,G>(&self,id:usize,store:&NativeServices<T>,values:&NativeEpisode<T>,work:&SetupWork<C,G>)->(out:bool)
        ensures out==(store.domain_id()==self.protocol().domain_id() && Some(values.origin())==work.origin()
            && values.origin().domain==self.protocol().domain_id() && values.origin().id==id
            && values.domain_id()==work.domain_id() && !values.closed()),
    {store.domain==self.domain() && work.lifecycle_ticket()==Some(values.context.origin) && values.context.origin.domain==self.domain() && values.context.origin.id==id && values.context.work_domain==work.domain() && !values.closed}

    pub fn finish_native_execution<T,C,G,I>(&mut self,id:usize,store:&mut NativeServices<T>,values:&NativeEpisode<T>,work:&SetupWork<C,G>,groups:&CleanupGroups<I>)
        ->(out:Result<(),Error>)
        requires old(self).wf(),old(store).wf(),values.wf(),work.wf(),groups.wf(),
        ensures final(self).control().generations_preserved(&old(self).control()), final(self).wf(),final(self).protocol().domain_id()==old(self).protocol().domain_id(),final(store).wf(),final(store).domain_id()==old(store).domain_id(),
            out.is_err() ==> *final(store)==*old(store) && final(self).control().unchanged(&old(self).control()),
            out.is_ok() ==> values.domain_id()==work.domain_id() && old(self).execution_matches(id,work,groups) && values.complete() && !values.closed() && Some(values.origin())==work.origin()
                && values.origin().id==id && values.origin().domain==old(self).protocol().domain_id()
                && final(store).entries().dom()==old(store).entries().dom().insert(id)
                && final(store).entries()[id].origin()==values.origin() && final(store).entries()[id].values()==values.owned()
                && final(store).entries()[id].capture()==values.capture()
                && (forall|other:usize| other!=id && #[trigger] old(store).entries().contains_key(other) ==> final(store).entries()[other]==old(store).entries()[other])
                && final(self).control().phase_of(id)==Some(Phase::Active)
                && crate::refinement::step(old(self).control().paper(),final(self).control().paper(),id,crate::refinement::Rule::Finish),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        proof {reveal(crate::Kernel::unchanged);}
        if !self.native_values_match(id,store,values,work) || values.missing().is_some() || store.entries.contains_key(&id) {return Err(Error::InvalidState);}
        self.finish_execution(id,work,groups)?;
        store.entries.insert(id,NativePublication {origin:values.context.origin,values:values.owned.clone(),capture:Ghost(values.capture())});Ok(())
    }

    pub fn release_native_execution<T,C,G,I>(&mut self,id:usize,store:&mut NativeServices<T>,values:&mut NativeEpisode<T>,work:&mut SetupWork<C,G>,groups:&mut CleanupGroups<I>)
        ->(out:Result<(CleanupOutcome,ReleasedNativeValues<T>),Error>)
        requires old(self).wf(),old(store).wf(),old(values).wf(),old(work).wf(),old(groups).wf(),
        ensures final(work).link()==old(work).link(),final(groups).execution_journal()==old(groups).execution_journal(),final(self).control().generations_preserved(&old(self).control()), out.is_ok() ==> old(work).idle() && old(groups).all_drained(), final(work).origin()==old(work).origin(), final(work).domain_id()==old(work).domain_id(), final(groups).origin()==old(groups).origin(), final(self).wf(),final(self).protocol().domain_id()==old(self).protocol().domain_id(),final(store).wf(),final(values).wf(),final(work).wf(),final(groups).wf(),
            final(store).domain_id()==old(store).domain_id(),final(values).same_identity(old(values)),
            out.is_err() ==> final(self).same(old(self)) && *final(store)==*old(store) && *final(values)==*old(values)
                && *final(work)==*old(work) && *final(groups)==*old(groups),
            out.is_ok() ==> old(values).domain_id()==old(work).domain_id() && Some(old(values).origin())==old(work).origin() && old(values).origin().id==id
                && (old(store).entries().contains_key(id) ==> old(store).entries()[id].origin()==old(values).origin())
                && final(values).closed() && final(values).owned()==Map::empty() && final(values).imports()==Map::empty()
                && out->Ok_0.1.owned()==old(values).owned() && out->Ok_0.1.imports()==old(values).imports()
                && out->Ok_0.1.imports()==old(values).capture().imports
                && out->Ok_0.1.published()==if old(store).entries().contains_key(id) {Some(old(store).entries()[id])} else {None}
                && final(store).entries()==old(store).entries().remove(id)
                && final(work).is_closed() && final(groups).closed() && final(self).control().no_committed(id)
                && final(self).control().phase_of(id)==Some(Phase::Inactive)
                && out->Ok_0.0==if old(groups).drained_failure() {CleanupOutcome::Drained} else {CleanupOutcome::Succeeded}
                && crate::refinement::step(old(self).control().paper(),final(self).control().paper(),id,crate::refinement::Rule::Unload),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        proof {reveal(crate::Kernel::unchanged);self.actions.same_reflexive();}
        if !self.native_values_match(id,store,values,work) {return Err(Error::InvalidState);}
        if let Some(entry)=store.entries.get(&id) {if entry.origin!=values.context.origin {return Err(Error::InvalidState);}}
        let outcome=self.release_execution(id,work,groups)?;
        let published=store.entries.remove(&id);
        let mut owned=BTreeMap::new();core::mem::swap(&mut values.owned,&mut owned);
        let mut imports=BTreeMap::new();core::mem::swap(&mut values.imports,&mut imports);
        values.closed=true;
        Ok((outcome,ReleasedNativeValues {owned,imports,published}))
    }
}
}

#[path = "native_payload_observation.rs"]
pub mod payloads;
