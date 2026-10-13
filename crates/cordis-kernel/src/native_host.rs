//! Own the real native registrations and lifecycle graph in one checked state.
//! Mutable host bookkeeping is opaque, but cannot replace a registered recipe,
//! move it to another identity, or bypass the real Insert/Remove transitions.
#[path = "managed_native.rs"]
pub mod managed;
#[path = "native_runtime.rs"]
pub mod runtime;
use super::registration::child::ChildSlot;
#[cfg(verus_keep_ghost)]
use super::registration::child::ChildStatus;
use super::registration::{
    ChildIdentity, PluginDefinition, RegisteredInvocation, RegisteredPlugin,
};
use super::services::{NativeEpisode, NativeServices, ReleasedNativeValues};
use super::LifecycleState;
use crate::action_ledger::ActionTicket;
use crate::cleanup_groups::CleanupGroups;
use crate::lifecycle_actions::CleanupOutcome;
#[cfg(verus_keep_ghost)]
use crate::refinement::{self, Rule};
use crate::setup_work::{SetupWork, WorkReceipt};
use crate::{Error, Kernel, Port};
use std::collections::BTreeMap;
use std::sync::Arc;
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::std_specs::iter::IteratorSpec;

verus! {

pub struct NativeEntry<R,H> {registration:RegisteredPlugin<R>,host:H}
impl<R,H> NativeEntry<R,H> {
    pub closed spec fn recipe(&self)->RegisteredPlugin<R> {self.registration}
    pub closed spec fn bookkeeping(&self)->H {self.host}
    pub closed spec fn with_host(&self,host:H)->Self {Self {registration:self.registration,host}}
    pub fn into_parts(self)->(out:(RegisteredPlugin<R>,H))
        ensures out.0==self.recipe(),out.1==self.bookkeeping(),
    {(self.registration,self.host)}
}

pub struct NativeHost<R,H> {lifecycle:LifecycleState,entries:BTreeMap<usize,NativeEntry<R,H>>}
impl<R,H> NativeHost<R,H> {
    pub closed spec fn state(&self)->LifecycleState {self.lifecycle}
    pub closed spec fn entries(&self)->Map<usize,NativeEntry<R,H>> {self.entries@}
    pub open spec fn recipe_matches(&self,id:usize)->bool {
        let r=self.entries()[id].recipe();let p=self.state().control().paper();
        &&& r.owner()==id && r.domain_id()==self.state().protocol().domain_id()
        &&& p.fibers[id].parent==r.parent_id()
        &&& forall|port:Port| #[trigger] p.fibers[id].dependencies.contains(port)==r.dependencies_spec().contains(port)
        &&& forall|port:Port| #[trigger] p.fibers[id].provisions.contains(port)==(r.provisions_spec().contains(port) || port==r.anchor_port())
    }
    pub open spec fn wf(&self)->bool {
        &&& self.state().wf()
        &&& forall|id:usize| #[trigger] self.entries().contains_key(id)==self.state().control().paper().fibers.dom().contains(id)
        &&& forall|id:usize| #[trigger] self.entries().contains_key(id) ==> self.recipe_matches(id)
    }
    pub open spec fn same_interfaces(a:refinement::State,z:refinement::State)->bool {
        forall|id:usize| #[trigger] a.fibers.dom().contains(id)==z.fibers.dom().contains(id)
            && (a.fibers.dom().contains(id) ==> refinement::interface_same(a.fibers[id],z.fibers[id]))
    }
    proof fn step_interfaces(a:refinement::State,z:refinement::State,id:usize,rule:Rule)
        requires refinement::step(a,z,id,rule),rule!=Rule::Insert,rule!=Rule::Remove,
        ensures Self::same_interfaces(a,z),
    {
        assert forall|n:usize| #[trigger] a.fibers.dom().contains(n)==z.fibers.dom().contains(n)
            && (a.fibers.dom().contains(n) ==> refinement::interface_same(a.fibers[n],z.fibers[n])) by {
            if rule==Rule::Stutter || rule==Rule::Iter {assert(a==z);}
            else {
                assert(refinement::frame(a,z,id));
                if n!=id {assert(refinement::registered(a,n)==refinement::registered(z,n));}
                else {assert(refinement::interface_same(a.fibers[id],z.fibers[id]));}
            }
        }
    }
    proof fn preserve(&self,prior:&Self)
        requires prior.wf(),self.state().wf(),self.entries()==prior.entries(),
            self.state().protocol().domain_id()==prior.state().protocol().domain_id(),
            Self::same_interfaces(prior.state().control().paper(),self.state().control().paper()),
        ensures self.wf(),
    {
        assert forall|id:usize| #[trigger] self.entries().contains_key(id) implies self.recipe_matches(id) by {
            assert(prior.recipe_matches(id));
        }
    }
    proof fn inserted(&self,prior:&Self,id:usize)
        requires prior.wf(),self.state().wf(),self.state().protocol().domain_id()==prior.state().protocol().domain_id(),
            refinement::step(prior.state().control().paper(),self.state().control().paper(),id,Rule::Insert),
            self.entries().dom()==prior.entries().dom().insert(id),self.recipe_matches(id),
            forall|n:usize| n!=id && #[trigger] prior.entries().contains_key(n) ==> self.entries()[n]==prior.entries()[n],
        ensures self.wf(),
    {
        let a=prior.state().control().paper();let z=self.state().control().paper();
        assert(refinement::frame(a,z,id));
        assert(!refinement::registered(a,id) && refinement::registered(z,id));
        assert forall|n:usize| #[trigger] self.entries().contains_key(n)==z.fibers.dom().contains(n) by {
            if n!=id {assert(refinement::registered(a,n)==refinement::registered(z,n));}
        }
        assert forall|n:usize| #[trigger] self.entries().contains_key(n) implies self.recipe_matches(n) by {
            if n!=id {assert(refinement::registered(a,n));assert(a.fibers[n]==z.fibers[n]);assert(prior.recipe_matches(n));}
        }
    }
    pub fn new(domain:u64)->(out:Self)
        ensures out.wf(),out.state().protocol().domain_id()==domain,out.entries()==Map::empty(),
    {Self {lifecycle:LifecycleState::new(domain),entries:BTreeMap::new()}}
    pub fn lifecycle(&self)->(out:&LifecycleState)
        requires self.wf(),ensures *out==self.state(),out.wf(),
    {&self.lifecycle}
    pub fn kernel(&self)->(out:&Kernel)
        requires self.wf(),ensures *out==self.state().control(),out.wf(),
    {self.lifecycle.kernel()}
    pub fn host(&self,id:usize)->(out:Option<&H>)
        ensures out.is_some()==self.entries().contains_key(id),out.is_some() ==> *out.unwrap()==self.entries()[id].bookkeeping(),
    {match self.entries.get(&id) {Some(entry)=>Some(&entry.host),None=>None}}
    /// Only the opaque host field is lent out. Registration and graph identity
    /// remain fixed even if a caller replaces all of its own bookkeeping.
    pub fn host_mut(&mut self,id:usize)->(out:Option<&mut H>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).state()==old(self).state(),
            match out {
                Some(host)=>old(self).entries().contains_key(id) && *host==old(self).entries()[id].bookkeeping()
                    && final(self).entries()==old(self).entries().insert(id,old(self).entries()[id].with_host(*final(host))),
                None=>!old(self).entries().contains_key(id) && final(self).entries()==old(self).entries(),
            },
    {
        let ghost prior=*self;
        proof {
            assert forall|after:Self| after.state()==prior.state() && after.entries().dom()==prior.entries().dom()
                && (forall|n:usize| #[trigger] prior.entries().contains_key(n) ==> after.entries()[n].recipe()==prior.entries()[n].recipe())
                implies #[trigger] after.wf() by {
                assert forall|n:usize| #[trigger] after.entries().contains_key(n) implies after.recipe_matches(n) by {
                    assert(prior.entries().contains_key(n));assert(prior.recipe_matches(n));
                }
            }
        }
        match self.entries.get_mut(&id) {Some(entry)=>Some(&mut entry.host),None=>None}
    }
    pub fn registration(&self,id:usize)->(out:Option<&RegisteredPlugin<R>>)
        ensures out.is_some()==self.entries().contains_key(id),out.is_some() ==> *out.unwrap()==self.entries()[id].recipe(),
    {match self.entries.get(&id) {Some(entry)=>Some(&entry.registration),None=>None}}
    /// Scan live entries, not all historical identity tombstones.
    pub fn ids(&self)->(out:Vec<usize>)
        ensures out@.to_set()==self.entries().dom(),out@.no_duplicates(),
    {
        let mut out=Vec::new();let keys=self.entries.keys();
        let ghost all=keys.remaining();let _count=self.entries.len();
        proof {all.unref().unique_seq_to_set();assert(all.len()==_count);}
        for key in iter: keys
            invariant all==iter.seq(),_count==all.len(),out@==iter.seq().take(iter.index()).unref(),
            decreases _count as int-out.len() as int,
        {out.push(*key);}
        assert(out@==all.unref());out
    }
    pub fn len(&self)->(out:usize) ensures out==self.entries().len(), {self.entries.len()}
    pub fn is_empty(&self)->(out:bool) ensures out==self.entries().is_empty(), {self.entries.is_empty()}

    /// No intermediate registered identity escapes before its actual callback
    /// and host value have been stored. Failed input is returned intact.
    pub fn register(&mut self,parent:Option<usize>,realms:&BTreeMap<u64,u64>,anchor:Port,definition:PluginDefinition<R>,host:H)
        ->(out:Result<usize,(Error,PluginDefinition<R>,H)>)
        requires old(self).wf(),
        ensures final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(), final(self).state().control().generations_preserved(&old(self).state().control()), final(self).wf(),final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(),
            out.is_ok()==old(self).state().registration_enabled(parent,realms@,anchor,&definition),
            out.is_err() ==> final(self).state().same(&old(self).state()) && final(self).entries()==old(self).entries()
                && out->Err_0.1==definition && out->Err_0.2==host,
            out.is_ok() ==> final(self).entries().dom()==old(self).entries().dom().insert(out->Ok_0)
                && !old(self).entries().contains_key(out->Ok_0)
                && final(self).entries()[out->Ok_0].recipe().payload()==definition.payload()
                && final(self).entries()[out->Ok_0].bookkeeping()==host
                && (forall|n:usize| #[trigger] old(self).entries().contains_key(n) ==> final(self).entries()[n]==old(self).entries()[n])
                && refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),out->Ok_0,Rule::Insert),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let ghost prior=*self;
        let result=self.lifecycle.register_plugin(parent,realms,anchor,definition);
        proof {self.lifecycle.protocol().same_observations(&prior.state().protocol());}
        match result {
            Ok(registration)=>{
                let id=registration.id();
                self.entries.insert(id,NativeEntry {registration,host});
                proof {self.inserted(&prior,id);}
                Ok(id)
            },
            Err((error,definition))=>{proof {self.lifecycle.control().unchanged_observations(&prior.state().control());self.preserve(&prior);}Err((error,definition,host))},
        }
    }
    pub fn register_child<E>(&mut self,slot:&mut ChildSlot<E>,realms:&BTreeMap<u64,u64>,anchor:Port,definition:PluginDefinition<R>,host:H)
        ->(out:Result<usize,(Error,PluginDefinition<R>,H)>)
        requires old(self).wf(),old(slot).wf(),
        ensures final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(), final(self).state().control().generations_preserved(&old(self).state().control()), final(self).wf(),final(slot).wf(),final(slot).same_origin(old(slot)),
            out.is_ok()==(old(slot).state() is Pending && old(slot).domain_id()==old(self).state().protocol().domain_id()
                && old(slot).episode()==old(self).state().control().generation_of(old(slot).owner())
                && (old(self).state().control().phase_of(old(slot).owner())==Some(crate::Phase::Loading)
                    || old(self).state().control().phase_of(old(slot).owner())==Some(crate::Phase::Active))
                && old(self).state().registration_enabled(Some(old(slot).owner()),realms@,anchor,&definition)),
            out.is_err() ==> final(self).state().same(&old(self).state()) && final(self).entries()==old(self).entries()
                && *final(slot)==*old(slot) && out->Err_0.1==definition && out->Err_0.2==host,
            out.is_ok() ==> final(self).entries().dom()==old(self).entries().dom().insert(out->Ok_0)
                && !old(self).entries().contains_key(out->Ok_0)
                && final(self).entries()[out->Ok_0].recipe().payload()==definition.payload()
                && final(self).entries()[out->Ok_0].bookkeeping()==host
                && final(slot).state() is Assigned && final(slot).state()->Assigned_0.child()==out->Ok_0
                && final(self).entries()[out->Ok_0].recipe().parent_id()==Some(old(slot).owner())
                && (forall|n:usize| #[trigger] old(self).entries().contains_key(n) ==> final(self).entries()[n]==old(self).entries()[n])
                && refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),out->Ok_0,Rule::Insert),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let ghost prior=*self;
        let result=self.lifecycle.register_child_slot(slot,realms,anchor,definition);
        proof {self.lifecycle.protocol().same_observations(&prior.state().protocol());}
        match result {
            Ok(registration)=>{
                let id=registration.id();self.entries.insert(id,NativeEntry {registration,host});
                proof {self.inserted(&prior,id);}Ok(id)
            },
            Err((error,definition))=>{proof {self.lifecycle.control().unchanged_observations(&prior.state().control());self.preserve(&prior);}Err((error,definition,host))},
        }
    }
    /// The actual entry is moved out only after the lifecycle Remove succeeds.
    pub fn remove(&mut self,id:usize)->(out:Result<NativeEntry<R,H>,Error>)
        requires old(self).wf(),
        ensures final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(), final(self).state().control().generations_preserved(&old(self).state().control()), final(self).wf(),
            out.is_err() ==> final(self).state().same(&old(self).state()) && final(self).entries()==old(self).entries(),
            out.is_ok() ==> old(self).entries().contains_key(id) && out->Ok_0==old(self).entries()[id]
                && final(self).entries()==old(self).entries().remove(id)
                && refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),id,Rule::Remove),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let ghost prior=*self;
        let result=self.lifecycle.remove(id);
        proof {self.lifecycle.protocol().same_observations(&prior.state().protocol());}
        match result {
            Ok(())=>{
                proof {
                    assert(refinement::registered(prior.state().control().paper(),id));
                    assert(prior.state().control().paper().fibers.dom().contains(id));
                    assert(prior.entries().contains_key(id));assert(self.entries@.contains_key(id));
                }
                let entry=self.entries.remove(&id).unwrap();
                proof {
                    let a=prior.state().control().paper();let z=self.state().control().paper();
                    assert(refinement::frame(a,z,id));assert(!refinement::registered(z,id));
                    assert forall|n:usize| #[trigger] self.entries().contains_key(n)==z.fibers.dom().contains(n) by {
                        assert(prior.entries().contains_key(n)==a.fibers.dom().contains(n));
                        if n!=id {assert(refinement::registered(a,n)==refinement::registered(z,n));}
                    }
                    assert forall|n:usize| #[trigger] self.entries().contains_key(n) implies self.recipe_matches(n) by {
                        assert(n!=id);assert(refinement::registered(a,n));assert(a.fibers[n]==z.fibers[n]);assert(prior.recipe_matches(n));
                    }
                }
                Ok(entry)
            },
            Err(error)=>{proof {self.lifecycle.control().unchanged_observations(&prior.state().control());self.preserve(&prior);}Err(error)},
        }
    }
    pub fn replace(&mut self,id:usize,payload:R)->(out:Result<R,(Error,R)>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).state()==old(self).state(),final(self).entries().dom()==old(self).entries().dom(),
            out.is_ok()==(old(self).entries().contains_key(id) && old(self).entries()[id].recipe().version()<u64::MAX),
            out.is_err() ==> final(self).entries()==old(self).entries() && out->Err_0.1==payload,
            out.is_ok() ==> old(self).entries().contains_key(id) && final(self).entries()[id].recipe().same_identity(&old(self).entries()[id].recipe())
                && final(self).entries()[id].recipe().version()==old(self).entries()[id].recipe().version()+1
                && final(self).entries()[id].recipe().payload()==payload && out->Ok_0==old(self).entries()[id].recipe().payload(),
            forall|n:usize| #[trigger] old(self).entries().contains_key(n) ==>
                final(self).entries()[n].bookkeeping()==old(self).entries()[n].bookkeeping()
                && (n!=id ==> final(self).entries()[n]==old(self).entries()[n]),
    {
        let ghost prior=*self;
        let out=match self.entries.get_mut(&id) {
            Some(entry)=>match entry.registration.replace(payload) {Ok(previous)=>Ok(previous),Err(payload)=>Err((Error::Capacity,payload))},
            None=>Err((Error::Unknown,payload)),
        };
        proof {
            assert forall|n:usize| #[trigger] self.entries().contains_key(n)==self.state().control().paper().fibers.dom().contains(n) by {
                assert(prior.entries().contains_key(n)==prior.state().control().paper().fibers.dom().contains(n));
            }
            assert forall|n:usize| #[trigger] self.entries().contains_key(n) implies self.recipe_matches(n) by {
                assert(prior.entries().contains_key(n));assert(prior.recipe_matches(n));
                assert(self.entries()[n].recipe().same_identity(&prior.entries()[n].recipe()));
            }
        }
        out
    }
    pub fn admit_root<C,G,A>(&self,id:usize,work:&mut SetupWork<C,G>,argument:A)->(out:Result<RegisteredInvocation<A>,A>)
        requires self.wf(),old(work).wf(),
        ensures final(work).origin()==old(work).origin(), final(work).domain_id()==old(work).domain_id(), final(work).accepts()==old(work).accepts(), final(work).is_closed()==old(work).is_closed(), final(work).wf(),out.is_err() ==> out->Err_0==argument && *final(work)==*old(work),
            out.is_ok() ==> self.entries().contains_key(id) && out->Ok_0.owner()==id
                && out->Ok_0.domain_id()==self.state().protocol().domain_id()
                && out->Ok_0.version()==self.entries()[id].recipe().version() && out->Ok_0.work().value()==argument
                && out->Ok_0.lifecycle()==old(work).origin().unwrap()
                && out->Ok_0.work().origin().domain_id()==old(work).domain_id()
                && self.state().root_invocation_enabled(out->Ok_0.lifecycle()),
    {
        match self.entries.get(&id) {
            Some(entry)=>self.lifecycle.admit_registered_root(&entry.registration,work,argument),None=>Err(argument),
        }
    }
    pub fn call<A,O>(&mut self,id:usize,invocation:RegisteredInvocation<A>)->(out:Result<WorkReceipt<O>,RegisteredInvocation<A>>)
        where R:FnMut(A)->O,
        requires old(self).wf(),old(self).entries().contains_key(id) ==> old(self).entries()[id].recipe().payload().requires((invocation.work().value(),)),
        ensures final(self).wf(),final(self).state()==old(self).state(),final(self).entries().dom()==old(self).entries().dom(),
            out.is_ok()==(old(self).entries().contains_key(id) && invocation.owner()==id
                && invocation.domain_id()==old(self).state().protocol().domain_id()
                && invocation.version()==old(self).entries()[id].recipe().version()
                && invocation.lifecycle().id==id && old(self).state().root_invocation_enabled(invocation.lifecycle())),
            out.is_err() ==> final(self).entries()==old(self).entries() && out->Err_0==invocation,
            out.is_ok() ==> old(self).entries().contains_key(id) && invocation.owner()==id
                && invocation.domain_id()==old(self).state().protocol().domain_id()
                && invocation.version()==old(self).entries()[id].recipe().version()
                && invocation.lifecycle().id==id && old(self).state().root_invocation_enabled(invocation.lifecycle())
                && out->Ok_0.origin()==invocation.work().origin()
                && old(self).entries()[id].recipe().payload().ensures((invocation.work().value(),),out->Ok_0.value()),
            forall|n:usize| #[trigger] old(self).entries().contains_key(n) ==>
                final(self).entries()[n].bookkeeping()==old(self).entries()[n].bookkeeping()
                && final(self).entries()[n].recipe().same_identity(&old(self).entries()[n].recipe())
                && final(self).entries()[n].recipe().version()==old(self).entries()[n].recipe().version()
                && (n!=id ==> final(self).entries()[n]==old(self).entries()[n]),
    {
        if invocation.lifecycle_ticket().id!=id || !self.lifecycle.accepts_root_invocation(invocation.lifecycle_ticket()) {return Err(invocation);}
        match self.entries.get_mut(&id) {Some(entry)=>entry.registration.call(invocation),None=>Err(invocation)}
    }
}

impl<R,H> NativeHost<R,H> {
    #[allow(clippy::type_complexity)]
    pub fn begin_native_execution<V,C,G,I>(&mut self,id:usize,store:&NativeServices<V>,cleanup_domain:u64)
        ->(out:Result<(SetupWork<C,G>,CleanupGroups<I>,NativeEpisode<V>),Error>)
        requires old(self).wf(),store.wf(),
        ensures final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(), (forall|n:usize| n!=id ==> final(self).state().control().generation_of(n)==old(self).state().control().generation_of(n)), out.is_ok() ==> out->Ok_0.0.accepts(), out.is_ok() ==> !out->Ok_0.0.is_closed() && !out->Ok_0.1.closed(), final(self).wf(),final(self).entries()==old(self).entries(),
            out.is_ok()==(old(self).entries().contains_key(id) && store.domain_id()==old(self).state().protocol().domain_id()
                && !store.entries().contains_key(id) && old(self).state().protocol().admission_enabled(id) && old(self).state().control().begin_enabled(id)),
            out.is_err() ==> final(self).state().same(&old(self).state()),
            out.is_ok() ==> old(self).entries().contains_key(id)
                && out->Ok_0.0.wf() && out->Ok_0.0.domain_id()==cleanup_domain && out->Ok_0.1.wf() && out->Ok_0.2.wf()
                && final(self).state().execution_matches(id,&out->Ok_0.0,&out->Ok_0.1)
                && !out->Ok_0.2.closed() && out->Ok_0.2.owned()==Map::empty()
                && Some(out->Ok_0.2.origin())==out->Ok_0.0.origin()
                && out->Ok_0.2.capture().control==final(self).state().control()
                && out->Ok_0.2.capture().sources==crate::lifecycle_state::services::capture::sources(store.entries())
                && out->Ok_0.2.capture().work_domain==cleanup_domain
                && out->Ok_0.2.provisions()==old(self).entries()[id].recipe().provisions_spec()
                && (forall|b:crate::Binding| out->Ok_0.2.bindings().contains(b)==final(self).state().control().binding_recorded(id,b))
                && (forall|key:(usize,u64,u64)| #[trigger] out->Ok_0.2.imports().contains_key(key)==(out->Ok_0.2.bindings().contains(crate::Binding {provider:key.0,key:key.1,realm:key.2})
                    && store.available(&final(self).state(),key.0,Port {key:key.1,realm:key.2})))
                && (forall|key:(usize,u64,u64)| #[trigger] out->Ok_0.2.imports().contains_key(key) ==>
                    out->Ok_0.2.imports()[key]==store.entries()[key.0].values()[(key.1,key.2)])
                && refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),id,Rule::Begin),
    {
        let ghost prior=*self;
        let entry=match self.entries.get(&id) {Some(entry)=>entry,None=>{
            proof {reveal(LifecycleState::same);reveal(Kernel::unchanged);self.lifecycle.protocol().same_reflexive();}
            return Err(Error::Unknown);
        }};
        assert(prior.recipe_matches(id));assert(entry.registration.owner()==id);
        let out=self.lifecycle.begin_native_execution(store,&entry.registration,cleanup_domain);
        proof {
            if out.is_ok() {Self::step_interfaces(prior.state().control().paper(),self.state().control().paper(),id,Rule::Begin);}
            else {self.lifecycle.control().unchanged_observations(&prior.state().control());}
            self.preserve(&prior);
        }
        out
    }
    pub fn native_value<'a,V>(&self,store:&'a NativeServices<V>,port:Port)->(out:Option<&'a Arc<V>>)
        requires self.wf(),store.wf(),
        ensures out.is_some()==(exists|id:usize| self.state().control().resolves_to(port,id) && store.available(&self.state(),id,port)),
            out.is_some() ==> exists|id:usize| self.state().control().resolves_to(port,id)
            && store.available(&self.state(),id,port) && *out.unwrap()==store.entries()[id].values()[(port.key,port.realm)],
    {store.visible(&self.lifecycle,port)}
    pub fn finish_native_execution<V,C,G,I>(&mut self,id:usize,store:&mut NativeServices<V>,values:&NativeEpisode<V>,work:&SetupWork<C,G>,groups:&CleanupGroups<I>)
        ->(out:Result<(),Error>)
        requires old(self).wf(),old(store).wf(),values.wf(),work.wf(),groups.wf(),
        ensures final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(), final(self).state().control().generations_preserved(&old(self).state().control()), final(self).wf(),final(self).entries()==old(self).entries(),final(store).wf(),final(store).domain_id()==old(store).domain_id(),
            out.is_err() ==> *final(store)==*old(store) && final(self).state().control().unchanged(&old(self).state().control()),
            out.is_ok() ==> old(self).state().execution_matches(id,work,groups) && values.complete() && !values.closed() && Some(values.origin())==work.origin()
                && values.origin().id==id && values.origin().domain==old(self).state().protocol().domain_id()
                && final(store).entries().dom()==old(store).entries().dom().insert(id)
                && final(store).entries()[id].capture()==values.capture()
                && final(store).entries()[id].origin()==values.origin() && final(store).entries()[id].values()==values.owned()
                && (forall|n:usize| n!=id && #[trigger] old(store).entries().contains_key(n) ==> final(store).entries()[n]==old(store).entries()[n])
                && refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),id,Rule::Finish),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let ghost prior=*self;
        let out=self.lifecycle.finish_native_execution(id,store,values,work,groups);
        proof {
            if out.is_ok() {Self::step_interfaces(prior.state().control().paper(),self.state().control().paper(),id,Rule::Finish);}
            else {self.lifecycle.control().unchanged_observations(&prior.state().control());}
            self.preserve(&prior);
        }
        out
    }
    pub fn release_native_execution<V,C,G,I>(&mut self,id:usize,store:&mut NativeServices<V>,values:&mut NativeEpisode<V>,work:&mut SetupWork<C,G>,groups:&mut CleanupGroups<I>)
        ->(out:Result<(CleanupOutcome,ReleasedNativeValues<V>),Error>)
        requires old(self).wf(),old(store).wf(),old(values).wf(),old(work).wf(),old(groups).wf(),
        ensures final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(), final(self).state().control().generations_preserved(&old(self).state().control()), out.is_ok() ==> old(work).idle() && old(groups).all_drained(), final(work).origin()==old(work).origin(), final(work).domain_id()==old(work).domain_id(), final(groups).origin()==old(groups).origin(), final(self).wf(),final(self).entries()==old(self).entries(),final(store).wf(),final(values).wf(),final(work).wf(),final(groups).wf(),
            final(store).domain_id()==old(store).domain_id(),final(values).same_identity(old(values)),
            out.is_err() ==> final(self).state().same(&old(self).state()) && *final(store)==*old(store) && *final(values)==*old(values)
                && *final(work)==*old(work) && *final(groups)==*old(groups),
            out.is_ok() ==> Some(old(values).origin())==old(work).origin() && old(values).origin().id==id
                && (old(store).entries().contains_key(id) ==> old(store).entries()[id].origin()==old(values).origin())
                && final(values).closed() && final(values).owned()==Map::empty() && final(values).imports()==Map::empty()
                && out->Ok_0.1.owned()==old(values).owned() && out->Ok_0.1.imports()==old(values).imports()
                && out->Ok_0.1.imports()==old(values).capture().imports
                && out->Ok_0.1.published()==if old(store).entries().contains_key(id) {Some(old(store).entries()[id])} else {None}
                && final(store).entries()==old(store).entries().remove(id)
                && final(work).is_closed() && final(groups).closed() && final(self).state().control().no_committed(id)
                && out->Ok_0.0==if old(groups).drained_failure() {CleanupOutcome::Drained} else {CleanupOutcome::Succeeded}
                && refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),id,Rule::Unload),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let ghost prior=*self;
        let out=self.lifecycle.release_native_execution(id,store,values,work,groups);
        proof {
            if out.is_ok() {Self::step_interfaces(prior.state().control().paper(),self.state().control().paper(),id,Rule::Unload);}
            else {self.lifecycle.control().unchanged_observations(&prior.state().control());}
            self.preserve(&prior);
        }
        out
    }
    pub fn retire_child_slot<E>(&mut self,slot:&mut ChildSlot<E>)->(out:Result<Option<ChildIdentity>,Error>)
        requires old(self).wf(),old(slot).wf(),
        ensures out.is_ok() && out->Ok_0.is_none() ==> final(self).state().same(&old(self).state()), final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(), final(self).state().control().generations_preserved(&old(self).state().control()), final(self).wf(),final(self).entries()==old(self).entries(),final(slot).wf(),final(slot).same_origin(old(slot)),
            !(old(slot).state() is Pending) ==> *final(slot)==*old(slot),
            out.is_err() ==> final(self).state().same(&old(self).state()) && *final(slot)==*old(slot),
            out.is_ok() ==> !(final(slot).state() is Pending)
                && (old(slot).state() is Pending ==> final(slot).state() is Cancelled && out->Ok_0.is_none())
                && (out->Ok_0.is_some() ==> old(slot).state() is Assigned && out->Ok_0==Some(old(slot).state()->Assigned_0)
                    && (if old(self).state().control().registered(out->Ok_0.unwrap().child()) {
                        refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),out->Ok_0.unwrap().child(),Rule::Retire)
                    } else {final(self).state().same(&old(self).state())})),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let ghost prior=*self;
        let ghost original=*slot;
        let out=self.lifecycle.retire_child_slot(slot);
        proof {
            self.lifecycle.protocol().same_observations(&prior.state().protocol());
            if out.is_ok() && original.state() is Assigned && prior.state().control().registered(original.state()->Assigned_0.child()) {
                Self::step_interfaces(prior.state().control().paper(),self.state().control().paper(),original.state()->Assigned_0.child(),Rule::Retire);
            } else {self.lifecycle.control().unchanged_observations(&prior.state().control());}
            self.preserve(&prior);
        }
        out
    }

    pub fn retire(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(), final(self).state().control().generations_preserved(&old(self).state().control()), final(self).wf(),final(self).entries()==old(self).entries(),
            out.is_err() ==> final(self).state().same(&old(self).state()),
            out.is_ok() ==> refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),id,Rule::Retire),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let ghost prior=*self;let out=self.lifecycle.retire(id);
        proof {
            self.lifecycle.protocol().same_observations(&prior.state().protocol());
            if out.is_ok() {Self::step_interfaces(prior.state().control().paper(),self.state().control().paper(),id,Rule::Retire);}
            else {self.lifecycle.control().unchanged_observations(&prior.state().control());}
            self.preserve(&prior);
        }
        out
    }

    pub fn leave(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(), final(self).state().control().generations_preserved(&old(self).state().control()), final(self).wf(),final(self).entries()==old(self).entries(),
            out.is_err() ==> final(self).state().same(&old(self).state()),
            out.is_ok() ==> refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),id,Rule::Restart),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let ghost prior=*self;let out=self.lifecycle.leave(id);
        proof {
            self.lifecycle.protocol().same_observations(&prior.state().protocol());
            if out.is_ok() {Self::step_interfaces(prior.state().control().paper(),self.state().control().paper(),id,Rule::Restart);}
            else {self.lifecycle.control().unchanged_observations(&prior.state().control());}
            self.preserve(&prior);
        }
        out
    }

    pub fn settle_execution<C,G,I>(&mut self,id:usize,work:&SetupWork<C,G>,groups:&CleanupGroups<I>)->(out:Result<(),Error>)
        requires old(self).wf(),work.wf(),groups.wf(),
        ensures final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(), final(self).state().control().generations_preserved(&old(self).state().control()), final(self).wf(),final(self).entries()==old(self).entries(),final(self).state().control().unchanged(&old(self).state().control()),
            out.is_err() ==> final(self).state().same(&old(self).state()),
            out.is_ok() ==> old(self).state().execution_matches(id,work,groups) && work.idle() && !groups.any_pending()
                && !final(self).state().protocol().outstanding(id),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let ghost prior=*self;let out=self.lifecycle.settle_execution(id,work,groups);
        proof {self.lifecycle.control().unchanged_observations(&prior.state().control());self.preserve(&prior);}
        out
    }

    pub fn fail_execution<C,G,I>(&mut self,id:usize,work:&SetupWork<C,G>,groups:&CleanupGroups<I>)->(out:Result<(),Error>)
        requires old(self).wf(),work.wf(),groups.wf(),
        ensures final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(), final(self).state().control().generations_preserved(&old(self).state().control()), final(self).wf(),final(self).entries()==old(self).entries(),final(self).state().control().unchanged(&old(self).state().control()),
            out.is_err() ==> final(self).state().same(&old(self).state()),
            out.is_ok() ==> old(self).state().execution_matches(id,work,groups) && groups.any_failed()
                && work.idle() && !groups.any_pending() && !groups.any_issued()
                && !final(self).state().protocol().eligible(id,work.origin().unwrap().generation),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let ghost prior=*self;let out=self.lifecycle.fail_execution(id,work,groups);
        proof {self.lifecycle.control().unchanged_observations(&prior.state().control());self.preserve(&prior);}
        out
    }

    pub fn retry_execution<C,G,I>(&mut self,id:usize,work:&SetupWork<C,G>,groups:&mut CleanupGroups<I>)->(out:Result<ActionTicket,Error>)
        requires old(self).wf(),work.wf(),old(groups).wf(),
        ensures final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(), final(self).state().control().generations_preserved(&old(self).state().control()), final(groups).origin()==old(groups).origin(), final(groups).domain_ids()==old(groups).domain_ids(), final(groups).queues().dom()==old(groups).queues().dom(), final(groups).closed()==old(groups).closed(), final(self).wf(),final(self).entries()==old(self).entries(),final(self).state().control().unchanged(&old(self).state().control()),
            out.is_err() ==> final(self).state().same(&old(self).state()) && *final(groups)==*old(groups),
            final(groups).wf(),final(groups).drained_failure()==old(groups).drained_failure(),
            out.is_ok() ==> old(self).state().execution_matches(id,work,old(groups)) && old(groups).retries_ready()
                && !final(groups).any_failed() && final(self).state().protocol().cleanup_reply_enabled(out->Ok_0)
                && out->Ok_0.id==id && out->Ok_0.generation==work.origin().unwrap().generation
                && out->Ok_0.action==old(self).state().protocol().next_id(),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let ghost prior=*self;let out=self.lifecycle.retry_execution(id,work,groups);
        proof {self.lifecycle.control().unchanged_observations(&prior.state().control());self.preserve(&prior);}
        out
    }

    pub fn begin_cleanup(&mut self,id:usize)->(out:Result<ActionTicket,Error>)
        requires old(self).wf(),
        ensures final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(), final(self).state().control().generations_preserved(&old(self).state().control()), final(self).wf(),final(self).entries()==old(self).entries(),
            final(self).state().control().paper()==old(self).state().control().paper(),
            out.is_err() ==> final(self).state().same(&old(self).state()),
            out.is_ok() ==> final(self).state().protocol().cleanup_reply_enabled(out->Ok_0)
                && final(self).state().control().restoration_guarded(id),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let ghost prior=*self;let out=self.lifecycle.begin_cleanup(id);
        proof {self.preserve(&prior);}out
    }

    pub fn compact_bindings(&mut self)->(out:usize)
        requires old(self).wf(),
        ensures final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(), final(self).state().control().generations_preserved(&old(self).state().control()), final(self).wf(),final(self).entries()==old(self).entries(),
            final(self).state().control().paper()==old(self).state().control().paper(),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let ghost prior=*self;let out=self.lifecycle.compact_bindings();
        proof {self.lifecycle.protocol().same_observations(&prior.state().protocol());self.preserve(&prior);}out
    }

    pub fn compact_declarations(&mut self)->(out:usize)
        requires old(self).wf(),
        ensures final(self).state().protocol().domain_id()==old(self).state().protocol().domain_id(), final(self).state().control().generations_preserved(&old(self).state().control()), final(self).wf(),final(self).entries()==old(self).entries(),
            final(self).state().control().paper()==old(self).state().control().paper(),
    {
        proof {reveal(crate::Kernel::generations_preserved);reveal(crate::Kernel::unchanged);}

        let ghost prior=*self;let out=self.lifecycle.compact_declarations();
        proof {self.lifecycle.protocol().same_observations(&prior.state().protocol());self.preserve(&prior);}out
    }
}
}
