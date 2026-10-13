//! The production native registry and its published values have one owner.
//! No independent service store can be substituted at Begin, Finish or Unload.
//! Its joint invariant covers real registry membership, episode generations,
//! complete declared values and retention throughout restoration. Opaque host
//! bookkeeping, escaped episode mutexes and slot interiors are separate bounds.
#[path = "native_history.rs"]
pub mod history;
#[path = "native_owner.rs"]
pub mod owner;
use super::{NativeEntry, NativeHost};
use crate::action_ledger::ActionTicket;
use crate::execution::Execution;
use crate::lifecycle_actions::CleanupOutcome;
use crate::lifecycle_state::registration::shared_child::{ChildTransition, SharedChild};
use crate::lifecycle_state::registration::{
    ChildIdentity, PluginDefinition, RegisteredInvocation, RegisteredPlugin,
};
use crate::lifecycle_state::services::{NativeServices, ReleasedNativeValues};
use crate::lifecycle_state::LifecycleState;
use crate::setup_work::WorkReceipt;
#[cfg(verus_keep_ghost)]
use crate::{
    refinement::{self, Rule},
    Phase,
};
use crate::{Error, Kernel, Port};
use history::History;
#[cfg(verus_keep_ghost)]
use history::Observation;
use owner::EpisodeOwner;
use std::collections::BTreeMap;
use std::sync::Arc;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
#[allow(dead_code)] // The joint history is erased by Cargo.
pub struct NativeRuntime<R,H,V> {host:NativeHost<R,H>,services:NativeServices<V>,history:Ghost<History<V>>,owners:BTreeMap<usize,EpisodeOwner>}
impl<R,H,V> NativeRuntime<R,H,V> {
    pub closed spec fn registry(&self)->NativeHost<R,H> {self.host}
    pub closed spec fn publications(&self)->NativeServices<V> {self.services}
    pub closed spec fn episode_owners(&self)->Map<usize,EpisodeOwner> {self.owners@}
    pub open spec fn state(&self)->LifecycleState {self.registry().state()}
    pub open spec fn linked(&self,id:usize)->bool {
        let control=self.state().control();let paper=control.paper();let values=self.publications().entries();
        &&& self.episode_owners().contains_key(id)==(refinement::registered(paper,id) && paper.fibers[id].phase!=Phase::Inactive)
        &&& self.episode_owners().contains_key(id) ==> {
            &&& self.episode_owners()[id].origin.id==id
            &&& self.episode_owners()[id].origin.domain==self.state().protocol().domain_id()
            &&& self.episode_owners()[id].origin.kind==crate::action_ledger::ActionKind::Setup
            &&& control.generation_of(id)==Some(self.episode_owners()[id].origin.generation)
        }
        &&& refinement::registered(paper,id) && paper.fibers[id].phase==Phase::Active ==> values.contains_key(id)
        &&& values.contains_key(id) ==> {
            &&& self.registry().entries().contains_key(id)
            &&& control.generation_of(id)==Some(values[id].origin().generation)
            &&& values[id].origin()==self.episode_owners()[id].origin
            &&& values[id].capture().work_domain==self.episode_owners()[id].work_domain
            &&& refinement::registered(paper,id)
            &&& paper.fibers[id].phase==Phase::Active || paper.fibers[id].phase==Phase::Unloading
            &&& forall|p:Port| #[trigger] values[id].values().contains_key((p.key,p.realm))==
                self.registry().entries()[id].recipe().provisions_spec().contains(p)
        }
    }
    pub open spec fn structural(&self)->bool {
        &&& self.registry().wf() && self.publications().wf()
        &&& self.publications().domain_id()==self.state().protocol().domain_id()
        &&& forall|id:usize| #[trigger] self.linked(id)
    }
    pub closed spec fn execution_history(&self)->History<V> {self.history@}
    pub closed spec fn observation(&self)->Observation<V> {
        Observation {control:self.state().control().paper(),publications:self.publications().entries(),owners:self.episode_owners()}
    }
    pub open spec fn wf(&self)->bool {
        self.structural() && self.execution_history().valid() && self.execution_history().states.last()==self.observation()
    }
    pub proof fn history_correspondence(&self)
        requires self.wf(),
        ensures self.execution_history().valid(),self.execution_history().states.last()==self.observation(),
            refinement::execution(self.execution_history().controls(),self.execution_history().labels,true),
            self.execution_history().base_only() ==> refinement::execution(self.execution_history().controls(),self.execution_history().labels,false)
                && refinement::reaches(self.execution_history().controls().first(),self.state().control().paper(),self.execution_history().labels.len(),false),
    {self.execution_history().correspondence();}
    /// A control step changes at most its actor; complete publication of that
    /// actor is checked separately at the actual Finish/Unload boundary.
    proof fn transition(tracked &mut self,prior:&Self,id:usize,rule:Rule)
        requires prior.wf(),old(self).execution_history()==prior.execution_history(),
            old(self).state().protocol().domain_id()==prior.state().protocol().domain_id(),
            rule!=Rule::Finish && rule!=Rule::Unload ==> old(self).publications()==prior.publications(),old(self).registry().wf(),old(self).publications().wf(),
            old(self).publications().domain_id()==old(self).state().protocol().domain_id(),
            refinement::step(prior.state().control().paper(),old(self).state().control().paper(),id,rule),
            old(self).linked(id),
            match rule {
                Rule::Begin=>!prior.episode_owners().contains_key(id) && old(self).episode_owners().contains_key(id)
                    && old(self).episode_owners()==prior.episode_owners().insert(id,old(self).episode_owners()[id]),
                Rule::Unload=>old(self).episode_owners()==prior.episode_owners().remove(id),
                _=>old(self).episode_owners()==prior.episode_owners(),
            },
            forall|n:usize| n!=id ==> old(self).state().control().generation_of(n)==prior.state().control().generation_of(n),
            forall|n:usize| n!=id ==> #[trigger] old(self).publications().entries().contains_key(n)==prior.publications().entries().contains_key(n),
            forall|n:usize| n!=id && prior.publications().entries().contains_key(n) ==> #[trigger] old(self).publications().entries()[n]==prior.publications().entries()[n],
            forall|n:usize| n!=id && #[trigger] prior.registry().entries().contains_key(n) ==>
                old(self).registry().entries().contains_key(n) && old(self).registry().entries()[n].recipe().provisions_spec()==prior.registry().entries()[n].recipe().provisions_spec(),
        ensures final(self).wf(),final(self).registry()==old(self).registry(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).execution_history().extends(prior.execution_history()),
    {
        reveal(Kernel::paper);reveal(Kernel::phase_of);
        assert(refinement::frame(prior.state().control().paper(),self.state().control().paper(),id));
        assert forall|n:usize| #[trigger] self.linked(n) by {
            if n!=id {
                assert(prior.linked(n));
                assert(self.episode_owners().contains_key(n)==prior.episode_owners().contains_key(n));
                if self.episode_owners().contains_key(n) {assert(self.episode_owners()[n]==prior.episode_owners()[n]);}
                assert(refinement::registered(prior.state().control().paper(),n)==refinement::registered(self.state().control().paper(),n));
            }
        }
        assert(self.structural());
        assert(prior.linked(id));
        if rule==Rule::Finish {
            assert(!prior.publications().entries().contains_key(id));
            assert(self.publications().entries().contains_key(id));
            assert forall|n:usize| self.publications().entries().contains_key(n)==prior.publications().entries().insert(id,self.publications().entries()[id]).contains_key(n) by {
                if n!=id {assert(self.publications().entries().contains_key(n)==prior.publications().entries().contains_key(n));}
            }
            assert forall|n:usize| self.publications().entries().contains_key(n) implies self.publications().entries()[n]==prior.publications().entries().insert(id,self.publications().entries()[id])[n] by {}
            assert(self.publications().entries() =~= prior.publications().entries().insert(id,self.publications().entries()[id]));
        } else if rule==Rule::Unload {
            assert(self.state().control().paper().fibers[id].phase==Phase::Inactive);
            assert(!self.publications().entries().contains_key(id));
            assert forall|n:usize| self.publications().entries().contains_key(n)==prior.publications().entries().remove(id).contains_key(n) by {
                if n!=id {assert(self.publications().entries().contains_key(n)==prior.publications().entries().contains_key(n));}
            }
            assert forall|n:usize| self.publications().entries().contains_key(n) implies self.publications().entries()[n]==prior.publications().entries().remove(id)[n] by {}
            assert(self.publications().entries() =~= prior.publications().entries().remove(id));
        }
        assert(history::step(prior.observation(),self.observation(),id,rule));
        let ghost before_record=*self;
        let ghost next=self.execution_history().append(self.observation(),id,rule);
        self.execution_history().extended(self.observation(),id,rule);
        assert(next.valid());assert(next.states.last()==self.observation());
        self.history=Ghost(next);
        assert(self.observation()==before_record.observation());
        assert(self.execution_history().valid());
        assert forall|n:usize| #[trigger] self.linked(n) by {assert(before_record.linked(n));}
        assert(self.structural());
        assert(self.execution_history().states.last()==self.observation());
    }
    proof fn unchanged(&self,prior:&Self)
        requires prior.wf(),self.episode_owners()==prior.episode_owners(),self.execution_history()==prior.execution_history(),self.registry().wf(),self.publications()==prior.publications(),
            self.state().protocol().domain_id()==prior.state().protocol().domain_id(),
            self.state().control().paper()==prior.state().control().paper(),
            self.state().control().generations_preserved(&prior.state().control()),
            forall|n:usize| #[trigger] prior.registry().entries().contains_key(n) ==>
                self.registry().entries()[n].recipe().provisions_spec()==prior.registry().entries()[n].recipe().provisions_spec(),
        ensures self.wf(),
    {
        reveal(Kernel::paper);reveal(Kernel::phase_of);
        assert forall|n:usize| #[trigger] self.linked(n) by {
            assert(prior.linked(n));
            if prior.publications().entries().contains_key(n) || prior.episode_owners().contains_key(n) {
                self.state().control().paper_observations(n);prior.state().control().paper_observations(n);
                self.state().control().generation_frame(&prior.state().control(),n);
            }
        }
    }
    proof fn generations(&self,prior:&Self)
        requires self.registry().wf(),prior.registry().wf(),
            self.state().control().generations_preserved(&prior.state().control()),
        ensures forall|n:usize| self.registry().entries().contains_key(n) && prior.registry().entries().contains_key(n) ==>
            self.state().control().generation_of(n)==prior.state().control().generation_of(n),
    {
        assert forall|n:usize| self.registry().entries().contains_key(n) && prior.registry().entries().contains_key(n) implies
            self.state().control().generation_of(n)==prior.state().control().generation_of(n) by {
            reveal(Kernel::paper);self.state().control().paper_observations(n);prior.state().control().paper_observations(n);
                self.state().control().generation_frame(&prior.state().control(),n);
        }
    }
    proof fn generation_step(&self,prior:&Self,id:usize,rule:Rule)
        requires self.registry().wf(),prior.registry().wf(),
            self.state().control().generations_preserved(&prior.state().control()),
            refinement::step(prior.state().control().paper(),self.state().control().paper(),id,rule),
            rule!=Rule::Stutter,rule!=Rule::Iter,
        ensures forall|n:usize| n!=id ==> self.state().control().generation_of(n)==prior.state().control().generation_of(n),
    {
        assert(refinement::frame(prior.state().control().paper(),self.state().control().paper(),id));
        assert forall|n:usize| n!=id implies self.state().control().generation_of(n)==prior.state().control().generation_of(n) by {
            self.state().control().paper_observations(n);prior.state().control().paper_observations(n);
            if prior.state().control().registered(n) {self.state().control().generation_frame(&prior.state().control(),n);}
        }
    }
    pub fn new(domain:u64)->(out:Self)
        ensures out.wf(),out.state().protocol().domain_id()==domain,out.registry().entries()==Map::empty(),out.publications().entries()==Map::empty(),
    {
        let host=NativeHost::new(domain);let services=NativeServices::new(domain);
        let ghost initial=Observation {control:host.state().control().paper(),publications:services.entries(),owners:Map::empty()};
        let out=Self {host,services,owners:BTreeMap::new(),history:Ghost(History {states:seq![initial],labels:Seq::empty()})};
        proof {assert forall|id:usize| #[trigger] out.linked(id) by {assert(!out.registry().entries().contains_key(id));assert(!refinement::registered(out.state().control().paper(),id));}
            assert forall|id:usize| !out.state().control().paper().fibers.dom().contains(id) by {
                assert(out.registry().entries().contains_key(id)==out.state().control().paper().fibers.dom().contains(id));
            }
            assert(out.state().control().paper().fibers.dom() =~= ISet::empty());
            assert(out.execution_history().valid());assert(out.execution_history().states.last()==out.observation());
        }out}
    pub fn lifecycle(&self)->(out:&LifecycleState)
        requires self.wf(),ensures *out==self.state(),out.wf(),
    {self.host.lifecycle()}
    pub fn kernel(&self)->(out:&Kernel)
        requires self.wf(),ensures *out==self.state().control(),out.wf(),
    {self.host.kernel()}
    pub fn host(&self,id:usize)->(out:Option<&H>)
        ensures out.is_some()==self.registry().entries().contains_key(id),out.is_some() ==> *out.unwrap()==self.registry().entries()[id].bookkeeping(),
    {self.host.host(id)}
    pub fn host_mut(&mut self,id:usize)->(out:Option<&mut H>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).state()==old(self).state(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            match out {
                Some(host)=>old(self).registry().entries().contains_key(id) && *host==old(self).registry().entries()[id].bookkeeping()
                    && final(self).registry().entries()==old(self).registry().entries().insert(id,old(self).registry().entries()[id].with_host(*final(host))),
                None=>!old(self).registry().entries().contains_key(id) && final(self).registry().entries()==old(self).registry().entries(),
            },
    {
        let ghost prior=*self;
        proof {
            assert forall|after:Self| after.registry().wf() && after.state()==prior.state() && after.publications()==prior.publications() && after.execution_history()==prior.execution_history() && after.episode_owners()==prior.episode_owners()
                && (forall|n:usize| #[trigger] prior.registry().entries().contains_key(n) ==>
                    after.registry().entries()[n].recipe().provisions_spec()==prior.registry().entries()[n].recipe().provisions_spec())
                implies #[trigger] after.wf() by {
                reveal(Kernel::generations_preserved);after.unchanged(&prior);
            }
        }
        self.host.host_mut(id)
    }
    pub fn registration(&self,id:usize)->(out:Option<&RegisteredPlugin<R>>)
        ensures out.is_some()==self.registry().entries().contains_key(id),out.is_some() ==> *out.unwrap()==self.registry().entries()[id].recipe(),
    {self.host.registration(id)}
    pub fn ids(&self)->(out:Vec<usize>)
        ensures out@.to_set()==self.registry().entries().dom(),out@.no_duplicates(),
    {self.host.ids()}
    pub fn len(&self)->(out:usize) ensures out==self.registry().entries().len(), {self.host.len()}
    pub fn is_empty(&self)->(out:bool) ensures out==self.registry().entries().is_empty(), {self.host.is_empty()}
    pub fn value_count(&self)->(out:usize) {self.services.value_count()}
    pub fn native_value(&self,port:Port)->(out:Option<&Arc<V>>)
        requires self.wf(),
        ensures out.is_some()==(exists|id:usize| self.state().control().resolves_to(port,id)
                && self.publications().available(&self.state(),id,port)),
            out.is_some() ==> exists|id:usize| self.state().control().resolves_to(port,id)
            && self.registry().entries().contains_key(id)
            && self.registry().entries()[id].recipe().provisions_spec().contains(port)
            && self.publications().available(&self.state(),id,port)
            && *out.unwrap()==self.publications().entries()[id].values()[(port.key,port.realm)],
    {
        let out=self.host.native_value(&self.services,port);
        proof {if out.is_some() {
            let id=choose|id:usize| self.state().control().resolves_to(port,id)
                && self.publications().available(&self.state(),id,port)
                && *out.unwrap()==self.publications().entries()[id].values()[(port.key,port.realm)];
            assert(self.linked(id));
        }}out
    }

    pub fn register(&mut self,parent:Option<usize>,realms:&BTreeMap<u64,u64>,anchor:Port,definition:PluginDefinition<R>,host:H)
        ->(out:Result<usize,(Error,PluginDefinition<R>,H)>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            out.is_err() ==> out->Err_0.1==definition && out->Err_0.2==host,
            out.is_ok() ==> final(self).registry().entries()[out->Ok_0].recipe().payload()==definition.payload()
                && final(self).registry().entries()[out->Ok_0].bookkeeping()==host
                && refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),out->Ok_0,Rule::Insert),
    {
        let ghost prior=*self;let out=self.host.register(parent,realms,anchor,definition,host);
        proof {self.generations(&prior);reveal(Kernel::generation_of);reveal(Kernel::registered);reveal(Kernel::paper);reveal(Kernel::phase_of);reveal(LifecycleState::same);reveal(Kernel::unchanged);
            if out.is_ok() {
                let id=out->Ok_0;assert(prior.linked(id));assert(!prior.publications().entries().contains_key(id));
                assert(prior.linked(id));self.generation_step(&prior,id,Rule::Insert);self.transition(&prior,id,Rule::Insert);
            } else {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}
        }out
    }
    pub open spec fn owns_execution<C,G,I>(&self,id:usize,execution:&Execution<V,C,G,I>)->bool {
        self.episode_owners().contains_key(id) && self.episode_owners()[id].owns(execution)
    }
    pub fn matches_execution<C,G,I>(&self,id:usize,execution:&Execution<V,C,G,I>)->(out:bool)
        ensures out==self.owns_execution(id,execution),
    {match self.owners.get(&id) {Some(owner)=>owner.matches(execution),None=>false}}
    pub fn begin_managed_execution<C,G,I>(&mut self,id:usize,domain:u64)->(out:Result<Execution<V,C,G,I>,Error>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).publications()==old(self).publications(),out.is_err() ==> final(self).episode_owners()==old(self).episode_owners(),
            out.is_ok() ==> final(self).episode_owners()==old(self).episode_owners().insert(id,EpisodeOwner {origin:out->Ok_0.origin().unwrap(),work_domain:domain}),
            out.is_ok() ==> out->Ok_0.wf() && out->Ok_0.value_state().is_some()
                && out->Ok_0.value_state().unwrap().capture().control==final(self).state().control()
                && out->Ok_0.value_state().unwrap().capture().sources==crate::lifecycle_state::services::capture::sources(final(self).publications().entries())
                && out->Ok_0.value_state().unwrap().capture().work_domain==domain
                && out->Ok_0.value_state().unwrap().provisions()==final(self).registry().entries()[id].recipe().provisions_spec()
                && final(self).state().execution_matches(id,&out->Ok_0.work_state(),&out->Ok_0.cleanup_state())
                && (forall|b:crate::Binding| out->Ok_0.value_state().unwrap().bindings().contains(b)==final(self).state().control().binding_recorded(id,b))
                && (forall|key:(usize,u64,u64)| #[trigger] out->Ok_0.value_state().unwrap().imports().contains_key(key)==(
                    out->Ok_0.value_state().unwrap().bindings().contains(crate::Binding {provider:key.0,key:key.1,realm:key.2})
                    && final(self).publications().available(&final(self).state(),key.0,Port {key:key.1,realm:key.2})))
                && (forall|key:(usize,u64,u64)| #[trigger] out->Ok_0.value_state().unwrap().imports().contains_key(key) ==>
                    out->Ok_0.value_state().unwrap().imports()[key]==final(self).publications().entries()[key.0].values()[(key.1,key.2)])
                && refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),id,Rule::Begin),
    {
        let ghost prior=*self;let out=self.host.begin_managed_execution(id,&self.services,domain);
        if let Ok(execution)=&out {
            self.owners.insert(id,EpisodeOwner {origin:execution.lifecycle_ticket().unwrap(),work_domain:domain});
        }
        proof {reveal(Kernel::paper);reveal(Kernel::phase_of);reveal(LifecycleState::same);reveal(Kernel::unchanged);reveal(Kernel::generations_preserved);
            if out.is_ok() {assert(prior.linked(id));assert(self.linked(id));assert(!prior.publications().entries().contains_key(id));self.transition(&prior,id,Rule::Begin);}
            else {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}
        }out
    }
    pub fn finish_managed_execution<C,G,I>(&mut self,id:usize,execution:&mut Execution<V,C,G,I>)->(out:Result<(),Error>)
        requires old(self).wf(),old(execution).wf(),
        ensures out.is_ok() ==> old(self).owns_execution(id,old(execution)),
            final(self).wf(),final(execution).wf(),final(execution).capture()==old(execution).capture(),
            out.is_err() ==> final(self).publications()==old(self).publications() && *final(execution)==*old(execution),
            out.is_ok() ==> final(self).publications().entries()[id].values()==final(execution).value_state().unwrap().owned()
                && final(self).publications().entries()[id].origin()==final(execution).origin().unwrap()
                && final(self).publications().entries()[id].capture()==old(execution).value_state().unwrap().capture()
                && refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),id,Rule::Finish),
    {
        if !self.matches_execution(id,execution) {return Err(Error::InvalidState);}
        let ghost prior=*self;
        let recipe=match self.host.registration(id) {Some(recipe)=>recipe,None=>return Err(Error::Unknown)};
        let values=match execution.native() {Some(values)=>values,None=>return Err(Error::InvalidState)};
        if !values.matches_provisions(recipe.provisions()) {return Err(Error::InvalidState);}
        let out=self.host.finish_managed_execution(id,&mut self.services,execution);
        proof {self.generations(&prior);reveal(Kernel::generation_of);reveal(Kernel::registered);reveal(Kernel::paper);reveal(Kernel::phase_of);reveal(Kernel::unchanged);
            if out.is_ok() {
                assert(self.linked(id));assert(prior.linked(id));self.generation_step(&prior,id,Rule::Finish);self.transition(&prior,id,Rule::Finish);
            } else {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}
        }out
    }
    pub fn release_managed_execution<C,G,I>(&mut self,id:usize,execution:&mut Execution<V,C,G,I>)
        ->(out:Result<(CleanupOutcome,ReleasedNativeValues<V>),Error>)
        requires old(self).wf(),old(execution).wf(),
        ensures out.is_ok() ==> old(self).owns_execution(id,old(execution)),
            final(self).wf(),final(execution).wf(),final(execution).capture()==old(execution).capture(),
            out.is_err() ==> final(self).publications()==old(self).publications() && *final(execution)==*old(execution),
            out.is_ok() ==> final(self).episode_owners()==old(self).episode_owners().remove(id)
                && final(self).publications().entries()==old(self).publications().entries().remove(id)
                && old(execution).work_state().idle() && old(execution).cleanup_state().all_drained()
                && out->Ok_0.1.owned()==old(execution).value_state().unwrap().owned()
                && out->Ok_0.1.imports()==old(execution).value_state().unwrap().imports()
                && out->Ok_0.1.imports()==old(execution).value_state().unwrap().capture().imports
                && refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),id,Rule::Unload),
    {
        if !self.matches_execution(id,execution) {return Err(Error::InvalidState);}
        let ghost prior=*self;let out=self.host.release_managed_execution(id,&mut self.services,execution);
        if out.is_ok() {self.owners.remove(&id);}
        proof {self.generations(&prior);reveal(Kernel::generation_of);reveal(Kernel::registered);reveal(Kernel::paper);reveal(Kernel::phase_of);reveal(LifecycleState::same);reveal(Kernel::unchanged);
            if out.is_ok() {assert(prior.linked(id));assert(self.linked(id));self.generation_step(&prior,id,Rule::Unload);self.transition(&prior,id,Rule::Unload);} else {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}
        }out
    }
    pub fn remove(&mut self,id:usize)->(out:Result<NativeEntry<R,H>,Error>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            out.is_ok() ==> out->Ok_0==old(self).registry().entries()[id]
                && !final(self).registry().entries().contains_key(id),
    {
        let ghost prior=*self;let out=self.host.remove(id);
        proof {self.generations(&prior);reveal(Kernel::generation_of);reveal(Kernel::registered);reveal(Kernel::paper);reveal(Kernel::phase_of);reveal(LifecycleState::same);reveal(Kernel::unchanged);
            if out.is_ok() {assert(prior.linked(id));assert(!prior.publications().entries().contains_key(id));assert(prior.linked(id));self.generation_step(&prior,id,Rule::Remove);self.transition(&prior,id,Rule::Remove);}
            else {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}
        }out
    }
    pub fn replace(&mut self,id:usize,payload:R)->(out:Result<R,(Error,R)>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).state()==old(self).state(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            out.is_ok() ==> final(self).registry().entries()[id].recipe().payload()==payload
                && out->Ok_0==old(self).registry().entries()[id].recipe().payload(),
            out.is_err() ==> out->Err_0.1==payload,
    {
        let ghost prior=*self;let out=self.host.replace(id,payload);
        proof {reveal(Kernel::generations_preserved);self.unchanged(&prior);}out
    }
    pub fn call<A,O>(&mut self,id:usize,invocation:RegisteredInvocation<A>)->(out:Result<WorkReceipt<O>,RegisteredInvocation<A>>)
        where R:FnMut(A)->O,
        requires old(self).wf(),old(self).registry().entries().contains_key(id) ==>
            old(self).registry().entries()[id].recipe().payload().requires((invocation.work().value(),)),
        ensures final(self).wf(),final(self).state()==old(self).state(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            out.is_err() ==> out->Err_0==invocation,
            out.is_ok() ==> old(self).episode_owners().contains_key(id)
                && old(self).episode_owners()[id].admits(&invocation)
                && old(self).state().root_invocation_enabled(invocation.lifecycle())
                && out->Ok_0.origin()==invocation.work().origin()
                && old(self).registry().entries()[id].recipe().payload().ensures((invocation.work().value(),),out->Ok_0.value()),
    {
        match self.owners.get(&id) {Some(owner)=>{if !owner.matches_invocation(&invocation) {return Err(invocation);}},None=>return Err(invocation)}
        let ghost prior=*self;let out=self.host.call(id,invocation);
        proof {reveal(Kernel::generations_preserved);self.unchanged(&prior);}out
    }
    pub fn admit_managed_root<C,G,I,A>(&self,id:usize,execution:&mut Execution<V,C,G,I>,argument:A)
        ->(out:Result<RegisteredInvocation<A>,A>)
        requires self.wf(),old(execution).wf(),
        ensures final(execution).wf(),final(execution).capture()==old(execution).capture(),out.is_err() ==> out->Err_0==argument && *final(execution)==*old(execution),
            out.is_ok() ==> out->Ok_0.work().value()==argument && out->Ok_0.owner()==id
                && self.owns_execution(id,old(execution)) && self.owns_execution(id,final(execution))
                && self.episode_owners()[id].admits(&out->Ok_0)
                && self.state().root_invocation_enabled(out->Ok_0.lifecycle()),
    {if !self.matches_execution(id,execution) {return Err(argument);}self.host.admit_managed_root(id,execution,argument)}

    pub fn retire(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            out.is_ok() ==> refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),id,Rule::Retire),
    {
        let ghost prior=*self;let out=self.host.retire(id);
        proof {self.generations(&prior);reveal(Kernel::generation_of);reveal(Kernel::registered);reveal(Kernel::paper);reveal(Kernel::phase_of);reveal(LifecycleState::same);reveal(Kernel::unchanged);
            if out.is_ok() {assert(prior.linked(id));self.generation_step(&prior,id,Rule::Retire);self.transition(&prior,id,Rule::Retire);} else {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}
        }out
    }

    pub fn leave(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            out.is_ok() ==> refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),id,Rule::Restart),
    {
        let ghost prior=*self;let out=self.host.leave(id);
        proof {self.generations(&prior);reveal(Kernel::generation_of);reveal(Kernel::registered);reveal(Kernel::paper);reveal(Kernel::phase_of);reveal(LifecycleState::same);reveal(Kernel::unchanged);
            if out.is_ok() {assert(prior.linked(id));self.generation_step(&prior,id,Rule::Restart);self.transition(&prior,id,Rule::Restart);} else {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}
        }out
    }

    pub fn withdraw_managed_execution<C,G,I>(&mut self,id:usize,execution:&mut Execution<V,C,G,I>,retiring:bool)->(out:Result<(),Error>)
        requires old(self).wf(),old(execution).wf(),
        ensures out.is_ok() ==> old(self).owns_execution(id,old(execution)),
            final(self).wf(),final(execution).wf(),final(execution).capture()==old(execution).capture(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(execution).value_state()==old(execution).value_state(),final(execution).cleanup_state()==old(execution).cleanup_state(),
            out.is_ok() ==> !final(execution).work_state().accepts(),out.is_err() ==> *final(execution)==*old(execution),
    {
        if !self.matches_execution(id,execution) {return Err(Error::InvalidState);}
        let ghost prior=*self;let out=self.host.withdraw_managed_execution(id,execution,retiring);
        proof {self.generations(&prior);reveal(Kernel::generation_of);reveal(Kernel::registered);reveal(Kernel::paper);reveal(Kernel::phase_of);reveal(LifecycleState::same);reveal(Kernel::unchanged);
            if out.is_ok() {assert(prior.linked(id));self.generation_step(&prior,id,if retiring {Rule::Retire} else {Rule::Restart});self.transition(&prior,id,if retiring {Rule::Retire} else {Rule::Restart});} else {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}
        }out
    }

    pub fn settle_managed_execution<C,G,I>(&mut self,id:usize,execution:&Execution<V,C,G,I>)->(out:Result<(),Error>)
        requires old(self).wf(),execution.wf(),
        ensures out.is_ok() ==> old(self).owns_execution(id,execution),
            final(self).wf(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).state().control().unchanged(&old(self).state().control()),
    {
        if !self.matches_execution(id,execution) {return Err(Error::InvalidState);}
        let ghost prior=*self;let out=self.host.settle_managed_execution(id,execution);
        proof {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}out
    }

    pub fn fail_managed_execution<C,G,I>(&mut self,id:usize,execution:&Execution<V,C,G,I>)->(out:Result<(),Error>)
        requires old(self).wf(),execution.wf(),
        ensures out.is_ok() ==> old(self).owns_execution(id,execution),
            final(self).wf(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).state().control().unchanged(&old(self).state().control()),
    {
        if !self.matches_execution(id,execution) {return Err(Error::InvalidState);}
        let ghost prior=*self;let out=self.host.fail_managed_execution(id,execution);
        proof {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}out
    }

    pub fn retry_managed_execution<C,G,I>(&mut self,id:usize,execution:&mut Execution<V,C,G,I>)->(out:Result<ActionTicket,Error>)
        requires old(self).wf(),old(execution).wf(),
        ensures out.is_ok() ==> old(self).owns_execution(id,old(execution)),
            final(self).wf(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).state().control().unchanged(&old(self).state().control()),
            final(execution).wf(),final(execution).value_state()==old(execution).value_state(),
    {
        if !self.matches_execution(id,execution) {return Err(Error::InvalidState);}
        let ghost prior=*self;let out=self.host.retry_managed_execution(id,execution);
        proof {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}out
    }

    pub fn begin_cleanup(&mut self,id:usize)->(out:Result<ActionTicket,Error>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).state().control().paper()==old(self).state().control().paper(),
    {
        let ghost prior=*self;let out=self.host.begin_cleanup(id);
        proof {self.unchanged(&prior);}out
    }

    pub fn compact_bindings(&mut self)->(out:usize)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).state().control().paper()==old(self).state().control().paper(),
    {
        let ghost prior=*self;let out=self.host.compact_bindings();
        proof {self.unchanged(&prior);}out
    }

    pub fn compact_declarations(&mut self)->(out:usize)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).state().control().paper()==old(self).state().control().paper(),
    {
        let ghost prior=*self;let out=self.host.compact_declarations();
        proof {self.unchanged(&prior);}out
    }

    #[allow(clippy::type_complexity)]
    pub fn register_shared_child(&mut self,child:&SharedChild,realms:&BTreeMap<u64,u64>,anchor:Port,definition:PluginDefinition<R>,host:H)
        ->(out:ChildTransition<Result<usize,(Error,PluginDefinition<R>,H)>>)
        requires old(self).wf(),child.wf(),
        ensures final(self).wf(),out.wf(child),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            out.result.is_err() ==> out.result->Err_0.1==definition && out.result->Err_0.2==host,
            out.result.is_ok() ==> final(self).registry().entries()[out.result->Ok_0].recipe().payload()==definition.payload()
                && final(self).registry().entries()[out.result->Ok_0].bookkeeping()==host,
    {
        let ghost prior=*self;let out=self.host.register_shared_child(child,realms,anchor,definition,host);
        proof {self.generations(&prior);reveal(Kernel::generation_of);reveal(Kernel::registered);reveal(Kernel::paper);reveal(Kernel::phase_of);reveal(LifecycleState::same);reveal(Kernel::unchanged);
            if out.result.is_ok() {let id=out.result->Ok_0;assert(prior.linked(id));assert(!prior.publications().entries().contains_key(id));assert(prior.linked(id));self.generation_step(&prior,id,Rule::Insert);self.transition(&prior,id,Rule::Insert);}
            else {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}
        }out
    }
    pub fn retire_shared_child(&mut self,child:&SharedChild)->(out:ChildTransition<Result<Option<ChildIdentity>,Error>>)
        requires old(self).wf(),child.wf(),
        ensures final(self).wf(),out.wf(child),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
    {
        let ghost prior=*self;let out=self.host.retire_shared_child(child);
        proof {self.generations(&prior);reveal(Kernel::generation_of);reveal(Kernel::registered);reveal(Kernel::paper);reveal(Kernel::phase_of);reveal(LifecycleState::same);reveal(Kernel::unchanged);
            if out.result.is_ok() && out.result->Ok_0.is_some() && prior.state().control().registered(out.result->Ok_0.unwrap().child()) {
                let id=out.result->Ok_0.unwrap().child();assert(prior.linked(id));self.generation_step(&prior,id,Rule::Retire);self.transition(&prior,id,Rule::Retire);
            } else {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}
        }out
    }

}
}
