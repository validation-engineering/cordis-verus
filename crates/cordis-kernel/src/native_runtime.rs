//! The production native registry and its published values have one owner.
//! No independent service store can be substituted at Begin, Finish or Unload.
//! Its joint invariant covers real registry membership, episode generations,
//! complete declared values and retention throughout restoration. Opaque host
//! bookkeeping, escaped episode mutexes and slot interiors are separate bounds.
#[path = "native_configuration.rs"]
pub mod configuration;
#[path = "native_history.rs"]
pub mod history;
#[path = "native_owner.rs"]
pub mod owner;
#[path = "native_production.rs"]
pub mod production;
#[path = "recipe_history.rs"]
pub mod recipes;
#[path = "native_slot_runtime.rs"]
pub mod slots;
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
use crate::refinement::Rule;
use crate::reversible_value::function::Body;
use crate::reversible_value::joint;
use crate::setup_work::WorkReceipt;
#[cfg(verus_keep_ghost)]
use crate::{
    refinement::{self},
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
pub struct NativeRuntime<R,H,V> {host:NativeHost<R,H>,services:NativeServices<V>,history:Ghost<History<V>>,positions:Ghost<Seq<nat>>,owners:BTreeMap<usize,EpisodeOwner>,joint:joint::Member,recipes:recipes::Ledger<R>}
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
    pub closed spec fn history_positions(&self)->Seq<nat> {self.positions@}
    pub closed spec fn joint_valid(&self)->bool {
        self.joint.wf() && self.joint.record()==(joint::Record::Native {state:self.observation().project(self.execution_history().labels.len())})
            && self.execution_history().indexed(self.history_positions(),self.joint.events(),self.joint.key())
    }
    pub closed spec fn journal_spec(&self)->joint::Journal {self.joint.journal()}
    pub closed spec fn recipe_history(&self)->recipes::History<R> {self.recipes.history()}
    pub closed spec fn recipe_valid(&self)->bool {
        self.recipes.wf() && self.recipes.journal()==self.journal_spec() && self.recipes.native()==self.joint_key()
            && self.recipes.current()==recipes::entries(self.registry().entries())
    }
    pub open spec fn wf(&self)->bool {self.core_wf() && self.recipe_valid()}
    pub open spec fn core_wf(&self)->bool {
        self.structural() && self.execution_history().valid() && self.execution_history().states.last()==self.observation()
            && self.joint_valid()
    }
    pub proof fn history_correspondence(&self)
        requires self.wf(),
        ensures self.execution_history().valid(),self.execution_history().states.last()==self.observation(),
            refinement::execution(self.execution_history().controls(),self.execution_history().labels,true),
            self.execution_history().base_only() ==> refinement::execution(self.execution_history().controls(),self.execution_history().labels,false)
                && refinement::reaches(self.execution_history().controls().first(),self.state().control().paper(),self.execution_history().labels.len(),false),
    {self.execution_history().correspondence();}
    pub fn recipe_snapshot(&self)->(out:recipes::Snapshot<R>)
        requires self.wf(),ensures out.certified(),out.history()==self.recipe_history(),out.native()==self.joint_key(),
            out.history().states.last()==recipes::entries(self.registry().entries()),out.joint_spec().journal_spec()==self.journal_spec(),
            out.joint_spec().last().contains_pair(self.joint_key(),joint::Record::Native {state:self.observation().project(self.execution_history().labels.len())}),
    {self.recipes.snapshot(&self.joint)}
    pub closed spec fn recipe_record_enabled(&self,event:joint::recipes::Event)->bool {
        self.recipes.wf() && self.recipes.journal()==self.journal_spec() && self.recipes.native()==self.joint_key()
            && recipes::step(self.recipes.current(),recipes::entries(self.registry().entries()),event)
            && joint::recipes::native_guard(self.observation().project(self.execution_history().labels.len()),event)
    }
    pub(crate) proof fn completed_recipe_call(&self,id:usize,version:u64,origin:ActionTicket,work:crate::setup_work::WorkTicket)
        requires self.wf(),self.registry().entries().contains_key(id),self.registry().entries()[id].recipe().version()==version,
            self.episode_owners().contains_key(id),self.episode_owners()[id].origin==origin,self.episode_owners()[id].work_domain==work.domain_id(),
            self.state().root_invocation_enabled(origin),origin.id==id,
        ensures self.recipe_record_enabled(joint::recipes::Event::Call {id,version,origin,work}),
    {
        reveal(Kernel::paper);reveal(Kernel::phase_of);reveal(Kernel::is_retired);
        let current=self.recipes.current();assert(current.contains_key(id));assert(current =~= current.insert(id,current[id]));
    }
    pub(crate) fn record_recipes(&mut self,Ghost(event):Ghost<joint::recipes::Event>)
        requires old(self).core_wf(),old(self).recipe_record_enabled(event),
        ensures final(self).wf(),final(self).recipe_history()==old(self).recipe_history().append(recipes::entries(old(self).registry().entries()),event),
            final(self).registry()==old(self).registry(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),final(self).execution_history()==old(self).execution_history(),final(self).history_positions()==old(self).history_positions(),
    {
        let tracked receipts=Map::<int,joint::Receipt>::tracked_empty();
        let _receipt=self.record_recipes_following::<int>(Ghost(event),Tracked(&receipts));
    }
    pub(crate) fn record_recipes_following<K>(&mut self,Ghost(event):Ghost<joint::recipes::Event>,Tracked(receipts):Tracked<&Map<K,joint::Receipt>>)->(out:Tracked<joint::Receipt>)
        requires old(self).core_wf(),old(self).recipe_record_enabled(event),
            forall|k:K| receipts.contains_key(k) ==> #[trigger] receipts[k].wf(),
        ensures out@.wf(),out@.journal()==old(self).journal_spec(),out@.event().change==(joint::Change::Recipes {event}),
            joint::classification::history(out@.events()),
            forall|k:K| receipts.contains_key(k) && #[trigger] receipts[k].journal()==out@.journal() ==> out@.follows(&receipts[k]),
            final(self).wf(),final(self).recipe_history()==old(self).recipe_history().append(recipes::entries(old(self).registry().entries()),event),
            final(self).registry()==old(self).registry(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),final(self).execution_history()==old(self).execution_history(),final(self).history_positions()==old(self).history_positions(),
    {
        let ghost prior=*self;
        let journal=self.joint.domain();let view=journal.write();self.joint.certify_write(&view);
        view.certify_receipts::<K>(Tracked(receipts));let ghost before=view.events();
        let view=self.recipes.advance(view,Ghost(recipes::entries(self.registry().entries())),Ghost(event));view.finish();
        let receipt=self.recipes.receipt();
        proof {
            joint::classification::classify_history(receipt@.events());
            assert forall|k:K| receipts.contains_key(k) && #[trigger] receipts[k].journal()==receipt@.journal() implies receipt@.follows(&receipts[k]) by {
                assert(receipt@.events().take(receipts[k].events().len() as int) =~= before.take(receipts[k].events().len() as int));
            }
            assert(self.registry()==prior.registry());assert(self.publications()==prior.publications());assert(self.episode_owners()==prior.episode_owners());
            assert forall|id:usize| #[trigger] self.linked(id) by {assert(prior.linked(id));}
            assert(self.structural());assert(self.observation()==prior.observation());assert(self.joint_valid());
            assert(self.core_wf());assert(self.recipe_valid());
        }
        receipt
    }
    /// A control step changes at most its actor; complete publication of that
    /// actor is checked separately at the actual Finish/Unload boundary.
    fn transition(&mut self,Ghost(prior):Ghost<Self>,Ghost(id):Ghost<usize>,Ghost(rule):Ghost<Rule>)
        requires prior.wf(),old(self).recipes==prior.recipes,
            old(self).execution_history()==prior.execution_history(),old(self).joint==prior.joint,old(self).history_positions()==prior.history_positions(),
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
        ensures final(self).core_wf(),final(self).recipes==old(self).recipes,final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),final(self).registry()==old(self).registry(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).execution_history().extends(prior.execution_history()),
    {
        proof {
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
        reveal(joint::changes);
        }
        let ghost prepared=*self;
        proof {history::project_step(prior.observation(),self.observation(),id,rule,prior.execution_history().labels.len());}
        self.joint.update(Ghost(joint::Record::Native {state:self.observation().project(self.execution_history().labels.len())}),Ghost(joint::Change::Native {actor:id,rule}));
        proof {
            prior.execution_history().append_indexed(prior.history_positions(),prior.joint.events(),self.joint.events(),self.joint.key(),self.observation(),id,rule);
            self.positions=Ghost(prior.history_positions().push((self.joint.events().len()-1) as nat));
        }
        proof {
            assert forall|n:usize| #[trigger] self.linked(n) by {assert(prepared.linked(n));}
            assert(self.structural());assert(self.joint_valid());
            assert(self.core_wf());
        }
    }
    proof fn unchanged(&self,prior:&Self)
        requires prior.wf(),self.joint==prior.joint,self.history_positions()==prior.history_positions(),self.episode_owners()==prior.episode_owners(),self.execution_history()==prior.execution_history(),self.registry().wf(),self.publications()==prior.publications(),
            self.state().protocol().domain_id()==prior.state().protocol().domain_id(),
            self.state().control().paper()==prior.state().control().paper(),
            self.state().control().generations_preserved(&prior.state().control()),
            forall|n:usize| #[trigger] prior.registry().entries().contains_key(n) ==>
                self.registry().entries()[n].recipe().provisions_spec()==prior.registry().entries()[n].recipe().provisions_spec(),
        ensures self.core_wf(),
            self.recipes==prior.recipes && recipes::entries(self.registry().entries())==prior.recipes.current() ==> self.wf(),
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
        let journal=joint::Journal::new();
        let joint=journal.allocate(Ghost(joint::Record::Native {state:initial.project(0)}));
        let ghost positions=seq![(joint.events().len()-1) as nat];
        let recipes=recipes::Ledger::new(&journal,Ghost(joint.key()));
        let out=Self {host,services,recipes,owners:BTreeMap::new(),history:Ghost(History {states:seq![initial],labels:Seq::empty()}),positions:Ghost(positions),joint};
        proof {assert forall|id:usize| #[trigger] out.linked(id) by {assert(!out.registry().entries().contains_key(id));assert(!refinement::registered(out.state().control().paper(),id));}
            assert forall|id:usize| !out.state().control().paper().fibers.dom().contains(id) by {
                assert(out.registry().entries().contains_key(id)==out.state().control().paper().fibers.dom().contains(id));
            }
            assert(out.state().control().paper().fibers.dom() =~= ISet::empty());
            assert(out.execution_history().valid());assert(out.execution_history().states.last()==out.observation());
            assert(recipes::entries(out.registry().entries()) =~= Map::empty());assert(out.recipe_valid());
        }out}
    /// Values allocated in this domain share the native lifecycle's actual
    /// commit order. Independent standalone values retain independent domains.
    pub fn execution_journal(&self)->(out:joint::Journal)
        ensures out==self.journal_spec(),
    {self.joint.domain()}
    pub closed spec fn joint_key(&self)->nat {self.joint.key()}
    pub(crate) fn certify_poll_control(&self,view:&joint::WriteView)
        requires self.wf(),view.wf(),view.journal_spec()==self.journal_spec(),
        ensures view.state().contains_pair(self.joint_key(),joint::Record::Native {state:self.observation().project(self.execution_history().labels.len())}),
            view.state()[self.joint_key()]->Native_state.owners==self.episode_owners(),
            view.state()[self.joint_key()]->Native_state.control==self.state().control().paper(),
    {self.joint.certify_write(view);}
    pub fn execution_snapshot(&self)->(out:joint::Snapshot)
        requires self.wf(),
        ensures out.certified(),out.domain()==self.journal_spec().source(),
            out.last().contains_key(self.joint_key()),out.last()[self.joint_key()]==(joint::Record::Native {state:self.observation().project(self.execution_history().labels.len())}),
            out.last()[self.joint_key()]->Native_state.control==self.state().control().paper(),
            self.execution_history().indexed(self.history_positions(),out.events(),self.joint_key()),
            joint::classification::history(out.events()),
    {
        let snapshot=self.publication_snapshot();
        let out=snapshot.into_joint();proof {out.classify();}out
    }
    /// A checkpoint of exact typed publications and their complete projection
    /// into the shared value/work/cleanup trajectory. Evidence is erased.
    pub fn publication_snapshot(&self)->(out:history::Snapshot<V>)
        requires self.wf(),
        ensures out.certified(),production::interpreted(out.joint_spec().events(),out.key()),out.history()==self.execution_history(),out.positions()==self.history_positions(),out.key()==self.joint_key(),
            out.joint_spec().certified(),out.joint_spec().domain()==self.journal_spec().source(),
            self.execution_history().indexed(self.history_positions(),out.joint_spec().events(),self.joint_key()),
            out.joint_spec().last().contains_pair(self.joint_key(),joint::Record::Native {state:self.observation().project(self.execution_history().labels.len())}),
    {
        let joint=self.joint.observe();
        proof {self.execution_history().extend_indexed(self.history_positions(),self.joint.events(),joint.events(),self.joint_key());}
        history::Snapshot::new(joint,Ghost(self.execution_history()),Ghost(self.history_positions()),Ghost(self.joint_key()))
    }
    /// Observe the native owner and its actual episode in one held read epoch.
    /// The domain premise follows from native Begin and the managed API's frame
    /// contracts; foreign/static executions use their own observation API.
    pub fn episode_snapshot<C,G,I>(&self,id:usize,execution:&Execution<V,C,G,I>)->(out:Option<history::Snapshot<V>>)
        requires self.wf(),execution.wf(),execution.execution_journal()==Some(self.journal_spec()),
        ensures out.is_some()==self.owns_execution(id,execution),
            out.is_some() ==> out.unwrap().certified() && out.unwrap().history()==self.execution_history()
                && out.unwrap().positions()==self.history_positions() && out.unwrap().key()==self.joint_key()
                && execution.observed(&out.unwrap().joint_spec())
                && out.unwrap().joint_spec().last().contains_pair(self.joint_key(),joint::Record::Native {
                    state:self.observation().project(self.execution_history().labels.len())})
                && self.episode_owners()[id].owns(execution),
    {
        if !self.matches_execution(id,execution) {return None;}
        let journal=self.execution_journal();let view=journal.read();
        self.joint.certify(&view);execution.certify(&view);
        proof {assert(execution.observed_state(view.state()));}
        let joint=view.finish();
        proof {self.execution_history().extend_indexed(self.history_positions(),self.joint.events(),joint.events(),self.joint_key());}
        Some(history::Snapshot::new(joint,Ghost(self.execution_history()),Ghost(self.history_positions()),Ghost(self.joint_key())))
    }
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
        ensures final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            final(self).wf(),final(self).state()==old(self).state(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            match out {
                Some(host)=>old(self).registry().entries().contains_key(id) && *host==old(self).registry().entries()[id].bookkeeping()
                    && final(self).registry().entries()==old(self).registry().entries().insert(id,old(self).registry().entries()[id].with_host(*final(host))),
                None=>!old(self).registry().entries().contains_key(id) && final(self).registry().entries()==old(self).registry().entries(),
            },
    {
        let ghost prior=*self;
        proof {
            assert forall|after:Self| after.recipes==prior.recipes && after.registry().entries().dom()==prior.registry().entries().dom() && after.joint==prior.joint && after.history_positions()==prior.history_positions() && after.registry().wf() && after.state()==prior.state() && after.publications()==prior.publications() && after.execution_history()==prior.execution_history() && after.episode_owners()==prior.episode_owners()
                && (forall|n:usize| #[trigger] prior.registry().entries().contains_key(n) ==>
                    after.registry().entries()[n].recipe()==prior.registry().entries()[n].recipe())
                implies #[trigger] after.wf() by {
                reveal(Kernel::generations_preserved);assert(recipes::entries(after.registry().entries()) =~= prior.recipes.current());after.unchanged(&prior);
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
        ensures out.is_ok() ==> final(self).recipe_history()==old(self).recipe_history().append(recipes::entries(final(self).registry().entries()),joint::recipes::Event::Insert {id:out->Ok_0}),
            !(out.is_ok()) ==> final(self).recipe_history()==old(self).recipe_history(),
            final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            final(self).wf(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            out.is_err() ==> out->Err_0.1==definition && out->Err_0.2==host,
            out.is_ok() ==> final(self).registry().entries()[out->Ok_0].recipe().payload()==definition.payload()
                && final(self).registry().entries()[out->Ok_0].recipe().realms()==realms@
                && final(self).registry().entries()[out->Ok_0].recipe().anchor_port()==anchor
                && final(self).registry().entries()[out->Ok_0].bookkeeping()==host
                && refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),out->Ok_0,Rule::Insert),
    {
        let ghost prior=*self;let out=self.host.register(parent,realms,anchor,definition,host);
        proof {self.generations(&prior);reveal(Kernel::generation_of);reveal(Kernel::registered);reveal(Kernel::paper);reveal(Kernel::phase_of);reveal(LifecycleState::same);reveal(Kernel::unchanged);
            if out.is_ok() {
                let id=out->Ok_0;assert(prior.linked(id));assert(!prior.publications().entries().contains_key(id));
                assert(prior.linked(id));self.generation_step(&prior,id,Rule::Insert);
            } else {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}
        }
        if out.is_ok() {self.transition(Ghost(prior),Ghost(out->Ok_0),Ghost(Rule::Insert));proof {assert(recipes::entries(self.registry().entries()) =~= prior.recipes.current().insert(out->Ok_0,self.registry().entries()[out->Ok_0].recipe()));}self.record_recipes(Ghost(joint::recipes::Event::Insert {id:out->Ok_0}));}
        out
    }
    pub open spec fn owns_execution<C,G,I>(&self,id:usize,execution:&Execution<V,C,G,I>)->bool {
        self.episode_owners().contains_key(id) && self.episode_owners()[id].owns(execution)
    }
    pub fn matches_execution<C,G,I>(&self,id:usize,execution:&Execution<V,C,G,I>)->(out:bool)
        ensures out==self.owns_execution(id,execution),
    {match self.owners.get(&id) {Some(owner)=>owner.matches(execution),None=>false}}
    pub fn begin_managed_execution<C,G,I>(&mut self,id:usize,domain:u64)->(out:Result<Execution<V,C,G,I>,Error>)
        requires old(self).wf(),
        ensures final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            final(self).wf(),final(self).publications()==old(self).publications(),out.is_err() ==> final(self).episode_owners()==old(self).episode_owners(),
            out.is_ok() ==> final(self).episode_owners()==old(self).episode_owners().insert(id,EpisodeOwner {origin:out->Ok_0.origin().unwrap(),work_domain:domain}),
            out.is_ok() ==> out->Ok_0.execution_journal()==Some(final(self).journal_spec()) && out->Ok_0.wf() && out->Ok_0.value_state().is_some()
                && out->Ok_0.value_state().unwrap().capture().control==final(self).state().control()
                && out->Ok_0.value_state().unwrap().capture().sources==crate::lifecycle_state::services::capture::sources(final(self).publications().entries())
                && out->Ok_0.value_state().unwrap().capture().work_domain==domain
                && out->Ok_0.value_state().unwrap().provisions()==final(self).registry().entries()[id].recipe().provisions_spec()
                && out->Ok_0.capture().unwrap().realms==final(self).registry().entries()[id].recipe().realms()
                && out->Ok_0.capture().unwrap().anchor==final(self).registry().entries()[id].recipe().anchor_port()
                && final(self).state().execution_matches(id,&out->Ok_0.work_state(),&out->Ok_0.cleanup_state())
                && (forall|b:crate::Binding| out->Ok_0.value_state().unwrap().bindings().contains(b)==final(self).state().control().binding_recorded(id,b))
                && (forall|key:(usize,u64,u64)| #[trigger] out->Ok_0.value_state().unwrap().imports().contains_key(key)==(
                    out->Ok_0.value_state().unwrap().bindings().contains(crate::Binding {provider:key.0,key:key.1,realm:key.2})
                    && final(self).publications().available(&final(self).state(),key.0,Port {key:key.1,realm:key.2})))
                && (forall|key:(usize,u64,u64)| #[trigger] out->Ok_0.value_state().unwrap().imports().contains_key(key) ==>
                    out->Ok_0.value_state().unwrap().imports()[key]==final(self).publications().entries()[key.0].values()[(key.1,key.2)])
                && refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),id,Rule::Begin),
    {
        let ghost prior=*self;let mut out=self.host.begin_managed_execution(id,&self.services,domain);
        if let Ok(execution)=&out {
            self.owners.insert(id,EpisodeOwner {origin:execution.lifecycle_ticket().unwrap(),work_domain:domain});
        }
        proof {reveal(Kernel::paper);reveal(Kernel::phase_of);reveal(LifecycleState::same);reveal(Kernel::unchanged);reveal(Kernel::generations_preserved);
            if out.is_ok() {assert(prior.linked(id));assert(self.linked(id));assert(!prior.publications().entries().contains_key(id));}
            else {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}
        }
        if out.is_ok() {self.transition(Ghost(prior),Ghost(id),Ghost(Rule::Begin));}
        if let Ok(execution)=&mut out {
            let journal=self.execution_journal();execution.attach_execution(&journal);
        }
        out
    }
    pub fn finish_managed_execution<C,G,I>(&mut self,id:usize,execution:&mut Execution<V,C,G,I>)->(out:Result<(),Error>)
        requires old(self).wf(),old(execution).wf(),
        ensures final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            out.is_ok() ==> old(self).owns_execution(id,old(execution)),
            final(self).wf(),final(execution).wf(),final(execution).execution_journal()==old(execution).execution_journal(),final(execution).value_attempts()==old(execution).value_attempts(),final(execution).capture()==old(execution).capture(),
            out.is_err() ==> final(self).publications()==old(self).publications() && *final(execution)==*old(execution),
            out.is_ok() ==> final(self).publications().entries()[id].values()==final(execution).value_state().unwrap().owned()
                && final(self).publications().entries()[id].origin()==final(execution).origin().unwrap()
                && final(self).publications().entries()[id].capture()==old(execution).value_state().unwrap().capture()
                && refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),id,Rule::Finish),
            final(execution).status_links()==old(execution).status_links(),
    {
        if !self.matches_execution(id,execution) {return Err(Error::InvalidState);}
        let ghost prior=*self;
        let recipe=match self.host.registration(id) {Some(recipe)=>recipe,None=>return Err(Error::Unknown)};
        let values=match execution.native() {Some(values)=>values,None=>return Err(Error::InvalidState)};
        if !values.matches_provisions(recipe.provisions()) {return Err(Error::InvalidState);}
        let out=self.host.finish_managed_execution(id,&mut self.services,execution);
        proof {self.generations(&prior);reveal(Kernel::generation_of);reveal(Kernel::registered);reveal(Kernel::paper);reveal(Kernel::phase_of);reveal(Kernel::unchanged);
            if out.is_ok() {
                assert(self.linked(id));assert(prior.linked(id));self.generation_step(&prior,id,Rule::Finish);
            } else {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}
        }
        if out.is_ok() {self.transition(Ghost(prior),Ghost(id),Ghost(Rule::Finish));}
        out
    }
    pub fn release_managed_execution<C,G,I>(&mut self,id:usize,execution:&mut Execution<V,C,G,I>)
        ->(out:Result<(CleanupOutcome,ReleasedNativeValues<V>),Error>)
        requires old(self).wf(),old(execution).wf(),
        ensures final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            out.is_ok() ==> old(self).owns_execution(id,old(execution)),
            final(self).wf(),final(execution).wf(),final(execution).execution_journal()==old(execution).execution_journal(),final(execution).value_attempts()==old(execution).value_attempts(),final(execution).capture()==old(execution).capture(),
            out.is_err() ==> final(self).publications()==old(self).publications() && *final(execution)==*old(execution),
            out.is_ok() ==> final(self).episode_owners()==old(self).episode_owners().remove(id)
                && final(self).publications().entries()==old(self).publications().entries().remove(id)
                && old(execution).work_state().idle() && old(execution).cleanup_state().all_drained()
                && out->Ok_0.1.owned()==old(execution).value_state().unwrap().owned()
                && out->Ok_0.1.imports()==old(execution).value_state().unwrap().imports()
                && out->Ok_0.1.imports()==old(execution).value_state().unwrap().capture().imports
                && refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),id,Rule::Unload),
            final(execution).status_links()==old(execution).status_links(),
    {
        if !self.matches_execution(id,execution) {return Err(Error::InvalidState);}
        let ghost prior=*self;let out=self.host.release_managed_execution(id,&mut self.services,execution);
        if out.is_ok() {self.owners.remove(&id);}
        proof {self.generations(&prior);reveal(Kernel::generation_of);reveal(Kernel::registered);reveal(Kernel::paper);reveal(Kernel::phase_of);reveal(LifecycleState::same);reveal(Kernel::unchanged);
            if out.is_ok() {assert(prior.linked(id));assert(self.linked(id));self.generation_step(&prior,id,Rule::Unload);} else {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}
        }
        if out.is_ok() {self.transition(Ghost(prior),Ghost(id),Ghost(Rule::Unload));}
        out
    }
    pub fn remove(&mut self,id:usize)->(out:Result<NativeEntry<R,H>,Error>)
        requires old(self).wf(),
        ensures out.is_ok() ==> final(self).recipe_history()==old(self).recipe_history().append(recipes::entries(final(self).registry().entries()),joint::recipes::Event::Remove {id}),
            !(out.is_ok()) ==> final(self).recipe_history()==old(self).recipe_history(),
            final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            final(self).wf(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            out.is_ok() ==> out->Ok_0==old(self).registry().entries()[id]
                && !final(self).registry().entries().contains_key(id),
    {
        let ghost prior=*self;let out=self.host.remove(id);
        proof {self.generations(&prior);reveal(Kernel::generation_of);reveal(Kernel::registered);reveal(Kernel::paper);reveal(Kernel::phase_of);reveal(LifecycleState::same);reveal(Kernel::unchanged);
            if out.is_ok() {assert(prior.linked(id));assert(!prior.publications().entries().contains_key(id));assert(prior.linked(id));self.generation_step(&prior,id,Rule::Remove);}
            else {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}
        }
        if out.is_ok() {self.transition(Ghost(prior),Ghost(id),Ghost(Rule::Remove));proof {assert(recipes::entries(self.registry().entries()) =~= prior.recipes.current().remove(id));}self.record_recipes(Ghost(joint::recipes::Event::Remove {id}));}
        out
    }
    pub fn replace(&mut self,id:usize,payload:R)->(out:Result<R,(Error,R)>)
        requires old(self).wf(),
        ensures out.is_ok() ==> final(self).recipe_history()==old(self).recipe_history().append(recipes::entries(final(self).registry().entries()),joint::recipes::Event::Replace {id}),
            !(out.is_ok()) ==> final(self).recipe_history()==old(self).recipe_history(),
            final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            final(self).wf(),final(self).state()==old(self).state(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            out.is_ok()==(old(self).registry().entries().contains_key(id) && old(self).registry().entries()[id].recipe().version()<u64::MAX),
            final(self).registry().entries().dom()==old(self).registry().entries().dom(),
            forall|n:usize| n!=id && old(self).registry().entries().contains_key(n) ==> #[trigger] final(self).registry().entries()[n]==old(self).registry().entries()[n],
            out.is_err() ==> final(self).registry().entries()==old(self).registry().entries(),
            out.is_ok() ==> final(self).registry().entries()[id].recipe().same_identity(&old(self).registry().entries()[id].recipe())
                && final(self).registry().entries()[id].recipe().version()==old(self).registry().entries()[id].recipe().version()+1
                && final(self).registry().entries()[id].recipe().payload()==payload
                && out->Ok_0==old(self).registry().entries()[id].recipe().payload(),
            forall|n:usize| #[trigger] old(self).registry().entries().contains_key(n) ==>
                final(self).registry().entries()[n].bookkeeping()==old(self).registry().entries()[n].bookkeeping(),
            out.is_err() ==> out->Err_0.1==payload,
    {
        let ghost prior=*self;let out=self.host.replace(id,payload);
        proof {reveal(Kernel::generations_preserved);self.unchanged(&prior);}
        if out.is_ok() {proof {assert(recipes::entries(self.registry().entries()) =~= prior.recipes.current().insert(id,self.registry().entries()[id].recipe()));}self.record_recipes(Ghost(joint::recipes::Event::Replace {id}));}
        out
    }
    pub fn call<A,O>(&mut self,id:usize,invocation:RegisteredInvocation<A>)->(out:Result<WorkReceipt<O>,RegisteredInvocation<A>>)
        where R:FnMut(A)->O,
        requires old(self).wf(),old(self).registry().entries().contains_key(id) ==>
            old(self).registry().entries()[id].recipe().payload().requires((invocation.work().value(),)),
        ensures out.is_ok() ==> final(self).recipe_history()==old(self).recipe_history().append(recipes::entries(final(self).registry().entries()),joint::recipes::Event::Call {id,version:invocation.version(),origin:invocation.lifecycle(),work:invocation.work().origin()}),
            !(out.is_ok()) ==> final(self).recipe_history()==old(self).recipe_history(),
            final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            final(self).wf(),final(self).state()==old(self).state(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            out.is_err() ==> out->Err_0==invocation,
            out.is_ok() ==> old(self).episode_owners().contains_key(id)
                && old(self).episode_owners()[id].admits(&invocation)
                && old(self).state().root_invocation_enabled(invocation.lifecycle())
                && out->Ok_0.origin()==invocation.work().origin()
                && old(self).registry().entries()[id].recipe().payload().ensures((invocation.work().value(),),out->Ok_0.value()),
    {
        match self.owners.get(&id) {Some(owner)=>{if !owner.matches_invocation(&invocation) {return Err(invocation);}},None=>return Err(invocation)}
        let ghost prior=*self;let ghost admitted=invocation;let out=self.host.call(id,invocation);
        proof {reveal(Kernel::generations_preserved);self.unchanged(&prior);}
        if out.is_ok() {
            proof {reveal(Kernel::paper);reveal(Kernel::phase_of);reveal(Kernel::is_retired);
                assert(recipes::entries(self.registry().entries()) =~= prior.recipes.current().insert(id,self.registry().entries()[id].recipe()));}
            self.record_recipes(Ghost(joint::recipes::Event::Call {id,version:admitted.version(),origin:admitted.lifecycle(),work:admitted.work().origin()}));
        }
        out
    }
    pub fn admit_managed_root<C,G,I,A>(&self,id:usize,execution:&mut Execution<V,C,G,I>,argument:A)
        ->(out:Result<RegisteredInvocation<A>,A>)
        requires self.wf(),old(execution).wf(),
        ensures final(execution).wf(),final(execution).execution_journal()==old(execution).execution_journal(),final(execution).value_attempts()==old(execution).value_attempts(),final(execution).capture()==old(execution).capture(),
            final(execution).cleanup_state()==old(execution).cleanup_state(),final(execution).value_state()==old(execution).value_state(),
            final(execution).work_state().domain_id()==old(execution).work_state().domain_id(),out.is_err() ==> out->Err_0==argument && *final(execution)==*old(execution),
            out.is_ok() ==> out->Ok_0.work().value()==argument && out->Ok_0.owner()==id
                && self.owns_execution(id,old(execution)) && self.owns_execution(id,final(execution))
                && self.episode_owners()[id].admits(&out->Ok_0)
                && self.state().root_invocation_enabled(out->Ok_0.lifecycle())
                && out->Ok_0.version()==self.registry().entries()[id].recipe().version()
                && final(execution).work_state().root_status()==crate::setup_work::RootStatus::Queued
                && out->Ok_0.work().origin().request_id()==0 && out->Ok_0.work().origin().request_kind()==crate::setup_work::WorkKind::Root,
            final(execution).status_links()==old(execution).status_links(),
    {if !self.matches_execution(id,execution) {return Err(argument);}self.host.admit_managed_root(id,execution,argument)}

    pub fn retire(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            final(self).wf(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            out.is_ok() ==> refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),id,Rule::Retire),
    {
        let ghost prior=*self;let out=self.host.retire(id);
        proof {self.generations(&prior);reveal(Kernel::generation_of);reveal(Kernel::registered);reveal(Kernel::paper);reveal(Kernel::phase_of);reveal(LifecycleState::same);reveal(Kernel::unchanged);
            if out.is_ok() {assert(prior.linked(id));self.generation_step(&prior,id,Rule::Retire);} else {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}
        }
        if out.is_ok() {self.transition(Ghost(prior),Ghost(id),Ghost(Rule::Retire));}
        out
    }

    pub fn leave(&mut self,id:usize)->(out:Result<(),Error>)
        requires old(self).wf(),
        ensures final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            final(self).wf(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            out.is_ok() ==> refinement::step(old(self).state().control().paper(),final(self).state().control().paper(),id,Rule::Restart),
    {
        let ghost prior=*self;let out=self.host.leave(id);
        proof {self.generations(&prior);reveal(Kernel::generation_of);reveal(Kernel::registered);reveal(Kernel::paper);reveal(Kernel::phase_of);reveal(LifecycleState::same);reveal(Kernel::unchanged);
            if out.is_ok() {assert(prior.linked(id));self.generation_step(&prior,id,Rule::Restart);} else {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}
        }
        if out.is_ok() {self.transition(Ghost(prior),Ghost(id),Ghost(Rule::Restart));}
        out
    }

    pub fn withdraw_managed_execution<C,G,I>(&mut self,id:usize,execution:&mut Execution<V,C,G,I>,retiring:bool)->(out:Result<(),Error>)
        requires old(self).wf(),old(execution).wf(),
        ensures final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            out.is_ok() ==> old(self).owns_execution(id,old(execution)),
            final(self).wf(),final(execution).wf(),final(execution).execution_journal()==old(execution).execution_journal(),final(execution).value_attempts()==old(execution).value_attempts(),final(execution).capture()==old(execution).capture(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(execution).value_state()==old(execution).value_state(),final(execution).cleanup_state()==old(execution).cleanup_state(),
            out.is_ok() ==> !final(execution).work_state().accepts(),out.is_err() ==> *final(execution)==*old(execution),
            final(execution).status_links()==old(execution).status_links(),
    {
        if !self.matches_execution(id,execution) {return Err(Error::InvalidState);}
        let ghost prior=*self;let out=self.host.withdraw_managed_execution(id,execution,retiring);
        proof {self.generations(&prior);reveal(Kernel::generation_of);reveal(Kernel::registered);reveal(Kernel::paper);reveal(Kernel::phase_of);reveal(LifecycleState::same);reveal(Kernel::unchanged);
            if out.is_ok() {assert(prior.linked(id));self.generation_step(&prior,id,if retiring {Rule::Retire} else {Rule::Restart});} else {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}
        }
        if out.is_ok() {self.transition(Ghost(prior),Ghost(id),Ghost(if retiring {Rule::Retire} else {Rule::Restart}));}
        out
    }

    pub fn settle_managed_execution<C,G,I>(&mut self,id:usize,execution:&Execution<V,C,G,I>)->(out:Result<(),Error>)
        requires old(self).wf(),execution.wf(),
        ensures final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            out.is_ok() ==> old(self).owns_execution(id,execution),
            final(self).wf(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).state().control().unchanged(&old(self).state().control()),
    {
        if !self.matches_execution(id,execution) {return Err(Error::InvalidState);}
        let ghost prior=*self;let out=self.host.settle_managed_execution(id,execution);
        proof {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}out
    }

    pub fn fail_managed_execution<C,G,I>(&mut self,id:usize,execution:&Execution<V,C,G,I>)->(out:Result<(),Error>)
        requires old(self).wf(),execution.wf(),
        ensures final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            out.is_ok() ==> old(self).owns_execution(id,execution),
            final(self).wf(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).state().control().unchanged(&old(self).state().control()),
    {
        if !self.matches_execution(id,execution) {return Err(Error::InvalidState);}
        let ghost prior=*self;let out=self.host.fail_managed_execution(id,execution);
        proof {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}out
    }

    pub fn retry_managed_execution<C,G,I>(&mut self,id:usize,execution:&mut Execution<V,C,G,I>)->(out:Result<ActionTicket,Error>)
        requires old(self).wf(),old(execution).wf(),
        ensures out.is_ok() ==> out->Ok_0.id==id && out->Ok_0.generation==old(execution).origin().unwrap().generation
                && out->Ok_0.action==old(self).state().protocol().next_id()
                && !final(execution).cleanup_state().any_failed()
                && final(self).state().protocol().cleanup_reply_enabled(out->Ok_0),
            final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            out.is_ok() ==> old(self).owns_execution(id,old(execution)),
            final(self).wf(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).state().control().unchanged(&old(self).state().control()),
            final(execution).wf(),final(execution).execution_journal()==old(execution).execution_journal(),final(execution).value_attempts()==old(execution).value_attempts(),final(execution).value_state()==old(execution).value_state(),
            final(execution).capture()==old(execution).capture(),final(execution).phase_spec()==old(execution).phase_spec(),
            out.is_err() ==> *final(execution)==*old(execution) && final(self).state().same(&old(self).state()),
            final(execution).status_links()==old(execution).status_links(),
    {
        proof {self.state().same_reflexive();}
        if !self.matches_execution(id,execution) {return Err(Error::InvalidState);}
        let ghost prior=*self;let out=self.host.retry_managed_execution(id,execution);
        proof {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}out
    }

    pub fn begin_cleanup(&mut self,id:usize)->(out:Result<ActionTicket,Error>)
        requires old(self).wf(),
        ensures final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            final(self).wf(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).state().control().paper()==old(self).state().control().paper(),
    {
        let ghost prior=*self;let out=self.host.begin_cleanup(id);
        proof {self.unchanged(&prior);}out
    }

    pub fn compact_bindings(&mut self)->(out:usize)
        requires old(self).wf(),
        ensures final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            final(self).wf(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).state().control().paper()==old(self).state().control().paper(),
    {
        let ghost prior=*self;let out=self.host.compact_bindings();
        proof {self.unchanged(&prior);}out
    }

    pub fn compact_declarations(&mut self)->(out:usize)
        requires old(self).wf(),
        ensures final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            final(self).wf(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            final(self).state().control().paper()==old(self).state().control().paper(),
    {
        let ghost prior=*self;let out=self.host.compact_declarations();
        proof {self.unchanged(&prior);}out
    }

    #[allow(clippy::type_complexity)]
    pub fn register_shared_child(&mut self,child:&SharedChild,realms:&BTreeMap<u64,u64>,anchor:Port,definition:PluginDefinition<R>,host:H)
        ->(out:ChildTransition<Result<usize,(Error,PluginDefinition<R>,H)>>)
        requires old(self).wf(),child.wf(),
        ensures out.result.is_ok() ==> final(self).recipe_history()==old(self).recipe_history().append(recipes::entries(final(self).registry().entries()),joint::recipes::Event::Insert {id:out.result->Ok_0}),
            !(out.result.is_ok()) ==> final(self).recipe_history()==old(self).recipe_history(),
            final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            final(self).wf(),out.wf(child),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            out.result.is_err() ==> out.result->Err_0.1==definition && out.result->Err_0.2==host,
            out.result.is_ok() ==> final(self).registry().entries()[out.result->Ok_0].recipe().payload()==definition.payload()
                && final(self).registry().entries()[out.result->Ok_0].recipe().realms()==realms@
                && final(self).registry().entries()[out.result->Ok_0].recipe().anchor_port()==anchor
                && final(self).registry().entries()[out.result->Ok_0].bookkeeping()==host,
    {
        let ghost prior=*self;let out=self.host.register_shared_child(child,realms,anchor,definition,host);
        proof {self.generations(&prior);reveal(Kernel::generation_of);reveal(Kernel::registered);reveal(Kernel::paper);reveal(Kernel::phase_of);reveal(LifecycleState::same);reveal(Kernel::unchanged);
            if out.result.is_ok() {let id=out.result->Ok_0;assert(prior.linked(id));assert(!prior.publications().entries().contains_key(id));assert(prior.linked(id));self.generation_step(&prior,id,Rule::Insert);}
            else {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}
        }
        if out.result.is_ok() {self.transition(Ghost(prior),Ghost(out.result->Ok_0),Ghost(Rule::Insert));proof {assert(recipes::entries(self.registry().entries()) =~= prior.recipes.current().insert(out.result->Ok_0,self.registry().entries()[out.result->Ok_0].recipe()));}self.record_recipes(Ghost(joint::recipes::Event::Insert {id:out.result->Ok_0}));}
        out
    }
    pub fn retire_shared_child(&mut self,child:&SharedChild)->(out:ChildTransition<Result<Option<ChildIdentity>,Error>>)
        requires old(self).wf(),child.wf(),
        ensures final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            final(self).wf(),out.wf(child),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
    {
        let ghost prior=*self;let out=self.host.retire_shared_child(child);
        proof {self.generations(&prior);reveal(Kernel::generation_of);reveal(Kernel::registered);reveal(Kernel::paper);reveal(Kernel::phase_of);reveal(LifecycleState::same);reveal(Kernel::unchanged);
            if out.result.is_ok() && out.result->Ok_0.is_some() && prior.state().control().registered(out.result->Ok_0.unwrap().child()) {
                let id=out.result->Ok_0.unwrap().child();assert(prior.linked(id));self.generation_step(&prior,id,Rule::Retire);
            } else {self.state().control().unchanged_observations(&prior.state().control());self.unchanged(&prior);}
        }
        if let Ok(Some(identity))=&out.result {
            let id=identity.id();
            if self.host.kernel().contains(id) {
                self.transition(Ghost(prior),Ghost(id),Ghost(Rule::Retire));
            }
        }
        out
    }

}
impl<R,H,V,F> NativeRuntime<Body<R,F>,H,V> {
    pub fn call_opaque<A,O>(&mut self,id:usize,invocation:RegisteredInvocation<A>)->(out:Result<WorkReceipt<O>,RegisteredInvocation<A>>)
        where R:FnMut(A)->O,
        requires old(self).wf(),old(self).registry().entries().contains_key(id) ==>
            old(self).registry().entries()[id].recipe().payload().callback_requires::<A,O>(invocation.work().value()),
        ensures out.is_ok() ==> final(self).recipe_history()==old(self).recipe_history().append(recipes::entries(final(self).registry().entries()),joint::recipes::Event::Call {id,version:invocation.version(),origin:invocation.lifecycle(),work:invocation.work().origin()}),
            out.is_err() ==> final(self).recipe_history()==old(self).recipe_history(),
            final(self).journal_spec()==old(self).journal_spec(),final(self).joint_key()==old(self).joint_key(),
            final(self).wf(),final(self).state()==old(self).state(),final(self).publications()==old(self).publications(),final(self).episode_owners()==old(self).episode_owners(),
            out.is_err() ==> out->Err_0==invocation,
            out.is_ok() ==> old(self).episode_owners().contains_key(id)
                && old(self).episode_owners()[id].admits(&invocation)
                && old(self).state().root_invocation_enabled(invocation.lifecycle())
                && out->Ok_0.origin()==invocation.work().origin()
                && old(self).registry().entries()[id].recipe().payload().callback_ensures::<A,O>(invocation.work().value(),out->Ok_0.value()),
    {
        match self.owners.get(&id) {Some(owner)=>{if !owner.matches_invocation(&invocation) {return Err(invocation);}},None=>return Err(invocation)}
        let ghost prior=*self;let ghost admitted=invocation;let out=self.host.call_opaque(id,invocation);
        proof {reveal(Kernel::generations_preserved);self.unchanged(&prior);}
        if out.is_ok() {
            proof {reveal(Kernel::paper);reveal(Kernel::phase_of);reveal(Kernel::is_retired);
                assert(recipes::entries(self.registry().entries()) =~= prior.recipes.current().insert(id,self.registry().entries()[id].recipe()));}
            self.record_recipes(Ghost(joint::recipes::Event::Call {id,version:admitted.version(),origin:admitted.lifecycle(),work:admitted.work().origin()}));
        }
        out
    }
}

}

#[path = "native_payload_runtime.rs"]
pub mod payloads;
