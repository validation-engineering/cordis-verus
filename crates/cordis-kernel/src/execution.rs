//! Production episode ownership: work, cleanup queues, values and phase.
//! No mutable constituent escapes to the ordinary host. Native publication and
//! release change the phase in the same checked operation as the lifecycle.
use crate::action_ledger::ActionTicket;
use crate::async_completion::Completion;
use crate::cleanup_groups::CleanupGroups;
use crate::cleanup_journal::{RestoreError, RestoreTicket};
use crate::cleanup_queue::completion::{CleanupPolicy, CleanupReport};
use crate::cleanup_queue::landing::StageReport;
use crate::cleanup_queue::CleanupQueue;
use crate::effect_work::{EffectReply, EffectRequest, EffectRun};
use crate::lifecycle_state::registration::shared_child::{
    ChildCleanup, ChildDispatch, SharedChild,
};
use crate::lifecycle_state::services::{NativeEpisode, NativeReadError, NativeValueError};
use crate::setup_work::{RootStatus, SetupWork, WorkItem, WorkReceipt, WorkTicket};
#[cfg(verus_keep_ghost)]
use crate::{cleanup_journal::RestoreOutcome, setup_work::WorkKind};
use crate::{Binding, Port};
use std::collections::BTreeMap;
use std::sync::Arc;
use vstd::prelude::*;

verus! {
#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum ExecutionPhase { Loading, Active, Restoring, Closed }

pub struct Execution<V,C,G,I> {
    pub(crate) work:SetupWork<C,EffectRequest<G>>,
    pub(crate) effects:BTreeMap<usize,EffectRun<G>>,
    pub(crate) checked_out:BTreeMap<usize,()>,
    pub(crate) statuses:BTreeMap<usize,crate::host_status::Link>,
    pub(crate) groups:CleanupGroups<I>,
    pub(crate) values:Option<NativeEpisode<V>>,
    pub(crate) initialized:bool,
    #[allow(dead_code)] // The owner-local receipt history is erased.
    pub(crate) attempts:Tracked<crate::reversible_value::attempt::Ledger>,
}
impl<V,C,G,I> Execution<V,C,G,I> {
    pub closed spec fn work_state(&self)->SetupWork<C,EffectRequest<G>> {self.work}
    pub closed spec fn cleanup_state(&self)->CleanupGroups<I> {self.groups}
    pub closed spec fn value_state(&self)->Option<NativeEpisode<V>> {self.values}
    pub closed spec fn effect_state(&self)->Map<usize,EffectRun<G>> {self.effects@}
    pub closed spec fn checked_out(&self)->Map<usize,()> {self.checked_out@}
    pub closed spec fn status_links(&self)->Map<usize,crate::host_status::Link> {self.statuses@}
    pub closed spec fn initialized(&self)->bool {self.initialized}
    pub closed spec fn value_attempts(&self)->crate::reversible_value::attempt::Ledger {self.attempts@}
    /// All runtime constituents are framed even when an erased rejection
    /// receipt is added. Interior shared values are described by that receipt.
    pub open spec fn same_runtime(&self,prior:&Self)->bool {
        self.work_state()==prior.work_state() && self.cleanup_state()==prior.cleanup_state()
            && self.value_state()==prior.value_state() && self.effect_state()==prior.effect_state()
            && self.checked_out()==prior.checked_out() && self.status_links()==prior.status_links() && self.initialized()==prior.initialized()
    }
    // Crate-private representation lemma: this exports equalities, no mutable
    // reference and no new assumption. Field visibility is unchanged.
    pub(crate) proof fn representation(&self)
        ensures self.work_state()==self.work,self.cleanup_state()==self.groups,
            self.value_state()==self.values,self.initialized()==self.initialized,self.effect_state()==self.effects@,self.checked_out()==self.checked_out@,self.status_links()==self.statuses@,self.value_attempts()==self.attempts@,
    {}
    pub open spec fn execution_journal(&self)->Option<crate::reversible_value::joint::Journal> {
        self.cleanup_state().execution_journal()
    }
    /// Create actual typed storage in this Episode's authoritative execution
    /// domain. Standalone/static executions allocate their own explicit domain.
    pub fn new_payload<T:?Sized>(&self,value:Arc<T>)->(out:crate::reversible_value::payload::SharedPayload<T>)
        ensures out.initial()==value,self.execution_journal().is_some() ==> out.journal_spec()==self.execution_journal().unwrap(),
    {
        match self.groups.execution_domain() {
            Some(journal)=>crate::reversible_value::payload::SharedPayload::new_in(journal,value),
            None=>crate::reversible_value::payload::SharedPayload::new(value),
        }
    }
    /// Actual work and live cleanup membership in one shared record map.
    pub open spec fn observed_state(&self,state:Map<nat,crate::reversible_value::joint::Record>)->bool {
        let work=self.work_state();
        work.link().is_some() && state.contains_key(work.link().unwrap().1)
            && state[work.link().unwrap().1]==(crate::reversible_value::joint::Record::Work {state:work.observation()})
            && self.cleanup_state().observed(state)
    }
    /// One read epoch observes the actual work owner, every live cleanup queue
    /// and their exact membership alongside the domain's values and native
    /// publication history. Opaque host flags and payload meaning stay outside.
    pub open spec fn observed(&self,snapshot:&crate::reversible_value::joint::Snapshot)->bool {
        snapshot.certified() && self.execution_journal()==Some(snapshot.journal_spec()) && self.observed_state(snapshot.last())
    }
    pub(crate) fn certify(&self,view:&crate::reversible_value::joint::ReadView)
        requires self.wf(),view.wf(),self.execution_journal()==Some(view.journal_spec()),
        ensures self.observed_state(view.state()),
    {self.work.certify(view);self.groups.certify(view);}
    pub fn observe_execution(&self)->(out:Option<crate::reversible_value::joint::Snapshot>)
        requires self.wf(),
        ensures out.is_some()==self.execution_journal().is_some(),out.is_some() ==> self.observed(&out.unwrap()),
    {
        let journal=self.groups.execution_domain()?;
        let view=journal.read();self.work.certify(&view);self.groups.certify(&view);
        Some(view.finish())
    }
    pub fn observe_execution_after(&self,earlier:&crate::reversible_value::joint::Snapshot)
        ->(out:crate::reversible_value::joint::Snapshot)
        requires self.wf(),earlier.certified(),self.execution_journal()==Some(earlier.journal_spec()),
        ensures self.observed(&out),out.extends(earlier),
    {
        let journal=self.groups.execution_domain().unwrap();
        let view=journal.read();view.certify_history(earlier);
        self.work.certify(&view);self.groups.certify(&view);view.finish()
    }
    /// Actual queue domains and the common point resources distinguish work
    /// from cleanup and distinguish every pair of live cleanup groups.
    pub proof fn observation_ownership(&self,snapshot:&crate::reversible_value::joint::Snapshot)
        requires self.wf(),self.observed(snapshot),
        ensures self.cleanup_state().link().is_some(),
            self.cleanup_state().link().unwrap().1!=self.work_state().link().unwrap().1,
            forall|id:usize| #[trigger] self.cleanup_state().queues().contains_key(id) ==>
                self.cleanup_state().queues()[id].link().unwrap().1!=self.cleanup_state().link().unwrap().1,
            forall|id:usize| #[trigger] self.cleanup_state().queues().contains_key(id) ==>
                self.cleanup_state().queues()[id].link().unwrap().1!=self.work_state().link().unwrap().1,
            forall|a:usize,b:usize| #[trigger] self.cleanup_state().queues().contains_key(a)
                && #[trigger] self.cleanup_state().queues().contains_key(b) && a!=b ==>
                self.cleanup_state().queues()[a].link().unwrap().1!=self.cleanup_state().queues()[b].link().unwrap().1,
    {
        assert forall|a:usize,b:usize| #[trigger] self.cleanup_state().queues().contains_key(a)
            && #[trigger] self.cleanup_state().queues().contains_key(b) && a!=b implies
            self.cleanup_state().queues()[a].link().unwrap().1!=self.cleanup_state().queues()[b].link().unwrap().1 by {
            let qa=self.cleanup_state().queues()[a];let qb=self.cleanup_state().queues()[b];
            assert(self.cleanup_state().domain_ids()[a]!=self.cleanup_state().domain_ids()[b]);
            assert(snapshot.last()[qa.link().unwrap().1]==(crate::reversible_value::joint::Record::Cleanup {state:qa.observation()}));
            assert(snapshot.last()[qb.link().unwrap().1]==(crate::reversible_value::joint::Record::Cleanup {state:qb.observation()}));
        }
    }
    pub(crate) fn attach_execution(&mut self,journal:&crate::reversible_value::joint::Journal)
        requires old(self).wf(),old(self).work_state().link().is_none(),old(self).execution_journal().is_none(),
            old(self).cleanup_state().queues().dom()==set![0usize],
        ensures final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).execution_journal()==Some(*journal),
            final(self).work_state().same_local(&old(self).work_state()),
            final(self).origin()==old(self).origin(),final(self).capture()==old(self).capture(),
            final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(),
            final(self).cleanup_state().origin()==old(self).cleanup_state().origin(),
            final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids(),
            final(self).cleanup_state().queues().dom()==old(self).cleanup_state().queues().dom(),
            final(self).status_links()==old(self).status_links(),
    {
        self.work.attach_execution(journal);self.groups.attach_execution(journal);
    }
    pub open spec fn origin(&self)->Option<ActionTicket> {self.work_state().origin()}
    pub open spec fn effects_wf(effects:Map<usize,EffectRun<G>>,origin:Option<ActionTicket>,domains:Map<usize,u64>,live:Set<usize>)->bool {
        forall|id:usize| #[trigger] effects.contains_key(id) ==> id!=0 && effects[id].wf()
            && effects[id].identity().group_id()==id && effects[id].identity().origin()==origin
            && live.contains(id) && domains.contains_key(id) && effects[id].identity().domain_id()==domains[id]
    }
    pub open spec fn checked_out_wf(checked:Map<usize,()>,live:Set<usize>,stored:Set<usize>)->bool {
        forall|id:usize| #[trigger] checked.contains_key(id) ==> id!=0 && live.contains(id) && !stored.contains(id)
    }
    pub open spec fn wf(&self)->bool {
        &&& self.work_state().wf() && self.cleanup_state().wf() && self.value_attempts().wf()
        &&& self.work_state().link().is_some()==self.execution_journal().is_some()
        &&& self.work_state().link().is_some() ==> self.work_state().link().unwrap().0==self.execution_journal().unwrap()
        &&& Self::effects_wf(self.effect_state(),self.cleanup_state().origin(),self.cleanup_state().domain_ids(),self.cleanup_state().queues().dom())
        &&& Self::checked_out_wf(self.checked_out(),self.cleanup_state().queues().dom(),self.effect_state().dom())
        &&& forall|id:usize| #[trigger] self.status_links().contains_key(id) ==> id!=0 && self.cleanup_state().live(id)
            && self.status_links()[id].bound(self)
            && self.status_links()[id].kind()==(crate::reversible_value::joint::host::Kind::Effect {group:id,domain:self.cleanup_state().domain_ids()[id]})
        &&& self.origin()==self.cleanup_state().origin()
        &&& self.work_state().is_closed()==self.cleanup_state().closed()
        &&& (!self.work_state().is_closed() ==> self.work_state().owns(&self.cleanup_state()))
        &&& self.value_state().is_some()==self.origin().is_some()
        &&& self.value_state().is_some() ==> self.value_state().unwrap().wf()
            && Some(self.value_state().unwrap().origin())==self.origin()
            && self.value_state().unwrap().capture().work_domain==self.work_state().domain_id()
            && self.value_state().unwrap().closed()==self.work_state().is_closed()
    }
    /// Fixed provenance of a native execution, separate from its changing
    /// local work and cleanup state. Static/external executions have no native
    /// Begin capture.
    pub open spec fn capture(&self)->Option<crate::lifecycle_state::services::capture::Capture<V>> {
        match self.value_state() {Some(values)=>Some(values.capture()),None=>None}
    }
    pub proof fn capture_correspondence(&self)
        requires self.wf(),self.capture().is_some(),
        ensures self.value_state().is_some(),self.capture().unwrap().wf(),
            self.origin()==Some(self.capture().unwrap().origin),
            self.capture().unwrap().work_domain==self.work_state().domain_id(),
            !self.work_state().is_closed() ==> self.value_state().unwrap().imports()==self.capture().unwrap().imports,
            self.work_state().is_closed() ==> self.value_state().unwrap().imports().is_empty(),
    {self.value_state().unwrap().capture_correspondence();}
    pub open spec fn phase_spec(&self)->ExecutionPhase {
        if self.work_state().is_closed() {ExecutionPhase::Closed}
        else if !self.work_state().accepts() {ExecutionPhase::Restoring}
        else if self.initialized() {ExecutionPhase::Active} else {ExecutionPhase::Loading}
    }
    pub fn phase(&self)->(out:ExecutionPhase) ensures out==self.phase_spec(), {
        if self.work.closed_now() {ExecutionPhase::Closed}
        else if !self.work.accepting_now() {ExecutionPhase::Restoring}
        else if self.initialized {ExecutionPhase::Active} else {ExecutionPhase::Loading}
    }
    pub fn new(domain:u64)->(out:Self)
        ensures out.wf(),out.origin().is_none(),out.phase_spec()==ExecutionPhase::Loading,out.value_attempts().events().len()==0,
    {Self {work:SetupWork::new(domain),groups:CleanupGroups::new(domain),values:None,initialized:false,effects:BTreeMap::new(),checked_out:BTreeMap::new(),statuses:BTreeMap::new(),attempts:Tracked(crate::reversible_value::attempt::Ledger::new())}}
    pub fn effects(&self)->(out:&BTreeMap<usize,EffectRun<G>>)
        ensures out@==self.effect_state(),
    {&self.effects}
    /// Check out the actual runner while retaining its identity in the owner.
    /// A dropped or abandoned checkout keeps removal and release blocked.
    pub fn take_effect(&mut self,id:usize)->(out:Option<EffectRun<G>>)
        requires old(self).wf(),ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),
            final(self).effect_state()==old(self).effect_state().remove(id),
            final(self).checked_out()==if out.is_some() {old(self).checked_out().insert(id,())} else {old(self).checked_out()},
            final(self).work_state()==old(self).work_state(),final(self).cleanup_state()==old(self).cleanup_state(),
            final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(),
            out.is_some()==old(self).effect_state().contains_key(id),
            out.is_some() ==> out.unwrap()==old(self).effect_state()[id] && out.unwrap().wf(),
            final(self).status_links()==old(self).status_links(),
    {let out=self.effects.remove(&id);if out.is_some() {self.checked_out.insert(id,());}out}
    pub fn put_effect(&mut self,run:EffectRun<G>)->(out:Result<(),EffectRun<G>>)
        requires old(self).wf(),run.wf(),ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),
            final(self).work_state()==old(self).work_state(),final(self).cleanup_state()==old(self).cleanup_state(),
            final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(),
            out.is_ok()==(old(self).checked_out().contains_key(run.identity().group_id()) && !old(self).effect_state().contains_key(run.identity().group_id())
                && run.identity().matches(&old(self).cleanup_state())),
            out.is_ok() ==> final(self).effect_state()==old(self).effect_state().insert(run.identity().group_id(),run)
                && final(self).checked_out()==old(self).checked_out().remove(run.identity().group_id()),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==run,
            final(self).status_links()==old(self).status_links(),
    {
        let id=run.id();
        if !self.checked_out.contains_key(&id) || self.effects.contains_key(&id) || !run.belongs(&self.groups) {return Err(run);}
        self.checked_out.remove(&id);self.effects.insert(id,run);Ok(())
    }
    /// Activation stores the actual request payload before its work receipt is
    /// completed. It cannot overwrite another live runner, even after reuse of
    /// a numeric group ID in another episode.
    pub fn activate_effect(&mut self,request:EffectRequest<G>)->(out:Result<(),EffectRequest<G>>)
        requires old(self).wf(),ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),
            final(self).work_state()==old(self).work_state(),final(self).cleanup_state()==old(self).cleanup_state(),
            final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==request,
            out.is_ok() ==> final(self).effect_state().contains_key(request.identity().group_id())
                && final(self).effect_state()[request.identity().group_id()].payload()==request.payload()
                && final(self).effect_state()[request.identity().group_id()].identity()==request.identity(),
            final(self).status_links()==old(self).status_links(),
    {
        if request.id()==0 || self.checked_out.contains_key(&request.id()) || self.effects.contains_key(&request.id()) {return Err(request);}
        let run=request.activate(&self.groups)?;
        self.effects.insert(run.id(),run);Ok(())
    }
    /// Consume the actual checked-out runner only after its queue is drained.
    /// Its real payload is returned for destruction outside the host mutex.
    pub fn retire_effect(&mut self,run:EffectRun<G>)->(out:Result<G,EffectRun<G>>)
        requires old(self).wf(),run.wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),
            final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(),
            final(self).effect_state()==old(self).effect_state(),
            final(self).cleanup_state().frame(&old(self).cleanup_state(),run.identity().group_id()),
            out.is_ok() ==> out->Ok_0==run.payload() && !final(self).cleanup_state().live(run.identity().group_id())
                && run.identity().group_id()<final(self).cleanup_state().next_id()
                && final(self).checked_out()==old(self).checked_out().remove(run.identity().group_id()),
            out.is_ok() && final(self).cleanup_state().link().is_some() ==> final(self).cleanup_state().membership_trace().last().event.change
                ==(crate::reversible_value::joint::Change::Groups {event:crate::reversible_value::joint::groups::Event::Remove {id:run.identity().group_id()}}),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==run,
            out.is_ok() ==> final(self).status_links()==old(self).status_links().remove(run.identity().group_id()),
    {
        let (payload,_observation)=self.retire_with_status(run)?;Ok(payload)
    }
    pub fn work(&self)->(out:&SetupWork<C,EffectRequest<G>>) ensures *out==self.work_state(), {&self.work}
    pub fn groups(&self)->(out:&CleanupGroups<I>) ensures *out==self.cleanup_state(), {&self.groups}
    pub fn native(&self)->(out:Option<&NativeEpisode<V>>)
        ensures out.is_some()==self.value_state().is_some(),out.is_some() ==> *out.unwrap()==self.value_state().unwrap(),
    {self.values.as_ref()}
    pub fn withdraw(&mut self)
        requires old(self).wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).origin()==old(self).origin(),
            final(self).cleanup_state()==old(self).cleanup_state(),final(self).value_state()==old(self).value_state(),
            final(self).phase_spec()==if old(self).phase_spec()==ExecutionPhase::Closed {ExecutionPhase::Closed} else {ExecutionPhase::Restoring},
            final(self).status_links()==old(self).status_links(),
    {self.work.withdraw();}
    /// External embeddings acknowledge their own lifecycle. A native episode
    /// can become Active only through NativeHost::finish_managed_execution.
    pub fn activate_external(&mut self)->(out:bool)
        requires old(self).wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),
            final(self).cleanup_state()==old(self).cleanup_state(),final(self).value_state()==old(self).value_state(),
            out==(!old(self).origin().is_some() && old(self).work_state().root_status()==RootStatus::Settled
                && !old(self).work_state().failed() && old(self).work_state().accepts() && !old(self).work_state().is_closed()),
            out ==> final(self).phase_spec()==ExecutionPhase::Active,!out ==> *final(self)==*old(self),
            final(self).status_links()==old(self).status_links(),
    {
        if self.work.lifecycle_ticket().is_some() || self.work.root()!=RootStatus::Settled
            || self.work.root_failed_now() || !self.work.accepting_now() || self.work.closed_now() {return false;}
        self.initialized=true;true
    }
    /// Static release uses the same all-work/all-queues drain check. Native
    /// release must also release its value owner and real lifecycle atomically.
    pub fn seal_external(&mut self)->(out:bool)
        requires old(self).wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).origin()==old(self).origin(),
            out ==> final(self).phase_spec()==ExecutionPhase::Closed && old(self).work_state().idle()
                && old(self).cleanup_state().all_drained(),!out ==> *final(self)==*old(self),
            final(self).status_links()==old(self).status_links(),
    {if self.values.is_some() || !self.effects.is_empty() || !self.checked_out.is_empty() || !self.statuses.is_empty() {return false;} self.work.seal(&mut self.groups)}
    pub fn provide(&mut self,port:Port,value:Arc<V>)->(out:Result<(),(NativeValueError,Arc<V>)>)
        requires old(self).wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),final(self).cleanup_state()==old(self).cleanup_state(),
            final(self).phase_spec()==old(self).phase_spec(),
            out.is_err() ==> out->Err_0.1==value && final(self).value_state()==old(self).value_state(),
            out.is_ok() ==> old(self).value_state().is_some()
                && final(self).value_state().unwrap().owned_table()==crate::coeffects::put(old(self).value_state().unwrap().owned_table(),port,Some(value)),
            final(self).status_links()==old(self).status_links(),
    {match self.values.as_mut() {Some(values)=>values.provide(port,value),None=>Err((NativeValueError::Undeclared,value))}}
    pub fn read(&self,port:Port)->(out:Result<(usize,&Arc<V>),NativeReadError>)
        requires self.wf(),
        ensures out.is_ok() ==> self.value_state().is_some() && !self.value_state().unwrap().closed(),
    {match self.values.as_ref() {Some(values)=>values.read(port),None=>Err(NativeReadError {reason:NativeValueError::Undeclared,provider:None})}}
    pub fn issue_root<A>(&mut self,argument:A)->(out:Result<WorkItem<A>,A>)
        requires old(self).wf(), old(self).work_state().wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).cleanup_state()==old(self).cleanup_state(),final(self).value_state()==old(self).value_state(),final(self).initialized()==old(self).initialized(), final(self).work_state().domain_id()==old(self).work_state().domain_id(), final(self).work_state().accepts()==old(self).work_state().accepts(), final(self).work_state().is_closed()==old(self).work_state().is_closed(), final(self).work_state().wf(),final(self).work_state().origin()==old(self).work_state().origin(),final(self).work_state().queued_unchanged(&old(self).work_state()),
            out.is_ok()==(old(self).work_state().root_status()==RootStatus::Unissued && !old(self).work_state().is_closed()),
            out.is_ok() ==> out->Ok_0.value()==argument && out->Ok_0.origin().domain()==old(self).work_state().domain_id() && out->Ok_0.origin().id()==0 && out->Ok_0.origin().kind()==WorkKind::Root
                && final(self).work_state().root_status()==RootStatus::Queued,
            out.is_err() ==> out->Err_0==argument && final(self).work_state()==old(self).work_state(),
            final(self).status_links()==old(self).status_links(),
    {self.work.issue_root(argument)}
    pub fn start_root(&mut self,ticket:WorkTicket)->(out:bool)
        requires old(self).wf(), old(self).work_state().wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).cleanup_state()==old(self).cleanup_state(),final(self).value_state()==old(self).value_state(),final(self).initialized()==old(self).initialized(), final(self).work_state().domain_id()==old(self).work_state().domain_id(), final(self).work_state().accepts()==old(self).work_state().accepts(), final(self).work_state().is_closed()==old(self).work_state().is_closed(), final(self).work_state().wf(),final(self).work_state().origin()==old(self).work_state().origin(),final(self).work_state().queued_unchanged(&old(self).work_state()),
            out==(ticket.domain()==old(self).work_state().domain_id() && ticket.id()==0 && ticket.kind()==WorkKind::Root
                && (old(self).work_state().root_status()==RootStatus::Queued || old(self).work_state().root_status()==RootStatus::Running)),
            out ==> final(self).work_state().root_status()==RootStatus::Running,
            !out ==> final(self).work_state()==old(self).work_state(),
            final(self).status_links()==old(self).status_links(),
    {self.work.start_root(ticket)}
    pub fn cancel_queued_root(&mut self,ticket:WorkTicket)->(out:bool)
        requires old(self).wf(), old(self).work_state().wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).cleanup_state()==old(self).cleanup_state(),final(self).value_state()==old(self).value_state(),final(self).initialized()==old(self).initialized(), final(self).work_state().domain_id()==old(self).work_state().domain_id(), final(self).work_state().accepts()==old(self).work_state().accepts(), final(self).work_state().is_closed()==old(self).work_state().is_closed(), final(self).work_state().wf(),final(self).work_state().origin()==old(self).work_state().origin(),final(self).work_state().queued_unchanged(&old(self).work_state()),
            out==(ticket.domain()==old(self).work_state().domain_id() && ticket.id()==0 && ticket.kind()==WorkKind::Root
                && old(self).work_state().root_status()==RootStatus::Queued && !old(self).work_state().accepts()),
            out ==> final(self).work_state().root_status()==RootStatus::Settled && final(self).work_state().failed(),
            !out ==> final(self).work_state()==old(self).work_state(),
            final(self).status_links()==old(self).status_links(),
    {self.work.cancel_queued_root(ticket)}
    pub fn complete_root<E>(&mut self,receipt:WorkReceipt<Result<(),E>>)->(out:Result<Result<(),E>,WorkReceipt<Result<(),E>>>)
        requires old(self).wf(), old(self).work_state().wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).cleanup_state()==old(self).cleanup_state(),final(self).value_state()==old(self).value_state(),final(self).initialized()==old(self).initialized(), final(self).work_state().domain_id()==old(self).work_state().domain_id(), final(self).work_state().accepts()==old(self).work_state().accepts(), final(self).work_state().is_closed()==old(self).work_state().is_closed(), final(self).work_state().wf(),final(self).work_state().origin()==old(self).work_state().origin(),final(self).work_state().queued_unchanged(&old(self).work_state()),
            out.is_ok()==(receipt.origin().domain()==old(self).work_state().domain_id() && receipt.origin().id()==0 && receipt.origin().kind()==WorkKind::Root
                && (old(self).work_state().root_status()==RootStatus::Queued || old(self).work_state().root_status()==RootStatus::Running)),
            out.is_ok() ==> out->Ok_0==receipt.value() && final(self).work_state().root_status()==RootStatus::Settled
                && final(self).work_state().failed()==receipt.value().is_err(),
            out.is_err() ==> out->Err_0==receipt && final(self).work_state()==old(self).work_state(),
            final(self).status_links()==old(self).status_links(),
    {self.work.complete_root(receipt)}
    pub fn fail_root<E>(&mut self,ticket:WorkTicket,error:E)->(out:Result<E,E>)
        requires old(self).wf(), old(self).work_state().wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).cleanup_state()==old(self).cleanup_state(),final(self).value_state()==old(self).value_state(),final(self).initialized()==old(self).initialized(), final(self).work_state().domain_id()==old(self).work_state().domain_id(), final(self).work_state().accepts()==old(self).work_state().accepts(), final(self).work_state().is_closed()==old(self).work_state().is_closed(), final(self).work_state().wf(),final(self).work_state().origin()==old(self).work_state().origin(),final(self).work_state().queued_unchanged(&old(self).work_state()),
            out.is_ok() ==> final(self).work_state().root_status()==RootStatus::Settled && final(self).work_state().failed() && out->Ok_0==error,
            out.is_err() ==> out->Err_0==error && final(self).work_state()==old(self).work_state(),
            final(self).status_links()==old(self).status_links(),
    {self.work.fail_root(ticket,error)}
    pub fn abandon_root(&mut self)
        requires old(self).wf(), old(self).work_state().wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).cleanup_state()==old(self).cleanup_state(),final(self).value_state()==old(self).value_state(),final(self).initialized()==old(self).initialized(), final(self).work_state().domain_id()==old(self).work_state().domain_id(), !final(self).work_state().accepts(), final(self).work_state().is_closed()==old(self).work_state().is_closed(), final(self).work_state().wf(),final(self).work_state().origin()==old(self).work_state().origin(),final(self).work_state().queued_unchanged(&old(self).work_state()),
            old(self).work_state().root_status()!=RootStatus::Settled ==> final(self).work_state().root_status()==RootStatus::Abandoned && !final(self).work_state().idle(),
            final(self).status_links()==old(self).status_links(),
    {self.work.abandon_root()}
    pub fn take_child(&mut self)->(out:Option<WorkItem<C>>)
        requires old(self).wf(), old(self).work_state().wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).cleanup_state()==old(self).cleanup_state(),final(self).value_state()==old(self).value_state(),final(self).initialized()==old(self).initialized(), final(self).work_state().domain_id()==old(self).work_state().domain_id(), final(self).work_state().accepts()==old(self).work_state().accepts(), final(self).work_state().is_closed()==old(self).work_state().is_closed(), final(self).work_state().wf(),final(self).work_state().origin()==old(self).work_state().origin(),out.is_some() ==> out.unwrap()==old(self).work_state().child_requests().first()
            && !old(self).work_state().outstanding().contains_key(out.unwrap().origin().id())
            && final(self).work_state().outstanding()==old(self).work_state().outstanding().insert(out.unwrap().origin().id(),WorkKind::Child)
            && final(self).work_state().child_requests()==old(self).work_state().child_requests().skip(1),
            out.is_none() ==> final(self).work_state()==old(self).work_state(),
            final(self).work_state().root_status()==old(self).work_state().root_status(),final(self).work_state().group_requests()==old(self).work_state().group_requests(),
            final(self).work_state().domain_id()==old(self).work_state().domain_id(),
            final(self).status_links()==old(self).status_links(),
    {self.work.take_child()}
    pub fn take_group(&mut self)->(out:Option<WorkItem<EffectRequest<G>>>)
        requires old(self).wf(), old(self).work_state().wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).cleanup_state()==old(self).cleanup_state(),final(self).value_state()==old(self).value_state(),final(self).initialized()==old(self).initialized(), final(self).work_state().domain_id()==old(self).work_state().domain_id(), final(self).work_state().accepts()==old(self).work_state().accepts(), final(self).work_state().is_closed()==old(self).work_state().is_closed(), final(self).work_state().wf(),final(self).work_state().origin()==old(self).work_state().origin(),out.is_some() ==> out.unwrap()==old(self).work_state().group_requests().first()
            && !old(self).work_state().outstanding().contains_key(out.unwrap().origin().id())
            && final(self).work_state().outstanding()==old(self).work_state().outstanding().insert(out.unwrap().origin().id(),WorkKind::Group)
            && final(self).work_state().group_requests()==old(self).work_state().group_requests().skip(1),
            out.is_none() ==> final(self).work_state()==old(self).work_state(),
            final(self).work_state().root_status()==old(self).work_state().root_status(),final(self).work_state().child_requests()==old(self).work_state().child_requests(),
            final(self).work_state().domain_id()==old(self).work_state().domain_id(),
            final(self).status_links()==old(self).status_links(),
    {self.work.take_group()}
    pub fn complete_request<R>(&mut self,receipt:WorkReceipt<R>)->(out:Result<R,WorkReceipt<R>>)
        requires old(self).wf(), old(self).work_state().wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).cleanup_state()==old(self).cleanup_state(),final(self).value_state()==old(self).value_state(),final(self).initialized()==old(self).initialized(), final(self).work_state().domain_id()==old(self).work_state().domain_id(), final(self).work_state().accepts()==old(self).work_state().accepts(), final(self).work_state().is_closed()==old(self).work_state().is_closed(), final(self).work_state().wf(),final(self).work_state().origin()==old(self).work_state().origin(),out.is_ok()==(receipt.origin().domain()==old(self).work_state().domain_id()
            && old(self).work_state().outstanding().contains_key(receipt.origin().id())
            && old(self).work_state().outstanding()[receipt.origin().id()]==receipt.origin().kind()),
            out.is_ok() ==> out->Ok_0==receipt.value()
                && final(self).work_state().outstanding()==old(self).work_state().outstanding().remove(receipt.origin().id()),
            out.is_err() ==> out->Err_0==receipt && final(self).work_state()==old(self).work_state(),
            final(self).work_state().child_requests()==old(self).work_state().child_requests(),final(self).work_state().group_requests()==old(self).work_state().group_requests(),
            final(self).work_state().root_status()==old(self).work_state().root_status(),final(self).work_state().domain_id()==old(self).work_state().domain_id(),
            final(self).status_links()==old(self).status_links(),
    {self.work.complete_request(receipt)}
    pub fn lifecycle_ticket(&self)->(out:Option<ActionTicket>) ensures out==self.origin(), {self.work.lifecycle_ticket()}
    pub fn child_count(&self)->(out:usize) ensures out==self.work_state().child_requests().len(), {self.work.child_count()}
    pub fn group_count(&self)->(out:usize) ensures out==self.work_state().group_requests().len(), {self.work.group_count()}
    pub fn is_idle(&self)->(out:bool) ensures out==self.work_state().idle(), {self.work.is_idle()}
    pub fn can_finish(&self,target:&[Binding])->(out:bool)
        requires self.wf(),ensures out ==> self.work_state().idle() && !self.work_state().failed()
            && !self.cleanup_state().any_pending() && !self.cleanup_state().any_failed(),
    {self.checked_out.is_empty() && self.work.can_finish(&self.groups,target)}
    #[allow(clippy::type_complexity)]
    pub fn register(&mut self,id:usize,payload:I)->(out:Result<usize,I>)
        requires old(self).wf(), old(self).cleanup_state().wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(), final(self).cleanup_state().wf(),final(self).cleanup_state().origin()==old(self).cleanup_state().origin(),final(self).cleanup_state().drained_failure()==old(self).cleanup_state().drained_failure(),final(self).cleanup_state().frame(&old(self).cleanup_state(),id),final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids(),out.is_ok()==old(self).cleanup_state().live(id),
            final(self).effect_state()==old(self).effect_state(),final(self).checked_out()==old(self).checked_out(),
            final(self).initialized()==old(self).initialized(),
            out.is_err() ==> final(self).cleanup_state()==old(self).cleanup_state() && out->Err_0==payload,
            out.is_ok() ==> final(self).cleanup_state().live(id)
                && out->Ok_0==old(self).cleanup_state().queues()[id].slots().len()
                && final(self).cleanup_state().queues()[id].slots()==old(self).cleanup_state().queues()[id].slots().push(Some(payload)),
            final(self).status_links()==old(self).status_links(),
    {self.groups.register(id,payload)}
    #[allow(clippy::type_complexity)]
    pub fn cancel(&mut self,id:usize)
        requires old(self).wf(), old(self).cleanup_state().wf(),ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(), final(self).cleanup_state().wf(),final(self).cleanup_state().origin()==old(self).cleanup_state().origin(),final(self).cleanup_state().drained_failure()==old(self).cleanup_state().drained_failure(),final(self).cleanup_state().frame(&old(self).cleanup_state(),id),final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids(),
            final(self).cleanup_state().live(id)==old(self).cleanup_state().live(id),
            old(self).cleanup_state().live(id) ==> final(self).cleanup_state().queues()[id].protocol().stage().cancellation()
                && final(self).cleanup_state().queues()[id].protocol().stage().pending()==old(self).cleanup_state().queues()[id].protocol().stage().pending(),
            final(self).status_links()==old(self).status_links(),
    {self.groups.cancel(id)}
    #[allow(clippy::type_complexity)]
    pub fn pop(&mut self,id:usize)->(out:Result<Option<(RestoreTicket,I)>,RestoreError>)
        requires old(self).wf(), old(self).cleanup_state().wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(), final(self).cleanup_state().wf(),final(self).cleanup_state().origin()==old(self).cleanup_state().origin(),final(self).cleanup_state().drained_failure()==old(self).cleanup_state().drained_failure(),final(self).cleanup_state().frame(&old(self).cleanup_state(),id),final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids(),final(self).cleanup_state().live(id)==old(self).cleanup_state().live(id),
            out.is_ok() && out->Ok_0.is_some() ==> old(self).cleanup_state().live(id)
                && final(self).cleanup_state().queues()[id].issued()
                && final(self).cleanup_state().queues()[id].protocol().selected()==Some(out->Ok_0.unwrap().0)
                && old(self).cleanup_state().queues()[id].slots()[out->Ok_0.unwrap().0.token as int]==Some(out->Ok_0.unwrap().1),
            final(self).status_links()==old(self).status_links(),
    {self.groups.pop(id)}
    #[allow(clippy::type_complexity)]
    pub fn complete_future<E>(&mut self,id:usize,completion:Completion<RestoreTicket,Result<(),E>>,retry:Option<I>,policy:CleanupPolicy)
        ->(out:Result<CleanupReport<E,I>,(Completion<RestoreTicket,Result<(),E>>,Option<I>)>)
        requires old(self).wf(), old(self).cleanup_state().wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(), final(self).cleanup_state().wf(),final(self).cleanup_state().origin()==old(self).cleanup_state().origin(),final(self).cleanup_state().drained_failure()==(old(self).cleanup_state().drained_failure() || (out.is_ok() && out->Ok_0.outcome==RestoreOutcome::Drained)),final(self).cleanup_state().frame(&old(self).cleanup_state(),id),final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids(),final(self).cleanup_state().live(id)==old(self).cleanup_state().live(id),
            out.is_err() ==> out->Err_0==(completion,retry),
            out.is_ok() ==> old(self).cleanup_state().live(id) && out->Ok_0.result==completion.result()
                && old(self).cleanup_state().queues()[id].issued()
                && old(self).cleanup_state().queues()[id].protocol().selected()==Some(completion.argument())
                && !final(self).cleanup_state().queues()[id].issued(),
            final(self).status_links()==old(self).status_links(),
    {self.groups.complete_future(id,completion,retry,policy)}
    #[allow(clippy::type_complexity)]
    pub fn complete_failure<E>(&mut self,id:usize,ticket:RestoreTicket,error:E,retry:Option<I>,policy:CleanupPolicy)
        ->(out:Result<CleanupReport<E,I>,(RestoreTicket,E,Option<I>)>)
        requires old(self).wf(), old(self).cleanup_state().wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(), final(self).cleanup_state().wf(),final(self).cleanup_state().origin()==old(self).cleanup_state().origin(),final(self).cleanup_state().drained_failure()==(old(self).cleanup_state().drained_failure() || (out.is_ok() && out->Ok_0.outcome==RestoreOutcome::Drained)),final(self).cleanup_state().frame(&old(self).cleanup_state(),id),final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids(),final(self).cleanup_state().live(id)==old(self).cleanup_state().live(id),
            out.is_err() ==> out->Err_0==(ticket,error,retry),
            out.is_ok() ==> out->Ok_0.result==Err(error) && out->Ok_0.outcome!=RestoreOutcome::Succeeded,
            final(self).status_links()==old(self).status_links(),
    {self.groups.complete_failure(id,ticket,error,retry,policy)}
    #[allow(clippy::type_complexity)]
    pub fn complete_result<E>(&mut self,id:usize,ticket:RestoreTicket,result:Result<(),E>,retry:Option<I>,policy:CleanupPolicy)
        ->(out:Result<CleanupReport<E,I>,(RestoreTicket,Result<(),E>,Option<I>)>)
        requires old(self).wf(), old(self).cleanup_state().wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(), final(self).cleanup_state().wf(),final(self).cleanup_state().origin()==old(self).cleanup_state().origin(),final(self).cleanup_state().frame(&old(self).cleanup_state(),id),final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids(),final(self).cleanup_state().live(id)==old(self).cleanup_state().live(id),
            final(self).cleanup_state().drained_failure()==(old(self).cleanup_state().drained_failure() || (out.is_ok() && out->Ok_0.outcome==RestoreOutcome::Drained)),
            out.is_err() ==> out->Err_0==(ticket,result,retry),
            out.is_ok() ==> out->Ok_0.result==result && out->Ok_0.outcome==crate::cleanup_queue::completion::outcome(result,retry,policy),
            final(self).status_links()==old(self).status_links(),
    {self.groups.complete_result(id,ticket,result,retry,policy)}
    #[allow(clippy::type_complexity)]
    pub fn retry(&mut self,id:usize)->(out:Result<RestoreTicket,RestoreError>)
        requires old(self).wf(), old(self).cleanup_state().wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(), final(self).cleanup_state().wf(),final(self).cleanup_state().origin()==old(self).cleanup_state().origin(),final(self).cleanup_state().drained_failure()==old(self).cleanup_state().drained_failure(),final(self).cleanup_state().frame(&old(self).cleanup_state(),id),final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids(),final(self).cleanup_state().live(id)==old(self).cleanup_state().live(id),
            out.is_ok()==(old(self).cleanup_state().live(id) && old(self).cleanup_state().queues()[id].retry_enabled()),
            out.is_ok() ==> !final(self).cleanup_state().queues()[id].protocol().failed_spec(),
            final(self).status_links()==old(self).status_links(),
    {self.groups.retry(id)}
    pub fn contains(&self,id:usize)->(out:bool) ensures out==self.cleanup_state().live(id), {self.groups.contains(id)}
    pub fn get(&self,id:usize)->(out:Option<&CleanupQueue<I>>)
        ensures out.is_some()==self.cleanup_state().live(id),out.is_some() ==> *out.unwrap()==self.cleanup_state().queues()[id],
    {self.groups.get(id)}
    pub fn accepts_acquisition(&self,id:usize)->(out:bool)
        requires self.wf(),ensures out==(self.work_state().accepts() && self.cleanup_state().acquisition_open(id)),
    {self.work.accepting_now() && self.groups.accepts_acquisition(id)}
    pub fn has_pending(&self)->(out:bool) requires self.wf(),ensures out==self.cleanup_state().any_pending(), {self.groups.has_pending()}
    pub fn has_issued(&self)->(out:bool) requires self.wf(),ensures out==self.cleanup_state().any_issued(), {self.groups.has_issued()}
    pub fn has_failed(&self)->(out:bool) requires self.wf(),ensures out==self.cleanup_state().any_failed(), {self.groups.has_failed()}
    pub fn can_retry_all(&self)->(out:bool) requires self.wf(),ensures out==self.cleanup_state().retries_ready(), {self.groups.can_retry_all()}
    pub fn can_seal(&self)->(out:bool) requires self.wf(),ensures out==self.cleanup_state().all_drained(), {self.groups.can_seal()}
    pub fn remove(&mut self,id:usize)->(out:bool)
        requires old(self).wf(),ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),
            final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(),
            out ==> id!=0 && !final(self).cleanup_state().live(id),
            !out ==> *final(self)==*old(self),
            final(self).status_links()==old(self).status_links(),
    {if id==0 || self.effects.contains_key(&id) || self.checked_out.contains_key(&id) || self.statuses.contains_key(&id) {false} else {self.groups.remove(id)}}
    pub fn enqueue_owned_child(&mut self,group:usize,payload:C,inverse:I)->(out:Result<usize,(C,I)>)
        requires old(self).wf(),ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).origin()==old(self).origin(),
            final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==(payload,inverse),
            out.is_ok() ==> old(self).work_state().accepts() && old(self).cleanup_state().acquisition_open(group)
                && final(self).work_state().child_requests().last().value()==payload
                && final(self).cleanup_state().queues()[group].slots()==old(self).cleanup_state().queues()[group].slots().push(Some(inverse)),
            final(self).status_links()==old(self).status_links(),
    {self.work.enqueue_owned_child(&mut self.groups,group,payload,inverse)}
}
impl<V,C,P,I> Execution<V,C,P,I> {
    pub fn enqueue_effect(&mut self,source:usize,domain:u64,committed:Vec<Binding>,payload:P)->(out:Result<usize,(Vec<Binding>,P)>)
        requires old(self).wf(),ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).origin()==old(self).origin(),
            final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(),
            out.is_err() ==> *final(self)==*old(self) && out->Err_0==(committed,payload),
            out.is_ok() ==> final(self).work_state().group_requests().last().value().payload()==payload
                && final(self).work_state().group_requests().last().value().identity().matches(&final(self).cleanup_state())
                && out->Ok_0==old(self).cleanup_state().next_id()
                && final(self).cleanup_state().queues().contains_key(out->Ok_0)
                && final(self).cleanup_state().queues().remove(out->Ok_0)==old(self).cleanup_state().queues()
                && final(self).cleanup_state().queues()[out->Ok_0].protocol().stage().committed_view()==committed@,
            final(self).status_links()==old(self).status_links(),
    {self.work.enqueue_effect(&mut self.groups,source,domain,committed,payload)}
    pub fn admit_effect(&mut self,run:&mut EffectRun<P>,target:Option<&[Binding]>)->(out:bool)
        requires old(self).wf(),old(run).wf(),ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(run).wf(),
            final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),
            final(self).phase_spec()==old(self).phase_spec(),
            final(run).identity()==old(run).identity(),
            out==(old(run).current().is_none() && old(run).next()<u64::MAX
                && old(run).identity().matches(&old(self).cleanup_state())
                && old(self).cleanup_state().poll_enabled(old(run).identity().group_id(),target)),
            !out ==> *final(run)==*old(run),
            out ==> final(run).identity().matches(&final(self).cleanup_state())
                && final(run).current()==Some(old(run).next()) && !final(run).called()
                && final(self).cleanup_state().queues()[old(run).identity().group_id()].protocol().stage().pending(),
            final(self).status_links()==old(self).status_links(),
    {run.admit(&mut self.groups,target)}
    pub fn land_effect<E>(&mut self,run:&mut EffectRun<P>,reply:EffectReply<I,E>)->(out:Result<Option<StageReport<E>>,EffectReply<I,E>>)
        requires old(self).wf(),old(run).wf(),ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(run).wf(),
            final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),
            final(self).phase_spec()==old(self).phase_spec(),
            out.is_err() ==> out->Err_0==reply && *final(self)==*old(self) && *final(run)==*old(run),
            final(self).status_links()==old(self).status_links(),
    {run.land(&mut self.groups,reply)}
}
impl<V,N,X,G,C,E> Execution<V,ChildDispatch<N,X>,G,ChildCleanup<C,E>> {
    pub fn enqueue_native_child(&mut self,group:usize,payload:N)->(out:Result<(SharedChild,usize),N>)
        requires old(self).wf(),ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).origin()==old(self).origin(),
            final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(),
            out.is_err() ==> out->Err_0==payload && *final(self)==*old(self),
            final(self).status_links()==old(self).status_links(),
    {self.work.enqueue_native_child(&mut self.groups,group,payload)}
}
/// A production operation result whose inverse is already inside the real
/// cleanup queue. It is not an unregistered token left with ordinary host code.
pub struct ValueAdmission {pub outcome:crate::reversible_value::Outcome,pub next:Option<usize>,pub token:usize,
    pub evidence:Tracked<crate::reversible_value::registration::Evidence>}
impl ValueAdmission {
    pub(crate) fn completion_receipt(&self)->(out:Tracked<crate::reversible_value::joint::Receipt>)
        requires self.registration().certified(),
        ensures out@.wf(),out@.same(&self.registration().completion()),out@.covers(&self.registration().write()),
    {Tracked(self.evidence.borrow().completion_receipt())}

    pub open spec fn registration(&self)->crate::reversible_value::registration::Evidence {self.evidence@}
}
impl<V,C,G,Cb,X> Execution<V,C,G,ChildCleanup<Cb,X>> {
    pub fn apply_value(&mut self,id:usize,value:&crate::reversible_value::ReversibleValue,
        operation:crate::reversible_value::Operation,branch:crate::reversible_value::Branch)
        ->(out:Result<ValueAdmission,crate::reversible_value::ValueError>)
        requires old(self).wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),
            final(self).phase_spec()==old(self).phase_spec(),
            out.is_err() ==> final(self).same_runtime(old(self)),
            (out==Err(crate::reversible_value::ValueError::Closed))==!(old(self).work_state().accepts() && old(self).cleanup_state().acquisition_open(id)),
            out==Err(crate::reversible_value::ValueError::Closed) ==> *final(self)==*old(self),
            out!=Err(crate::reversible_value::ValueError::Closed) ==> final(self).value_attempts().appended(&old(self).value_attempts(),value),
            out!=Err(crate::reversible_value::ValueError::Closed) && out.is_err() ==>
                crate::reversible_value::attempt::value_rejection(final(self).value_attempts().event(),operation,out->Err_0),
            out.is_ok() ==> final(self).value_attempts().events().last().same(&out->Ok_0.registration().write()),
            out.is_ok() ==> old(self).work_state().accepts() && old(self).cleanup_state().acquisition_open(id) && final(self).cleanup_state().live(id)
                && out->Ok_0.next==branch.selected(out->Ok_0.outcome)
                && out->Ok_0.token==old(self).cleanup_state().queues()[id].slots().len()
                && final(self).cleanup_state().queues()[id].slots().len()==old(self).cleanup_state().queues()[id].slots().len()+1
                && final(self).cleanup_state().queues()[id].slots()[out->Ok_0.token as int].is_some()
                && final(self).cleanup_state().queues()[id].slots()[out->Ok_0.token as int].unwrap() is Value
                && out->Ok_0.registration().records(final(self).cleanup_state().queues()[id].slots()[out->Ok_0.token as int].unwrap()->Value_0,
                    final(self).cleanup_state().queues()[id].link(),final(self).cleanup_state().queues()[id].protocol().domain_id(),out->Ok_0.token)
                && (crate::reversible_value::Applied {outcome:out->Ok_0.outcome,next:out->Ok_0.next,pending:Tracked(None),
                    inverse:final(self).cleanup_state().queues()[id].slots()[out->Ok_0.token as int].unwrap()->Value_0}).corresponds(value,operation,branch),
            final(self).status_links()==old(self).status_links(),
    {self.apply_value_following(id,value,operation,branch,Tracked(None))}
    pub(crate) fn apply_value_following(&mut self,id:usize,value:&crate::reversible_value::ReversibleValue,
        operation:crate::reversible_value::Operation,branch:crate::reversible_value::Branch,Tracked(cause):Tracked<Option<crate::reversible_value::joint::Receipt>>)
        ->(out:Result<ValueAdmission,crate::reversible_value::ValueError>)
        requires old(self).wf(),cause.is_some() ==> cause.unwrap().wf(),
        ensures out!=Err(crate::reversible_value::ValueError::Closed) && cause.is_some() && cause.unwrap().journal()==value.journal_spec() ==>
                final(self).value_attempts().events().last().follows(&cause.unwrap()),
            final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),
            final(self).phase_spec()==old(self).phase_spec(),
            out.is_err() ==> final(self).same_runtime(old(self)),
            (out==Err(crate::reversible_value::ValueError::Closed))==!(old(self).work_state().accepts() && old(self).cleanup_state().acquisition_open(id)),
            out==Err(crate::reversible_value::ValueError::Closed) ==> *final(self)==*old(self),
            out!=Err(crate::reversible_value::ValueError::Closed) ==> final(self).value_attempts().appended(&old(self).value_attempts(),value),
            out.is_err() && out!=Err(crate::reversible_value::ValueError::Closed) ==>
                crate::reversible_value::attempt::value_rejection(final(self).value_attempts().event(),operation,out->Err_0),
            out.is_ok() ==> final(self).value_attempts().events().last().same(&out->Ok_0.registration().write()),
            out.is_ok() ==> final(self).cleanup_state().queues()[id].protocol().waiting()==old(self).cleanup_state().queues()[id].protocol().waiting().push(out->Ok_0.token),
            out.is_ok() ==> final(self).cleanup_state().frame(&old(self).cleanup_state(),id)
                && final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids()
                && final(self).cleanup_state().queues()[id].link()==old(self).cleanup_state().queues()[id].link()
                && final(self).cleanup_state().queues()[id].slots().take(old(self).cleanup_state().queues()[id].slots().len() as int)==old(self).cleanup_state().queues()[id].slots(),
            out.is_ok() ==> final(self).cleanup_state().live(id) && old(self).work_state().accepts() && old(self).cleanup_state().acquisition_open(id)
                && out->Ok_0.next==branch.selected(out->Ok_0.outcome)
                && out->Ok_0.token==old(self).cleanup_state().queues()[id].slots().len()
                && final(self).cleanup_state().queues()[id].slots().len()==old(self).cleanup_state().queues()[id].slots().len()+1
                && final(self).cleanup_state().queues()[id].slots()[out->Ok_0.token as int].is_some()
                && final(self).cleanup_state().queues()[id].slots()[out->Ok_0.token as int].unwrap() is Value
                && out->Ok_0.registration().records(final(self).cleanup_state().queues()[id].slots()[out->Ok_0.token as int].unwrap()->Value_0,
                    final(self).cleanup_state().queues()[id].link(),final(self).cleanup_state().queues()[id].protocol().domain_id(),out->Ok_0.token)
                && (crate::reversible_value::Applied {outcome:out->Ok_0.outcome,next:out->Ok_0.next,pending:Tracked(None),
                    inverse:final(self).cleanup_state().queues()[id].slots()[out->Ok_0.token as int].unwrap()->Value_0}).corresponds(value,operation,branch),
            final(self).status_links()==old(self).status_links(),
    {
        if !self.accepts_acquisition(id) {return Err(crate::reversible_value::ValueError::Closed);}
        let applied=value.apply_pending_following(operation,branch,Ghost(crate::reversible_value::joint::local(self.cleanup_state().queues()[id].link(),value.journal_spec())),Tracked(self.attempts.borrow_mut()),Tracked(cause))?;
        let outcome=applied.outcome;let next=applied.next;
        let registered=self.register_inverse(id,applied);
        Ok(ValueAdmission {outcome,next,token:registered.token,evidence:registered.evidence})
    }

}

impl<V,C,G,Cb,X> Execution<V,C,G,ChildCleanup<Cb,X>> {
    pub fn dispatch_cleanup(&mut self,id:usize)->(out:Result<Option<crate::cleanup_queue::completion::CleanupDispatch<Cb,X>>,RestoreError>)
        requires old(self).wf(),
        ensures final(self).execution_journal()==old(self).execution_journal(),final(self).wf(),final(self).value_attempts()==old(self).value_attempts(),final(self).capture()==old(self).capture(),final(self).work_state()==old(self).work_state(),final(self).value_state()==old(self).value_state(),final(self).phase_spec()==old(self).phase_spec(),
            final(self).cleanup_state().frame(&old(self).cleanup_state(),id),
            final(self).cleanup_state().domain_ids()==old(self).cleanup_state().domain_ids(),
            final(self).cleanup_state().queues().dom()==old(self).cleanup_state().queues().dom(),
            final(self).cleanup_state().drained_failure()==old(self).cleanup_state().drained_failure(),
            (out.is_err() || out==Ok(None)) && old(self).cleanup_state().live(id) ==>
                final(self).cleanup_state().queues()[id].same(&old(self).cleanup_state().queues()[id])
                && final(self).cleanup_state().queues()[id].trace()==old(self).cleanup_state().queues()[id].trace(),
            out.is_ok() && out->Ok_0.is_some() ==> out->Ok_0.unwrap().selected_from(old(self).cleanup_state().queues()[id].protocol().selected(),old(self).cleanup_state().queues()[id].protocol().waiting()),
            out.is_ok() && out->Ok_0.is_some() ==> old(self).cleanup_state().live(id)
                && out->Ok_0.unwrap().from_slot(old(self).cleanup_state().queues()[id].slots()),
            out.is_ok() && out->Ok_0.is_some() && out->Ok_0.unwrap() is Value ==> {
                let report=out->Ok_0.unwrap();let ticket=report->Value_ticket;let completion=report->Value_completion;
                &&& completion.evidence().records(old(self).cleanup_state().queues()[id].slots()[ticket.token as int].unwrap()->Value_0,ticket,old(self).cleanup_state().queues()[id].link())
                &&& final(self).cleanup_state().queues()[id].link().is_some() ==> completion.evidence().acknowledgement().unwrap().events()==final(self).cleanup_state().queues()[id].trace()
                &&& final(self).cleanup_state().queues()[id].slots()==old(self).cleanup_state().queues()[id].slots().update(ticket.token as int,
                    if completion.restored.is_some() {None} else {old(self).cleanup_state().queues()[id].slots()[ticket.token as int]})
                &&& final(self).cleanup_state().queues()[id].protocol().failed_spec()==completion.restored.is_none()
            },
            final(self).status_links()==old(self).status_links(),
    {self.groups.dispatch(id)}
}

} // verus!
