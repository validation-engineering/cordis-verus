//! Publication, Episode ownership and pending inverses at every actual cut.
//! The source is the runtime's complete typed history and shared Journal, not
//! a caller-supplied restored table or a value-only control projection.
#[path = "native_observation_client.rs"]
pub mod client;
use super::{registry_recovery as registry, History, Observation, Snapshot};
#[cfg(verus_keep_ghost)]
use crate::lifecycle_state::{native::runtime::owner::EpisodeOwner, services::NativePublication};
use crate::reversible_value::joint::pending_recovery as pending;
#[cfg(verus_keep_ghost)]
use crate::{refinement::Rule, reversible_value::joint};
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
impl<V> History<V> {
    pub open spec fn publication_registry(&self)->registry::Registry<NativePublication<V>> {
        registry::Registry {states:self.states.map(|_:int,s:Observation<V>|s.publications),labels:self.labels,opening:Rule::Finish}
    }
    pub open spec fn owner_registry(&self)->registry::Registry<EpisodeOwner> {
        registry::Registry {states:self.states.map(|_:int,s:Observation<V>|s.owners),labels:self.labels,opening:Rule::Begin}
    }
    pub proof fn recovery_registries(&self)
        requires self.valid(),ensures self.publication_registry().valid(),self.owner_registry().valid(),
    {
        assert forall|i:int|0<=i<self.labels.len() implies #[trigger] self.publication_registry().transition(i) by {assert(super::step(self.states[i],self.states[i+1],self.labels[i].0,self.labels[i].1));}
        assert forall|i:int|0<=i<self.labels.len() implies #[trigger] self.owner_registry().transition(i) by {assert(super::step(self.states[i],self.states[i+1],self.labels[i].0,self.labels[i].1));}
    }
}
/// An exact typed/native observation at a raw Journal cut. Cleanup and value
/// events between lifecycle commits remain visible in the pending component.
pub ghost struct Point<V> {pub native:Observation<V>,pub pending:Map<nat,nat>,pub index:int}
pub ghost struct Interval<V> {pub source:Snapshot<V>,pub start:nat,pub first:int}
pub ghost struct Scope {pub providers:Set<usize>,pub objects:Set<nat>}
pub ghost enum Issue {Publication(registry::Issue),Owner(registry::Issue),Pending(pending::Issue)}
impl<V> Interval<V> {
    pub open spec fn frames(&self)->Seq<joint::Frame> {self.source.joint_spec().events()}
    pub open spec fn history(&self)->History<V> {self.source.history()}
    pub open spec fn end(&self)->nat {self.frames().len()}
    pub open spec fn last(&self)->int {self.history().states.len()-1}
    pub open spec fn wf(&self)->bool {
        self.source.certified() && self.start<=self.end() && joint::native::recorded(self.frames(),self.start,self.source.key())
            && 0<=self.first<=self.last()
            && self.history().states[self.first].project(self.first as nat)==joint::native::at(self.frames(),self.start,self.source.key())
            && self.source.positions()[self.first]<self.start
            && forall|i:int|self.first<i<self.history().states.len() ==> self.start<=#[trigger] self.source.positions()[i]
    }
    pub open spec fn normalized(&self)->bool {
        self.history().states.last().publications==self.history().publication_registry().reconstructed(self.first,self.last())
            && self.history().states.last().owners==self.history().owner_registry().reconstructed(self.first,self.last())
            && joint::pending_at(self.frames(),self.end())==pending::reconstructed(self.frames(),self.start,self.end())
    }
    pub open spec fn balanced(&self,scope:Scope)->bool {
        self.history().publication_registry().balanced(self.first,self.last(),scope.providers)
            && self.history().owner_registry().balanced(self.first,self.last(),scope.providers)
            && pending::balanced(self.frames(),self.start,self.end(),scope.objects)
    }
    pub open spec fn recovered(&self,scope:Scope)->bool {
        self.history().publication_registry().same_on(self.first,self.last(),scope.providers)
            && self.history().owner_registry().same_on(self.first,self.last(),scope.providers)
            && pending::project(joint::pending_at(self.frames(),self.end()),scope.objects)
                ==pending::project(joint::pending_at(self.frames(),self.start),scope.objects)
    }
    pub open spec fn diagnosed(&self,scope:Scope,issue:Issue)->bool {
        match issue {
            Issue::Publication(issue)=>self.history().publication_registry().diagnosed(self.first,self.last(),scope.providers,issue),
            Issue::Owner(issue)=>self.history().owner_registry().diagnosed(self.first,self.last(),scope.providers,issue),
            Issue::Pending(issue)=>pending::diagnosed(self.frames(),self.start,self.end(),scope.objects,issue),
        }
    }
    /// Finite scope is collected from the actual source, not a claimed list of
    /// successful effects. It covers all providers and pending objects here.
    pub open spec fn scope(&self)->Scope {
        Scope {providers:self.history().states[self.first].publications.dom()
            .union(self.history().states[self.first].owners.dom())
            .union(self.history().labels.map(|_:int,label:(usize,Rule)|label.0).to_set()),
            objects:self.frames().map(|_:int,frame:joint::Frame|frame.event.key).to_set()}
    }
    pub open spec fn recovered_all(&self)->bool {
        self.history().states.last().publications==self.history().states[self.first].publications
            && self.history().states.last().owners==self.history().states[self.first].owners
            && joint::pending_at(self.frames(),self.end())==joint::pending_at(self.frames(),self.start)
    }
    #[verifier::spinoff_prover]
    pub proof fn complete_scope(&self)
        requires self.wf(),self.normalized(),self.recovered(self.scope()),
        ensures self.recovered_all(),
    {
        hide(joint::valid);hide(joint::step);hide(super::step);
        self.source.valid_history();self.source.joint_spec().valid_history();self.history().recovery_registries();
        self.history().publication_registry().recover_map(self.first,self.last(),self.scope().providers);
        self.history().owner_registry().recover_map(self.first,self.last(),self.scope().providers);
        pending::complete_scope(self.frames(),self.start);pending::complete_scope(self.frames(),self.end());
    }
    /// The three observation components are restored together, or a concrete
    /// source effect prevents that conclusion. Control/heap equality is separate.
    #[verifier::spinoff_prover]
    pub proof fn check_all(&self)->(issue:Option<Issue>)
        requires self.wf(),
        ensures self.normalized(),issue.is_none()==self.balanced(self.scope()),
            issue.is_none() ==> self.recovered_all(),
            issue.is_some() ==> self.diagnosed(self.scope(),issue.unwrap()),
    {
        let issue=self.check(self.scope());
        if issue.is_none() {self.complete_scope();}
        issue
    }
    /// Derive the whole observation from retained sources and unconsumed
    /// creations, at an arbitrary intermediate cut, including failed cleanup.
    #[verifier::spinoff_prover]
    pub proof fn at(&self,n:nat)->(point:Point<V>)
        requires self.wf(),self.start<=n<=self.end(),
        ensures self.first<=point.index<=self.last(),point.native==self.history().states[point.index],
            point.native.project(point.index as nat)==joint::native::at(self.frames(),n,self.source.key()),
            point.pending==joint::pending_at(self.frames(),n),
            point.native.publications==self.history().publication_registry().reconstructed(self.first,point.index),
            point.native.owners==self.history().owner_registry().reconstructed(self.first,point.index),
            point.pending==pending::reconstructed(self.frames(),self.start,n),
    {
        hide(joint::valid);hide(joint::step);
        self.source.valid_history();self.source.joint_spec().valid_history();self.history().recovery_registries();
        joint::native::monotone(self.frames(),self.start,n,self.source.key());
        let index=self.source.recovery_index(n);
        self.history().publication_registry().normalize(self.first,index);
        self.history().owner_registry().normalize(self.first,index);
        pending::normalize(self.frames(),self.start,n);
        Point {native:self.history().states[index],pending:joint::pending_at(self.frames(),n),index}
    }
    #[verifier::spinoff_prover]
    pub proof fn check(&self,scope:Scope)->(issue:Option<Issue>)
        requires self.wf(),
        ensures self.normalized(),issue.is_none()==self.balanced(scope),
            issue.is_none() ==> self.recovered(scope),issue.is_some() ==> self.diagnosed(scope,issue.unwrap()),
    {
        hide(joint::valid);hide(joint::step);hide(super::step);
        self.source.valid_history();self.source.joint_spec().valid_history();self.history().recovery_registries();
        self.at(self.end());
        if let Some(issue)=self.history().publication_registry().check(self.first,self.last(),scope.providers) {
            return Some(Issue::Publication(issue));
        }
        if let Some(issue)=self.history().owner_registry().check(self.first,self.last(),scope.providers) {
            return Some(Issue::Owner(issue));
        }
        if let Some(issue)=pending::check(self.frames(),self.start,self.end(),scope.objects) {return Some(Issue::Pending(issue));}
        assert(self.balanced(scope));
        None
    }
    /// Every reported registry event has an actual ordered native commit.
    /// A label-level index cannot silently name a different provider or rule.
    pub proof fn native_source(&self,index:int)
        requires self.wf(),self.first<=index<self.last(),
        ensures self.start<=self.source.positions()[index+1]<self.end(),
            self.frames()[self.source.positions()[index+1] as int].event.key==self.source.key(),
            self.frames()[self.source.positions()[index+1] as int].event.change==
                (joint::Change::Native {actor:self.history().labels[index].0,rule:self.history().labels[index].1}),
    {self.source.valid_history();}
}
impl<V> Snapshot<V> {
    /// Derive the typed state index at a raw cut from the real native record.
    /// This includes cuts strictly between lifecycle commits.
    #[verifier::spinoff_prover]
    pub proof fn recovery_index(&self,n:nat)->(index:int)
        requires self.certified(),n<=self.joint_spec().events().len(),joint::native::recorded(self.joint_spec().events(),n,self.key()),
        ensures 0<=index<self.history().states.len(),self.positions()[index]<n,
            self.history().states[index].project(index as nat)==joint::native::at(self.joint_spec().events(),n,self.key()),
            forall|i:int|index<i<self.history().states.len() ==> n<=#[trigger] self.positions()[i],
    {
        hide(joint::valid);hide(joint::step);self.valid_history();self.joint_spec().valid_history();
        let frames=self.joint_spec().events();let key=self.key();
        let at=joint::record_origin(frames,n,key);let index=self.complete_at(at);
        assert(joint::step(joint::state_at(frames,at),frames[at as int].state,frames[at as int].event)) by {reveal(joint::valid);}
        assert(joint::native::recorded(frames,at+1,key)) by {reveal(joint::step);}
        assert(joint::native::at(frames,at+1,key)==joint::native::at(frames,n,key)) by {reveal(joint::step);}
        joint::native::unchanged_interval(frames,at+1,n,key);
        assert forall|i:int|index<i<self.history().states.len() implies n<=#[trigger] self.positions()[i] by {
            if self.positions()[i]<n {assert(at<self.positions()[i]<n);}
        }
        index
    }
    /// The actual invocation Begin selects the pre-Begin cut, rather than the
    /// later return snapshot. Intermediate publication and pending changes are
    /// therefore included even if the call returned successfully.
    #[verifier::spinoff_prover]
    pub proof fn recovery_since_begin(&self,begin:&super::super::episode::Begin)->(out:Interval<V>)
        requires self.certified(),begin.wf(),self.key()==begin.native(),self.joint_spec().covers(&begin.checkpoint()),
        ensures out.wf(),out.source==*self,out.start==begin.at(),out.normalized(),
    {
        hide(joint::valid);hide(joint::step);self.valid_history();self.joint_spec().valid_history();begin.facts();
        let frames=self.joint_spec().events();let at=begin.at();
        assert(frames[at as int]==begin.checkpoint().events()[at as int]);
        assert(joint::step(joint::state_at(frames,at),frames[at as int].state,frames[at as int].event)) by {reveal(joint::valid);}
        assert(joint::native::recorded(frames,at,self.key())) by {reveal(joint::step);reveal(joint::changes);}
        self.recovery_interval(at)
    }
    #[verifier::spinoff_prover]
    pub proof fn recovery_interval(&self,start:nat)->(out:Interval<V>)
        requires self.certified(),start<=self.joint_spec().events().len(),joint::native::recorded(self.joint_spec().events(),start,self.key()),
        ensures out.wf(),out.source==*self,out.start==start,out.normalized(),
    {
        let first=self.recovery_index(start);let out=Interval {source:*self,start,first};
        out.at(out.end());out
    }
}
/// The snapshot is real; normalization and historical payloads are erased.
pub struct Capture<V> {pub cut:Snapshot<V>,pub interval:Ghost<Interval<V>>,pub issue:Ghost<Option<Issue>>}
}
