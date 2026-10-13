//! Joint history of actual native control and published slot tables.
//! This observation preserves retained publications while a provider unloads.
//! It does not interpret slot interiors, outstanding episode programs or opaque
//! callbacks as paper effect functions.
use super::owner::EpisodeOwner;
use crate::lifecycle_state::services::NativePublication;
use crate::refinement as r;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub struct Observation<V> {pub control:r::State,pub publications:Map<usize,NativePublication<V>>,pub owners:Map<usize,EpisodeOwner>}
/// Independent public-registry relation. Finish adds exactly its publication;
/// Unload removes exactly its publication. Every other rule preserves all
/// published slots, even when they become invisible during restoration.
pub open spec fn step<V>(a:Observation<V>,z:Observation<V>,actor:usize,rule:r::Rule)->bool {
    &&& r::step(a.control,z.control,actor,rule)
    &&& match rule {
        r::Rule::Begin=> !a.owners.contains_key(actor) && z.owners.contains_key(actor)
            && z.owners==a.owners.insert(actor,z.owners[actor]),
        r::Rule::Unload=>z.owners==a.owners.remove(actor),
        _=>z.owners==a.owners,
    }
    &&& match rule {
        r::Rule::Finish=> !a.publications.contains_key(actor) && z.publications.contains_key(actor)
            && z.publications==a.publications.insert(actor,z.publications[actor]),
        r::Rule::Unload=>z.publications==a.publications.remove(actor),
        _=>z.publications==a.publications,
    }
}
pub struct History<V> {pub states:Seq<Observation<V>>,pub labels:Seq<(usize,r::Rule)>}
impl<V> History<V> {
    pub open spec fn valid(&self)->bool {
        &&& self.states.len()==self.labels.len()+1
        &&& self.states.first().control.fibers.dom().is_empty() && self.states.first().publications.is_empty() && self.states.first().owners.is_empty()
        &&& forall|i:int| 0<=i<self.labels.len() ==>
            #[trigger] step(self.states[i],self.states[i+1],self.labels[i].0,self.labels[i].1)
    }
    pub open spec fn append(&self,state:Observation<V>,actor:usize,rule:r::Rule)->Self {
        Self {states:self.states.push(state),labels:self.labels.push((actor,rule))}
    }
    pub open spec fn extends(&self,prior:Self)->bool {
        self.labels.len()==prior.labels.len()+1 && self.states.drop_last()==prior.states && self.labels.drop_last()==prior.labels
    }
    pub proof fn extended(&self,state:Observation<V>,actor:usize,rule:r::Rule)
        requires self.valid(),step(self.states.last(),state,actor,rule),
        ensures self.append(state,actor,rule).valid(),self.append(state,actor,rule).extends(*self),
    {
        let next=self.append(state,actor,rule);
        assert(next.states.drop_last() =~= self.states);assert(next.labels.drop_last() =~= self.labels);
        assert forall|i:int| 0<=i<next.labels.len() implies
            #[trigger] step(next.states[i],next.states[i+1],next.labels[i].0,next.labels[i].1) by {
            if i<self.labels.len() {assert(step(self.states[i],self.states[i+1],self.labels[i].0,self.labels[i].1));}
        }
    }
    /// No lifecycle transition before successful Unload can rebind an escaped
    /// execution to another work domain, including Retire/Restart and Finish.
    pub proof fn owner_retained(&self,start:int,end:int,id:usize)
        requires self.valid(),0<=start<=end<self.states.len(),self.states[start].owners.contains_key(id),
            forall|i:int| start<=i<end ==> #[trigger] self.labels[i]!=(id,r::Rule::Unload),
        ensures self.states[end].owners.contains_key(id),self.states[end].owners[id]==self.states[start].owners[id],
        decreases end-start,
    {
        if start<end {
            self.owner_retained(start,end-1,id);
            let i=end-1;
            assert(0<=i<self.labels.len());
            assert(step::<V>(self.states[i],self.states[i+1],self.labels[i].0,self.labels[i].1));
        }
    }
    /// Every retained owner in this actual history comes from a successful
    /// Begin, rather than a caller's claimed expected execution identity.
    pub proof fn owner_has_begin(&self,index:int,id:usize)
        requires self.valid(),0<=index<self.states.len(),self.states[index].owners.contains_key(id),
        ensures exists|at:int| 0<=at<index && self.labels[at]==(id,r::Rule::Begin)
            && self.states[at+1].owners.contains_key(id)
            && self.states[at+1].owners[id]==self.states[index].owners[id],
        decreases index,
    {
        assert(index>0);
        let i=index-1;
        assert(0<=i<self.labels.len());
        assert(step::<V>(self.states[i],self.states[i+1],self.labels[i].0,self.labels[i].1));
        if self.labels[index-1]==(id,r::Rule::Begin) {
            assert(self.labels[index-1]==(id,r::Rule::Begin));
        } else {
            self.owner_has_begin(index-1,id);
            let at=choose|at:int| 0<=at<index-1 && self.labels[at]==(id,r::Rule::Begin)
                && self.states[at+1].owners.contains_key(id)
                && self.states[at+1].owners[id]==self.states[index-1].owners[id];
            assert(self.states[at+1].owners[id]==self.states[index].owners[id]);
        }
    }
    pub open spec fn controls(&self)->Seq<r::State> {self.states.map(|_:int,s:Observation<V>|s.control)}
    pub open spec fn base_only(&self)->bool {forall|i:int| 0<=i<self.labels.len() ==> #[trigger] self.labels[i].1!=r::Rule::Restart}
    /// The structural/value history has one continuous control projection.
    /// Explicit Restart remains an extension when interpreting this projection.
    pub proof fn correspondence(&self)
        requires self.valid(),
        ensures r::execution(self.controls(),self.labels,true),
            self.base_only() ==> r::execution(self.controls(),self.labels,false)
                && r::reaches(self.controls().first(),self.controls().last(),self.labels.len(),false),
    {
        assert forall|i:int| 0<=i<self.labels.len() implies r::labelled_step(self.controls()[i],self.controls()[i+1],self.labels[i],true) by {
            assert(step(self.states[i],self.states[i+1],self.labels[i].0,self.labels[i].1));
        }
        if self.base_only() {
            assert forall|i:int| 0<=i<self.labels.len() implies r::labelled_step(self.controls()[i],self.controls()[i+1],self.labels[i],false) by {
                assert(step(self.states[i],self.states[i+1],self.labels[i].0,self.labels[i].1));
            }
            r::finite_execution_refines(self.controls(),self.labels,false);
        }
    }
}
}
