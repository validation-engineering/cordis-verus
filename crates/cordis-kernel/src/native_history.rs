//! Joint history of actual native control and published slot tables.
//! This observation preserves retained publications while a provider unloads.
//! It does not interpret slot interiors, outstanding episode programs or opaque
//! callbacks as paper effect functions.
use super::owner::EpisodeOwner;
use crate::lifecycle_state::services::NativePublication;
use crate::refinement as r;
use crate::reversible_value::joint;
#[cfg(verus_keep_ghost)]
use crate::reversible_value::joint::native;
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
pub open spec fn publication<V>(p:NativePublication<V>)->native::Publication {
    native::Publication {origin:p.origin(),work_domain:p.capture().work_domain,realms:p.capture().realms,anchor:p.capture().anchor,ports:p.values().dom(),
        bindings:p.capture().bindings,imports:p.capture().imports.dom(),
        sources:Map::new(p.capture().sources.dom(),|id:usize|p.capture().sources[id].origin)}
}
pub open spec fn publications<V>(entries:Map<usize,NativePublication<V>>)->Map<usize,native::Publication> {
    Map::new(entries.dom(),|id:usize|publication(entries[id]))
}
impl<V> Observation<V> {
    pub open spec fn project(&self,revision:nat)->native::State {
        native::State {revision,control:self.control,owners:self.owners,publications:publications(self.publications)}
    }
}
pub proof fn project_step<V>(a:Observation<V>,b:Observation<V>,actor:usize,rule:r::Rule,revision:nat)
    requires step(a,b,actor,rule),ensures native::step(a.project(revision),b.project(revision+1),actor,rule),
{
    reveal(native::step);
    if rule==r::Rule::Finish {
        assert(publications(b.publications) =~= publications(a.publications).insert(actor,publication(b.publications[actor])));
    } else if rule==r::Rule::Unload {
        assert(publications(b.publications) =~= publications(a.publications).remove(actor));
    }
}
pub struct History<V> {pub states:Seq<Observation<V>>,pub labels:Seq<(usize,r::Rule)>}
impl<V> History<V> {
    /// Every exact typed observation has an actual, ordered joint commit.
    /// Position zero records allocation; later positions record the same rule.
    pub open spec fn indexed(&self,positions:Seq<nat>,frames:Seq<joint::Frame>,key:nat)->bool {
        &&& positions.len()==self.states.len()
        &&& forall|i:int| 0<=i<self.states.len() ==> #[trigger] positions[i]<frames.len()
            && frames[positions[i] as int].event.key==key
            && frames[positions[i] as int].event.after==(joint::Record::Native {state:self.states[i].project(i as nat)})
            && frames[positions[i] as int].event.change==if i==0 {joint::Change::Allocate}
                else {joint::Change::Native {actor:self.labels[i-1].0,rule:self.labels[i-1].1}}
        &&& forall|i:int,j:int| 0<=i<j<self.states.len() ==> #[trigger] positions[i]<#[trigger] positions[j]
    }
    pub proof fn extend_indexed(&self,positions:Seq<nat>,before:Seq<joint::Frame>,after:Seq<joint::Frame>,key:nat)
        requires self.indexed(positions,before,key),before.len()<=after.len(),after.take(before.len() as int)==before,
        ensures self.indexed(positions,after,key),
    {
        assert forall|i:int| 0<=i<self.states.len() implies #[trigger] positions[i]<after.len()
            && after[positions[i] as int].event.key==key
            && after[positions[i] as int].event.after==(joint::Record::Native {state:self.states[i].project(i as nat)})
            && after[positions[i] as int].event.change==if i==0 {joint::Change::Allocate}
                else {joint::Change::Native {actor:self.labels[i-1].0,rule:self.labels[i-1].1}} by {
            assert(after[positions[i] as int]==before[positions[i] as int]);
        }
    }
    pub proof fn append_indexed(&self,positions:Seq<nat>,before:Seq<joint::Frame>,after:Seq<joint::Frame>,key:nat,state:Observation<V>,actor:usize,rule:r::Rule)
        requires self.valid(),self.indexed(positions,before,key),before.len()<after.len(),after.take(before.len() as int)==before,
            after.last().event.key==key,after.last().event.change==(joint::Change::Native {actor,rule}),
            after.last().event.after==(joint::Record::Native {state:state.project(self.states.len())}),
        ensures self.append(state,actor,rule).indexed(positions.push((after.len()-1) as nat),after,key),
    {
        self.extend_indexed(positions,before,after,key);
        let next=positions.push((after.len()-1) as nat);
        assert forall|i:int,j:int| 0<=i<j<self.states.len()+1 implies #[trigger] next[i]<#[trigger] next[j] by {
            if j==self.states.len() {assert(positions[i]<before.len());}
        }
    }
    /// The interval before each indexed transition has no hidden native step.
    /// Thus the typed history is a complete projection, not just a subsequence.
    pub proof fn interval(&self,positions:Seq<nat>,frames:Seq<joint::Frame>,key:nat,index:int)
        requires self.valid(),joint::valid(frames),self.indexed(positions,frames,key),0<=index<self.labels.len(),
        ensures native::recorded(frames,positions[index]+1,key),native::recorded(frames,positions[index+1],key),
            native::at(frames,positions[index]+1,key)==self.states[index].project(index as nat),
            native::at(frames,positions[index+1],key)==self.states[index].project(index as nat),
            forall|i:int| positions[index]<i<positions[index+1] ==> #[trigger] frames[i].event.key!=key,
    {
        let start=positions[index];let end=positions[index+1];
        assert(joint::step(joint::state_at(frames,start),frames[start as int].state,frames[start as int].event));
        assert(joint::step(joint::state_at(frames,end),frames[end as int].state,frames[end as int].event));
        reveal(joint::changes);reveal(native::step);
        native::unchanged_interval(frames,start+1,end,key);
    }
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
    /// This is equality of the actual typed publications, including Arc
    /// references and their exact Begin capture, not merely equal port names.
    pub proof fn publication_retained(&self,start:int,end:int,id:usize)
        requires self.valid(),0<=start<=end<self.states.len(),self.states[start].publications.contains_key(id),
            forall|i:int| start<=i<end ==> #[trigger] self.labels[i]!=(id,r::Rule::Unload),
        ensures self.states[end].publications.contains_pair(id,self.states[start].publications[id]),
        decreases end-start,
    {
        if start<end {
            self.publication_retained(start,end-1,id);
            let i=end-1;assert(0<=i<self.labels.len());
            assert(step::<V>(self.states[i],self.states[i+1],self.labels[i].0,self.labels[i].1));
        }
    }
    /// Every retained publication is the exact value table produced by an
    /// actual successful Finish. A restart cannot forge a replacement table.
    pub proof fn publication_has_finish(&self,index:int,id:usize)
        requires self.valid(),0<=index<self.states.len(),self.states[index].publications.contains_key(id),
        ensures exists|at:int| 0<=at<index && self.labels[at]==(id,r::Rule::Finish)
            && self.states[at+1].publications.contains_pair(id,self.states[index].publications[id]),
        decreases index,
    {
        assert(index>0);let i=index-1;
        assert(0<=i<self.labels.len());
        assert(step::<V>(self.states[i],self.states[i+1],self.labels[i].0,self.labels[i].1));
        if self.labels[i]!=(id,r::Rule::Finish) {
            self.publication_has_finish(i,id);
            let at=choose|at:int| 0<=at<i && self.labels[at]==(id,r::Rule::Finish)
                && self.states[at+1].publications.contains_pair(id,self.states[i].publications[id]);
            assert(self.states[at+1].publications.contains_pair(id,self.states[index].publications[id]));
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
    /// Every current root or Child has an actual Insert with the same parent.
    /// A later lifecycle rule cannot manufacture or reparent a registration.
    pub proof fn insertion_origin(&self,end:int,id:usize)->(at:int)
        requires self.valid(),0<=end<self.states.len(),r::registered(self.states[end].control,id),
        ensures 0<=at<end,self.labels[at]==(id,r::Rule::Insert),
            r::registered(self.states[at+1].control,id),
            self.states[at+1].control.fibers[id].parent==self.states[end].control.fibers[id].parent,
        decreases end,
    {
        assert(end>0);let i=end-1;
        assert(0<=i<self.labels.len());assert(step(self.states[i],self.states[i+1],self.labels[i].0,self.labels[i].1));
        if self.labels[i]==(id,r::Rule::Insert) {i}
        else {self.insertion_origin(i,id)}
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

/// An actual native checkpoint retains typed evidence only in erased fields.
/// Rust keeps one shared Journal handle; it does not retain old Arc payloads.
#[allow(dead_code)]
pub struct Snapshot<V> {joint:joint::Snapshot,history:Ghost<History<V>>,positions:Ghost<Seq<nat>>,key:Ghost<nat>}
impl<V> Snapshot<V> {
    pub closed spec fn history(&self)->History<V> {self.history@}
    pub closed spec fn positions(&self)->Seq<nat> {self.positions@}
    pub closed spec fn key(&self)->nat {self.key@}
    pub closed spec fn joint_spec(&self)->joint::Snapshot {self.joint}
    pub closed spec fn certified(&self)->bool {
        self.joint_spec().certified() && self.history().valid()
            && self.history().indexed(self.positions(),self.joint_spec().events(),self.key())
            && self.joint_spec().last().contains_pair(self.key(),joint::Record::Native {
                state:self.history().states.last().project(self.history().labels.len())})
    }
    pub(crate) fn new(joint:joint::Snapshot,Ghost(history):Ghost<History<V>>,Ghost(positions):Ghost<Seq<nat>>,Ghost(key):Ghost<nat>)->(out:Self)
        requires joint.certified(),history.valid(),history.indexed(positions,joint.events(),key),
            joint.last().contains_pair(key,joint::Record::Native {state:history.states.last().project(history.labels.len())}),
        ensures out.certified(),out.joint_spec()==joint,out.history()==history,out.positions()==positions,out.key()==key,
            super::production::interpreted(out.joint_spec().events(),out.key()),
    {let out=Self {joint,history:Ghost(history),positions:Ghost(positions),key:Ghost(key)};proof {out.production_trace();}out}
    pub proof fn valid_history(&self)
        requires self.certified(),ensures self.joint_spec().certified(),self.history().valid(),
            self.positions().len()==self.history().states.len(),
            self.history().indexed(self.positions(),self.joint_spec().events(),self.key()),
            self.joint_spec().last().contains_pair(self.key(),joint::Record::Native {state:self.history().states.last().project(self.history().labels.len())}),
    {}
    pub fn joint(&self)->(out:&joint::Snapshot) ensures *out==self.joint_spec(), {&self.joint}
    pub fn into_joint(self)->(out:joint::Snapshot)
        requires self.certified(),ensures out==self.joint_spec(),out.certified(),super::production::interpreted(out.events(),self.key()),
    {proof {self.production_trace();}self.joint}
    proof fn complete_at(&self,n:nat)->(index:int)
        requires self.certified(),n<self.joint_spec().events().len(),
            self.joint_spec().events()[n as int].event.key==self.key(),
        ensures 0<=index<self.history().states.len(),self.positions()[index]==n,
    {
        let frames=self.joint_spec().events();let key=self.key();let positions=self.positions();let h=self.history();
        self.joint.valid_history();
        if n<positions[0] {
            assert(joint::step(joint::state_at(frames,n),frames[n as int].state,frames[n as int].event));
            assert(joint::state_at(frames,n+1).contains_key(key));
            joint::key_persists(frames,n+1,positions[0],key);
            assert(frames[positions[0] as int].event.change==joint::Change::Allocate);
            assert(joint::step(joint::state_at(frames,positions[0]),frames[positions[0] as int].state,frames[positions[0] as int].event));
            assert(false);
        }
        if n==positions[0] {0} else {
            let start=positions[0];
            assert(0<h.states.len());assert(positions[0]<frames.len());
            assert(frames[start as int].event.after==(joint::Record::Native {state:h.states[0].project(0)}));
            assert(joint::step(joint::state_at(frames,start),frames[start as int].state,frames[start as int].event));
            assert(native::recorded(frames,start+1,key));
            native::monotone(frames,start+1,n,key);native::edge(frames,n,key);
            native::monotone(frames,n+1,frames.len(),key);
            assert(native::at(frames,frames.len(),key)==h.states.last().project(h.labels.len()));
            let i=frames[n as int].event.after->Native_state.revision as int;
            assert(0<=i<h.states.len());
            assert(positions[i]<frames.len());
            assert(frames[positions[i] as int].event.after==(joint::Record::Native {state:h.states[i].project(i as nat)}));
            native::unique_revision(frames,n,positions[i],key);
            i
        }
    }
    /// Every mutation of this native owner in the complete checkpoint is an
    /// indexed typed state. Other records may interleave, but none is hidden.
    pub proof fn complete_projection(&self)
        requires self.certified(),
        ensures forall|n:int| 0<=n<self.joint_spec().events().len()
            && #[trigger] self.joint_spec().events()[n].event.key==self.key() ==>
                exists|i:int| 0<=i<self.history().states.len() && self.positions()[i]==n,
    {
        assert forall|n:int| 0<=n<self.joint_spec().events().len()
            && #[trigger] self.joint_spec().events()[n].event.key==self.key() implies
                exists|i:int| 0<=i<self.history().states.len() && self.positions()[i]==n by {
            let i=self.complete_at(n as nat);assert(self.positions()[i]==n);
        }
    }
    /// Unload-free native history keeps the full publication, and every
    /// corresponding joint commit keeps its ports and provider provenance.
    pub proof fn retained_publication(&self,start:int,end:int,id:usize)
        requires self.certified(),0<=start<=end<self.history().states.len(),
            self.history().states[start].publications.contains_key(id),
            forall|i:int| start<=i<end ==> #[trigger] self.history().labels[i]!=(id,r::Rule::Unload),
        ensures self.history().states[end].publications.contains_pair(id,self.history().states[start].publications[id]),
            self.joint_spec().events()[self.positions()[end] as int].event.after->Native_state.publications.contains_pair(
                id,publication(self.history().states[start].publications[id])),
    {self.history().publication_retained(start,end,id);}
}
}
