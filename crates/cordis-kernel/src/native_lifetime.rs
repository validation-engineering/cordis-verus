//! Allocation freshness and terminal Child state in the actual typed history.
//! The bound comes from the executable Kernel's monotonically growing IDs.
#[cfg(verus_keep_ghost)]
use super::Observation;
use super::{History, Snapshot};
#[cfg(verus_keep_ghost)]
use crate::{refinement as r, reversible_value::joint, Phase};
use vstd::prelude::*;

verus! {
impl<V> History<V> {
    #[verifier::opaque]
    pub open spec fn allocated_below(&self,limit:nat)->bool {
        forall|i:int,id:usize|0<=i<self.states.len() && #[trigger] r::registered(self.states[i].control,id) ==> id<limit
    }
    #[verifier::opaque]
    pub open spec fn fresh_insertions(&self)->bool {
        forall|i:int,j:int|0<=i<=j<self.labels.len() && self.labels[j].1==r::Rule::Insert ==>
            !(#[trigger] r::registered(self.states[i].control,self.labels[j].0))
    }
    pub proof fn initial_allocation(&self,limit:nat)
        requires self.valid(),self.labels.len()==0,
        ensures self.allocated_below(limit),self.fresh_insertions(),
    {reveal(History::allocated_below);reveal(History::fresh_insertions);}

    pub proof fn raise_allocation_bound(&self,before:nat,after:nat)
        requires self.allocated_below(before),before<=after,
        ensures self.allocated_below(after),
    {reveal(History::allocated_below);}

    pub proof fn append_allocation(&self,state:Observation<V>,actor:usize,rule:r::Rule,before:nat,after:nat)
        requires self.valid(),self.allocated_below(before),self.fresh_insertions(),before<=after,
            rule==r::Rule::Insert ==> before<=actor,
            forall|id:usize|r::registered(state.control,id) ==> id<after,
        ensures self.append(state,actor,rule).allocated_below(after),self.append(state,actor,rule).fresh_insertions(),
    {
        reveal(History::allocated_below);reveal(History::fresh_insertions);
        let next=self.append(state,actor,rule);
        assert forall|i:int,id:usize|0<=i<next.states.len() && #[trigger] r::registered(next.states[i].control,id) implies id<after by {
            if i<self.states.len() {assert(next.states[i]==self.states[i]);}
            else {assert(next.states[i]==state);}
        }
        assert forall|i:int,j:int|0<=i<=j<next.labels.len() && next.labels[j].1==r::Rule::Insert implies
            !(#[trigger] r::registered(next.states[i].control,next.labels[j].0)) by {
            if j<self.labels.len() {assert(next.labels[j]==self.labels[j]);assert(next.states[i]==self.states[i]);}
            else {assert(next.labels[j]==(actor,rule));assert(next.states[i]==self.states[i]);}
        }
    }

    /// No later Insert can reuse an identity that was registered at this cut.
    pub proof fn no_rebirth(&self,born:int,later:int,id:usize)
        requires self.valid(),self.fresh_insertions(),0<=born<=later<self.labels.len(),
            r::registered(self.states[born].control,id),
        ensures self.labels[later]!=(id,r::Rule::Insert),
    {
        reveal(History::fresh_insertions);
        if self.labels[later]==(id,r::Rule::Insert) {
            assert(!r::registered(self.states[born].control,self.labels[later].0));
        }
    }

    pub proof fn transition_at(&self,index:int)
        requires self.valid(),0<=index<self.labels.len(),
        ensures super::step(self.states[index],self.states[index+1],self.labels[index].0,self.labels[index].1),
    {reveal(History::valid);}

    pub proof fn terminal_retained(&self,born:int,start:int,end:int,id:usize)
        requires self.valid(),self.fresh_insertions(),0<=born<=start<=end<self.states.len(),
            r::registered(self.states[born].control,id),terminal(self.states[start],id),
        ensures terminal(self.states[end],id),
        decreases end-start,
    {
        hide(super::step);
        if start<end {
            self.terminal_retained(born,start,end-1,id);
            self.no_rebirth(born,end-1,id);
            assert(0<=end-1<self.labels.len());
            self.transition_at(end-1);
            terminal_step(self.states[end-1],self.states[end],self.labels[end-1].0,self.labels[end-1].1,id);
        }
    }
}
pub open spec fn terminal<V>(state:Observation<V>,id:usize)->bool {
    !state.owners.contains_key(id) && !state.publications.contains_key(id)
        && (r::registered(state.control,id) ==> state.control.fibers[id].retired && state.control.fibers[id].phase==Phase::Inactive)
}
pub proof fn terminal_step<V>(before:Observation<V>,after:Observation<V>,actor:usize,rule:r::Rule,id:usize)
    requires super::step(before,after,actor,rule),terminal(before,id),actor!=id || rule!=r::Rule::Insert,
    ensures terminal(after,id),
{
    if actor==id {match rule {
        r::Rule::Begin=>{assert(!r::target(before.control,id,after.control.fibers[id].committed));},
        _=>{},
    }}
}

impl<V> Snapshot<V> {
    /// Locate a covered authentic native receipt in the complete typed history.
    pub proof fn source_index(&self,receipt:&joint::Receipt)->(index:int)
        requires self.certified(),receipt.wf(),self.joint_spec().covers(receipt),
            receipt.event().key==self.key(),receipt.event().after is Native,
        ensures 0<=index<self.history().states.len(),self.positions()[index]==receipt.at(),
            self.history().states[index].project(index as nat)==receipt.event().after->Native_state,
    {
        self.valid_history();let frames=self.joint_spec().events();
        assert(frames[receipt.at() as int]==receipt.events()[receipt.at() as int]);
        self.complete_at(receipt.at())
    }
    pub proof fn source_order(&self,earlier:&joint::Receipt,later:&joint::Receipt,a:int,b:int)
        requires self.certified(),earlier.wf(),later.wf(),later.covers(earlier),
            0<=a<self.history().states.len(),0<=b<self.history().states.len(),
            self.positions()[a]==earlier.at(),self.positions()[b]==later.at(),
        ensures a<=b,
    {self.valid_history();if b<a {assert(self.positions()[b]<self.positions()[a]);}}
}
}
