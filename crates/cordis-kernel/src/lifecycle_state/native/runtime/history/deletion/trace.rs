//! Splice one selected native episode window into the complete actual history.
//! Prefix/suffix episodes stay intact; source positions retain Joint provenance.
#[cfg(verus_keep_ghost)]
use super::super::Observation;
use super::super::{History, Snapshot};
use super::Region;
#[cfg(verus_keep_ghost)]
use super::{boundary, boundary_identity, closed, project, transport};
#[cfg(verus_keep_ghost)]
use crate::{refinement as r, reversible_value::joint};
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub ghost struct Window {pub start:int,pub end:int,pub region:Region}
pub ghost enum Issue {Range,Region,Opening,Closing,Birth {index:int,child:usize,parent:usize},Parent {index:int,child:usize},Consumer {index:int,consumer:usize,provider:usize}}
impl Window {
    pub open spec fn bounds<V>(self,h:History<V>)->bool {0<=self.start<=self.end<h.states.len()}
    pub open spec fn births_closed<V>(self,h:History<V>)->bool {
        forall|i:int|self.start<=i<self.end && h.labels[i].1==r::Rule::Insert
            && h.states[i+1].control.fibers[h.labels[i].0].parent.is_some()
            && self.region.episodes.contains(h.states[i+1].control.fibers[h.labels[i].0].parent.unwrap())
            ==> self.region.born.contains(h.labels[i].0)
    }
    pub open spec fn admissible<V>(self,h:History<V>)->bool {
        self.bounds(h) && self.region.wf() && self.births_closed(h) && boundary(h.states[self.start],self.region) && boundary(h.states[self.end],self.region)
            && forall|i:int|self.start<=i<=self.end ==> closed(h.states[i].control,self.region)
    }
    pub open spec fn keep(self,i:int,label:(usize,r::Rule))->bool {
        i<self.start || self.end<=i || self.region.keep(label.0,label.1)
    }
    pub open spec fn at<V>(self,h:History<V>,i:int)->Observation<V> {
        if self.start<=i<=self.end {project(h.states[i],self.region)} else {h.states[i]}
    }
    pub open spec fn diagnosed<V>(self,h:History<V>,issue:Issue)->bool {
        match issue {
            Issue::Range=>!self.bounds(h),Issue::Region=>!self.region.wf(),
            Issue::Opening=>self.bounds(h) && !boundary(h.states[self.start],self.region),
            Issue::Closing=>self.bounds(h) && !boundary(h.states[self.end],self.region),
            Issue::Birth {index,child,parent}=>self.start<=index<self.end && 0<=index<h.labels.len()
                && h.labels[index]==(child,r::Rule::Insert) && h.states[index+1].control.fibers[child].parent==Some(parent)
                && self.region.episodes.contains(parent) && !self.region.born.contains(child),
            Issue::Parent {index,child}=>self.start<=index<=self.end && 0<=index<h.states.len()
                && r::registered(h.states[index].control,child) && !self.region.born.contains(child)
                && h.states[index].control.fibers[child].parent.is_some()
                && self.region.born.contains(h.states[index].control.fibers[child].parent.unwrap()),
            Issue::Consumer {index,consumer,provider}=>self.start<=index<=self.end && 0<=index<h.states.len()
                && r::registered(h.states[index].control,consumer) && r::registered(h.states[index].control,provider)
                && !self.region.episodes.contains(consumer) && self.region.episodes.contains(provider)
                && !h.states[index].control.fibers[consumer].dependencies.disjoint(h.states[index].control.fibers[provider].provisions),
        }
    }
    pub proof fn check<V>(self,h:History<V>)->(issue:Option<Issue>)
        requires h.valid(),
        ensures issue.is_none()==self.admissible(h),issue.is_some() ==> self.diagnosed(h,issue.unwrap()),
    {
        if !self.bounds(h) {return Some(Issue::Range);}
        if !self.region.wf() {return Some(Issue::Region);}
        if !boundary(h.states[self.start],self.region) {return Some(Issue::Opening);}
        if !boundary(h.states[self.end],self.region) {return Some(Issue::Closing);}
        if exists|i:int|self.start<=i<=self.end && !closed(h.states[i].control,self.region) {
            let i=choose|i:int|self.start<=i<=self.end && !closed(h.states[i].control,self.region);
            let a=h.states[i].control;
            if exists|n:usize|r::registered(a,n) && !self.region.born.contains(n) && a.fibers[n].parent.is_some() && self.region.born.contains(a.fibers[n].parent.unwrap()) {
                let n=choose|n:usize|r::registered(a,n) && !self.region.born.contains(n) && a.fibers[n].parent.is_some() && self.region.born.contains(a.fibers[n].parent.unwrap());
                return Some(Issue::Parent {index:i,child:n});
            }
            let (n,m)=choose|n:usize,m:usize|r::registered(a,n) && r::registered(a,m) && !self.region.episodes.contains(n) && self.region.episodes.contains(m)
                && !a.fibers[n].dependencies.disjoint(a.fibers[m].provisions);
            return Some(Issue::Consumer {index:i,consumer:n,provider:m});
        }
        if !self.births_closed(h) {
            let i=choose|i:int|self.start<=i<self.end && h.labels[i].1==r::Rule::Insert
                && h.states[i+1].control.fibers[h.labels[i].0].parent.is_some()
                && self.region.episodes.contains(h.states[i+1].control.fibers[h.labels[i].0].parent.unwrap())
                && !self.region.born.contains(h.labels[i].0);
            return Some(Issue::Birth {index:i,child:h.labels[i].0,parent:h.states[i+1].control.fibers[h.labels[i].0].parent.unwrap()});
        }
        assert(self.admissible(h));
        None
    }
    pub proof fn edge<V>(self,h:History<V>,i:int)
        requires h.valid(),self.admissible(h),0<=i<h.labels.len(),
        ensures self.keep(i,h.labels[i]) ==> super::super::step(self.at(h,i),self.at(h,i+1),h.labels[i].0,h.labels[i].1),
            !self.keep(i,h.labels[i]) ==> self.at(h,i)==self.at(h,i+1),
    {
        if self.start<=i<self.end {
            transport(h.states[i],h.states[i+1],h.labels[i].0,h.labels[i].1,self.region);
        } else {
            if i+1==self.start {boundary_identity(h.states[self.start],self.region);}
            if i==self.end {boundary_identity(h.states[self.end],self.region);}
        }
        assert(self.keep(i,h.labels[i]) ==> super::super::step(self.at(h,i),self.at(h,i+1),h.labels[i].0,h.labels[i].1));
    }
    pub open spec fn positions<V>(self,h:History<V>,n:nat)->Seq<int>
        decreases n,
    {if n==0 {Seq::empty()} else {
        let before=self.positions(h,(n-1) as nat);let i=n as int-1;
        if self.keep(i,h.labels[i]) {before.push(i)} else {before}
    }}
    pub open spec fn prefix<V>(self,h:History<V>,n:nat)->History<V>
        decreases n,
    {if n==0 {History {states:seq![self.at(h,0)],labels:Seq::empty()}} else {
        let before=self.prefix(h,(n-1) as nat);let i=n as int-1;
        if self.keep(i,h.labels[i]) {before.append(self.at(h,n as int),h.labels[i].0,h.labels[i].1)} else {before}
    }}
    pub open spec fn target<V>(self,h:History<V>)->History<V> {self.prefix(h,h.labels.len())}
    /// The source step list also serves as the unique provenance map. No
    /// retained Birth/Begin/Finish/Unload can be fabricated by the constructor.
    #[verifier::spinoff_prover]
    pub proof fn construct<V>(self,h:History<V>,n:nat)
        requires h.valid(),self.admissible(h),n<=h.labels.len(),
        ensures self.prefix(h,n).valid(),self.prefix(h,n).states.first()==h.states.first(),
            self.prefix(h,n).states.last()==self.at(h,n as int),
            self.prefix(h,n).labels.len()==self.positions(h,n).len(),
            forall|k:int|#![trigger self.positions(h,n)[k]] 0<=k<self.positions(h,n).len() ==> {
                let i=self.positions(h,n)[k];
                &&& 0<=i<n && self.keep(i,h.labels[i])
                &&& self.prefix(h,n).labels[k]==h.labels[i]
                &&& self.prefix(h,n).states[k]==self.at(h,i)
                &&& self.prefix(h,n).states[k+1]==self.at(h,i+1)
            },
        decreases n,
    {
        if n==0 {
            if self.start==0 {boundary_identity(h.states[0],self.region);}
        } else {
            self.construct(h,(n-1) as nat);let i=n as int-1;self.edge(h,i);
            let before=self.prefix(h,(n-1) as nat);let out=self.prefix(h,n);
            if self.keep(i,h.labels[i]) {before.extended(self.at(h,n as int),h.labels[i].0,h.labels[i].1);}
            assert forall|k:int|#![trigger self.positions(h,n)[k]] 0<=k<self.positions(h,n).len() implies {
                let j=self.positions(h,n)[k];
                &&& 0<=j<n && self.keep(j,h.labels[j])
                &&& out.labels[k]==h.labels[j]
                &&& out.states[k]==self.at(h,j)
                &&& out.states[k+1]==self.at(h,j+1)
            } by {
                if k<self.positions(h,(n-1) as nat).len() {assert(self.positions(h,n)[k]==self.positions(h,(n-1) as nat)[k]);}
                else {assert(k==before.labels.len());assert(self.positions(h,n)[k]==i);}
            }
        }
    }
    pub proof fn selected_position<V>(self,h:History<V>,n:nat,i:int)
        requires n<=h.labels.len(),0<=i<n,self.keep(i,h.labels[i]),
        ensures self.positions(h,i as nat).len()<self.positions(h,n).len(),
            self.positions(h,n)[self.positions(h,i as nat).len() as int]==i,
        decreases n,
    {
        if i<n-1 {self.selected_position(h,(n-1) as nat,i);}
    }
    pub proof fn ordered<V>(self,h:History<V>,n:nat)
        requires n<=h.labels.len(),
        ensures forall|a:int,b:int|0<=a<b<self.positions(h,n).len() ==> self.positions(h,n)[a]<self.positions(h,n)[b],
            forall|a:int|#![trigger self.positions(h,n)[a]] 0<=a<self.positions(h,n).len() ==> 0<=self.positions(h,n)[a]<n,
        decreases n,
    {
        if n>0 {
            self.ordered(h,(n-1) as nat);let before=self.positions(h,(n-1) as nat);let out=self.positions(h,n);
            assert forall|a:int|#![trigger out[a]] 0<=a<out.len() implies 0<=out[a]<n by {
                if a<before.len() {assert(out[a]==before[a]);} else {assert(a==before.len());}
            }
            assert forall|a:int,b:int|0<=a<b<out.len() implies out[a]<out[b] by {
                if b<before.len() {assert(out[a]==before[a]);assert(out[b]==before[b]);}
                else {assert(b==before.len());assert(out[a]==before[a]);}
            }
        }
    }
    /// Both the earlier and the later episodes of the same provider survive.
    pub proof fn unchanged_outside<V>(self,h:History<V>,i:int)
        requires h.valid(),self.admissible(h),0<=i<h.labels.len(),i<self.start || self.end<=i,
        ensures {
            let k=self.positions(h,i as nat).len() as int;let out=self.target(h);
            &&& 0<=k<out.labels.len() && out.labels[k]==h.labels[i]
            &&& out.states[k]==h.states[i] && out.states[k+1]==h.states[i+1]
        },
    {
        self.construct(h,h.labels.len());self.selected_position(h,h.labels.len(),i);
        if i+1==self.start {boundary_identity(h.states[self.start],self.region);}
        if i==self.end {boundary_identity(h.states[self.end],self.region);}
    }
    /// Source freshness survives the splice: the target cannot reuse a Child
    /// identity that was already allocated in a retained earlier episode.
    pub proof fn fresh<V>(self,h:History<V>)
        requires h.valid(),h.fresh_insertions(),self.admissible(h),
        ensures self.target(h).fresh_insertions(),
    {
        self.construct(h,h.labels.len());self.ordered(h,h.labels.len());
        reveal(History::fresh_insertions);let out=self.target(h);let positions=self.positions(h,h.labels.len());
        assert forall|i:int,j:int|0<=i<=j<out.labels.len() && out.labels[j].1==r::Rule::Insert implies
            !(#[trigger] r::registered(out.states[i].control,out.labels[j].0)) by {
            let a=positions[i];let b=positions[j];
            assert(a<=b);assert(h.labels[b]==out.labels[j]);
            assert(!r::registered(h.states[a].control,h.labels[b].0));
        }
    }
    /// Constructive finite native recovery: source guards imply legality and
    /// exact final publication/owner/control equality after the interior splice.
    pub proof fn delete<V>(self,h:History<V>)->(out:History<V>)
        requires h.valid(),self.admissible(h),
        ensures out==self.target(h),out.valid(),out.states.first()==h.states.first(),out.states.last()==h.states.last(),
            h.base_only() ==> out.base_only(),
            r::execution(out.controls(),out.labels,true),
            out.base_only() ==> r::execution(out.controls(),out.labels,false),
    {
        self.construct(h,h.labels.len());
        if self.end==h.labels.len() {boundary_identity(h.states[self.end],self.region);}
        let out=self.target(h);
        assert forall|k:int|0<=k<out.labels.len() && h.base_only() implies #[trigger] out.labels[k].1!=r::Rule::Restart by {
            let i=self.positions(h,h.labels.len())[k];assert(out.labels[k]==h.labels[i]);
        }
        out.correspondence();out
    }
}
impl<V> Snapshot<V> {
    /// Read-only query over the certified production snapshot. Failure reports
    /// a source obstruction; it never asks the caller for a legal target trace.
    pub proof fn delete_window(&self,window:Window)->(out:Result<History<V>,Issue>)
        requires self.certified(),
        ensures out.is_ok()==window.admissible(self.history()),
            out.is_ok() ==> out->Ok_0==window.target(self.history()) && out->Ok_0.valid() && out->Ok_0.fresh_insertions()
                && out->Ok_0.states.first()==self.history().states.first() && out->Ok_0.states.last()==self.history().states.last()
                && r::execution(out->Ok_0.controls(),out->Ok_0.labels,true)
                && (self.history().base_only() ==> out->Ok_0.base_only() && r::execution(out->Ok_0.controls(),out->Ok_0.labels,false)),
            out.is_err() ==> window.diagnosed(self.history(),out->Err_0),
    {
        self.valid_history();let issue=window.check(self.history());
        match issue {Some(issue)=>Err(issue),None=>{window.fresh(self.history());Ok(window.delete(self.history()))}}
    }
    /// Select the opening cut from an authentic invocation Begin; later Child
    /// cleanup/removal may extend the interval past the parent's own Unload.
    pub proof fn delete_since_begin(&self,begin:&super::super::super::episode::Begin,region:Region)->(out:(Window,Result<History<V>,Issue>))
        requires self.certified(),begin.wf(),self.key()==begin.native(),self.joint_spec().covers(&begin.checkpoint()),
        ensures out.0.region==region,out.0.end==self.history().labels.len(),
            0<=out.0.start<self.history().labels.len(),self.history().labels[out.0.start]==(begin.owner().origin.id,r::Rule::Begin),
            self.positions()[out.0.start+1]==begin.at(),
            out.1.is_ok()==out.0.admissible(self.history()),
            out.1.is_ok() ==> out.1->Ok_0==out.0.target(self.history()) && out.1->Ok_0.valid() && out.1->Ok_0.fresh_insertions()
                && out.1->Ok_0.states.last()==self.history().states.last(),
            out.1.is_err() ==> out.0.diagnosed(self.history(),out.1->Err_0),
    {
        self.valid_history();begin.facts();
        assert(self.joint_spec().events()[begin.at() as int]==begin.checkpoint().events()[begin.at() as int]);
        let index=self.complete_at(begin.at());
        assert(index>0);
        let window=Window {start:index-1,end:self.history().labels.len() as int,region};
        (window,self.delete_window(window))
    }
    pub open spec fn deletion_commit(&self,window:Window,k:int)->nat {
        self.positions()[window.positions(self.history(),self.history().labels.len())[k]+1]
    }
    /// Retained commits cannot be duplicated or reordered by the constructor.
    pub proof fn deletion_order(&self,window:Window)
        requires self.certified(),window.admissible(self.history()),
        ensures forall|a:int,b:int|0<=a<b<window.target(self.history()).labels.len() ==>
            #[trigger] self.deletion_commit(window,a)<#[trigger] self.deletion_commit(window,b),
    {
        self.valid_history();window.construct(self.history(),self.history().labels.len());window.ordered(self.history(),self.history().labels.len());
        assert forall|a:int,b:int|0<=a<b<window.target(self.history()).labels.len() implies
            #[trigger] self.deletion_commit(window,a)<#[trigger] self.deletion_commit(window,b) by {
            let indices=window.positions(self.history(),self.history().labels.len());
            assert(0<=indices[a]+1<indices[b]+1<self.positions().len());
        }
    }
    /// Each retained label is tied back to its original actual Joint commit;
    /// source commits are ordered and distinct even after episode deletion.
    pub proof fn deletion_source(&self,window:Window,k:int)->(at:nat)
        requires self.certified(),window.admissible(self.history()),0<=k<window.target(self.history()).labels.len(),
        ensures at<self.joint_spec().events().len(),at==self.positions()[window.positions(self.history(),self.history().labels.len())[k]+1],
            self.joint_spec().events()[at as int].event.key==self.key(),
            self.joint_spec().events()[at as int].event.change==(joint::Change::Native {
                actor:window.target(self.history()).labels[k].0,rule:window.target(self.history()).labels[k].1}),
    {
        self.valid_history();window.construct(self.history(),self.history().labels.len());
        let i=window.positions(self.history(),self.history().labels.len())[k];self.positions()[i+1]
    }
}
pub struct Capture<V> {pub cut:Snapshot<V>,pub deletion:Ghost<Result<History<V>,Issue>>}
}
