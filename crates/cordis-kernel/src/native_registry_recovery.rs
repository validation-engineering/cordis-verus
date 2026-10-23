//! Source normalization for the actual native publication and Episode maps.
//! An opening has a unique history position, even when a provider publishes
//! equal payloads again. Unload, rather than visibility, consumes that opening.
use crate::refinement::Rule;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
pub ghost struct Registry<V> {
    pub states:Seq<Map<usize,V>>,
    pub labels:Seq<(usize,Rule)>,
    pub opening:Rule,
}
pub ghost enum Issue {Removed {id:usize,at:int},Introduced {id:usize,at:int}}
pub open spec fn get<V>(values:Map<usize,V>,id:usize)->Option<V> {
    if values.contains_key(id) {Some(values[id])} else {None}
}
impl<V> Registry<V> {
    pub open spec fn transition(&self,i:int)->bool {
        let a=self.states[i];let b=self.states[i+1];let (id,rule)=self.labels[i];
        if rule==self.opening {!a.contains_key(id) && b.contains_key(id) && b==a.insert(id,b[id])}
        else if rule==Rule::Unload {b==a.remove(id)} else {b==a}
    }
    pub open spec fn valid(&self)->bool {
        self.opening!=Rule::Unload && self.states.len()==self.labels.len()+1 && self.states.first().is_empty()
            && forall|i:int|0<=i<self.labels.len() ==> #[trigger] self.transition(i)
    }
    pub open spec fn no_unload(&self,id:usize,start:int,end:int)->bool {
        forall|i:int|start<=i<end ==> #[trigger] self.labels[i]!=(id,Rule::Unload)
    }
    pub open spec fn live_birth(&self,id:usize,at:int,end:int)->bool {
        0<=at<end<self.states.len() && self.labels[at]==(id,self.opening) && self.no_unload(id,at+1,end)
    }
    pub proof fn retained(&self,start:int,end:int,id:usize)
        requires self.valid(),0<=start<=end<self.states.len(),self.states[start].contains_key(id),self.no_unload(id,start,end),
        ensures self.states[end].contains_pair(id,self.states[start][id]),
        decreases end-start,
    {
        if start<end {self.retained(start,end-1,id);assert(self.transition(end-1));}
    }
    /// The current payload comes from the latest unconsumed actual opening.
    pub proof fn source(&self,end:int,id:usize)->(at:int)
        requires self.valid(),0<=end<self.states.len(),self.states[end].contains_key(id),
        ensures self.live_birth(id,at,end),self.states[at+1].contains_pair(id,self.states[end][id]),
        decreases end,
    {
        assert(end>0);let i=end-1;assert(self.transition(i));
        if self.labels[i]==(id,self.opening) {i}
        else {
            assert(self.labels[i]!=(id,Rule::Unload));
            let at=self.source(i,id);
            assert forall|j:int|at+1<=j<end implies #[trigger] self.labels[j]!=(id,Rule::Unload) by {}
            at
        }
    }
    pub proof fn birth_value(&self,id:usize,at:int,end:int)
        requires self.valid(),self.live_birth(id,at,end),
        ensures self.states[end].contains_pair(id,self.states[at+1][id]),
    {assert(self.transition(at));self.retained(at+1,end,id);}
    pub proof fn unique_birth(&self,id:usize,a:int,b:int,end:int)
        requires self.valid(),self.live_birth(id,a,end),self.live_birth(id,b,end),
        ensures a==b,
    {
        if a<b {assert(self.transition(a));self.retained(a+1,b,id);assert(self.transition(b));}
        if b<a {assert(self.transition(b));self.retained(b+1,a,id);assert(self.transition(a));}
    }
    pub open spec fn introduced(&self,start:int,end:int,id:usize)->bool {
        exists|at:int|start<=at<end && #[trigger] self.live_birth(id,at,end)
    }
    pub open spec fn kept(&self,start:int,end:int,id:usize)->bool {
        self.states[start].contains_key(id) && self.no_unload(id,start,end)
    }
    /// This normal form depends on actual openings and their consumption, not
    /// on an expected endpoint map supplied by a caller.
    pub open spec fn reconstructed(&self,start:int,end:int)->Map<usize,V> {
        Map::new(self.states[start].dom().union(self.labels.map(|_:int,label:(usize,Rule)|label.0).to_set())
            .filter(|id:usize|self.kept(start,end,id) || self.introduced(start,end,id)),|id:usize|
            if self.kept(start,end,id) {self.states[start][id]}
            else {let at=choose|at:int|start<=at<end && self.live_birth(id,at,end);self.states[at+1][id]})
    }
    pub proof fn normalize(&self,start:int,end:int)
        requires self.valid(),0<=start<=end<self.states.len(),
        ensures self.states[end]==self.reconstructed(start,end),
            forall|id:usize|self.kept(start,end,id) ==> !#[trigger] self.introduced(start,end,id),
    {
        assert forall|id:usize|self.kept(start,end,id) implies !#[trigger] self.introduced(start,end,id) by {
            if self.introduced(start,end,id) {
                let at=choose|at:int|start<=at<end && self.live_birth(id,at,end);
                self.retained(start,at,id);assert(self.transition(at));
            }
        }
        assert forall|id:usize|self.states[end].contains_key(id) implies
            self.reconstructed(start,end).contains_key(id) by {
            let at=self.source(end,id);
            assert(self.labels.map(|_:int,label:(usize,Rule)|label.0)[at]==id);
            assert(self.labels.map(|_:int,label:(usize,Rule)|label.0).to_set().contains(id));
            if at<start {self.birth_value(id,at,start);}
            else {assert(self.live_birth(id,at,end));}
        }
        assert forall|id:usize|self.reconstructed(start,end).contains_key(id) implies
            self.states[end].contains_pair(id,self.reconstructed(start,end)[id]) by {
            if self.kept(start,end,id) {self.retained(start,end,id);}
            else {let at=choose|at:int|start<=at<end && self.live_birth(id,at,end);self.birth_value(id,at,end);}
        }
        assert(self.states[end] =~= self.reconstructed(start,end));
    }
    pub proof fn recover_map(&self,start:int,end:int,scope:Set<usize>)
        requires self.valid(),0<=start<=end<self.states.len(),self.same_on(start,end,scope),
            self.states[start].dom().subset_of(scope),self.labels.map(|_:int,label:(usize,Rule)|label.0).to_set().subset_of(scope),
        ensures self.states[end]==self.states[start],
    {
        self.normalize(start,end);
        assert forall|id:usize|self.states[end].contains_key(id) || self.states[start].contains_key(id) implies
            get(self.states[end],id)==get(self.states[start],id) by {assert(scope.contains(id));}
        assert(self.states[end] =~= self.states[start]);
    }
    pub proof fn first_unload(&self,start:int,end:int,id:usize)->(at:int)
        requires self.valid(),0<=start<=end<self.states.len(),self.states[start].contains_key(id),!self.no_unload(id,start,end),
        ensures start<=at<end,self.labels[at]==(id,Rule::Unload),self.no_unload(id,start,at),
            self.states[at].contains_pair(id,self.states[start][id]),!self.states[at+1].contains_key(id),
        decreases end-start,
    {
        assert(start<end);assert(self.transition(start));
        if self.labels[start]==(id,Rule::Unload) {start}
        else {
            assert(!self.no_unload(id,start+1,end));
            let at=self.first_unload(start+1,end,id);
            assert forall|i:int|start<=i<at implies #[trigger] self.labels[i]!=(id,Rule::Unload) by {}
            at
        }
    }
    pub open spec fn balanced(&self,start:int,end:int,scope:Set<usize>)->bool {
        forall|id:usize|#[trigger] scope.contains(id) ==>
            (self.states[start].contains_key(id) ==> self.no_unload(id,start,end)) && !self.introduced(start,end,id)
    }
    pub proof fn closed_from_unloads(&self,start:int,end:int,scope:Set<usize>)
        requires self.valid(),0<=start<=end<self.states.len(),
            forall|id:usize|scope.contains(id) && self.states[start].contains_key(id) ==> #[trigger] self.no_unload(id,start,end),
            forall|i:int|start<=i<end && scope.contains(self.labels[i].0) && self.labels[i].1==self.opening ==>
                exists|j:int|i<j<end && #[trigger] self.labels[j]==(self.labels[i].0,Rule::Unload),
        ensures self.balanced(start,end,scope),
    {
        assert forall|id:usize|scope.contains(id) implies !#[trigger] self.introduced(start,end,id) by {
            if self.introduced(start,end,id) {
                let i=choose|i:int|start<=i<end && self.live_birth(id,i,end);
                let j=choose|j:int|i<j<end && self.labels[j]==(id,Rule::Unload);
                assert(self.labels[j]!=(id,Rule::Unload));
            }
        }
    }
    pub open spec fn same_on(&self,start:int,end:int,scope:Set<usize>)->bool {
        forall|id:usize|#[trigger] scope.contains(id) ==> get(self.states[end],id)==get(self.states[start],id)
    }
    pub open spec fn diagnosed(&self,start:int,end:int,scope:Set<usize>,issue:Issue)->bool {
        match issue {
            Issue::Removed {id,at}=>scope.contains(id) && self.states[start].contains_key(id)
                && start<=at<end && self.labels[at]==(id,Rule::Unload) && self.no_unload(id,start,at)
                && self.states[at].contains_pair(id,self.states[start][id]) && !self.states[at+1].contains_key(id),
            Issue::Introduced {id,at}=>scope.contains(id) && start<=at<end && self.live_birth(id,at,end),
        }
    }
    /// A history-based test of exact recovery. It detects source replacement
    /// even if the later value happens to compare equal to the earlier one.
    pub proof fn check(&self,start:int,end:int,scope:Set<usize>)->(issue:Option<Issue>)
        requires self.valid(),0<=start<=end<self.states.len(),
        ensures issue.is_none()==self.balanced(start,end,scope),
            issue.is_none() ==> self.same_on(start,end,scope),
            issue.is_some() ==> self.diagnosed(start,end,scope,issue.unwrap()),
    {
        if exists|id:usize,at:int|scope.contains(id) && self.states[start].contains_key(id)
            && start<=at<end && self.labels[at]==(id,Rule::Unload) {
            let (id,at)=choose|id:usize,at:int|scope.contains(id) && self.states[start].contains_key(id)
                && start<=at<end && self.labels[at]==(id,Rule::Unload);
            assert(!self.no_unload(id,start,end));
            let at=self.first_unload(start,end,id);
            Some(Issue::Removed {id,at})
        } else if exists|id:usize,at:int|scope.contains(id) && start<=at<end && self.live_birth(id,at,end) {
            let (id,at)=choose|id:usize,at:int|scope.contains(id) && start<=at<end && self.live_birth(id,at,end);
            Some(Issue::Introduced {id,at})
        } else {
            self.normalize(start,end);
            assert(self.balanced(start,end,scope));
            assert forall|id:usize|#[trigger] scope.contains(id) implies get(self.states[end],id)==get(self.states[start],id) by {}
            None
        }
    }
}
}
