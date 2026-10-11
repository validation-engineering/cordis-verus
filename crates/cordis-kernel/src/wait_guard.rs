//! Read-only admission for a callback waiting on lifecycle work.
//!
//! The host supplies whether its invocation still holds work open. The kernel
//! checks the exact episode and its committed dependency closure, including an
//! affected provider below the target in the ownership tree. This is not a
//! scheduler or a general RPC wait graph; callback execution remains external.
#[cfg(verus_keep_ghost)]
use crate::Binding;
use crate::Kernel;
use vstd::prelude::*;

verus! {

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum WaitDecision { Allowed, StaleEpisode, Blocked { retained: usize } }

pub open spec fn marked(bits:Seq<bool>,id:usize)->bool {
    id < bits.len() && bits[id as int]
}

impl Kernel {
    /// Service edges only. Parent ownership does not create a dependency.
    pub closed spec fn committed_edge(&self,consumer:usize,provider:usize)->bool {
        exists|b:Binding| self.binding_recorded(consumer,b) && b.provider==provider
    }

    pub open spec fn dependency_closed(&self,ids:ISet<usize>)->bool {
        forall|a:usize,b:usize| ids.contains(a) && self.committed_edge(a,b) ==> ids.contains(b)
    }

    /// Reflexive transitive closure, specified independently of traversal order.
    pub open spec fn committed_reachable(&self,from:usize,target:usize)->bool {
        forall|ids:ISet<usize>| self.dependency_closed(ids) && ids.contains(from) ==> ids.contains(target)
    }

    proof fn reach_self(&self,from:usize)
        ensures self.committed_reachable(from,from),
    { }

    proof fn reach_edge(&self,from:usize,a:usize,b:usize)
        requires self.committed_reachable(from,a),self.committed_edge(a,b),
        ensures self.committed_reachable(from,b),
    {
        assert forall|ids:ISet<usize>| self.dependency_closed(ids) && ids.contains(from) implies ids.contains(b) by {
            assert(ids.contains(a));
        }
    }

    proof fn graph_facts(&self)
        requires self.wf(),
        ensures Self::link_order(self.links@),
            forall|i:int| 0<=i<self.links.len() ==> Self::link_ok(self.nodes@,self.links[i]),
            forall|i:int| 0<=i<self.nodes.len() ==> Self::node_ok(self.nodes@,i),
    {
        reveal(Kernel::wf);reveal(Kernel::safety_wf);
    }

    /// Live commitment positions decrease along dependency paths. A single
    /// reverse pass therefore computes the full closure, without a host graph.
    fn committed_closure(&self,from:usize)->(bits:Vec<bool>)
        requires self.wf(),self.registered(from),
        ensures bits.len()==self.nodes.len(),
            forall|id:usize| marked(bits@,id)==self.committed_reachable(from,id),
    {
        proof { self.graph_facts();reveal(Kernel::registered);self.reach_self(from); }
        let mut bits=Vec::new();let mut i=0;
        while i<self.nodes.len()
            invariant i==bits.len(),i<=self.nodes.len(),
                forall|k:int| 0<=k<i ==> bits[k]==(k==from),
            decreases self.nodes.len()-i,
        {
            bits.push(i==from);i+=1;
        }
        let mut cursor=self.links.len();
        while cursor>0
            invariant self.wf(),self.registered(from),Self::link_order(self.links@),
                forall|k:int| 0<=k<self.links.len() ==> Self::link_ok(self.nodes@,self.links[k]),
                bits.len()==self.nodes.len(),marked(bits@,from),cursor<=self.links.len(),
                forall|id:usize| marked(bits@,id) ==> self.committed_reachable(from,id),
                forall|k:int| cursor<=k<self.links.len() && self.links[k].live
                    && marked(bits@,self.links[k].consumer) ==> marked(bits@,self.links[k].binding.provider),
            decreases cursor,
        {
            cursor-=1;
            let link=self.links[cursor];
            let ghost before=bits@;
            if link.live && bits[link.consumer] {
                proof {
                    reveal(Kernel::committed_edge);reveal(Kernel::binding_recorded);
                    assert(self.binding_recorded(link.consumer,link.binding));
                    assert(self.committed_edge(link.consumer,link.binding.provider));
                    self.reach_edge(from,link.consumer,link.binding.provider);
                }
                bits.set(link.binding.provider,true);
            }
            proof {
                assert forall|k:int| cursor<=k<self.links.len() && self.links[k].live
                    && marked(bits@,self.links[k].consumer) implies marked(bits@,self.links[k].binding.provider) by {
                    if k>cursor && !marked(before,self.links[k].consumer) {
                        assert(link.live && self.links[k].consumer==link.binding.provider);
                        assert(k<cursor);
                    }
                }
            }
        }
        proof {
            let ids=ISet::new(|id:usize| marked(bits@,id));
            assert(self.dependency_closed(ids)) by {
                assert forall|a:usize,b:usize| ids.contains(a) && self.committed_edge(a,b) implies ids.contains(b) by {
                    reveal(Kernel::committed_edge);reveal(Kernel::binding_recorded);
                    let binding=choose|binding:Binding| self.binding_recorded(a,binding) && binding.provider==b;
                    let k=choose|k:int| 0<=k<self.links.len() && self.links[k].live
                        && self.links[k].consumer==a && self.links[k].binding==binding;
                    assert(marked(bits@,self.links[k].binding.provider));
                }
            }
            assert forall|id:usize| marked(bits@,id)==self.committed_reachable(from,id) by {
                if self.committed_reachable(from,id) { assert(ids.contains(id)); }
            }
        }
        bits
    }

    /// A stale episode cannot obtain a dependency answer, even when its new
    /// episode happens to resolve to the same providers.
    pub fn committed_reaches(&self,from:usize,generation:u64,target:usize)->(out:Option<bool>)
        requires self.wf(),
        ensures out.is_some()==(self.generation_of(from)==Some(generation)),
            out.is_some() ==> out.unwrap()==self.committed_reachable(from,target),
    {
        if self.episode_generation(from)!=Some(generation) {return None;}
        proof { reveal(Kernel::generation_of); }
        let bits=self.committed_closure(from);
        Some(target<bits.len() && bits[target])
    }

    /// A subtree relation, separate from service reachability.
    pub closed spec fn owned_by(&self,node:usize,ancestor:usize)->bool
        decreases node,
    {
        self.registered(node) && (node==ancestor || match self.nodes[node as int].parent {
            Some(parent) => parent<node && self.owned_by(parent,ancestor),
            None => false,
        })
    }

    fn is_owned_by(&self,node:usize,ancestor:usize)->(found:bool)
        requires self.wf(),
        ensures found==self.owned_by(node,ancestor),
    {
        proof {self.graph_facts();}
        if !self.contains(node) {return false;}
        let mut current=node;
        loop
            invariant self.registered(current),current<=node,
                forall|k:int| 0<=k<self.nodes.len() ==> Self::node_ok(self.nodes@,k),
                self.owned_by(node,ancestor)==self.owned_by(current,ancestor),
            decreases current,
        {
            if current==ancestor {return true;}
            proof {
                reveal(Kernel::registered);
                assert(Self::node_ok(self.nodes@,current as int));
            }
            match self.nodes[current].parent {
                Some(parent)=>{current=parent;},
                None=>{return false;},
            }
        }
    }

    pub open spec fn wait_conflict(&self,from:usize,target:usize)->bool {
        exists|provider:usize| self.committed_reachable(from,provider) && self.owned_by(provider,target)
    }

    /// Exact admission relative to the host's live-invocation fact. Rejection
    /// returns an actual retained member of the target subtree. This operation
    /// borrows the kernel immutably and cannot retire or release anything.
    pub fn check_wait(&self,from:usize,generation:u64,target:usize,holding:bool)->(out:WaitDecision)
        requires self.wf(),
        ensures
            (out==WaitDecision::StaleEpisode)==(self.generation_of(from)!=Some(generation)),
            (out==WaitDecision::Allowed)==(self.generation_of(from)==Some(generation)
                && (!holding || !self.wait_conflict(from,target))),
            match out {
                WaitDecision::Blocked {retained}=> self.generation_of(from)==Some(generation) && holding
                    && self.committed_reachable(from,retained) && self.owned_by(retained,target),
                _=>true,
            },
    {
        if self.episode_generation(from)!=Some(generation) {return WaitDecision::StaleEpisode;}
        if !holding {return WaitDecision::Allowed;}
        if self.is_owned_by(from,target) {
            proof {self.reach_self(from);}
            return WaitDecision::Blocked {retained:from};
        }
        proof {reveal(Kernel::generation_of);}
        let bits=self.committed_closure(from);
        let mut i=0;
        while i<bits.len()
            invariant self.wf(),self.generation_of(from)==Some(generation),holding,
                i<=bits.len(),bits.len()==self.nodes.len(),
                forall|id:usize| marked(bits@,id)==self.committed_reachable(from,id),
                forall|k:usize| k<i ==> !(self.committed_reachable(from,k) && self.owned_by(k,target)),
            decreases bits.len()-i,
        {
            if bits[i] && self.is_owned_by(i,target) {return WaitDecision::Blocked {retained:i};}
            i+=1;
        }
        proof {
            assert(!self.wait_conflict(from,target)) by {
                if self.wait_conflict(from,target) {
                    let p=choose|p:usize| self.committed_reachable(from,p) && self.owned_by(p,target);
                    assert(marked(bits@,p));
                }
            }
        }
        WaitDecision::Allowed
    }

    /// A non-reflexive dependency path ends in an actual live commitment.
    /// The ordinary lifecycle cleanup guard therefore cannot release its target.
    pub proof fn retained_dependency_blocks_cleanup(&self,from:usize,target:usize)
        requires self.wf(),from!=target,self.committed_reachable(from,target),
        ensures !self.cleanup_enabled(target),
    {
        if !(exists|a:usize| self.committed_reachable(from,a) && self.committed_edge(a,target)) {
            let ids=ISet::new(|id:usize| id!=target && self.committed_reachable(from,id));
            self.reach_self(from);
            assert(self.dependency_closed(ids)) by {
                assert forall|a:usize,b:usize| ids.contains(a) && self.committed_edge(a,b) implies ids.contains(b) by {
                    self.reach_edge(from,a,b);
                }
            }
            assert(ids.contains(from));
            assert(ids.contains(target));
        }
        let a=choose|a:usize| self.committed_reachable(from,a) && self.committed_edge(a,target);
        reveal(Kernel::committed_edge);reveal(Kernel::binding_recorded);reveal(Kernel::cleanup_enabled);
        let b=choose|b:Binding| self.binding_recorded(a,b) && b.provider==target;
        let k=choose|k:int| 0<=k<self.links.len() && self.links[k].live
            && self.links[k].consumer==a && self.links[k].binding==b;
    }

    /// In particular, a live callback cannot wait on its own ancestor.
    pub proof fn own_ancestor_conflicts(&self,from:usize,target:usize)
        requires self.owned_by(from,target),
        ensures self.wait_conflict(from,target),
    {
        self.reach_self(from);
        assert(self.committed_reachable(from,from) && self.owned_by(from,target));
    }
}

} // verus!
