//! Owning driver for strict child-retirement inverses.
//!
//! A child referenced by any actual journal cannot be removed. Kernel and
//! episode handles never escape, so checked generations cannot be bypassed and
//! a new activation cannot discard an earlier activation's inverse accumulator.
use crate::ownership::{ChildEpisode, ChildError};
#[cfg(verus_keep_ghost)]
use crate::{child_history, ownership, refinement as paper, semantics, Binding};
use crate::{Error, Kernel, Phase, Port};
use vstd::prelude::*;

verus! {

#[derive(Copy, Clone, Debug, PartialEq, Eq, Structural)]
pub enum ChildDriverError { Kernel(Error), Episode(ChildError), Pending, Retained }

pub struct ChildDriver { kernel: Kernel, episodes: Vec<ChildEpisode> }
impl Default for ChildDriver { fn default() -> Self { Self::new() } }

/// In this concrete interpreter each inverse token is exactly its child ID.
pub open spec fn token_kind(token:nat) -> Option<usize> {
    if token <= usize::MAX {Some(token as usize)} else {None}
}

pub open spec fn retained(s: paper::State, e: &ChildEpisode) -> bool {
    forall|j:int| 0 <= j < e.children().len() ==> paper::registered(s,e.children()[j])
}
pub open spec fn profile(a:paper::State,z:paper::State,n:usize) -> bool {
    paper::registered(a,n) == paper::registered(z,n)
        && (paper::registered(a,n) ==> a.fibers[n].phase == z.fibers[n].phase
            && a.fibers[n].committed == z.fibers[n].committed)
}

/// One externally visible child landing: a coherent stage stays Loading;
/// target loss lands the child and its inverse directly in Unloading.
pub open spec fn child_landing(a:paper::State,z:paper::State,parent:usize,child:usize) -> bool {
    exists|middle:paper::State| ownership::child_effect(a,middle,parent,child)
        && (paper::coherent(a,parent) && z == middle
            || !paper::coherent(a,parent) && paper::step(middle,z,parent,paper::Rule::Divert))
}

pub proof fn child_target_unchanged(a:paper::State,z:paper::State,parent:usize,child:usize)
    requires ownership::child_effect(a,z,parent,child),
    ensures paper::coherent(a,parent) == paper::coherent(z,parent),
{
    assert(parent != child);
    assert(a.fibers[parent] == z.fibers[parent]);
    assert forall|p:Port,n:usize| paper::publishes(a,p,n) == paper::publishes(z,p,n) by {
        if n != child {
            assert(paper::registered(a,n) == paper::registered(z,n));
            if paper::registered(a,n) {assert(a.fibers[n] == z.fibers[n]);}
        }
    }
}

impl ChildDriver {
    pub closed spec fn control(&self) -> paper::State { self.kernel.paper() }
    pub closed spec fn generation(&self,id:usize) -> Option<u64> {self.kernel.generation_of(id)}
    pub closed spec fn journal(&self,id:usize) -> Seq<usize> { self.episodes[id as int].children() }
    pub closed spec fn pending(&self,id:usize) -> bool { self.episodes[id as int].pending() }
    pub open spec fn good(s:paper::State,e:&ChildEpisode,id:usize) -> bool {
        &&& e.wf() && e.owner() == id
        &&& (!paper::registered(s,id) || s.fibers[id].phase == Phase::Inactive
            ==> e.children().len() == 0 && !e.pending())
        &&& (paper::registered(s,id) && s.fibers[id].phase == Phase::Active ==> e.settled() && !e.pending())
        &&& (paper::registered(s,id) && s.fibers[id].phase != Phase::Inactive
            ==> s.fibers[id].committed == ISet::new(|b:Binding| e.committed().contains(b)))
    }
    pub closed spec fn wf(&self) -> bool {
        &&& self.kernel.wf() && self.episodes.len() == self.kernel.next_id()
        &&& forall|i:int| 0 <= i < self.episodes.len() ==> Self::good(self.control(),&self.episodes[i],i as usize)
            && retained(self.control(),&self.episodes[i])
    }
    /// Projection used for the strict child-reference policy. Tables and
    /// iterator identities are erased here; the accumulators are mapped from
    /// the real executable journals, not from separate ghost birth metadata.
    pub closed spec fn retention_snapshot(&self) -> semantics::State<()> {
        semantics::State {
            control:self.control(),
            tables:IMap::new(|n:usize| paper::registered(self.control(),n),|_:usize| IMap::empty()),
            effects:IMap::new(|n:usize| paper::registered(self.control(),n),|_:usize| 0nat),
            iterators:IMap::new(|n:usize| paper::registered(self.control(),n),|n:usize|
                if self.control().fibers[n].phase == Phase::Loading {Some(0nat)} else {None}),
            accumulators:IMap::new(|n:usize| paper::registered(self.control(),n),|n:usize|
                Seq::new(self.journal(n).len(),|i:int| self.journal(n)[i] as nat)),
        }
    }

    pub proof fn refines_retention(&self)
        requires self.wf(),
        ensures child_history::retained(|token:nat| token_kind(token),self.retention_snapshot()),
    {
        let a = self.retention_snapshot();
        assert forall|owner:usize,token:nat,child:usize| semantics::registered(a,owner)
            && a.accumulators[owner].contains(token) && token_kind(token) == Some(child)
            implies semantics::registered(a,child) by {
            self.kernel.paper_observations(owner);
            let i = choose|i:int| 0 <= i < a.accumulators[owner].len() && a.accumulators[owner][i] == token;
            assert(self.journal(owner)[i] == child);
            assert(retained(self.control(),&self.episodes[owner as int]));
        }
    }

    proof fn removal_refines(&self,child:usize)
        requires self.wf(),!self.referenced(child),
        ensures child_history::remove_unreferenced(|token:nat| token_kind(token),self.retention_snapshot(),child),
    {
        let a = self.retention_snapshot();
        assert forall|owner:usize,token:nat| semantics::registered(a,owner) && a.accumulators[owner].contains(token)
            implies token_kind(token) != Some(child) by {
            self.kernel.paper_observations(owner);
            let i = choose|i:int| 0 <= i < a.accumulators[owner].len() && a.accumulators[owner][i] == token;
            if token_kind(token) == Some(child) {
                assert(self.journal(owner)[i] == child);
                assert(self.journal(owner).contains(child));
                assert(self.referenced(child));
            }
        }
    }

    pub closed spec fn referenced(&self,child:usize) -> bool {
        exists|i:int| 0 <= i < self.episodes.len() && self.episodes[i].children().contains(child)
    }

    /// Reassemble the owned invariant after changing at most two entries. The
    /// removed-name exception is permitted only when no actual journal names it.
    proof fn rebuild(&self,prior:&Self,actor:usize,extra:usize,removed:Option<usize>)
        requires prior.wf(), self.kernel.wf(), self.episodes.len() == self.kernel.next_id(),
            forall|n:usize| paper::registered(prior.control(),n) && removed != Some(n) ==> paper::registered(self.control(),n),
            removed.is_some() ==> !self.referenced(removed.unwrap()),
            forall|i:int| 0 <= i < self.episodes.len() && i != actor && i != extra
                ==> i < prior.episodes.len() && self.episodes[i] == prior.episodes[i] && profile(prior.control(),self.control(),i as usize),
            actor < self.episodes.len() ==> Self::good(self.control(),&self.episodes[actor as int],actor) && retained(self.control(),&self.episodes[actor as int]),
            extra < self.episodes.len() ==> Self::good(self.control(),&self.episodes[extra as int],extra) && retained(self.control(),&self.episodes[extra as int]),
        ensures self.wf(),
    {
        assert forall|i:int| 0 <= i < self.episodes.len() implies Self::good(self.control(),&self.episodes[i],i as usize)
            && retained(self.control(),&self.episodes[i]) by {
            if i != actor && i != extra {
                assert(Self::good(prior.control(),&prior.episodes[i],i as usize));
                assert(retained(prior.control(),&prior.episodes[i]));
                assert forall|j:int| 0 <= j < self.episodes[i].children().len() implies
                    paper::registered(self.control(),self.episodes[i].children()[j]) by {
                    let child = self.episodes[i].children()[j];
                    assert(self.episodes[i].children().contains(child));
                    if removed == Some(child) { assert(self.referenced(child)); }
                }
            }
        }
    }

    pub fn new() -> (out:Self)
        ensures out.wf(),out.control().fibers.dom().is_empty(),
    { Self {kernel:Kernel::new(),episodes:Vec::new()} }

    pub fn insert(&mut self,parent:Option<usize>,dependencies:Vec<Port>,provisions:Vec<Port>) -> (r:Result<usize,ChildDriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),r.is_ok() ==> paper::step(old(self).control(),final(self).control(),r.unwrap(),paper::Rule::Insert),
    {
        let ghost prior = *self;
        match self.kernel.insert(parent,dependencies,provisions) {
            Err(e) => { proof { self.kernel.unchanged_observations(&prior.kernel); } Err(ChildDriverError::Kernel(e)) },
            Ok(id) => {
                self.episodes.push(ChildEpisode::new(id,Vec::new()));
                proof { self.rebuild(&prior,id,id,None); }
                Ok(id)
            },
        }
    }

    pub fn begin(&mut self,id:usize) -> (r:Result<(),ChildDriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),r.is_ok() ==> paper::step(old(self).control(),final(self).control(),id,paper::Rule::Begin),
    {
        let ghost prior = *self;
        match self.kernel.begin(id) {
            Err(e) => { proof { self.kernel.unchanged_observations(&prior.kernel); } Err(ChildDriverError::Kernel(e)) },
            Ok(()) => {
                proof { self.kernel.paper_observations(id); }
                let episode = ChildEpisode::attach(&self.kernel,id);
                match episode {
                    Err(e) => Err(ChildDriverError::Episode(e)),
                    Ok(episode) => {
                        self.episodes.set(id,episode);
                        proof { self.rebuild(&prior,id,id,None); }
                        Ok(())
                    },
                }
            },
        }
    }

    pub fn admit(&mut self,id:usize) -> (r:Result<bool,ChildDriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).control() == old(self).control(),
            r == Ok(true) ==> old(self).pending(id) || paper::coherent(old(self).control(),id),
    {
        let ghost prior = *self;
        proof { self.kernel.paper_observations(id); }
        if self.kernel.phase(id) != Some(Phase::Loading) { return Err(ChildDriverError::Kernel(Error::InvalidState)); }
        let r = match self.episodes[id].admit_current(&self.kernel) {Ok(x)=>Ok(x),Err(e)=>Err(ChildDriverError::Episode(e))};
        proof { self.rebuild(&prior,id,id,None); }
        r
    }

    /// The actual newly allocated child ID is stored in its parent's journal
    /// before this call returns. A target change cannot discard a pending yield.
    #[verifier::spinoff_prover]
    pub fn land_child(&mut self,id:usize,dependencies:Vec<Port>,provisions:Vec<Port>) -> (r:Result<usize,ChildDriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),r.is_ok() ==> child_landing(old(self).control(),final(self).control(),id,r.unwrap())
            && final(self).journal(id) == old(self).journal(id).push(r.unwrap()) && !final(self).pending(id),
    {
        let ghost prior = *self;
        proof { self.kernel.paper_observations(id); }
        if self.kernel.phase(id) != Some(Phase::Loading) { return Err(ChildDriverError::Kernel(Error::InvalidState)); }
        if !self.episodes[id].is_pending() { return Err(ChildDriverError::Episode(ChildError::NotAdmitted)); }
        if let Err(e) = self.episodes[id].admit_current(&self.kernel) {
            proof {self.rebuild(&prior,id,id,None);}
            return Err(ChildDriverError::Episode(e));
        }
        let has_target = match self.kernel.target(id) {
            Some(_target) => {
                proof {
                    self.kernel.refines_paper();
                    self.kernel.paper_target_vector(id,_target@);
                    paper::available_installed_coherent(self.control(),id,ISet::new(|b:Binding| _target@.contains(b)));
                }
                true
            },
            None => {proof {self.kernel.unavailable_not_coherent(id);} false},
        };
        assert(has_target == paper::coherent(prior.control(),id));
        match self.episodes[id].land_child(&mut self.kernel,dependencies,provisions) {
            Err(e) => {
                proof { self.kernel.unchanged_observations(&prior.kernel); self.rebuild(&prior,id,id,None); }
                Err(ChildDriverError::Episode(e))
            },
            Ok(child) => {
                self.episodes.push(ChildEpisode::new(child,Vec::new()));
                let ghost middle = self.control();
                proof {child_target_unchanged(prior.control(),middle,id,child);}
                if !has_target {
                    proof {self.kernel.paper_observations(id);}
                    let _departed = self.kernel.leave_if_changed(id);
                    assert(_departed.is_ok());
                    self.episodes[id].cancel();
                }
                proof {
                    assert(child_landing(prior.control(),self.control(),id,child));
                    assert(child != id);
                    assert forall|j:int| 0 <= j < self.episodes[id as int].children().len() implies
                        paper::registered(self.control(),self.episodes[id as int].children()[j]) by {
                        if j < prior.episodes[id as int].children().len() {
                            let c = prior.episodes[id as int].children()[j];
                            assert(paper::registered(prior.control(),c));
                            assert(c != child);
                        }
                    }
                    assert forall|i:int| 0 <= i < self.episodes.len() && i != id && i != child implies
                        i < prior.episodes.len() && self.episodes[i] == prior.episodes[i] && profile(prior.control(),self.control(),i as usize) by {
                        assert(profile(prior.control(),middle,i as usize));
                        if !has_target {assert(profile(middle,self.control(),i as usize));}
                    }
                    self.rebuild(&prior,id,child,None);
                }
                Ok(child)
            },
        }
    }

    pub fn end(&mut self,id:usize) -> (r:Result<(),ChildDriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),final(self).control() == old(self).control(),
    {
        let ghost prior = *self;
        proof { self.kernel.paper_observations(id); }
        if self.kernel.phase(id) != Some(Phase::Loading) {return Err(ChildDriverError::Kernel(Error::InvalidState));}
        let accepted = self.episodes[id].end();
        proof {self.rebuild(&prior,id,id,None);}
        if accepted {Ok(())} else {Err(ChildDriverError::Pending)}
    }

    pub fn finish(&mut self,id:usize) -> (r:Result<(),ChildDriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),r.is_ok() ==> paper::step(old(self).control(),final(self).control(),id,paper::Rule::Finish),
    {
        let ghost prior = *self;
        proof {self.kernel.paper_observations(id);}
        if !self.kernel.contains(id) {return Err(ChildDriverError::Kernel(Error::Unknown));}
        if !self.episodes[id].is_settled() || self.episodes[id].is_pending() {return Err(ChildDriverError::Pending);}
        match self.kernel.finish(id) {
            Ok(())=>{proof {self.rebuild(&prior,id,id,None);} Ok(())},
            Err(e)=>{proof {self.kernel.unchanged_observations(&prior.kernel);} Err(ChildDriverError::Kernel(e))},
        }
    }

    pub fn retire(&mut self,id:usize) -> (r:Result<(),ChildDriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),r.is_ok() ==> paper::step(old(self).control(),final(self).control(),id,paper::Rule::Retire),
    {
        let ghost prior = *self;
        match self.kernel.retire(id) {
            Ok(())=>{proof {self.rebuild(&prior,id,id,None);} Ok(())},
            Err(e)=>{proof {self.kernel.unchanged_observations(&prior.kernel);} Err(ChildDriverError::Kernel(e))},
        }
    }

    pub fn depart(&mut self,id:usize) -> (r:Result<(),ChildDriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),r.is_ok() ==> paper::step(old(self).control(),final(self).control(),id,
            if old(self).control().fibers[id].phase == Phase::Loading {paper::Rule::Divert} else {paper::Rule::Leave}),
    {
        let ghost prior = *self;
        proof {self.kernel.paper_observations(id);}
        if !self.kernel.contains(id) {return Err(ChildDriverError::Kernel(Error::Unknown));}
        if self.episodes[id].is_pending() {return Err(ChildDriverError::Pending);}
        match self.kernel.leave_if_changed(id) {
            Ok(())=>{self.episodes[id].cancel(); proof {self.rebuild(&prior,id,id,None);} Ok(())},
            Err(e)=>{proof {self.kernel.unchanged_observations(&prior.kernel);} Err(ChildDriverError::Kernel(e))},
        }
    }

    /// The kernel dependency guard precedes actual child retirement. Retirement
    /// does not wait for child deactivation; only later Remove waits for children.
    pub fn unload(&mut self,id:usize) -> (r:Result<(),ChildDriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),r.is_ok() ==> ownership::child_unload(old(self).control(),final(self).control(),id,old(self).journal(id))
            && final(self).journal(id).len() == 0,
    {
        let ghost prior = *self;
        proof {self.kernel.paper_observations(id);}
        if !self.kernel.contains(id) {return Err(ChildDriverError::Kernel(Error::Unknown));}
        if self.episodes[id].is_pending() {return Err(ChildDriverError::Pending);}
        match self.episodes[id].finish_restore(&mut self.kernel) {
            Err(e)=>{proof {self.kernel.unchanged_observations(&prior.kernel); self.rebuild(&prior,id,id,None);} Err(ChildDriverError::Episode(e))},
            Ok(())=>{
                proof {
                    assert(prior.episodes[id as int].owner() == id);
                    assert(ownership::child_unload(prior.control(),self.control(),id,prior.journal(id)));
                    let middle = choose|middle:paper::State| ownership::retired_children(prior.control(),middle,prior.journal(id))
                        && paper::step(middle,self.control(),id,paper::Rule::Unload);
                    assert forall|n:usize| paper::registered(prior.control(),n) implies paper::registered(self.control(),n) by {
                        if n != id {assert(paper::registered(middle,n) == paper::registered(self.control(),n));}
                    }
                    assert forall|i:int| 0 <= i < self.episodes.len() && i != id implies
                        i < prior.episodes.len() && self.episodes[i] == prior.episodes[i] && profile(prior.control(),self.control(),i as usize) by {
                        if paper::registered(prior.control(),i as usize) {
                            assert(paper::registered(middle,i as usize));
                            assert(middle.fibers[i as usize].phase == prior.control().fibers[i as usize].phase);
                        }
                    }
                    self.rebuild(&prior,id,id,None);
                }
                Ok(())
            },
        }
    }

    fn has_reference(&self,child:usize) -> (found:bool)
        ensures found == self.referenced(child),
    {
        let mut i = 0;
        while i < self.episodes.len()
            invariant i <= self.episodes.len(),
                forall|j:int| 0 <= j < i ==> !self.episodes[j].children().contains(child),
            decreases self.episodes.len()-i,
        {
            let mut j = 0;
            while j < self.episodes[i].len()
                invariant i < self.episodes.len(), j <= self.episodes[i as int].children().len(),
                    forall|k:int| 0 <= k < j ==> self.episodes[i as int].children()[k] != child,
                decreases self.episodes[i as int].children().len()-j,
            {
                if self.episodes[i].child_at(j) == Some(child) {
                    assert(self.episodes[i as int].children().contains(child));
                    return true;
                }
                j += 1;
            }
            i += 1;
        }
        false
    }

    /// Strict inverse policy: even a retired Inactive child remains registered
    /// until every actual journal reference to it has been consumed.
    pub fn remove(&mut self,id:usize) -> (r:Result<(),ChildDriverError>)
        requires old(self).wf(),
        ensures final(self).wf(),r.is_ok() ==> !old(self).referenced(id)
            && child_history::remove_unreferenced(|token:nat| token_kind(token),old(self).retention_snapshot(),id)
            && paper::step(old(self).control(),final(self).control(),id,paper::Rule::Remove),
            r == Err(ChildDriverError::Retained) ==> old(self).referenced(id),
    {
        let ghost prior = *self;
        if self.has_reference(id) {return Err(ChildDriverError::Retained);}
        proof {self.removal_refines(id);}
        match self.kernel.remove(id) {
            Ok(())=>{proof {self.rebuild(&prior,id,id,Some(id));} Ok(())},
            Err(e)=>{proof {self.kernel.unchanged_observations(&prior.kernel);} Err(ChildDriverError::Kernel(e))},
        }
    }

    pub fn phase(&self,id:usize)->(phase:Option<Phase>)
        ensures phase == if paper::registered(self.control(),id) {Some(self.control().fibers[id].phase)} else {None},
    {proof {self.kernel.paper_observations(id);} self.kernel.phase(id)}

    pub fn episode_generation(&self,id:usize)->(generation:Option<u64>)
        ensures generation == self.generation(id),
    {self.kernel.episode_generation(id)}

    pub fn retired(&self,id:usize)->(retired:bool)
        ensures retired == (paper::registered(self.control(),id) && self.control().fibers[id].retired),
    {proof {self.kernel.paper_observations(id);} self.kernel.retired(id)}

    pub fn inverse_count(&self,id:usize)->(count:Option<usize>)
        requires self.wf(),
        ensures count == if paper::registered(self.control(),id) {Some(self.journal(id).len() as usize)} else {None},
    {
        proof {self.kernel.paper_observations(id);}
        if self.kernel.contains(id) {Some(self.episodes[id].len())} else {None}
    }
}
} // verus!
