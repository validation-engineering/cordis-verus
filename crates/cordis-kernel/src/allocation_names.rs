//! Executable finite permutations used to compact historical allocation names.
//! Identities outside the stored prefix are fixed, giving a total bijection.
use super::{Outcome, Transition};
#[cfg(verus_keep_ghost)]
use crate::alpha;
use vstd::prelude::*;
verus! {
pub struct Names { forward:Vec<usize>, backward:Vec<usize> }
impl Names {
    pub closed spec fn size(&self)->nat {self.forward.len() as nat}
    pub closed spec fn wf(&self)->bool {
        &&& self.forward.len()==self.backward.len()
        &&& forall|i:int| #![trigger self.forward[i]] #![trigger self.backward[i]] 0<=i<self.forward.len() ==> self.forward[i]<self.forward.len()
            && self.backward[i]<self.forward.len()
            && self.backward[self.forward[i] as int]==i
            && self.forward[self.backward[i] as int]==i
    }
    pub closed spec fn name_spec(&self,n:usize)->usize {
        if n<self.forward.len() {self.forward[n as int]} else {n}
    }
    pub closed spec fn inverse_spec(&self,n:usize)->usize {
        if n<self.backward.len() {self.backward[n as int]} else {n}
    }
    pub open spec fn renaming(&self)->alpha::Renaming {
        alpha::Renaming {forward:|n:usize|self.name_spec(n),backward:|n:usize|self.inverse_spec(n)}
    }
    pub proof fn bijection(&self)
        requires self.wf(),ensures alpha::bijective(self.renaming()),
    {
        let r=self.renaming();
        assert forall|n:usize| #[trigger] (r.backward)((r.forward)(n))==n by {
            if n<self.forward.len() {assert(self.backward[self.forward[n as int] as int]==n);}
        }
        assert forall|n:usize| #[trigger] (r.forward)((r.backward)(n))==n by {
            if n<self.backward.len() {assert(self.forward[self.backward[n as int] as int]==n);}
        }
    }
    pub proof fn prefix_pairing(&self,prior:&Self,source:usize,destination:usize)
        requires prior.wf(),prior.name_spec(source)>=destination,
            forall|n:usize|self.name_spec(n)==alpha::swap(prior.name_spec(source),destination,prior.name_spec(n)),
        ensures forall|n:usize|#[trigger] self.name_spec(n)<destination as nat+1 <==> prior.name_spec(n)<destination || n==source,
            forall|n:usize|#[trigger] prior.name_spec(n)<destination ==> self.name_spec(n)==prior.name_spec(n),
    {
        prior.bijection();
        assert forall|n:usize|#[trigger] self.name_spec(n)<destination as nat+1 <==> prior.name_spec(n)<destination || n==source by {
            if n!=source {prior.distinct(n,source);}
        }
    }
    pub proof fn distinct(&self,a:usize,b:usize)
        requires self.wf(),a!=b,ensures self.name_spec(a)!=self.name_spec(b),
    {self.bijection();}
    pub proof fn name_bound(&self,n:usize)
        requires self.wf(),n<self.size(),
        ensures self.name_spec(n)<self.size(),
    {}
    pub fn identity(size:usize)->(out:Self)
        ensures out.wf(),out.size()==size,forall|n:usize|out.name_spec(n)==n,
    {
        let mut forward:Vec<usize>=Vec::new();let mut backward:Vec<usize>=Vec::new();let mut i=0;
        while i<size
            invariant i<=size,forward.len()==i,backward.len()==i,
                forall|j:int|0<=j<i ==> forward[j]==j && backward[j]==j,
            decreases size-i,
        {forward.push(i);backward.push(i);i+=1;}
        Self {forward,backward}
    }
    #[verifier::when_used_as_spec(name_spec)]
    pub fn name(&self,n:usize)->(out:usize) ensures out==self.name_spec(n), {
        if n<self.forward.len() {self.forward[n]} else {n}
    }
    /// Exchange two destination names. This never discards the old inverse map.
    #[verifier::spinoff_prover]
    #[verifier::rlimit(20)]
    pub fn pair(&mut self,source:usize,destination:usize)
        requires old(self).wf(),source<old(self).size(),destination<old(self).size(),
        ensures final(self).wf(),final(self).size()==old(self).size(),
            final(self).name_spec(source)==destination,
            forall|n:usize|final(self).name_spec(n)==alpha::swap(old(self).name_spec(source),destination,old(self).name_spec(n)),
    {
        let ghost prior=*self;
        let previous=self.forward[source];let other=self.backward[destination];
        assert(prior.forward[source as int]<prior.forward.len());
        assert(prior.backward[destination as int]<prior.forward.len());
        assert(other<self.forward.len() && previous<self.backward.len());
        self.forward.set(source,destination);self.forward.set(other,previous);
        self.backward.set(destination,source);self.backward.set(previous,other);
        assert forall|i:int|0<=i<self.forward.len() implies self.forward[i]<self.forward.len()
            && self.backward[i]<self.forward.len()
            && self.backward[self.forward[i] as int]==i
            && self.forward[self.backward[i] as int]==i by {
            if i!=source && i!=other {
                assert(prior.backward[prior.forward[i] as int]==i);
                assert(prior.forward[i]!=previous && prior.forward[i]!=destination);
            }
            if i!=previous && i!=destination {
                assert(prior.forward[prior.backward[i] as int]==i);
                assert(prior.backward[i]!=source && prior.backward[i]!=other);
            }
        }
        assert forall|n:usize|self.name_spec(n)==alpha::swap(prior.name_spec(source),destination,prior.name_spec(n)) by {
            if n<prior.forward.len() && n!=source && n!=other {
                assert(prior.backward[prior.forward[n as int] as int]==n);
            }
        }
    }
    fn parent(&self,p:Option<usize>)->(out:Option<usize>)
        ensures out==alpha::parent(self.renaming(),p),
    {p.map(|n:usize| -> (out:usize) ensures out==self.name_spec(n), {self.name(n)})}
    pub fn transition(&self,t:Transition)->(out:Transition)
        ensures out==renamed(self.renaming(),t),
    {
        match t {
            Transition::Insert {parent,blueprint,actor}=>Transition::Insert {parent:self.parent(parent),blueprint,actor:self.name(actor)},
            Transition::Begin {actor}=>Transition::Begin {actor:self.name(actor)},
            Transition::Step {actor,outcome}=>{
                let outcome=match outcome {Outcome::Child {child,finished}=>Outcome::Child {child:self.name(child),finished},_=>outcome};
                Transition::Step {actor:self.name(actor),outcome}
            },
            Transition::Retire {actor}=>Transition::Retire {actor:self.name(actor)},
            Transition::Depart {actor,departure}=>Transition::Depart {actor:self.name(actor),departure},
            Transition::Unload {actor}=>Transition::Unload {actor:self.name(actor)},
            Transition::Remove {actor}=>Transition::Remove {actor:self.name(actor)},
        }
    }
}
pub open spec fn renamed(r:alpha::Renaming,t:Transition)->Transition {
    match t {
        Transition::Insert {parent,blueprint,actor}=>Transition::Insert {parent:alpha::parent(r,parent),blueprint,actor:(r.forward)(actor)},
        Transition::Begin {actor}=>Transition::Begin {actor:(r.forward)(actor)},
        Transition::Step {actor,outcome}=>Transition::Step {actor:(r.forward)(actor),outcome:match outcome {
            Outcome::Child {child,finished}=>Outcome::Child {child:(r.forward)(child),finished},_=>outcome}},
        Transition::Retire {actor}=>Transition::Retire {actor:(r.forward)(actor)},
        Transition::Depart {actor,departure}=>Transition::Depart {actor:(r.forward)(actor),departure},
        Transition::Unload {actor}=>Transition::Unload {actor:(r.forward)(actor)},
        Transition::Remove {actor}=>Transition::Remove {actor:(r.forward)(actor)},
    }
}
pub proof fn label(r:alpha::Renaming,t:Transition)
    ensures super::label(renamed(r,t))==((r.forward)(super::label(t).0),super::label(t).1,alpha::parent(r,super::label(t).2)),
        super::allocation::birth_spec(renamed(r,t))==alpha::parent(r,super::allocation::birth_spec(t)),
{match t {Transition::Step {outcome,..}=>{match outcome {Outcome::Child {..}=>{},_=>{}}},_=>{}}}
}
