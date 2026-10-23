//! Checked command preparation after deleting allocation-producing transitions.
//! Keep source order, compact births, and reject any use without a retained origin.
#[cfg(verus_keep_ghost)]
use super::names;
use super::{allocation as a, names::Names, Command, ScriptReport, Transition};
#[cfg(verus_keep_ghost)]
use crate::alpha;
use vstd::prelude::*;
verus! {
#[derive(Copy,Clone,Debug,PartialEq,Eq,Structural)]
pub enum Error {MaskLength,UnknownBirth {index:usize},RepeatedBirth {index:usize},Overflow {index:usize},MissingOrigin {index:usize}}

pub open spec fn selected(ts:Seq<Transition>,keep:Seq<bool>)->Seq<Transition>
    decreases ts.len(),
{
    if ts.len()==0 {Seq::empty()} else {
        let prior=selected(ts.drop_last(),keep.drop_last());
        if keep.last() {prior.push(ts.last())} else {prior}
    }
}
pub open spec fn renamed(r:alpha::Renaming,ts:Seq<Transition>)->Seq<Transition> {
    ts.map(|_:int,t:Transition|names::renamed(r,t))
}
pub proof fn prefix(ts:Seq<Transition>,keep:Seq<bool>,i:int)
    requires ts.len()==keep.len(),0<=i<ts.len(),
    ensures selected(ts.take(i+1),keep.take(i+1))==if keep[i] {selected(ts.take(i),keep.take(i)).push(ts[i])} else {selected(ts.take(i),keep.take(i))},
{
    assert(ts.take(i+1).drop_last()==ts.take(i));assert(keep.take(i+1).drop_last()==keep.take(i));
}
pub open spec fn available(next:nat,t:Transition)->bool {
    match t {
        Transition::Insert {parent,actor,..}=>actor==next && (parent.is_some() ==> parent.unwrap()<next),
        _=>t.actor()<next && (a::birth_spec(t).is_some() ==> a::birth_spec(t).unwrap()==next),
    }
}
fn check_available(next:usize,t:Transition)->(out:bool) ensures out==available(next as nat,t), {
    match t {
        Transition::Insert {parent,actor,..}=>actor==next && match parent {Some(p)=>p<next,None=>true},
        _=>t.actor()<next && match a::birth(t) {Some(child)=>child==next,None=>true},
    }
}
/// This is preparation data, not authority to skip the real driver's checks.
pub struct Plan {pub names:Names,pub transitions:Vec<Transition>,pub allocated:usize}
impl Plan {
    pub open spec fn matches(&self,source:Seq<Transition>,keep:Seq<bool>)->bool {
        &&& source.len()==keep.len() && self.names.wf()
        &&& self.transitions@==renamed(self.names.renaming(),selected(source,keep))
        &&& a::history(self.transitions@,self.allocated as nat)
        &&& forall|i:int|0<=i<self.transitions.len() ==> available(a::count(self.transitions@.take(i)),self.transitions[i])
    }
    pub fn commands(&self)->(out:Vec<Command>)
        ensures out@==self.transitions@.map(|_:int,t:Transition|t.command()),
    {
        let mut out:Vec<Command>=Vec::new();let mut i=0;
        while i<self.transitions.len()
            invariant i<=self.transitions.len(),out.len()==i,
                forall|j:int|0<=j<i ==> out[j]==self.transitions[j].command(),
            decreases self.transitions.len()-i,
        {out.push(self.transitions[i].command());i+=1;}
        assert(out@ =~= self.transitions@.map(|_:int,t:Transition|t.command()));out
    }
}

/// Keep the images of earlier retained births fixed while pairing the next one.
#[verifier::spinoff_prover]
#[verifier::rlimit(20)]
fn choose_names(source:&[Transition],keep:&[bool],bound:usize)->(out:Result<Names,Error>)
    requires source.len()==keep.len(),
    ensures a::history(source@,bound as nat) ==> out.is_ok(),
        out.is_ok() ==> out.unwrap().wf() && out.unwrap().size()==bound
        && forall|j:int|0<=j<source.len() && keep[j] && a::birth_spec(source[j]).is_some() ==>
            out.unwrap().name_spec(a::birth_spec(source[j]).unwrap())==a::count(selected(source@.take(j),keep@.take(j))),
{
    let mut names=Names::identity(bound);let mut next=0usize;let mut i=0usize;
    while i<source.len()
        invariant i<=source.len(),keep.len()==source.len(),names.wf(),names.size()==bound,next<=bound,
            a::history(source@,bound as nat) ==> origins::origin_bound(&names,next as nat,a::count(source@.take(i as int))),
            next==a::count(selected(source@.take(i as int),keep@.take(i as int))),
            forall|j:int|0<=j<i && keep[j] && a::birth_spec(source[j]).is_some() ==>
                names.name_spec(a::birth_spec(source[j]).unwrap())==a::count(selected(source@.take(j),keep@.take(j)))
                && names.name_spec(a::birth_spec(source[j]).unwrap())<next,
        decreases source.len()-i,
    {
        proof {
            prefix(source@,keep@,i as int);
            origins::selected_bound(source@.take(i as int),keep@.take(i as int));
            origins::monotone(source@,i as int,i as int+1);
        }
        if keep[i] {
            assert(selected(source@.take(i as int+1),keep@.take(i as int+1)).drop_last()==selected(source@.take(i as int),keep@.take(i as int)));
            if let Some(born)=a::birth(source[i]) {
                proof {if a::history(source@,bound as nat) {origins::birth_bound(source@,bound as nat,i as int);}}
                if born>=bound {return Err(Error::UnknownBirth {index:i});}
                if names.name(born)<next {return Err(Error::RepeatedBirth {index:i});}
                if next>=bound {return Err(Error::Overflow {index:i});}
                let ghost prior=names;
                names.pair(born,next);
                proof {
                    if a::history(source@,bound as nat) {origins::extend_origin(&prior,&names,born,next,a::count(source@.take(i as int)));}
                    assert forall|j:int|0<=j<i && keep[j] && a::birth_spec(source[j]).is_some() implies
                        names.name_spec(a::birth_spec(source[j]).unwrap())==a::count(selected(source@.take(j),keep@.take(j)))
                        && names.name_spec(a::birth_spec(source[j]).unwrap())<next+1 by {
                        let n=a::birth_spec(source[j]).unwrap();assert(prior.name_spec(n)<next);
                    }
                }
                next+=1;
            }
        }
        assert(next==a::count(selected(source@.take(i as int+1),keep@.take(i as int+1))));
        i+=1;
    }
    Ok(names)
}

/// Malformed birth metadata and uses without retained origins are rejected.
/// Real ScriptReport callers use the actual historical allocation bound below.
#[verifier::spinoff_prover]
pub fn compact(source:&[Transition],keep:&[bool],bound:usize)->(out:Result<Plan,Error>)
    ensures a::history(source@,bound as nat) && origins::closed(source@,keep@) ==> out.is_ok(),
        out.is_ok() ==> out.unwrap().matches(source@,keep@),
{
    if source.len()!=keep.len() {return Err(Error::MaskLength);}
    let names=choose_names(source,keep,bound)?;
    let mut out:Vec<Transition>=Vec::new();let mut allocated=0usize;let mut i=0usize;
    while i<source.len()
        invariant i<=source.len(),keep.len()==source.len(),names.wf(),origins::paired(&names,source@,keep@),
            out@==renamed(names.renaming(),selected(source@.take(i as int),keep@.take(i as int))),
            a::history(out@,allocated as nat),
            forall|j:int|0<=j<out.len() ==> available(a::count(out@.take(j)),out[j]),
        decreases source.len()-i,
    {
        proof {prefix(source@,keep@,i as int);}
        if keep[i] {
            let t=names.transition(source[i]);
            proof {
                origins::renamed_count(names.renaming(),selected(source@.take(i as int),keep@.take(i as int)));
                if origins::closed(source@,keep@) {origins::enabled(&names,source@,keep@,i as int);}
            }
            if !check_available(allocated,t) {return Err(Error::MissingOrigin {index:i});}
            let ghost previous=out@;let ghost old_next=allocated as nat;
            if a::birth(t).is_some() {
                proof {
                    if a::history(source@,bound as nat) {
                        names::label(names.renaming(),source[i as int]);
                        origins::birth_bound(source@,bound as nat,i as int);
                        origins::selected_bound(source@.take(i as int),keep@.take(i as int));
                    }
                }
                if allocated==usize::MAX {return Err(Error::Overflow {index:i});}
                allocated+=1;
            }
            out.push(t);
            proof {
                a::append(previous,old_next,t,allocated as nat);
                assert forall|j:int|0<=j<out.len() implies available(a::count(out@.take(j)),out[j]) by {
                    if j<previous.len() {assert(out@.take(j)==previous.take(j));}
                    else {assert(j==previous.len());assert(out@.take(j)==previous);}
                }
                assert(out@ =~= renamed(names.renaming(),selected(source@.take(i as int+1),keep@.take(i as int+1))));
            }
        }
        i+=1;
    }
    assert(source@.take(i as int)==source@);assert(keep@.take(i as int)==keep@);
    let plan=Plan {names,transitions:out,allocated};
    assert(plan.matches(source@,keep@));Ok(plan)
}
impl ScriptReport {
    pub fn compact(&self,keep:&[bool])->(out:Result<Plan,Error>)
        ensures execution_origins::admitted(self,keep@) ==> out.is_ok(),
            a::history(self.transitions@,self.machine.next_id()) && origins::closed(self.transitions@,keep@) ==> out.is_ok(),
            out.is_ok() ==> out.unwrap().matches(self.transitions@,keep@),
    {
        proof {if execution_origins::admitted(self,keep@) {execution_origins::admission_complete(self,keep@);}}
        compact(self.transitions.as_slice(),keep,self.machine.allocation_bound())
    }
}
}

pub mod source;

pub mod origins;

pub mod execution_origins;
