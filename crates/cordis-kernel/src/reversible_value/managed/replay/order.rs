//! Actual recipe positions order retained calls; caller slice order is irrelevant.
//! Positions are qualified by their original recipe stream, never by a reused
//! lifecycle domain or by Begin ticket order.
use super::Source;
use crate::reversible_value::effect::ScalarEffect;
use crate::reversible_value::joint;
use std::sync::Arc;
use vstd::prelude::*;

verus! {
broadcast use vstd::seq_lib::group_seq_properties;
/// An actual call coordinate retains its stream identity together with its
/// non-wrapping revision. Construction preserves both runtime inputs; Source
/// separately binds them to its authentic completion receipt.
pub(super) struct CallPosition {pub(super) revision:Option<u64>,pub(super) stream:Arc<joint::identity::AllocationIdentity>}
impl CallPosition {
    pub(super) fn new(revision:Option<u64>,stream:Arc<joint::identity::AllocationIdentity>)->(out:Self)
        ensures out.revision==revision,out.stream==stream,
    {Self {revision,stream}}
}

#[derive(Debug,PartialEq,Eq)]
pub enum Error {DifferentStream {call:usize},UnnamedStream {call:usize},Exhausted {call:usize},Duplicate {first:usize,second:usize}}
pub open spec fn compatible_namespace<E:ScalarEffect,T:?Sized>(sources:Seq<Source<E,T>>)->bool {
    forall|i:int|0<=i<sources.len() ==> (#[trigger] sources[i]).stream_identity().namespace()==sources[0].stream_identity().namespace()
}
pub open spec fn same_stream<E:ScalarEffect,T:?Sized>(sources:Seq<Source<E,T>>)->bool {
    forall|i:int,j:int|0<=i<sources.len() && 0<=j<sources.len() ==>
        (#[trigger] sources[i]).original().completion().journal()==(#[trigger] sources[j]).original().completion().journal()
        && sources[i].original().completion().event().key==sources[j].original().completion().event().key
}
pub open spec fn prefix<E:ScalarEffect,T:?Sized>(sources:Seq<Source<E,T>>,indices:Seq<usize>,n:nat)->bool {
    indices.len()==n && indices.no_duplicates()
        && (forall|i:int|0<=i<indices.len() ==> (#[trigger] indices[i])<n && sources[indices[i] as int].call_position().is_some())
        && (forall|i:int|0<=i<n ==> #[trigger] indices.contains(i as usize))
        && (forall|i:int,j:int|0<=i<j<indices.len() ==>
            sources[#[trigger] indices[i] as int].call_position().unwrap()<sources[#[trigger] indices[j] as int].call_position().unwrap())
}
pub open spec fn chronological<E:ScalarEffect,T:?Sized>(sources:Seq<Source<E,T>>,indices:Seq<usize>)->bool {
    forall|i:int,j:int|0<=i<j<indices.len() ==>
        sources[#[trigger] indices[j] as int].original().completion().follows(&sources[#[trigger] indices[i] as int].original().completion())
}
#[allow(unused_variables)] // Only persistent proof resources are compared.
fn positions_order<E:ScalarEffect,T:?Sized>(earlier:&Source<E,T>,later:&Source<E,T>)
    requires earlier.wf(),later.wf(),earlier.call_position().is_some(),later.call_position().is_some(),
        earlier.call_position().unwrap()<later.call_position().unwrap(),
        earlier.original().completion().journal()==later.original().completion().journal(),
        earlier.original().completion().event().key==later.original().completion().event().key,
    ensures later.original().completion().follows(&earlier.original().completion()),
{
    proof {
    let tracked a=earlier.completion.borrow();let tracked b=later.completion.borrow();
    a.compare(b);
    if a.covers(b) {
        a.included(b);let frames=a.events();let key=a.event().key;
        assert(joint::step(joint::state_at(frames,b.at()),frames[b.at() as int].state,frames[b.at() as int].event));
        assert(joint::step(joint::state_at(frames,a.at()),frames[a.at() as int].state,frames[a.at() as int].event));
        joint::recipes::monotone(frames,b.at()+1,a.at()+1,key);
        assert(false);
    }
    assert(a.events().len()!=b.events().len());
    }
}
/// Sorting only depends on retained coordinates. Keep unrelated effect/path
/// quantifiers out of this helper, and compose receipt order in `plan` afterwards.
fn sort_positions<E:ScalarEffect,T:?Sized>(sources:&[Source<E,T>])->(out:Result<Vec<usize>,Error>)
    ensures out.is_ok() ==> prefix(sources@,out->Ok_0@,sources@.len()),
        out.is_err() ==> match out->Err_0 {
            Error::Exhausted {call}=>call<sources.len() && sources@[call as int].call_position().is_none(),
            Error::Duplicate {first,second}=>first<second<sources.len() && sources@[first as int].call_position()==sources@[second as int].call_position(),
            _=>false,
        },
{
    let mut indices:Vec<usize>=Vec::new();let mut i=0;
    while i<sources.len()
        invariant i<=sources.len(),prefix(sources@,indices@,i as nat),
        decreases sources.len()-i,
    {
        let position=match sources[i].stamp.revision {Some(p)=>p,None=>return Err(Error::Exhausted {call:i})};
        let mut j=0;let mut searching=true;
        while j<indices.len() && searching
            invariant j<=indices.len(),!searching ==> j<indices.len() && position<sources@[indices@[j as int] as int].call_position().unwrap(),i<sources.len(),prefix(sources@,indices@,i as nat),sources@[i as int].call_position()==Some(position),
                    forall|k:int|0<=k<j ==> sources@[#[trigger] indices@[k] as int].call_position().unwrap()<position,
            decreases indices.len()-j, if searching {1int} else {0int},
        {
            let prior=indices[j];let observed=match sources[prior].stamp.revision {Some(p)=>p,None=>{assert(false);panic!("certified recipe position")}};
            if observed==position {return Err(Error::Duplicate {first:prior,second:i});}
            if observed>position {searching=false;}else {j+=1;}
        }
        assert(j<indices.len() ==> position<sources@[indices@[j as int] as int].call_position().unwrap());
        let ghost before=indices@;
        indices.insert(j,i);
        proof {
            assert forall|k:int|0<=k<indices.len() implies (#[trigger] indices@[k])<i+1 && sources@[indices@[k] as int].call_position().is_some() by {
                if k<j as int {assert(indices@[k]==before[k]);} else if k>j as int {assert(indices@[k]==before[k-1]);}
            }
            assert forall|k:int|0<=k<i+1 implies #[trigger] indices@.contains(k as usize) by {
                if k<i {assert(before.contains(k as usize));let p=choose|p:int|0<=p<before.len() && before[p]==k as usize;
                    if p<j as int {assert(indices@[p]==k as usize);} else {assert(indices@[p+1]==k as usize);}
                } else {assert(indices@[j as int]==i);}
            }
            assert forall|a:int,b:int|0<=a<b<indices.len() implies
                sources@[#[trigger] indices@[a] as int].call_position().unwrap()<sources@[#[trigger] indices@[b] as int].call_position().unwrap() by {
                if b<j as int {assert(indices@[a]==before[a]);assert(indices@[b]==before[b]);}
                else if a>j as int {assert(indices@[a]==before[a-1]);assert(indices@[b]==before[b-1]);}
                else if b==j as int {assert(indices@[a]==before[a]);assert(sources@[before[a] as int].call_position().unwrap()<position);}
                else if a==j as int {assert(indices@[b]==before[b-1]);assert(position<sources@[before[j as int] as int].call_position().unwrap());if b-1>j as int {assert(sources@[before[j as int] as int].call_position().unwrap()<sources@[before[b-1] as int].call_position().unwrap());}}
                else {assert(indices@[a]==before[a]);assert(indices@[b]==before[b-1]);assert(sources@[before[a] as int].call_position().unwrap()<sources@[before[b-1] as int].call_position().unwrap());}
            }
            assert(indices@.no_duplicates()) by {
                assert forall|a:int,b:int|0<=a<indices.len() && 0<=b<indices.len() && a!=b implies indices@[a]!=indices@[b] by {
                    if a<b {assert(sources@[indices@[a] as int].call_position().unwrap()<sources@[indices@[b] as int].call_position().unwrap());}
                    else {assert(sources@[indices@[b] as int].call_position().unwrap()<sources@[indices@[a] as int].call_position().unwrap());}
                }
            }
        }
        i+=1;
    }
    Ok(indices)
}
/// Insertion sort is over source indices only: no operation or inverse moves,
/// and retained inputs are never read from the live source objects again.
pub fn plan<E:ScalarEffect,T:?Sized>(sources:&[Source<E,T>])->(out:Result<Vec<usize>,Error>)
    requires forall|i:int|0<=i<sources.len() ==> (#[trigger] sources@[i]).wf(),compatible_namespace(sources@),
    ensures out.is_ok() ==> same_stream(sources@) && prefix(sources@,out->Ok_0@,sources@.len()) && chronological(sources@,out->Ok_0@),
        out.is_err() ==> match out->Err_0 {
            Error::DifferentStream {call}=>call<sources.len() && sources@[call as int].stream_identity().address()!=sources@[0].stream_identity().address(),
            Error::UnnamedStream {call}=>call<sources.len() && sources@[call as int].stream_identity().number_spec().is_none(),
            Error::Exhausted {call}=>call<sources.len() && sources@[call as int].call_position().is_none(),
            Error::Duplicate {first,second}=>first<second<sources.len() && sources@[first as int].call_position()==sources@[second as int].call_position(),
        },
{
    let mut c=0;
    while c<sources.len()
        invariant c<=sources.len(),compatible_namespace(sources@),c>0 ==> sources@[0].stream_identity().number_spec().is_some(),
            forall|k:int|0<=k<sources.len() ==> (#[trigger] sources@[k]).wf(),
            forall|k:int|0<=k<c ==> (#[trigger] sources@[k]).stream_identity().address()==sources@[0].stream_identity().address(),
        decreases sources.len()-c,
    {
        if sources[c].stamp.stream.number().is_none() {return Err(Error::UnnamedStream {call:c});}
        if sources[0].stamp.stream.same(&sources[c].stamp.stream)==Some(false) {return Err(Error::DifferentStream {call:c});}
        c+=1;
    }
    assert(same_stream(sources@));
    let indices=sort_positions(sources)?;
    let mut n=1;
    while n<indices.len()
        invariant 1<=n,n<=indices.len() || indices.len()==0,
            prefix(sources@,indices@,sources@.len()),same_stream(sources@),
            forall|k:int|0<=k<sources.len() ==> (#[trigger] sources@[k]).wf(),
            forall|i:int,j:int|0<=i<j<n && j<indices.len() ==>
                sources@[#[trigger] indices@[j] as int].original().completion().follows(&sources@[#[trigger] indices@[i] as int].original().completion()),
        decreases indices.len()-n,
    {
        positions_order(&sources[indices[n-1]],&sources[indices[n]]);
        proof {
            assert forall|i:int|0<=i<n implies sources@[indices@[n as int] as int].original().completion().follows(&sources@[#[trigger] indices@[i] as int].original().completion()) by {
                if i<n-1 {let a=sources@[indices@[n as int] as int].original().completion();let b=sources@[indices@[n as int-1] as int].original().completion();let c=sources@[indices@[i] as int].original().completion();a.after_cover(&b,&c);}
            }
        }
        n+=1;
    }
    Ok(indices)
}
}
