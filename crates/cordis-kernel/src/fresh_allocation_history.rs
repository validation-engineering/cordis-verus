//! Allocation history of the actual transactional Fresh driver.
//! A rejected command consumes no identity, while Remove preserves the bound.
use super::{Outcome, Transition};
#[cfg(verus_keep_ghost)]
use crate::{mixed_driver::Index, mixed_grammar as mx, refinement as r};
use vstd::prelude::*;
verus! {
pub open spec fn birth_spec(t:Transition)->Option<usize> {
    match t {Transition::Insert {actor,..}=>Some(actor),
        Transition::Step {outcome:Outcome::Child {child,..},..}=>Some(child),_=>None}
}
#[verifier::when_used_as_spec(birth_spec)]
pub fn birth(t:Transition)->(out:Option<usize>) ensures out==birth_spec(t), {
    match t {Transition::Insert {actor,..}=>Some(actor),
        Transition::Step {outcome:Outcome::Child {child,..},..}=>Some(child),_=>None}
}
pub open spec fn count(ts:Seq<Transition>)->nat decreases ts.len(), {
    if ts.len()==0 {0} else {count(ts.drop_last())+if birth_spec(ts.last()).is_some() {1nat} else {0nat}}
}
pub open spec fn advance(before:nat,t:Transition,after:nat)->bool {
    match birth_spec(t) {Some(n)=>n==before && after==before+1,None=>after==before}
}
pub open spec fn history(ts:Seq<Transition>,end:nat)->bool {
    &&& end==count(ts)
    &&& forall|i:int|0<=i<ts.len() ==> advance(count(ts.take(i)),ts[i],count(ts.take(i+1)))
}
pub proof fn append(ts:Seq<Transition>,before:nat,t:Transition,after:nat)
    requires history(ts,before),advance(before,t,after),
    ensures history(ts.push(t),after),
{
    assert(ts.push(t).drop_last()==ts);
    assert forall|i:int|0<=i<ts.push(t).len() implies advance(count(ts.push(t).take(i)),ts.push(t)[i],count(ts.push(t).take(i+1))) by {
        if i<ts.len() {assert(ts.push(t).take(i)==ts.take(i));assert(ts.push(t).take(i+1)==ts.take(i+1));}
        else {assert(i==ts.len());assert(ts.push(t).take(i)==ts);assert(ts.push(t).take(i+1)==ts.push(t));}
    }
}
/// Insert metadata is copied from the actual successful command, not reconstructed
/// from its label (which intentionally contains only actor and rule).
pub open spec fn payload(t:Transition,z:mx::Configuration<u64,Index>)->bool {
    match t {Transition::Insert {actor,parent,blueprint}=>
        r::registered(z.state.control,actor) && z.state.control.fibers[actor].parent==parent
            && z.roots.dom().contains(actor) && z.roots[actor]==(Index {blueprint,pc:0}),_=>true}
}
pub open spec fn payloads(ts:Seq<Transition>,states:Seq<mx::Configuration<u64,Index>>)->bool {
    states.len()==ts.len()+1 && forall|i:int|0<=i<ts.len() ==> payload(ts[i],states[i+1])
}
pub proof fn append_payload(ts:Seq<Transition>,states:Seq<mx::Configuration<u64,Index>>,t:Transition,z:mx::Configuration<u64,Index>)
    requires payloads(ts,states),payload(t,z),
    ensures payloads(ts.push(t),states.push(z)),
{
    assert forall|i:int|0<=i<ts.push(t).len() implies payload(ts.push(t)[i],states.push(z)[i+1]) by {
        if i<ts.len() {assert(payload(ts[i],states[i+1]));} else {assert(i==ts.len());}
    }
}

}
