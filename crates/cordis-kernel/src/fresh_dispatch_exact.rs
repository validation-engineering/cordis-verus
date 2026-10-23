//! Exact successors of the synchronous command dispatcher.
//! A plain departure keeps history unchanged; admitted in-flight landings use
//! their separate API and remain allowed by the general paper relation.
use super::FreshDriver;
#[cfg(verus_keep_ghost)]
use crate::{
    fresh_grammar as fg, fresh_semantics as fs, mixed_driver as core,
    mixed_driver::fresh::{self as driver, allocation},
    mixed_grammar as mx, refinement as r, semantics as s, Phase,
};
use vstd::prelude::*;
verus! {
pub open spec fn plain(a:mx::Configuration<u64,core::Index>,z:mx::Configuration<u64,core::Index>,t:core::Transition)->bool {
    match t {core::Transition::Depart {..}=>z.history==a.history,_=>true}
}
pub open spec fn step(bank:Seq<core::Blueprint>,a:mx::Configuration<u64,core::Index>,z:mx::Configuration<u64,core::Index>,t:core::Transition)->bool {
    let label=driver::label(t);
    &&& fs::step(core::library(),driver::programs(bank),a,z,label.0,label.1,label.2)
    &&& plain(a,z,t) && allocation::payload(t,z) && super::shape::configuration(bank,z)
}
pub open spec fn trace(states:Seq<mx::Configuration<u64,core::Index>>,ts:Seq<core::Transition>)->bool {
    states.len()==ts.len()+1 && forall|i:int|0<=i<ts.len() ==> plain(states[i],states[i+1],ts[i])
}
pub open spec fn allocated(next:nat,t:core::Transition)->bool {
    match allocation::birth_spec(t) {Some(n)=>n==next,None=>true}
}
proof fn framed_control(a:r::State,z:r::State,other:r::State,actor:usize)
    requires r::frame(a,z,actor),r::frame(a,other,actor),r::registered(z,actor)==r::registered(other,actor),
        r::registered(z,actor) ==> z.fibers[actor]==other.fibers[actor],
    ensures z==other,
{
    assert(z.fibers.dom() =~= other.fibers.dom()) by {
        assert forall|n:usize|z.fibers.dom().contains(n)==other.fibers.dom().contains(n) by {
            if n!=actor {assert(r::registered(z,n)==r::registered(a,n));assert(r::registered(other,n)==r::registered(a,n));}
        }
    }
    assert(z.fibers =~= other.fibers) by {
        assert forall|n:usize|z.fibers.dom().contains(n) implies z.fibers[n]==other.fibers[n] by {
            if n!=actor {assert(r::registered(z,n));assert(r::registered(a,n));assert(z.fibers[n]==a.fibers[n]);assert(other.fibers[n]==a.fibers[n]);}
        }
    }
}
/// The label alone loses Insert's blueprint and Divert's branch. The actual
/// record, runtime shape and plain-departure fact recover a unique successor.
#[verifier::spinoff_prover]
pub proof fn unique(bank:Seq<core::Blueprint>,a:mx::Configuration<u64,core::Index>,z:mx::Configuration<u64,core::Index>,t:core::Transition,
    other:mx::Configuration<u64,core::Index>,u:core::Transition,next:nat)
    requires fs::well_formed(core::library(),driver::programs(bank),a),s::total_active(a.state),
        step(bank,a,z,t),step(bank,a,other,u),t.command()==u.command(),allocated(next,t),allocated(next,u),
    ensures t==u,z==other,
{
    let actor=t.actor();
    match t {
        core::Transition::Insert {blueprint,..}=>{
            assert(actor==u.actor());
            super::shape::observations(bank,z,actor);super::shape::observations(bank,other,actor);
            assert(z.state.control.fibers[actor]==other.state.control.fibers[actor]);
            framed_control(a.state.control,z.state.control,other.state.control,actor);
        },
        core::Transition::Begin {..}=>{
            s::total_targets_agree(a.state,actor,z.state.control.fibers[actor].committed);
            s::total_targets_agree(a.state,actor,other.state.control.fibers[actor].committed);
            r::target_unique(a.state.control,actor,z.state.control.fibers[actor].committed,other.state.control.fibers[actor].committed);
        },
        core::Transition::Step {..}=>{
            let node=driver::programs(bank)(actor)(a.current[actor].unwrap());
            match node {fg::Node::Dependent {..}=>{},fg::Node::FreshChild {..}=>{}}
            assert(driver::label(t).2==driver::label(u).2);
            assert(driver::label(t).1==driver::label(u).1);
            match (t,u) {(core::Transition::Step {outcome:x,..},core::Transition::Step {outcome:y,..})=>{
                match (x,y) {(core::Outcome::Advanced,_)=>{},(core::Outcome::Finished,_)=>{},(core::Outcome::Child {..},_)=>{}}
            },_=>{}}
        },
        core::Transition::Retire {..}=>{
            framed_control(a.state.control,z.state.control,other.state.control,actor);
        },
        core::Transition::Depart {..}=>{
            assert(driver::label(t).1==driver::label(u).1);
            assert(z==mx::edit(a,actor,Phase::Unloading,a.state.control.fibers[actor].committed,None,a.state.accumulators[actor]));
            assert(other==mx::edit(a,actor,Phase::Unloading,a.state.control.fibers[actor].committed,None,a.state.accumulators[actor]));
        },
        _=>{},
    }
}
impl FreshDriver {
    /// Observable contract of an actual successful synchronous command.
    pub open spec fn applied(&self,after:&Self,t:core::Transition)->bool {
        let label=driver::label(t);
        &&& self.ack(after,label.0,label.1,label.2) && after.insertion_record(t)
        &&& allocation::advance(self.next_id(),t,after.next_id())
        &&& match t {core::Transition::Depart {actor,..}=>self.journal(actor)==after.journal(actor),_=>true}
    }
    pub proof fn advance_command_source(&self,after:&Self,bank:Seq<core::Blueprint>,a:mx::Configuration<u64,core::Index>,t:core::Transition)
        ->(z:mx::Configuration<u64,core::Index>)
        requires self.wf(),after.wf(),after.unique_declarations(),self.represents(bank,a),
            fs::well_formed(core::library(),driver::programs(bank),a),self.applied(after,t),
        ensures step(bank,a,z,t),after.represents(bank,z),fs::well_formed(core::library(),driver::programs(bank),z),
    {
        let label=driver::label(t);let z=self.advance_source(after,bank,a,label.0,label.1,label.2);
        after.insertion_source(t,bank,z);after.source_runtime_shape(bank,z);
        if let core::Transition::Depart {actor,..}=t {
            assert(a.state.accumulators[actor].len()==self.journal(actor).len());
            assert(z.state.accumulators[actor].len()==after.journal(actor).len());
            assert(z.history==a.history);
        }
        z
    }
    /// Success cannot silently choose another source successor. The model call
    /// supplies no executable result; the actual dispatch contract supplies it.
    pub proof fn exact_successor(&self,after:&Self,bank:Seq<core::Blueprint>,a:mx::Configuration<u64,core::Index>,z:mx::Configuration<u64,core::Index>,t:core::Transition,u:core::Transition)
        requires super::source::call(self,bank,a,z,t),plain(a,z,t),after.wf(),after.unique_declarations(),self.applied(after,u),u.command()==t.command(),
        ensures u==t,after.represents(bank,z),
    {
        let actual=self.advance_command_source(after,bank,a,u);self.inner.paper_total(a.state);
        unique(bank,a,z,t,actual,u,self.next_id());
    }
}
pub proof fn append(states:Seq<mx::Configuration<u64,core::Index>>,ts:Seq<core::Transition>,z:mx::Configuration<u64,core::Index>,t:core::Transition)
    requires trace(states,ts),plain(states.last(),z,t),
    ensures trace(states.push(z),ts.push(t)),
{
    assert forall|i:int|0<=i<ts.push(t).len() implies plain(states.push(z)[i],states.push(z)[i+1],ts.push(t)[i]) by {
        if i<ts.len() {assert(plain(states[i],states[i+1],ts[i]));}else {assert(i==ts.len());}
    }
}
}

#[path = "fresh_synchronous_transport.rs"]
pub mod transport;
