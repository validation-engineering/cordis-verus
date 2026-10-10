//! Concrete nonempty executions of the unified dependent/child interpreter.
//!
//! These witnesses construct every transition from an empty registry. Neither
//! successful steps nor intermediate invariants are premises of the proofs.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, dependent_grammar as d, global, mixed_grammar as g,
    mixed_syntax as syntax, preservation as inv, refinement as r, semantics as s, Phase, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn key(owner:usize)->Port {Port {key:owner as u64,realm:0}}
pub open spec fn provided(owner:usize)->ISet<Port> {ISet::empty().insert(key(owner))}
pub open spec fn library()->g::Library<(),(),u64,()> {
    d::Library {values:|_key:Port,_value:u64|true,arguments:|_op:(),_arg:()|true,
        outcomes:|_op:(),_outcome:()|true,key:|_op:()|key(0),allowed:ISet::empty(),
        apply:|_op:(),_arg:()| |_value:u64|None}
}
pub open spec fn equality()->spec_fn(Port,u64,u64)->bool {|_key:Port,a:u64,b:u64|a==b}
pub open spec fn programs()->g::Programs<(),(),u64,(),bool> {
    |actor:usize| |next:bool| if actor==0 && !next {
        g::Node::Child {child:1,dependencies:ISet::empty(),provisions:provided(1),root:false,next:Some(true)}
    } else if actor==0 {
        g::Node::Dependent {node:d::Node::Provision {key:key(0),value:7,next:None}}
    } else if actor==1 {
        g::Node::Dependent {node:d::Node::Provision {key:key(1),value:42,next:None}}
    } else {g::Node::Dependent {node:d::Node::Unit}}
}
pub proof fn primitive_theory()
    ensures d::primitive_theory(equality(),library()),
{ }
pub proof fn root_members()
    ensures syntax::member(library(),programs(),0,provided(0),provided(0),false),
        syntax::member(library(),programs(),0,provided(0),provided(0),true),
        syntax::member(library(),programs(),1,provided(1),provided(1),false),
{
    syntax::constructor_member(library(),programs(),1,provided(1),provided(1),false);
    syntax::constructor_member(library(),programs(),0,provided(0),provided(0),true);
    assert(ISet::<Port>::empty().union(provided(1)) =~= provided(1));
    syntax::constructor_member(library(),programs(),0,provided(0),provided(0),false);
}
pub open spec fn insert_parent(a:g::Configuration<u64,bool>)->g::Configuration<u64,bool> {
    g::Configuration {
        state:s::extend_child(a.state,global::insert_fiber(a.state.control,0,None,ISet::empty(),provided(0)),0,0),
        roots:a.roots.insert(0,false),current:a.current.insert(0,None),history:a.history,
    }
}
pub open spec fn retire(a:g::Configuration<u64,bool>,actor:usize)->g::Configuration<u64,bool> {
    g::Configuration {state:s::with_control(a.state,global::retire_fiber(a.state.control,actor)),
        roots:a.roots,current:a.current,history:a.history}
}
pub open spec fn erase(a:g::Configuration<u64,bool>,actor:usize)->g::Configuration<u64,bool> {
    g::Configuration {state:s::erase(a.state,actor),roots:a.roots.remove(actor),current:a.current.remove(actor),history:a.history}
}
#[verifier::opaque]
pub open spec fn trace()->Seq<g::Configuration<u64,bool>> {
    let a0=g::empty::<u64,bool>();let a1=insert_parent(a0);
    let a2=g::edit(a1,0,Phase::Loading,ISet::empty(),Some(false),Seq::empty());
    let a3=g::land(library(),programs(),a2,0,Phase::Loading);
    let a4=g::edit(a3,1,Phase::Loading,ISet::empty(),Some(false),Seq::empty());
    let a5=g::land(library(),programs(),a4,1,Phase::Active);
    let a6=g::land(library(),programs(),a5,0,Phase::Active);
    let a7=retire(a6,0);
    let a8=g::edit(a7,0,Phase::Unloading,ISet::empty(),None,a7.state.accumulators[0usize]);
    let a9=g::unload(a8,0);
    seq![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9]
}
pub open spec fn labels()->Seq<(usize,r::Rule)> {
    seq![(0usize,r::Rule::Insert),(0usize,r::Rule::Begin),(0usize,r::Rule::Iter),
        (1usize,r::Rule::Begin),(1usize,r::Rule::Finish),(0usize,r::Rule::Finish),
        (0usize,r::Rule::Retire),(0usize,r::Rule::Leave),(0usize,r::Rule::Unload)]
}
/// Every label is an actual successful mixed transition. The continuation
/// representation is `bool`; the table values and inverse receipts are real.
pub proof fn actual_execution()
    ensures g::execution(library(),programs(),trace(),labels()),trace().first()==g::empty::<u64,bool>(),
        trace().len()==10,
{
    reveal(trace);root_members();let states=trace();
    assert(ISet::<Port>::empty().union(provided(0)) =~= provided(0));
    assert(g::step(library(),programs(),states[0],states[1],0,r::Rule::Insert));
    assert(g::step(library(),programs(),states[1],states[2],0,r::Rule::Begin));
    assert(g::step(library(),programs(),states[2],states[3],0,r::Rule::Iter));
    assert(g::step(library(),programs(),states[3],states[4],1,r::Rule::Begin));
    assert(g::step(library(),programs(),states[4],states[5],1,r::Rule::Finish));
    assert(g::step(library(),programs(),states[5],states[6],0,r::Rule::Finish));
    ch::concrete_child_retirement(states[6].state,0);
    assert(g::step(library(),programs(),states[6],states[7],0,r::Rule::Retire));
    assert(g::step(library(),programs(),states[7],states[8],0,r::Rule::Leave));
    assert(states[8].state.accumulators[0usize] =~= seq![0nat,2nat]);
    reveal_with_fuel(g::restore,3);
    assert(g::restore(states[8].history,states[8].state.accumulators[0usize],states[8].state,0).is_some());
    assert(g::step(library(),programs(),states[8],states[9],0,r::Rule::Unload));
    assert forall|i:int| 0<=i<labels().len() implies g::step(library(),programs(),states[i],states[i+1],labels()[i].0,labels()[i].1) by {
        if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else if i==5 {} else if i==6 {} else if i==7 {} else {assert(i==8);}
    }
}
/// Parent restoration consumes the actual captured child receipt and its own
/// provision inverse, while the child remains Active with its published value.
pub proof fn parent_recovers_with_active_child()
    ensures {
        let states=trace();let before=states[8];let after=states[9];
        &&& g::execution(library(),programs(),states,labels())
        &&& forall|i:int| 0<=i<states.len() ==> g::well_formed(library(),programs(),states[i]) && inv::resource_safe(states[i].state)
        &&& g::child_domains(before.history,before.state.accumulators[0usize],before.state,0)
        &&& before.state.accumulators[0usize]==seq![0nat,2nat]
        &&& g::captured_child(before.history[0].landed.receipt)==Some(1usize)
        &&& !before.state.control.fibers[1usize].retired
        &&& after.state.control.fibers[0usize].phase==Phase::Inactive && after.state.tables[0usize].is_empty()
        &&& after.state.accumulators[0usize].len()==0
        &&& after.state.control.fibers[1usize].retired && after.state.control.fibers[1usize].phase==Phase::Active
        &&& after.state.tables[1usize][key(1)]==42 && after.state.tables[1usize].dom().contains(key(1))
    },
{
    actual_execution();primitive_theory();g::from_empty_safe(equality(),library(),programs(),trace(),labels());
    reveal(trace);let states=trace();
    g::journal_child_domains(library(),programs(),states[8],0);
    assert(states[8].state.accumulators[0usize] =~= seq![0nat,2nat]);
    g::restore_retires(library(),programs(),states[8].history,states[8].state.accumulators[0usize],states[8].state,0);
    assert(states[8].state.accumulators[0usize].contains(0nat));
    assert(g::kind(states[8].history)(0nat)==Some(1usize));
    reveal_with_fuel(g::restore,3);
}
/// In a second real prefix the child is retired before it starts. The original
/// Remove guard permits erasure, but the parent's actual journal retains it.
pub proof fn retained_inactive_child_cannot_be_removed()
    ensures {
        let source=trace()[3];let retired=retire(source,1);let removed=erase(retired,1);
        &&& g::step(library(),programs(),source,retired,1,r::Rule::Retire)
        &&& g::well_formed(library(),programs(),retired)
        &&& retired.state.control.fibers[1usize].retired && retired.state.control.fibers[1usize].phase==Phase::Inactive
        &&& r::step(retired.state.control,removed.state.control,1,r::Rule::Remove)
        &&& !ch::remove_unreferenced(g::kind(retired.history),retired.state,1)
        &&& !g::step(library(),programs(),retired,removed,1,r::Rule::Remove)
        &&& g::child_domains(retired.history,retired.state.accumulators[0usize],retired.state,0)
    },
{
    actual_execution();primitive_theory();g::from_empty_safe(equality(),library(),programs(),trace(),labels());
    reveal(trace);let source=trace()[3];let retired=retire(source,1);let removed=erase(retired,1);
    ch::concrete_child_retirement(source.state,1);
    assert(g::step(library(),programs(),source,retired,1,r::Rule::Retire));
    g::configuration_preservation(equality(),library(),programs(),source,retired,1,r::Rule::Retire);
    g::journal_child_domains(library(),programs(),retired,0);
    assert(retired.state.accumulators[0usize].contains(0nat));
    assert(g::kind(retired.history)(0nat)==Some(1usize));
    assert forall|n:usize| s::registered(retired.state,n) implies retired.state.control.fibers[n].parent!=Some(1usize) by {
        assert(n==0 || n==1);
    }
}

}
