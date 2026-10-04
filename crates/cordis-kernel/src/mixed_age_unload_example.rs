//! One real foreign journal contains receipts on both sides of the cut.
//!
//! A foreign episode yields after its first +7, then finishes with another +7
//! among the owner's Provision and Operation. Its one LIFO Unload consumes new
//! token 3 and old token 1. Deletion renames only the new token, to 2.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, dependent_grammar as d, dependent_lift as dep, foreign_unload as fu,
    grammar_lift as lift, mixed_age_unload as mixed, mixed_grammar as g,
    mixed_observational_runs as obs, mixed_syntax as syntax, mixed_transposition as t,
    observational_lift as ol, old_journal_unload as old, providing_owner_deletion as source_proof,
    providing_owner_execution as deletion, recovery_examples as ex, refinement as r,
    semantics as s, shared_execution as sh, shared_unload_execution as history, Binding, Phase,
};
use vstd::prelude::*;

verus! {

pub open spec fn programs()->g::Programs<crate::Port,int,int,(),nat> {
    |actor:usize| |stage:nat|if actor==0 {
        g::Node::Dependent {node:d::Node::Provision {key:ex::key(0),value:10,next:None}}
    } else if actor==1 && stage==0 {
        g::Node::Dependent {node:d::Node::Provision {key:ex::key(1),value:99,next:Some(1nat)}}
    } else {g::Node::Dependent {node:d::Node::Operation {operation:ex::key(0),argument:if actor==1 {5}else{7},
        select:|_:()|if actor==2 && stage==0 {Some(1nat)}else{None}}}}
}
#[verifier::opaque]
pub open spec fn setup()->Seq<g::Configuration<int,nat>> {
    let empty=g::empty::<int,nat>();
    let a1=t::insert(empty,0,None,ISet::empty(),ex::provided(0),0nat);
    let a2=t::insert(a1,1,None,ex::provided(0),ex::provided(1),0nat);
    let a3=t::insert(a2,2,None,ex::provided(0),ISet::empty(),0nat);
    let a4=g::edit(a3,0,Phase::Loading,ISet::empty(),Some(0nat),Seq::empty());
    let a5=g::land(ex::library(),programs(),a4,0,Phase::Active);
    let a6=g::edit(a5,2,Phase::Loading,sh::example_view(),Some(0nat),Seq::empty());
    let a7=g::land(ex::library(),programs(),a6,2,Phase::Loading);
    seq![empty,a1,a2,a3,a4,a5,a6,a7]
}
pub open spec fn setup_labels()->Seq<(usize,r::Rule)> {
    seq![(0usize,r::Rule::Insert),(1usize,r::Rule::Insert),(2usize,r::Rule::Insert),(0usize,r::Rule::Begin),
        (0usize,r::Rule::Finish),(2usize,r::Rule::Begin),(2usize,r::Rule::Iter)]
}
#[verifier::opaque]
pub open spec fn source()->Seq<g::Configuration<int,nat>> {
    let cut=setup().last();
    let a1=g::edit(cut,1,Phase::Loading,sh::example_view(),Some(0nat),Seq::empty());
    let a2=g::land(ex::library(),programs(),a1,1,Phase::Loading);
    let a3=g::land(ex::library(),programs(),a2,2,Phase::Active);
    let a4=g::land(ex::library(),programs(),a3,1,Phase::Active);
    let a5=sh::retire(a4,1);
    let a6=g::edit(a5,1,Phase::Unloading,sh::example_view(),None,a5.state.accumulators[1usize]);
    let a7=sh::retire(a6,2);
    let a8=g::edit(a7,2,Phase::Unloading,sh::example_view(),None,a7.state.accumulators[2usize]);
    seq![cut,a1,a2,a3,a4,a5,a6,a7,a8]
}
pub open spec fn labels()->Seq<(usize,r::Rule)> {
    seq![(1usize,r::Rule::Begin),(1usize,r::Rule::Iter),(2usize,r::Rule::Finish),(1usize,r::Rule::Finish),
        (1usize,r::Rule::Retire),(1usize,r::Rule::Leave),(2usize,r::Rule::Retire),(2usize,r::Rule::Leave)]
}
pub open spec fn target()->Seq<g::Configuration<int,nat>> {
    deletion::delete(ex::library(),programs(),source(),labels(),1)
}
#[verifier::opaque]
pub open spec fn surviving()->Seq<g::Configuration<int,nat>> {
    let cut=setup().last();let a1=g::land(ex::library(),programs(),cut,2,Phase::Active);
    let a2=sh::retire(a1,1);let a3=sh::retire(a2,2);
    let a4=g::edit(a3,2,Phase::Unloading,a3.state.control.fibers[2usize].committed,None,a3.state.accumulators[2usize]);
    seq![cut,a1,a2,a3,a4]
}

pub proof fn component_members()
    ensures syntax::member(ex::library(),programs(),0,ex::provided(0),ex::provided(0),0nat),
        syntax::member(ex::library(),programs(),1,ex::provided(0).union(ex::provided(1)),ex::provided(1),0nat),
        syntax::member(ex::library(),programs(),2,ex::provided(0),ISet::empty(),0nat),
{
    let lib=ex::library();
    syntax::constructor_member(lib,programs(),0,ex::provided(0),ex::provided(0),0nat);
    syntax::constructor_member(lib,programs(),1,ex::provided(0).union(ex::provided(1)),ex::provided(1),1nat);
    syntax::constructor_member(lib,programs(),1,ex::provided(0).union(ex::provided(1)),ex::provided(1),0nat);
    syntax::constructor_member(lib,programs(),2,ex::provided(0),ISet::empty(),1nat);
    syntax::constructor_member(lib,programs(),2,ex::provided(0),ISet::empty(),0nat);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn actual_setup()
    ensures g::execution(ex::library(),programs(),setup(),setup_labels()),setup().first()==g::empty::<int,nat>(),setup().last()==source().first(),
        g::well_formed(ex::library(),programs(),source().first()),
        source().first().history.len()==2,source().first().state.tables[0usize][ex::key(0)]==17,
        source().first().state.accumulators[2usize]==seq![1nat],source().first().current[2usize]==Some(1nat),
        source().first().state.control.fibers[2usize].phase==Phase::Loading,
        source().first().state.control.fibers[1usize].phase==Phase::Inactive,source().first().state.tables[1usize].is_empty(),
{
    component_members();sh::example_interface();reveal(setup);reveal(source);
    let lib=ex::library();let states=setup();let steps=setup_labels();
    assert(ISet::<crate::Port>::empty().union(ex::provided(0)) =~= ex::provided(0));
    assert(ex::provided(0).union(ISet::empty()) =~= ex::provided(0));
    g::empty_well_formed(lib,programs());
    t::insertion_step(lib,programs(),states[0],0,None,ISet::empty(),ex::provided(0),0nat);
    ol::configuration_preservation(ex::equality(),lib,programs(),states[0],states[1],0,r::Rule::Insert);
    t::insertion_step(lib,programs(),states[1],1,None,ex::provided(0),ex::provided(1),0nat);
    ol::configuration_preservation(ex::equality(),lib,programs(),states[1],states[2],1,r::Rule::Insert);
    t::insertion_step(lib,programs(),states[2],2,None,ex::provided(0),ISet::empty(),0nat);
    ol::configuration_preservation(ex::equality(),lib,programs(),states[2],states[3],2,r::Rule::Insert);
    assert(g::step(lib,programs(),states[3],states[4],0,r::Rule::Begin));
    ol::configuration_preservation(ex::equality(),lib,programs(),states[3],states[4],0,r::Rule::Begin);
    assert(g::step(lib,programs(),states[4],states[5],0,r::Rule::Finish));
    ol::configuration_preservation(ex::equality(),lib,programs(),states[4],states[5],0,r::Rule::Finish);
    sh::example_target(states[5].state,2);assert(g::step(lib,programs(),states[5],states[6],2,r::Rule::Begin));
    ol::configuration_preservation(ex::equality(),lib,programs(),states[5],states[6],2,r::Rule::Begin);
    assert(lift::names_key(Binding {key:0,realm:0,provider:0},ex::key(0)));
    assert(states[6].state.control.fibers[2usize].committed.contains(Binding {key:0,realm:0,provider:0}));
    assert(exists|b:Binding| states[6].state.control.fibers[2usize].committed.contains(b) && lift::names_key(b,ex::key(0)));
    assert(lift::resolve(states[6].state,2,ex::key(0))==Some(0usize));
    assert(g::step(lib,programs(),states[6],states[7],2,r::Rule::Iter));
    ol::configuration_preservation(ex::equality(),lib,programs(),states[6],states[7],2,r::Rule::Iter);
    assert(states[7].state.accumulators[2usize] =~= seq![1nat]);
    assert forall|i:int| 0<=i<steps.len() implies g::step(lib,programs(),states[i],states[i+1],steps[i].0,steps[i].1) by {
        if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else if i==5 {} else {assert(i==6);}
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn actual_source()
    ensures g::execution(ex::library(),programs(),source(),labels()),source_proof::separated(source().first().state,1),
        source_proof::fragment(programs(),source(),labels(),2,1),!old::owner_window(source(),labels(),1),
        source().last().history.len()==5,source().last().state.accumulators[2usize]==seq![1nat,3nat],
        source().last().state.accumulators[1usize]==seq![2nat,4nat],
        old::old_tokens(programs(),source().last().history,source().last().state.accumulators[2usize],source().last().history.len(),2),
        !old::old_tokens(programs(),source().last().history,source().last().state.accumulators[2usize],2,2),
        !fu::tracked_tokens(source().last().history,source().last().state.accumulators[2usize],2,2),
        source().last().state.control.fibers[1usize].phase==Phase::Unloading,
        source().last().state.tables[0usize][ex::key(0)]==29,source().last().state.tables[1usize][ex::key(1)]==99,
        g::step(ex::library(),programs(),source().last(),g::unload(source().last(),2),2,r::Rule::Unload),
        g::unload(source().last(),2).state.tables[0usize][ex::key(0)]==15,g::unload(source().last(),2).state.tables[1usize][ex::key(1)]==99,
        s::registered(g::unload(source().last(),2).state,0),g::unload(source().last(),2).state.tables[0usize].dom().contains(ex::key(0)),
{
    actual_setup();sh::example_interface();reveal(source);reveal(setup);
    let lib=ex::library();let states=source();let steps=labels();
    sh::example_target(states[0].state,1);assert(g::step(lib,programs(),states[0],states[1],1,r::Rule::Begin));
    assert(g::step(lib,programs(),states[1],states[2],1,r::Rule::Iter));
    assert(lift::names_key(Binding {key:0,realm:0,provider:0},ex::key(0)));
    assert(states[2].state.control.fibers[2usize].committed.contains(Binding {key:0,realm:0,provider:0}));
    assert(exists|b:Binding| states[2].state.control.fibers[2usize].committed.contains(b) && lift::names_key(b,ex::key(0)));
    assert(lift::resolve(states[2].state,2,ex::key(0))==Some(0usize));assert(g::step(lib,programs(),states[2],states[3],2,r::Rule::Finish));
    assert(states[3].state.control.fibers[1usize].committed.contains(Binding {key:0,realm:0,provider:0}));
    assert(exists|b:Binding| states[3].state.control.fibers[1usize].committed.contains(b) && lift::names_key(b,ex::key(0)));
    assert(lift::resolve(states[3].state,1,ex::key(0))==Some(0usize));assert(g::step(lib,programs(),states[3],states[4],1,r::Rule::Finish));
    ch::concrete_child_retirement(states[4].state,1);assert(g::step(lib,programs(),states[4],states[5],1,r::Rule::Retire));
    assert(g::step(lib,programs(),states[5],states[6],1,r::Rule::Leave));
    ch::concrete_child_retirement(states[6].state,2);assert(g::step(lib,programs(),states[6],states[7],2,r::Rule::Retire));
    assert(g::step(lib,programs(),states[7],states[8],2,r::Rule::Leave));
    assert forall|i:int| 0<=i<steps.len() implies g::step(lib,programs(),states[i],states[i+1],steps[i].0,steps[i].1) by {
        if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else if i==5 {} else if i==6 {} else {assert(i==7);}
    }
    assert(source_proof::separated(states[0].state,1)) by {
        assert forall|n:usize| s::registered(states[0].state,n) && n!=1 implies dep::declarations(states[0].state,n).disjoint(states[0].state.control.fibers[1usize].provisions) by {
            if n==0 {} else {assert(n==2);}
        }
    }
    assert(source_proof::fragment(programs(),states,steps,2,1)) by {
        assert forall|i:int| 0<=i<steps.len() && g::landing(states[i],states[i+1],steps[i].1) implies {
            let node=programs()(steps[i].0)(states[i].current[steps[i].0].unwrap());source_proof::table_node(node) && (steps[i].0!=1 ==> crate::shared_replay::operational_mixed(node))
        } by {if i==1 {} else if i==2 {} else {assert(i==3);}}
        assert forall|i:int| #![trigger steps[i]] 0<=i<steps.len() implies {
            let label=steps[i];label.1!=r::Rule::Insert && label.1!=r::Rule::Remove
                && (label.1==r::Rule::Unload ==> label.0!=1 && fu::tracked_tokens(states[i].history,states[i].state.accumulators[label.0],2,label.0))
        } by {}
    }
    assert(!old::owner_window(states,steps,1)) by {assert(g::landing(states[2],states[3],steps[2].1));assert(steps[2].0==2);}
    assert(states.last().state.accumulators[2usize] =~= seq![1nat,3nat]);assert(states.last().state.accumulators[1usize] =~= seq![2nat,4nat]);
    assert(old::old_tokens(programs(),states.last().history,states.last().state.accumulators[2usize],states.last().history.len(),2)) by {
        assert forall|i:int| #![trigger states.last().state.accumulators[2usize][i]] 0<=i<states.last().state.accumulators[2usize].len() implies {
            let token=states.last().state.accumulators[2usize][i];let e=states.last().history[token as int];
            token<states.last().history.len() && g::owner(e.landed.receipt)==2 && crate::shared_replay::operational_mixed(programs()(2)(e.iterator))
        } by {if i==0 {} else {assert(i==1);}}
    }
    assert(!old::old_tokens(programs(),states.last().history,states.last().state.accumulators[2usize],2,2)) by {assert(states.last().state.accumulators[2usize][1]==3);}
    assert(!fu::tracked_tokens(states.last().history,states.last().state.accumulators[2usize],2,2)) by {assert(states.last().state.accumulators[2usize][0]==1);}
    reveal_with_fuel(g::restore,3);assert(g::step(lib,programs(),states.last(),g::unload(states.last(),2),2,r::Rule::Unload));
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn deletion_shape()
    ensures target()==surviving(),
{
    reveal(source);reveal(surviving);reveal_with_fuel(deletion::delete,9);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn target_shape()
    ensures target().len()==5,target().last().history.len()==3,target().last().history[1]==source().first().history[1],
        target().last().state.accumulators[2usize]==seq![1nat,2nat],
        history::index(source().last().history,2,1,1)==1,history::index(source().last().history,2,1,3)==2,
        g::unload(target().last(),2).state.tables[0usize][ex::key(0)]==10,g::unload(target().last(),2).state.tables[1usize].is_empty(),
        s::registered(g::unload(target().last(),2).state,0),g::unload(target().last(),2).state.tables[0usize].dom().contains(ex::key(0)),
{
    actual_setup();actual_source();deletion_shape();reveal(source);reveal(surviving);reveal(setup);
    reveal_with_fuel(history::index,6);reveal_with_fuel(g::restore,3);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn closed_transport()
    ensures {
        let states=source();let kept=target();let foreign=g::unload(states.last(),2);
        let terminal=g::unload(foreign,1);let out=g::unload(kept.last(),2);
        &&& kept.first()==states.first()
        &&& g::step(ex::library(),programs(),foreign,terminal,1,r::Rule::Unload)
        &&& g::execution(ex::library(),programs(),states.push(foreign).push(terminal),labels().push((2usize,r::Rule::Unload)).push((1usize,r::Rule::Unload)))
        &&& g::step(ex::library(),programs(),kept.last(),out,2,r::Rule::Unload)
        &&& g::execution(ex::library(),programs(),kept.push(out),sh::labels_without(labels(),1).push((2usize,r::Rule::Unload)))
        &&& g::well_formed(ex::library(),programs(),terminal) && g::well_formed(ex::library(),programs(),out)
        &&& terminal.state.control==out.state.control && obs::tables_related(ex::equality(),terminal.state,out.state)
        &&& terminal.state.tables[1usize].is_empty() && out.state.tables[1usize].is_empty()
    },
{
    actual_setup();actual_source();sh::example_interface();
    let states=source();let kept=target();let foreign=g::unload(states.last(),2);
    mixed::closed_deletion(ex::equality(),ex::library(),programs(),setup(),setup_labels(),states,labels(),foreign,1,2);
    let out=g::unload(kept.last(),2);let kept_labels=sh::labels_without(labels(),1);let i=kept_labels.len() as int;
    assert(kept.len()==i+1);assert(kept.push(out)[i]==kept.last());assert(kept.push(out)[i+1]==out);
    assert(kept_labels.push((2usize,r::Rule::Unload))[i]==(2usize,r::Rule::Unload));
}

/// One same-episode journal crosses the cut, so neither old-only nor new-only
/// token bounds apply. Every call and both complete terminal traces are real.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn actual_mixed_age_unload()
    ensures {
        let states=source();let kept=target();let foreign=g::unload(states.last(),2);
        let terminal=g::unload(foreign,1);let out=g::unload(kept.last(),2);let tokens=states.last().state.accumulators[2usize];
        &&& g::execution(ex::library(),programs(),setup(),setup_labels()) && setup().first()==g::empty::<int,nat>()
        &&& setup().last()==states.first() && kept.first()==states.first()
        &&& states.first().state.control.fibers[2usize].phase==Phase::Loading && states.first().current[2usize]==Some(1nat)
        &&& states.first().state.accumulators[2usize]==seq![1nat] && tokens==seq![1nat,3nat]
        &&& mixed::operational_tokens(programs(),states.last().history,tokens,2)
        &&& !old::old_tokens(programs(),states.last().history,tokens,2,2) && !fu::tracked_tokens(states.last().history,tokens,2,2)
        &&& kept.last().state.accumulators[2usize]==seq![1nat,2nat]
        &&& history::index(states.last().history,2,1,1)==1 && history::index(states.last().history,2,1,3)==2
        &&& g::step(ex::library(),programs(),states.last(),foreign,2,r::Rule::Unload)
        &&& g::step(ex::library(),programs(),foreign,terminal,1,r::Rule::Unload)
        &&& g::execution(ex::library(),programs(),states.push(foreign).push(terminal),labels().push((2usize,r::Rule::Unload)).push((1usize,r::Rule::Unload)))
        &&& g::step(ex::library(),programs(),kept.last(),out,2,r::Rule::Unload)
        &&& g::execution(ex::library(),programs(),kept.push(out),sh::labels_without(labels(),1).push((2usize,r::Rule::Unload)))
        &&& g::well_formed(ex::library(),programs(),terminal) && g::well_formed(ex::library(),programs(),out)
        &&& terminal.state.control==out.state.control && obs::tables_related(ex::equality(),terminal.state,out.state)
        &&& terminal.state.tables[0usize][ex::key(0)]==10 && out.state.tables[0usize][ex::key(0)]==10
        &&& terminal.state.tables[1usize].is_empty() && out.state.tables[1usize].is_empty()
        &&& states.first().history.len()==2 && terminal.history.len()==5 && out.history.len()==3
        &&& foreign.state.tables[0usize][ex::key(0)]==15 && foreign.state.tables[1usize][ex::key(1)]==99
    },
{
    actual_setup();actual_source();target_shape();closed_transport();
    let states=source();let kept=target();let foreign=g::unload(states.last(),2);
    let terminal=g::unload(foreign,1);let out=g::unload(kept.last(),2);
    assert(s::registered(terminal.state,0));assert(terminal.state.tables[0usize].dom()==out.state.tables[0usize].dom());
    assert(ex::equality()(ex::key(0),terminal.state.tables[0usize][ex::key(0)],out.state.tables[0usize][ex::key(0)]));
    assert(terminal.history==states.last().history);assert(out.history==kept.last().history);
}

} // verus!
