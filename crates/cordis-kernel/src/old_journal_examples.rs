//! A real old journal survives deletion of a later providing-owner episode.
//!
//! The foreign +7 receipt is minted before the cut. The deleted owner then
//! publishes a private key and adds 5 to the shared key. The same old token 1
//! is consumed by both actual foreign Unloads, without offset subtraction.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, dependent_lift as dep, foreign_unload as fu, grammar_lift as lift,
    mixed_grammar as g, observational_lift as ol, old_journal_unload as old,
    providing_owner_deletion as source_proof, providing_owner_examples as base,
    providing_owner_execution as deletion, providing_owner_transport as target_proof,
    recovery_examples as ex, refinement as r, semantics as s, shared_execution as sh,
    shared_unload_execution as history, Binding, Phase,
};
use vstd::prelude::*;

verus! {

#[verifier::opaque]
pub open spec fn setup()->Seq<g::Configuration<int,bool>> {
    let initial=base::bootstrap().last();
    let loading=g::edit(initial,2,Phase::Loading,sh::example_view(),Some(true),Seq::empty());
    base::bootstrap().push(loading).push(g::land(ex::library(),base::programs(),loading,2,Phase::Active))
}
pub open spec fn setup_labels()->Seq<(usize,r::Rule)> {
    base::bootstrap_labels().push((2usize,r::Rule::Begin)).push((2usize,r::Rule::Finish))
}
#[verifier::opaque]
pub open spec fn source()->Seq<g::Configuration<int,bool>> {
    let cut=setup().last();
    let a1=g::edit(cut,1,Phase::Loading,sh::example_view(),Some(false),Seq::empty());
    let a2=g::land(ex::library(),base::programs(),a1,1,Phase::Loading);
    let a3=g::land(ex::library(),base::programs(),a2,1,Phase::Active);
    let a4=sh::retire(a3,1);
    let a5=g::edit(a4,1,Phase::Unloading,sh::example_view(),None,a4.state.accumulators[1usize]);
    let a6=sh::retire(a5,2);
    let a7=g::edit(a6,2,Phase::Unloading,sh::example_view(),None,a6.state.accumulators[2usize]);
    seq![cut,a1,a2,a3,a4,a5,a6,a7]
}
pub open spec fn labels()->Seq<(usize,r::Rule)> {
    seq![(1usize,r::Rule::Begin),(1usize,r::Rule::Iter),(1usize,r::Rule::Finish),
        (1usize,r::Rule::Retire),(1usize,r::Rule::Leave),(2usize,r::Rule::Retire),(2usize,r::Rule::Leave)]
}
pub open spec fn target()->Seq<g::Configuration<int,bool>> {
    deletion::delete(ex::library(),base::programs(),source(),labels(),1)
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn actual_setup()
    ensures g::execution(ex::library(),base::programs(),setup(),setup_labels()),setup().first()==g::empty::<int,bool>(),
        setup().last()==source().first(),g::well_formed(ex::library(),base::programs(),source().first()),
        source().first().history.len()==2,source().first().state.tables[0usize][ex::key(0)]==17,
        source().first().state.accumulators[2usize]==seq![1nat],
        source().first().state.control.fibers[1usize].phase==Phase::Inactive,source().first().state.tables[1usize].is_empty(),
{
    reveal(setup);reveal(source);reveal(base::trace);base::bootstrap_execution();sh::example_interface();
    let lib=ex::library();let programs=base::programs();let initial=base::bootstrap().last();
    let loading=g::edit(initial,2,Phase::Loading,sh::example_view(),Some(true),Seq::empty());
    let cut=g::land(lib,programs,loading,2,Phase::Active);
    sh::example_target(initial.state,2);assert(g::step(lib,programs,initial,loading,2,r::Rule::Begin));
    assert(lift::names_key(Binding {key:0,realm:0,provider:0},ex::key(0)));
    assert(loading.state.control.fibers[2usize].committed.contains(Binding {key:0,realm:0,provider:0}));
    assert(exists|b:Binding| loading.state.control.fibers[2usize].committed.contains(b) && lift::names_key(b,ex::key(0)));
    assert(lift::resolve(loading.state,2,ex::key(0))==Some(0usize));
    assert(g::step(lib,programs,loading,cut,2,r::Rule::Finish));
    ol::configuration_preservation(ex::equality(),lib,programs,initial,loading,2,r::Rule::Begin);
    ol::configuration_preservation(ex::equality(),lib,programs,loading,cut,2,r::Rule::Finish);
    assert(cut.state.accumulators[2usize] =~= seq![1nat]);
    let states=setup();let steps=setup_labels();
    assert forall|i:int| 0<=i<steps.len() implies g::step(lib,programs,states[i],states[i+1],steps[i].0,steps[i].1) by {
        if i<base::bootstrap_labels().len() {
            assert(states[i]==base::bootstrap()[i]);assert(states[i+1]==base::bootstrap()[i+1]);
            assert(steps[i]==base::bootstrap_labels()[i]);
        } else if i==base::bootstrap_labels().len() {} else {assert(i==base::bootstrap_labels().len()+1);}
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn actual_source()
    ensures g::execution(ex::library(),base::programs(),source(),labels()),
        source_proof::separated(source().first().state,1),source_proof::fragment(base::programs(),source(),labels(),2,1),old::owner_window(source(),labels(),1),
        source().last().history.len()==4,source().last().state.accumulators[2usize]==seq![1nat],
        old::old_tokens(base::programs(),source().last().history,source().last().state.accumulators[2usize],2,2),
        !fu::tracked_tokens(source().last().history,source().last().state.accumulators[2usize],2,2),
        source().last().state.tables[0usize][ex::key(0)]==22,source().last().state.tables[1usize][ex::key(1)]==99,
        g::step(ex::library(),base::programs(),source().last(),g::unload(source().last(),2),2,r::Rule::Unload),
        g::unload(source().last(),2).state.tables[0usize][ex::key(0)]==15,
        g::unload(source().last(),2).state.tables[1usize][ex::key(1)]==99,
{
    actual_setup();reveal(source);reveal(setup);reveal(base::trace);sh::example_interface();
    let lib=ex::library();let programs=base::programs();let states=source();let steps=labels();
    sh::example_target(states[0].state,1);assert(g::step(lib,programs,states[0],states[1],1,r::Rule::Begin));
    assert(g::step(lib,programs,states[1],states[2],1,r::Rule::Iter));
    assert(lift::names_key(Binding {key:0,realm:0,provider:0},ex::key(0)));
    assert(states[2].state.control.fibers[1usize].committed.contains(Binding {key:0,realm:0,provider:0}));
    assert(exists|b:Binding| states[2].state.control.fibers[1usize].committed.contains(b) && lift::names_key(b,ex::key(0)));
    assert(lift::resolve(states[2].state,1,ex::key(0))==Some(0usize));
    assert(g::step(lib,programs,states[2],states[3],1,r::Rule::Finish));
    ch::concrete_child_retirement(states[3].state,1);assert(g::step(lib,programs,states[3],states[4],1,r::Rule::Retire));
    assert(g::step(lib,programs,states[4],states[5],1,r::Rule::Leave));
    ch::concrete_child_retirement(states[5].state,2);assert(g::step(lib,programs,states[5],states[6],2,r::Rule::Retire));
    assert(g::step(lib,programs,states[6],states[7],2,r::Rule::Leave));
    assert forall|i:int| 0<=i<steps.len() implies g::step(lib,programs,states[i],states[i+1],steps[i].0,steps[i].1) by {
        if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else if i==5 {} else {assert(i==6);}
    }
    assert(source_proof::separated(states[0].state,1)) by {
        assert forall|n:usize| s::registered(states[0].state,n) && n!=1 implies dep::declarations(states[0].state,n).disjoint(states[0].state.control.fibers[1usize].provisions) by {
            if n==0 {} else {assert(n==2);}
        }
    }
    assert(source_proof::fragment(programs,states,steps,2,1)) by {
        assert forall|i:int| 0<=i<steps.len() && g::landing(states[i],states[i+1],steps[i].1) implies {
            let node=programs(steps[i].0)(states[i].current[steps[i].0].unwrap());source_proof::table_node(node) && (steps[i].0!=1 ==> crate::shared_replay::operational_mixed(node))
        } by {if i==1 {} else {assert(i==2);}}
        assert forall|i:int| #![trigger steps[i]] 0<=i<steps.len() implies {
            let label=steps[i];label.1!=r::Rule::Insert && label.1!=r::Rule::Remove
                && (label.1==r::Rule::Unload ==> label.0!=1 && fu::tracked_tokens(states[i].history,states[i].state.accumulators[label.0],2,label.0))
        } by {}
    }
    assert(old::owner_window(states,steps,1)) by {
        assert forall|i:int| #![trigger steps[i]] 0<=i<steps.len() implies steps[i].1!=r::Rule::Unload
            && (g::landing(states[i],states[i+1],steps[i].1) ==> steps[i].0==1) by {if i<5 {} else if i==5 {} else {assert(i==6);}}
    }
    assert(states.last().state.accumulators[2usize] =~= seq![1nat]);
    assert(states.last().history[1].iterator);
    assert(!fu::tracked_tokens(states.last().history,states.last().state.accumulators[2usize],2,2)) by {
        assert(states.last().state.accumulators[2usize][0]==1);
    }
    reveal_with_fuel(g::restore,2);
    assert(g::step(lib,programs,states.last(),g::unload(states.last(),2),2,r::Rule::Unload));
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn target_shape()
    ensures target().len()==4,target().last().history.len()==2,target().last().history==source().first().history,
        target().last().state.accumulators[2usize]==seq![1nat],history::index(source().last().history,2,1,1)==1,
        target().last().state.tables[0usize][ex::key(0)]==17,target().last().state.tables[1usize].is_empty(),
        g::unload(target().last(),2).state.tables[0usize][ex::key(0)]==10,
        g::unload(target().last(),2).state.tables[1usize].is_empty(),
{
    actual_setup();actual_source();reveal(source);reveal(setup);reveal(base::trace);
    reveal_with_fuel(deletion::delete,8);reveal(history::index);
    reveal_with_fuel(g::restore,2);
}

/// Both Unloads are legal executions. The surviving old token is 1 on both
/// sides, below the cut offset 2; only the two later owner entries disappear.
pub proof fn actual_old_unload()
    ensures {
        let out=g::unload(target().last(),2);let source_out=g::unload(source().last(),2);
        &&& g::execution(ex::library(),base::programs(),setup(),setup_labels()) && setup().first()==g::empty::<int,bool>() && setup().last()==source().first()
        &&& g::execution(ex::library(),base::programs(),source(),labels())
        &&& g::step(ex::library(),base::programs(),source().last(),source_out,2,r::Rule::Unload)
        &&& g::execution(ex::library(),base::programs(),target().push(out),sh::labels_without(labels(),1).push((2usize,r::Rule::Unload)))
        &&& g::step(ex::library(),base::programs(),target().last(),out,2,r::Rule::Unload) && g::well_formed(ex::library(),base::programs(),out)
        &&& target_proof::related(ex::equality(),source_out,out,2,1)
        &&& source().first().history.len()==2 && source().last().history.len()==4 && out.history.len()==2
        &&& source().last().state.accumulators[2usize]==seq![1nat] && target().last().state.accumulators[2usize]==seq![1nat]
        &&& history::index(source().last().history,2,1,1)==1
        &&& source_out.state.tables[0usize][ex::key(0)]==15 && source_out.state.tables[1usize][ex::key(1)]==99
        &&& out.state.tables[0usize][ex::key(0)]==10 && out.state.tables[1usize].is_empty()
    },
{
    actual_setup();actual_source();target_shape();sh::example_interface();
    old::delete_with_old_unload(ex::equality(),ex::library(),base::programs(),setup(),setup_labels(),source(),labels(),g::unload(source().last(),2),1,2);
}

} // verus!
