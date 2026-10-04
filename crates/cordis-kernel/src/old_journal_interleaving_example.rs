//! Old and newly minted foreign journals in one real interleaved owner episode.
//!
//! Actor 2's +7 receipt predates the cut. Actor 3 loads between the owner's
//! Provision and Operation, then unloads its new receipt before actor 2 consumes
//! its old one. Deletion retains old token 1 and compresses new token 3 to 2.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, dependent_lift as dep, foreign_unload as fu, grammar_lift as lift,
    mixed_grammar as g, mixed_observational_runs as obs, mixed_syntax as syntax,
    mixed_transposition as t, observational_lift as ol, old_journal_examples as earlier,
    old_journal_interleaving as interleaving, old_journal_unload as old,
    providing_owner_deletion as source_proof, providing_owner_examples as base,
    providing_owner_execution as deletion, recovery_examples as ex, refinement as r,
    semantics as s, shared_execution as sh, shared_unload_execution as history, Binding, Phase,
    Port,
};
use vstd::prelude::*;

verus! {

#[verifier::opaque]
pub open spec fn setup()->Seq<g::Configuration<int,bool>> {
    earlier::setup().push(t::insert(earlier::setup().last(),3,None,ex::provided(0),ISet::empty(),true))
}
pub open spec fn setup_labels()->Seq<(usize,r::Rule)> {
    earlier::setup_labels().push((3usize,r::Rule::Insert))
}
#[verifier::opaque]
pub open spec fn source()->Seq<g::Configuration<int,bool>> {
    let cut=setup().last();
    let a1=g::edit(cut,1,Phase::Loading,sh::example_view(),Some(false),Seq::empty());
    let a2=g::land(ex::library(),base::programs(),a1,1,Phase::Loading);
    let a3=g::edit(a2,3,Phase::Loading,sh::example_view(),Some(true),Seq::empty());
    let a4=g::land(ex::library(),base::programs(),a3,3,Phase::Active);
    let a5=g::land(ex::library(),base::programs(),a4,1,Phase::Active);
    let a6=sh::retire(a5,3);
    let a7=g::edit(a6,3,Phase::Unloading,sh::example_view(),None,a6.state.accumulators[3usize]);
    let a8=g::unload(a7,3);
    let a9=sh::retire(a8,1);
    let a10=g::edit(a9,1,Phase::Unloading,sh::example_view(),None,a9.state.accumulators[1usize]);
    let a11=sh::retire(a10,2);
    let a12=g::edit(a11,2,Phase::Unloading,sh::example_view(),None,a11.state.accumulators[2usize]);
    seq![cut,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12]
}
pub open spec fn labels()->Seq<(usize,r::Rule)> {
    seq![(1usize,r::Rule::Begin),(1usize,r::Rule::Iter),(3usize,r::Rule::Begin),(3usize,r::Rule::Finish),
        (1usize,r::Rule::Finish),(3usize,r::Rule::Retire),(3usize,r::Rule::Leave),(3usize,r::Rule::Unload),
        (1usize,r::Rule::Retire),(1usize,r::Rule::Leave),(2usize,r::Rule::Retire),(2usize,r::Rule::Leave)]
}
pub open spec fn target()->Seq<g::Configuration<int,bool>> {
    deletion::delete(ex::library(),base::programs(),source(),labels(),1)
}
#[verifier::opaque]
pub open spec fn surviving()->Seq<g::Configuration<int,bool>> {
    let cut=setup().last();
    let a1=g::edit(cut,3,Phase::Loading,sh::example_view(),Some(true),Seq::empty());
    let a2=g::land(ex::library(),base::programs(),a1,3,Phase::Active);
    let a3=sh::retire(a2,3);
    let a4=g::edit(a3,3,Phase::Unloading,a3.state.control.fibers[3usize].committed,None,a3.state.accumulators[3usize]);
    let a5=g::unload(a4,3);let a6=sh::retire(a5,1);let a7=sh::retire(a6,2);
    let a8=g::edit(a7,2,Phase::Unloading,a7.state.control.fibers[2usize].committed,None,a7.state.accumulators[2usize]);
    seq![cut,a1,a2,a3,a4,a5,a6,a7,a8]
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
    earlier::actual_setup();sh::example_interface();reveal(setup);reveal(source);reveal(earlier::setup);reveal(base::trace);
    let lib=ex::library();let programs=base::programs();let input=earlier::setup().last();let cut=setup().last();
    syntax::constructor_member(lib,programs,3,ex::provided(0),ISet::empty(),true);
    assert(ex::provided(0).union(ISet::empty()) =~= ex::provided(0));
    let previous=earlier::setup()[6];
    assert(earlier::setup_labels().len()==7);
    assert(earlier::setup_labels()[6]==(2usize,r::Rule::Finish));
    assert(earlier::setup()[7]==input);
    assert(g::step(lib,programs,earlier::setup()[6],earlier::setup()[7],earlier::setup_labels()[6].0,earlier::setup_labels()[6].1));
    assert(g::step(lib,programs,previous,input,2,r::Rule::Finish));
    assert(!s::registered(input.state,3));
    assert forall|n:usize,k:Port| s::registered(input.state,n) && input.state.control.fibers[n].provisions.contains(k) implies !ISet::<Port>::empty().contains(k) by {}
    assert(syntax::member(lib,programs,3,ex::provided(0).union(ISet::empty()),ISet::empty(),true));
    t::insertion_step(lib,programs,input,3,None,ex::provided(0),ISet::empty(),true);
    ol::configuration_preservation(ex::equality(),lib,programs,input,cut,3,r::Rule::Insert);
    let states=setup();let steps=setup_labels();
    assert forall|i:int| 0<=i<steps.len() implies g::step(lib,programs,states[i],states[i+1],steps[i].0,steps[i].1) by {
        if i<earlier::setup_labels().len() {
            assert(states[i]==earlier::setup()[i]);assert(states[i+1]==earlier::setup()[i+1]);
            assert(steps[i]==earlier::setup_labels()[i]);
        } else {assert(i==earlier::setup_labels().len());}
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn actual_source()
    ensures g::execution(ex::library(),base::programs(),source(),labels()),
        source_proof::separated(source().first().state,1),source_proof::fragment(base::programs(),source(),labels(),2,1),
        !old::owner_window(source(),labels(),1),
        g::landing(source()[3],source()[4],r::Rule::Finish),labels()[3]==(3usize,r::Rule::Finish),
        source()[7].state.accumulators[3usize]==seq![3nat],g::step(ex::library(),base::programs(),source()[7],source()[8],3,r::Rule::Unload),
        source().last().history.len()==5,source().last().state.accumulators[2usize]==seq![1nat],
        old::old_tokens(base::programs(),source().last().history,source().last().state.accumulators[2usize],2,2),
        !fu::tracked_tokens(source().last().history,source().last().state.accumulators[2usize],2,2),
        source().last().state.control.fibers[1usize].phase==Phase::Unloading,
        source().last().state.tables[0usize][ex::key(0)]==22,source().last().state.tables[1usize][ex::key(1)]==99,
        g::step(ex::library(),base::programs(),source().last(),g::unload(source().last(),2),2,r::Rule::Unload),
        g::unload(source().last(),2).state.tables[0usize][ex::key(0)]==15,
        g::unload(source().last(),2).state.tables[1usize][ex::key(1)]==99,
        s::registered(g::unload(source().last(),2).state,0),g::unload(source().last(),2).state.tables[0usize].dom().contains(ex::key(0)),
{
    actual_setup();reveal(source);reveal(setup);reveal(earlier::setup);reveal(base::trace);sh::example_interface();
    let lib=ex::library();let programs=base::programs();let states=source();let steps=labels();
    sh::example_target(states[0].state,1);assert(g::step(lib,programs,states[0],states[1],1,r::Rule::Begin));
    assert(g::step(lib,programs,states[1],states[2],1,r::Rule::Iter));
    sh::example_target(states[2].state,3);assert(g::step(lib,programs,states[2],states[3],3,r::Rule::Begin));
    assert(lift::names_key(Binding {key:0,realm:0,provider:0},ex::key(0)));
    assert(states[3].state.control.fibers[3usize].committed.contains(Binding {key:0,realm:0,provider:0}));
    assert(exists|b:Binding| states[3].state.control.fibers[3usize].committed.contains(b) && lift::names_key(b,ex::key(0)));
    assert(lift::resolve(states[3].state,3,ex::key(0))==Some(0usize));
    assert(g::step(lib,programs,states[3],states[4],3,r::Rule::Finish));
    assert(states[4].state.control.fibers[1usize].committed.contains(Binding {key:0,realm:0,provider:0}));
    assert(exists|b:Binding| states[4].state.control.fibers[1usize].committed.contains(b) && lift::names_key(b,ex::key(0)));
    assert(lift::resolve(states[4].state,1,ex::key(0))==Some(0usize));
    assert(g::step(lib,programs,states[4],states[5],1,r::Rule::Finish));
    ch::concrete_child_retirement(states[5].state,3);assert(g::step(lib,programs,states[5],states[6],3,r::Rule::Retire));
    assert(g::step(lib,programs,states[6],states[7],3,r::Rule::Leave));
    assert(states[7].state.accumulators[3usize] =~= seq![3nat]);reveal_with_fuel(g::restore,2);
    assert(g::step(lib,programs,states[7],states[8],3,r::Rule::Unload));
    ch::concrete_child_retirement(states[8].state,1);assert(g::step(lib,programs,states[8],states[9],1,r::Rule::Retire));
    assert(g::step(lib,programs,states[9],states[10],1,r::Rule::Leave));
    ch::concrete_child_retirement(states[10].state,2);assert(g::step(lib,programs,states[10],states[11],2,r::Rule::Retire));
    assert(g::step(lib,programs,states[11],states[12],2,r::Rule::Leave));
    assert forall|i:int| 0<=i<steps.len() implies g::step(lib,programs,states[i],states[i+1],steps[i].0,steps[i].1) by {
        if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else if i==5 {} else if i==6 {} else if i==7 {} else if i==8 {} else if i==9 {} else if i==10 {} else {assert(i==11);}
    }
    assert(source_proof::separated(states[0].state,1)) by {
        assert forall|n:usize| s::registered(states[0].state,n) && n!=1 implies dep::declarations(states[0].state,n).disjoint(states[0].state.control.fibers[1usize].provisions) by {
            if n==0 {} else if n==2 {} else {assert(n==3);}
        }
    }
    assert(source_proof::fragment(programs,states,steps,2,1)) by {
        assert forall|i:int| 0<=i<steps.len() && g::landing(states[i],states[i+1],steps[i].1) implies {
            let node=programs(steps[i].0)(states[i].current[steps[i].0].unwrap());source_proof::table_node(node) && (steps[i].0!=1 ==> crate::shared_replay::operational_mixed(node))
        } by {if i==1 {} else if i==3 {} else {assert(i==4);}}
        assert forall|i:int| #![trigger steps[i]] 0<=i<steps.len() implies {
            let label=steps[i];label.1!=r::Rule::Insert && label.1!=r::Rule::Remove
                && (label.1==r::Rule::Unload ==> label.0!=1 && fu::tracked_tokens(states[i].history,states[i].state.accumulators[label.0],2,label.0))
        } by {if i==7 {assert(states[i].state.accumulators[3usize] =~= seq![3nat]);}}
    }
    assert(!old::owner_window(states,steps,1)) by {assert(steps[7].1==r::Rule::Unload);}
    assert(states.last().state.accumulators[2usize] =~= seq![1nat]);assert(states.last().history[1].iterator);
    assert(!fu::tracked_tokens(states.last().history,states.last().state.accumulators[2usize],2,2)) by {assert(states.last().state.accumulators[2usize][0]==1);}
    assert(g::step(lib,programs,states.last(),g::unload(states.last(),2),2,r::Rule::Unload));
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn deletion_shape()
    ensures target()==surviving(),
{
    actual_source();reveal(source);reveal(surviving);
    reveal_with_fuel(deletion::delete,13);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn target_shape()
    ensures target().len()==9,target().last().history.len()==3,
        target().last().history[1]==source().first().history[1],
        source()[7].state.accumulators[3usize]==seq![3nat],target()[4].state.accumulators[3usize]==seq![2nat],
        history::index(source().last().history,2,1,1)==1,history::index(source().last().history,2,1,3)==2,
        target().last().state.accumulators[2usize]==seq![1nat],target().last().state.tables[1usize].is_empty(),
        g::unload(target().last(),2).state.tables[0usize][ex::key(0)]==10,g::unload(target().last(),2).state.tables[1usize].is_empty(),
        s::registered(g::unload(target().last(),2).state,0),g::unload(target().last(),2).state.tables[0usize].dom().contains(ex::key(0)),
{
    actual_setup();actual_source();deletion_shape();reveal(surviving);reveal(source);reveal(setup);reveal(earlier::setup);reveal(base::trace);
    reveal_with_fuel(history::index,6);reveal_with_fuel(g::restore,2);
}

pub proof fn surviving_labels()
    ensures sh::labels_without(labels(),1)==seq![(3usize,r::Rule::Begin),(3usize,r::Rule::Finish),(3usize,r::Rule::Retire),(3usize,r::Rule::Leave),
        (3usize,r::Rule::Unload),(1usize,r::Rule::Retire),(2usize,r::Rule::Retire),(2usize,r::Rule::Leave)],
{
    reveal_with_fuel(sh::labels_without,13);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn closed_transport()
    ensures {
        let states=source();let steps=labels();let kept=target();
        let foreign=g::unload(states.last(),2);let terminal=g::unload(foreign,1);let out=g::unload(kept.last(),2);
        &&& kept.first()==states.first()
        &&& g::step(ex::library(),base::programs(),foreign,terminal,1,r::Rule::Unload)
        &&& g::execution(ex::library(),base::programs(),states.push(foreign).push(terminal),steps.push((2usize,r::Rule::Unload)).push((1usize,r::Rule::Unload)))
        &&& g::step(ex::library(),base::programs(),kept.last(),out,2,r::Rule::Unload)
        &&& g::execution(ex::library(),base::programs(),kept.push(out),sh::labels_without(steps,1).push((2usize,r::Rule::Unload)))
        &&& g::well_formed(ex::library(),base::programs(),terminal) && g::well_formed(ex::library(),base::programs(),out)
        &&& terminal.state.control==out.state.control && obs::tables_related(ex::equality(),terminal.state,out.state)
        &&& terminal.state.tables[1usize].is_empty() && out.state.tables[1usize].is_empty()
    },
{
    actual_setup();actual_source();sh::example_interface();
    let states=source();let steps=labels();let kept=target();let foreign=g::unload(states.last(),2);
    interleaving::closed_deletion(ex::equality(),ex::library(),base::programs(),setup(),setup_labels(),states,steps,foreign,1,2);
    let out=g::unload(kept.last(),2);let kept_labels=sh::labels_without(steps,1);let i=kept_labels.len() as int;
    assert(kept.len()==i+1);assert(kept.push(out)[i]==kept.last());assert(kept.push(out)[i+1]==out);
    assert(kept_labels.push((2usize,r::Rule::Unload))[i]==(2usize,r::Rule::Unload));
}

/// The fresh foreign landing and fresh Unload are inside the deletion window;
/// the old foreign Unload and final owner Unload close the complete execution.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn actual_interleaved_old_unload()
    ensures {
        let states=source();let steps=labels();let kept=target();
        let foreign=g::unload(states.last(),2);let terminal=g::unload(foreign,1);let out=g::unload(kept.last(),2);
        &&& g::execution(ex::library(),base::programs(),setup(),setup_labels()) && setup().first()==g::empty::<int,bool>() && setup().last()==states.first()
        &&& kept.first()==states.first()
        &&& !old::owner_window(states,steps,1)
        &&& g::landing(states[3],states[4],r::Rule::Finish) && steps[3]==(3usize,r::Rule::Finish)
        &&& g::step(ex::library(),base::programs(),states[7],states[8],3,r::Rule::Unload)
        &&& g::step(ex::library(),base::programs(),kept[4],kept[5],3,r::Rule::Unload)
        &&& states[7].state.accumulators[3usize]==seq![3nat] && kept[4].state.accumulators[3usize]==seq![2nat]
        &&& g::step(ex::library(),base::programs(),states.last(),foreign,2,r::Rule::Unload)
        &&& g::step(ex::library(),base::programs(),foreign,terminal,1,r::Rule::Unload)
        &&& g::execution(ex::library(),base::programs(),states.push(foreign).push(terminal),steps.push((2usize,r::Rule::Unload)).push((1usize,r::Rule::Unload)))
        &&& g::step(ex::library(),base::programs(),kept.last(),out,2,r::Rule::Unload)
        &&& g::execution(ex::library(),base::programs(),kept.push(out),sh::labels_without(steps,1).push((2usize,r::Rule::Unload)))
        &&& g::well_formed(ex::library(),base::programs(),terminal) && g::well_formed(ex::library(),base::programs(),out)
        &&& terminal.state.control==out.state.control && obs::tables_related(ex::equality(),terminal.state,out.state)
        &&& terminal.state.tables[0usize][ex::key(0)]==10 && out.state.tables[0usize][ex::key(0)]==10
        &&& terminal.state.tables[1usize].is_empty() && out.state.tables[1usize].is_empty()
        &&& states.first().history.len()==2 && terminal.history.len()==5 && out.history.len()==3
        &&& states.last().state.accumulators[2usize]==seq![1nat] && kept.last().state.accumulators[2usize]==seq![1nat]
        &&& history::index(states.last().history,2,1,1)==1 && history::index(states.last().history,2,1,3)==2
        &&& foreign.state.tables[0usize][ex::key(0)]==15 && foreign.state.tables[1usize][ex::key(1)]==99
    },
{
    actual_setup();actual_source();target_shape();closed_transport();surviving_labels();
    let states=source();let steps=labels();let kept=target();let foreign=g::unload(states.last(),2);
    let terminal=g::unload(foreign,1);let out=g::unload(kept.last(),2);
    assert(s::registered(terminal.state,0));assert(terminal.state.tables[0usize].dom()==out.state.tables[0usize].dom());
    assert(ex::equality()(ex::key(0),terminal.state.tables[0usize][ex::key(0)],out.state.tables[0usize][ex::key(0)]));
    assert(sh::labels_without(steps,1)[4]==(3usize,r::Rule::Unload));
    let complete=kept.push(out);let complete_labels=sh::labels_without(steps,1).push((2usize,r::Rule::Unload));
    assert(complete[4]==kept[4]);assert(complete[5]==kept[5]);assert(complete_labels[4]==(3usize,r::Rule::Unload));
    assert(g::step(ex::library(),base::programs(),complete[4],complete[5],complete_labels[4].0,complete_labels[4].1));
    assert(g::step(ex::library(),base::programs(),kept[4],kept[5],3,r::Rule::Unload));
    assert(terminal.history==states.last().history);assert(out.history==kept.last().history);
}

} // verus!
