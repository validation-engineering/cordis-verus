//! A mixed-age foreign Unload occurs inside a still-loading owner episode.
//!
//! The owner's actual Operation runs after that cleanup. This trace therefore
//! requires continued replay past an internal old receipt, rather than merely
//! appending an old cleanup after an otherwise supported source window.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, dependent_lift as dep, foreign_unload as fu, grammar_lift as lift,
    internal_old_unload as internal, mixed_age_unload as mixed, mixed_age_unload_example as age,
    mixed_grammar as g, mixed_observational_runs as obs, providing_owner_deletion as source_proof,
    providing_owner_execution as deletion, recovery_examples as ex, refinement as r,
    semantics as s, shared_execution as sh, shared_unload_execution as history, Binding, Phase,
};
use vstd::prelude::*;

verus! {

pub open spec fn setup()->Seq<g::Configuration<int,nat>> {age::setup()}
pub open spec fn setup_labels()->Seq<(usize,r::Rule)> {age::setup_labels()}
#[verifier::opaque]
pub open spec fn source()->Seq<g::Configuration<int,nat>> {
    let cut=setup().last();
    let a1=g::edit(cut,1,Phase::Loading,sh::example_view(),Some(0nat),Seq::empty());
    let a2=g::land(ex::library(),age::programs(),a1,1,Phase::Loading);
    let a3=g::land(ex::library(),age::programs(),a2,2,Phase::Active);
    let a4=sh::retire(a3,2);
    let a5=g::edit(a4,2,Phase::Unloading,sh::example_view(),None,a4.state.accumulators[2usize]);
    let a6=g::unload(a5,2);
    let a7=g::land(ex::library(),age::programs(),a6,1,Phase::Active);
    let a8=sh::retire(a7,1);
    let a9=g::edit(a8,1,Phase::Unloading,sh::example_view(),None,a8.state.accumulators[1usize]);
    seq![cut,a1,a2,a3,a4,a5,a6,a7,a8,a9]
}
pub open spec fn labels()->Seq<(usize,r::Rule)> {
    seq![(1usize,r::Rule::Begin),(1usize,r::Rule::Iter),(2usize,r::Rule::Finish),(2usize,r::Rule::Retire),
        (2usize,r::Rule::Leave),(2usize,r::Rule::Unload),(1usize,r::Rule::Finish),(1usize,r::Rule::Retire),(1usize,r::Rule::Leave)]
}
pub open spec fn target()->Seq<g::Configuration<int,nat>> {
    deletion::delete(ex::library(),age::programs(),source(),labels(),1)
}
#[verifier::opaque]
pub open spec fn surviving()->Seq<g::Configuration<int,nat>> {
    let cut=setup().last();let a1=g::land(ex::library(),age::programs(),cut,2,Phase::Active);
    let a2=sh::retire(a1,2);
    let a3=g::edit(a2,2,Phase::Unloading,a2.state.control.fibers[2usize].committed,None,a2.state.accumulators[2usize]);
    let a4=g::unload(a3,2);let a5=sh::retire(a4,1);
    seq![cut,a1,a2,a3,a4,a5]
}

pub proof fn actual_setup()
    ensures g::execution(ex::library(),age::programs(),setup(),setup_labels()),setup().first()==g::empty::<int,nat>(),setup().last()==source().first(),
        g::well_formed(ex::library(),age::programs(),source().first()),
        source().first().history.len()==2,source().first().state.tables[0usize][ex::key(0)]==17,
        source().first().state.accumulators[2usize]==seq![1nat],source().first().current[2usize]==Some(1nat),
        source().first().state.control.fibers[2usize].phase==Phase::Loading,
        source().first().state.control.fibers[1usize].phase==Phase::Inactive,source().first().state.tables[1usize].is_empty(),
{
    age::actual_setup();reveal(source);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn actual_source()
    ensures g::execution(ex::library(),age::programs(),source(),labels()),source_proof::separated(source().first().state,1),
        !source_proof::fragment(age::programs(),source(),labels(),2,1),
        source()[5].state.accumulators[2usize]==seq![1nat,3nat],
        mixed::operational_tokens(age::programs(),source()[5].history,source()[5].state.accumulators[2usize],2),
        !fu::tracked_tokens(source()[5].history,source()[5].state.accumulators[2usize],2,2),
        g::step(ex::library(),age::programs(),source()[5],source()[6],2,r::Rule::Unload),
        source()[6].state.control.fibers[1usize].phase==Phase::Loading,source()[6].current[1usize]==Some(1nat),
        g::step(ex::library(),age::programs(),source()[6],source()[7],1,r::Rule::Finish),g::landing(source()[6],source()[7],r::Rule::Finish),
        source()[6].state.tables[0usize][ex::key(0)]==10,source()[7].state.tables[0usize][ex::key(0)]==15,
        source().last().history.len()==5,source().last().state.accumulators[1usize]==seq![2nat,4nat],source().last().state.accumulators[2usize].len()==0,
        source().last().state.control.fibers[1usize].phase==Phase::Unloading,
        source().last().state.tables[0usize][ex::key(0)]==15,source().last().state.tables[1usize][ex::key(1)]==99,
        s::registered(source().last().state,0),source().last().state.tables[0usize].dom().contains(ex::key(0)),
{
    actual_setup();sh::example_interface();reveal(source);reveal(age::setup);
    let lib=ex::library();let programs=age::programs();let states=source();let steps=labels();
    sh::example_target(states[0].state,1);assert(g::step(lib,programs,states[0],states[1],1,r::Rule::Begin));
    assert(g::step(lib,programs,states[1],states[2],1,r::Rule::Iter));
    assert(lift::names_key(Binding {key:0,realm:0,provider:0},ex::key(0)));
    assert(states[2].state.control.fibers[2usize].committed.contains(Binding {key:0,realm:0,provider:0}));
    assert(exists|b:Binding| states[2].state.control.fibers[2usize].committed.contains(b) && lift::names_key(b,ex::key(0)));
    assert(lift::resolve(states[2].state,2,ex::key(0))==Some(0usize));assert(g::step(lib,programs,states[2],states[3],2,r::Rule::Finish));
    ch::concrete_child_retirement(states[3].state,2);assert(g::step(lib,programs,states[3],states[4],2,r::Rule::Retire));
    assert(g::step(lib,programs,states[4],states[5],2,r::Rule::Leave));
    assert(states[5].state.accumulators[2usize] =~= seq![1nat,3nat]);reveal_with_fuel(g::restore,3);
    assert(g::step(lib,programs,states[5],states[6],2,r::Rule::Unload));
    assert(states[6].state.control.fibers[1usize].committed.contains(Binding {key:0,realm:0,provider:0}));
    assert(exists|b:Binding| states[6].state.control.fibers[1usize].committed.contains(b) && lift::names_key(b,ex::key(0)));
    assert(lift::resolve(states[6].state,1,ex::key(0))==Some(0usize));assert(g::step(lib,programs,states[6],states[7],1,r::Rule::Finish));
    ch::concrete_child_retirement(states[7].state,1);assert(g::step(lib,programs,states[7],states[8],1,r::Rule::Retire));
    assert(g::step(lib,programs,states[8],states[9],1,r::Rule::Leave));
    assert forall|i:int| 0<=i<steps.len() implies g::step(lib,programs,states[i],states[i+1],steps[i].0,steps[i].1) by {
        if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else if i==5 {} else if i==6 {} else if i==7 {} else {assert(i==8);}
    }
    assert(source_proof::separated(states[0].state,1)) by {
        assert forall|n:usize| s::registered(states[0].state,n) && n!=1 implies dep::declarations(states[0].state,n).disjoint(states[0].state.control.fibers[1usize].provisions) by {
            if n==0 {} else {assert(n==2);}
        }
    }
    assert(mixed::operational_tokens(programs,states[5].history,states[5].state.accumulators[2usize],2)) by {
        assert forall|i:int| #![trigger states[5].state.accumulators[2usize][i]] 0<=i<states[5].state.accumulators[2usize].len() implies {
            let token=states[5].state.accumulators[2usize][i];let e=states[5].history[token as int];
            token<states[5].history.len() && g::owner(e.landed.receipt)==2 && crate::shared_replay::operational_mixed(programs(2)(e.iterator))
        } by {if i==0 {} else {assert(i==1);}}
    }
    assert(!fu::tracked_tokens(states[5].history,states[5].state.accumulators[2usize],2,2)) by {assert(states[5].state.accumulators[2usize][0]==1);}
    assert(!source_proof::fragment(programs,states,steps,2,1)) by {assert(steps[5]==(2usize,r::Rule::Unload));}
    assert(states.last().state.accumulators[1usize] =~= seq![2nat,4nat]);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn deletion_shape()
    ensures target()==surviving(),
{
    reveal(source);reveal(surviving);reveal_with_fuel(deletion::delete,10);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn target_shape()
    ensures target().len()==6,target().last().history.len()==3,target().last().history[1]==source().first().history[1],
        target()[3].state.accumulators[2usize]==seq![1nat,2nat],target()[4].state.accumulators[2usize].len()==0,
        history::index(source().last().history,2,1,1)==1,history::index(source().last().history,2,1,3)==2,
        target().last().state.tables[0usize][ex::key(0)]==10,target().last().state.tables[1usize].is_empty(),
        s::registered(target().last().state,0),target().last().state.tables[0usize].dom().contains(ex::key(0)),
{
    actual_setup();actual_source();deletion_shape();reveal(source);reveal(surviving);reveal(age::setup);
    reveal_with_fuel(history::index,6);reveal_with_fuel(g::restore,3);
}

/// The old token is permitted by the internal-cleanup fragment, whereas the
/// earlier fragment's cut-bound token requirement rejects the same real trace.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn actual_fragment()
    ensures internal::fragment(age::programs(),source(),labels(),1),
        !source_proof::fragment(age::programs(),source(),labels(),2,1),
{
    actual_setup();actual_source();reveal(source);
    let states=source();let steps=labels();let programs=age::programs();
    assert forall|i:int| 0<=i<steps.len() && g::landing(states[i],states[i+1],steps[i].1) implies {
        let node=programs(steps[i].0)(states[i].current[steps[i].0].unwrap());
        source_proof::table_node(node) && (steps[i].0!=1 ==> crate::shared_replay::operational_mixed(node))
    } by {if i==1 {} else if i==2 {} else {assert(i==6);}}
    assert forall|i:int| #![trigger steps[i]] 0<=i<steps.len() implies {
        let label=steps[i];label.1!=r::Rule::Insert && label.1!=r::Rule::Remove
            && (label.1==r::Rule::Unload ==> label.0!=1 && mixed::operational_tokens(programs,states[i].history,states[i].state.accumulators[label.0],label.0))
    } by {if steps[i].1==r::Rule::Unload {assert(i==5);}}
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn closed_transport()
    ensures {
        let states=source();let kept=target();let terminal=g::unload(states.last(),1);
        &&& kept.first()==states.first()
        &&& g::step(ex::library(),age::programs(),states.last(),terminal,1,r::Rule::Unload)
        &&& g::execution(ex::library(),age::programs(),states.push(terminal),labels().push((1usize,r::Rule::Unload)))
        &&& g::execution(ex::library(),age::programs(),kept,sh::labels_without(labels(),1))
        &&& g::well_formed(ex::library(),age::programs(),terminal) && g::well_formed(ex::library(),age::programs(),kept.last())
        &&& terminal.state.control==kept.last().state.control && obs::tables_related(ex::equality(),terminal.state,kept.last().state)
        &&& terminal.state.tables[1usize].is_empty() && kept.last().state.tables[1usize].is_empty()
    },
{
    actual_setup();actual_source();actual_fragment();sh::example_interface();
    internal::closed_deletion(ex::equality(),ex::library(),age::programs(),setup(),setup_labels(),source(),labels(),1);
}

/// An authentic mixed-age cleanup is followed by another real owner call.
/// The generic theorem constructs the surviving internal cleanup and continuation.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn actual_internal_old_unload()
    ensures {
        let states=source();let kept=target();let terminal=g::unload(states.last(),1);
        &&& g::execution(ex::library(),age::programs(),setup(),setup_labels()) && setup().first()==g::empty::<int,nat>()
        &&& setup().last()==states.first() && kept.first()==states.first()
        &&& g::execution(ex::library(),age::programs(),states,labels())
        &&& internal::fragment(age::programs(),states,labels(),1) && !source_proof::fragment(age::programs(),states,labels(),2,1)
        &&& states.first().state.control.fibers[2usize].phase==Phase::Loading && states.first().current[2usize]==Some(1nat)
        &&& states.first().state.accumulators[2usize]==seq![1nat] && states[5].state.accumulators[2usize]==seq![1nat,3nat]
        &&& mixed::operational_tokens(age::programs(),states[5].history,states[5].state.accumulators[2usize],2)
        &&& !fu::tracked_tokens(states[5].history,states[5].state.accumulators[2usize],2,2)
        &&& kept[3].state.accumulators[2usize]==seq![1nat,2nat]
        &&& history::index(states.last().history,2,1,1)==1 && history::index(states.last().history,2,1,3)==2
        &&& g::step(ex::library(),age::programs(),states[5],states[6],2,r::Rule::Unload)
        &&& g::step(ex::library(),age::programs(),kept[3],kept[4],2,r::Rule::Unload)
        &&& states[6].state.control.fibers[1usize].phase==Phase::Loading && states[6].current[1usize]==Some(1nat)
        &&& g::step(ex::library(),age::programs(),states[6],states[7],1,r::Rule::Finish) && g::landing(states[6],states[7],r::Rule::Finish)
        &&& states[6].state.tables[0usize][ex::key(0)]==10 && states[7].state.tables[0usize][ex::key(0)]==15
        &&& g::step(ex::library(),age::programs(),states.last(),terminal,1,r::Rule::Unload)
        &&& g::execution(ex::library(),age::programs(),states.push(terminal),labels().push((1usize,r::Rule::Unload)))
        &&& g::execution(ex::library(),age::programs(),kept,sh::labels_without(labels(),1))
        &&& g::well_formed(ex::library(),age::programs(),terminal) && g::well_formed(ex::library(),age::programs(),kept.last())
        &&& terminal.state.control==kept.last().state.control && obs::tables_related(ex::equality(),terminal.state,kept.last().state)
        &&& terminal.state.tables[0usize][ex::key(0)]==10 && kept.last().state.tables[0usize][ex::key(0)]==10
        &&& terminal.state.tables[1usize].is_empty() && kept.last().state.tables[1usize].is_empty()
        &&& states.first().history.len()==2 && terminal.history.len()==5 && kept.last().history.len()==3
        &&& states.last().state.tables[0usize][ex::key(0)]==15 && states.last().state.tables[1usize][ex::key(1)]==99
    },
{
    actual_setup();actual_source();actual_fragment();target_shape();closed_transport();
    let states=source();let kept=target();let terminal=g::unload(states.last(),1);
    reveal_with_fuel(sh::labels_without,10);
    assert(sh::labels_without(labels(),1)[3]==(2usize,r::Rule::Unload));
    assert(s::registered(terminal.state,0));assert(terminal.state.tables[0usize].dom()==kept.last().state.tables[0usize].dom());
    assert(ex::equality()(ex::key(0),terminal.state.tables[0usize][ex::key(0)],kept.last().state.tables[0usize][ex::key(0)]));
    assert(terminal.history==states.last().history);
}

} // verus!
