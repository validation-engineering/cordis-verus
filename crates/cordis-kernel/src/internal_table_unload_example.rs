//! Authentic old Provision cleanup inside two different owner phases.
//!
//! Both traces unload the same foreign Provision and two Operations internally.
//! One does so after the owner publishes Q; the other does so before the owner
//! begins, with an empty owner journal. Real owner calls follow both cleanups.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, dependent_lift as dep, foreign_unload as fu, grammar_lift as lift,
    internal_old_unload as previous, internal_table_unload as internal,
    mixed_age_unload as operational, mixed_grammar as g, mixed_observational_runs as obs,
    old_provision_journal as mixed, old_provision_journal_example as base,
    providing_owner_deletion as source_proof, providing_owner_execution as deletion,
    recovery_examples as ex, refinement as r, semantics as s, shared_execution as sh,
    shared_unload_execution as history, Binding, Phase,
};
use vstd::prelude::*;

verus! {

pub open spec fn setup()->Seq<g::Configuration<int,nat>> {base::setup()}
pub open spec fn setup_labels()->Seq<(usize,r::Rule)> {base::setup_labels()}
pub open spec fn cleanup(installed:bool)->int {if installed {5}else{3}}
pub open spec fn fresh_token(installed:bool)->nat {if installed {4}else{3}}
#[verifier::opaque]
pub open spec fn source(installed:bool)->Seq<g::Configuration<int,nat>> {
    let cut=setup().last();
    let middle=if installed {
        let a1=g::edit(cut,1,Phase::Loading,sh::example_view(),Some(0nat),Seq::empty());
        let a2=g::land(ex::library(),base::programs(),a1,1,Phase::Loading);
        let a3=g::land(ex::library(),base::programs(),a2,2,Phase::Active);
        let a4=sh::retire(a3,2);
        let a5=g::edit(a4,2,Phase::Unloading,sh::example_view(),None,a4.state.accumulators[2usize]);
        let a6=g::unload(a5,2);
        seq![cut,a1,a2,a3,a4,a5,a6]
    } else {
        let a1=g::land(ex::library(),base::programs(),cut,2,Phase::Active);
        let a2=sh::retire(a1,2);
        let a3=g::edit(a2,2,Phase::Unloading,sh::example_view(),None,a2.state.accumulators[2usize]);
        let a4=g::unload(a3,2);
        let a5=g::edit(a4,1,Phase::Loading,sh::example_view(),Some(0nat),Seq::empty());
        let a6=g::land(ex::library(),base::programs(),a5,1,Phase::Loading);
        seq![cut,a1,a2,a3,a4,a5,a6]
    };
    let a7=g::land(ex::library(),base::programs(),middle.last(),1,Phase::Active);
    let a8=sh::retire(a7,1);
    let a9=g::edit(a8,1,Phase::Unloading,sh::example_view(),None,a8.state.accumulators[1usize]);
    middle.push(a7).push(a8).push(a9)
}
pub open spec fn labels(installed:bool)->Seq<(usize,r::Rule)> {
    let middle=if installed {
        seq![(1usize,r::Rule::Begin),(1usize,r::Rule::Iter),(2usize,r::Rule::Finish),(2usize,r::Rule::Retire),
            (2usize,r::Rule::Leave),(2usize,r::Rule::Unload)]
    } else {
        seq![(2usize,r::Rule::Finish),(2usize,r::Rule::Retire),(2usize,r::Rule::Leave),(2usize,r::Rule::Unload),
            (1usize,r::Rule::Begin),(1usize,r::Rule::Iter)]
    };
    middle.push((1usize,r::Rule::Finish)).push((1usize,r::Rule::Retire)).push((1usize,r::Rule::Leave))
}
pub open spec fn target(installed:bool)->Seq<g::Configuration<int,nat>> {
    deletion::delete(ex::library(),base::programs(),source(installed),labels(installed),1)
}
#[verifier::opaque]
pub open spec fn surviving()->Seq<g::Configuration<int,nat>> {
    let cut=setup().last();let a1=g::land(ex::library(),base::programs(),cut,2,Phase::Active);
    let a2=sh::retire(a1,2);
    let a3=g::edit(a2,2,Phase::Unloading,a2.state.control.fibers[2usize].committed,None,a2.state.accumulators[2usize]);
    let a4=g::unload(a3,2);let a5=sh::retire(a4,1);
    seq![cut,a1,a2,a3,a4,a5]
}

pub proof fn actual_setup(installed:bool)
    ensures g::execution(ex::library(),base::programs(),setup(),setup_labels()),setup().first()==g::empty::<int,nat>(),setup().last()==source(installed).first(),
        g::well_formed(ex::library(),base::programs(),source(installed).first()),
        source(installed).first().history.len()==3,source(installed).first().state.tables[0usize][ex::key(0)]==17,
        source(installed).first().state.tables[2usize][ex::key(2)]==77,
        source(installed).first().state.accumulators[2usize]==seq![1nat,2nat],source(installed).first().current[2usize]==Some(2nat),
        source(installed).first().state.control.fibers[2usize].phase==Phase::Loading,
        source(installed).first().state.control.fibers[1usize].phase==Phase::Inactive,source(installed).first().state.tables[1usize].is_empty(),
{
    base::actual_setup();reveal(source);reveal(base::setup);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub proof fn actual_source(installed:bool)
    ensures {
        let states=source(installed);let u=cleanup(installed);let fresh=fresh_token(installed);
        &&& g::execution(ex::library(),base::programs(),states,labels(installed)) && source_proof::separated(states.first().state,1)
        &&& !previous::fragment(base::programs(),states,labels(installed),1)
        &&& !source_proof::fragment(base::programs(),states,labels(installed),3,1)
        &&& states[u].state.accumulators[2usize]==seq![1nat,2nat,fresh]
        &&& mixed::table_tokens(base::programs(),states[u].history,states[u].state.accumulators[2usize],2)
        &&& !operational::operational_tokens(base::programs(),states[u].history,states[u].state.accumulators[2usize],2)
        &&& !fu::tracked_tokens(states[u].history,states[u].state.accumulators[2usize],3,2)
        &&& g::step(ex::library(),base::programs(),states[u],states[u+1],2,r::Rule::Unload)
        &&& states[u].state.tables[2usize][ex::key(2)]==77 && states[u+1].state.tables[2usize].is_empty()
        &&& states[u+1].state.tables[0usize][ex::key(0)]==10
        &&& (installed ==> states[u].state.control.fibers[1usize].phase==Phase::Loading && states[u].current[1usize]==Some(1nat)
            && states[u].state.accumulators[1usize]==seq![3nat] && states[u].state.tables[1usize][ex::key(1)]==99)
        &&& (!installed ==> states[u].state.control.fibers[1usize].phase==Phase::Inactive && states[u].state.accumulators[1usize].len()==0
            && states[u].state.tables[1usize].is_empty()
            && g::step(ex::library(),base::programs(),states[4],states[5],1,r::Rule::Begin))
        &&& states[6].state.control.fibers[1usize].phase==Phase::Loading && states[6].current[1usize]==Some(1nat)
        &&& g::step(ex::library(),base::programs(),states[6],states[7],1,r::Rule::Finish) && g::landing(states[6],states[7],r::Rule::Finish)
        &&& states[6].state.tables[0usize][ex::key(0)]==10 && states[7].state.tables[0usize][ex::key(0)]==15
        &&& states.last().history.len()==6 && states.last().state.accumulators[1usize]==seq![if installed {3nat}else{4nat},5nat]
        &&& states.last().state.control.fibers[1usize].phase==Phase::Unloading
        &&& states.last().state.tables[0usize][ex::key(0)]==15 && states.last().state.tables[1usize][ex::key(1)]==99 && states.last().state.tables[2usize].is_empty()
    },
{
    actual_setup(installed);sh::example_interface();reveal(source);reveal(base::setup);
    let lib=ex::library();let programs=base::programs();let states=source(installed);let steps=labels(installed);let u=cleanup(installed);
    assert(lift::names_key(Binding {key:0,realm:0,provider:0},ex::key(0)));
    if installed {
        sh::example_target(states[0].state,1);assert(g::step(lib,programs,states[0],states[1],1,r::Rule::Begin));
        assert(g::step(lib,programs,states[1],states[2],1,r::Rule::Iter));
        assert(states[2].state.control.fibers[2usize].committed.contains(Binding {key:0,realm:0,provider:0}));
        assert(exists|b:Binding| states[2].state.control.fibers[2usize].committed.contains(b) && lift::names_key(b,ex::key(0)));
        assert(lift::resolve(states[2].state,2,ex::key(0))==Some(0usize));assert(g::step(lib,programs,states[2],states[3],2,r::Rule::Finish));
        ch::concrete_child_retirement(states[3].state,2);assert(g::step(lib,programs,states[3],states[4],2,r::Rule::Retire));
        assert(g::step(lib,programs,states[4],states[5],2,r::Rule::Leave));
    } else {
        assert(states[0].state.control.fibers[2usize].committed.contains(Binding {key:0,realm:0,provider:0}));
        assert(exists|b:Binding| states[0].state.control.fibers[2usize].committed.contains(b) && lift::names_key(b,ex::key(0)));
        assert(lift::resolve(states[0].state,2,ex::key(0))==Some(0usize));assert(g::step(lib,programs,states[0],states[1],2,r::Rule::Finish));
        ch::concrete_child_retirement(states[1].state,2);assert(g::step(lib,programs,states[1],states[2],2,r::Rule::Retire));
        assert(g::step(lib,programs,states[2],states[3],2,r::Rule::Leave));
    }
    assert(states[u].state.accumulators[2usize] =~= seq![1nat,2nat,fresh_token(installed)]);reveal_with_fuel(g::restore,4);
    assert(g::step(lib,programs,states[u],states[u+1],2,r::Rule::Unload));
    if !installed {
        sh::example_target(states[4].state,1);assert(g::step(lib,programs,states[4],states[5],1,r::Rule::Begin));
        assert(g::step(lib,programs,states[5],states[6],1,r::Rule::Iter));
    }
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
    assert(mixed::table_tokens(programs,states[u].history,states[u].state.accumulators[2usize],2)) by {
        assert forall|i:int| #![trigger states[u].state.accumulators[2usize][i]] 0<=i<states[u].state.accumulators[2usize].len() implies {
            let token=states[u].state.accumulators[2usize][i];let e=states[u].history[token as int];
            token<states[u].history.len() && g::owner(e.landed.receipt)==2 && source_proof::table_node(programs(2)(e.iterator))
        } by {if i==0 {} else if i==1 {} else {assert(i==2);}}
    }
    assert(!operational::operational_tokens(programs,states[u].history,states[u].state.accumulators[2usize],2)) by {
        assert(states[u].state.accumulators[2usize][0]==1);
        assert(!crate::shared_replay::operational_mixed(programs(2)(states[u].history[1].iterator)));
    }
    assert(!fu::tracked_tokens(states[u].history,states[u].state.accumulators[2usize],3,2)) by {assert(states[u].state.accumulators[2usize][0]==1);}
    assert(!previous::fragment(programs,states,steps,1)) by {assert(steps[u]==(2usize,r::Rule::Unload));}
    assert(!source_proof::fragment(programs,states,steps,3,1)) by {assert(steps[u]==(2usize,r::Rule::Unload));}
    assert(states.last().state.accumulators[1usize] =~= seq![if installed {3nat}else{4nat},5nat]);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn deletion_shape(installed:bool)
    ensures target(installed)==surviving(),
{
    reveal(source);reveal(surviving);reveal_with_fuel(deletion::delete,10);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn target_shape(installed:bool)
    ensures {
        let states=source(installed);let kept=target(installed);
        &&& kept.len()==6 && kept.last().history.len()==4 && kept.last().history[1]==states.first().history[1] && kept.last().history[2]==states.first().history[2]
        &&& kept[3].state.accumulators[2usize]==seq![1nat,2nat,3nat] && kept[4].state.accumulators[2usize].len()==0
        &&& history::index(states.last().history,3,1,1)==1 && history::index(states.last().history,3,1,2)==2
        &&& history::index(states.last().history,3,1,fresh_token(installed))==3
        &&& kept.last().state.tables[0usize][ex::key(0)]==10 && kept.last().state.tables[1usize].is_empty() && kept.last().state.tables[2usize].is_empty()
        &&& s::registered(kept.last().state,0) && kept.last().state.tables[0usize].dom().contains(ex::key(0)) && s::registered(kept.last().state,2)
    },
{
    actual_setup(installed);actual_source(installed);deletion_shape(installed);reveal(source);reveal(surviving);reveal(base::setup);
    reveal_with_fuel(history::index,7);reveal_with_fuel(g::restore,4);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn actual_fragment(installed:bool)
    ensures internal::fragment(base::programs(),source(installed),labels(installed),1),
        !previous::fragment(base::programs(),source(installed),labels(installed),1),
{
    actual_setup(installed);actual_source(installed);reveal(source);
    let states=source(installed);let steps=labels(installed);let programs=base::programs();
    assert forall|i:int| 0<=i<steps.len() && g::landing(states[i],states[i+1],steps[i].1) implies {
        let node=programs(steps[i].0)(states[i].current[steps[i].0].unwrap());
        source_proof::table_node(node) && (steps[i].0!=1 ==> crate::shared_replay::operational_mixed(node))
    } by {
        if installed {if i==1 {} else if i==2 {} else {assert(i==6);}}
        else {if i==0 {} else if i==5 {} else {assert(i==6);}}
    }
    assert forall|i:int| #![trigger steps[i]] 0<=i<steps.len() implies {
        let label=steps[i];label.1!=r::Rule::Insert && label.1!=r::Rule::Remove
            && (label.1==r::Rule::Unload ==> label.0!=1 && mixed::table_tokens(programs,states[i].history,states[i].state.accumulators[label.0],label.0))
    } by {if steps[i].1==r::Rule::Unload {assert(i==cleanup(installed));}}
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn closed_transport(installed:bool)
    ensures {
        let states=source(installed);let kept=target(installed);let terminal=g::unload(states.last(),1);
        &&& kept.first()==states.first()
        &&& g::step(ex::library(),base::programs(),states.last(),terminal,1,r::Rule::Unload)
        &&& g::execution(ex::library(),base::programs(),states.push(terminal),labels(installed).push((1usize,r::Rule::Unload)))
        &&& g::execution(ex::library(),base::programs(),kept,sh::labels_without(labels(installed),1))
        &&& g::well_formed(ex::library(),base::programs(),terminal) && g::well_formed(ex::library(),base::programs(),kept.last())
        &&& terminal.state.control==kept.last().state.control && obs::tables_related(ex::equality(),terminal.state,kept.last().state)
        &&& terminal.state.tables[1usize].is_empty() && kept.last().state.tables[1usize].is_empty()
    },
{
    actual_setup(installed);actual_source(installed);actual_fragment(installed);sh::example_interface();
    internal::closed_deletion(ex::equality(),ex::library(),base::programs(),setup(),setup_labels(),source(installed),labels(installed),1);
}

/// Decode the kept cleanup and its final observations in a small context.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn internal_table_unload_observations(installed:bool)
    ensures {
        let states=source(installed);let kept=target(installed);let terminal=g::unload(states.last(),1);
        &&& g::step(ex::library(),base::programs(),kept[3],kept[4],2,r::Rule::Unload)
        &&& terminal.state.tables[0usize][ex::key(0)]==10 && terminal.state.tables[2usize].is_empty()
        &&& terminal.history==states.last().history
    },
{
    target_shape(installed);closed_transport(installed);
    let states=source(installed);let kept=target(installed);let terminal=g::unload(states.last(),1);
    reveal_with_fuel(sh::labels_without,10);
    assert(sh::labels_without(labels(installed),1)[3]==(2usize,r::Rule::Unload));
    assert(s::registered(terminal.state,0));assert(terminal.state.tables[0usize].dom()==kept.last().state.tables[0usize].dom());
    assert(ex::equality()(ex::key(0),terminal.state.tables[0usize][ex::key(0)],kept.last().state.tables[0usize][ex::key(0)]));
    assert(s::registered(terminal.state,2));assert(terminal.state.tables[2usize].dom()==kept.last().state.tables[2usize].dom());assert(terminal.state.tables[2usize] =~= IMap::empty());
}

/// Both boolean instantiations are real, empty-origin lifecycle executions.
/// In particular the false case exercises Provision cleanup with an empty own
/// batch before Begin, then continues with genuine owner publication and calls.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn actual_internal_table_unload(installed:bool)
    ensures {
        let states=source(installed);let kept=target(installed);let terminal=g::unload(states.last(),1);let u=cleanup(installed);
        &&& g::execution(ex::library(),base::programs(),setup(),setup_labels()) && setup().first()==g::empty::<int,nat>()
        &&& setup().last()==states.first() && kept.first()==states.first()
        &&& g::execution(ex::library(),base::programs(),states,labels(installed))
        &&& internal::fragment(base::programs(),states,labels(installed),1) && !previous::fragment(base::programs(),states,labels(installed),1)
        &&& states.first().state.tables[0usize][ex::key(0)]==17 && states.first().state.tables[2usize][ex::key(2)]==77
        &&& states.first().state.accumulators[2usize]==seq![1nat,2nat] && states[u].state.accumulators[2usize]==seq![1nat,2nat,fresh_token(installed)]
        &&& mixed::table_tokens(base::programs(),states[u].history,states[u].state.accumulators[2usize],2)
        &&& !operational::operational_tokens(base::programs(),states[u].history,states[u].state.accumulators[2usize],2)
        &&& !fu::tracked_tokens(states[u].history,states[u].state.accumulators[2usize],3,2)
        &&& kept[3].state.accumulators[2usize]==seq![1nat,2nat,3nat]
        &&& history::index(states.last().history,3,1,1)==1 && history::index(states.last().history,3,1,2)==2
        &&& history::index(states.last().history,3,1,fresh_token(installed))==3
        &&& g::step(ex::library(),base::programs(),states[u],states[u+1],2,r::Rule::Unload)
        &&& g::step(ex::library(),base::programs(),kept[3],kept[4],2,r::Rule::Unload)
        &&& states[u].state.tables[2usize][ex::key(2)]==77 && states[u+1].state.tables[2usize].is_empty()
        &&& states[u+1].state.tables[0usize][ex::key(0)]==10
        &&& (installed ==> states[u].state.control.fibers[1usize].phase==Phase::Loading && states[u].current[1usize]==Some(1nat)
            && states[u].state.accumulators[1usize]==seq![3nat] && states[u].state.tables[1usize][ex::key(1)]==99)
        &&& (!installed ==> states[u].state.control.fibers[1usize].phase==Phase::Inactive && states[u].state.accumulators[1usize].len()==0
            && states[u].state.tables[1usize].is_empty()
            && g::step(ex::library(),base::programs(),states[4],states[5],1,r::Rule::Begin))
        &&& states[6].state.control.fibers[1usize].phase==Phase::Loading && states[6].current[1usize]==Some(1nat)
        &&& g::step(ex::library(),base::programs(),states[6],states[7],1,r::Rule::Finish) && g::landing(states[6],states[7],r::Rule::Finish)
        &&& states[6].state.tables[0usize][ex::key(0)]==10 && states[7].state.tables[0usize][ex::key(0)]==15
        &&& g::step(ex::library(),base::programs(),states.last(),terminal,1,r::Rule::Unload)
        &&& g::execution(ex::library(),base::programs(),states.push(terminal),labels(installed).push((1usize,r::Rule::Unload)))
        &&& g::execution(ex::library(),base::programs(),kept,sh::labels_without(labels(installed),1))
        &&& g::well_formed(ex::library(),base::programs(),terminal) && g::well_formed(ex::library(),base::programs(),kept.last())
        &&& terminal.state.control==kept.last().state.control && obs::tables_related(ex::equality(),terminal.state,kept.last().state)
        &&& terminal.state.tables[0usize][ex::key(0)]==10 && kept.last().state.tables[0usize][ex::key(0)]==10
        &&& terminal.state.tables[1usize].is_empty() && kept.last().state.tables[1usize].is_empty()
        &&& terminal.state.tables[2usize].is_empty() && kept.last().state.tables[2usize].is_empty()
        &&& states.first().history.len()==3 && terminal.history.len()==6 && kept.last().history.len()==4
        &&& states.last().state.tables[0usize][ex::key(0)]==15 && states.last().state.tables[1usize][ex::key(1)]==99
    },
{
    actual_setup(installed);actual_source(installed);actual_fragment(installed);target_shape(installed);closed_transport(installed);
    internal_table_unload_observations(installed);
}

} // verus!
