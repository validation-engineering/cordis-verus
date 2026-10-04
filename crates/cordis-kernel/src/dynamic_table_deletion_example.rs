//! A dynamically inserted actor runs, cleans up, and is removed with history.
//!
//! Its actual +7 receipt is retained in historical provenance after removal.
//! The deleted owner contributes Q99 and +5; source and target therefore differ
//! while the new actor runs (22 versus 17) but agree after final owner cleanup.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, dynamic_table_deletion as full, dynamic_table_registry as registry,
    dynamic_table_registry_example as reg, foreign_provision_transport as fp,
    generalized_table_deletion as fixed, grammar_lift as lift, mixed_grammar as g,
    mixed_observational_runs as obs, mixed_orchestration as orchestration,
    observational_lift as ol, old_provision_journal as table,
    old_provision_journal_example as base, providing_owner_deletion as own,
    recovery_examples as ex, refinement as r, semantics as s, shared_execution as sh,
    shared_unload_execution as history, Binding, Phase,
};
use vstd::prelude::*;

verus! {

pub open spec fn setup()->Seq<g::Configuration<int,nat>> {base::setup().take(7)}
pub open spec fn setup_labels()->Seq<(usize,r::Rule)> {base::setup_labels().take(6)}
#[verifier::opaque]
pub open spec fn source()->Seq<g::Configuration<int,nat>> {
    let a4=reg::inserted();let a5=g::edit(a4,3,Phase::Loading,sh::example_view(),Some(0nat),Seq::empty());
    let a6=g::land(ex::library(),base::programs(),a5,3,Phase::Active);let a7=sh::retire(a6,3);
    let a8=g::edit(a7,3,Phase::Unloading,a7.state.control.fibers[3usize].committed,None,a7.state.accumulators[3usize]);
    let a9=g::unload(a8,3);let a10=orchestration::remove(a9,3);let a11=sh::retire(a10,1);
    let a12=g::edit(a11,1,Phase::Unloading,a11.state.control.fibers[1usize].committed,None,a11.state.accumulators[1usize]);
    fp::example_prefix().push(a4).push(a5).push(a6).push(a7).push(a8).push(a9).push(a10).push(a11).push(a12)
}
pub open spec fn labels()->Seq<(usize,r::Rule)> {
    fp::example_labels()+seq![(3usize,r::Rule::Insert),(3usize,r::Rule::Begin),(3usize,r::Rule::Finish),
        (3usize,r::Rule::Retire),(3usize,r::Rule::Leave),(3usize,r::Rule::Unload),(3usize,r::Rule::Remove),
        (1usize,r::Rule::Retire),(1usize,r::Rule::Leave)]
}
pub open spec fn target()->Seq<g::Configuration<int,nat>> {full::delete(ex::library(),base::programs(),source(),labels(),1)}
#[verifier::opaque]
pub open spec fn surviving()->Seq<g::Configuration<int,nat>> {
    let cut=setup().last();let a1=crate::mixed_transposition::insert(cut,3,Some(1),ex::provided(0),ISet::empty(),0nat);
    let a2=g::edit(a1,3,Phase::Loading,sh::example_view(),Some(0nat),Seq::empty());
    let a3=g::land(ex::library(),base::programs(),a2,3,Phase::Active);let a4=sh::retire(a3,3);
    let a5=g::edit(a4,3,Phase::Unloading,a4.state.control.fibers[3usize].committed,None,a4.state.accumulators[3usize]);
    let a6=g::unload(a5,3);let a7=orchestration::remove(a6,3);let a8=sh::retire(a7,1);
    seq![cut,a1,a2,a3,a4,a5,a6,a7,a8]
}

#[verifier::spinoff_prover]
#[verifier::rlimit(45)]
pub proof fn actual_source()
    ensures {
        let states=source();let lib=ex::library();let programs=base::programs();
        &&& g::execution(lib,programs,setup(),setup_labels()) && setup().first()==g::empty::<int,nat>() && setup().last()==states.first()
        &&& g::execution(lib,programs,states,labels()) && own::separated(states.first().state,1)
        &&& states.first().state.control.fibers[1usize].phase==Phase::Inactive && states.first().state.tables[1usize].is_empty()
        &&& states.first().history.len()==1 && states.last().history.len()==4
        &&& states[3].state.tables[0usize][ex::key(0)]==15 && states[3].state.tables[1usize][ex::key(1)]==99
        &&& registry::guard(states[3],states[4],3,r::Rule::Insert,1)
        &&& !s::registered(states[3].state,3) && s::registered(states[4].state,3) && !s::registered(states[10].state,3)
        &&& states[8].state.accumulators[3usize]==seq![3nat] && states[8].state.tables[0usize][ex::key(0)]==22
        &&& g::step(lib,programs,states[8],states[9],3,r::Rule::Unload) && g::step(lib,programs,states[9],states[10],3,r::Rule::Remove)
        &&& states[9].state.tables[0usize][ex::key(0)]==15 && states[9].state.tables[3usize].is_empty()
        &&& states.last().state.control.fibers[1usize].phase==Phase::Unloading && states.last().state.accumulators[1usize]==seq![1nat,2nat]
        &&& g::owner(states.last().history[3].landed.receipt)==3 && states.last().history[3].input.control.fibers.dom().contains(3usize)
    },
{
    reg::actual_source_registry();fp::actual_prefix();sh::example_interface();reveal(source);reveal(fp::example_prefix);reveal(base::setup);
    let states=source();let steps=labels();let lib=ex::library();let programs=base::programs();let prefix=fp::example_prefix();let eq=ex::equality();
    assert(states[3]==prefix.last());assert(states[4]==reg::inserted());
    sh::example_target(states[4].state,3);assert(g::step(lib,programs,states[4],states[5],3,r::Rule::Begin));
    assert(lift::names_key(Binding {key:0,realm:0,provider:0},ex::key(0)));
    assert(states[5].state.control.fibers[3usize].committed.contains(Binding {key:0,realm:0,provider:0}));
    assert(exists|b:Binding|states[5].state.control.fibers[3usize].committed.contains(b) && lift::names_key(b,ex::key(0)));
    assert(lift::resolve(states[5].state,3,ex::key(0))==Some(0usize));
    assert(g::step(lib,programs,states[5],states[6],3,r::Rule::Finish));
    ch::concrete_child_retirement(states[6].state,3);assert(g::step(lib,programs,states[6],states[7],3,r::Rule::Retire));
    assert(g::step(lib,programs,states[7],states[8],3,r::Rule::Leave));
    assert(states[8].state.accumulators[3usize] =~= seq![3nat]);reveal_with_fuel(g::restore,2);
    assert(g::step(lib,programs,states[8],states[9],3,r::Rule::Unload));
    assert forall|n:usize|r::registered(states[9].state.control,n) implies states[9].state.control.fibers[n].parent!=Some(3usize) by {if n==0{}else if n==1{}else if n==2{}else{assert(n==3);}}
    assert forall|token:nat|token<states[9].history.len() implies (#[trigger] g::kind(states[9].history)(token)).is_none() by {if token==0{}else if token==1{}else if token==2{}else{assert(token==3);}}
    assert(ch::remove_unreferenced(g::kind(states[9].history),states[9].state,3)) by {
        assert forall|actor:usize,token:nat|s::registered(states[9].state,actor) && states[9].state.accumulators[actor].contains(token) implies g::kind(states[9].history)(token)!=Some(3usize) by {
            if actor==0 {assert(token==0);}else if actor==1 {assert(token==1 || token==2);}else if actor==2{}else {assert(actor==3);}
        }
    }
    assert(r::frame(states[9].state.control,states[10].state.control,3));assert(g::step(lib,programs,states[9],states[10],3,r::Rule::Remove));
    ch::concrete_child_retirement(states[10].state,1);assert(g::step(lib,programs,states[10],states[11],1,r::Rule::Retire));
    assert(g::step(lib,programs,states[11],states[12],1,r::Rule::Leave));
    assert forall|i:int|0<=i<steps.len() implies g::step(lib,programs,states[i],states[i+1],steps[i].0,steps[i].1) by {
        if i<3 {assert(states[i]==prefix[i]);assert(states[i+1]==prefix[i+1]);assert(steps[i]==fp::example_labels()[i]);}
        else if i==3{}else if i==4{}else if i==5{}else if i==6{}else if i==7{}else if i==8{}else if i==9{}else if i==10{}else{assert(i==11);}
    }
    assert(states.last().state.accumulators[1usize] =~= seq![1nat,2nat]);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn actual_fragment()
    ensures full::fragment(base::programs(),source(),labels(),1),!fixed::fragment(base::programs(),source(),labels(),1),
{
    actual_source();reveal(source);reveal(fp::example_prefix);reveal(base::setup);
    let states=source();let steps=labels();let programs=base::programs();
    assert forall|i:int|0<=i<steps.len() && g::landing(states[i],states[i+1],steps[i].1) implies own::table_node(programs(steps[i].0)(states[i].current[steps[i].0].unwrap())) by {if i==1{}else if i==2{}else{assert(i==5);}}
    assert(table::table_tokens(programs,states[8].history,states[8].state.accumulators[3usize],3)) by {
        assert forall|i:int| #![trigger states[8].state.accumulators[3usize][i]] 0<=i<states[8].state.accumulators[3usize].len() implies {
            let token=states[8].state.accumulators[3usize][i];let e=states[8].history[token as int];token<states[8].history.len() && g::owner(e.landed.receipt)==3 && own::table_node(programs(3)(e.iterator))
        } by {assert(i==0);}
    }
    assert forall|i:int| #![trigger steps[i]] 0<=i<steps.len() implies {
        let label=steps[i];
        &&& ((label.1==r::Rule::Insert || label.1==r::Rule::Remove) ==> registry::guard(states[i],states[i+1],label.0,label.1,1))
        &&& (label.1==r::Rule::Unload ==> label.0!=1 && table::table_tokens(programs,states[i].history,states[i].state.accumulators[label.0],label.0))
    } by {if steps[i].1==r::Rule::Insert {assert(i==3);}else if steps[i].1==r::Rule::Remove {assert(i==9);}else if steps[i].1==r::Rule::Unload {assert(i==8);}}
    assert(!fixed::fragment(programs,states,steps,1)) by {assert(steps[3].1==r::Rule::Insert);}
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn deletion_shape()
    ensures target()==surviving(),
{
    reveal(source);reveal(fp::example_prefix);reveal(surviving);reveal(base::setup);reveal_with_fuel(full::delete,13);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(35)]
pub proof fn target_values()
    ensures {
        let kept=target();let states=source();
        &&& kept.len()==9 && kept.last().history.len()==2
        &&& kept[1].state.control.fibers[3usize]==states[4].state.control.fibers[3usize] && kept[1].roots[3usize]==states[4].roots[3usize]
        &&& kept[5].state.accumulators[3usize]==seq![1nat] && kept[5].state.tables[0usize][ex::key(0)]==17
        &&& kept[6].state.tables[0usize][ex::key(0)]==10 && kept[6].state.accumulators[3usize].len()==0
        &&& !s::registered(kept[7].state,3) && g::owner(kept[7].history[1].landed.receipt)==3
        &&& history::index(states.last().history,1,1,3)==1
        &&& kept.last().state.tables[0usize][ex::key(0)]==10 && kept.last().state.tables[1usize].is_empty()
        &&& s::registered(kept.last().state,0) && kept.last().state.tables[0usize].dom().contains(ex::key(0))
    },
{
    actual_source();deletion_shape();reveal(source);reveal(fp::example_prefix);reveal(surviving);reveal(base::setup);
    reveal_with_fuel(g::restore,2);reveal_with_fuel(history::index,5);assert(target()[5].state.accumulators[3usize] =~= seq![1nat]);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(35)]
pub proof fn closed_transport()
    ensures {
        let states=source();let kept=target();let terminal=g::unload(states.last(),1);
        &&& g::execution(ex::library(),base::programs(),kept,sh::labels_without(labels(),1))
        &&& g::step(ex::library(),base::programs(),states.last(),terminal,1,r::Rule::Unload)
        &&& g::execution(ex::library(),base::programs(),states.push(terminal),labels().push((1usize,r::Rule::Unload)))
        &&& terminal.state.control==kept.last().state.control && obs::tables_related(ex::equality(),terminal.state,kept.last().state)
        &&& terminal.state.tables[1usize].is_empty() && kept.last().state.tables[1usize].is_empty()
        &&& forall|i:int|0<=i<kept.len() ==> g::well_formed(ex::library(),base::programs(),kept[i])
        &&& terminal.state.tables[0usize][ex::key(0)]==10
    },
{
    actual_source();actual_fragment();target_values();sh::example_interface();
    full::closed_deletion(ex::equality(),ex::library(),base::programs(),setup(),setup_labels(),source(),labels(),1);
    let terminal=g::unload(source().last(),1);let kept=target();
    assert(s::registered(terminal.state,0));assert(terminal.state.tables[0usize].dom()==kept.last().state.tables[0usize].dom());
    assert(ex::equality()(ex::key(0),terminal.state.tables[0usize][ex::key(0)],kept.last().state.tables[0usize][ex::key(0)]));
}

} // verus!
