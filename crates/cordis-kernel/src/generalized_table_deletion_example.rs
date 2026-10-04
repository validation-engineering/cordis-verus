//! A fresh foreign Provision and its actual cleanup survive a complete deletion.
//!
//! The own batch already holds Q's Provision and a shared-key Operation when
//! the foreign actor provides R. Its two subsequent Operations and three real
//! inverse receipts all survive, with compressed authentic history positions.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, foreign_provision_transport as fp, generalized_table_deletion as full,
    grammar_lift as lift, internal_table_unload as previous, mixed_grammar as g,
    mixed_observational_runs as obs, old_provision_journal as table,
    old_provision_journal_example as base, providing_owner_deletion as source_proof,
    providing_owner_execution as deletion, recovery_examples as ex, refinement as r,
    semantics as s, shared_execution as sh, shared_unload_execution as history, Binding, Phase,
};
use vstd::prelude::*;

verus! {

pub open spec fn setup()->Seq<g::Configuration<int,nat>> {base::setup().take(7)}
pub open spec fn setup_labels()->Seq<(usize,r::Rule)> {base::setup_labels().take(6)}
#[verifier::opaque]
pub open spec fn source()->Seq<g::Configuration<int,nat>> {
    let prefix=fp::example_prefix();let a=prefix.last();
    let a4=g::land(ex::library(),base::programs(),a,2,Phase::Loading);
    let a5=g::land(ex::library(),base::programs(),a4,2,Phase::Loading);
    let a6=g::land(ex::library(),base::programs(),a5,2,Phase::Active);
    let a7=sh::retire(a6,2);
    let a8=g::edit(a7,2,Phase::Unloading,a7.state.control.fibers[2usize].committed,None,a7.state.accumulators[2usize]);
    let a9=g::unload(a8,2);let a10=sh::retire(a9,1);
    let a11=g::edit(a10,1,Phase::Unloading,a10.state.control.fibers[1usize].committed,None,a10.state.accumulators[1usize]);
    prefix.push(a4).push(a5).push(a6).push(a7).push(a8).push(a9).push(a10).push(a11)
}
pub open spec fn labels()->Seq<(usize,r::Rule)> {
    fp::example_labels()+seq![(2usize,r::Rule::Iter),(2usize,r::Rule::Iter),(2usize,r::Rule::Finish),
        (2usize,r::Rule::Retire),(2usize,r::Rule::Leave),(2usize,r::Rule::Unload),
        (1usize,r::Rule::Retire),(1usize,r::Rule::Leave)]
}
pub open spec fn target()->Seq<g::Configuration<int,nat>> {
    deletion::delete(ex::library(),base::programs(),source(),labels(),1)
}
#[verifier::opaque]
pub open spec fn surviving()->Seq<g::Configuration<int,nat>> {
    let cut=setup().last();let a1=g::land(ex::library(),base::programs(),cut,2,Phase::Loading);
    let a2=g::land(ex::library(),base::programs(),a1,2,Phase::Loading);
    let a3=g::land(ex::library(),base::programs(),a2,2,Phase::Active);let a4=sh::retire(a3,2);
    let a5=g::edit(a4,2,Phase::Unloading,a4.state.control.fibers[2usize].committed,None,a4.state.accumulators[2usize]);
    let a6=g::unload(a5,2);let a7=sh::retire(a6,1);
    seq![cut,a1,a2,a3,a4,a5,a6,a7]
}

#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub proof fn actual_source()
    ensures {
        let states=source();let lib=ex::library();let programs=base::programs();
        &&& g::execution(lib,programs,setup(),setup_labels()) && setup().first()==g::empty::<int,nat>() && setup().last()==states.first()
        &&& g::execution(lib,programs,states,labels()) && source_proof::separated(states.first().state,1)
        &&& states.first().state.control.fibers[1usize].phase==Phase::Inactive && states.first().state.tables[1usize].is_empty()
        &&& states.first().history.len()==1 && states.last().history.len()==6
        &&& states[3].state.tables[0usize][ex::key(0)]==15 && states[3].state.tables[1usize][ex::key(1)]==99
        &&& states[3].state.accumulators[1usize]==seq![1nat,2nat] && states[3].state.tables[2usize].is_empty()
        &&& g::step(lib,programs,states[3],states[4],2,r::Rule::Iter) && g::landing(states[3],states[4],r::Rule::Iter)
        &&& states[4].state.tables[2usize][ex::key(2)]==77 && states[4].state.accumulators[2usize]==seq![3nat]
        &&& states[8].state.accumulators[2usize]==seq![3nat,4nat,5nat] && states[8].state.tables[0usize][ex::key(0)]==29
        &&& g::step(lib,programs,states[8],states[9],2,r::Rule::Unload)
        &&& states[9].state.tables[0usize][ex::key(0)]==15 && states[9].state.tables[2usize].is_empty()
        &&& states.last().state.control.fibers[1usize].phase==Phase::Unloading && states.last().state.accumulators[1usize]==seq![1nat,2nat]
    },
{
    fp::actual_prefix();sh::example_interface();reveal(source);reveal(fp::example_prefix);reveal(base::setup);
    let states=source();let steps=labels();let lib=ex::library();let programs=base::programs();let prefix=fp::example_prefix();
    assert(states.first()==prefix.first());assert(states[3]==prefix.last());
    assert(g::step(lib,programs,states[3],states[4],2,r::Rule::Iter));
    assert(lift::names_key(Binding {key:0,realm:0,provider:0},ex::key(0)));
    assert(states[4].state.control.fibers[2usize].committed.contains(Binding {key:0,realm:0,provider:0}));
    assert(exists|b:Binding|states[4].state.control.fibers[2usize].committed.contains(b) && lift::names_key(b,ex::key(0)));
    assert(lift::resolve(states[4].state,2,ex::key(0))==Some(0usize));
    assert(g::step(lib,programs,states[4],states[5],2,r::Rule::Iter));
    assert(states[5].state.control.fibers[2usize].committed.contains(Binding {key:0,realm:0,provider:0}));
    assert(exists|b:Binding|states[5].state.control.fibers[2usize].committed.contains(b) && lift::names_key(b,ex::key(0)));
    assert(lift::resolve(states[5].state,2,ex::key(0))==Some(0usize));
    assert(g::step(lib,programs,states[5],states[6],2,r::Rule::Finish));
    ch::concrete_child_retirement(states[6].state,2);assert(g::step(lib,programs,states[6],states[7],2,r::Rule::Retire));
    assert(g::step(lib,programs,states[7],states[8],2,r::Rule::Leave));
    assert(states[8].state.accumulators[2usize] =~= seq![3nat,4nat,5nat]);reveal_with_fuel(g::restore,4);
    assert(g::step(lib,programs,states[8],states[9],2,r::Rule::Unload));
    ch::concrete_child_retirement(states[9].state,1);assert(g::step(lib,programs,states[9],states[10],1,r::Rule::Retire));
    assert(g::step(lib,programs,states[10],states[11],1,r::Rule::Leave));
    assert forall|i:int|0<=i<steps.len() implies g::step(lib,programs,states[i],states[i+1],steps[i].0,steps[i].1) by {
        if i<3 {assert(states[i]==prefix[i]);assert(states[i+1]==prefix[i+1]);assert(steps[i]==fp::example_labels()[i]);}
        else if i==3{}else if i==4{}else if i==5{}else if i==6{}else if i==7{}else if i==8{}else if i==9{}else{assert(i==10);}
    }
    assert(states[4].state.accumulators[2usize] =~= seq![3nat]);assert(states.last().state.accumulators[1usize] =~= seq![1nat,2nat]);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn actual_fragment()
    ensures full::fragment(base::programs(),source(),labels(),1),!previous::fragment(base::programs(),source(),labels(),1),
{
    actual_source();reveal(source);reveal(fp::example_prefix);reveal(base::setup);
    let states=source();let steps=labels();let programs=base::programs();
    assert forall|i:int|0<=i<steps.len() && g::landing(states[i],states[i+1],steps[i].1) implies source_proof::table_node(programs(steps[i].0)(states[i].current[steps[i].0].unwrap())) by {
        if i==1{}else if i==2{}else if i==3{}else if i==4{}else{assert(i==5);}
    }
    assert(table::table_tokens(programs,states[8].history,states[8].state.accumulators[2usize],2)) by {
        assert forall|i:int| #![trigger states[8].state.accumulators[2usize][i]] 0<=i<states[8].state.accumulators[2usize].len() implies {
            let token=states[8].state.accumulators[2usize][i];let entry=states[8].history[token as int];token<states[8].history.len() && g::owner(entry.landed.receipt)==2 && source_proof::table_node(programs(2)(entry.iterator))
        } by {if i==0{}else if i==1{}else{assert(i==2);}}
    }
    assert forall|i:int| #![trigger steps[i]] 0<=i<steps.len() implies {
        let label=steps[i];label.1!=r::Rule::Insert && label.1!=r::Rule::Remove && (label.1==r::Rule::Unload ==> label.0!=1 && table::table_tokens(programs,states[i].history,states[i].state.accumulators[label.0],label.0))
    } by {if steps[i].1==r::Rule::Unload {assert(i==8);}}
    assert(!previous::fragment(programs,states,steps,1)) by {
        assert(steps[3]==(2usize,r::Rule::Iter));assert(g::landing(states[3],states[4],r::Rule::Iter));
        assert(!crate::shared_replay::operational_mixed(programs(2)(states[3].current[2usize].unwrap())));
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn deletion_shape()
    ensures target()==surviving(),
{
    reveal(source);reveal(fp::example_prefix);reveal(surviving);reveal(base::setup);reveal_with_fuel(deletion::delete,12);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn target_shape()
    ensures {
        let kept=target();let states=source();
        &&& kept.len()==8 && kept.last().history.len()==4
        &&& kept[1].state.tables[2usize][ex::key(2)]==77 && kept[1].state.accumulators[2usize]==seq![1nat]
        &&& kept[5].state.accumulators[2usize]==seq![1nat,2nat,3nat] && kept[5].state.tables[0usize][ex::key(0)]==24
        &&& kept[6].state.accumulators[2usize].len()==0 && kept[6].state.tables[0usize][ex::key(0)]==10
        &&& kept.last().state.tables[0usize][ex::key(0)]==10 && kept.last().state.tables[1usize].is_empty() && kept.last().state.tables[2usize].is_empty()
        &&& history::index(states.last().history,1,1,3)==1 && history::index(states.last().history,1,1,4)==2 && history::index(states.last().history,1,1,5)==3
        &&& s::registered(kept.last().state,0) && kept.last().state.tables[0usize].dom().contains(ex::key(0)) && s::registered(kept.last().state,2)
    },
{
    actual_source();deletion_shape();reveal(source);reveal(fp::example_prefix);reveal(surviving);reveal(base::setup);
    reveal_with_fuel(g::restore,4);reveal_with_fuel(history::index,7);
    assert(target()[1].state.accumulators[2usize] =~= seq![1nat]);assert(target()[5].state.accumulators[2usize] =~= seq![1nat,2nat,3nat]);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn closed_transport()
    ensures {
        let states=source();let kept=target();let terminal=g::unload(states.last(),1);
        &&& kept.first()==states.first()
        &&& g::step(ex::library(),base::programs(),states.last(),terminal,1,r::Rule::Unload)
        &&& g::execution(ex::library(),base::programs(),states.push(terminal),labels().push((1usize,r::Rule::Unload)))
        &&& g::execution(ex::library(),base::programs(),kept,sh::labels_without(labels(),1))
        &&& g::well_formed(ex::library(),base::programs(),terminal) && g::well_formed(ex::library(),base::programs(),kept.last())
        &&& terminal.state.control==kept.last().state.control && obs::tables_related(ex::equality(),terminal.state,kept.last().state)
        &&& terminal.state.tables[1usize].is_empty() && kept.last().state.tables[1usize].is_empty()
    },
{
    actual_source();actual_fragment();sh::example_interface();
    full::closed_deletion(ex::equality(),ex::library(),base::programs(),setup(),setup_labels(),source(),labels(),1);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn final_observations()
    ensures {
        let states=source();let kept=target();let terminal=g::unload(states.last(),1);
        &&& g::step(ex::library(),base::programs(),kept[0],kept[1],2,r::Rule::Iter)
        &&& g::step(ex::library(),base::programs(),kept[5],kept[6],2,r::Rule::Unload)
        &&& terminal.state.tables[0usize][ex::key(0)]==10 && terminal.state.tables[2usize].is_empty()
    },
{
    target_shape();closed_transport();let states=source();let kept=target();let terminal=g::unload(states.last(),1);
    reveal_with_fuel(sh::labels_without,12);
    assert(sh::labels_without(labels(),1)[0]==(2usize,r::Rule::Iter));assert(sh::labels_without(labels(),1)[5]==(2usize,r::Rule::Unload));
    assert(s::registered(terminal.state,0));assert(terminal.state.tables[0usize].dom()==kept.last().state.tables[0usize].dom());
    assert(ex::equality()(ex::key(0),terminal.state.tables[0usize][ex::key(0)],kept.last().state.tables[0usize][ex::key(0)]));
    assert(s::registered(terminal.state,2));assert(terminal.state.tables[2usize].dom()==kept.last().state.tables[2usize].dom());assert(terminal.state.tables[2usize] =~= IMap::empty());
}

/// Both new forward publication and its own later partial inverse are real
/// steps, before final owner recovery, in source and constructed target alike.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn actual_generalized_table_deletion()
    ensures {
        let states=source();let kept=target();let terminal=g::unload(states.last(),1);
        &&& g::execution(ex::library(),base::programs(),setup(),setup_labels()) && setup().first()==g::empty::<int,nat>() && setup().last()==states.first()
        &&& g::execution(ex::library(),base::programs(),states,labels()) && full::fragment(base::programs(),states,labels(),1) && !previous::fragment(base::programs(),states,labels(),1)
        &&& states[3].state.tables[0usize][ex::key(0)]==15 && states[3].state.tables[1usize][ex::key(1)]==99 && states[3].state.accumulators[1usize]==seq![1nat,2nat]
        &&& g::step(ex::library(),base::programs(),states[3],states[4],2,r::Rule::Iter) && g::step(ex::library(),base::programs(),kept[0],kept[1],2,r::Rule::Iter)
        &&& states[4].state.tables[2usize][ex::key(2)]==77 && kept[1].state.tables[2usize][ex::key(2)]==77
        &&& states[8].state.accumulators[2usize]==seq![3nat,4nat,5nat] && kept[5].state.accumulators[2usize]==seq![1nat,2nat,3nat]
        &&& states[8].state.tables[0usize][ex::key(0)]==29 && kept[5].state.tables[0usize][ex::key(0)]==24
        &&& g::step(ex::library(),base::programs(),states[8],states[9],2,r::Rule::Unload) && g::step(ex::library(),base::programs(),kept[5],kept[6],2,r::Rule::Unload)
        &&& states[9].state.tables[0usize][ex::key(0)]==15 && kept[6].state.tables[0usize][ex::key(0)]==10
        &&& states[9].state.tables[2usize].is_empty()
        &&& history::index(states.last().history,1,1,3)==1 && history::index(states.last().history,1,1,4)==2 && history::index(states.last().history,1,1,5)==3
        &&& g::step(ex::library(),base::programs(),states.last(),terminal,1,r::Rule::Unload)
        &&& g::execution(ex::library(),base::programs(),states.push(terminal),labels().push((1usize,r::Rule::Unload)))
        &&& g::execution(ex::library(),base::programs(),kept,sh::labels_without(labels(),1))
        &&& terminal.state.control==kept.last().state.control && obs::tables_related(ex::equality(),terminal.state,kept.last().state)
        &&& terminal.state.tables[0usize][ex::key(0)]==10 && kept.last().state.tables[0usize][ex::key(0)]==10
        &&& terminal.state.tables[1usize].is_empty() && kept.last().state.tables[1usize].is_empty() && terminal.state.tables[2usize].is_empty() && kept.last().state.tables[2usize].is_empty()
        &&& states.first().history.len()==1 && states.last().history.len()==6 && kept.last().history.len()==4
    },
{
    actual_source();actual_fragment();target_shape();closed_transport();final_observations();
}

} // verus!
