//! Nonempty table-owner deletion with an authentic surviving child lifetime.
//!
//! Parent 2 creates child 3, captures its name in its actual journal, and later
//! Unloads to retire it. Only then can Remove erase child 3; obsolete history
//! still records the original captured name. Owner 1 finally restores Q99/+5.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, dependent_grammar as d, dynamic_table_deletion as table_delete,
    dynamic_table_registry as registry, foreign_child_transport as child, foreign_unload as fu,
    grammar_lift as lift, internal_old_unload as batch_state, mixed_grammar as g,
    mixed_observational_runs as obs, mixed_orchestration as orchestration, mixed_syntax as syntax,
    mixed_transposition as insert, observational_lift as ol, old_journal_closure as closure,
    providing_owner_deletion as own, providing_owner_transport as transport,
    recovery_examples as ex, refinement as r, semantics as s, shared_execution as sh,
    shared_unload_execution as history, strict_journal as sj, Binding, Phase, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn programs()->g::Programs<Port,int,int,(),nat> {
    |actor:usize| |id:nat|if actor==0 {g::Node::Dependent {node:d::Node::Provision {key:ex::key(0),value:10,next:None}}}
    else if actor==1 && id==0 {g::Node::Dependent {node:d::Node::Provision {key:ex::key(1),value:99,next:Some(1nat)}}}
    else if actor==1 {g::Node::Dependent {node:d::Node::Operation {operation:ex::key(0),argument:5,select:|_:()|None}}}
    else if actor==2 {g::Node::Child {child:3,dependencies:ex::provided(0),provisions:ISet::empty(),root:0nat,next:None}}
    else {g::Node::Dependent {node:d::Node::Unit}}
}
#[verifier::opaque]
pub open spec fn setup()->Seq<g::Configuration<int,nat>> {
    let a0=g::empty::<int,nat>();let a1=insert::insert(a0,0,None,ISet::empty(),ex::provided(0),0nat);
    let a2=insert::insert(a1,1,None,ex::provided(0),ex::provided(1),0nat);
    let a3=insert::insert(a2,2,None,ISet::empty(),ISet::empty(),0nat);
    let a4=g::edit(a3,0,Phase::Loading,ISet::empty(),Some(0nat),Seq::empty());let a5=g::land(ex::library(),programs(),a4,0,Phase::Active);
    seq![a0,a1,a2,a3,a4,a5]
}
pub open spec fn setup_labels()->Seq<(usize,r::Rule)> {seq![(0usize,r::Rule::Insert),(1usize,r::Rule::Insert),(2usize,r::Rule::Insert),(0usize,r::Rule::Begin),(0usize,r::Rule::Finish)]}
#[verifier::opaque]
pub open spec fn prefix()->Seq<g::Configuration<int,nat>> {
    let a0=setup().last();let a1=g::edit(a0,1,Phase::Loading,sh::example_view(),Some(0nat),Seq::empty());
    let a2=g::land(ex::library(),programs(),a1,1,Phase::Loading);let a3=g::land(ex::library(),programs(),a2,1,Phase::Active);
    let a4=g::edit(a3,2,Phase::Loading,ISet::empty(),Some(0nat),Seq::empty());seq![a0,a1,a2,a3,a4]
}
pub open spec fn prefix_labels()->Seq<(usize,r::Rule)> {seq![(1usize,r::Rule::Begin),(1usize,r::Rule::Iter),(1usize,r::Rule::Finish),(2usize,r::Rule::Begin)]}
#[verifier::opaque]
pub open spec fn source()->Seq<g::Configuration<int,nat>> {
    let a5=g::land(ex::library(),programs(),prefix().last(),2,Phase::Active);let a6=sh::retire(a5,2);
    let a7=g::edit(a6,2,Phase::Unloading,ISet::empty(),None,a6.state.accumulators[2usize]);let a8=g::unload(a7,2);
    let a9=orchestration::remove(a8,3);let a10=sh::retire(a9,1);
    let a11=g::edit(a10,1,Phase::Unloading,sh::example_view(),None,a10.state.accumulators[1usize]);
    prefix().push(a5).push(a6).push(a7).push(a8).push(a9).push(a10).push(a11)
}
pub open spec fn labels()->Seq<(usize,r::Rule)> {prefix_labels()+seq![(2usize,r::Rule::Finish),(2usize,r::Rule::Retire),(2usize,r::Rule::Leave),(2usize,r::Rule::Unload),(3usize,r::Rule::Remove),(1usize,r::Rule::Retire),(1usize,r::Rule::Leave)]}
#[verifier::opaque]
pub open spec fn target()->Seq<g::Configuration<int,nat>> {
    let cut=setup().last();let a1=g::edit(cut,2,Phase::Loading,ISet::empty(),Some(0nat),Seq::empty());
    let a2=g::land(ex::library(),programs(),a1,2,Phase::Active);let a3=sh::retire(a2,2);
    let a4=g::edit(a3,2,Phase::Unloading,ISet::empty(),None,a3.state.accumulators[2usize]);let a5=g::unload(a4,2);
    let a6=orchestration::remove(a5,3);let a7=sh::retire(a6,1);seq![cut,a1,a2,a3,a4,a5,a6,a7]
}

pub proof fn component_members()
    ensures syntax::member(ex::library(),programs(),0,ex::provided(0),ex::provided(0),0nat),
        syntax::member(ex::library(),programs(),1,ex::provided(0).union(ex::provided(1)),ex::provided(1),0nat),
        syntax::member(ex::library(),programs(),2,ISet::empty(),ISet::empty(),0nat),
{
    syntax::constructor_member(ex::library(),programs(),0,ex::provided(0),ex::provided(0),0nat);
    syntax::constructor_member(ex::library(),programs(),1,ex::provided(0).union(ex::provided(1)),ex::provided(1),1nat);
    syntax::constructor_member(ex::library(),programs(),1,ex::provided(0).union(ex::provided(1)),ex::provided(1),0nat);
    syntax::constructor_member(ex::library(),programs(),3,ex::provided(0),ISet::empty(),0nat);
    assert(ex::provided(0).union(ISet::empty()) =~= ex::provided(0));syntax::constructor_member(ex::library(),programs(),2,ISet::empty(),ISet::empty(),0nat);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(35)]
pub proof fn actual_prefix()
    ensures g::execution(ex::library(),programs(),setup(),setup_labels()),setup().first()==g::empty::<int,nat>(),setup().last()==prefix().first(),
        g::execution(ex::library(),programs(),prefix(),prefix_labels()),g::well_formed(ex::library(),programs(),prefix().first()),g::well_formed(ex::library(),programs(),prefix().last()),
        own::separated(prefix().first().state,1),table_delete::fragment(programs(),prefix(),prefix_labels(),1),
        prefix().first().state.control.fibers[1usize].phase==Phase::Inactive,prefix().first().state.tables[1usize].is_empty(),prefix().first().history.len()==1,
        prefix().last().state.tables[0usize][ex::key(0)]==15,prefix().last().state.tables[1usize][ex::key(1)]==99,
        prefix().last().state.accumulators[1usize]==seq![1nat,2nat],prefix().last().state.control.fibers[2usize].phase==Phase::Loading,
        prefix().last().state.control.fibers[1usize].provisions==ex::provided(1),
{
    component_members();sh::example_interface();reveal(setup);reveal(prefix);let lib=ex::library();let eq=ex::equality();let states=setup();let steps=setup_labels();
    assert(ISet::<Port>::empty().union(ex::provided(0)) =~= ex::provided(0));assert(ISet::<Port>::empty().union(ISet::empty()) =~= ISet::empty());
    g::empty_well_formed(lib,programs());
    insert::insertion_step(lib,programs(),states[0],0,None,ISet::empty(),ex::provided(0),0nat);ol::configuration_preservation(eq,lib,programs(),states[0],states[1],0,r::Rule::Insert);
    insert::insertion_step(lib,programs(),states[1],1,None,ex::provided(0),ex::provided(1),0nat);ol::configuration_preservation(eq,lib,programs(),states[1],states[2],1,r::Rule::Insert);
    insert::insertion_step(lib,programs(),states[2],2,None,ISet::empty(),ISet::empty(),0nat);ol::configuration_preservation(eq,lib,programs(),states[2],states[3],2,r::Rule::Insert);
    assert(g::step(lib,programs(),states[3],states[4],0,r::Rule::Begin));ol::configuration_preservation(eq,lib,programs(),states[3],states[4],0,r::Rule::Begin);
    assert(g::step(lib,programs(),states[4],states[5],0,r::Rule::Finish));ol::configuration_preservation(eq,lib,programs(),states[4],states[5],0,r::Rule::Finish);
    assert forall|i:int|0<=i<steps.len() implies g::step(lib,programs(),states[i],states[i+1],steps[i].0,steps[i].1) by {if i==0{}else if i==1{}else if i==2{}else if i==3{}else{assert(i==4);}}
    let ps=prefix();let ls=prefix_labels();sh::example_target(ps[0].state,1);
    assert(g::step(lib,programs(),ps[0],ps[1],1,r::Rule::Begin));assert(g::step(lib,programs(),ps[1],ps[2],1,r::Rule::Iter));
    assert(lift::names_key(Binding {key:0,realm:0,provider:0},ex::key(0)));assert(ps[2].state.control.fibers[1usize].committed.contains(Binding {key:0,realm:0,provider:0}));
    assert(exists|b:Binding|ps[2].state.control.fibers[1usize].committed.contains(b) && lift::names_key(b,ex::key(0)));assert(lift::resolve(ps[2].state,1,ex::key(0))==Some(0usize));
    assert(g::step(lib,programs(),ps[2],ps[3],1,r::Rule::Finish));assert(g::step(lib,programs(),ps[3],ps[4],2,r::Rule::Begin));
    assert forall|i:int|0<=i<ls.len() implies g::step(lib,programs(),ps[i],ps[i+1],ls[i].0,ls[i].1) by {if i==0{}else if i==1{}else if i==2{}else{assert(i==3);}}
    ol::execution_preservation(eq,lib,programs(),ps,ls);
    assert forall|i:int|0<=i<ls.len() && g::landing(ps[i],ps[i+1],ls[i].1) implies own::table_node(programs()(ls[i].0)(ps[i].current[ls[i].0].unwrap())) by {if i==1{}else{assert(i==2);}}
    assert forall|i:int| #![trigger ls[i]] 0<=i<ls.len() implies {
        let label=ls[i];
        &&& ((label.1==r::Rule::Insert || label.1==r::Rule::Remove) ==> registry::guard(ps[i],ps[i+1],label.0,label.1,1))
        &&& (label.1==r::Rule::Unload ==> label.0!=1 && crate::old_provision_journal::table_tokens(programs(),ps[i].history,ps[i].state.accumulators[label.0],label.0))
    } by {if i==0{}else if i==1{}else if i==2{}else{assert(i==3);}}
    assert(ps.last().state.accumulators[1usize] =~= seq![1nat,2nat]);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn actual_source()
    ensures {
        let states=source();
        &&& g::execution(ex::library(),programs(),states,labels()) && states.first()==setup().last()
        &&& forall|i:int|0<=i<states.len() ==> g::well_formed(ex::library(),programs(),states[i])
        &&& states[5].state.accumulators[2usize]==seq![3nat] && states[5].roots[3usize]==0nat && states[5].state.control.fibers[3usize].parent==Some(2usize)
        &&& states[7].state.accumulators[2usize]==seq![3nat] && child::child_tokens(states[7].history,states[7].state.accumulators[2usize],2)
        &&& !states[7].state.control.fibers[3usize].retired && states[8].state.control.fibers[3usize].retired
        &&& states[8].state.accumulators[2usize].len()==0 && !s::registered(states[9].state,3)
        &&& g::step(ex::library(),programs(),states[7],states[8],2,r::Rule::Unload) && g::step(ex::library(),programs(),states[8],states[9],3,r::Rule::Remove)
        &&& states.last().history[3].landed.receipt==g::Receipt::<int>::Child {actor:2,child:3}
        &&& states.last().state.control.fibers[1usize].phase==Phase::Unloading && states.last().state.accumulators[1usize]==seq![1nat,2nat]
        &&& states.last().state.tables[0usize][ex::key(0)]==15 && states.last().state.tables[1usize][ex::key(1)]==99
    },
{
    actual_prefix();sh::example_interface();reveal(setup);reveal(prefix);reveal(source);let states=source();let steps=labels();let lib=ex::library();let eq=ex::equality();
    assert(states[4]==prefix().last());assert(g::step(lib,programs(),states[4],states[5],2,r::Rule::Finish));ol::configuration_preservation(eq,lib,programs(),states[4],states[5],2,r::Rule::Finish);
    ch::concrete_child_retirement(states[5].state,2);assert(g::step(lib,programs(),states[5],states[6],2,r::Rule::Retire));ol::configuration_preservation(eq,lib,programs(),states[5],states[6],2,r::Rule::Retire);
    assert(g::step(lib,programs(),states[6],states[7],2,r::Rule::Leave));ol::configuration_preservation(eq,lib,programs(),states[6],states[7],2,r::Rule::Leave);
    assert(child::child_tokens(states[7].history,states[7].state.accumulators[2usize],2)) by {assert(states[7].state.accumulators[2usize] =~= seq![3nat]);}
    child::retained_children_defined(eq,lib,programs(),states[7],states[7].state.accumulators[2usize],2);
    assert(g::step(lib,programs(),states[7],states[8],2,r::Rule::Unload));ol::configuration_preservation(eq,lib,programs(),states[7],states[8],2,r::Rule::Unload);reveal_with_fuel(g::restore,2);
    assert(states[8].state.control.fibers[3usize].retired);assert(states[8].state.control.fibers[3usize].phase==Phase::Inactive);
    assert forall|n:usize|r::registered(states[8].state.control,n) implies states[8].state.control.fibers[n].parent!=Some(3usize) by {if n==0{}else if n==1{}else if n==2{}else{assert(n==3);}}
    assert(ch::remove_unreferenced(g::kind(states[8].history),states[8].state,3)) by {
        assert forall|actor:usize,token:nat|s::registered(states[8].state,actor) && states[8].state.accumulators[actor].contains(token) implies g::kind(states[8].history)(token)!=Some(3usize) by {
            if actor==0 {assert(token==0);}else if actor==1 {assert(token==1 || token==2);}else if actor==2{}else {assert(actor==3);}
        }
    }
    assert(r::frame(states[8].state.control,states[9].state.control,3));assert(g::step(lib,programs(),states[8],states[9],3,r::Rule::Remove));
    ch::concrete_child_retirement(states[9].state,1);assert(g::step(lib,programs(),states[9],states[10],1,r::Rule::Retire));assert(g::step(lib,programs(),states[10],states[11],1,r::Rule::Leave));
    assert forall|i:int|0<=i<steps.len() implies g::step(lib,programs(),states[i],states[i+1],steps[i].0,steps[i].1) by {
        if i<4 {assert(states[i]==prefix()[i]);assert(states[i+1]==prefix()[i+1]);assert(steps[i]==prefix_labels()[i]);}
        else if i==4{}else if i==5{}else if i==6{}else if i==7{}else if i==8{}else if i==9{}else {assert(i==10);}
    }
    ol::execution_preservation(eq,lib,programs(),states,steps);assert(states.last().state.accumulators[1usize] =~= seq![1nat,2nat]);
}

/// Constructor equations are established separately from the semantic
/// transport, keeping the actual bridge proof independent of giant expansions.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn bridge_shapes()
    ensures {
        let states=source();let kept=target();let lib=ex::library();
        &&& states.len()==12 && kept.len()==8 && states[4]==prefix().last() && kept.first()==states.first()
        &&& table_delete::delete(lib,programs(),prefix(),prefix_labels(),1)==kept.take(2)
        &&& transport::advance(lib,programs(),states[4],states[5],kept[1],2,r::Rule::Finish,1)==kept[2]
        &&& transport::advance(lib,programs(),states[5],states[6],kept[2],2,r::Rule::Retire,1)==kept[3]
        &&& transport::advance(lib,programs(),states[6],states[7],kept[3],2,r::Rule::Leave,1)==kept[4]
        &&& g::unload(kept[4],2)==kept[5]
        &&& registry::advance(lib,programs(),states[8],states[9],kept[5],3,r::Rule::Remove,1)==kept[6]
        &&& transport::advance(lib,programs(),states[9],states[10],kept[6],1,r::Rule::Retire,1)==kept[7]
        &&& transport::advance(lib,programs(),states[10],states[11],kept[7],1,r::Rule::Leave,1)==kept[7]
    },
{
    reveal(setup);reveal(prefix);reveal(source);reveal(target);reveal_with_fuel(table_delete::delete,5);
    assert(target().take(2) =~= seq![target()[0],target()[1]]);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(25)]
pub proof fn target_values()
    ensures {
        let states=source();let kept=target();
        &&& kept[4].state.accumulators[2usize]==seq![1nat] && kept[4].history[1].landed.receipt==states[7].history[3].landed.receipt
        &&& kept[5].state.control.fibers[3usize].retired && !s::registered(kept[6].state,3) && history::index(states.last().history,1,1,3)==1
        &&& kept.last().state.tables[0usize][ex::key(0)]==10 && kept.last().state.tables[0usize].dom().contains(ex::key(0)) && s::registered(kept.last().state,0)
        &&& kept.last().state.tables[1usize].is_empty()
    },
{
    actual_prefix();actual_source();reveal(setup);reveal(prefix);reveal(source);reveal(target);reveal_with_fuel(g::restore,2);reveal_with_fuel(history::index,5);
    assert(target()[4].state.accumulators[2usize] =~= seq![1nat]);
}

pub open spec fn actions_after_parent()->Seq<fu::Action<IMap<Port,int>>> {
    let actions=batch_state::landing_catalogue(ex::library(),programs(),prefix(),prefix_labels(),1);
    let call=fu::entry_pair(ex::library(),programs(),g::entry(ex::library(),programs(),source()[4],2),1);
    actions.push(fu::Action::Forward {call}).push(fu::Action::Identity).push(fu::Action::Identity).push(fu::Action::Identity)
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn parent_lifetime()
    ensures {
        let states=source();let kept=target();let lib=ex::library();let eq=ex::equality();
        &&& g::step(lib,programs(),kept[0],kept[1],2,r::Rule::Begin)
        &&& g::step(lib,programs(),kept[1],kept[2],2,r::Rule::Finish)
        &&& g::step(lib,programs(),kept[2],kept[3],2,r::Rule::Retire)
        &&& g::step(lib,programs(),kept[3],kept[4],2,r::Rule::Leave)
        &&& g::step(lib,programs(),kept[4],kept[5],2,r::Rule::Unload)
        &&& g::well_formed(lib,programs(),states[8]) && g::well_formed(lib,programs(),kept[5])
        &&& transport::related(eq,states[8],kept[5],1,1) && own::separated(states[8].state,1)
        &&& batch_state::synchronized(eq,actions_after_parent(),states[8],kept[5])
        &&& own::pinned_tokens(states[8].history,states[8].state.accumulators[1usize],states[8].state,1)
        &&& sh::receipt_word(states[8].history,states[8].state.accumulators[1usize])==sj::journal(fu::events(actions_after_parent()))
    },
{
    actual_prefix();actual_source();bridge_shapes();sh::example_interface();let lib=ex::library();let eq=ex::equality();let states=source();let kept=target();
    table_delete::delete_execution(eq,lib,programs(),setup(),setup_labels(),prefix(),prefix_labels(),1);
    crate::old_receipt_support::history_from_empty(eq,lib,programs(),setup(),setup_labels());
    table_delete::actual_journal(eq,lib,programs(),prefix(),prefix_labels(),1);
    let actions=batch_state::landing_catalogue(lib,programs(),prefix(),prefix_labels(),1);
    assert(table_delete::delete(lib,programs(),prefix(),prefix_labels(),1)==seq![kept[0],kept[1]]) by {assert(kept.take(2) =~= seq![kept[0],kept[1]]);}
    assert(labels()[4]==(2usize,r::Rule::Finish));assert(g::step(lib,programs(),states[4],states[5],labels()[4].0,labels()[4].1));
    assert(labels()[5]==(2usize,r::Rule::Retire));assert(g::step(lib,programs(),states[5],states[6],labels()[5].0,labels()[5].1));
    assert(labels()[6]==(2usize,r::Rule::Leave));assert(g::step(lib,programs(),states[6],states[7],labels()[6].0,labels()[6].1));
    assert(child::guard(programs(),states[4],2,1));child::synchronized_landing(eq,lib,programs(),states[4],states[5],kept[1],actions,1,1,2,r::Rule::Finish);
    let call=fu::entry_pair(lib,programs(),g::entry(lib,programs(),states[4],2),1);let a1=actions.push(fu::Action::Forward {call});assert(!call.own);child::foreign_word(actions,fu::Action::Forward {call});
    child::control_transport(eq,lib,programs(),states[5],states[6],kept[2],a1,1,1,2,r::Rule::Retire);let a2=a1.push(fu::Action::Identity);child::foreign_word(a1,fu::Action::Identity);
    child::control_transport(eq,lib,programs(),states[6],states[7],kept[3],a2,1,1,2,r::Rule::Leave);let a3=a2.push(fu::Action::Identity);child::foreign_word(a2,fu::Action::Identity);
    child::unload_transport(eq,lib,programs(),states[7],states[8],kept[4],a3,1,1,2);let a4=a3.push(fu::Action::Identity);child::foreign_word(a3,fu::Action::Identity);
    assert(actions_after_parent()==a4);
    assert(sj::journal(fu::events(a4))==sj::journal(fu::events(actions)));
    assert(g::step(lib,programs(),kept[0],kept[1],2,r::Rule::Begin));
}

#[verifier::spinoff_prover]
#[verifier::rlimit(45)]
pub proof fn actual_target_and_closure()
    ensures {
        let states=source();let kept=target();let terminal=g::unload(states.last(),1);
        &&& g::execution(ex::library(),programs(),kept,sh::labels_without(labels(),1)) && kept.first()==states.first()
        &&& g::step(ex::library(),programs(),kept[1],kept[2],2,r::Rule::Finish) && g::step(ex::library(),programs(),kept[4],kept[5],2,r::Rule::Unload)
        &&& kept[4].state.accumulators[2usize]==seq![1nat] && kept[4].history[1].landed.receipt==states[7].history[3].landed.receipt
        &&& kept[5].state.control.fibers[3usize].retired && !s::registered(kept[6].state,3) && history::index(states.last().history,1,1,3)==1
        &&& g::step(ex::library(),programs(),kept[5],kept[6],3,r::Rule::Remove)
        &&& g::step(ex::library(),programs(),states.last(),terminal,1,r::Rule::Unload)
        &&& g::execution(ex::library(),programs(),states.push(terminal),labels().push((1usize,r::Rule::Unload)))
        &&& terminal.state.control==kept.last().state.control && obs::tables_related(ex::equality(),terminal.state,kept.last().state)
        &&& terminal.state.tables[0usize][ex::key(0)]==10 && kept.last().state.tables[0usize][ex::key(0)]==10
        &&& terminal.state.tables[1usize].is_empty() && kept.last().state.tables[1usize].is_empty()
    },
{
    actual_source();bridge_shapes();target_values();parent_lifetime();sh::example_interface();let lib=ex::library();let eq=ex::equality();let states=source();let kept=target();
    let a4=actions_after_parent();
    assert(labels()[9]==(1usize,r::Rule::Retire));assert(g::step(lib,programs(),states[9],states[10],labels()[9].0,labels()[9].1));
    assert(labels()[10]==(1usize,r::Rule::Leave));assert(g::step(lib,programs(),states[10],states[11],labels()[10].0,labels()[10].1));
    registry::synchronized_registry(eq,lib,programs(),states[8],states[9],kept[5],a4,1,1,3,r::Rule::Remove);let a5=a4.push(fu::Action::Identity);child::foreign_word(a4,fu::Action::Identity);
    registry::pinned_journal(eq,lib,programs(),states[8],states[9],3,r::Rule::Remove,1);
    child::control_transport(eq,lib,programs(),states[9],states[10],kept[6],a5,1,1,1,r::Rule::Retire);let a6=a5.push(fu::Action::Identity);child::foreign_word(a5,fu::Action::Identity);
    child::control_transport(eq,lib,programs(),states[10],states[11],kept[7],a6,1,1,1,r::Rule::Leave);let a7=a6.push(fu::Action::Identity);child::foreign_word(a6,fu::Action::Identity);
    assert(sj::journal(fu::events(a7))==sj::journal(fu::events(a4)));
    closure::close_from_strict_word(eq,lib,programs(),states.last(),kept.last(),1);closure::append_execution(lib,programs(),states,labels(),g::unload(states.last(),1),1,r::Rule::Unload);
    reveal_with_fuel(sh::labels_without,12);let steps=sh::labels_without(labels(),1);
    assert forall|i:int|0<=i<steps.len() implies g::step(lib,programs(),kept[i],kept[i+1],steps[i].0,steps[i].1) by {if i==0{}else if i==1{}else if i==2{}else if i==3{}else if i==4{}else if i==5{}else{assert(i==6);}}
    let terminal=g::unload(states.last(),1);assert(s::registered(terminal.state,0));assert(terminal.state.tables[0usize].dom()==kept.last().state.tables[0usize].dom());
    assert(ex::equality()(ex::key(0),terminal.state.tables[0usize][ex::key(0)],kept.last().state.tables[0usize][ex::key(0)]));
}

/// A retired, inactive child still cannot be removed while its parent's real
/// inverse token is live. The same obsolete receipt is allowed after Unload.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn pending_inverse_blocks_remove()
    ensures {
        let before=sh::retire(source()[7],3);let erased=orchestration::remove(before,3);
        &&& g::step(ex::library(),programs(),source()[7],before,3,r::Rule::Retire)
        &&& before.state.control.fibers[3usize].retired && before.state.control.fibers[3usize].phase==Phase::Inactive && before.state.tables[3usize].is_empty()
        &&& !ch::remove_unreferenced(g::kind(before.history),before.state,3)
        &&& !g::step(ex::library(),programs(),before,erased,3,r::Rule::Remove)
    },
{
    actual_source();reveal(setup);reveal(prefix);reveal(source);let before=sh::retire(source()[7],3);
    ch::concrete_child_retirement(source()[7].state,3);assert(g::step(ex::library(),programs(),source()[7],before,3,r::Rule::Retire));
    assert(before.state.accumulators[2usize].contains(3nat));assert(g::kind(before.history)(3nat)==Some(3usize));assert(s::registered(before.state,2));
}

} // verus!
