//! A single actual foreign LIFO stack crosses the cut: old +7, new Child,
//! new Provision R77 and new +11. Its interior Unload retires the child and
//! revokes R; Remove then erases the child. The owner Q99/+5 finally restores.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, dependent_grammar as d, foreign_child_deletion as deletion,
    foreign_child_transport as child, grammar_lift as lift, mixed_grammar as g,
    mixed_observational_runs as obs, mixed_orchestration as orchestration, mixed_syntax as syntax,
    mixed_transposition as insert, observational_lift as ol, providing_owner_deletion as own,
    recovery_examples as ex, refinement as r, semantics as s, shared_execution as sh,
    shared_unload_execution as history, Binding, Phase, Port,
};
use vstd::prelude::*;
verus! {
pub open spec fn programs()->g::Programs<Port,int,int,(),nat> {
    |actor:usize| |id:nat|if actor==0 {g::Node::Dependent {node:d::Node::Provision {key:ex::key(0),value:10,next:None}}}
    else if actor==1 && id==0 {g::Node::Dependent {node:d::Node::Provision {key:ex::key(1),value:99,next:Some(1nat)}}}
    else if actor==1 {g::Node::Dependent {node:d::Node::Operation {operation:ex::key(0),argument:5,select:|_:()|None}}}
    else if actor==2 && id==0 {g::Node::Dependent {node:d::Node::Operation {operation:ex::key(0),argument:7,select:|_:()|Some(1nat)}}}
    else if actor==2 && id==1 {g::Node::Child {child:3,dependencies:ex::provided(0),provisions:ISet::empty(),root:0nat,next:Some(2nat)}}
    else if actor==2 && id==2 {g::Node::Dependent {node:d::Node::Provision {key:ex::key(2),value:77,next:Some(3nat)}}}
    else if actor==2 {g::Node::Dependent {node:d::Node::Operation {operation:ex::key(0),argument:11,select:|_:()|None}}}
    else {g::Node::Dependent {node:d::Node::Unit}}
}
#[verifier::opaque]
pub open spec fn setup()->Seq<g::Configuration<int,nat>> {
    let a0=g::empty::<int,nat>();let a1=insert::insert(a0,0,None,ISet::empty(),ex::provided(0),0nat);
    let a2=insert::insert(a1,1,None,ex::provided(0),ex::provided(1),0nat);let a3=insert::insert(a2,2,None,ex::provided(0),ex::provided(2),0nat);
    let a4=g::edit(a3,0,Phase::Loading,ISet::empty(),Some(0nat),Seq::empty());let a5=g::land(ex::library(),programs(),a4,0,Phase::Active);
    let a6=g::edit(a5,2,Phase::Loading,sh::example_view(),Some(0nat),Seq::empty());let a7=g::land(ex::library(),programs(),a6,2,Phase::Loading);
    seq![a0,a1,a2,a3,a4,a5,a6,a7]
}
pub open spec fn setup_labels()->Seq<(usize,r::Rule)> {seq![(0usize,r::Rule::Insert),(1usize,r::Rule::Insert),(2usize,r::Rule::Insert),(0usize,r::Rule::Begin),(0usize,r::Rule::Finish),(2usize,r::Rule::Begin),(2usize,r::Rule::Iter)]}
#[verifier::opaque]
pub open spec fn prefix()->Seq<g::Configuration<int,nat>> {
    let a0=setup().last();let a1=g::edit(a0,1,Phase::Loading,sh::example_view(),Some(0nat),Seq::empty());let a2=g::land(ex::library(),programs(),a1,1,Phase::Loading);
    let a3=g::land(ex::library(),programs(),a2,1,Phase::Active);let a4=g::land(ex::library(),programs(),a3,2,Phase::Loading);
    let a5=g::land(ex::library(),programs(),a4,2,Phase::Loading);let a6=g::land(ex::library(),programs(),a5,2,Phase::Active);
    seq![a0,a1,a2,a3,a4,a5,a6]
}
pub open spec fn prefix_labels()->Seq<(usize,r::Rule)> {seq![(1usize,r::Rule::Begin),(1usize,r::Rule::Iter),(1usize,r::Rule::Finish),(2usize,r::Rule::Iter),(2usize,r::Rule::Iter),(2usize,r::Rule::Finish)]}
#[verifier::opaque]
pub open spec fn source()->Seq<g::Configuration<int,nat>> {
    let a7=sh::retire(prefix().last(),2);let a8=g::edit(a7,2,Phase::Unloading,sh::example_view(),None,a7.state.accumulators[2usize]);let a9=g::unload(a8,2);
    let a10=orchestration::remove(a9,3);let a11=sh::retire(a10,1);let a12=g::edit(a11,1,Phase::Unloading,sh::example_view(),None,a11.state.accumulators[1usize]);
    prefix().push(a7).push(a8).push(a9).push(a10).push(a11).push(a12)
}
pub open spec fn labels()->Seq<(usize,r::Rule)> {prefix_labels()+seq![(2usize,r::Rule::Retire),(2usize,r::Rule::Leave),(2usize,r::Rule::Unload),(3usize,r::Rule::Remove),(1usize,r::Rule::Retire),(1usize,r::Rule::Leave)]}

pub proof fn component_members()
    ensures syntax::member(ex::library(),programs(),0,ex::provided(0),ex::provided(0),0nat),
        syntax::member(ex::library(),programs(),1,ex::provided(0).union(ex::provided(1)),ex::provided(1),0nat),
        syntax::member(ex::library(),programs(),2,ex::provided(0).union(ex::provided(2)),ex::provided(2),0nat),
{
    syntax::constructor_member(ex::library(),programs(),0,ex::provided(0),ex::provided(0),0nat);
    syntax::constructor_member(ex::library(),programs(),1,ex::provided(0).union(ex::provided(1)),ex::provided(1),1nat);
    syntax::constructor_member(ex::library(),programs(),1,ex::provided(0).union(ex::provided(1)),ex::provided(1),0nat);
    syntax::constructor_member(ex::library(),programs(),3,ex::provided(0),ISet::empty(),0nat);assert(ex::provided(0).union(ISet::empty()) =~= ex::provided(0));
    syntax::constructor_member(ex::library(),programs(),2,ex::provided(0).union(ex::provided(2)),ex::provided(2),3nat);
    syntax::constructor_member(ex::library(),programs(),2,ex::provided(0).union(ex::provided(2)),ex::provided(2),2nat);
    syntax::constructor_member(ex::library(),programs(),2,ex::provided(0).union(ex::provided(2)),ex::provided(2),1nat);
    syntax::constructor_member(ex::library(),programs(),2,ex::provided(0).union(ex::provided(2)),ex::provided(2),0nat);
}
#[verifier::spinoff_prover]
#[verifier::rlimit(35)]
pub proof fn actual_setup()
    ensures g::execution(ex::library(),programs(),setup(),setup_labels()),setup().first()==g::empty::<int,nat>(),
        g::well_formed(ex::library(),programs(),setup().last()),own::separated(setup().last().state,1),
        setup().last().history.len()==2,setup().last().state.accumulators[2usize]==seq![1nat],setup().last().current[2usize]==Some(1nat),
        setup().last().state.tables[0usize][ex::key(0)]==17,setup().last().state.tables[1usize].is_empty(),setup().last().state.control.fibers[1usize].phase==Phase::Inactive,
{
    component_members();sh::example_interface();reveal(setup);let states=setup();let steps=setup_labels();let lib=ex::library();let eq=ex::equality();
    assert(ISet::<Port>::empty().union(ex::provided(0)) =~= ex::provided(0));g::empty_well_formed(lib,programs());
    insert::insertion_step(lib,programs(),states[0],0,None,ISet::empty(),ex::provided(0),0nat);ol::configuration_preservation(eq,lib,programs(),states[0],states[1],0,r::Rule::Insert);
    insert::insertion_step(lib,programs(),states[1],1,None,ex::provided(0),ex::provided(1),0nat);ol::configuration_preservation(eq,lib,programs(),states[1],states[2],1,r::Rule::Insert);
    insert::insertion_step(lib,programs(),states[2],2,None,ex::provided(0),ex::provided(2),0nat);ol::configuration_preservation(eq,lib,programs(),states[2],states[3],2,r::Rule::Insert);
    assert(g::step(lib,programs(),states[3],states[4],0,r::Rule::Begin));assert(g::step(lib,programs(),states[4],states[5],0,r::Rule::Finish));
    sh::example_target(states[5].state,2);assert(g::step(lib,programs(),states[5],states[6],2,r::Rule::Begin));
    let binding=Binding {key:0,realm:0,provider:0};assert(lift::names_key(binding,ex::key(0)));assert(states[6].state.control.fibers[2usize].committed.contains(binding));
    assert(exists|b:Binding|states[6].state.control.fibers[2usize].committed.contains(b) && lift::names_key(b,ex::key(0)));assert(lift::resolve(states[6].state,2,ex::key(0))==Some(0usize));
    assert(g::step(lib,programs(),states[6],states[7],2,r::Rule::Iter));
    assert forall|i:int|0<=i<steps.len() implies g::step(lib,programs(),states[i],states[i+1],steps[i].0,steps[i].1) by {if i==0{}else if i==1{}else if i==2{}else if i==3{}else if i==4{}else if i==5{}else{assert(i==6);}}
    ol::from_empty_safe(eq,lib,programs(),states,steps);assert(states.last().state.accumulators[2usize] =~= seq![1nat]);
}
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn actual_landings()
    ensures g::execution(ex::library(),programs(),prefix(),prefix_labels()),prefix().first()==setup().last(),
        forall|i:int|0<=i<prefix().len() ==> g::well_formed(ex::library(),programs(),prefix()[i]),
        prefix().last().state.tables[0usize][ex::key(0)]==33,prefix().last().state.tables[1usize][ex::key(1)]==99,prefix().last().state.tables[2usize][ex::key(2)]==77,
        prefix().last().state.accumulators[2usize]==seq![1nat,4nat,5nat,6nat],prefix().last().state.accumulators[1usize]==seq![2nat,3nat],
        prefix().last().history[4].landed.receipt==(g::Receipt::<int>::Child {actor:2,child:3}),!prefix().last().state.control.fibers[3usize].retired,
        prefix().last().history.len()==7,
        prefix().last().history[2].landed.receipt==(g::Receipt::Table {receipt:lift::Receipt {actor:1,inverse:lift::Inverse::Provision {key:ex::key(1)}}}),
        prefix().last().history[3].landed.receipt==(g::Receipt::Table {receipt:lift::Receipt {actor:1,inverse:lift::Inverse::Operation {provider:0,key:ex::key(0),undo:|v:int|Some(v-5)}}}),
        forall|i:int|0<=i<7 ==> g::owner(#[trigger] prefix().last().history[i].landed.receipt)==if i==0 {0usize}else if i==2||i==3 {1usize}else{2usize},
{
    actual_setup();sh::example_interface();reveal(setup);reveal(prefix);let states=prefix();let steps=prefix_labels();let lib=ex::library();let eq=ex::equality();
    sh::example_target(states[0].state,1);assert(g::step(lib,programs(),states[0],states[1],1,r::Rule::Begin));assert(g::step(lib,programs(),states[1],states[2],1,r::Rule::Iter));
    let binding=Binding {key:0,realm:0,provider:0};assert(lift::names_key(binding,ex::key(0)));assert(states[2].state.control.fibers[1usize].committed.contains(binding));
    assert(exists|b:Binding|states[2].state.control.fibers[1usize].committed.contains(b) && lift::names_key(b,ex::key(0)));assert(lift::resolve(states[2].state,1,ex::key(0))==Some(0usize));
    assert(g::step(lib,programs(),states[2],states[3],1,r::Rule::Finish));
    assert(g::step(lib,programs(),states[3],states[4],2,r::Rule::Iter));assert(g::step(lib,programs(),states[4],states[5],2,r::Rule::Iter));
    assert(states[5].state.control.fibers[2usize].committed.contains(binding));assert(exists|b:Binding|states[5].state.control.fibers[2usize].committed.contains(b) && lift::names_key(b,ex::key(0)));assert(lift::resolve(states[5].state,2,ex::key(0))==Some(0usize));
    assert(g::step(lib,programs(),states[5],states[6],2,r::Rule::Finish));
    assert forall|i:int|0<=i<steps.len() implies g::step(lib,programs(),states[i],states[i+1],steps[i].0,steps[i].1) by {if i==0{}else if i==1{}else if i==2{}else if i==3{}else if i==4{}else{assert(i==5);}}
    ol::execution_preservation(eq,lib,programs(),states,steps);assert(states.last().state.accumulators[2usize] =~= seq![1nat,4nat,5nat,6nat]);assert(states.last().state.accumulators[1usize] =~= seq![2nat,3nat]);
}
#[verifier::spinoff_prover]
#[verifier::rlimit(45)]
pub proof fn actual_cleanup()
    ensures g::execution(ex::library(),programs(),source(),labels()),source().first()==setup().last(),deletion::fragment(programs(),source(),labels(),1),
        forall|i:int|0<=i<source().len() ==> g::well_formed(ex::library(),programs(),source()[i]),
        source()[8].state.accumulators[2usize]==seq![1nat,4nat,5nat,6nat],source()[9].state.control.fibers[3usize].retired,!s::registered(source()[10].state,3),
        source().last().state.tables[0usize][ex::key(0)]==15,source().last().state.tables[1usize][ex::key(1)]==99,source().last().state.tables[2usize].is_empty(),
        source().last().state.control.fibers[1usize].phase==Phase::Unloading,source().last().state.accumulators[1usize]==seq![2nat,3nat],
        s::registered(source().last().state,0),s::registered(source().last().state,2),source().last().state.tables[0usize].dom().contains(ex::key(0)),source().last().state.tables[1usize].dom().contains(ex::key(1)),
        source().last().state.control.fibers[1usize].dependencies==ex::provided(0),source().last().state.control.fibers[1usize].provisions==ex::provided(1),
{
    actual_setup();actual_landings();sh::example_interface();reveal(setup);reveal(prefix);reveal(source);let states=source();let steps=labels();let lib=ex::library();let eq=ex::equality();
    ch::concrete_child_retirement(states[6].state,2);assert(g::step(lib,programs(),states[6],states[7],2,r::Rule::Retire));ol::configuration_preservation(eq,lib,programs(),states[6],states[7],2,r::Rule::Retire);
    assert(g::step(lib,programs(),states[7],states[8],2,r::Rule::Leave));ol::configuration_preservation(eq,lib,programs(),states[7],states[8],2,r::Rule::Leave);
    reveal_with_fuel(g::restore,5);let tokens=states[8].state.accumulators[2usize];assert(tokens =~= seq![1nat,4nat,5nat,6nat]);
    let r6=g::undo(states[8].history[6].landed.receipt,states[8].state);assert(r6.is_some());
    let r5=g::undo(states[8].history[5].landed.receipt,r6.unwrap());assert(r5.is_some());
    let r4=g::undo(states[8].history[4].landed.receipt,r5.unwrap());assert(r4.is_some());
    let r1=g::undo(states[8].history[1].landed.receipt,r4.unwrap());assert(r1.is_some());
    assert(g::restore(states[8].history,tokens,states[8].state,2).is_some());assert(g::step(lib,programs(),states[8],states[9],2,r::Rule::Unload));ol::configuration_preservation(eq,lib,programs(),states[8],states[9],2,r::Rule::Unload);
    assert forall|n:usize|r::registered(states[9].state.control,n) implies states[9].state.control.fibers[n].parent!=Some(3usize) by {if n==0{}else if n==1{}else if n==2{}else{assert(n==3);}}
    assert(ch::remove_unreferenced(g::kind(states[9].history),states[9].state,3)) by {assert forall|actor:usize,token:nat|s::registered(states[9].state,actor) && states[9].state.accumulators[actor].contains(token) implies g::kind(states[9].history)(token)!=Some(3usize) by {if actor==0{assert(token==0);}else if actor==1{assert(token==2||token==3);}else if actor==2{}else{assert(actor==3);}}}
    assert(r::frame(states[9].state.control,states[10].state.control,3));assert(g::step(lib,programs(),states[9],states[10],3,r::Rule::Remove));
    ch::concrete_child_retirement(states[10].state,1);assert(g::step(lib,programs(),states[10],states[11],1,r::Rule::Retire));assert(g::step(lib,programs(),states[11],states[12],1,r::Rule::Leave));
    assert forall|i:int|0<=i<steps.len() implies g::step(lib,programs(),states[i],states[i+1],steps[i].0,steps[i].1) by {if i<6 {assert(states[i]==prefix()[i]);assert(states[i+1]==prefix()[i+1]);assert(steps[i]==prefix_labels()[i]);}else if i==6{}else if i==7{}else if i==8{}else if i==9{}else if i==10{}else{assert(i==11);}}
    ol::execution_preservation(eq,lib,programs(),states,steps);
    assert forall|i:int|0<=i<steps.len() && g::landing(states[i],states[i+1],steps[i].1) implies own::table_node(programs()(steps[i].0)(states[i].current[steps[i].0].unwrap())) || child::guard(programs(),states[i],steps[i].0,1) by {if i==1{}else if i==2{}else if i==3{}else if i==4{}else{assert(i==5);}}
    assert(deletion::fragment(programs(),states,steps,1));assert(states.last().state.accumulators[1usize] =~= seq![2nat,3nat]);
}

/// Concrete returned receipts suffice to evaluate the final two inverses;
/// no complete surviving execution is unfolded in this value calculation.
#[verifier::spinoff_prover]
#[verifier::rlimit(25)]
pub proof fn terminal_values()
    ensures {
        let terminal=g::unload(source().last(),1);
        &&& terminal.state.tables[0usize][ex::key(0)]==10 && terminal.state.tables[0usize].dom().contains(ex::key(0))
        &&& terminal.state.tables[1usize].is_empty() && terminal.state.tables[2usize].is_empty()
        &&& s::registered(terminal.state,0) && s::registered(terminal.state,2) && !s::registered(terminal.state,3)
    },
{
    actual_landings();actual_cleanup();reveal(source);reveal_with_fuel(g::restore,3);
    let a=source().last();assert(a.history==prefix().last().history);
    assert(a.state.accumulators[1usize] =~= seq![2nat,3nat]);
    let one=g::undo(a.history[3].landed.receipt,a.state);assert(one.is_some());
    let two=g::undo(a.history[2].landed.receipt,one.unwrap());assert(two.is_some());
    assert(g::restore(a.history,a.state.accumulators[1usize],a.state,1)==two);
}

pub proof fn token_indices()
    ensures history::index(source().last().history,2,1,1)==1 && history::index(source().last().history,2,1,4)==2,
        history::index(source().last().history,2,1,5)==3 && history::index(source().last().history,2,1,6)==4,
{
    actual_landings();reveal(source);assert(source().last().history==prefix().last().history);reveal_with_fuel(history::index,8);
}

/// Read the concrete source prefix separately from constructing its target.
/// Unfolding source() here must not also unfold the surviving execution.
#[verifier::spinoff_prover]
proof fn target_stack_source()
    ensures {
        let states=source().take(9);let steps=labels().take(8);let a=states.last();
        &&& g::execution(ex::library(),programs(),states,steps)
        &&& deletion::fragment(programs(),states,steps,1)
        &&& states.first()==setup().last()
        &&& s::registered(a.state,2) && a.history.len()==7
        &&& a.state.accumulators[2usize]==seq![1nat,4nat,5nat,6nat]
        &&& a.history[4].landed.receipt==(g::Receipt::<int>::Child {actor:2,child:3})
        &&& history::index(a.history,2,1,1)==1 && history::index(a.history,2,1,4)==2
        &&& history::index(a.history,2,1,5)==3 && history::index(a.history,2,1,6)==4
    },
{
    actual_landings();actual_cleanup();token_indices();
    let states=source().take(9);let steps=labels().take(8);
    assert(states.len()==9);assert(steps.len()==8);
    assert(states.first()==source().first());assert(states.last()==source()[8]);
    assert(g::execution(ex::library(),programs(),states,steps)) by {
        assert forall|i:int| 0<=i<steps.len() implies g::step(ex::library(),programs(),states[i],states[i+1],steps[i].0,steps[i].1) by {
            assert(states[i]==source()[i]);assert(states[i+1]==source()[i+1]);assert(steps[i]==labels()[i]);
            assert(g::step(ex::library(),programs(),source()[i],source()[i+1],labels()[i].0,labels()[i].1));
        }
    }
    assert(deletion::fragment(programs(),states,steps,1)) by {
        assert forall|i:int| 0<=i<steps.len() && g::landing(states[i],states[i+1],steps[i].1) implies {
            let node=programs()(steps[i].0)(states[i].current[steps[i].0].unwrap());
            own::table_node(node) || child::guard(programs(),states[i],steps[i].0,1)
        } by {assert(states[i]==source()[i]);assert(states[i+1]==source()[i+1]);assert(steps[i]==labels()[i]);}
        assert forall|i:int| #![trigger steps[i]] 0<=i<steps.len() implies {
            let label=steps[i];
            &&& ((label.1==r::Rule::Insert || label.1==r::Rule::Remove) ==> crate::dynamic_table_registry::guard(states[i],states[i+1],label.0,label.1,1))
            &&& (label.1==r::Rule::Unload ==> label.0!=1)
        } by {assert(states[i]==source()[i]);assert(states[i+1]==source()[i+1]);assert(steps[i]==labels()[i]);}
    }
    assert(labels()[8]==(2usize,r::Rule::Unload));
    assert(g::step(ex::library(),programs(),source()[8],source()[9],2,r::Rule::Unload));
    assert(s::registered(states.last().state,2));
    reveal(source);
    assert(states.last().history==source().last().history);
    assert(states.last().history==prefix().last().history);
    assert(g::well_formed(ex::library(),programs(),source()[8]));
    assert(states.last().state.accumulators[2usize]==seq![1nat,4nat,5nat,6nat]);
}

/// Extract only the four concrete token images and the retained Child receipt
/// from an authentic deletion relation. No target execution is unfolded here.
#[verifier::spinoff_prover]
proof fn compressed_target_stack(a:g::Configuration<int,nat>,target:g::Configuration<int,nat>)
    requires crate::providing_owner_transport::related(ex::equality(),a,target,2,1),
        s::registered(a.state,2),a.history.len()==7,a.state.accumulators[2usize]==seq![1nat,4nat,5nat,6nat],
        a.history[4].landed.receipt==(g::Receipt::<int>::Child {actor:2,child:3}),
        history::index(a.history,2,1,1)==1,history::index(a.history,2,1,4)==2,
        history::index(a.history,2,1,5)==3,history::index(a.history,2,1,6)==4,
    ensures target.state.accumulators[2usize]==seq![1nat,2nat,3nat,4nat],
        target.history[2].landed.receipt==(g::Receipt::<int>::Child {actor:2,child:3}),
{
    let tokens=a.state.accumulators[2usize];let renamed=history::rename(a.history,2,1,tokens);
    assert(target.state.accumulators[2usize]==renamed);
    assert(renamed.len()==4);
    assert(renamed[0]==history::index(a.history,2,1,1));
    assert(renamed[1]==history::index(a.history,2,1,4));
    assert(renamed[2]==history::index(a.history,2,1,5));
    assert(renamed[3]==history::index(a.history,2,1,6));
    assert(renamed =~= seq![1nat,2nat,3nat,4nat]);
    assert(history::histories(ex::equality(),a.history,target.history,2,1));
    assert(g::owner(a.history[4].landed.receipt)==2);
    assert(obs::receipt_related(ex::equality(),a.history[4].landed.receipt,target.history[history::index(a.history,2,1,4) as int].landed.receipt));
    assert(obs::receipt_related(ex::equality(),a.history[4].landed.receipt,target.history[2].landed.receipt));
}

/// The surviving prefix has its own actual mixed stack. Old token 1 stays
/// in place; the three new receipts use compressed tokens 2, 3, and 4.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn actual_target_stack()
    ensures {
        let states=source().take(9);let steps=labels().take(8);let target=deletion::delete(ex::library(),programs(),states,steps,1);
        &&& g::execution(ex::library(),programs(),target,sh::labels_without(steps,1))
        &&& target.last().state.accumulators[2usize]==seq![1nat,2nat,3nat,4nat]
        &&& target.last().history[2].landed.receipt==(g::Receipt::<int>::Child {actor:2,child:3})
        &&& states.last().state.accumulators[2usize]==seq![1nat,4nat,5nat,6nat]
    },
{
    actual_setup();target_stack_source();sh::example_interface();
    let states=source().take(9);let steps=labels().take(8);let lib=ex::library();let eq=ex::equality();
    assert(states.first()==setup().last());assert(states.first().history.len()==2);
    deletion::delete_execution(eq,lib,programs(),setup(),setup_labels(),states,steps,1);
    let target=deletion::delete(lib,programs(),states,steps,1).last();
    assert(crate::providing_owner_transport::related(eq,states.last(),target,2,1));
    compressed_target_stack(states.last(),target);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(45)]
pub proof fn actual_closed_deletion()
    ensures {
        let states=source();let target=deletion::delete(ex::library(),programs(),states,labels(),1);let terminal=g::unload(states.last(),1);
        &&& g::execution(ex::library(),programs(),target,sh::labels_without(labels(),1))
        &&& g::step(ex::library(),programs(),states.last(),terminal,1,r::Rule::Unload)
        &&& terminal.state.control==target.last().state.control && obs::tables_related(ex::equality(),terminal.state,target.last().state)
        &&& terminal.state.tables[0usize][ex::key(0)]==10 && target.last().state.tables[0usize][ex::key(0)]==10
        &&& terminal.state.tables[1usize].is_empty() && target.last().state.tables[1usize].is_empty() && target.last().state.tables[2usize].is_empty()
        &&& !s::registered(target.last().state,3)
        &&& history::index(states.last().history,2,1,1)==1 && history::index(states.last().history,2,1,4)==2
        &&& history::index(states.last().history,2,1,5)==3 && history::index(states.last().history,2,1,6)==4
    },
{
    actual_setup();actual_cleanup();sh::example_interface();deletion::closed_deletion(ex::equality(),ex::library(),programs(),setup(),setup_labels(),source(),labels(),1);
    terminal_values();token_indices();
    let terminal=g::unload(source().last(),1);let target=deletion::delete(ex::library(),programs(),source(),labels(),1).last();
    assert(terminal.state.tables[0usize][ex::key(0)]==10);assert(s::registered(terminal.state,0));assert(terminal.state.tables[0usize].dom().contains(ex::key(0)));
    assert(ex::equality()(ex::key(0),terminal.state.tables[0usize][ex::key(0)],target.state.tables[0usize][ex::key(0)]));
    assert(s::registered(target.state,2));assert(target.state.tables[2usize].dom().is_empty());assert(target.state.tables[2usize] =~= IMap::empty());
}
} // verus!
