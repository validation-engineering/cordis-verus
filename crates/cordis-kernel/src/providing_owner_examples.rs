//! A nonempty private provision, shared updates and an actual foreign Unload.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, dependent_grammar as d, grammar_lift as lift, mixed_grammar as g,
    mixed_observational_runs as obs, mixed_syntax as syntax, mixed_transposition as t,
    observational_lift as ol, providing_owner_deletion as source_proof,
    providing_owner_execution as deletion, recovery_examples as ex, refinement as r,
    semantics as s, shared_execution as sh, shared_unload_execution as history, Binding, Phase,
    Port,
};
use vstd::prelude::*;

verus! {
pub open spec fn programs()->g::Programs<Port,int,int,(),bool> {
    |actor:usize| |shift:bool|if !shift {
        g::Node::Dependent {node:d::Node::Provision {key:ex::key(actor),value:if actor==0 {10}else{99},next:if actor==1 {Some(true)}else{None}}}
    } else {g::Node::Dependent {node:d::Node::Operation {operation:ex::key(0),argument:if actor==1 {5}else{7},select:|_:()|None}}}
}
#[verifier::opaque]
pub open spec fn trace()->Seq<g::Configuration<int,bool>> {
    let empty=g::empty::<int,bool>();let a1=t::insert(empty,0,None,ISet::empty(),ex::provided(0),false);
    let a2=t::insert(a1,1,None,ex::provided(0),ex::provided(1),false);let a3=t::insert(a2,2,None,ex::provided(0),ISet::empty(),true);
    let a4=g::edit(a3,0,Phase::Loading,ISet::empty(),Some(false),Seq::empty());let initial=g::land(ex::library(),programs(),a4,0,Phase::Active);
    let b1=g::edit(initial,1,Phase::Loading,sh::example_view(),Some(false),Seq::empty());let b2=g::land(ex::library(),programs(),b1,1,Phase::Loading);
    let b3=g::land(ex::library(),programs(),b2,1,Phase::Active);
    let b4=g::edit(b3,2,Phase::Loading,sh::example_view(),Some(true),Seq::empty());let b5=g::land(ex::library(),programs(),b4,2,Phase::Active);
    let b6=sh::retire(b5,1);let b7=g::edit(b6,1,Phase::Unloading,sh::example_view(),None,b6.state.accumulators[1usize]);
    let b8=sh::retire(b7,2);let b9=g::edit(b8,2,Phase::Unloading,sh::example_view(),None,b8.state.accumulators[2usize]);
    seq![initial,b1,b2,b3,b4,b5,b6,b7,b8,b9,g::unload(b9,2)]
}
pub open spec fn labels()->Seq<(usize,r::Rule)> {
    seq![(1usize,r::Rule::Begin),(1usize,r::Rule::Iter),(1usize,r::Rule::Finish),
        (2usize,r::Rule::Begin),(2usize,r::Rule::Finish),(1usize,r::Rule::Retire),(1usize,r::Rule::Leave),
        (2usize,r::Rule::Retire),(2usize,r::Rule::Leave),(2usize,r::Rule::Unload)]
}
pub open spec fn bootstrap()->Seq<g::Configuration<int,bool>> {
    let empty=g::empty::<int,bool>();let a1=t::insert(empty,0,None,ISet::empty(),ex::provided(0),false);
    let a2=t::insert(a1,1,None,ex::provided(0),ex::provided(1),false);let a3=t::insert(a2,2,None,ex::provided(0),ISet::empty(),true);
    let a4=g::edit(a3,0,Phase::Loading,ISet::empty(),Some(false),Seq::empty());
    seq![empty,a1,a2,a3,a4,trace().first()]
}
pub open spec fn bootstrap_labels()->Seq<(usize,r::Rule)> {
    seq![(0usize,r::Rule::Insert),(1usize,r::Rule::Insert),(2usize,r::Rule::Insert),(0usize,r::Rule::Begin),(0usize,r::Rule::Finish)]
}
/// The nonempty initial provider history is reached by actual lifecycle steps
/// from the empty registry, rather than supplied as a history-shaped value.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn bootstrap_execution()
    ensures g::execution(ex::library(),programs(),bootstrap(),bootstrap_labels()),
        bootstrap().first()==g::empty::<int,bool>(),bootstrap().last()==trace().first(),
        g::well_formed(ex::library(),programs(),trace().first()),
{
    reveal(trace);sh::example_interface();let lib=ex::library();let states=trace();
    syntax::constructor_member(lib,programs(),0,ex::provided(0),ex::provided(0),false);
    syntax::constructor_member(lib,programs(),1,ex::provided(0).union(ex::provided(1)),ex::provided(1),true);
    syntax::constructor_member(lib,programs(),1,ex::provided(0).union(ex::provided(1)),ex::provided(1),false);
    syntax::constructor_member(lib,programs(),2,ex::provided(0),ISet::empty(),true);
    assert(ISet::<Port>::empty().union(ex::provided(0)) =~= ex::provided(0));assert(ex::provided(0).union(ISet::empty()) =~= ex::provided(0));
    let empty=g::empty::<int,bool>();let a1=t::insert(empty,0,None,ISet::empty(),ex::provided(0),false);
    let a2=t::insert(a1,1,None,ex::provided(0),ex::provided(1),false);let a3=t::insert(a2,2,None,ex::provided(0),ISet::empty(),true);
    let a4=g::edit(a3,0,Phase::Loading,ISet::empty(),Some(false),Seq::empty());
    g::empty_well_formed(lib,programs());t::insertion_step(lib,programs(),empty,0,None,ISet::empty(),ex::provided(0),false);
    ol::configuration_preservation(ex::equality(),lib,programs(),empty,a1,0,r::Rule::Insert);
    t::insertion_step(lib,programs(),a1,1,None,ex::provided(0),ex::provided(1),false);ol::configuration_preservation(ex::equality(),lib,programs(),a1,a2,1,r::Rule::Insert);
    t::insertion_step(lib,programs(),a2,2,None,ex::provided(0),ISet::empty(),true);ol::configuration_preservation(ex::equality(),lib,programs(),a2,a3,2,r::Rule::Insert);
    assert(g::step(lib,programs(),a3,a4,0,r::Rule::Begin));ol::configuration_preservation(ex::equality(),lib,programs(),a3,a4,0,r::Rule::Begin);
    assert(g::step(lib,programs(),a4,states[0],0,r::Rule::Finish));ol::configuration_preservation(ex::equality(),lib,programs(),a4,states[0],0,r::Rule::Finish);

    let states=bootstrap();let steps=bootstrap_labels();
    assert(g::execution(lib,programs(),states,steps)) by {
        assert forall|i:int| 0<=i<steps.len() implies g::step(lib,programs(),states[i],states[i+1],steps[i].0,steps[i].1) by {
            if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else {assert(i==4);}
        }
    }
}
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn actual_source()
    ensures g::execution(ex::library(),programs(),trace(),labels()),g::well_formed(ex::library(),programs(),trace().first()),
        source_proof::separated(trace().first().state,1),source_proof::fragment(programs(),trace(),labels(),1,1),
        trace().first().history.len()==1,trace().last().history.len()==4,
        trace().first().state.control.fibers[1usize].phase==Phase::Inactive,trace().first().state.tables[1usize].is_empty(),
        trace().first().state.control.fibers[1usize].provisions==ex::provided(1),
        trace().last().state.control.fibers[1usize].phase==Phase::Unloading,
        trace()[9].state.accumulators[2usize]==seq![3nat],
        trace().last().state.tables[0usize][ex::key(0)]==15,trace().last().state.tables[1usize][ex::key(1)]==99,
{
    reveal(trace);sh::example_interface();let lib=ex::library();let states=trace();let steps=labels();
    bootstrap_execution();
    sh::example_target(states[0].state,1);assert(g::step(lib,programs(),states[0],states[1],1,r::Rule::Begin));
    assert(g::step(lib,programs(),states[1],states[2],1,r::Rule::Iter));
    assert(lift::names_key(Binding {key:0,realm:0,provider:0},ex::key(0)));
    assert(states[2].state.control.fibers[1usize].committed.contains(Binding {key:0,realm:0,provider:0}));
    assert(exists|b:Binding| states[2].state.control.fibers[1usize].committed.contains(b) && lift::names_key(b,ex::key(0)));
    assert(lift::resolve(states[2].state,1,ex::key(0))==Some(0usize));assert(g::step(lib,programs(),states[2],states[3],1,r::Rule::Finish));
    sh::example_target(states[3].state,2);assert(g::step(lib,programs(),states[3],states[4],2,r::Rule::Begin));
    assert(states[4].state.control.fibers[2usize].committed.contains(Binding {key:0,realm:0,provider:0}));
    assert(exists|b:Binding| states[4].state.control.fibers[2usize].committed.contains(b) && lift::names_key(b,ex::key(0)));
    assert(lift::resolve(states[4].state,2,ex::key(0))==Some(0usize));assert(g::step(lib,programs(),states[4],states[5],2,r::Rule::Finish));
    ch::concrete_child_retirement(states[5].state,1);assert(g::step(lib,programs(),states[5],states[6],1,r::Rule::Retire));assert(g::step(lib,programs(),states[6],states[7],1,r::Rule::Leave));
    ch::concrete_child_retirement(states[7].state,2);assert(g::step(lib,programs(),states[7],states[8],2,r::Rule::Retire));assert(g::step(lib,programs(),states[8],states[9],2,r::Rule::Leave));
    assert(states[9].state.accumulators[2usize] =~= seq![3nat]);reveal_with_fuel(g::restore,2);assert(g::step(lib,programs(),states[9],states[10],2,r::Rule::Unload));
    assert(g::execution(lib,programs(),states,steps)) by {
        assert forall|i:int| 0<=i<steps.len() implies g::step(lib,programs(),states[i],states[i+1],steps[i].0,steps[i].1) by {
            if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else if i==5 {} else if i==6 {} else if i==7 {} else if i==8 {} else {assert(i==9);}
        }
    }
    assert(source_proof::separated(states[0].state,1)) by {
        assert forall|n:usize| s::registered(states[0].state,n) && n!=1 implies crate::dependent_lift::declarations(states[0].state,n).disjoint(states[0].state.control.fibers[1usize].provisions) by {
            if n==0 {} else {assert(n==2);}
        }
    }
    assert(source_proof::fragment(programs(),states,steps,1,1)) by {
        assert forall|i:int| 0<=i<steps.len() && g::landing(states[i],states[i+1],steps[i].1) implies {
            let node=programs()(steps[i].0)(states[i].current[steps[i].0].unwrap());source_proof::table_node(node) && (steps[i].0!=1 ==> crate::shared_replay::operational_mixed(node))
        } by {if i==1 {} else if i==2 {} else {assert(i==4);}}
        assert forall|i:int| #![trigger steps[i]] 0<=i<steps.len() implies {
            let label=steps[i];label.1!=r::Rule::Insert && label.1!=r::Rule::Remove
                && (label.1==r::Rule::Unload ==> label.0!=1 && crate::foreign_unload::tracked_tokens(states[i].history,states[i].state.accumulators[label.0],1,label.0))
        } by {if i<9 {} else {assert(i==9);}}
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn source_shape()
    ensures trace().len()==11,trace()[9].history==trace().last().history,
        g::owner(trace().last().history[1].landed.receipt)==1,g::owner(trace().last().history[2].landed.receipt)==1,
        g::owner(trace().last().history[3].landed.receipt)==2,
        g::unload(trace().last(),1).state.tables[0usize].dom().contains(ex::key(0)),
        g::unload(trace().last(),1).state.tables[0usize][ex::key(0)]==10,
        s::registered(g::unload(trace().last(),1).state,0),
{
    actual_source();reveal(trace);reveal_with_fuel(g::restore,3);
    assert(trace().last().state.accumulators[1usize] =~= seq![1nat,2nat]);
}
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn source_indices()
    ensures trace().len()==11,trace()[9].history==trace().last().history,
        g::owner(trace().last().history[1].landed.receipt)==1,g::owner(trace().last().history[2].landed.receipt)==1,
        g::owner(trace().last().history[3].landed.receipt)==2,
        history::index(trace().last().history,1,1,3)==1,history::index(trace().last().history,1,1,4)==2,
{
    actual_source();reveal(trace);reveal_with_fuel(history::index,5);
}
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
proof fn source_history_head()
    ensures trace().first().history[0]==trace().last().history[0],
{
    reveal(trace);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
proof fn deletion_history()
    ensures {
        let source=trace();let target=deletion::delete(ex::library(),programs(),source,labels(),1);
        &&& g::execution(ex::library(),programs(),target,sh::labels_without(labels(),1))
        &&& source.first().history.len()==1 && source.last().history.len()==4
        &&& history::histories(ex::equality(),source.last().history,target.last().history,1,1)
    },
{
    actual_source();sh::example_interface();
    deletion::delete_execution(ex::equality(),ex::library(),programs(),trace(),labels(),1);
}

// Separate the full deletion theorem from its pre-Unload prefix. Each call
// exposes many quantified invariants; their consumers need only these concrete
// history facts and one final lifecycle step, not both theorem contexts at once.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
proof fn compressed_target()
    ensures {
        let source=trace();let target=deletion::delete(ex::library(),programs(),source,labels(),1);
        &&& source.len()==11 && target.len()==7
        &&& source.first().history.len()==1 && source.last().history.len()==4 && target.last().history.len()==2
        &&& target.last().history[0]==source.first().history[0]
        &&& g::step(ex::library(),programs(),target[target.len() as int-2],target.last(),2,r::Rule::Unload)
    },
{
    deletion_history();source_indices();
    let source=trace();let steps=labels();let lib=ex::library();
    reveal_with_fuel(sh::labels_without,11);
    let target=deletion::delete(lib,programs(),source,steps,1);
    let kept=sh::labels_without(steps,1);
    assert(kept.len()==6);assert(kept[5]==(2usize,r::Rule::Unload));
    assert(target.len()==7);
    assert(g::step(lib,programs(),target[5],target[6],2,r::Rule::Unload));
    assert(history::histories(ex::equality(),source.last().history,target.last().history,1,1));
    assert(history::index(source.last().history,1,1,source.last().history.len())==2);
    assert(target.last().history[0]==source.last().history[0]);
    source_history_head();
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
proof fn compressed_pre_unload()
    ensures {
        let target=deletion::delete(ex::library(),programs(),trace(),labels(),1);
        &&& target.len()>=2
        &&& target[target.len() as int-2].state.accumulators[2usize]==seq![1nat]
    },
{
    actual_source();source_indices();sh::example_interface();
    let source=trace();let steps=labels();let lib=ex::library();
    let prefix=source.drop_last();let earlier=steps.drop_last();
    assert(prefix.len()==10);assert(earlier.len()==9);
    assert(g::execution(lib,programs(),prefix,earlier));
    assert(source_proof::fragment(programs(),prefix,earlier,1,1));
    assert(prefix.first()==source.first());
    deletion::delete_execution(ex::equality(),lib,programs(),prefix,earlier,1);
    let previous=deletion::delete(lib,programs(),prefix,earlier,1);
    let a=prefix.last();let b=previous.last();
    assert(a==source[9]);
    assert(g::step(lib,programs(),a,source[10],2,r::Rule::Unload));
    assert(s::registered(a.state,2));
    assert(a.history==source.last().history);
    assert(a.state.accumulators[2usize]==seq![3nat]);
    assert(history::index(a.history,1,1,3)==1);
    assert(b.state.accumulators[2usize]==history::rename(a.history,1,1,a.state.accumulators[2usize]));
    history::rename_laws(a.history,1,1,Seq::empty(),3);
    assert(Seq::<nat>::empty().push(3) =~= seq![3nat]);
    assert(b.state.accumulators[2usize] =~= seq![1nat]);
    let target=deletion::delete(lib,programs(),source,steps,1);
    reveal(deletion::delete);
    assert(steps.last()==(2usize,r::Rule::Unload));
    assert(target==previous.push(g::unload(b,2)));
    assert(previous.len()>=1);
    assert(target[target.len() as int-2]==b);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn compressed_history()
    ensures {
        let source=trace();let target=deletion::delete(ex::library(),programs(),source,labels(),1);
        &&& target.len()==7 && source.first().history.len()==1 && source.last().history.len()==4 && target.last().history.len()==2
        &&& target.last().history[0]==source.first().history[0]
        &&& target[target.len() as int-2].state.accumulators[2usize]==seq![1nat]
        &&& g::step(ex::library(),programs(),target[target.len() as int-2],target.last(),2,r::Rule::Unload)
    },
{
    compressed_target();compressed_pre_unload();
}
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn closed_observation()
    ensures {
        let source=trace();let target=deletion::delete(ex::library(),programs(),source,labels(),1);let terminal=g::unload(source.last(),1);
        &&& g::execution(ex::library(),programs(),target,sh::labels_without(labels(),1))
        &&& g::step(ex::library(),programs(),source.last(),terminal,1,r::Rule::Unload)
        &&& obs::tables_related(ex::equality(),terminal.state,target.last().state)
        &&& terminal.state.tables[1usize].is_empty() && target.last().state.tables[1usize].is_empty()
        &&& terminal.state.tables[0usize][ex::key(0)]==10 && target.last().state.tables[0usize][ex::key(0)]==10
    },
{
    actual_source();source_shape();sh::example_interface();let lib=ex::library();let source=trace();let steps=labels();
    deletion::terminal_deletion(ex::equality(),lib,programs(),source,steps,1);deletion::delete_execution(ex::equality(),lib,programs(),source,steps,1);
    let target=deletion::delete(lib,programs(),source,steps,1);let terminal=g::unload(source.last(),1);
    assert(s::registered(source.last().state,1));assert(s::registered(target.last().state,1));assert(s::registered(terminal.state,1));
    assert(target.last().state.tables[1usize].is_empty());assert(terminal.state.tables[1usize].dom()==target.last().state.tables[1usize].dom());
    assert(terminal.state.tables[0usize].dom().contains(ex::key(0)));assert(target.last().state.tables[0usize].dom().contains(ex::key(0)));
    assert(ex::equality()(ex::key(0),terminal.state.tables[0usize][ex::key(0)],target.last().state.tables[0usize][ex::key(0)]));
}
pub proof fn actual_providing_deletion()
    ensures {
        let source=trace();let target=deletion::delete(ex::library(),programs(),source,labels(),1);let terminal=g::unload(source.last(),1);
        &&& g::execution(ex::library(),programs(),target,sh::labels_without(labels(),1))
        &&& g::step(ex::library(),programs(),source.last(),terminal,1,r::Rule::Unload)
        &&& source.first().state.control.fibers[1usize].provisions==ex::provided(1)
        &&& target.len()==7 && source.first().history.len()==1 && source.last().history.len()==4 && target.last().history.len()==2
        &&& target.last().history[0]==source.first().history[0]
        &&& target[target.len() as int-2].state.accumulators[2usize]==seq![1nat]
        &&& g::step(ex::library(),programs(),target[target.len() as int-2],target.last(),2,r::Rule::Unload)
        &&& obs::tables_related(ex::equality(),terminal.state,target.last().state)
        &&& terminal.state.tables[1usize].is_empty() && target.last().state.tables[1usize].is_empty()
        &&& terminal.state.tables[0usize][ex::key(0)]==10 && target.last().state.tables[0usize][ex::key(0)]==10
    },
{
    actual_source();compressed_history();closed_observation();
}

} // verus!
