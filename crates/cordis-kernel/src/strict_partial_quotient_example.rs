//! Nonempty real traces with unequal roots, current IDs and journal lengths.
//!
//! A worker branches on a real coeffect value. The right run reads while a
//! mutator contributes +1, takes one extra read, then observes the mutator's
//! actual inverse restore zero. Both cuts agree on control/tables; their stored
//! functions agree even though the worker journal has one versus two entries.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, dependent_grammar as d, grammar_lift as lift, mediated as m,
    mixed_grammar as g, mixed_observational_runs as rows, mixed_syntax as syntax,
    mixed_transposition as insert, observational_grammar as og, observational_lift as ol,
    preservation as inv, recovery_examples as ex, refinement as r, semantics as s,
    shared_execution as sh, strict_partial_quotient as q,
    strict_partial_quotient_reflexive as reflexive, Binding, Phase, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn identity()->m::PartialMap<int> {|v:int|Some(v)}
pub open spec fn operation(increment:bool)->m::Operation<int,int> {
    |v:int|if increment {Some(m::ValueYield {value:v+1,undo:|w:int|Some(w-1),outcome:v})}
        else {Some(m::ValueYield {value:v,undo:identity(),outcome:v})}
}
pub open spec fn library()->g::Library<bool,(),int,int> {
    d::Library {values:|_:Port,_:int|true,arguments:|_:bool,_:()|true,outcomes:|_:bool,_:int|true,
        key:|_:bool|ex::key(0),allowed:ISet::full(),apply:|inc:bool,_:()|operation(inc)}
}
pub open spec fn programs()->g::Programs<bool,(),int,int,nat> {
    |actor:usize| |id:nat|g::Node::Dependent {node:if actor==0 {
        d::Node::Provision {key:ex::key(0),value:0,next:None}
    } else if actor==2 {d::Node::Operation {operation:true,argument:(),select:|_:int|None}}
    else if actor==1 && (id==0 || id==1) {
        d::Node::Operation {operation:false,argument:(),select:|v:int|Some(if v==0 {2nat}else{3nat})}
    } else if actor==1 && id==3 {
        d::Node::Operation {operation:false,argument:(),select:|_:int|Some(4nat)}
    } else {d::Node::Unit}}
}
pub open spec fn dependencies(actor:usize)->ISet<Port> {if actor==0 {ISet::empty()}else{ex::provided(0)}}
pub open spec fn provisions(actor:usize)->ISet<Port> {if actor==0 {ex::provided(0)}else{ISet::empty()}}

pub proof fn theory()
    ensures og::primitive_theory(ex::equality(),library()),
{
    assert(d::primitive_theory(ex::equality(),library())) by {
        assert forall|op:bool,arg:()| library().allowed.contains(op) && (library().arguments)(op,arg)
            implies #[trigger] d::operation_typed(library(),op,arg)
                && m::operation_admissible(|u:int,v:int|ex::equality()(ex::key(0),u,v),(library().apply)(op,arg)) by {}
    }
    og::exact_theory(ex::equality(),library());
}
pub proof fn members(actor:usize,id:nat)
    ensures syntax::member(library(),programs(),actor,dependencies(actor).union(provisions(actor)),provisions(actor),id),
{
    let keys=dependencies(actor).union(provisions(actor));let ps=provisions(actor);
    if actor==1 {
        syntax::constructor_member(library(),programs(),actor,keys,ps,2nat);
        syntax::constructor_member(library(),programs(),actor,keys,ps,4nat);
        syntax::constructor_member(library(),programs(),actor,keys,ps,3nat);
    }
    syntax::constructor_member(library(),programs(),actor,keys,ps,id);
}

#[verifier::opaque]
pub open spec fn setup(right:bool)->Seq<g::Configuration<int,nat>> {
    let a0=g::empty::<int,nat>();let a1=insert::insert(a0,0,None,dependencies(0),provisions(0),0nat);
    let a2=insert::insert(a1,1,None,dependencies(1),provisions(1),if right {1nat}else{0nat});
    let a3=insert::insert(a2,2,None,dependencies(2),provisions(2),0nat);
    let a4=g::edit(a3,0,Phase::Loading,ISet::empty(),Some(0nat),Seq::empty());
    let a5=g::land(library(),programs(),a4,0,Phase::Active);seq![a0,a1,a2,a3,a4,a5]
}
pub open spec fn setup_labels()->Seq<(usize,r::Rule)> {seq![(0usize,r::Rule::Insert),(1usize,r::Rule::Insert),(2usize,r::Rule::Insert),(0usize,r::Rule::Begin),(0usize,r::Rule::Finish)]}
#[verifier::opaque]
pub open spec fn left()->Seq<g::Configuration<int,nat>> {
    let states=setup(false);let a6=g::edit(states.last(),1,Phase::Loading,sh::example_view(),Some(0nat),Seq::empty());
    let a7=g::land(library(),programs(),a6,1,Phase::Loading);let a8=sh::retire(a7,2);
    states.push(a6).push(a7).push(a8)
}
pub open spec fn left_labels()->Seq<(usize,r::Rule)> {setup_labels()+seq![(1usize,r::Rule::Begin),(1usize,r::Rule::Iter),(2usize,r::Rule::Retire)]}
#[verifier::opaque]
pub open spec fn right()->Seq<g::Configuration<int,nat>> {
    let states=setup(true);let a6=g::edit(states.last(),2,Phase::Loading,sh::example_view(),Some(0nat),Seq::empty());
    let a7=g::land(library(),programs(),a6,2,Phase::Active);
    let a8=g::edit(a7,1,Phase::Loading,sh::example_view(),Some(1nat),Seq::empty());
    let a9=g::land(library(),programs(),a8,1,Phase::Loading);let a10=g::land(library(),programs(),a9,1,Phase::Loading);
    let a11=sh::retire(a10,2);let a12=g::edit(a11,2,Phase::Unloading,sh::example_view(),None,a11.state.accumulators[2usize]);
    let a13=g::unload(a12,2);states.push(a6).push(a7).push(a8).push(a9).push(a10).push(a11).push(a12).push(a13)
}
pub open spec fn right_labels()->Seq<(usize,r::Rule)> {
    setup_labels()+seq![(2usize,r::Rule::Begin),(2usize,r::Rule::Finish),(1usize,r::Rule::Begin),(1usize,r::Rule::Iter),(1usize,r::Rule::Iter),
        (2usize,r::Rule::Retire),(2usize,r::Rule::Leave),(2usize,r::Rule::Unload)]
}

#[verifier::spinoff_prover]
pub proof fn actual_setup(branch:bool)
    ensures g::execution(library(),programs(),setup(branch),setup_labels()),setup(branch).first()==g::empty::<int,nat>(),
        g::well_formed(library(),programs(),setup(branch).last()),
{
    theory();members(0,0nat);members(1,if branch {1nat}else{0nat});members(2,0nat);reveal(setup);
    let states=setup(branch);let steps=setup_labels();let lib=library();let ps=programs();
    g::empty_well_formed(lib,ps);
    insert::insertion_step(lib,ps,states[0],0,None,dependencies(0),provisions(0),0nat);
    ol::configuration_preservation(ex::equality(),lib,ps,states[0],states[1],0,r::Rule::Insert);
    insert::insertion_step(lib,ps,states[1],1,None,dependencies(1),provisions(1),if branch {1nat}else{0nat});
    ol::configuration_preservation(ex::equality(),lib,ps,states[1],states[2],1,r::Rule::Insert);
    insert::insertion_step(lib,ps,states[2],2,None,dependencies(2),provisions(2),0nat);
    ol::configuration_preservation(ex::equality(),lib,ps,states[2],states[3],2,r::Rule::Insert);
    assert(g::step(lib,ps,states[3],states[4],0,r::Rule::Begin));
    ol::configuration_preservation(ex::equality(),lib,ps,states[3],states[4],0,r::Rule::Begin);
    assert(g::step(lib,ps,states[4],states[5],0,r::Rule::Finish));
    ol::configuration_preservation(ex::equality(),lib,ps,states[4],states[5],0,r::Rule::Finish);
    assert forall|i:int|0<=i<steps.len() implies g::step(lib,ps,states[i],states[i+1],steps[i].0,steps[i].1) by {
        if i==0{}else if i==1{}else if i==2{}else if i==3{}else{assert(i==4);}
    }
}

/// The real installed view resolves K to provider0, including before publication
/// of the consumer. This lemma records the concrete binding existential.
pub proof fn resolution(a:s::State<int>,actor:usize)
    requires s::registered(a,actor),a.control.fibers[actor].dependencies==ex::provided(0),a.control.fibers[actor].provisions.is_empty(),
        a.control.fibers[actor].committed==sh::example_view(),
    ensures lift::resolve(a,actor,ex::key(0))==Some(0usize),
{
    let b=Binding {key:0,realm:0,provider:0};assert(lift::names_key(b,ex::key(0)));assert(sh::example_view().contains(b));
    assert(exists|b:Binding| a.control.fibers[actor].committed.contains(b) && lift::names_key(b,ex::key(0)));
}

#[verifier::spinoff_prover]
#[verifier::rlimit(35)]
pub proof fn actual_left()
    ensures g::execution(library(),programs(),left(),left_labels()),left().first()==g::empty::<int,nat>(),
        g::well_formed(library(),programs(),left().last()),left().last().current[1usize]==Some(2nat),
        left().last().state.accumulators[1usize]==seq![1nat],left().last().history.len()==2,
{
    actual_setup(false);theory();reveal(left);reveal(setup);let states=left();let steps=left_labels();
    sh::example_target(states[5].state,1);assert(g::step(library(),programs(),states[5],states[6],1,r::Rule::Begin));
    resolution(states[6].state,1);assert(g::step(library(),programs(),states[6],states[7],1,r::Rule::Iter));
    ch::concrete_child_retirement(states[7].state,2);assert(g::step(library(),programs(),states[7],states[8],2,r::Rule::Retire));
    assert forall|i:int|0<=i<steps.len() implies g::step(library(),programs(),states[i],states[i+1],steps[i].0,steps[i].1) by {
        if i<5 {assert(states[i]==setup(false)[i]);assert(states[i+1]==setup(false)[i+1]);assert(steps[i]==setup_labels()[i]);}
        else if i==5{}else if i==6{}else{assert(i==7);}
    }
    assert(states.last().state.accumulators[1usize] =~= seq![1nat]);
    ol::from_empty_safe(ex::equality(),library(),programs(),states,steps);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn actual_right()
    ensures g::execution(library(),programs(),right(),right_labels()),right().first()==g::empty::<int,nat>(),
        g::well_formed(library(),programs(),right().last()),right().last().current[1usize]==Some(4nat),
        right().last().state.accumulators[1usize]==seq![2nat,3nat],right().last().history.len()==4,
        right()[7].state.tables[0usize][ex::key(0)]==1,right().last().state.tables[0usize][ex::key(0)]==0,
{
    actual_setup(true);theory();reveal(right);reveal(setup);let states=right();let steps=right_labels();
    sh::example_target(states[5].state,2);assert(g::step(library(),programs(),states[5],states[6],2,r::Rule::Begin));
    resolution(states[6].state,2);assert(g::step(library(),programs(),states[6],states[7],2,r::Rule::Finish));
    sh::example_target(states[7].state,1);assert(g::step(library(),programs(),states[7],states[8],1,r::Rule::Begin));
    resolution(states[8].state,1);assert(g::step(library(),programs(),states[8],states[9],1,r::Rule::Iter));
    resolution(states[9].state,1);assert(g::step(library(),programs(),states[9],states[10],1,r::Rule::Iter));
    ch::concrete_child_retirement(states[10].state,2);assert(g::step(library(),programs(),states[10],states[11],2,r::Rule::Retire));
    assert(g::step(library(),programs(),states[11],states[12],2,r::Rule::Leave));
    resolution(states[12].state,2);reveal_with_fuel(g::restore,2);
    assert(g::step(library(),programs(),states[12],states[13],2,r::Rule::Unload));
    assert forall|i:int|0<=i<steps.len() implies g::step(library(),programs(),states[i],states[i+1],steps[i].0,steps[i].1) by {
        if i<5 {assert(states[i]==setup(true)[i]);assert(states[i+1]==setup(true)[i+1]);assert(steps[i]==setup_labels()[i]);}
        else if i==5{}else if i==6{}else if i==7{}else if i==8{}else if i==9{}else if i==10{}else if i==11{}else{assert(i==12);}
    }
    assert(states.last().state.accumulators[1usize] =~= seq![2nat,3nat]);
    ol::from_empty_safe(ex::equality(),library(),programs(),states,steps);
}

pub open spec fn read_receipt()->lift::Receipt<int> {
    lift::Receipt {actor:1,inverse:lift::Inverse::Operation {provider:0,key:ex::key(0),undo:identity()}}
}
pub open spec fn provider_receipt()->lift::Receipt<int> {
    lift::Receipt {actor:0,inverse:lift::Inverse::Provision {key:ex::key(0)}}
}

#[verifier::spinoff_prover]
#[verifier::rlimit(35)]
pub proof fn cut_shapes()
    ensures {
        let a=left().last();let b=right().last();
        &&& rows::tables_related(ex::equality(),a.state,b.state)
        &&& a.state.control.fibers.dom()==ISet::empty().insert(0usize).insert(1usize).insert(2usize)
        &&& a.roots[0usize]==b.roots[0usize] && a.roots[2usize]==b.roots[2usize]
        &&& a.roots[1usize]==0 && b.roots[1usize]==1
        &&& a.current[0usize].is_none() && b.current[0usize].is_none() && a.current[2usize].is_none() && b.current[2usize].is_none()
        &&& a.current[1usize]==Some(2nat) && b.current[1usize]==Some(4nat)
        &&& a.state.accumulators[0usize]==seq![0nat] && b.state.accumulators[0usize]==seq![0nat]
        &&& a.state.accumulators[1usize]==seq![1nat] && b.state.accumulators[1usize]==seq![2nat,3nat]
        &&& a.state.accumulators[2usize].len()==0 && b.state.accumulators[2usize].len()==0
        &&& a.history.len()==2 && b.history.len()==4
        &&& a.history[0].landed.receipt==(g::Receipt::Table {receipt:provider_receipt()})
        &&& b.history[0].landed.receipt==(g::Receipt::Table {receipt:provider_receipt()})
        &&& a.history[1].landed.receipt==(g::Receipt::Table {receipt:read_receipt()})
        &&& b.history[2].landed.receipt==(g::Receipt::Table {receipt:read_receipt()})
        &&& b.history[3].landed.receipt==(g::Receipt::Table {receipt:read_receipt()})
        &&& a.state.tables[0usize][ex::key(0)]==0 && b.state.tables[0usize][ex::key(0)]==0
    },
{
    actual_left();actual_right();reveal(left);reveal(right);reveal(setup);reveal_with_fuel(g::restore,2);
    let a=left().last();let b=right().last();
    assert(a.state.control.fibers.dom() =~= ISet::empty().insert(0usize).insert(1usize).insert(2usize));
    assert(a.state.control.fibers =~= b.state.control.fibers);
    assert forall|actor:usize|s::registered(a.state,actor) implies {
        &&& a.state.tables[actor].dom()==b.state.tables[actor].dom()
        &&& forall|key:Port|a.state.tables[actor].dom().contains(key) ==> ex::equality()(key,a.state.tables[actor][key],b.state.tables[actor][key])
    } by {if actor==0{}else if actor==1{}else{assert(actor==2);}}
    assert(a.state.accumulators[0usize] =~= seq![0nat]);assert(b.state.accumulators[0usize] =~= seq![0nat]);
}

pub proof fn aliases(actor:usize,i:nat,j:nat)
    requires programs()(actor)(i)==programs()(actor)(j),
    ensures q::iterator_related(ex::equality(),library(),programs(),actor,i,j),
{
    theory();let names=ISet::<nat>::full();
    assert(reflexive::closed_tables(library(),programs(),actor,names));
    reflexive::table_aliases(ex::equality(),library(),programs(),actor,names,i,j);
}

/// The actual read inverse is a partial identity, not an unconditional identity:
/// its captured provider/binding must still be present on the test input.
pub proof fn read_identity(a:s::State<int>)
    requires inv::well_formed(a),lift::undo(read_receipt(),a).is_some(),
    ensures lift::undo(read_receipt(),a)==Some(a),
{
    let table=a.tables[0usize];assert(table.insert(ex::key(0),table[ex::key(0)]) =~= table);
    assert(a.tables.insert(0usize,table) =~= a.tables);
}
pub proof fn worker_function(a:s::State<int>)
    requires inv::well_formed(a),
    ensures q::accumulator(left().last(),1)(a)==lift::undo(read_receipt(),a),
        q::accumulator(right().last(),1)(a)==lift::undo(read_receipt(),a),
{
    cut_shapes();reveal_with_fuel(g::restore,3);
    if lift::undo(read_receipt(),a).is_some() {read_identity(a);}
}

pub proof fn field_accumulators(actor:usize)
    requires actor==0 || actor==1 || actor==2,
    ensures m::partial_related(q::input_relation(ex::equality(),actor),q::accumulator(left().last(),actor),q::accumulator(right().last(),actor)),
{
    cut_shapes();theory();let a=left().last();let b=right().last();let eq=ex::equality();
    let receipt=if actor==0 {provider_receipt()}else{read_receipt()};
    assert(rows::receipt_related(eq,g::Receipt::Table {receipt},g::Receipt::Table {receipt}));
    reflexive::inverse_pair(eq,actor,receipt,receipt);
    assert forall|u:s::State<int>,v:s::State<int>| #![trigger q::accumulator(a,actor)(u),q::accumulator(b,actor)(v)] q::legal_input(eq,actor,u,v) implies {
        &&& q::accumulator(a,actor)(u).is_some()==q::accumulator(b,actor)(v).is_some()
        &&& (q::accumulator(a,actor)(u).is_some() ==> q::legal_input(eq,actor,q::accumulator(a,actor)(u).unwrap(),q::accumulator(b,actor)(v).unwrap()))
    } by {
        if actor==1 {worker_function(u);worker_function(v);}
        else {reveal_with_fuel(g::restore,2);}
        if actor!=2 {
            assert(q::accumulator(a,actor)(u)==lift::undo(receipt,u));
            assert(q::accumulator(b,actor)(v)==lift::undo(receipt,v));
            assert(m::partial_related(q::input_relation(eq,actor),|t:s::State<int>|lift::undo(receipt,t),|t:s::State<int>|lift::undo(receipt,t)));
            assert(lift::undo(receipt,u).is_some()==lift::undo(receipt,v).is_some());
            if lift::undo(receipt,u).is_some() {
                crate::mixed_observational_transport::undo_observations(eq,g::Receipt::Table {receipt},g::Receipt::Table {receipt},u,v);
                lift::undo_preservation(receipt,u);lift::undo_preservation(receipt,v);
                assert(q::legal_input(eq,actor,lift::undo(receipt,u).unwrap(),lift::undo(receipt,v).unwrap()));
            }
        } else {assert(q::accumulator(a,actor)(u)==Some(u));assert(q::accumulator(b,actor)(v)==Some(v));}
    }
}

/// Both configurations are reached from empty by genuine steps. Equal raw
/// roots, current IDs, tokens or accumulator lengths are all false for worker1.
pub proof fn actual_unequal_fields()
    ensures {
        let a=left().last();let b=right().last();
        &&& g::execution(library(),programs(),left(),left_labels()) && left().first()==g::empty::<int,nat>()
        &&& g::execution(library(),programs(),right(),right_labels()) && right().first()==g::empty::<int,nat>()
        &&& g::well_formed(library(),programs(),a) && g::well_formed(library(),programs(),b)
        &&& q::related(ex::equality(),library(),programs(),a,b)
        &&& a.roots[1usize]!=b.roots[1usize] && a.current[1usize]!=b.current[1usize]
        &&& a.state.accumulators[1usize].len()==1 && b.state.accumulators[1usize].len()==2 && a.history.len()!=b.history.len()
    },
{
    actual_left();actual_right();cut_shapes();let a=left().last();let b=right().last();
    assert forall|actor:usize|s::registered(a.state,actor) implies {
        &&& q::iterator_related(ex::equality(),library(),programs(),actor,a.roots[actor],b.roots[actor])
        &&& q::continuations(ex::equality(),library(),programs(),actor,a.current[actor],b.current[actor])
        &&& m::partial_related(q::input_relation(ex::equality(),actor),q::accumulator(a,actor),q::accumulator(b,actor))
    } by {
        if actor==0{}else if actor==1{}else{assert(actor==2);}
        aliases(actor,a.roots[actor],b.roots[actor]);field_accumulators(actor);
        if actor==1 {aliases(actor,2nat,4nat);}
    }
}

/// None remains distinct even on a legal, registered input: before worker
/// Begin it has no committed binding. After Begin the real inverse is defined.
pub proof fn actual_success_and_failure()
    ensures {
        let before=setup(false).last().state;let after=left().last().state;
        &&& q::legal_input(ex::equality(),1,before,before) && q::legal_input(ex::equality(),1,after,after)
        &&& q::accumulator(left().last(),1)(before).is_none() && q::accumulator(right().last(),1)(before).is_none()
        &&& q::accumulator(left().last(),1)(after)==Some(after) && q::accumulator(right().last(),1)(after)==Some(after)
        &&& g::run(library(),programs()(1)(0nat),before,1).is_none()
        &&& g::run(library(),programs()(1)(0nat),after,1).is_some()
    },
{
    actual_setup(false);actual_left();theory();reveal(setup);reveal(left);
    let before=setup(false).last().state;let after=left().last().state;
    rows::tables_reflexive(ex::equality(),before);rows::tables_reflexive(ex::equality(),after);
    resolution(after,1);worker_function(before);worker_function(after);read_identity(after);
}

#[verifier::opaque]
pub open spec fn suffix()->Seq<g::Configuration<int,nat>> {
    let a=left().last();let b=g::land(library(),programs(),a,1,Phase::Active);let c=sh::retire(b,1);
    let e=g::edit(c,1,Phase::Unloading,sh::example_view(),None,c.state.accumulators[1usize]);let f=g::unload(e,1);
    seq![a,b,c,e,f]
}
pub open spec fn suffix_labels()->Seq<(usize,r::Rule)> {seq![(1usize,r::Rule::Finish),(1usize,r::Rule::Retire),(1usize,r::Rule::Leave),(1usize,r::Rule::Unload)]}

/// Invoke the general proof on this unequal-field pair. The target suffix is
/// computed by its own real operations/restore, with no target-step premise.
#[verifier::spinoff_prover]
#[verifier::rlimit(35)]
pub proof fn actual_suffix_transport()
    ensures {
        let out=q::replay(library(),programs(),suffix(),suffix_labels(),seq![0nat,0nat,0nat,0nat],right().last());
        &&& g::execution(library(),programs(),suffix(),suffix_labels())
        &&& g::execution(library(),programs(),out,suffix_labels()) && out.first()==right().last()
        &&& q::related(ex::equality(),library(),programs(),suffix().last(),out.last())
        &&& forall|i:int|0<=i<out.len() ==> g::well_formed(library(),programs(),out[i])
        &&& out.last().state.control.fibers[1usize].phase==Phase::Inactive
        &&& out.last().state.accumulators[1usize].len()==0
    },
{
    actual_unequal_fields();theory();cut_shapes();reveal(left);reveal(right);reveal(setup);reveal(suffix);
    let a=left().last();let b=right().last();let states=suffix();let labels=suffix_labels();
    sh::example_target(a.state,1);assert(g::step(library(),programs(),states[0],states[1],1,r::Rule::Finish));
    ch::concrete_child_retirement(states[1].state,1);assert(g::step(library(),programs(),states[1],states[2],1,r::Rule::Retire));
    assert(g::step(library(),programs(),states[2],states[3],1,r::Rule::Leave));
    resolution(states[3].state,1);reveal_with_fuel(g::restore,3);
    assert(g::step(library(),programs(),states[3],states[4],1,r::Rule::Unload));
    assert forall|i:int|0<=i<labels.len() implies g::step(library(),programs(),states[i],states[i+1],labels[i].0,labels[i].1) by {if i==0{}else if i==1{}else if i==2{}else{assert(i==3);}}
    assert(q::table_programs(programs()));
    assert(q::live_tables(a)) by {
        assert forall|actor:usize|s::registered(a.state,actor) implies q::table_tokens(a.history,#[trigger] a.state.accumulators[actor]) by {
            if actor==0{}else if actor==1{}else{assert(actor==2);}
        }
    }
    assert(q::live_tables(b)) by {
        assert forall|actor:usize|s::registered(b.state,actor) implies q::table_tokens(b.history,#[trigger] b.state.accumulators[actor]) by {
            if actor==0{}else if actor==1{}else{assert(actor==2);}
        }
    }
    q::execution_simulates(ex::equality(),library(),programs(),states,labels,seq![0nat,0nat,0nat,0nat],b);
    let out=q::replay(library(),programs(),states,labels,seq![0nat,0nat,0nat,0nat],b);
    assert(q::related(ex::equality(),library(),programs(),states.last(),out.last()));
    assert(out.last().state.control==states.last().state.control);
}

}
