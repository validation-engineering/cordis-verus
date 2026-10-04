//! Nonvacuous operations for the actual mixed recovery theorem.
//!
//! Every key admits integer translations. Both forward and returned inverse
//! generators are translations, so the exact scalar interface is proved for
//! arbitrary arguments. The final trace contains real own and foreign calls.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, dependent_grammar as d, entangled as e, global, grammar_recovery as gr,
    mediated as m, mixed_grammar as g, mixed_recovery as recovery, mixed_syntax as syntax,
    projection as p, refinement as r, semantics as s, Phase, Port,
};
use vstd::prelude::*;

verus! {

#[derive(PartialEq,Eq,Structural)]
pub enum Stage {Spawn,Provide,Shift}
pub open spec fn key(owner:usize)->Port {Port {key:owner as u64,realm:0}}
pub open spec fn provided(owner:usize)->ISet<Port> {ISet::empty().insert(key(owner))}
pub open spec fn translation(amount:int)->m::Operation<int,()> {
    |value:int|Some(m::ValueYield {value:value+amount,undo:|after:int|Some(after-amount),outcome:()})
}
pub open spec fn library()->g::Library<Port,int,int,()> {
    d::Library {values:|_key:Port,_value:int|true,arguments:|_op:Port,_arg:int|true,
        outcomes:|_op:Port,_outcome:()|true,key:|op:Port|op,allowed:ISet::full(),
        apply:|_op:Port,amount:int|translation(amount)}
}
pub open spec fn equality()->spec_fn(Port,int,int)->bool {|_key:Port,a:int,b:int|a==b}
/// No assumptions and no empty allowed-operation set: every integer argument
/// names a real addition and an exact subtraction inverse at every input.
pub proof fn primitive_theory()
    ensures d::primitive_theory(equality(),library()),library().allowed.contains(key(0)),
        forall|op:Port,amount:int,value:int| #[trigger] (library().apply)(op,amount)(value).is_some(),
{
    assert forall|op:Port,amount:int| library().allowed.contains(op) && (library().arguments)(op,amount)
        implies #[trigger] d::operation_typed(library(),op,amount)
            && m::operation_admissible(|a:int,b:int|equality()(op,a,b),(library().apply)(op,amount)) by {}
}
pub open spec fn value_shift(amount:int)->spec_fn(int)->int {|v:int|v+amount}
pub proof fn generator_is_translation(k:Port,f:spec_fn(int)->int)
    requires gr::generator(library(),k,f),
    ensures exists|amount:int| f==#[trigger] value_shift(amount),
{
    let lib=library();
    let (op,amount)=choose|op:Port,amount:int| lib.allowed.contains(op) && #[trigger] (lib.arguments)(op,amount)
        && (lib.key)(op)==k && {
            let call=(lib.apply)(op,amount);
            f==gr::forward(call) || exists|v:int| #[trigger] call(v).is_some() && f==gr::total(call(v).unwrap().undo)
        };
    let call=translation(amount);
    if f==gr::forward(call) {
        assert(f =~= value_shift(amount));
    } else {
        let before=choose|v:int| #[trigger] call(v).is_some() && f==gr::total(call(v).unwrap().undo);
        assert(f =~= value_shift(-amount));
    }
}
pub proof fn scalar_interface()
    ensures gr::independent_keys(library()),
{
    assert forall|k:Port,f:spec_fn(int)->int,h:spec_fn(int)->int| gr::generator(library(),k,f) && gr::generator(library(),k,h)
        implies forall|v:int| #[trigger] f(h(v))==h(f(v)) by {
        generator_is_translation(k,f);generator_is_translation(k,h);
        let a=choose|a:int| f==#[trigger] value_shift(a);
        let b=choose|b:int| h==#[trigger] value_shift(b);
        assert forall|v:int| #[trigger] f(h(v))==h(f(v)) by {}
    }
}
/// The actual finite-context stage has a nontrivial value change and captures
/// its real inverse. Missing key remains a strict failed call.
pub proof fn actual_operation(amount:int,before:int)
    ensures {
        let node=d::Node::Operation {operation:key(0),argument:amount,select:|_:()|None::<Stage>};
        let input=Map::empty().insert(key(0),before);let out=d::run(library(),node,input).unwrap();
        &&& d::run(library(),node,input).is_some()
        &&& out.state[key(0)]==before+amount && out.next.is_none()
        &&& (out.undo)(out.state)==Some(input)
        &&& d::run(library(),node,Map::empty()).is_none()
    },
{
    let input=Map::empty().insert(key(0),before);
    assert(input.insert(key(0),before+amount).insert(key(0),before) =~= input);
}

pub open spec fn programs()->g::Programs<Port,int,int,(),Stage> {
    |actor:usize| |stage:Stage|match stage {
        Stage::Spawn=>if actor==0 {
            g::Node::Child {child:1,dependencies:ISet::empty(),provisions:provided(1),root:Stage::Provide,next:Some(Stage::Provide)}
        } else {g::Node::Dependent {node:d::Node::Unit}},
        Stage::Provide=>g::Node::Dependent {node:d::Node::Provision {key:key(actor),value:if actor==0 {7}else{42},next:Some(Stage::Shift)}},
        Stage::Shift=>g::Node::Dependent {node:d::Node::Operation {operation:key(actor),argument:if actor==0 {5}else{-3},select:|_:()|None}},
    }
}
pub proof fn root_members()
    ensures syntax::member(library(),programs(),0,provided(0),provided(0),Stage::Spawn),
        syntax::member(library(),programs(),1,provided(1),provided(1),Stage::Provide),
{
    syntax::constructor_member(library(),programs(),0,provided(0),provided(0),Stage::Shift);
    syntax::constructor_member(library(),programs(),0,provided(0),provided(0),Stage::Provide);
    syntax::constructor_member(library(),programs(),1,provided(1),provided(1),Stage::Shift);
    syntax::constructor_member(library(),programs(),1,provided(1),provided(1),Stage::Provide);
    assert(ISet::<Port>::empty().union(provided(1)) =~= provided(1));
    syntax::constructor_member(library(),programs(),0,provided(0),provided(0),Stage::Spawn);
}
pub open spec fn insert_parent(a:g::Configuration<int,Stage>)->g::Configuration<int,Stage> {
    g::Configuration {
        state:s::extend_child(a.state,global::insert_fiber(a.state.control,0,None,ISet::empty(),provided(0)),0,0),
        roots:a.roots.insert(0,Stage::Spawn),current:a.current.insert(0,None),history:a.history,
    }
}
pub open spec fn retire_parent(a:g::Configuration<int,Stage>)->g::Configuration<int,Stage> {
    g::Configuration {state:s::with_control(a.state,global::retire_fiber(a.state.control,0)),
        roots:a.roots,current:a.current,history:a.history}
}
#[verifier::opaque]
pub open spec fn trace()->Seq<g::Configuration<int,Stage>> {
    let a0=g::empty::<int,Stage>();let a1=insert_parent(a0);
    let a2=g::edit(a1,0,Phase::Loading,ISet::empty(),Some(Stage::Spawn),Seq::empty());
    let a3=g::land(library(),programs(),a2,0,Phase::Loading);
    let a4=g::edit(a3,1,Phase::Loading,ISet::empty(),Some(Stage::Provide),Seq::empty());
    let a5=g::land(library(),programs(),a4,1,Phase::Loading);
    let a6=g::land(library(),programs(),a5,1,Phase::Active);
    let a7=g::land(library(),programs(),a6,0,Phase::Loading);
    let a8=g::land(library(),programs(),a7,0,Phase::Active);
    let a9=retire_parent(a8);
    let a10=g::edit(a9,0,Phase::Unloading,ISet::empty(),None,a9.state.accumulators[0usize]);
    let a11=g::unload(a10,0);
    seq![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11]
}
pub open spec fn labels()->Seq<(usize,r::Rule)> {
    seq![(0usize,r::Rule::Insert),(0usize,r::Rule::Begin),(0usize,r::Rule::Iter),
        (1usize,r::Rule::Begin),(1usize,r::Rule::Iter),(1usize,r::Rule::Finish),
        (0usize,r::Rule::Iter),(0usize,r::Rule::Finish),(0usize,r::Rule::Retire),
        (0usize,r::Rule::Leave),(0usize,r::Rule::Unload)]
}
/// This complete execution contains both own (+5) and foreign (-3) Operations.
/// All source guards and all actual inverse domains are proved, not assumed.
pub proof fn actual_execution()
    ensures g::execution(library(),programs(),trace(),labels()),trace().first()==g::empty::<int,Stage>(),
        trace().len()==12,trace()[8].state.tables[0usize][key(0)]==12,
        trace()[8].state.tables[1usize][key(1)]==39,
{
    reveal(trace);root_members();let states=trace();
    assert(ISet::<Port>::empty().union(provided(0)) =~= provided(0));
    assert(g::step(library(),programs(),states[0],states[1],0,r::Rule::Insert));
    assert(g::step(library(),programs(),states[1],states[2],0,r::Rule::Begin));
    assert(g::step(library(),programs(),states[2],states[3],0,r::Rule::Iter));
    assert(g::step(library(),programs(),states[3],states[4],1,r::Rule::Begin));
    assert(g::step(library(),programs(),states[4],states[5],1,r::Rule::Iter));
    assert(g::step(library(),programs(),states[5],states[6],1,r::Rule::Finish));
    assert(g::step(library(),programs(),states[6],states[7],0,r::Rule::Iter));
    assert(g::step(library(),programs(),states[7],states[8],0,r::Rule::Finish));
    ch::concrete_child_retirement(states[8].state,0);
    assert(g::step(library(),programs(),states[8],states[9],0,r::Rule::Retire));
    assert(g::step(library(),programs(),states[9],states[10],0,r::Rule::Leave));
    assert(states[10].state.accumulators[0usize] =~= seq![0nat,3nat,4nat]);
    reveal_with_fuel(g::restore,4);
    assert(g::restore(states[10].history,states[10].state.accumulators[0usize],states[10].state,0).is_some());
    assert(g::step(library(),programs(),states[10],states[11],0,r::Rule::Unload));
    assert forall|i:int| 0<=i<labels().len() implies g::step(library(),programs(),states[i],states[i+1],labels()[i].0,labels()[i].1) by {
        if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else if i==5 {} else if i==6 {} else if i==7 {} else if i==8 {} else if i==9 {} else {assert(i==10);}
    }
}
/// Instantiate the generic terminal theorem with the nonempty translation
/// library and real own/foreign operations. The child is retired, still Active,
/// and retains the value 39 computed by its own actual operation.
pub proof fn terminal_operation_recovery()
    ensures {
        let states=trace();let after=states[11];
        &&& g::execution(library(),programs(),states,labels())
        &&& d::primitive_theory(equality(),library()) && gr::independent_keys(library())
        &&& after.state.tables[0usize].is_empty()
        &&& p::project(after.state,ISet::full())==e::foreign_state(
            recovery::events(library(),programs(),states.subrange(2,11),labels().subrange(2,10),0),p::project(states[2].state,ISet::full()))
        &&& after.state.control.fibers[1usize].retired && after.state.control.fibers[1usize].phase==Phase::Active
        &&& after.state.tables[1usize].dom().contains(key(1)) && after.state.tables[1usize][key(1)]==39
    },
{
    actual_execution();primitive_theory();scalar_interface();
    reveal(trace);let states=trace();
    assert forall|i:int| 2<=i<=10 implies gr::installed(states[i].state,0) by {
        if i==2 {} else if i==3 {} else if i==4 {} else if i==5 {} else if i==6 {} else if i==7 {} else if i==8 {} else if i==9 {} else {assert(i==10);}
    }
    recovery::actual_terminal_recovery(equality(),library(),programs(),states,labels(),0,2,10);
    reveal_with_fuel(g::restore,4);
}

}
