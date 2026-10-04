//! Actual same-provider operations with recovery only modulo observation.
//!
//! Two children modify their parent's one published value. Hidden state is
//! overwritten, so inverse recovery and generator commutation fail at raw
//! equality while the visible integer obeys the observational contracts.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, dependent_grammar as d, entangled as e, global, grammar_lift as gl,
    grammar_recovery as gr, mediated as m, mixed_grammar as g, mixed_recovery as mr,
    mixed_syntax as syntax, observational_execution as execution, observational_grammar as weak,
    observational_lift as ol, observational_recovery as obs, projection as p, refinement as r,
    semantics as s, Binding, Phase, Port,
};
use vstd::prelude::*;

verus! {

#[derive(PartialEq,Eq,Structural)]
pub enum Stage {SpawnFirst,SpawnSecond,Provide,Consume}
pub open spec fn key()->Port {Port {key:0,realm:0}}
pub open spec fn provided()->ISet<Port> {ISet::empty().insert(key())}
pub open spec fn binding()->Binding {Binding {key:0,realm:0,provider:0}}
pub open spec fn committed()->ISet<Binding> {ISet::empty().insert(binding())}
pub open spec fn operation(amount:int,hidden:int)->m::Operation<(int,int),()> {
    |before:(int,int)|Some(m::ValueYield {value:(before.0+amount,hidden),outcome:(),
        undo:|after:(int,int)|Some((after.0-amount,0))})
}
pub open spec fn library()->g::Library<Port,(int,int),(int,int),()> {
    d::Library {values:|_key:Port,_value:(int,int)|true,arguments:|_op:Port,_arg:(int,int)|true,
        outcomes:|_op:Port,_outcome:()|true,key:|op:Port|op,allowed:ISet::full(),
        apply:|_op:Port,arg:(int,int)|operation(arg.0,arg.1)}
}
pub open spec fn equality()->spec_fn(Port,(int,int),(int,int))->bool {|_key:Port,a:(int,int),b:(int,int)|a.0==b.0}
pub proof fn primitive_theory()
    ensures weak::primitive_theory(equality(),library()),!d::primitive_theory(equality(),library()),library().allowed.contains(key()),
{
    let lib=library();let eq=equality();
    assert forall|op:Port,arg:(int,int)|lib.allowed.contains(op)&&(lib.arguments)(op,arg) implies
        #[trigger] d::operation_typed(lib,op,arg)&&weak::operation_admissible(|a:(int,int),b:(int,int)|eq(op,a,b),(lib.apply)(op,arg)) by {}
    let call=operation(5,1);let original=(7int,10int);
    assert(call(original).is_some());assert((call(original).unwrap().undo)(call(original).unwrap().value)==Some((7int,0int)));
    assert(!m::operation_admissible(|a:(int,int),b:(int,int)|eq(key(),a,b),call));
    if d::primitive_theory(eq,lib) {assert(d::operation_typed(lib,key(),(5,1)));}
}
pub open spec fn visible_translation(f:spec_fn((int,int))->(int,int),amount:int)->bool {
    forall|v:(int,int)| #[trigger] f(v).0==v.0+amount
}
pub proof fn generator_visible_translation(k:Port,f:spec_fn((int,int))->(int,int))
    requires gr::generator(library(),k,f),
    ensures exists|amount:int| #[trigger] visible_translation(f,amount),
{
    let lib=library();
    let (op,arg)=choose|op:Port,arg:(int,int)|lib.allowed.contains(op)&& #[trigger] (lib.arguments)(op,arg)&&(lib.key)(op)==k && {
        let call=(lib.apply)(op,arg);f==gr::forward(call)||exists|v:(int,int)| #[trigger] call(v).is_some()&&f==gr::total(call(v).unwrap().undo)
    };
    let call=operation(arg.0,arg.1);
    if f==gr::forward(call) {assert forall|v:(int,int)| #[trigger] f(v).0==v.0+arg.0 by {} assert(visible_translation(f,arg.0));}
    else {
        let before=choose|v:(int,int)| #[trigger] call(v).is_some()&&f==gr::total(call(v).unwrap().undo);
        assert forall|v:(int,int)| #[trigger] f(v).0==v.0+(-arg.0) by {}
        assert(visible_translation(f,-arg.0));
    }
}
pub proof fn observational_interface()
    ensures obs::independent_keys(equality(),library()),!gr::independent_keys(library()),
{
    assert forall|k:Port,f:spec_fn((int,int))->(int,int),h:spec_fn((int,int))->(int,int)|gr::generator(library(),k,f)&&gr::generator(library(),k,h)
        implies forall|v:(int,int)| #[trigger] equality()(k,f(h(v)),h(f(v))) by {
        generator_visible_translation(k,f);generator_visible_translation(k,h);
        let a=choose|a:int| #[trigger] visible_translation(f,a);
        let b=choose|b:int| #[trigger] visible_translation(h,b);
        assert forall|v:(int,int)| #[trigger] equality()(k,f(h(v)),h(f(v))) by {}
    }
    let op=operation(5,1);let f=gr::forward(op);let h=gr::total(op((7,10)).unwrap().undo);
    assert((library().apply)(key(),(5,1))==op);
    assert((library().arguments)(key(),(5,1)));assert(library().allowed.contains(key()));
    assert(op((7,10)).is_some());
    assert(exists|v:(int,int)| #[trigger] op(v).is_some()&&h==gr::total(op(v).unwrap().undo));
    assert(gr::generator(library(),key(),f));assert(gr::generator(library(),key(),h));
    assert(f(h((7,10)))==(7int,1int));assert(h(f((7,10)))==(7int,0int));
    if gr::independent_keys(library()) {assert(f(h((7,10)))==h(f((7,10))));}
}
pub open spec fn programs()->g::Programs<Port,(int,int),(int,int),(),Stage> {
    |actor:usize| |stage:Stage|match stage {
        Stage::SpawnFirst=>g::Node::Child {child:1,dependencies:provided(),provisions:ISet::empty(),root:Stage::Consume,next:Some(Stage::SpawnSecond)},
        Stage::SpawnSecond=>g::Node::Child {child:2,dependencies:provided(),provisions:ISet::empty(),root:Stage::Consume,next:Some(Stage::Provide)},
        Stage::Provide=>g::Node::Dependent {node:d::Node::Provision {key:key(),value:(7,10),next:None}},
        Stage::Consume=>g::Node::Dependent {node:d::Node::Operation {operation:key(),argument:if actor==1 {(5,1)}else{(3,2)},select:|_:()|None}},
    }
}
pub proof fn root_members()
    ensures syntax::member(library(),programs(),0,provided(),provided(),Stage::SpawnFirst),
        syntax::member(library(),programs(),1,provided(),ISet::empty(),Stage::Consume),
        syntax::member(library(),programs(),2,provided(),ISet::empty(),Stage::Consume),
{
    syntax::constructor_member(library(),programs(),1,provided(),ISet::empty(),Stage::Consume);
    syntax::constructor_member(library(),programs(),2,provided(),ISet::empty(),Stage::Consume);
    syntax::constructor_member(library(),programs(),0,provided(),provided(),Stage::Provide);
    assert(provided().union(ISet::empty()) =~= provided());
    syntax::constructor_member(library(),programs(),0,provided(),provided(),Stage::SpawnSecond);
    syntax::constructor_member(library(),programs(),0,provided(),provided(),Stage::SpawnFirst);
}
pub open spec fn insert_parent(a:g::Configuration<(int,int),Stage>)->g::Configuration<(int,int),Stage> {
    g::Configuration {state:s::extend_child(a.state,global::insert_fiber(a.state.control,0,None,ISet::empty(),provided()),0,0),
        roots:a.roots.insert(0,Stage::SpawnFirst),current:a.current.insert(0,None),history:a.history}
}
pub open spec fn retire_consumer(a:g::Configuration<(int,int),Stage>)->g::Configuration<(int,int),Stage> {
    g::Configuration {state:s::with_control(a.state,global::retire_fiber(a.state.control,1)),roots:a.roots,current:a.current,history:a.history}
}
#[verifier::opaque]
pub open spec fn trace()->Seq<g::Configuration<(int,int),Stage>> {
    let a0=g::empty::<(int,int),Stage>();let a1=insert_parent(a0);
    let a2=g::edit(a1,0,Phase::Loading,ISet::empty(),Some(Stage::SpawnFirst),Seq::empty());
    let a3=g::land(library(),programs(),a2,0,Phase::Loading);
    let a4=g::land(library(),programs(),a3,0,Phase::Loading);
    let a5=g::land(library(),programs(),a4,0,Phase::Active);
    let a6=g::edit(a5,1,Phase::Loading,committed(),Some(Stage::Consume),Seq::empty());
    let a7=g::land(library(),programs(),a6,1,Phase::Active);
    let a8=g::edit(a7,2,Phase::Loading,committed(),Some(Stage::Consume),Seq::empty());
    let a9=g::land(library(),programs(),a8,2,Phase::Active);
    let a10=retire_consumer(a9);
    let a11=g::edit(a10,1,Phase::Unloading,committed(),None,a10.state.accumulators[1usize]);
    let a12=g::unload(a11,1);
    seq![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12]
}
pub open spec fn labels()->Seq<(usize,r::Rule)> {
    seq![(0usize,r::Rule::Insert),(0usize,r::Rule::Begin),(0usize,r::Rule::Iter),(0usize,r::Rule::Iter),
        (0usize,r::Rule::Finish),(1usize,r::Rule::Begin),(1usize,r::Rule::Finish),(2usize,r::Rule::Begin),
        (2usize,r::Rule::Finish),(1usize,r::Rule::Retire),(1usize,r::Rule::Leave),(1usize,r::Rule::Unload)]
}
pub proof fn consumer_target(state:s::State<(int,int)>,actor:usize)
    requires s::registered(state,actor),!state.control.fibers[actor].retired,
        state.control.fibers[actor].dependencies==provided(),s::publishes(state,key(),0),
    ensures s::target(state,actor,committed()),
{
    assert forall|b:Binding|committed().contains(b) implies state.control.fibers[actor].dependencies.contains(Port {key:b.key,realm:b.realm})
        &&s::publishes(state,Port {key:b.key,realm:b.realm},b.provider) by {assert(b==binding());}
    assert forall|p:Port|state.control.fibers[actor].dependencies.contains(p) implies exists|b:Binding|committed().contains(b)&&b.key==p.key&&b.realm==p.realm by {
        assert(p==key());assert(committed().contains(binding()));
    }
}
pub proof fn consumer_resolution(state:s::State<(int,int)>,actor:usize)
    requires s::registered(state,actor),state.control.fibers[actor].provisions.is_empty(),
        state.control.fibers[actor].dependencies==provided(),state.control.fibers[actor].committed==committed(),
    ensures gl::resolve(state,actor,key())==Some(0usize),
{
    assert(state.control.fibers[actor].committed.contains(binding())&&gl::names_key(binding(),key()));
    let b=choose|b:Binding|state.control.fibers[actor].committed.contains(b)&&gl::names_key(b,key());
    assert(b==binding());
}
/// No successful step is a premise: both children resolve and modify the very
/// same committed provider and key, followed by an actual strict Unload.
pub proof fn actual_execution()
    ensures g::execution(library(),programs(),trace(),labels()),trace().first()==g::empty::<(int,int),Stage>(),trace().len()==13,
        trace()[6].state.control.fibers[1usize].committed==committed(),trace()[8].state.control.fibers[2usize].committed==committed(),
        trace()[7].state.tables[0usize][key()]==(12int,1int),trace()[9].state.tables[0usize][key()]==(15int,2int),
        trace()[12].state.tables[0usize][key()]==(10int,0int),
        trace()[6].state.tables[0usize][key()]==(7int,10int),trace()[8].current[2usize]==Some(Stage::Consume),
        p::owns(trace()[6].state,key(),0),p::owns(trace()[12].state,key(),0),
        forall|i:int|6<=i<=11 ==> gr::installed(trace()[i].state,1),
        g::undo(trace()[7].history[3].landed.receipt,trace()[7].history[3].landed.state).is_some(),
        g::undo(trace()[7].history[3].landed.receipt,trace()[7].history[3].landed.state).unwrap().tables[0usize][key()]==(7int,0int),
        trace()[7].history[3].input.tables[0usize][key()]==(7int,10int),
        trace()[12].state.control.fibers[1usize].phase==Phase::Inactive,
{
    reveal(trace);root_members();let states=trace();
    assert(ISet::<Port>::empty().union(provided()) =~= provided());
    assert(g::step(library(),programs(),states[0],states[1],0,r::Rule::Insert));
    assert(g::step(library(),programs(),states[1],states[2],0,r::Rule::Begin));
    assert(g::step(library(),programs(),states[2],states[3],0,r::Rule::Iter));
    assert(g::step(library(),programs(),states[3],states[4],0,r::Rule::Iter));
    assert(g::step(library(),programs(),states[4],states[5],0,r::Rule::Finish));
    consumer_target(states[5].state,1);consumer_target(states[6].state,1);
    consumer_resolution(states[6].state,1);
    assert(g::step(library(),programs(),states[5],states[6],1,r::Rule::Begin));
    assert(g::step(library(),programs(),states[6],states[7],1,r::Rule::Finish));
    consumer_target(states[7].state,2);consumer_target(states[8].state,2);
    consumer_resolution(states[8].state,2);
    assert(g::step(library(),programs(),states[7],states[8],2,r::Rule::Begin));
    assert(g::step(library(),programs(),states[8],states[9],2,r::Rule::Finish));
    ch::concrete_child_retirement(states[9].state,1);
    assert(g::step(library(),programs(),states[9],states[10],1,r::Rule::Retire));
    assert(g::step(library(),programs(),states[10],states[11],1,r::Rule::Leave));
    consumer_resolution(states[11].state,1);
    assert(states[11].state.accumulators[1usize] =~= seq![3nat]);reveal_with_fuel(g::restore,2);
    assert(g::restore(states[11].history,states[11].state.accumulators[1usize],states[11].state,1).is_some());
    assert(g::step(library(),programs(),states[11],states[12],1,r::Rule::Unload));
    consumer_resolution(states[7].history[3].landed.state,1);
    assert forall|i:int|6<=i<=11 implies gr::installed(states[i].state,1) by {
        if i==6 {} else if i==7 {} else if i==8 {} else if i==9 {} else if i==10 {} else {assert(i==11);}
    }
    assert forall|i:int|0<=i<labels().len() implies g::step(library(),programs(),states[i],states[i+1],labels()[i].0,labels()[i].1) by {
        if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else if i==5 {} else if i==6 {} else if i==7 {} else if i==8 {} else if i==9 {} else if i==10 {} else {assert(i==11);}
    }
}
pub open spec fn foreign()->IMap<Port,(int,int)> {
    e::foreign_state(mr::events(library(),programs(),trace().subrange(6,12),labels().subrange(6,11),1),p::project(trace()[6].state,ISet::full()))
}
proof fn event_sequence(states:Seq<g::Configuration<(int,int),Stage>>,steps:Seq<(usize,r::Rule)>,owner:usize)
    requires states.len()==steps.len()+1,
    ensures mr::events(library(),programs(),states,steps,owner)==Seq::new(steps.len(),|i:int|mr::event(library(),programs(),states[i],states[i+1],steps[i].0,steps[i].1,owner)),
    decreases steps.len(),
{
    if steps.len()>0 {event_sequence(states.drop_last(),steps.drop_last(),owner);}
    assert(mr::events(library(),programs(),states,steps,owner) =~= Seq::new(steps.len(),|i:int|mr::event(library(),programs(),states[i],states[i+1],steps[i].0,steps[i].1,owner)));
}
proof fn five_events(es:Seq<e::Event<(int,int)>>,initial:IMap<Port,(int,int)>,action:e::Action<(int,int)>)
    requires es.len()==5,es[0].returned.is_some(),es[1].returned.is_none(),es[1].forward.len()==0,
        es[2].returned.is_none(),es[2].forward==seq![action],es[3].returned.is_none(),es[3].forward.len()==0,
        es[4].returned.is_none(),es[4].forward.len()==0,
    ensures e::foreign_state(es,initial)==e::apply(action,initial),
{
    reveal_with_fuel(e::foreign_state,6);reveal_with_fuel(e::run,2);
}
pub proof fn foreign_value()
    ensures foreign().dom().contains(key()),foreign()[key()]==(10int,2int),
{
    actual_execution();primitive_theory();ol::from_empty_safe(equality(),library(),programs(),trace(),labels());
    p::unique_owner(trace()[6].state);p::lookup(trace()[6].state,ISet::full(),key(),0);
    let es=mr::events(library(),programs(),trace().subrange(6,12),labels().subrange(6,11),1);
    event_sequence(trace().subrange(6,12),labels().subrange(6,11),1);assert(es.len()==5);
    assert(es[0].returned.is_some());assert(es[1].returned.is_none()&&es[1].forward.len()==0);
    let action=mr::forward_action(library(),programs()(2)(Stage::Consume));
    assert(es[2].returned.is_none()&&es[2].forward==seq![action]);
    assert(es[3].returned.is_none()&&es[3].forward.len()==0);assert(es[4].returned.is_none()&&es[4].forward.len()==0);
    five_events(es,p::project(trace()[6].state,ISet::full()),action);
}
/// The generic observational execution theorem is instantiated by the actual
/// history. Foreign value replay differs in raw hidden data from real recovery.
pub proof fn actual_observational_recovery()
    ensures {
        let states=trace();let after=states[12];
        &&& g::execution(library(),programs(),states,labels())
        &&& forall|i:int|0<=i<states.len() ==> g::well_formed(library(),programs(),states[i])
        &&& weak::primitive_theory(equality(),library())&&obs::independent_keys(equality(),library())
        &&& !d::primitive_theory(equality(),library())&&!gr::independent_keys(library())
        &&& after.state.tables[1usize].is_empty()&&after.state.control.fibers[1usize].phase==Phase::Inactive
        &&& after.state.tables[0usize][key()]==(10int,0int)
        &&& foreign().dom().contains(key())&&foreign()[key()]==(10int,2int)
        &&& obs::related(equality(),p::project(after.state,ISet::full()),foreign())
        &&& p::project(after.state,ISet::full())!=foreign()
        &&& g::undo(states[7].history[3].landed.receipt,states[7].history[3].landed.state).is_some()
        &&& g::undo(states[7].history[3].landed.receipt,states[7].history[3].landed.state).unwrap().tables[0usize][key()]==(7int,0int)
        &&& states[7].history[3].input.tables[0usize][key()]==(7int,10int)
    },
{
    actual_execution();primitive_theory();observational_interface();
    ol::from_empty_safe(equality(),library(),programs(),trace(),labels());let states=trace();foreign_value();
    execution::actual_terminal_recovery(equality(),library(),programs(),states,labels(),1,6,11);
    p::unique_owner(states[12].state);p::lookup(states[12].state,ISet::full(),key(),0);
    assert(p::project(states[12].state,ISet::full())[key()]==(10int,0int));
}

} // verus!
