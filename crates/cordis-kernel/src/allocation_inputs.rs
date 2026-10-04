//! The literal-name reading of external inputs is stronger than alpha input
//! equivalence. These two real executions use one fresh-binding program family
//! and identical external Insert payloads and Retire(2), yet expose different
//! service keys at quiescence. Renaming fibers cannot rename service keys.
//! No component computes, orders, or inspects the allocation atoms.
#[cfg(verus_keep_ghost)]
use crate::{
    alpha as names, causal_normalization as c, dependent_grammar as d, fresh_grammar as f,
    fresh_semantics as g, global, mixed_transposition as insert, observation as o,
    observational_grammar as og, preservation as inv, projection as p, refinement as r,
    semantics as s, Phase, Port,
};
use vstd::prelude::*;

verus! {
#[derive(PartialEq,Eq,Structural)]
pub enum Stage {SpawnA,SpawnB,ProvideA,ProvideB}

pub open spec fn key_a()->Port {Port {key:0,realm:0}}
pub open spec fn key_b()->Port {Port {key:1,realm:0}}
pub open spec fn keys(k:Port)->ISet<Port> {ISet::empty().insert(k)}
pub open spec fn provisions(id:Stage)->ISet<Port> {
    match id {Stage::ProvideA=>keys(key_a()),Stage::ProvideB=>keys(key_b()),_=>ISet::empty()}
}
pub open spec fn library()->g::Library<Port,int,int,()> {crate::recovery_examples::library()}
pub open spec fn programs()->g::Programs<Port,int,int,(),Stage> {
    |_:usize| |id:Stage| match id {
        Stage::SpawnA=>f::Node::FreshChild {dependencies:ISet::empty(),provisions:keys(key_a()),body:|_:usize|(Stage::ProvideA,None)},
        Stage::SpawnB=>f::Node::FreshChild {dependencies:ISet::empty(),provisions:keys(key_b()),body:|_:usize|(Stage::ProvideB,None)},
        Stage::ProvideA=>f::Node::Dependent {node:d::Node::Provision {key:key_a(),value:1,next:None}},
        Stage::ProvideB=>f::Node::Dependent {node:d::Node::Provision {key:key_b(),value:1,next:None}},
    }
}

/// Component code is independent of the chosen atom, including child roots.
pub proof fn natural_program()
    ensures f::natural(f::name_free::<Stage>(),programs()),
{
    assert forall|rho:names::Renaming,actor:usize,id:Stage,choice:Option<usize>|names::bijective(rho) implies
        #[trigger] f::instantiate(programs()((rho.forward)(actor))((f::name_free::<Stage>().apply)(rho,id)),names::parent(rho,choice))
            ==f::instantiate(f::node(rho,f::action_map(f::name_free::<Stage>(),rho),programs()(actor)(id)),names::parent(rho,choice)) by {
        match id {Stage::SpawnA=>{},Stage::SpawnB=>{},Stage::ProvideA=>{},Stage::ProvideB=>{}}
    }
}
pub proof fn component_member(actor:usize,id:Stage)
    ensures f::member(library(),programs(),actor,provisions(id),provisions(id),id),
{
    match id {
        Stage::SpawnA=>{
            assert forall|child:usize|f::member(library(),programs(),child,keys(key_a()),keys(key_a()),Stage::ProvideA) by {
                f::constructor_member(library(),programs(),child,keys(key_a()),keys(key_a()),Stage::ProvideA);
            }
        },
        Stage::SpawnB=>{
            assert forall|child:usize|f::member(library(),programs(),child,keys(key_b()),keys(key_b()),Stage::ProvideB) by {
                f::constructor_member(library(),programs(),child,keys(key_b()),keys(key_b()),Stage::ProvideB);
            }
        },_=>{},
    }
    f::constructor_member(library(),programs(),actor,provisions(id),provisions(id),id);
}

/// Every successful activation is one landing and installs its entire declared
/// provision in every well-formed input, not just in the two example traces.
pub proof fn total_component(a:s::State<int>,actor:usize,id:Stage,choice:Option<usize>)
    requires inv::well_formed(a),s::registered(a,actor),a.control.fibers[actor].provisions==provisions(id),
        f::run(library(),programs()(actor)(id),a,actor,choice).is_some(),
    ensures f::run(library(),programs()(actor)(id),a,actor,choice).unwrap().next.is_none(),
        f::run(library(),programs()(actor)(id),a,actor,choice).unwrap().state.tables[actor].dom()==provisions(id),
{
    let out=f::run(library(),programs()(actor)(id),a,actor,choice).unwrap();
    match id {
        Stage::SpawnA | Stage::SpawnB=>{f::allocation_guard(library(),programs()(actor)(id),a,actor,choice);assert(a.tables[actor].dom() =~= ISet::empty());},
        Stage::ProvideA | Stage::ProvideB=>{assert(out.state.tables[actor].dom() =~= provisions(id));},
    }
}

pub type Label=crate::fresh_semantics::Label;
pub open spec fn execution(states:Seq<g::Configuration<int,Stage>>,labels:Seq<Label>)->bool {
    g::execution(library(),programs(),states,labels)
}
pub open spec fn plain(labels:Seq<Label>)->Seq<c::Label> {labels.map(|_:int,label:Label|(label.0,label.1))}

/// `reverse` changes only the lifecycle scheduling. Both executions draw 2
/// then 3, legal choices of fresh atoms; neither component chooses a number.
#[verifier::opaque]
pub open spec fn trace(reverse:bool)->Seq<g::Configuration<int,Stage>> {
    let first=if reverse {1usize}else{0usize};let second=if reverse {0usize}else{1usize};
    let a0=g::empty::<int,Stage>();
    let a1=insert::insert(a0,0,None,ISet::empty(),ISet::empty(),Stage::SpawnA);
    let a2=insert::insert(a1,1,None,ISet::empty(),ISet::empty(),Stage::SpawnB);
    let a3=g::edit(a2,first,Phase::Loading,ISet::empty(),Some(a2.roots[first]),Seq::empty());
    let a4=g::land(library(),programs(),a3,first,Phase::Active,Some(2));
    let a5=g::edit(a4,second,Phase::Loading,ISet::empty(),Some(a4.roots[second]),Seq::empty());
    let a6=g::land(library(),programs(),a5,second,Phase::Active,Some(3));
    let a7=g::Configuration {state:s::with_control(a6.state,global::retire_fiber(a6.state.control,2)),..a6};
    let a8=g::edit(a7,3,Phase::Loading,ISet::empty(),Some(a7.roots[3usize]),Seq::empty());
    let a9=g::land(library(),programs(),a8,3,Phase::Active,None);
    seq![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9]
}
pub open spec fn labels(reverse:bool)->Seq<Label> {
    let first=if reverse {1usize}else{0usize};let second=if reverse {0usize}else{1usize};
    seq![(0usize,r::Rule::Insert,None),(1usize,r::Rule::Insert,None),
        (first,r::Rule::Begin,None),(first,r::Rule::Finish,Some(2usize)),
        (second,r::Rule::Begin,None),(second,r::Rule::Finish,Some(3usize)),
        (2usize,r::Rule::Retire,None),(3usize,r::Rule::Begin,None),(3usize,r::Rule::Finish,None)]
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn actual_execution(reverse:bool)
    ensures execution(trace(reverse),labels(reverse)),trace(reverse).first()==g::empty::<int,Stage>(),
        forall|i:int| 0<=i<trace(reverse).len() ==> g::well_formed(library(),programs(),trace(reverse)[i]),
{
    let lib=library();let code=programs();let eq=crate::recovery_examples::equality();
    crate::recovery_examples::primitive_theory();og::exact_theory(eq,lib);
    component_member(0,Stage::SpawnA);component_member(1,Stage::SpawnB);g::empty_well_formed(lib,code);
    reveal(trace);let t=trace(reverse);let l=labels(reverse);let first=if reverse {1usize}else{0usize};let second=if reverse {0usize}else{1usize};
    assert(g::step(lib,code,t[0],t[1],0,r::Rule::Insert,None));g::configuration_preservation(eq,lib,code,t[0],t[1],0,r::Rule::Insert,None);
    assert(g::step(lib,code,t[1],t[2],1,r::Rule::Insert,None));g::configuration_preservation(eq,lib,code,t[1],t[2],1,r::Rule::Insert,None);
    assert(g::step(lib,code,t[2],t[3],first,r::Rule::Begin,None));g::configuration_preservation(eq,lib,code,t[2],t[3],first,r::Rule::Begin,None);
    assert(g::step(lib,code,t[3],t[4],first,r::Rule::Finish,Some(2)));g::configuration_preservation(eq,lib,code,t[3],t[4],first,r::Rule::Finish,Some(2));
    assert(g::step(lib,code,t[4],t[5],second,r::Rule::Begin,None));g::configuration_preservation(eq,lib,code,t[4],t[5],second,r::Rule::Begin,None);
    assert(g::step(lib,code,t[5],t[6],second,r::Rule::Finish,Some(3)));g::configuration_preservation(eq,lib,code,t[5],t[6],second,r::Rule::Finish,Some(3));
    assert(g::step(lib,code,t[6],t[7],2,r::Rule::Retire,None));g::configuration_preservation(eq,lib,code,t[6],t[7],2,r::Rule::Retire,None);
    assert(g::step(lib,code,t[7],t[8],3,r::Rule::Begin,None));g::configuration_preservation(eq,lib,code,t[7],t[8],3,r::Rule::Begin,None);
    assert(g::step(lib,code,t[8],t[9],3,r::Rule::Finish,None));g::configuration_preservation(eq,lib,code,t[8],t[9],3,r::Rule::Finish,None);
    assert forall|i:int| 0<=i<l.len() implies g::step(lib,code,t[i],t[i+1],l[i].0,l[i].1,l[i].2) by {
        if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else if i==5 {} else if i==6 {} else if i==7 {} else {assert(i==8);}
    }
    assert forall|i:int| 0<=i<t.len() implies g::well_formed(lib,code,t[i]) by {
        if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else if i==5 {} else if i==6 {} else if i==7 {} else if i==8 {} else {assert(i==9);}
    }
}

pub proof fn same_inputs()
    ensures c::inputs(trace(false),plain(labels(false)))==c::inputs(trace(true),plain(labels(true))),
        c::externals(plain(labels(false)))==seq![(0usize,r::Rule::Insert),(1usize,r::Rule::Insert),(2usize,r::Rule::Retire)],
        c::externals(plain(labels(true)))==c::externals(plain(labels(false))),
        trace(false)[1]==trace(true)[1],trace(false)[2]==trace(true)[2],
{
    reveal(trace);reveal_with_fuel(c::externals,10);
    assert(c::raw_inputs(trace(false),plain(labels(false))) =~= c::raw_inputs(trace(true),plain(labels(true)))) by {
        assert forall|i:int| 0<=i<labels(false).len() implies c::input(trace(false)[i+1],plain(labels(false))[i])==c::input(trace(true)[i+1],plain(labels(true))[i]) by {
            if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else if i==5 {} else if i==6 {} else if i==7 {} else {assert(i==8);}
        }
    }
}

pub proof fn terminal(reverse:bool)
    ensures trace(reverse).len()==10,g::well_formed(library(),programs(),trace(reverse).last()),
        trace(reverse).last().roots[2usize]==if reverse {Stage::ProvideB}else{Stage::ProvideA},
        trace(reverse).last().state.control.fibers[2usize].retired,
        trace(reverse).last().state.control.fibers.dom()==ISet::empty().insert(0usize).insert(1usize).insert(2usize).insert(3usize),
        s::quiet(trace(reverse).last().state),s::total_active(trace(reverse).last().state),
        global::support_ranking(trace(reverse).last().state.control,seq![0nat,0nat,1nat,1nat]),
        trace(reverse).last().state.tables[3usize]==IMap::empty().insert(if reverse {key_a()}else{key_b()},1int),
        forall|id:usize| s::registered(trace(reverse).last().state,id) && id!=3 ==> trace(reverse).last().state.tables[id].is_empty(),
        p::project(trace(reverse).last().state,ISet::full()).dom()==keys(if reverse {key_a()}else{key_b()}),
{
    actual_execution(reverse);reveal(trace);let z=trace(reverse).last();let k=if reverse {key_a()}else{key_b()};
    assert(z.state.tables[3usize] =~= IMap::empty().insert(k,1int));
    assert(z.state.control.fibers.dom() =~= ISet::empty().insert(0usize).insert(1usize).insert(2usize).insert(3usize));
    assert(s::quiet(z.state)) by {
        assert forall|id:usize| s::registered(z.state,id) implies match z.state.control.fibers[id].phase {
            Phase::Inactive=>!(exists|view:ISet<crate::Binding>|s::target(z.state,id,view)),
            Phase::Active=>s::coherent(z.state,id),_=>false,
        } by {if id==0 {} else if id==1 {} else if id==2 {} else {assert(id==3);}}
    }
    assert(s::total_active(z.state)) by {
        assert forall|id:usize| s::registered(z.state,id) && z.state.control.fibers[id].phase==Phase::Active implies z.state.tables[id].dom()==z.state.control.fibers[id].provisions by {
            if id==0 {} else if id==1 {} else {assert(id==3);assert(z.state.tables[id].dom() =~= keys(k));}
        }
    }
    assert(global::support_ranking(z.state.control,seq![0nat,0nat,1nat,1nat]));
    assert(p::project(z.state,ISet::full()).dom() =~= keys(k)) by {
        assert forall|key:Port| p::project(z.state,ISet::full()).dom().contains(key)==keys(k).contains(key) by {
            if p::project(z.state,ISet::full()).dom().contains(key) {
                let id=choose|id:usize|p::owns(z.state,key,id);assert(id==3);
            } else if key==k {assert(p::owns(z.state,key,3));}
        }
    }
}

/// The two terminal observations are separated by key B for every bijection
/// of fiber atoms. The impossibility already holds at the coarse all-table view.
pub proof fn no_terminal_alpha(rho:names::Renaming)
    requires names::bijective(rho),
    ensures !o::context_equal(crate::recovery_examples::equality(),ISet::full(),
        p::project(names::context(rho,trace(false).last().state),ISet::full()),p::project(trace(true).last().state,ISet::full())),
{
    terminal(false);terminal(true);let a=trace(false).last().state;let b=trace(true).last().state;
    let renamed=names::context(rho,a);let owner=(rho.forward)(3usize);
    assert((rho.backward)(owner)==3);assert(a.tables.dom().contains(3usize));
    names::observations(rho,a.control,3);
    assert(renamed.tables[owner]==a.tables[3usize]);assert(p::owns(renamed,key_b(),owner));
    assert(p::project(renamed,ISet::full()).dom().contains(key_b()));
    assert(!p::project(b,ISet::full()).dom().contains(key_b()));
}

/// The only component templates occurring in either execution use the precise
/// interfaces for which total_component proved universal completion coverage.
pub open spec fn bounded_catalogue(states:Seq<g::Configuration<int,Stage>>,events:Seq<Label>)->bool {
    &&& forall|i:int| 0<=i<states.len() ==> {
        &&& states[i].state.control.fibers.dom().subset_of(ISet::empty().insert(0usize).insert(1usize).insert(2usize).insert(3usize))
        &&& global::support_ranking(states[i].state.control,seq![0nat,0nat,1nat,1nat])
        &&& forall|id:usize| s::registered(states[i].state,id) ==> {
            &&& states[i].state.control.fibers[id].dependencies.is_empty()
            &&& states[i].state.control.fibers[id].provisions==provisions(states[i].roots[id])
        }
    }
    &&& forall|i:int| 0<=i<events.len() && g::landing(states[i],states[i+1],events[i].1) ==> {
        let out=f::run(library(),programs()(events[i].0)(states[i].current[events[i].0].unwrap()),states[i].state,events[i].0,events[i].2);
        &&& out.is_some() && out.unwrap().next.is_none()
    }
}
pub proof fn catalogue(reverse:bool)
    ensures bounded_catalogue(trace(reverse),labels(reverse)),
        forall|i:int,id:usize| 0<=i<trace(reverse).len() && s::registered(trace(reverse)[i].state,id) ==> {
        let a=trace(reverse)[i];
        &&& a.state.control.fibers[id].dependencies.is_empty()
        &&& a.state.control.fibers[id].provisions==provisions(a.roots[id])
    },
{
    reveal(trace);let t=trace(reverse);
    assert forall|i:int,id:usize| 0<=i<t.len() && s::registered(t[i].state,id) implies {
        let a=t[i];
        &&& a.state.control.fibers[id].dependencies.is_empty()
        &&& a.state.control.fibers[id].provisions==provisions(a.roots[id])
    } by {
        if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else if i==5 {} else if i==6 {} else if i==7 {} else if i==8 {} else {assert(i==9);}
    }
    assert forall|i:int| 0<=i<t.len() implies t[i].state.control.fibers.dom().subset_of(ISet::empty().insert(0usize).insert(1usize).insert(2usize).insert(3usize))
        && global::support_ranking(t[i].state.control,seq![0nat,0nat,1nat,1nat]) by {
        if i==0 {} else if i==1 {} else if i==2 {} else if i==3 {} else if i==4 {} else if i==5 {} else if i==6 {} else if i==7 {} else if i==8 {} else {assert(i==9);}
    }
    let events=labels(reverse);
    assert forall|i:int| 0<=i<events.len() && g::landing(t[i],t[i+1],events[i].1) implies {
        let out=f::run(library(),programs()(events[i].0)(t[i].current[events[i].0].unwrap()),t[i].state,events[i].0,events[i].2);
        &&& out.is_some() && out.unwrap().next.is_none()
    } by {
        if i==3 {} else if i==5 {} else {assert(i==8);}
    }

}

/// A concrete boundary for a literal-name interpretation of Theorem 80(2).
/// The input subsequences agree including both Insert payloads and their roots.
/// They do not agree when dynamic references are transported by birth origin:
/// atom 2 names A's child in one execution and B's child in the other.
#[verifier::spinoff_prover]
#[verifier::rlimit(20)]
pub proof fn literal_input_counterexample()
    ensures {
        let left=trace(false);let right=trace(true);
        &&& f::natural(f::name_free::<Stage>(),programs())
        &&& bounded_catalogue(left,labels(false)) && bounded_catalogue(right,labels(true))
        &&& left.first()==g::empty::<int,Stage>() && right.first()==left.first()
        &&& g::execution(library(),programs(),left,labels(false)) && g::execution(library(),programs(),right,labels(true))
        &&& g::well_formed(library(),programs(),left.last()) && g::well_formed(library(),programs(),right.last())
        &&& c::inputs(left,plain(labels(false)))==c::inputs(right,plain(labels(true)))
        &&& c::externals(plain(labels(false)))==c::externals(plain(labels(true)))
        &&& c::externals(plain(labels(false)))==seq![(0usize,r::Rule::Insert),(1usize,r::Rule::Insert),(2usize,r::Rule::Retire)]
        &&& s::quiet(left.last().state) && s::quiet(right.last().state) && s::total_active(left.last().state) && s::total_active(right.last().state)
        &&& global::support_ranking(left.last().state.control,seq![0nat,0nat,1nat,1nat])
        &&& global::support_ranking(right.last().state.control,seq![0nat,0nat,1nat,1nat])
        &&& left.last().roots[2usize]==Stage::ProvideA && right.last().roots[2usize]==Stage::ProvideB
        &&& left.last().state.control.fibers[2usize].retired && right.last().state.control.fibers[2usize].retired
        &&& p::project(left.last().state,ISet::full()).dom()==keys(key_b()) && p::project(right.last().state,ISet::full()).dom()==keys(key_a())
        &&& forall|rho:names::Renaming| names::bijective(rho) ==> !o::context_equal(crate::recovery_examples::equality(),ISet::full(),
            p::project(names::context(rho,left.last().state),ISet::full()),p::project(right.last().state,ISet::full()))
    },
{
    hide(f::natural);hide(g::well_formed);hide(g::execution);hide(o::context_equal);hide(bounded_catalogue);
    natural_program();actual_execution(false);actual_execution(true);same_inputs();terminal(false);terminal(true);catalogue(false);catalogue(true);
    assert forall|rho:names::Renaming| names::bijective(rho) implies !o::context_equal(crate::recovery_examples::equality(),ISet::full(),
        p::project(names::context(rho,trace(false).last().state),ISet::full()),p::project(trace(true).last().state,ISet::full())) by {no_terminal_alpha(rho);}
}

} // verus!
