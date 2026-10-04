//! Strict shared-key replay with raw dependent outcome stability.
//!
//! Value commutation alone cannot retain a continuation selected from an
//! operation outcome. The existing coeffect interface also compares outcomes
//! and the returned partial inverse maps. This module uses that interface
//! without turning a failed source callback into a transition.
#[cfg(verus_keep_ghost)]
use crate::{
    calculus as c, dependent_grammar as d, dependent_lift as dep, grammar_lift as lift,
    mediated as m, mixed_grammar as g, observation as o, observational_grammar as og,
    observational_lift as ol, partial_independence as pi, preservation as inv, projection as p,
    refinement as r, semantics as s, strict_journal as sj, Phase, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn operational<A,X,U,B,I>(node:dep::Node<A,X,U,B,I>)->bool {
    match node {d::Node::Unit | d::Node::Operation {..}=>true,_=>false}
}
/// Same-key witnesses include forward/inverse strict commutation, raw outcome
/// stability and related returned inverses. Distinct keys need no scalar law.
pub open spec fn interface<A,X,U,B>(eq:spec_fn(Port,U,U)->bool,lib:dep::Library<A,X,U,B>)->bool {
    forall|a:A,b:A,x:X,y:X| #![trigger (lib.apply)(a,x),(lib.apply)(b,y)] lib.allowed.contains(a) && lib.allowed.contains(b)
        && (lib.arguments)(a,x) && (lib.arguments)(b,y) && (lib.key)(a)==(lib.key)(b)
        ==> pi::value_independent(|u:U,v:U|eq((lib.key)(a),u,v),(lib.apply)(a,x),(lib.apply)(b,y))
}
pub proof fn context_equivalence<A,X,U,B>(eq:spec_fn(Port,U,U)->bool,lib:dep::Library<A,X,U,B>)
    requires og::primitive_theory(eq,lib),
    ensures c::equivalence(pi::context_eq(eq)),
{
    assert forall|key:Port| ISet::<Port>::full().contains(key) implies c::equivalence(|u:U,v:U|eq(key,u,v)) by {
        assert(m::key_equivalence(eq,key));
    }
    o::context_equivalence(eq,ISet::full());
}

/// Observational primitive witnesses suffice for the old IMap interpreter's
/// respect clause; its stronger literal-recovery premise is not imported.
pub proof fn stage_respects<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:dep::Library<A,X,U,B>,node:dep::Node<A,X,U,B,I>,keys:ISet<Port>,provided:ISet<Port>)
    requires og::primitive_theory(eq,lib),d::permitted(lib,keys,provided,node),operational(node),
    ensures m::stage_respects(eq,ISet::full(),dep::stage(lib,node)),
{
    let stage=dep::stage(lib,node);
    assert forall|a:IMap<Port,U>,b:IMap<Port,U>| #![trigger m::run(stage,a),m::run(stage,b)] pi::context_eq(eq)(a,b) implies {
        &&& m::run(stage,a).is_some()==m::run(stage,b).is_some()
        &&& (m::run(stage,a).is_some() ==> {
            let x=m::run(stage,a).unwrap();let y=m::run(stage,b).unwrap();
            &&& pi::context_eq(eq)(x.state,y.state)
            &&& m::partial_related(pi::context_eq(eq),x.undo,y.undo) && x.next==y.next
        })
    } by {
        match node {
            d::Node::Operation {operation,argument,..}=>{
                let key=(lib.key)(operation);let op=(lib.apply)(operation,argument);
                assert(d::operation_typed(lib,operation,argument));
                assert(og::operation_respects(|u:U,v:U|eq(key,u,v),op));
                assert(o::context_equal(eq,ISet::full(),a,b));assert(ISet::<Port>::full().contains(key));
                assert(a.dom().contains(key)==b.dom().contains(key));
                if a.dom().contains(key) {
                    assert(eq(key,a[key],b[key]));
                    if op(a[key]).is_some() {
                        let left=op(a[key]).unwrap();let right=op(b[key]).unwrap();
                        m::update_related(eq,ISet::full(),key,a,b,left.value,right.value);
                        m::inverse_lift_respects(eq,ISet::full(),key,left.undo,right.undo);
                    }
                }
            },
            _=>{},
        }
    }
}

pub proof fn stages_independent<A,X,U,B,I,J>(eq:spec_fn(Port,U,U)->bool,lib:dep::Library<A,X,U,B>,left:dep::Node<A,X,U,B,I>,right:dep::Node<A,X,U,B,J>,
    left_keys:ISet<Port>,left_provided:ISet<Port>,right_keys:ISet<Port>,right_provided:ISet<Port>)
    requires og::primitive_theory(eq,lib),interface(eq,lib),operational(left),operational(right),
        d::permitted(lib,left_keys,left_provided,left),d::permitted(lib,right_keys,right_provided,right),
    ensures pi::independent(eq,dep::stage(lib,left),dep::stage(lib,right)),
{
    context_equivalence(eq,lib);stage_respects(eq,lib,left,left_keys,left_provided);stage_respects(eq,lib,right,right_keys,right_provided);
    match left {
        d::Node::Unit=>{pi::unit_independence::<Port,U,B,B>(eq,dep::stage(lib,right));},
        d::Node::Operation {operation:a,argument:x,select:an}=>{match right {
            d::Node::Unit=>{pi::unit_independence::<Port,U,B,B>(eq,dep::stage(lib,left));},
            d::Node::Operation {operation:b,argument:y,select:bn}=>{
                if (lib.key)(a)==(lib.key)(b) {
                    assert(pi::value_independent(|u:U,v:U|eq((lib.key)(a),u,v),(lib.apply)(a,x),(lib.apply)(b,y)));
                    pi::shared_operations(eq,(lib.key)(a),(lib.apply)(a,x),(lib.apply)(b,y),|out:B|dep::marker(an(out)),|out:B|dep::marker(bn(out)));
                } else {pi::distinct_nodes(eq,dep::stage(lib,left),dep::stage(lib,right));}
            },
            _=>{},
        }},
        _=>{},
    }
}

pub proof fn actual_receipt_projects<A,X,U,B,I>(lib:dep::Library<A,X,U,B>,node:dep::Node<A,X,U,B,I>,a:s::State<U>,actor:usize)
    requires inv::well_formed(a),dep::run(lib,node,a,actor).is_some(),
    ensures {
        let stage=dep::stage(lib,node);let input=p::project(a,ISet::full());
        &&& m::run(stage,input).is_some()
        &&& lift::projected_inverse(dep::run(lib,node,a,actor).unwrap().receipt)==m::run(stage,input).unwrap().undo
        &&& pi::generators(stage).contains(lift::projected_inverse(dep::run(lib,node,a,actor).unwrap().receipt))
    },
{
    lift::run_projects(dep::stage(lib,node),a,actor);
    match node {
        d::Node::Operation {operation,..}=>{
            let key=(lib.key)(operation);let provider=lift::resolve(a,actor,key).unwrap();
            lift::resolution_sound(a,actor,key);p::unique_owner(a);p::lookup(a,ISet::full(),key,provider);
        },_=>{},
    }
    let stage=dep::stage(lib,node);let input=p::project(a,ISet::full());
    assert(exists|input:IMap<Port,U>| #[trigger] m::run(stage,input).is_some()
        && m::run(stage,input).unwrap().undo==lift::projected_inverse(dep::run(lib,node,a,actor).unwrap().receipt));
}

pub proof fn raw_outcome_respects<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:dep::Library<A,X,U,B>,node:dep::Node<A,X,U,B,I>,
    keys:ISet<Port>,provided:ISet<Port>,a:IMap<Port,U>,b:IMap<Port,U>)
    requires og::primitive_theory(eq,lib),d::permitted(lib,keys,provided,node),pi::context_eq(eq)(a,b),
    ensures pi::outcome(dep::stage(lib,node),a)==pi::outcome(dep::stage(lib,node),b),
{
    match node {
        d::Node::Operation {operation,argument,..}=>{
            let key=(lib.key)(operation);let op=(lib.apply)(operation,argument);
            assert(d::operation_typed(lib,operation,argument));assert(og::operation_respects(|u:U,v:U|eq(key,u,v),op));
            assert(o::context_equal(eq,ISet::full(),a,b));assert(ISet::<Port>::full().contains(key));
            assert(a.dom().contains(key)==b.dom().contains(key));
            if a.dom().contains(key) {assert(eq(key,a[key],b[key]));}
        },_=>{},
    }
}

pub proof fn actual_next<A,X,U,B,I>(lib:dep::Library<A,X,U,B>,node:dep::Node<A,X,U,B,I>,a:s::State<U>,b:s::State<U>,actor:usize)
    requires inv::well_formed(a),inv::well_formed(b),dep::run(lib,node,a,actor).is_some(),dep::run(lib,node,b,actor).is_some(),
        pi::outcome(dep::stage(lib,node),p::project(a,ISet::full()))==pi::outcome(dep::stage(lib,node),p::project(b,ISet::full())),
    ensures dep::run(lib,node,a,actor).unwrap().next==dep::run(lib,node,b,actor).unwrap().next,
{
    match node {
        d::Node::Operation {operation,..}=>{
            let key=(lib.key)(operation);let pa=lift::resolve(a,actor,key).unwrap();let pb=lift::resolve(b,actor,key).unwrap();
            lift::resolution_sound(a,actor,key);lift::resolution_sound(b,actor,key);
            p::unique_owner(a);p::unique_owner(b);p::lookup(a,ISet::full(),key,pa);p::lookup(b,ISet::full(),key,pb);
        },_=>{},
    }
}

/// Local replay bridge. A completed strict journal word and local coeffect
/// witnesses determine an actual target run, including its arbitrary-I next
/// index and the relation of the two freshly returned inverse receipts.
pub proof fn run_after_word<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:dep::Library<A,X,U,B>,node:dep::Node<A,X,U,B,I>,
    source:s::State<U>,target:s::State<U>,actor:usize,word:Seq<m::PartialMap<IMap<Port,U>>>)
    requires og::primitive_theory(eq,lib),inv::well_formed(source),inv::well_formed(target),operational(node),
        s::registered(target,actor),target.control.fibers[actor].phase!=Phase::Inactive,
        source.control.fibers[actor]==target.control.fibers[actor],
        d::permitted(lib,dep::declarations(source,actor),source.control.fibers[actor].provisions,node),
        dep::run(lib,node,source,actor).is_some(),
        pi::run(word,p::project(source,ISet::full())).is_some(),
        pi::context_eq(eq)(pi::run(word,p::project(source,ISet::full())).unwrap(),p::project(target,ISet::full())),
        forall|i:int| 0<=i<word.len() ==> pi::stable(eq,dep::stage(lib,node),#[trigger] word[i]),
    ensures {
        let old=dep::run(lib,node,source,actor).unwrap();let new=dep::run(lib,node,target,actor).unwrap();
        &&& dep::run(lib,node,target,actor).is_some() && new.next==old.next
        &&& pi::outcome(dep::stage(lib,node),p::project(source,ISet::full()))
            ==pi::outcome(dep::stage(lib,node),p::project(target,ISet::full()))
        &&& m::partial_related(pi::context_eq(eq),lift::projected_inverse(old.receipt),lift::projected_inverse(new.receipt))
    },
{
    context_equivalence(eq,lib);stage_respects(eq,lib,node,dep::declarations(source,actor),source.control.fibers[actor].provisions);
    let stage=dep::stage(lib,node);let input=p::project(source,ISet::full());let middle=pi::run(word,input).unwrap();let output=p::project(target,ISet::full());
    actual_receipt_projects(lib,node,source,actor);pi::stable_word(eq,stage,word);
    let restore=|s:IMap<Port,U>|pi::run(word,s);
    assert(pi::stable(eq,stage,restore));assert(restore(input).is_some());
    assert(m::run(stage,middle).is_some());assert(m::run(stage,output).is_some());
    raw_outcome_respects(eq,lib,node,dep::declarations(source,actor),source.control.fibers[actor].provisions,middle,output);
    let allowed=|_:Port,_:m::Operation<U,B>|true;
    lift::run_definedness(stage,allowed,target,actor);
    actual_receipt_projects(lib,node,target,actor);actual_next(lib,node,source,target,actor);
    pi::partial_relation_transitive(pi::context_eq(eq),m::run(stage,input).unwrap().undo,m::run(stage,middle).unwrap().undo,m::run(stage,output).unwrap().undo);
}

pub open spec fn call_event<A,X,U,B,I>(lib:dep::Library<A,X,U,B>,node:dep::Node<A,X,U,B,I>,input:s::State<U>,actor:usize,own:bool)->sj::Event<IMap<Port,U>> {
    sj::Event {forward:pi::forward(dep::stage(lib,node)),
        inverse:lift::projected_inverse(dep::run(lib,node,input,actor).unwrap().receipt),own}
}
/// An event is extracted from the actual full-state operation and actual
/// returned inverse. Its local witness and respect laws follow from primitives.
pub proof fn call_contract<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:dep::Library<A,X,U,B>,node:dep::Node<A,X,U,B,I>,input:s::State<U>,actor:usize,own:bool)
    requires og::primitive_theory(eq,lib),inv::well_formed(input),dep::run(lib,node,input,actor).is_some(),operational(node),
        d::permitted(lib,dep::declarations(input,actor),input.control.fibers[actor].provisions,node),
    ensures {
        let e=call_event(lib,node,input,actor,own);let start=p::project(input,ISet::full());
        &&& (e.forward)(start)==Some(p::project(dep::run(lib,node,input,actor).unwrap().state,ISet::full()))
        &&& (e.inverse)((e.forward)(start).unwrap()).is_some()
        &&& pi::context_eq(eq)((e.inverse)((e.forward)(start).unwrap()).unwrap(),start)
        &&& pi::respects(pi::context_eq(eq),e.forward) && pi::respects(pi::context_eq(eq),e.inverse)
    },
{
    context_equivalence(eq,lib);let ctx=pi::context_eq(eq);let start=p::project(input,ISet::full());let stage=dep::stage(lib,node);
    actual_receipt_projects(lib,node,input,actor);stage_respects(eq,lib,node,dep::declarations(input,actor),input.control.fibers[actor].provisions);
    lift::run_projects(stage,input,actor);assert(ctx(start,start));
    let e=call_event(lib,node,input,actor,own);
    assert forall|a:IMap<Port,U>,b:IMap<Port,U>| #![trigger (e.forward)(a),(e.forward)(b)] ctx(a,b) implies {
        &&& (e.forward)(a).is_some()==(e.forward)(b).is_some()
        &&& ((e.forward)(a).is_some() ==> ctx((e.forward)(a).unwrap(),(e.forward)(b).unwrap()))
    } by {assert(m::run(stage,a).is_some()==m::run(stage,b).is_some());}
    match node {
        d::Node::Operation {operation,argument,..}=>{
            let key=(lib.key)(operation);let op=(lib.apply)(operation,argument);let y=op(start[key]).unwrap();
            assert(d::operation_typed(lib,operation,argument));assert(og::operation_witness(|a:U,b:U|eq(key,a,b),op));
            assert((y.undo)(y.value).is_some());let restored=(y.undo)(y.value).unwrap();assert(eq(key,restored,start[key]));
            m::update_related(eq,ISet::full(),key,start,start,restored,start[key]);
            assert(start.insert(key,start[key]) =~= start);
            assert(start.insert(key,y.value).insert(key,restored) =~= start.insert(key,restored));
        },_=>{},
    }
}

/// Pairwise contracts are derived for the actual returned inverses, including
/// inverses from operations whose raw outcomes have different dependent fibers.
pub proof fn call_independence<A,X,U,B,I,J>(eq:spec_fn(Port,U,U)->bool,lib:dep::Library<A,X,U,B>,left:dep::Node<A,X,U,B,I>,right:dep::Node<A,X,U,B,J>,
    a:s::State<U>,b:s::State<U>,actor:usize,foreign:usize)
    requires og::primitive_theory(eq,lib),interface(eq,lib),inv::well_formed(a),inv::well_formed(b),operational(left),operational(right),
        dep::run(lib,left,a,actor).is_some(),dep::run(lib,right,b,foreign).is_some(),
        d::permitted(lib,dep::declarations(a,actor),a.control.fibers[actor].provisions,left),
        d::permitted(lib,dep::declarations(b,foreign),b.control.fibers[foreign].provisions,right),
    ensures {
        let old=call_event(lib,left,a,actor,true);let next=call_event(lib,right,b,foreign,false);
        &&& pi::commutes(pi::context_eq(eq),old.inverse,next.forward)
        &&& pi::commutes(pi::context_eq(eq),old.inverse,next.inverse)
        &&& pi::stable(eq,dep::stage(lib,right),old.inverse)
    },
{
    actual_receipt_projects(lib,left,a,actor);actual_receipt_projects(lib,right,b,foreign);
    stages_independent(eq,lib,left,right,dep::declarations(a,actor),a.control.fibers[actor].provisions,
        dep::declarations(b,foreign),b.control.fibers[foreign].provisions);
    assert(pi::generators(dep::stage(lib,right)).contains(pi::forward(dep::stage(lib,right))));
}

pub open spec fn dependent<A,X,U,B,I>(node:g::Node<A,X,U,B,I>)->dep::Node<A,X,U,B,I> {
    match node {g::Node::Dependent {node}=>node,_=>d::Node::Unit}
}
pub open spec fn operational_mixed<A,X,U,B,I>(node:g::Node<A,X,U,B,I>)->bool {
    match node {g::Node::Dependent {node}=>operational(node),_=>false}
}
/// First shared-key boundary: a fixed registry, no Child/Provision stages and
/// no Unload inside the fragment. Actual foreign inverses need a separate
/// inverse-of-inverse argument before a foreign Unload can be admitted here.
pub open spec fn fragment_step<A,X,U,B,I>(programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule)->bool {
    rule!=r::Rule::Insert && rule!=r::Rule::Remove && rule!=r::Rule::Unload
        && (g::landing(a,z,rule) ==> operational_mixed(programs(actor)(a.current[actor].unwrap())))
}
pub open spec fn fragment<A,X,U,B,I>(programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)->bool {
    forall|i:int| 0<=i<labels.len() ==> fragment_step(programs,source[i],source[i+1],labels[i].0,labels[i].1)
}
pub open spec fn identity<U>()->m::PartialMap<IMap<Port,U>> {|state:IMap<Port,U>|Some(state)}
pub open spec fn event<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,owner:usize)->sj::Event<IMap<Port,U>> {
    if g::landing(a,z,rule) {call_event(lib,dependent(programs(actor)(a.current[actor].unwrap())),a.state,actor,actor==owner)}
    else {sj::Event {forward:identity(),inverse:identity(),own:false}}
}
pub open spec fn events<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)->Seq<sj::Event<IMap<Port,U>>> {
    labels.map(|i:int,label:(usize,r::Rule)|event(lib,programs,source[i],source[i+1],label.0,label.1,owner))
}
pub proof fn identity_contract<U>(eq:spec_fn(Port,U,U)->bool,f:m::PartialMap<IMap<Port,U>>)
    requires c::equivalence(pi::context_eq(eq)),
    ensures pi::respects(pi::context_eq(eq),identity::<U>()),pi::commutes(pi::context_eq(eq),f,identity::<U>()),
{
    let ctx=pi::context_eq(eq);
    assert forall|state:IMap<Port,U>| #[trigger] pi::optional_equal(ctx,pi::compose(f,identity())(state),pi::compose(identity(),f)(state)) by {
        if f(state).is_some() {assert(ctx(f(state).unwrap(),f(state).unwrap()));}
    }
}

pub proof fn event_contract<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,owner:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,z,actor,rule),fragment_step(programs,a,z,actor,rule),
    ensures {
        let e=event(lib,programs,a,z,actor,rule,owner);let start=p::project(a.state,ISet::full());let end=p::project(z.state,ISet::full());
        &&& (e.forward)(start)==Some(end) && (e.inverse)(end).is_some()
        &&& pi::context_eq(eq)((e.inverse)(end).unwrap(),start)
        &&& pi::respects(pi::context_eq(eq),e.forward) && pi::respects(pi::context_eq(eq),e.inverse)
    },
{
    context_equivalence(eq,lib);ol::frame(eq,lib,programs,a,z,actor,rule);ol::configuration_preservation(eq,lib,programs,a,z,actor,rule);
    if g::landing(a,z,rule) {
        let id=a.current[actor].unwrap();let node=dependent(programs(actor)(id));let out=dep::run(lib,node,a.state,actor).unwrap();
        ol::run_members(eq,lib,programs,a.state,actor,id);call_contract(eq,lib,node,a.state,actor,actor==owner);
        lift::run_preservation(dep::stage(lib,node),a.state,actor);p::unique_owner(out.state);
        p::lifecycle_edit(out.state,actor,z.state.control.fibers[actor].phase,a.state.control.fibers[actor].committed,
            z.state.iterators[actor],z.state.accumulators[actor],ISet::full());
    } else {
        assert(a.state.tables==z.state.tables);assert(a.state.control.fibers.dom() =~= z.state.control.fibers.dom());
        p::unique_owner(a.state);p::unique_owner(z.state);assert(p::bindings_equal(a.state,z.state));p::projection_equal(a.state,z.state,ISet::full());
        identity_contract(eq,identity::<U>());assert(pi::context_eq(eq)(p::project(a.state,ISet::full()),p::project(a.state,ISet::full())));
    }
}

pub proof fn journal_origin<S>(es:Seq<sj::Event<S>>,at:int)
    requires 0<=at<sj::journal(es).len(),
    ensures exists|i:int| 0<=i<es.len() && es[i].own && es[i].inverse==sj::journal(es)[at],
    decreases es.len(),
{
    assert(es.len()>0);
    if es.last().own && at==0 {assert(es[es.len()-1].inverse==sj::journal(es)[at]);}
    else {
        let previous=if es.last().own {at-1} else {at};
        assert(0<=previous<sj::journal(es.drop_last()).len());assert(sj::journal(es.drop_last())[previous]==sj::journal(es)[at]);
        journal_origin(es.drop_last(),previous);
        let i=choose|i:int| 0<=i<es.drop_last().len() && es.drop_last()[i].own && es.drop_last()[i].inverse==sj::journal(es.drop_last())[previous];
        assert(es[i]==es.drop_last()[i]);
    }
}

/// Every local crossing premise comes from two actual source calls and their
/// primitive coeffect interface. No replay or restoration state is supplied.
pub proof fn pending_crossings<A,X,U,B,I,J>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize,node:dep::Node<A,X,U,B,J>,input:s::State<U>,actor:usize)
    requires og::primitive_theory(eq,lib),interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),fragment(programs,source,labels),
        inv::well_formed(input),dep::run(lib,node,input,actor).is_some(),operational(node),
        d::permitted(lib,dep::declarations(input,actor),input.control.fibers[actor].provisions,node),
    ensures {
        let word=sj::journal(events(lib,programs,source,labels,owner));let next=call_event(lib,node,input,actor,false);
        &&& sj::crosses(pi::context_eq(eq),word,next.forward) && sj::crosses(pi::context_eq(eq),word,next.inverse)
        &&& forall|i:int| 0<=i<word.len() ==> pi::stable(eq,dep::stage(lib,node),#[trigger] word[i])
    },
{
    ol::execution_preservation(eq,lib,programs,source,labels);
    let es=events(lib,programs,source,labels,owner);let word=sj::journal(es);let next=call_event(lib,node,input,actor,false);
    assert forall|at:int| 0<=at<word.len() implies pi::commutes(pi::context_eq(eq),#[trigger] word[at],next.forward)
        && pi::commutes(pi::context_eq(eq),word[at],next.inverse) && pi::stable(eq,dep::stage(lib,node),word[at]) by {
        journal_origin(es,at);
        let i=choose|i:int| 0<=i<es.len() && es[i].own && es[i].inverse==word[at];
        let a=source[i];let z=source[i+1];let who=labels[i].0;let rule=labels[i].1;
        assert(g::landing(a,z,rule));assert(who==owner);
        ol::frame(eq,lib,programs,a,z,who,rule);ol::run_members(eq,lib,programs,a.state,who,a.current[who].unwrap());
        let old=dependent(programs(who)(a.current[who].unwrap()));
        call_independence(eq,lib,old,node,a.state,input,who,actor);
    }
}

/// Derive the complete strict algebra from the real grammar fragment. The
/// theorem accepts no episode profile or whole-journal enabledness premise.
pub proof fn actual_admissible<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires og::primitive_theory(eq,lib),interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),fragment(programs,source,labels),
    ensures sj::admissible(pi::context_eq(eq),events(lib,programs,source,labels,owner),p::project(source.first().state,ISet::full())),
        sj::trace(events(lib,programs,source,labels,owner),p::project(source.first().state,ISet::full()))==Some(p::project(source.last().state,ISet::full())),
    decreases labels.len(),
{
    context_equivalence(eq,lib);
    let es=events(lib,programs,source,labels,owner);let initial=p::project(source.first().state,ISet::full());
    if labels.len()>0 {
        let prefix=source.drop_last();let previous=labels.drop_last();assert(g::execution(lib,programs,prefix,previous));assert(fragment(programs,prefix,previous));
        actual_admissible(eq,lib,programs,prefix,previous,owner);ol::execution_preservation(eq,lib,programs,source,labels);
        let a=prefix.last();let z=source.last();let actor=labels.last().0;let rule=labels.last().1;
        assert(a==source[source.len()-2]);assert(es.drop_last() =~= events(lib,programs,prefix,previous,owner));
        assert(es.last()==event(lib,programs,a,z,actor,rule,owner));
        event_contract(eq,lib,programs,a,z,actor,rule,owner);
        if !es.last().own {
            if g::landing(a,z,rule) {
                ol::frame(eq,lib,programs,a,z,actor,rule);ol::run_members(eq,lib,programs,a.state,actor,a.current[actor].unwrap());
                pending_crossings(eq,lib,programs,prefix,previous,owner,dependent(programs(actor)(a.current[actor].unwrap())),a.state,actor);
            } else {
                let word=sj::journal(es.drop_last());
                assert forall|i:int| 0<=i<word.len() implies pi::commutes(pi::context_eq(eq),#[trigger] word[i],identity::<U>()) by {identity_contract(eq,word[i]);}
            }
        }
    } else {assert(source.len()==1);assert(source.first()==source.last());}
}

pub proof fn strict_fragment_recovery<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires og::primitive_theory(eq,lib),interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),fragment(programs,source,labels),
    ensures {
        let es=events(lib,programs,source,labels,owner);let initial=p::project(source.first().state,ISet::full());let current=p::project(source.last().state,ISet::full());
        &&& sj::foreign(es,initial).is_some() && pi::run(sj::journal(es),current).is_some()
        &&& pi::context_eq(eq)(pi::run(sj::journal(es),current).unwrap(),sj::foreign(es,initial).unwrap())
    },
{
    actual_admissible(eq,lib,programs,source,labels,owner);context_equivalence(eq,lib);
    sj::recovery(pi::context_eq(eq),events(lib,programs,source,labels,owner),p::project(source.first().state,ISet::full()));
}

/// The next target callback is constructed from a real source prefix. Strict
/// restoration/domain premises are derived above, and the target returns its
/// own actual receipt. This is the induction step for a surviving execution,
/// not a claim that the flat replay already is a lifecycle execution.
pub proof fn next_foreign_call<A,X,U,B,I,J>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize,node:dep::Node<A,X,U,B,J>,target:s::State<U>,actor:usize)
    requires og::primitive_theory(eq,lib),interface(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),fragment(programs,source,labels),
        actor!=owner,inv::well_formed(target),s::registered(target,actor),target.control.fibers[actor].phase!=Phase::Inactive,
        source.last().state.control.fibers[actor]==target.control.fibers[actor],operational(node),
        d::permitted(lib,dep::declarations(source.last().state,actor),source.last().state.control.fibers[actor].provisions,node),
        dep::run(lib,node,source.last().state,actor).is_some(),
        pi::context_eq(eq)(sj::foreign(events(lib,programs,source,labels,owner),p::project(source.first().state,ISet::full())).unwrap(),p::project(target,ISet::full())),
    ensures {
        let old=dep::run(lib,node,source.last().state,actor).unwrap();let new=dep::run(lib,node,target,actor).unwrap();
        let es=events(lib,programs,source,labels,owner);let initial=p::project(source.first().state,ISet::full());
        let next=call_event(lib,node,source.last().state,actor,false);
        &&& dep::run(lib,node,target,actor).is_some() && new.next==old.next
        &&& pi::outcome(dep::stage(lib,node),p::project(source.last().state,ISet::full()))==pi::outcome(dep::stage(lib,node),p::project(target,ISet::full()))
        &&& m::partial_related(pi::context_eq(eq),lift::projected_inverse(old.receipt),lift::projected_inverse(new.receipt))
        &&& sj::foreign(es.push(next),initial).is_some()
        &&& pi::context_eq(eq)(sj::foreign(es.push(next),initial).unwrap(),p::project(new.state,ISet::full()))
    },
{
    strict_fragment_recovery(eq,lib,programs,source,labels,owner);ol::execution_preservation(eq,lib,programs,source,labels);
    context_equivalence(eq,lib);let ctx=pi::context_eq(eq);let a=source.last().state;
    let es=events(lib,programs,source,labels,owner);let initial=p::project(source.first().state,ISet::full());let word=sj::journal(es);
    pending_crossings(eq,lib,programs,source,labels,owner,node,a,actor);
    assert(ctx(pi::run(word,p::project(a,ISet::full())).unwrap(),p::project(target,ISet::full())));
    run_after_word(eq,lib,node,a,target,actor,word);
    let next=call_event(lib,node,a,actor,false);call_contract(eq,lib,node,a,actor,false);
    assert(es.push(next).drop_last() =~= es);
    lift::run_projects(dep::stage(lib,node),target,actor);
    assert((next.forward)(p::project(target,ISet::full())).is_some());
    assert((next.forward)(sj::foreign(es,initial).unwrap()).is_some());
    assert(ctx((next.forward)(sj::foreign(es,initial).unwrap()).unwrap(),(next.forward)(p::project(target,ISet::full())).unwrap()));
}

/// Even four commuting forward/inverse value generators cannot replace the
/// raw-outcome stability clause: deleting an increment changes a read result.
pub proof fn value_commutation_does_not_preserve_outcome()
    ensures {
        let eq=|a:int,b:int|a==b;
        let op=|v:int|Some(m::ValueYield {value:v+1,undo:|w:int|Some(w-1),outcome:v});
        let plus=|v:int|Some(v+1);let minus=|v:int|Some(v-1);
        &&& og::operation_admissible(eq,op)
        &&& pi::commutes(eq,plus,plus) && pi::commutes(eq,plus,minus)
        &&& pi::commutes(eq,minus,plus) && pi::commutes(eq,minus,minus)
        &&& !pi::value_stable(eq,op,minus)
        &&& op(1).unwrap().outcome!=op(minus(1).unwrap()).unwrap().outcome
    },
{
    let eq=|a:int,b:int|a==b;
    let op=|v:int|Some(m::ValueYield {value:v+1,undo:|w:int|Some(w-1),outcome:v});
    let plus=|v:int|Some(v+1);let minus=|v:int|Some(v-1);
    assert forall|a:int,b:int| #![trigger op(a),op(b)] eq(a,b) implies {
        &&& op(a).is_some()==op(b).is_some()
        &&& (op(a).is_some() ==> eq(op(a).unwrap().value,op(b).unwrap().value)
            && op(a).unwrap().outcome==op(b).unwrap().outcome && m::partial_related(eq,op(a).unwrap().undo,op(b).unwrap().undo))
    } by {assert(op(a).unwrap().undo =~= op(b).unwrap().undo);}
    assert forall|v:int| #[trigger] pi::optional_equal(eq,pi::compose(plus,minus)(v),pi::compose(minus,plus)(v)) by {}
    assert forall|v:int| #[trigger] pi::optional_equal(eq,pi::compose(minus,plus)(v),pi::compose(plus,minus)(v)) by {}
    assert forall|v:int| #[trigger] pi::optional_equal(eq,pi::compose(plus,plus)(v),pi::compose(plus,plus)(v)) by {}
    assert forall|v:int| #[trigger] pi::optional_equal(eq,pi::compose(minus,minus)(v),pi::compose(minus,minus)(v)) by {}
    if pi::value_stable(eq,op,minus) {assert(op(1).unwrap().outcome==op(minus(1).unwrap()).unwrap().outcome);}
}

} // verus!
