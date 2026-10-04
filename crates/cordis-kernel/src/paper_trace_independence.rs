//! Definition 65 as a conditional, structured semantic predicate.
//!
//! The state base is Definition 33's all-key coeffect observation, as used by
//! Definition 34, not the whole-state relation of Equation 54. A supplied total
//! primitive interpretation is explicit. This file neither constructs recursive
//! Gamma nor proves Lemma 66 for the strict partial source interpreter.
//!
//! Child payloads are read from actual primitive results and compared in the
//! SAME greatest relation as continuations. Operation support uses least reach
//! and interpreted Operation nodes, not declarations or scheduled calls. The
//! printed literal-name reading and the stronger incarnation reading are named
//! separately, including for finite and infinite execution catalogues.
#[cfg(verus_keep_ghost)]
use crate::{
    calculus as c, dependent_grammar as d, iterator_independence as ind, mediated as med,
    monoid as m, observation as o, paper_observations as po, partial_independence as pi,
};
use crate::{paper_components as pc, quotient as q};
use vstd::prelude::*;

verus! {

/// The operation-independence relation of Definitions 44/46 is an explicit
/// parameter of the compound definition. `independent(k,a,b)` must be supplied
/// with the intended operation interpretation; the compound predicate cannot
/// turn an arbitrary Boolean relation into a witnessed coeffect.
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(A)]
pub struct Coeffects<K,A> {
    pub allowed:spec_fn(K,A)->bool,
    pub independent:spec_fn(K,A,A)->bool,
}
pub open spec fn commutative_key<K,A>(coeffects:Coeffects<K,A>,key:K)->bool {
    forall|a:A,b:A|(coeffects.allowed)(key,a) && (coeffects.allowed)(key,b)
        ==> #[trigger] (coeffects.independent)(key,a,b)
}
/// Adapter for a supplied total coeffect-lift interpretation. This does not
/// extend a failed source operation by identity, or prove original partial
/// operations total. The strict adapter below retains their actual None cases.
pub open spec fn total_lift_interface<K,V,A,X,Y>(eq:spec_fn(K,V,V)->bool,ops:Operations<K,V,A,X,Y>)->Coeffects<K,A> {
    Coeffects {allowed:ops.allowed,independent:|_:K,a:A,b:A|operations_independent(eq,ops,a,b)}
}
pub proof fn total_adapter_exact<K,V,A,X,Y>(eq:spec_fn(K,V,V)->bool,ops:Operations<K,V,A,X,Y>,key:K)
    ensures commutative_key(total_lift_interface(eq,ops),key)==total_lift_commutative_key(eq,ops,key),
{
    let interface=total_lift_interface(eq,ops);
    if commutative_key(interface,key) {
        assert forall|a:A,b:A|(ops.allowed)(key,a) && (ops.allowed)(key,b)
            implies #[trigger] operations_independent(eq,ops,a,b) by {assert((interface.independent)(key,a,b));}
    }
    if total_lift_commutative_key(eq,ops,key) {
        assert forall|a:A,b:A|(interface.allowed)(key,a) && (interface.allowed)(key,b)
            implies #[trigger] (interface.independent)(key,a,b) by {assert(operations_independent(eq,ops,a,b));}
    }
}

#[verifier::reject_recursive_types(S)]
pub struct OperationYield<S,Y> {pub state:S,pub undo:spec_fn(S)->S,pub outcome:Y}
pub type LiftedOperations<K,V,A,X,Y> = spec_fn(A,X,IMap<K,V>)->OperationYield<IMap<K,V>,Y>;
/// Arguments and results can be tagged dependent carriers. `arguments(a,x)`
/// selects the fiber of a; this definition never calls a disallowed argument.
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(V)]
#[verifier::reject_recursive_types(A)]
#[verifier::reject_recursive_types(X)]
#[verifier::reject_recursive_types(Y)]
pub struct Operations<K,V,A,X,Y> {
    pub allowed:spec_fn(K,A)->bool,
    pub arguments:spec_fn(A,X)->bool,
    pub apply:LiftedOperations<K,V,A,X,Y>,
}
pub open spec fn operation_effect<K,V,A,X,Y>(ops:Operations<K,V,A,X,Y>,a:A,x:X)->q::IteratorFamily<IMap<K,V>,()> {
    |_:(),s:IMap<K,V>| {let y=(ops.apply)(a,x,s);q::Iteration {state:y.state,undo:y.undo,next:None}}
}
pub open spec fn operation_generators<K,V,A,X,Y>(ops:Operations<K,V,A,X,Y>,a:A)->ISet<spec_fn(IMap<K,V>)->IMap<K,V>> {
    ISet::new(|map:spec_fn(IMap<K,V>)->IMap<K,V>| exists|x:X| (ops.arguments)(a,x)
        && (map==ind::forward(operation_effect(ops,a,x),())
            || exists|s:IMap<K,V>| (#[trigger] (ops.apply)(a,x,s)).undo==map))
}
/// Total-lift reading of Definition 44: effect independence at every pair of arguments AND exact raw
/// outcome stability under the other operation's entire all-argument monoid.
pub open spec fn operations_independent<K,V,A,X,Y>(eq:spec_fn(K,V,V)->bool,ops:Operations<K,V,A,X,Y>,a:A,b:A)->bool {
    let base=|s:IMap<K,V>,t:IMap<K,V>|o::context_equal(eq,ISet::full(),s,t);
    &&& forall|x:X,y:X| (ops.arguments)(a,x) && (ops.arguments)(b,y)
        ==> #[trigger] ind::independent(base,operation_effect(ops,a,x),(),operation_effect(ops,b,y),())
    &&& forall|x:X,map:spec_fn(IMap<K,V>)->IMap<K,V>,s:IMap<K,V>|
        (ops.arguments)(a,x) && m::generated(operation_generators(ops,b),map)
        ==> (#[trigger] (ops.apply)(a,x,map(s))).outcome==(ops.apply)(a,x,s).outcome
    &&& forall|y:X,map:spec_fn(IMap<K,V>)->IMap<K,V>,s:IMap<K,V>|
        (ops.arguments)(b,y) && m::generated(operation_generators(ops,a),map)
        ==> (#[trigger] (ops.apply)(b,y,map(s))).outcome==(ops.apply)(b,y,s).outcome
}
pub open spec fn total_lift_commutative_key<K,V,A,X,Y>(eq:spec_fn(K,V,V)->bool,ops:Operations<K,V,A,X,Y>,key:K)->bool {
    forall|a:A,b:A| (ops.allowed)(key,a) && (ops.allowed)(key,b)
        ==> #[trigger] operations_independent(eq,ops,a,b)
}
pub proof fn commutative_self<K,V,A,X,Y>(eq:spec_fn(K,V,V)->bool,ops:Operations<K,V,A,X,Y>,key:K,a:A)
    requires total_lift_commutative_key(eq,ops,key),(ops.allowed)(key,a),
    ensures operations_independent(eq,ops,a,a),
{ }

#[verifier::reject_recursive_types(N)]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(V)]
#[verifier::reject_recursive_types(Y)]
pub enum Node<N,K,V,I,A,X,Y> {
    Unit,
    Operation {key:K,operation:A,argument:X,select:spec_fn(Y)->Option<I>},
    Provision {key:K,value:V,next:Option<I>},
    Child {component:pc::Component<K,I>,body:spec_fn(N)->Option<I>},
}
#[verifier::reject_recursive_types(G)]
pub struct ChildYield<G,N> {pub state:G,pub undo:spec_fn(G)->G,pub fresh:N}
pub type NodeInterpreter<G,N,K,V,I,A,X,Y> = spec_fn(N,I,G)->Node<N,K,V,I,A,X,Y>;
pub type OperationInterpreter<G,N,K,A,X,Y> = spec_fn(N,K,A,X,G)->OperationYield<G,Y>;
pub type ChildInterpreter<G,N,K,I> = spec_fn(N,pc::Component<K,I>,G)->ChildYield<G,N>;
#[verifier::reject_recursive_types(G)]
#[verifier::reject_recursive_types(N)]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(V)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(A)]
#[verifier::reject_recursive_types(X)]
#[verifier::reject_recursive_types(Y)]
pub struct Language<G,N,K,V,I,A,X,Y> {
    pub node:NodeInterpreter<G,N,K,V,I,A,X,Y>,
    pub operation:OperationInterpreter<G,N,K,A,X,Y>,
    pub provision:spec_fn(N,K,V,G)->q::Iteration<G,()>,
    pub child:ChildInterpreter<G,N,K,I>,
}
#[verifier::reject_recursive_types(K)]
pub enum Payload<N,K,I,A,X,Y> {
    Plain,
    Operation {key:K,operation:A,argument:X,outcome:Y},
    Child {fresh:N,component:pc::Component<K,I>},
}
#[verifier::reject_recursive_types(G)]
#[verifier::reject_recursive_types(K)]
pub struct Stage<G,N,K,I,A,X,Y> {pub state:G,pub undo:spec_fn(G)->G,pub next:Option<(N,I)>,pub payload:Payload<N,K,I,A,X,Y>}
pub open spec fn tag<N,I>(actor:N,next:Option<I>)->Option<(N,I)> {match next {Some(id)=>Some((actor,id)),None=>None}}
/// The classifier is computed by the same branch that evaluates the primitive.
/// There is no free children_agree/operation_keys predicate to supply instead.
pub open spec fn run<G,N,K,V,I,A,X,Y>(lang:Language<G,N,K,V,I,A,X,Y>,id:(N,I),input:G)->Stage<G,N,K,I,A,X,Y> {
    match (lang.node)(id.0,id.1,input) {
        Node::Unit=>Stage {state:input,undo:|s:G|s,next:None,payload:Payload::Plain},
        Node::Operation {key,operation,argument,select}=>{
            let y=(lang.operation)(id.0,key,operation,argument,input);
            Stage {state:y.state,undo:y.undo,next:tag(id.0,select(y.outcome)),
                payload:Payload::Operation {key,operation,argument,outcome:y.outcome}}
        },
        Node::Provision {key,value,next}=>{
            let y=(lang.provision)(id.0,key,value,input);
            Stage {state:y.state,undo:y.undo,next:tag(id.0,next),payload:Payload::Plain}
        },
        Node::Child {component,body}=>{
            let y=(lang.child)(id.0,component,input);
            Stage {state:y.state,undo:y.undo,next:tag(id.0,body(y.fresh)),payload:Payload::Child {fresh:y.fresh,component}}
        },
    }
}
pub open spec fn family<G,N,K,V,I,A,X,Y>(lang:Language<G,N,K,V,I,A,X,Y>)->q::IteratorFamily<G,(N,I)> {
    |id:(N,I),s:G| {let y=run(lang,id,s);q::Iteration {state:y.state,undo:y.undo,next:y.next}}
}
pub open spec fn view_denotes<G,N,K,V,I,A,X,Y>(view:po::View<G,N,K,V,I>,lang:Language<G,N,K,V,I,A,X,Y>)->bool {
    forall|n:N,id:I,s:G| #![trigger run(lang,(n,id),s)] {let y=run(lang,(n,id),s);let z=(view.families)(n)(id,s);
        &&& y.state==z.state && y.undo==z.undo
        &&& y.next==tag(n,z.next)
    }
}
/// Local descriptor provenance laws, NOT a complete Definition 52 model.
/// Component membership and the actual captured O-Retire inverse are separate.
/// Local interpretation laws. In particular the Child descriptor names the
/// actually inserted record, and Operation outcomes/inverses are the actual
/// primitive results. These laws are obligations for a supplied total model;
/// the existing strict source interpreter is NOT asserted to satisfy them.
pub open spec fn payload_provenance<G,N,K,V,I,A,X,Y>(view:po::View<G,N,K,V,I>,lang:Language<G,N,K,V,I,A,X,Y>,ops:Operations<K,V,A,X,Y>)->bool {
    forall|n:N,id:I,s:G| match (#[trigger] (lang.node)(n,id,s)) {
        Node::Unit=>true,
        Node::Operation {key,operation,argument,select:_}=>{
            let y=(lang.operation)(n,key,operation,argument,s);
            let z=(ops.apply)(operation,argument,po::project(view,s,ISet::full()));
            &&& (ops.allowed)(key,operation) && (ops.arguments)(operation,argument)
            &&& po::project(view,y.state,ISet::full())==z.state && y.outcome==z.outcome
            &&& forall|input:G| po::project(view,#[trigger] (y.undo)(input),ISet::full())
                ==(z.undo)(po::project(view,input,ISet::full()))
        },
        Node::Provision {key,value,next:_}=>{
            let y=(lang.provision)(n,key,value,s);let before=(view.registry)(s);let after=(view.registry)(y.state);
            &&& before.dom().contains(n) && !before[n].table.dom().contains(key)
            &&& after==before.insert(n,po::Fiber {table:before[n].table.insert(key,value),..before[n]})
        },
        Node::Child {component,body:_}=>{
            let y=(lang.child)(n,component,s);let before=(view.registry)(s);
            &&& !before.dom().contains(y.fresh)
            &&& (view.registry)(y.state)==before.insert(y.fresh,po::Fiber {
                component,parent:Some(n),retired:false,table:IMap::empty(),theta:po::Theta::Inactive})
        },
    }
}

pub open spec fn component_agrees<N,K,I>(relation:spec_fn((N,I),(N,I))->bool,left:N,a:pc::Component<K,I>,right:N,b:pc::Component<K,I>)->bool {
    a.dependencies==b.dependencies && a.provisions==b.provisions && relation((left,a.root),(right,b.root))
}
pub open spec fn payload_agrees<N,K,I,A,X,Y>(relation:spec_fn((N,I),(N,I))->bool,a:Payload<N,K,I,A,X,Y>,b:Payload<N,K,I,A,X,Y>)->bool {
    match (a,b) {
        (Payload::Child {fresh:left,component:a},Payload::Child {fresh:right,component:b})=>component_agrees(relation,left,a,right,b),
        (Payload::Child {..},_)|(_,Payload::Child {..})=>false,
        _=>true,
    }
}
pub open spec fn bisimulation<G,N,K,V,I,A,X,Y>(base:spec_fn(G,G)->bool,lang:Language<G,N,K,V,I,A,X,Y>,relation:spec_fn((N,I),(N,I))->bool)->bool {
    forall|i:(N,I),j:(N,I),a:G,b:G| #![trigger run(lang,i,a),run(lang,j,b)]
        relation(i,j) && base(a,b) ==> {
            let x=run(lang,i,a);let y=run(lang,j,b);
            &&& base(x.state,y.state) && o::related_maps(base,x.undo,y.undo)
            &&& q::continuation(relation,x.next,y.next)
            &&& payload_agrees(relation,x.payload,y.payload)
        }
}
pub open spec fn iterator_related<G,N,K,V,I,A,X,Y>(base:spec_fn(G,G)->bool,lang:Language<G,N,K,V,I,A,X,Y>,i:(N,I),j:(N,I))->bool {
    exists|r:spec_fn((N,I),(N,I))->bool|bisimulation(base,lang,r) && r(i,j)
}
pub proof fn greatest_bisimulation<G,N,K,V,I,A,X,Y>(base:spec_fn(G,G)->bool,lang:Language<G,N,K,V,I,A,X,Y>)
    ensures bisimulation(base,lang,|i:(N,I),j:(N,I)|iterator_related(base,lang,i,j)),
{
    let greatest=|i:(N,I),j:(N,I)|iterator_related(base,lang,i,j);
    assert forall|i:(N,I),j:(N,I),a:G,b:G| #![trigger run(lang,i,a),run(lang,j,b)]
        greatest(i,j) && base(a,b) implies {
            let x=run(lang,i,a);let y=run(lang,j,b);
            &&& base(x.state,y.state) && o::related_maps(base,x.undo,y.undo)
            &&& q::continuation(greatest,x.next,y.next)
            &&& payload_agrees(greatest,x.payload,y.payload)
        } by {
        let r=choose|r:spec_fn((N,I),(N,I))->bool|bisimulation(base,lang,r) && r(i,j);
        let x=run(lang,i,a);let y=run(lang,j,b);
        assert(q::continuation(r,x.next,y.next));
        match (x.next,y.next) {(Some(k),Some(l))=>{assert(greatest(k,l));},_=>{}}
        assert(payload_agrees(r,x.payload,y.payload));
        match (x.payload,y.payload) {
            (Payload::Child {fresh:left,component:c},Payload::Child {fresh:right,component:d})=>{
                assert(r((left,c.root),(right,d.root)));assert(greatest((left,c.root),(right,d.root)));
            },_=>{},
        }
    }
}
pub proof fn forget_payload<G,N,K,V,I,A,X,Y>(base:spec_fn(G,G)->bool,lang:Language<G,N,K,V,I,A,X,Y>,i:(N,I),j:(N,I))
    requires iterator_related(base,lang,i,j),
    ensures q::iterator_related(base,family(lang),i,j),
{
    let r=choose|r:spec_fn((N,I),(N,I))->bool|bisimulation(base,lang,r) && r(i,j);
    assert(q::bisimulation(base,family(lang),r)) by {
        assert forall|k:(N,I),l:(N,I),a:G,b:G| #![trigger family(lang)(k,a),family(lang)(l,b)]
            r(k,l) && base(a,b) implies {
                let x=family(lang)(k,a);let y=family(lang)(l,b);
                &&& base(x.state,y.state) && o::related_maps(base,x.undo,y.undo)
                &&& q::continuation(r,x.next,y.next)
            } by {assert(base(run(lang,k,a).state,run(lang,l,b).state));}
    }
}
pub open spec fn yields_related<G,N,K,V,I,A,X,Y>(base:spec_fn(G,G)->bool,lang:Language<G,N,K,V,I,A,X,Y>,a:Stage<G,N,K,I,A,X,Y>,b:Stage<G,N,K,I,A,X,Y>)->bool {
    let relation=|i:(N,I),j:(N,I)|iterator_related(base,lang,i,j);
    o::related_maps(base,a.undo,b.undo) && q::continuation(relation,a.next,b.next) && payload_agrees(relation,a.payload,b.payload)
}
pub open spec fn stable<G,N,K,V,I,A,X,Y>(base:spec_fn(G,G)->bool,lang:Language<G,N,K,V,I,A,X,Y>,id:(N,I),map:spec_fn(G)->G)->bool {
    forall|s:G| #[trigger] yields_related(base,lang,run(lang,id,map(s)),run(lang,id,s))
}
pub open spec fn independent<G,N,K,V,I,A,X,Y>(base:spec_fn(G,G)->bool,lang:Language<G,N,K,V,I,A,X,Y>,i:(N,I),j:(N,I))->bool {
    let f=family(lang);
    &&& forall|a:spec_fn(G)->G,b:spec_fn(G)->G|ind::transforms(f,i,a) && ind::transforms(f,j,b) ==> ind::commutes(base,a,b)
    &&& forall|k:(N,I),b:spec_fn(G)->G|ind::reach(f,i).contains(k) && ind::transforms(f,j,b) ==> stable(base,lang,k,b)
    &&& forall|k:(N,I),a:spec_fn(G)->G|ind::reach(f,j).contains(k) && ind::transforms(f,i,a) ==> stable(base,lang,k,a)
}
pub proof fn forget_stability<G,N,K,V,I,A,X,Y>(base:spec_fn(G,G)->bool,lang:Language<G,N,K,V,I,A,X,Y>,id:(N,I),map:spec_fn(G)->G)
    requires stable(base,lang,id,map),
    ensures ind::stable(base,family(lang),id,map),
{
    assert forall|s:G| #[trigger] ind::yields_related(base,family(lang),family(lang)(id,map(s)),family(lang)(id,s)) by {
        let a=run(lang,id,map(s));let b=run(lang,id,s);
        assert(yields_related(base,lang,a,b));
        match (a.next,b.next) {(Some(i),Some(j))=>{forget_payload(base,lang,i,j);},_=>{}}
    }
}
pub proof fn definition42_projection<G,N,K,V,I,A,X,Y>(base:spec_fn(G,G)->bool,lang:Language<G,N,K,V,I,A,X,Y>,i:(N,I),j:(N,I))
    requires independent(base,lang,i,j),
    ensures ind::independent(base,family(lang),i,family(lang),j),
{
    let f=family(lang);
    assert forall|k:(N,I),b:spec_fn(G)->G|ind::reach(f,i).contains(k) && ind::transforms(f,j,b)
        implies ind::stable(base,f,k,b) by {forget_stability(base,lang,k,b);}
    assert forall|k:(N,I),a:spec_fn(G)->G|ind::reach(f,j).contains(k) && ind::transforms(f,i,a)
        implies ind::stable(base,f,k,a) by {forget_stability(base,lang,k,a);}
}

pub open spec fn operation_keys<G,N,K,V,I,A,X,Y>(lang:Language<G,N,K,V,I,A,X,Y>,root:(N,I))->ISet<K> {
    ISet::new(|key:K|exists|id:(N,I),input:G|ind::reach(family(lang),root).contains(id)
        && match (#[trigger] run(lang,id,input)).payload {Payload::Operation {key:k,..}=>key==k,_=>false})
}
pub proof fn actual_operation_key<G,N,K,V,I,A,X,Y>(lang:Language<G,N,K,V,I,A,X,Y>,root:(N,I),id:(N,I),s:G,key:K,a:A,x:X,select:spec_fn(Y)->Option<I>)
    requires ind::reach(family(lang),root).contains(id),(lang.node)(id.0,id.1,s)==(Node::Operation {key,operation:a,argument:x,select}),
    ensures operation_keys(lang,root).contains(key),
{ assert(match run(lang,id,s).payload {Payload::Operation {key:k,..}=>k==key,_=>false}); }
pub open spec fn operation_descriptor<G,N,K,V,I,A,X,Y>(lang:Language<G,N,K,V,I,A,X,Y>,id:(N,I),s:G,key:K,a:A,x:X,select:spec_fn(Y)->Option<I>)->bool {
    (lang.node)(id.0,id.1,s)==(Node::Operation {key,operation:a,argument:x,select})
}
pub proof fn operation_provenance<G,N,K,V,I,A,X,Y>(view:po::View<G,N,K,V,I>,lang:Language<G,N,K,V,I,A,X,Y>,ops:Operations<K,V,A,X,Y>,root:(N,I),key:K)
    requires payload_provenance(view,lang,ops),operation_keys(lang,root).contains(key),
    ensures exists|id:(N,I),s:G,a:A,x:X,select:spec_fn(Y)->Option<I>|
        ind::reach(family(lang),root).contains(id) && (#[trigger] operation_descriptor(lang,id,s,key,a,x,select))
        && (ops.allowed)(key,a) && (ops.arguments)(a,x),
{
    let (id,s)=choose|id:(N,I),s:G|ind::reach(family(lang),root).contains(id)
        && match (#[trigger] run(lang,id,s)).payload {Payload::Operation {key:k,..}=>key==k,_=>false};
    match (lang.node)(id.0,id.1,s) {Node::Operation {key:k,operation:a,argument:x,select}=>{
        assert(k==key);assert((ops.allowed)(key,a));assert((ops.arguments)(a,x));assert(operation_descriptor(lang,id,s,key,a,x,select));
    },_=>{}}
}

pub open spec fn entangled<K,I>(a:pc::Component<K,I>,b:pc::Component<K,I>)->bool {
    !a.provisions.intersect(b.dependencies.union(b.provisions)).is_empty()
        || !b.provisions.intersect(a.dependencies.union(a.provisions)).is_empty()
}
#[derive(PartialEq,Eq,Structural)]
pub struct Occurrence<N> {pub time:nat,pub name:N}
pub open spec fn held<G,N,K,V,I>(view:po::View<G,N,K,V,I>,trace:po::Execution<G,N>,x:Occurrence<N>)->bool {
    po::has_state(trace,x.time) && po::registered(view,(trace.states)(x.time),x.name)
}
pub open spec fn component_at<G,N,K,V,I>(view:po::View<G,N,K,V,I>,trace:po::Execution<G,N>,x:Occurrence<N>)->pc::Component<K,I> {
    (view.registry)((trace.states)(x.time))[x.name].component
}
/// Different literal names, or two occurrences of a reused name separated by
/// an absent registry record. No name-allocation uniqueness is assumed.
pub open spec fn distinct_incarnations<G,N,K,V,I>(view:po::View<G,N,K,V,I>,trace:po::Execution<G,N>,a:Occurrence<N>,b:Occurrence<N>)->bool {
    a.name!=b.name || exists|t:nat| (a.time<t<b.time || b.time<t<a.time)
        && !(#[trigger] po::registered(view,(trace.states)(t),a.name))
}
pub open spec fn pair_condition<G,N,K,V,I,A,X,Y>(eq:spec_fn(K,V,V)->bool,view:po::View<G,N,K,V,I>,lang:Language<G,N,K,V,I,A,X,Y>,coeffects:Coeffects<K,A>,trace:po::Execution<G,N>,a:Occurrence<N>,b:Occurrence<N>)->bool {
    let left=component_at(view,trace,a);let right=component_at(view,trace,b);
    let i=(a.name,left.root);let j=(b.name,right.root);let base=|s:G,t:G|po::observed(eq,view,s,t);
    independent(base,lang,i,j) || (entangled(left,right) &&
        forall|k:K|operation_keys(lang,i).contains(k) && operation_keys(lang,j).contains(k) ==> commutative_key(coeffects,k))
}
/// The printed literal m != n reading, over EVERY historically held record,
/// including internally instantiated children and later removed records.
pub open spec fn pairwise<G,N,K,V,I,A,X,Y>(eq:spec_fn(K,V,V)->bool,view:po::View<G,N,K,V,I>,lang:Language<G,N,K,V,I,A,X,Y>,coeffects:Coeffects<K,A>,trace:po::Execution<G,N>)->bool {
    view_denotes(view,lang) && forall|a:Occurrence<N>,b:Occurrence<N>|held(view,trace,a) && held(view,trace,b) && a.name!=b.name
        ==> #[trigger] pair_condition(eq,view,lang,coeffects,trace,a,b)
}
pub open spec fn pairwise_birth_distinct<G,N,K,V,I,A,X,Y>(eq:spec_fn(K,V,V)->bool,view:po::View<G,N,K,V,I>,lang:Language<G,N,K,V,I,A,X,Y>,coeffects:Coeffects<K,A>,trace:po::Execution<G,N>)->bool {
    view_denotes(view,lang) && forall|a:Occurrence<N>,b:Occurrence<N>|held(view,trace,a) && held(view,trace,b) && distinct_incarnations(view,trace,a,b)
        ==> #[trigger] pair_condition(eq,view,lang,coeffects,trace,a,b)
}
/// Interpretation fidelity is kept separate from the compound independence
/// property. Neither entails that the given catalogue is a legal execution.
pub open spec fn total_lift_interpreted_pairwise<G,N,K,V,I,A,X,Y>(eq:spec_fn(K,V,V)->bool,view:po::View<G,N,K,V,I>,lang:Language<G,N,K,V,I,A,X,Y>,ops:Operations<K,V,A,X,Y>,trace:po::Execution<G,N>)->bool {
    view_denotes(view,lang) && payload_provenance(view,lang,ops) && pairwise(eq,view,lang,total_lift_interface(eq,ops),trace)
}
pub proof fn birth_reading_implies_literal<G,N,K,V,I,A,X,Y>(eq:spec_fn(K,V,V)->bool,view:po::View<G,N,K,V,I>,lang:Language<G,N,K,V,I,A,X,Y>,coeffects:Coeffects<K,A>,trace:po::Execution<G,N>)
    requires pairwise_birth_distinct(eq,view,lang,coeffects,trace),
    ensures pairwise(eq,view,lang,coeffects,trace),
{ }
pub proof fn pairwise_cases<G,N,K,V,I,A,X,Y>(eq:spec_fn(K,V,V)->bool,view:po::View<G,N,K,V,I>,lang:Language<G,N,K,V,I,A,X,Y>,coeffects:Coeffects<K,A>,trace:po::Execution<G,N>,a:Occurrence<N>,b:Occurrence<N>)
    requires pairwise(eq,view,lang,coeffects,trace),held(view,trace,a),held(view,trace,b),a.name!=b.name,
    ensures pair_condition(eq,view,lang,coeffects,trace,a,b),
{ }
pub proof fn nonentangled_case<G,N,K,V,I,A,X,Y>(eq:spec_fn(K,V,V)->bool,view:po::View<G,N,K,V,I>,lang:Language<G,N,K,V,I,A,X,Y>,coeffects:Coeffects<K,A>,trace:po::Execution<G,N>,a:Occurrence<N>,b:Occurrence<N>)
    requires pairwise(eq,view,lang,coeffects,trace),held(view,trace,a),held(view,trace,b),a.name!=b.name,
        !entangled(component_at(view,trace,a),component_at(view,trace,b)),
    ensures independent(|s:G,t:G|po::observed(eq,view,s,t),lang,(a.name,component_at(view,trace,a).root),(b.name,component_at(view,trace,b).root)),
{ pairwise_cases(eq,view,lang,coeffects,trace,a,b); }


pub proof fn entangled_shared_key_case<G,N,K,V,I,A,X,Y>(eq:spec_fn(K,V,V)->bool,view:po::View<G,N,K,V,I>,lang:Language<G,N,K,V,I,A,X,Y>,coeffects:Coeffects<K,A>,trace:po::Execution<G,N>,a:Occurrence<N>,b:Occurrence<N>,key:K)
    requires pairwise(eq,view,lang,coeffects,trace),held(view,trace,a),held(view,trace,b),a.name!=b.name,
        !independent(|s:G,t:G|po::observed(eq,view,s,t),lang,(a.name,component_at(view,trace,a).root),(b.name,component_at(view,trace,b).root)),
        operation_keys(lang,(a.name,component_at(view,trace,a).root)).contains(key),
        operation_keys(lang,(b.name,component_at(view,trace,b).root)).contains(key),
    ensures entangled(component_at(view,trace,a),component_at(view,trace,b)),commutative_key(coeffects,key),
{ pairwise_cases(eq,view,lang,coeffects,trace,a,b); }

/// Agreement really exposes declaration equality and the semantic root relation
/// under each actual fresh actor; it does not require equal allocated names.
pub proof fn child_payload_contract<G,N,K,V,I,A,X,Y>(base:spec_fn(G,G)->bool,lang:Language<G,N,K,V,I,A,X,Y>,a:Stage<G,N,K,I,A,X,Y>,b:Stage<G,N,K,I,A,X,Y>,left:N,right:N,lc:pc::Component<K,I>,rc:pc::Component<K,I>)
    requires yields_related(base,lang,a,b),a.payload==(Payload::Child {fresh:left,component:lc}),b.payload==(Payload::Child {fresh:right,component:rc}),
    ensures lc.dependencies==rc.dependencies,lc.provisions==rc.provisions,
        iterator_related(base,lang,(left,lc.root),(right,rc.root)),
{ }
pub open spec fn no_children<G,N,K,V,I,A,X,Y>(lang:Language<G,N,K,V,I,A,X,Y>)->bool {
    forall|id:(N,I),s:G| match (#[trigger] run(lang,id,s)).payload {Payload::Child {..}=>false,_=>true}
}
pub proof fn ordinary_bisimulation_lifts<G,N,K,V,I,A,X,Y>(base:spec_fn(G,G)->bool,lang:Language<G,N,K,V,I,A,X,Y>,i:(N,I),j:(N,I))
    requires no_children(lang),q::iterator_related(base,family(lang),i,j),
    ensures iterator_related(base,lang,i,j),
{
    let r=choose|r:spec_fn((N,I),(N,I))->bool|q::bisimulation(base,family(lang),r) && r(i,j);
    assert(bisimulation(base,lang,r)) by {
        assert forall|k:(N,I),l:(N,I),a:G,b:G| #![trigger run(lang,k,a),run(lang,l,b)]
            r(k,l) && base(a,b) implies {
                let x=run(lang,k,a);let y=run(lang,l,b);
                &&& base(x.state,y.state) && o::related_maps(base,x.undo,y.undo)
                &&& q::continuation(r,x.next,y.next) && payload_agrees(r,x.payload,y.payload)
            } by {assert(base(family(lang)(k,a).state,family(lang)(l,b).state));}
    }
}
pub proof fn ordinary_stability_lifts<G,N,K,V,I,A,X,Y>(base:spec_fn(G,G)->bool,lang:Language<G,N,K,V,I,A,X,Y>,id:(N,I),map:spec_fn(G)->G)
    requires no_children(lang),ind::stable(base,family(lang),id,map),
    ensures stable(base,lang,id,map),
{
    assert forall|s:G| #[trigger] yields_related(base,lang,run(lang,id,map(s)),run(lang,id,s)) by {
        let a=run(lang,id,map(s));let b=run(lang,id,s);
        assert(ind::yields_related(base,family(lang),family(lang)(id,map(s)),family(lang)(id,s)));
        match (a.next,b.next) {(Some(i),Some(j))=>{ordinary_bisimulation_lifts(base,lang,i,j);},_=>{}}
    }
}
/// Without instantiation this definition is EXACTLY the existing Definition 42,
/// including both transformation monoids and both stability directions.
pub proof fn ordinary_independence_equivalence<G,N,K,V,I,A,X,Y>(base:spec_fn(G,G)->bool,lang:Language<G,N,K,V,I,A,X,Y>,i:(N,I),j:(N,I))
    requires no_children(lang),
    ensures independent(base,lang,i,j)==ind::independent(base,family(lang),i,family(lang),j),
{
    if independent(base,lang,i,j) {definition42_projection(base,lang,i,j);}
    if ind::independent(base,family(lang),i,family(lang),j) {
        assert forall|k:(N,I),b:spec_fn(G)->G|ind::reach(family(lang),i).contains(k) && ind::transforms(family(lang),j,b)
            implies stable(base,lang,k,b) by {ordinary_stability_lifts(base,lang,k,b);}
        assert forall|k:(N,I),a:spec_fn(G)->G|ind::reach(family(lang),j).contains(k) && ind::transforms(family(lang),i,a)
            implies stable(base,lang,k,a) by {ordinary_stability_lifts(base,lang,k,a);}
    }
}

pub open spec fn unit_language<G,N,K,V,I>()->Language<G,N,K,V,I,(),(),()> {
    Language {node:|_:N,_:I,_:G|Node::Unit,
        operation:|_:N,_:K,_:(),_:(),s:G|OperationYield {state:s,undo:|t:G|t,outcome:()},
        provision:|_:N,_:K,_:V,s:G|q::Iteration {state:s,undo:|t:G|t,next:None},
        child:|n:N,_:pc::Component<K,I>,s:G|ChildYield {state:s,undo:|t:G|t,fresh:n}}
}
pub proof fn identity_word<G>(word:Seq<spec_fn(G)->G>,input:G)
    requires forall|i:int|0<=i<word.len() ==> #[trigger] word[i]==(|s:G|s),
    ensures c::run(word,input)==input,
    decreases word.len(),
{
    if word.len()>0 {identity_word(word.drop_last(),input);assert(word.last()==(|s:G|s));}
}
pub proof fn unit_transform<G,N,K,V,I>(root:(N,I),map:spec_fn(G)->G)
    requires ind::transforms(family(unit_language::<G,N,K,V,I>()),root,map),
    ensures map==(|s:G|s),
{
    let lang=unit_language::<G,N,K,V,I>();let generators=ind::generators(family(lang),root);
    assert forall|g:spec_fn(G)->G|generators.contains(g) implies g==(|s:G|s) by {
        let id=choose|id:(N,I)|ind::reach(family(lang),root).contains(id)
            && (g==ind::forward(family(lang),id) || exists|input:G| (#[trigger] family(lang)(id,input)).undo==g);
        assert(ind::forward(family(lang),id) =~= (|s:G|s));
    }
    let word=choose|word:Seq<spec_fn(G)->G>|m::represents(generators,word,map);
    assert forall|s:G| #[trigger] map(s)==s by {identity_word(word,s);}
    assert(map =~= (|s:G|s));
}
pub proof fn unit_independent<G,N,K,V,I>(base:spec_fn(G,G)->bool,left:(N,I),right:(N,I))
    ensures independent(base,unit_language::<G,N,K,V,I>(),left,right),
{
    let lang=unit_language::<G,N,K,V,I>();let f=family(lang);
    assert forall|a:spec_fn(G)->G,b:spec_fn(G)->G|ind::transforms(f,left,a) && ind::transforms(f,right,b)
        implies ind::commutes(base,a,b) by {unit_transform::<G,N,K,V,I>(left,a);unit_transform::<G,N,K,V,I>(right,b);}
    assert forall|id:(N,I),map:spec_fn(G)->G| #[trigger] stable(base,lang,id,map) by { }
}
pub proof fn unit_pairwise<G,N,K,V,I>(eq:spec_fn(K,V,V)->bool,view:po::View<G,N,K,V,I>,coeffects:Coeffects<K,()>,trace:po::Execution<G,N>)
    requires view_denotes(view,unit_language::<G,N,K,V,I>()),
    ensures pairwise(eq,view,unit_language::<G,N,K,V,I>(),coeffects,trace),
        pairwise_birth_distinct(eq,view,unit_language::<G,N,K,V,I>(),coeffects,trace),
{
    assert forall|a:Occurrence<N>,b:Occurrence<N>| #[trigger] pair_condition(eq,view,unit_language(),coeffects,trace,a,b) by {
        unit_independent::<G,N,K,V,I>(|s:G,t:G|po::observed(eq,view,s,t),(a.name,component_at(view,trace,a).root),(b.name,component_at(view,trace,b).root));
    }
}

/// An actual external-rule trace demonstrates the nonempty same-component case
/// and a removed/reused literal name with two different historical declarations.
pub open spec fn unit_model()->crate::semantics::Model<int> {
    crate::semantics::Model {iterate:|_:usize,_:nat,s:crate::semantics::State<int>|crate::semantics::Yield {state:s,inverse:0,next:None},undo:|_:nat,s:crate::semantics::State<int>|s}
}
pub open spec fn example_insert(s:crate::semantics::State<int>,n:usize,d:ISet<crate::Port>)->crate::semantics::State<int> {
    crate::semantics::extend_child(s,crate::global::insert_fiber(s.control,n,None,d,ISet::empty()),n,0)
}
pub proof fn example_insert_step(a:crate::semantics::State<int>,n:usize,deps:ISet<crate::Port>)
    requires crate::semantics::shaped(a),!crate::semantics::registered(a,n),
    ensures crate::semantics::step(unit_model(),a,example_insert(a,n,deps),n,crate::refinement::Rule::Insert),
        crate::semantics::shaped(example_insert(a,n,deps)),
{
    use crate::{semantics as s,refinement as r};let z=example_insert(a,n,deps);
    assert(r::frame(a.control,z.control,n));
    assert(s::shaped(z)) by {
        assert forall|actor:usize|s::registered(z,actor) implies {
            &&& z.tables[actor].dom().subset_of(z.control.fibers[actor].provisions)
            &&& (z.control.fibers[actor].phase==crate::Phase::Inactive ==> z.iterators[actor].is_none() && z.accumulators[actor].len()==0 && z.control.fibers[actor].committed.is_empty())
            &&& (z.control.fibers[actor].phase==crate::Phase::Loading ==> z.iterators[actor].is_some())
            &&& (z.control.fibers[actor].phase==crate::Phase::Active || z.control.fibers[actor].phase==crate::Phase::Unloading ==> z.iterators[actor].is_none())
        } by {if actor!=n {assert(s::registered(a,actor));}}
    }
}
pub open spec fn reuse_states()->Seq<crate::semantics::State<int>> {
    let a0=crate::semantics::empty_state();let a1=example_insert(a0,0,ISet::empty());let a2=example_insert(a1,1,ISet::empty());
    let a3=crate::semantics::with_control(a2,crate::global::retire_fiber(a2.control,1));let a4=crate::semantics::erase(a3,1);
    let a5=example_insert(a4,1,ISet::empty().insert(crate::Port {key:7,realm:0}));seq![a0,a1,a2,a3,a4,a5]
}
pub open spec fn reuse_labels()->Seq<(usize,crate::refinement::Rule)> {
    use crate::refinement::Rule;seq![(0usize,Rule::Insert),(1usize,Rule::Insert),(1usize,Rule::Retire),(1usize,Rule::Remove),(1usize,Rule::Insert)]
}
pub open spec fn unused_operations<K,V>()->Operations<K,V,(),(),()> {
    Operations {allowed:|_:K,_:()|false,arguments:|_:(),_:()|true,
        apply:|_:(),_:(),s:IMap<K,V>|OperationYield {state:s,undo:|t:IMap<K,V>|t,outcome:()}}
}
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn nonempty_unit_and_reused_name()
    ensures crate::semantics::execution(unit_model(),reuse_states(),reuse_labels()),
        reuse_states().first()==crate::semantics::empty_state::<int>(),
        total_lift_interpreted_pairwise(|_:crate::Port,a:int,b:int|a==b,po::from_model(unit_model()),unit_language(),unused_operations(),po::finite_execution(reuse_states(),reuse_labels())),
        held(po::from_model(unit_model()),po::finite_execution(reuse_states(),reuse_labels()),Occurrence {time:2,name:0usize}),
        held(po::from_model(unit_model()),po::finite_execution(reuse_states(),reuse_labels()),Occurrence {time:2,name:1usize}),
        component_at(po::from_model(unit_model()),po::finite_execution(reuse_states(),reuse_labels()),Occurrence {time:2,name:0usize})
            ==component_at(po::from_model(unit_model()),po::finite_execution(reuse_states(),reuse_labels()),Occurrence {time:2,name:1usize}),
        held(po::from_model(unit_model()),po::finite_execution(reuse_states(),reuse_labels()),Occurrence {time:5,name:1usize}),
        distinct_incarnations(po::from_model(unit_model()),po::finite_execution(reuse_states(),reuse_labels()),Occurrence {time:2,name:1usize},Occurrence {time:5,name:1usize}),
        component_at(po::from_model(unit_model()),po::finite_execution(reuse_states(),reuse_labels()),Occurrence {time:2,name:1usize}).dependencies
            !=component_at(po::from_model(unit_model()),po::finite_execution(reuse_states(),reuse_labels()),Occurrence {time:5,name:1usize}).dependencies,
{
    use crate::{semantics as s,refinement as r};let states=reuse_states();let labels=reuse_labels();

    example_insert_step(states[0],0,ISet::empty());
    example_insert_step(states[1],1,ISet::empty());
    assert(s::step(unit_model(),states[2],states[3],1,r::Rule::Retire));
    assert(s::step(unit_model(),states[3],states[4],1,r::Rule::Remove));
    assert(states[4].control.fibers =~= states[1].control.fibers);
    assert(states[4].tables =~= states[1].tables);assert(states[4].effects =~= states[1].effects);
    assert(states[4].iterators =~= states[1].iterators);assert(states[4].accumulators =~= states[1].accumulators);
    assert(states[4]==states[1]);
    example_insert_step(states[4],1,ISet::empty().insert(crate::Port {key:7,realm:0}));
    assert forall|i:int|0<=i<labels.len() implies s::step(unit_model(),states[i],states[i+1],labels[i].0,labels[i].1) by {
        if i==0 {}else if i==1 {}else if i==2 {}else if i==3 {}else {assert(i==4);}
    }
    let view=po::from_model(unit_model());let trace=po::finite_execution(states,labels);let lang=unit_language();
    assert(view_denotes(view,lang)) by {
        assert forall|n:usize,id:nat,s:s::State<int>| #![trigger run(lang,(n,id),s)] {let y=run(lang,(n,id),s);let z=(view.families)(n)(id,s);
            &&& y.state==z.state && y.undo==z.undo && y.next==tag(n,z.next)
        } by {assert(run(lang,(n,id),s).undo =~= (view.families)(n)(id,s).undo);}
    }
    unit_pairwise(|_:crate::Port,a:int,b:int|a==b,view,total_lift_interface(|_:crate::Port,a:int,b:int|a==b,unused_operations()),trace);
    assert(!po::registered(view,(trace.states)(4),1usize));
    let key=crate::Port {key:7,realm:0};
    assert(!ISet::<crate::Port>::empty().contains(key));assert(ISet::empty().insert(key).contains(key));
    assert(ISet::<crate::Port>::empty()!=ISet::empty().insert(key));
}
/// Actual mixed Child landing is present in the catalogue even though there is
/// NO external Insert of name 1 anywhere in this source trace. Only catalogue
/// extraction is claimed: this does not identify the strict Child interpreter
/// with the arbitrary total Model supplied to the observation adapter.
#[verifier::spinoff_prover]
pub proof fn internal_child_is_catalogued(model:crate::semantics::Model<u64>)
    ensures crate::mixed_grammar::execution(crate::mixed_examples::library(),crate::mixed_examples::programs(),crate::mixed_examples::trace(),crate::mixed_examples::labels()),
        held(po::from_model(model),po::finite_execution(crate::mixed_grammar::states(crate::mixed_examples::trace()),crate::mixed_examples::labels()),Occurrence {time:3,name:1usize}),
        forall|i:int|0<=i<crate::mixed_examples::labels().len() ==> #[trigger] crate::mixed_examples::labels()[i]!=(1usize,crate::refinement::Rule::Insert),
{
    use crate::mixed_examples as ex;ex::actual_execution();reveal(ex::trace);
    assert forall|i:int|0<=i<ex::labels().len() implies #[trigger] ex::labels()[i]!=(1usize,crate::refinement::Rule::Insert) by {
        if i==0 {}else if i==1 {}else if i==2 {}else if i==3 {}else if i==4 {}else if i==5 {}else if i==6 {}else if i==7 {}else {assert(i==8);}
    }
}



/// When the supplied primitive interpretation is faithful, the coinductive
/// Child clause compares the ACTUAL inserted registry records and their roots.
pub proof fn child_agreement_names_actual_components<G,N,K,V,I,A,X,Y>(base:spec_fn(G,G)->bool,
    view:po::View<G,N,K,V,I>,lang:Language<G,N,K,V,I,A,X,Y>,ops:Operations<K,V,A,X,Y>,
    i:(N,I),j:(N,I),a:G,b:G,left:N,right:N,lc:pc::Component<K,I>,rc:pc::Component<K,I>)
    requires payload_provenance(view,lang,ops),iterator_related(base,lang,i,j),base(a,b),
        run(lang,i,a).payload==(Payload::Child {fresh:left,component:lc}),
        run(lang,j,b).payload==(Payload::Child {fresh:right,component:rc}),
    ensures po::registered(view,run(lang,i,a).state,left),po::registered(view,run(lang,j,b).state,right),
        (view.registry)(run(lang,i,a).state)[left].component==lc,
        (view.registry)(run(lang,j,b).state)[right].component==rc,
        lc.dependencies==rc.dependencies,lc.provisions==rc.provisions,
        iterator_related(base,lang,(left,lc.root),(right,rc.root)),
{
    greatest_bisimulation(base,lang);
    let x=run(lang,i,a);let y=run(lang,j,b);
    assert(payload_agrees(|u:(N,I),v:(N,I)|iterator_related(base,lang,u,v),x.payload,y.payload));
    match (lang.node)(i.0,i.1,a) {Node::Child {component,body:_}=>{
        let z=(lang.child)(i.0,component,a);assert(z.fresh==left);assert(component==lc);
        assert((view.registry)(z.state).dom().contains(left));
    },_=>{}}
    match (lang.node)(j.0,j.1,b) {Node::Child {component,body:_}=>{
        let z=(lang.child)(j.0,component,b);assert(z.fresh==right);assert(component==rc);
        assert((view.registry)(z.state).dom().contains(right));
    },_=>{}}
}

pub open spec fn key_equivalent<K,V>(eq:spec_fn(K,V,V)->bool,key:K)->bool {c::equivalence(|a:V,b:V|eq(key,a,b))}
pub proof fn unit_is_full_component<G,K,V,I>(eq:spec_fn(K,V,V)->bool,coeffects:spec_fn(G)->IMap<K,V>,component:pc::Component<K,I>)
    requires forall|key:K| #[trigger] key_equivalent(eq,key),
    ensures pc::component(eq,coeffects,pc::unit::<G,I>(),|_:I,_:G|ISet::empty(),component),
{
    let keys=component.dependencies.union(component.provisions);
    assert forall|key:K|keys.contains(key) implies c::equivalence(|a:V,b:V|eq(key,a,b)) by {assert(key_equivalent(eq,key));}
    o::context_equivalence(eq,keys);
    let table=|a:IMap<K,V>,b:IMap<K,V>|o::context_equal(eq,keys,a,b);assert(c::equivalence(table));
    let base=|a:G,b:G|pc::observed(eq,coeffects,keys,a,b);
    assert forall|a:G| #[trigger] base(a,a) by {assert(table(coeffects(a),coeffects(a)));}
    pc::unit_witnessed(base,component.root);
}

/// Both distinct names in the actual Unit example carry genuine full-carrier
/// witnessed Components. This fact is not inferred from a successful step.
pub proof fn example_components_are_witnessed()
    ensures forall|time:nat,n:usize|held(po::from_model(unit_model()),po::finite_execution(reuse_states(),reuse_labels()),Occurrence {time,name:n})
        ==> pc::component(|_:crate::Port,a:int,b:int|a==b,
            |a:crate::semantics::State<int>|po::project(po::from_model(unit_model()),a,ISet::full()),
            (po::from_model(unit_model()).families)(n),|_:nat,_:crate::semantics::State<int>|ISet::empty(),
            component_at(po::from_model(unit_model()),po::finite_execution(reuse_states(),reuse_labels()),Occurrence {time,name:n})),
{
    use crate::{semantics as s,Port};let view=po::from_model(unit_model());let trace=po::finite_execution(reuse_states(),reuse_labels());
    assert forall|time:nat,n:usize|held(view,trace,Occurrence {time,name:n})
        implies pc::component(|_:Port,a:int,b:int|a==b,|a:s::State<int>|po::project(view,a,ISet::full()),
            (view.families)(n),|_:nat,_:s::State<int>|ISet::empty(),component_at(view,trace,Occurrence {time,name:n})) by {
        let left=(view.families)(n);let right=pc::unit::<s::State<int>,nat>();
        assert forall|id:nat,a:s::State<int>| #[trigger] left(id,a)==right(id,a) by {
            assert(left(id,a).undo =~= right(id,a).undo);
        }
        assert(left =~= right);
        unit_is_full_component(|_:Port,a:int,b:int|a==b,|a:s::State<int>|po::project(view,a,ISet::full()),component_at(view,trace,Occurrence {time,name:n}));
    }
}



/// A nonempty operation interface, with two operation names and EVERY integer
/// argument. Raw outcomes differ across arguments; every actual map is identity.
pub open spec fn reporting_operations()->Operations<bool,int,bool,int,int> {
    Operations {allowed:|key:bool,_:bool|!key,arguments:|_:bool,_:int|true,
        apply:|_:bool,arg:int,s:IMap<bool,int>|OperationYield {state:s,undo:|t:IMap<bool,int>|t,outcome:arg}}
}
pub proof fn raw_unit_transform<G>(map:spec_fn(G)->G)
    requires ind::transforms(pc::unit::<G,()>(),(),map),
    ensures map==(|s:G|s),
{
    let family=pc::unit::<G,()>();let generators=ind::generators(family,());
    assert forall|g:spec_fn(G)->G|generators.contains(g) implies g==(|s:G|s) by {
        assert(ind::forward(family,()) =~= (|s:G|s));
    }
    let word=choose|word:Seq<spec_fn(G)->G>|m::represents(generators,word,map);
    assert forall|s:G| #[trigger] map(s)==s by {identity_word(word,s);}
    assert(map =~= (|s:G|s));
}
pub proof fn raw_unit_independent<G>(base:spec_fn(G,G)->bool)
    ensures ind::independent(base,pc::unit::<G,()>(),(),pc::unit::<G,()>(),()),
{
    let family=pc::unit::<G,()>();
    assert forall|a:spec_fn(G)->G,b:spec_fn(G)->G|ind::transforms(family,(),a) && ind::transforms(family,(),b)
        implies ind::commutes(base,a,b) by {raw_unit_transform(a);raw_unit_transform(b);}
    assert forall|id:(),map:spec_fn(G)->G| #[trigger] ind::stable(base,family,id,map) by { }
}
pub proof fn nonempty_commutative_interface()
    ensures total_lift_commutative_key(|_:bool,a:int,b:int|a==b,reporting_operations(),false),
        (reporting_operations().allowed)(false,false),(reporting_operations().allowed)(false,true),
        (reporting_operations().arguments)(false,7),(reporting_operations().arguments)(true,9),
        (reporting_operations().apply)(false,7,IMap::empty().insert(false,42)).outcome==7,
        (reporting_operations().apply)(true,9,IMap::empty().insert(false,42)).outcome==9,
{
    let ops=reporting_operations();let eq=|_:bool,a:int,b:int|a==b;
    let base=|s:IMap<bool,int>,t:IMap<bool,int>|o::context_equal(eq,ISet::full(),s,t);
    raw_unit_independent(base);
    assert forall|a:bool,b:bool| (ops.allowed)(false,a) && (ops.allowed)(false,b)
        implies #[trigger] operations_independent(eq,ops,a,b) by {
        assert forall|x:int,y:int| (ops.arguments)(a,x) && (ops.arguments)(b,y)
            implies #[trigger] ind::independent(base,operation_effect(ops,a,x),(),operation_effect(ops,b,y),()) by {
            assert(operation_effect(ops,a,x) =~= pc::unit::<IMap<bool,int>,()>());
            assert(operation_effect(ops,b,y) =~= pc::unit::<IMap<bool,int>,()>());
        }
    }
}



/// Strict source adapter: every generator is the real partial forward map or
/// an inverse returned on a successful call. No failure is completed by identity.
pub open spec fn strict_generators<K,A,X,V,Y>(lib:d::Library<K,A,X,V,Y>,a:A)->ISet<med::PartialMap<V>> {
    ISet::new(|map:med::PartialMap<V>|exists|x:X|(lib.arguments)(a,x)
        && #[trigger] pi::value_generators((lib.apply)(a,x)).contains(map))
}
pub open spec fn strict_operations_independent<K,A,X,V,Y>(eq:spec_fn(V,V)->bool,lib:d::Library<K,A,X,V,Y>,a:A,b:A)->bool {
    let left=strict_generators(lib,a);let right=strict_generators(lib,b);
    &&& forall|f:med::PartialMap<V>,g:med::PartialMap<V>|pi::generated(left,f) && pi::generated(right,g) ==> #[trigger] pi::commutes(eq,f,g)
    &&& forall|x:X,g:med::PartialMap<V>|(lib.arguments)(a,x) && pi::generated(right,g) ==> #[trigger] pi::value_stable(eq,(lib.apply)(a,x),g)
    &&& forall|x:X,f:med::PartialMap<V>|(lib.arguments)(b,x) && pi::generated(left,f) ==> #[trigger] pi::value_stable(eq,(lib.apply)(b,x),f)
}
/// A second, explicitly strict reading of 44, plugged into the SAME compound
/// predicate. Its input is the existing key/argument-indexed source library;
/// this adapter does not assert that Language's total G maps realize that library.
pub open spec fn strict_interface<K,A,X,V,Y>(eq:spec_fn(K,V,V)->bool,lib:d::Library<K,A,X,V,Y>)->Coeffects<K,A> {
    Coeffects {allowed:|key:K,a:A|lib.allowed.contains(a) && (lib.key)(a)==key,
        independent:|key:K,a:A,b:A|strict_operations_independent(|u:V,v:V|eq(key,u,v),lib,a,b)}
}
pub proof fn strict_value_stable_word<V,Y>(eq:spec_fn(V,V)->bool,op:med::Operation<V,Y>,word:Seq<med::PartialMap<V>>)
    requires c::equivalence(eq),
        forall|v:V| #[trigger] op(v).is_some() ==> med::partial_related(eq,op(v).unwrap().undo,op(v).unwrap().undo),
        forall|i:int|0<=i<word.len() ==> pi::value_stable(eq,op,#[trigger] word[i]),
    ensures pi::value_stable(eq,op,|s:V|pi::run(word,s)),
    decreases word.len(),
{
    if word.len()>0 {strict_value_stable_word(eq,op,word.drop_last());}
    assert forall|v:V| #[trigger] pi::run(word,v).is_some() implies {
        let a=op(v);let b=op(pi::run(word,v).unwrap());
        &&& a.is_some()==b.is_some()
        &&& a.is_some() ==> a.unwrap().outcome==b.unwrap().outcome && med::partial_related(eq,a.unwrap().undo,b.unwrap().undo)
    } by {
        if word.len()>0 {
            let previous=|s:V|pi::run(word.drop_last(),s);let middle=previous(v).unwrap();
            assert(pi::value_stable(eq,op,previous));assert(previous(v).is_some());
            assert(pi::run(word.drop_last(),v).is_some());assert((word.last())(middle).is_some());
            assert(pi::value_stable(eq,op,word.last()));
            assert(op(v).is_some()==op(middle).is_some());
            assert(op(middle).is_some()==op(pi::run(word,v).unwrap()).is_some());
            if op(v).is_some() {pi::partial_relation_transitive(eq,op(v).unwrap().undo,op(middle).unwrap().undo,op(pi::run(word,v).unwrap()).unwrap().undo);}
        }
    }
}
/// Existing generator-form value_independent contracts, over ALL argument
/// pairs, imply the full two monoids and both raw outcome/inverse word clauses.
pub proof fn strict_basis_full<K,A,X,V,Y>(eq:spec_fn(V,V)->bool,lib:d::Library<K,A,X,V,Y>,a:A,b:A)
    requires c::equivalence(eq),
        forall|x:X,y:X|(lib.arguments)(a,x) && (lib.arguments)(b,y) ==> #[trigger] pi::value_independent(eq,(lib.apply)(a,x),(lib.apply)(b,y)),
        forall|map:med::PartialMap<V>|strict_generators(lib,a).contains(map) || strict_generators(lib,b).contains(map) ==> #[trigger] pi::respects(eq,map),
    ensures strict_operations_independent(eq,lib,a,b),
{
    let left=strict_generators(lib,a);let right=strict_generators(lib,b);
    assert forall|f:med::PartialMap<V>,g:med::PartialMap<V>|left.contains(f) && right.contains(g) implies #[trigger] pi::commutes(eq,f,g) by {
        let x=choose|x:X|(lib.arguments)(a,x) && #[trigger] pi::value_generators((lib.apply)(a,x)).contains(f);
        let y=choose|y:X|(lib.arguments)(b,y) && #[trigger] pi::value_generators((lib.apply)(b,y)).contains(g);
        assert(pi::value_independent(eq,(lib.apply)(a,x),(lib.apply)(b,y)));
    }
    assert forall|f:med::PartialMap<V>,g:med::PartialMap<V>|pi::generated(left,f) && pi::generated(right,g) implies #[trigger] pi::commutes(eq,f,g) by {
        pi::generated_commutation(eq,left,right,f,g);
    }
    assert forall|x:X,g:med::PartialMap<V>|(lib.arguments)(a,x) && pi::generated(right,g) implies #[trigger] pi::value_stable(eq,(lib.apply)(a,x),g) by {
        let op=(lib.apply)(a,x);
        let word=choose|word:Seq<med::PartialMap<V>>|pi::word_in(right,word) && g==(|s:V|pi::run(word,s));
        assert forall|v:V| #[trigger] op(v).is_some() implies med::partial_related(eq,op(v).unwrap().undo,op(v).unwrap().undo) by {
            assert(pi::value_generators(op).contains(op(v).unwrap().undo));assert(left.contains(op(v).unwrap().undo));assert(pi::respects(eq,op(v).unwrap().undo));
        }
        assert forall|i:int|0<=i<word.len() implies pi::value_stable(eq,op,#[trigger] word[i]) by {
            let y=choose|y:X|(lib.arguments)(b,y) && #[trigger] pi::value_generators((lib.apply)(b,y)).contains(word[i]);
            assert(pi::value_independent(eq,op,(lib.apply)(b,y)));
        }
        strict_value_stable_word(eq,op,word);
    }
    assert forall|x:X,f:med::PartialMap<V>|(lib.arguments)(b,x) && pi::generated(left,f) implies #[trigger] pi::value_stable(eq,(lib.apply)(b,x),f) by {
        let op=(lib.apply)(b,x);
        let word=choose|word:Seq<med::PartialMap<V>>|pi::word_in(left,word) && f==(|s:V|pi::run(word,s));
        assert forall|v:V| #[trigger] op(v).is_some() implies med::partial_related(eq,op(v).unwrap().undo,op(v).unwrap().undo) by {
            assert(pi::value_generators(op).contains(op(v).unwrap().undo));assert(right.contains(op(v).unwrap().undo));assert(pi::respects(eq,op(v).unwrap().undo));
        }
        assert forall|i:int|0<=i<word.len() implies pi::value_stable(eq,op,#[trigger] word[i]) by {
            let y=choose|y:X|(lib.arguments)(a,y) && #[trigger] pi::value_generators((lib.apply)(a,y)).contains(word[i]);
            assert(pi::value_independent(eq,(lib.apply)(a,y),op));
        }
        strict_value_stable_word(eq,op,word);
    }
}



pub open spec fn partial_shift(amount:int)->med::PartialMap<int> {|v:int|Some(v+amount)}
pub proof fn translation_generator(amount:int,map:med::PartialMap<int>)
    requires pi::value_generators(crate::recovery_examples::translation(amount)).contains(map),
    ensures map==partial_shift(amount) || map==partial_shift(-amount),
{
    let op=crate::recovery_examples::translation(amount);
    if map==pi::value_forward(op) {assert(map =~= partial_shift(amount));}
    else {let input=choose|input:int| #[trigger] op(input).is_some() && op(input).unwrap().undo==map;
        assert(map =~= partial_shift(-amount));}
}
pub proof fn translations_value_independent(a:int,b:int)
    ensures pi::value_independent(|x:int,y:int|x==y,crate::recovery_examples::translation(a),crate::recovery_examples::translation(b)),
{
    let eq=|x:int,y:int|x==y;let left=crate::recovery_examples::translation(a);let right=crate::recovery_examples::translation(b);
    assert forall|f:med::PartialMap<int>,g:med::PartialMap<int>|pi::value_generators(left).contains(f) && #[trigger] pi::value_generators(right).contains(g)
        implies #[trigger] pi::commutes(eq,f,g) by {translation_generator(a,f);translation_generator(b,g);}
    assert forall|g:med::PartialMap<int>| #[trigger] pi::value_stable(eq,left,g) by { }
    assert forall|f:med::PartialMap<int>| #[trigger] pi::value_stable(eq,right,f) by { }
}
/// A nonempty existing source library instantiates the strict ALL-argument
/// interface. The real context-mediated call still fails at a missing key.
#[verifier::spinoff_prover]
pub proof fn strict_source_commutative_key(key:crate::Port)
    ensures commutative_key(strict_interface(crate::recovery_examples::equality(),crate::recovery_examples::library()),key),
        (strict_interface(crate::recovery_examples::equality(),crate::recovery_examples::library()).allowed)(key,key),
        d::run(crate::recovery_examples::library(),d::Node::Operation {operation:crate::recovery_examples::key(0),argument:7,select:|_:()|None::<crate::recovery_examples::Stage>},Map::empty()).is_none(),
        d::run(crate::recovery_examples::library(),d::Node::Operation {operation:crate::recovery_examples::key(0),argument:7,select:|_:()|None::<crate::recovery_examples::Stage>},Map::empty().insert(crate::recovery_examples::key(0),10)).unwrap().state[crate::recovery_examples::key(0)]==17,
{
    use crate::recovery_examples as ex;let lib=ex::library();let eq=|x:int,y:int|x==y;
    assert forall|a:crate::Port,b:crate::Port| (strict_interface(ex::equality(),lib).allowed)(key,a) && (strict_interface(ex::equality(),lib).allowed)(key,b)
        implies #[trigger] (strict_interface(ex::equality(),lib).independent)(key,a,b) by {
        assert forall|x:int,y:int|(lib.arguments)(a,x) && (lib.arguments)(b,y)
            implies #[trigger] pi::value_independent(eq,(lib.apply)(a,x),(lib.apply)(b,y)) by {translations_value_independent(x,y);}
        assert forall|map:med::PartialMap<int>| #[trigger] pi::respects(eq,map) by { }
        strict_basis_full(eq,lib,a,b);
        assert((|u:int,v:int|(ex::equality())(key,u,v)) =~= eq);
    }
    ex::actual_operation(7,10);
}

} // verus!
