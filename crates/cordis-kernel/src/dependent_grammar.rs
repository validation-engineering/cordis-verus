//! Context-mediated iterators with dependent value, argument and outcome fibers.
//!
//! `U`, `X` and `B` are sum carriers, not a requirement that keys or operations
//! expose a common Rust type. Bijections transport each primitive's own types.
//! Contexts are finite maps and continuation indices have arbitrary type `I`.
#[cfg(verus_keep_ghost)]
use crate::{calculus, iterators as it, observation as o};
use crate::{contexts as c, mediated as m};
use vstd::prelude::*;

verus! {

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(A)]
#[verifier::reject_recursive_types(X)]
#[verifier::reject_recursive_types(U)]
#[verifier::reject_recursive_types(B)]
pub struct Library<K,A,X,U,B> {
    pub values:c::Family<K,U>,
    pub arguments:c::Family<A,X>,
    pub outcomes:c::Family<A,B>,
    pub key:spec_fn(A)->K,
    pub allowed:ISet<A>,
    pub apply:spec_fn(A,X)->m::Operation<U,B>,
}
#[verifier::reject_recursive_types(B)]
pub enum Node<K,A,X,U,B,I> {
    Unit,
    Operation { operation:A, argument:X, select:spec_fn(B)->Option<I> },
    Provision { key:K, value:U, next:Option<I> },
}
pub type Program<K,A,X,U,B,I> = spec_fn(I)->Node<K,A,X,U,B,I>;

pub open spec fn operation_typed<K,A,X,U,B>(lib:Library<K,A,X,U,B>,a:A,x:X)->bool {
    forall|u:U| #[trigger] (lib.apply)(a,x)(u).is_some() ==> {
        let y=(lib.apply)(a,x)(u).unwrap();let k=(lib.key)(a);
        &&& (lib.values)(k,u)
        &&& (lib.values)(k,y.value)
        &&& (lib.outcomes)(a,y.outcome)
        &&& forall|v:U| #[trigger] (y.undo)(v).is_some() ==> (lib.values)(k,v) && (lib.values)(k,(y.undo)(v).unwrap())
    }
}
pub open spec fn primitive_theory<K,A,X,U,B>(eq:spec_fn(K,U,U)->bool,lib:Library<K,A,X,U,B>)->bool {
    &&& forall|k:K| #[trigger] m::key_equivalence(eq,k)
    &&& forall|a:A,x:X| lib.allowed.contains(a) && (lib.arguments)(a,x) ==>
        #[trigger] operation_typed(lib,a,x)
        && m::operation_admissible(|u:U,v:U|eq((lib.key)(a),u,v),(lib.apply)(a,x))
}
pub open spec fn inverse<K,U>(k:K,undo:m::PartialMap<U>)->m::PartialMap<Map<K,U>> {
    |s:Map<K,U>| if !s.dom().contains(k) {None} else {
        match undo(s[k]) {None=>None,Some(v)=>Some(s.insert(k,v))}
    }
}
pub open spec fn run<K,A,X,U,B,I>(lib:Library<K,A,X,U,B>,node:Node<K,A,X,U,B,I>,s:Map<K,U>)
    ->Option<it::PartialIteration<Map<K,U>,I>>
{
    match node {
        Node::Unit=>Some(it::PartialIteration {state:s,undo:|t:Map<K,U>|Some(t),next:None}),
        Node::Operation {operation:a,argument:x,select}=>{
            let k=(lib.key)(a);
            if !s.dom().contains(k) {None} else {match (lib.apply)(a,x)(s[k]) {
                None=>None,
                Some(y)=>Some(it::PartialIteration {state:s.insert(k,y.value),undo:inverse(k,y.undo),next:select(y.outcome)}),
            }}
        },
        Node::Provision {key,value,next}=>if s.dom().contains(key) {None} else {
            Some(it::PartialIteration {state:s.insert(key,value),undo:|t:Map<K,U>|c::revoke(t,key),next})
        },
    }
}
pub open spec fn family<K,A,X,U,B,I>(lib:Library<K,A,X,U,B>,program:Program<K,A,X,U,B,I>)
    ->it::PartialFamily<Map<K,U>,I>
{
    |id:I,s:Map<K,U>|run(lib,program(id),s)
}
pub open spec fn context_equal<K,U>(eq:spec_fn(K,U,U)->bool,keys:ISet<K>,a:Map<K,U>,b:Map<K,U>)->bool {
    o::context_equal(eq,keys,c::embed(a),c::embed(b))
}
pub open spec fn permitted<K,A,X,U,B,I>(lib:Library<K,A,X,U,B>,keys:ISet<K>,provisions:ISet<K>,node:Node<K,A,X,U,B,I>)->bool {
    match node {
        Node::Unit=>true,
        Node::Operation {operation:a,argument:x,..}=>lib.allowed.contains(a) && keys.contains((lib.key)(a)) && (lib.arguments)(a,x),
        Node::Provision {key,value,..}=>provisions.contains(key) && (lib.values)(key,value),
    }
}
/// Only inhabitants of this operation's outcome type name continuations.
/// A continuation attached to another sum tag cannot affect membership.
pub open spec fn continuations<K,A,X,U,B,I>(lib:Library<K,A,X,U,B>,node:Node<K,A,X,U,B,I>,names:ISet<I>)->bool {
    match node {
        Node::Unit=>true,
        Node::Operation {operation:a,select,..}=>forall|b:B| (lib.outcomes)(a,b) && #[trigger] select(b).is_some() ==> names.contains(select(b).unwrap()),
        Node::Provision {next,..}=>next.is_some() ==> names.contains(next.unwrap()),
    }
}
pub open spec fn closed<K,A,X,U,B,I>(lib:Library<K,A,X,U,B>,program:Program<K,A,X,U,B,I>,keys:ISet<K>,provisions:ISet<K>,names:ISet<I>)->bool {
    forall|id:I| permitted(lib,keys,provisions,program(id)) && continuations(lib,program(id),names) ==> names.contains(id)
}
pub open spec fn member<K,A,X,U,B,I>(lib:Library<K,A,X,U,B>,program:Program<K,A,X,U,B,I>,keys:ISet<K>,provisions:ISet<K>,id:I)->bool {
    forall|names:ISet<I>| closed(lib,program,keys,provisions,names) ==> names.contains(id)
}
pub open spec fn members<K,A,X,U,B,I>(lib:Library<K,A,X,U,B>,program:Program<K,A,X,U,B,I>,keys:ISet<K>,provisions:ISet<K>)->ISet<I> {
    ISet::new(|id:I|member(lib,program,keys,provisions,id))
}
pub proof fn continuations_monotone<K,A,X,U,B,I>(lib:Library<K,A,X,U,B>,node:Node<K,A,X,U,B,I>,a:ISet<I>,b:ISet<I>)
    requires a.subset_of(b),continuations(lib,node,a),
    ensures continuations(lib,node,b),
{ }
pub proof fn constructor_member<K,A,X,U,B,I>(lib:Library<K,A,X,U,B>,program:Program<K,A,X,U,B,I>,keys:ISet<K>,provisions:ISet<K>,id:I)
    requires permitted(lib,keys,provisions,program(id)),continuations(lib,program(id),members(lib,program,keys,provisions)),
    ensures member(lib,program,keys,provisions,id),
{
    assert forall|names:ISet<I>| closed(lib,program,keys,provisions,names) implies names.contains(id) by {
        assert(members(lib,program,keys,provisions).subset_of(names));
        continuations_monotone(lib,program(id),members(lib,program,keys,provisions),names);
    }
}
pub proof fn member_unfolding<K,A,X,U,B,I>(lib:Library<K,A,X,U,B>,program:Program<K,A,X,U,B,I>,keys:ISet<K>,provisions:ISet<K>,id:I)
    ensures member(lib,program,keys,provisions,id) == (permitted(lib,keys,provisions,program(id))
        && continuations(lib,program(id),members(lib,program,keys,provisions))),
{
    let all=members(lib,program,keys,provisions);
    if permitted(lib,keys,provisions,program(id)) && continuations(lib,program(id),all) {constructor_member(lib,program,keys,provisions,id);}
    let good=ISet::new(|i:I|member(lib,program,keys,provisions,i) && permitted(lib,keys,provisions,program(i)) && continuations(lib,program(i),all));
    assert(good.subset_of(all));
    assert(closed(lib,program,keys,provisions,good)) by {
        assert forall|i:I| permitted(lib,keys,provisions,program(i)) && continuations(lib,program(i),good) implies good.contains(i) by {
            continuations_monotone(lib,program(i),good,all);
            constructor_member(lib,program,keys,provisions,i);
        }
    }
    if member(lib,program,keys,provisions,id) {assert(good.contains(id));}
}
pub open spec fn covers<K,A,X,U,B,I>(lib:Library<K,A,X,U,B>,keys:ISet<K>,node:Node<K,A,X,U,B,I>)->bool {
    match node {Node::Unit=>true,Node::Operation {operation,..}=>keys.contains((lib.key)(operation)),Node::Provision {key,..}=>keys.contains(key)}
}
pub open spec fn covered<K,A,X,U,B,I>(lib:Library<K,A,X,U,B>,program:Program<K,A,X,U,B,I>,keys:ISet<K>,id:I)->bool {
    exists|names:ISet<I>| names.contains(id) && forall|i:I| names.contains(i) ==> covers(lib,keys,program(i)) && continuations(lib,program(i),names)
}
pub proof fn covered_unfolding<K,A,X,U,B,I>(lib:Library<K,A,X,U,B>,program:Program<K,A,X,U,B,I>,keys:ISet<K>,id:I)
    requires covered(lib,program,keys,id),
    ensures covers(lib,keys,program(id)),continuations(lib,program(id),ISet::new(|i:I|covered(lib,program,keys,i))),
{
    let names=choose|names:ISet<I>| names.contains(id) && forall|i:I| names.contains(i) ==> covers(lib,keys,program(i)) && continuations(lib,program(i),names);
    let all=ISet::new(|i:I|covered(lib,program,keys,i));
    assert(names.subset_of(all)) by {assert forall|i:I| names.contains(i) implies all.contains(i) by { }}
    continuations_monotone(lib,program(id),names,all);
}

pub proof fn update_related<K,U>(eq:spec_fn(K,U,U)->bool,keys:ISet<K>,key:K,a:Map<K,U>,b:Map<K,U>,u:U,v:U)
    requires context_equal(eq,keys,a,b),eq(key,u,v),
    ensures context_equal(eq,keys,a.insert(key,u),b.insert(key,v)),
{
    c::finite_embedding(a,a,key,u);c::finite_embedding(b,b,key,v);
    m::update_related(eq,keys,key,c::embed(a),c::embed(b),u,v);
}
pub proof fn inverse_respects<K,U>(eq:spec_fn(K,U,U)->bool,keys:ISet<K>,key:K,a:m::PartialMap<U>,b:m::PartialMap<U>)
    requires keys.contains(key),m::partial_related(|u:U,v:U|eq(key,u,v),a,b),
    ensures m::partial_related(|s:Map<K,U>,t:Map<K,U>|context_equal(eq,keys,s,t),inverse(key,a),inverse(key,b)),
{
    let left=inverse(key,a);let right=inverse(key,b);
    assert forall|s:Map<K,U>,t:Map<K,U>| #![trigger left(s),right(t)] context_equal(eq,keys,s,t) implies {
        &&& left(s).is_some()==right(t).is_some()
        &&& (left(s).is_some() ==> context_equal(eq,keys,left(s).unwrap(),right(t).unwrap()))
    } by {
        if s.dom().contains(key) {
            assert(eq(key,s[key],t[key]));assert(a(s[key]).is_some()==b(t[key]).is_some());
            if a(s[key]).is_some() {update_related(eq,keys,key,s,t,a(s[key]).unwrap(),b(t[key]).unwrap());}
        }
    }
}
/// Primitive validation proves finite-support preservation, the actual partial
/// inverse, and observational respect. It assumes no checked callback cast.
pub proof fn stage_admissible<K,A,X,U,B,I>(id:I,eq:spec_fn(K,U,U)->bool,lib:Library<K,A,X,U,B>,node:Node<K,A,X,U,B,I>,declared:ISet<K>,provisions:ISet<K>,observed:ISet<K>)
    requires primitive_theory(eq,lib),permitted(lib,declared,provisions,node),covers(lib,observed,node),
    ensures it::partial_respects(|s:Map<K,U>,t:Map<K,U>|context_equal(eq,observed,s,t),|_:I,s:Map<K,U>|run(lib,node,s),id),
        forall|s:Map<K,U>| #[trigger] run(lib,node,s).is_some() ==> (run(lib,node,s).unwrap().undo)(run(lib,node,s).unwrap().state)==Some(s),
        forall|s:Map<K,U>| c::typed(lib.values,s) && #[trigger] run(lib,node,s).is_some() ==> c::typed(lib.values,run(lib,node,s).unwrap().state),
{
    let ctx=|s:Map<K,U>,t:Map<K,U>|context_equal(eq,observed,s,t);
    assert forall|s:Map<K,U>,t:Map<K,U>| #![trigger run(lib,node,s),run(lib,node,t)] ctx(s,t) implies {
        &&& run(lib,node,s).is_some()==run(lib,node,t).is_some()
        &&& (run(lib,node,s).is_some() ==> {
            let x=run(lib,node,s).unwrap();let y=run(lib,node,t).unwrap();
            &&& ctx(x.state,y.state)
            &&& m::partial_related(ctx,x.undo,y.undo)
            &&& x.next==y.next
        })
    } by {
        match node {
            Node::Unit=>{},
            Node::Operation {operation:a,argument:x,select}=>{
                let k=(lib.key)(a);let op=(lib.apply)(a,x);
                assert(operation_typed(lib,a,x));assert(m::operation_admissible(|u:U,v:U|eq(k,u,v),op));
                if s.dom().contains(k) {
                    assert(eq(k,s[k],t[k]));assert(op(s[k]).is_some()==op(t[k]).is_some());
                    if op(s[k]).is_some() {
                        let p=op(s[k]).unwrap();let q=op(t[k]).unwrap();
                        assert(p.outcome==q.outcome);
                        update_related(eq,observed,k,s,t,p.value,q.value);inverse_respects(eq,observed,k,p.undo,q.undo);
                    }
                }
            },
            Node::Provision {key,value,..}=>{
                assert(m::key_equivalence(eq,key));let local=|u:U,v:U|eq(key,u,v);assert(calculus::equivalence(local));assert(local(value,value));assert(eq(key,value,value));
                if !s.dom().contains(key) {update_related(eq,observed,key,s,t,value,value);}
                let undo=|p:Map<K,U>|c::revoke(p,key);
                assert(m::partial_related(ctx,undo,undo)) by {
                    assert forall|a:Map<K,U>,b:Map<K,U>| #![trigger undo(a),undo(b)] ctx(a,b) implies {
                        &&& undo(a).is_some()==undo(b).is_some()
                        &&& (undo(a).is_some() ==> ctx(undo(a).unwrap(),undo(b).unwrap()))
                    } by {c::finite_embedding(a,a,key,value);c::finite_embedding(b,b,key,value);m::remove_related(eq,observed,key,c::embed(a),c::embed(b));}
                }
            },
        }
    }
    assert forall|s:Map<K,U>| #[trigger] run(lib,node,s).is_some() implies (run(lib,node,s).unwrap().undo)(run(lib,node,s).unwrap().state)==Some(s) by {
        match node {
            Node::Unit=>{},
            Node::Operation {operation:a,argument:x,..}=>{
                let k=(lib.key)(a);let op=(lib.apply)(a,x);let y=op(s[k]).unwrap();
                assert(operation_typed(lib,a,x));assert(m::operation_admissible(|u:U,v:U|eq(k,u,v),op));assert((y.undo)(y.value)==Some(s[k]));
                assert(s.insert(k,y.value).insert(k,s[k]) =~= s);
            },
            Node::Provision {key,value,..}=>{assert(s.insert(key,value).remove(key) =~= s);},
        }
    }
    assert forall|s:Map<K,U>| c::typed(lib.values,s) && #[trigger] run(lib,node,s).is_some() implies c::typed(lib.values,run(lib,node,s).unwrap().state) by {
        match node {
            Node::Operation {operation:a,argument:x,..}=>{assert(operation_typed(lib,a,x));},
            _=>{},
        }
    }
}

pub proof fn selected_continuation<K,A,X,U,B,I>(eq:spec_fn(K,U,U)->bool,lib:Library<K,A,X,U,B>,node:Node<K,A,X,U,B,I>,declared:ISet<K>,provisions:ISet<K>,names:ISet<I>,s:Map<K,U>)
    requires primitive_theory(eq,lib),permitted(lib,declared,provisions,node),continuations(lib,node,names),run(lib,node,s).is_some(),run(lib,node,s).unwrap().next.is_some(),
    ensures names.contains(run(lib,node,s).unwrap().next.unwrap()),
{
    match node {
        Node::Operation {operation:a,argument:x,select}=>{
            let k=(lib.key)(a);let op=(lib.apply)(a,x);
            assert(operation_typed(lib,a,x));assert((lib.outcomes)(a,op(s[k]).unwrap().outcome));
        },
        _=>{},
    }
}
/// The least grammar implies the least iterator type even for uncountable
/// continuation indices and outcome branching without a common finite rank.
pub proof fn grammar_inductive<K,A,X,U,B,I>(eq:spec_fn(K,U,U)->bool,lib:Library<K,A,X,U,B>,program:Program<K,A,X,U,B,I>,declared:ISet<K>,provisions:ISet<K>,id:I)
    requires primitive_theory(eq,lib),member(lib,program,declared,provisions,id),
    ensures it::inductive_member(it::encode_partial(family(lib,program)),id),
{
    let encoded=it::encode_partial(family(lib,program));let good=it::inductive_members(encoded);
    assert(closed(lib,program,declared,provisions,good)) by {
        assert forall|i:I| permitted(lib,declared,provisions,program(i)) && continuations(lib,program(i),good) implies good.contains(i) by {
            assert forall|s:Option<Map<K,U>>| #[trigger] encoded(i,s).next.is_some() implies good.contains(encoded(i,s).next.unwrap()) by {
                assert(s.is_some());assert(run(lib,program(i),s.unwrap()).is_some());
                selected_continuation(eq,lib,program(i),declared,provisions,good,s.unwrap());
            }
            it::inductive_constructor(encoded,i);
        }
    }
    assert(good.contains(id));
}
/// Lemma 39 for the dependent finite context grammar. The observed keys need
/// only cover reachable stages, independently of the declaration set. Actual
/// raw outcomes select recursively witnessed continuations; failure is kept.
pub proof fn grammar_paper_witnessed<K,A,X,U,B,I>(eq:spec_fn(K,U,U)->bool,lib:Library<K,A,X,U,B>,program:Program<K,A,X,U,B,I>,declared:ISet<K>,provisions:ISet<K>,observed:ISet<K>,id:I)
    requires primitive_theory(eq,lib),provisions.subset_of(declared),member(lib,program,declared,provisions,id),covered(lib,program,observed,id),
    ensures it::paper_partial_witnessed(|s:Map<K,U>,t:Map<K,U>|context_equal(eq,observed,s,t),family(lib,program),id),
        forall|s:Map<K,U>| #[trigger] run(lib,program(id),s).is_some() ==> (run(lib,program(id),s).unwrap().undo)(run(lib,program(id),s).unwrap().state)==Some(s),
        forall|s:Map<K,U>| c::typed(lib.values,s) && #[trigger] run(lib,program(id),s).is_some() ==> c::typed(lib.values,run(lib,program(id),s).unwrap().state),
{
    let names=ISet::new(|i:I|member(lib,program,declared,provisions,i) && covered(lib,program,observed,i));
    let ctx=|s:Map<K,U>,t:Map<K,U>|context_equal(eq,observed,s,t);let f=family(lib,program);
    assert forall|k:K| observed.contains(k) implies calculus::equivalence(|u:U,v:U|eq(k,u,v)) by {assert(m::key_equivalence(eq,k));}
    o::context_equivalence(eq,observed);
    assert forall|i:I| names.contains(i) implies it::partial_respects(ctx,f,i) by {
        member_unfolding(lib,program,declared,provisions,i);covered_unfolding(lib,program,observed,i);
        stage_admissible(i,eq,lib,program(i),declared,provisions,observed);
        let one=|_:I,s:Map<K,U>|run(lib,program(i),s);
        assert forall|a:Map<K,U>,b:Map<K,U>| #![trigger f(i,a),f(i,b)] ctx(a,b) implies {
            &&& f(i,a).is_some()==f(i,b).is_some()
            &&& (f(i,a).is_some() ==> ctx(f(i,a).unwrap().state,f(i,b).unwrap().state)
                && m::partial_related(ctx,f(i,a).unwrap().undo,f(i,b).unwrap().undo)
                && f(i,a).unwrap().next==f(i,b).unwrap().next)
        } by {assert(one(i,a)==f(i,a));assert(one(i,b)==f(i,b));}
    }
    assert forall|i:I,s:Map<K,U>| #![trigger f(i,s)] names.contains(i) && f(i,s).is_some() implies {
        let yielded=f(i,s).unwrap();
        &&& (yielded.undo)(yielded.state).is_some()
        &&& ctx((yielded.undo)(yielded.state).unwrap(),s)
        &&& (yielded.next.is_some() ==> names.contains(yielded.next.unwrap()))
    } by {
        member_unfolding(lib,program,declared,provisions,i);covered_unfolding(lib,program,observed,i);
        stage_admissible(i,eq,lib,program(i),declared,provisions,observed);
        let ambient=|a:IMap<K,U>,b:IMap<K,U>|o::context_equal(eq,observed,a,b);assert(calculus::equivalence(ambient));assert(ambient(c::embed(s),c::embed(s)));assert(ctx(s,s));
        if f(i,s).unwrap().next.is_some() {
            selected_continuation(eq,lib,program(i),declared,provisions,members(lib,program,declared,provisions),s);
            selected_continuation(eq,lib,program(i),declared,provisions,ISet::new(|j:I|covered(lib,program,observed,j)),s);
        }
    }
    it::partial_family_coinduction(ctx,f,names,id);
    grammar_inductive(eq,lib,program,declared,provisions,id);
    member_unfolding(lib,program,declared,provisions,id);covered_unfolding(lib,program,observed,id);
    stage_admissible(id,eq,lib,program(id),declared,provisions,observed);
}

/// Encode one operation's own `T`, `Arg`, and `Out`, independently of all
/// other operations. No downcast is unchecked: wrong sum tags return `None`.
pub open spec fn transport<K,A,X,U,B,T,Arg,Out>(value:c::FiberCodec<K,U,T>,argument:c::FiberCodec<A,X,Arg>,outcome:c::FiberCodec<A,B,Out>,operation:spec_fn(Arg)->m::Operation<T,Out>,x:X)->m::Operation<U,B> {
    |u:U| match ((argument.decode)(x),(value.decode)(u)) {
        (Some(a),Some(v))=>match operation(a)(v) {
            None=>None,
            Some(y)=>Some(m::ValueYield {value:(value.encode)(y.value),undo:c::encoded_inverse(value,y.undo),outcome:(outcome.encode)(y.outcome)}),
        },
        _=>None,
    }
}
/// Every constituent of the primitive theory follows from typed source
/// operations and bijective codecs, including raw outcomes and partial undo.
pub proof fn transport_admissible<K,A,X,U,B,T,Arg,Out>(values:c::Family<K,U>,arguments:c::Family<A,X>,outcomes:c::Family<A,B>,value:c::FiberCodec<K,U,T>,argument:c::FiberCodec<A,X,Arg>,outcome:c::FiberCodec<A,B,Out>,eq:spec_fn(T,T)->bool,operation:spec_fn(Arg)->m::Operation<T,Out>,x:X)
    requires c::codec(values,value),c::codec(arguments,argument),c::codec(outcomes,outcome),argument.key==outcome.key,
        forall|a:Arg| #[trigger] m::operation_admissible(eq,operation(a)),
    ensures m::operation_admissible(|u:U,v:U|it::codec_relation(value,eq,u,v),transport(value,argument,outcome,operation,x)),
        forall|u:U| #[trigger] transport(value,argument,outcome,operation,x)(u).is_some() ==> {
            let y=transport(value,argument,outcome,operation,x)(u).unwrap();
            &&& values(value.key,u)
            &&& values(value.key,y.value)
            &&& outcomes(outcome.key,y.outcome)
            &&& forall|v:U| #[trigger] (y.undo)(v).is_some() ==> values(value.key,v) && values(value.key,(y.undo)(v).unwrap())
        },
{
    let op=transport(value,argument,outcome,operation,x);
    assert forall|u:U,v:U| #![trigger op(u),op(v)] it::codec_relation(value,eq,u,v) implies {
        &&& op(u).is_some()==op(v).is_some()
        &&& (op(u).is_some() ==> {
            let p=op(u).unwrap();let q=op(v).unwrap();
            &&& it::codec_relation(value,eq,p.value,q.value) && p.outcome==q.outcome
            &&& m::partial_related(|s:U,t:U|it::codec_relation(value,eq,s,t),p.undo,q.undo)
        })
    } by {
        if (argument.decode)(x).is_some() && (value.decode)(u).is_some() {
            let a=(argument.decode)(x).unwrap();let p=(value.decode)(u).unwrap();let q=(value.decode)(v).unwrap();
            assert(m::operation_admissible(eq,operation(a)));assert(eq(p,q));
            if operation(a)(p).is_some() {
                let yp=operation(a)(p).unwrap();let yq=operation(a)(q).unwrap();
                assert(operation(a)(q).is_some());
                it::codec_inverse_respects(values,value,eq,yp.undo,yq.undo);
                assert((value.decode)((value.encode)(yp.value))==Some(yp.value));
                assert((value.decode)((value.encode)(yq.value))==Some(yq.value));
            }
        }
    }
    assert forall|u:U| #[trigger] op(u).is_some() implies (op(u).unwrap().undo)(op(u).unwrap().value)==Some(u) by {
        let a=(argument.decode)(x).unwrap();let v=(value.decode)(u).unwrap();let y=operation(a)(v).unwrap();
        assert(m::operation_admissible(eq,operation(a)));assert((y.undo)(y.value)==Some(v));
        assert((value.decode)((value.encode)(y.value))==Some(y.value));assert((value.encode)(v)==u);
    }
    assert forall|u:U| #[trigger] op(u).is_some() implies {
        let y=op(u).unwrap();
        &&& values(value.key,u)
        &&& values(value.key,y.value)
        &&& outcomes(outcome.key,y.outcome)
        &&& forall|v:U| #[trigger] (y.undo)(v).is_some() ==> values(value.key,v) && values(value.key,(y.undo)(v).unwrap())
    } by {
        let a=(argument.decode)(x).unwrap();let v=(value.decode)(u).unwrap();let original=operation(a)(v).unwrap();
        assert((value.decode)((value.encode)(original.value))==Some(original.value));
        assert((outcome.decode)((outcome.encode)(original.outcome))==Some(original.outcome));
        assert(values(value.key,(value.encode)(original.value)));assert(outcomes(outcome.key,(outcome.encode)(original.outcome)));
        assert forall|w:U| #[trigger] (op(u).unwrap().undo)(w).is_some() implies values(value.key,w) && values(value.key,(op(u).unwrap().undo)(w).unwrap()) by {
            assert((value.decode)(w).is_some());
            let restored=(original.undo)((value.decode)(w).unwrap()).unwrap();assert((value.decode)((value.encode)(restored))==Some(restored));assert(values(value.key,(value.encode)(restored)));
        }
    }
}
/// Round-tripping the exact raw outcome proves that encoding cannot identify
/// two observably different outcomes merely because they select the same next.
pub proof fn transport_exact<K,A,X,U,B,T,Arg,Out>(values:c::Family<K,U>,arguments:c::Family<A,X>,outcomes:c::Family<A,B>,value:c::FiberCodec<K,U,T>,argument:c::FiberCodec<A,X,Arg>,outcome:c::FiberCodec<A,B,Out>,operation:spec_fn(Arg)->m::Operation<T,Out>,a:Arg,v:T)
    requires c::codec(values,value),c::codec(arguments,argument),c::codec(outcomes,outcome),
    ensures transport(value,argument,outcome,operation,(argument.encode)(a))((value.encode)(v)).is_some()==operation(a)(v).is_some(),
        operation(a)(v).is_some() ==> {
            let original=operation(a)(v).unwrap();let encoded=transport(value,argument,outcome,operation,(argument.encode)(a))((value.encode)(v)).unwrap();
            &&& (outcome.decode)(encoded.outcome)==Some(original.outcome)
            &&& (value.decode)(encoded.value)==Some(original.value)
            &&& forall|w:T| #[trigger] (encoded.undo)((value.encode)(w)).is_some()==(original.undo)(w).is_some()
                && ((original.undo)(w).is_some() ==> (value.decode)((encoded.undo)((value.encode)(w)).unwrap())==(original.undo)(w))
        },
{ }

#[derive(PartialEq,Eq,Structural)]
pub enum ExampleOperation { Toggle, Add, Positive }
#[derive(PartialEq,Eq,Structural)]
pub enum ExampleArgument { Toggle(bool), Add(int), Read }
#[derive(PartialEq,Eq,Structural)]
pub enum ExampleOutcome { PreviousFlag(bool), PreviousCount(int), Positive(bool) }
#[derive(PartialEq,Eq,Structural)]
pub enum ExampleIndex { InstallFlag, InstallCount, Toggle, Add, Positive }
pub open spec fn example_arguments(a:ExampleOperation,x:ExampleArgument)->bool {
    match (a,x) {(ExampleOperation::Toggle,ExampleArgument::Toggle(_))=>true,
        (ExampleOperation::Add,ExampleArgument::Add(_))=>true,
        (ExampleOperation::Positive,ExampleArgument::Read)=>true,_=>false}
}
pub open spec fn example_outcomes(a:ExampleOperation,b:ExampleOutcome)->bool {
    match (a,b) {(ExampleOperation::Toggle,ExampleOutcome::PreviousFlag(_))=>true,
        (ExampleOperation::Add,ExampleOutcome::PreviousCount(_))=>true,
        (ExampleOperation::Positive,ExampleOutcome::Positive(_))=>true,_=>false}
}
pub open spec fn toggle_argument()->c::FiberCodec<ExampleOperation,ExampleArgument,bool> {
    c::FiberCodec {key:ExampleOperation::Toggle,encode:|x:bool|ExampleArgument::Toggle(x),decode:|x:ExampleArgument|match x {ExampleArgument::Toggle(x)=>Some(x),_=>None}}
}
pub open spec fn add_argument()->c::FiberCodec<ExampleOperation,ExampleArgument,int> {
    c::FiberCodec {key:ExampleOperation::Add,encode:|x:int|ExampleArgument::Add(x),decode:|x:ExampleArgument|match x {ExampleArgument::Add(x)=>Some(x),_=>None}}
}
pub open spec fn positive_argument()->c::FiberCodec<ExampleOperation,ExampleArgument,()> {
    c::FiberCodec {key:ExampleOperation::Positive,encode:|_:()|ExampleArgument::Read,decode:|x:ExampleArgument|match x {ExampleArgument::Read=>Some(()),_=>None}}
}
pub open spec fn toggle_outcome()->c::FiberCodec<ExampleOperation,ExampleOutcome,bool> {
    c::FiberCodec {key:ExampleOperation::Toggle,encode:|x:bool|ExampleOutcome::PreviousFlag(x),decode:|x:ExampleOutcome|match x {ExampleOutcome::PreviousFlag(x)=>Some(x),_=>None}}
}
pub open spec fn add_outcome()->c::FiberCodec<ExampleOperation,ExampleOutcome,int> {
    c::FiberCodec {key:ExampleOperation::Add,encode:|x:int|ExampleOutcome::PreviousCount(x),decode:|x:ExampleOutcome|match x {ExampleOutcome::PreviousCount(x)=>Some(x),_=>None}}
}
pub open spec fn positive_outcome()->c::FiberCodec<ExampleOperation,ExampleOutcome,bool> {
    c::FiberCodec {key:ExampleOperation::Positive,encode:|x:bool|ExampleOutcome::Positive(x),decode:|x:ExampleOutcome|match x {ExampleOutcome::Positive(x)=>Some(x),_=>None}}
}
pub open spec fn toggle(x:bool)->m::Operation<bool,bool> {
    |v:bool|Some(m::ValueYield {value:v!=x,undo:|w:bool|Some(w!=x),outcome:v})
}
pub open spec fn add(x:int)->m::Operation<int,int> {
    |v:int|Some(m::ValueYield {value:v+x,undo:|w:int|Some(w-x),outcome:v})
}
pub open spec fn positive(_argument:())->m::Operation<int,bool> {
    |v:int|Some(m::ValueYield {value:v,undo:|w:int|Some(w),outcome:v>0})
}
pub open spec fn example_library()->Library<c::ExampleKey,ExampleOperation,ExampleArgument,c::ExampleValue,ExampleOutcome> {
    Library {values:|k,u|c::example_family(k,u),arguments:|a,x|example_arguments(a,x),outcomes:|a,b|example_outcomes(a,b),
        key:|a:ExampleOperation|match a {ExampleOperation::Toggle=>c::ExampleKey::Flag,_=>c::ExampleKey::Count},allowed:ISet::full(),
        apply:|a:ExampleOperation,x:ExampleArgument|match a {
            ExampleOperation::Toggle=>transport(c::flag_codec(),toggle_argument(),toggle_outcome(),|x|toggle(x),x),
            ExampleOperation::Add=>transport(c::count_codec(),add_argument(),add_outcome(),|x|add(x),x),
            ExampleOperation::Positive=>transport(c::count_codec(),positive_argument(),positive_outcome(),|x|positive(x),x),
        }}
}
pub open spec fn example_equal(k:c::ExampleKey,u:c::ExampleValue,v:c::ExampleValue)->bool {
    match k {c::ExampleKey::Flag=>it::codec_relation(c::flag_codec(),|a:bool,b:bool|a==b,u,v),
        c::ExampleKey::Count=>it::codec_relation(c::count_codec(),|a:int,b:int|a==b,u,v)}
}
pub proof fn heterogeneous_primitives()
    ensures primitive_theory(|k,u,v|example_equal(k,u,v),example_library()),
        c::codec(|a,b|example_outcomes(a,b),add_outcome()),
        c::codec(|a,b|example_outcomes(a,b),positive_outcome()),
{
    c::heterogeneous_family();
    let values=|k,u|c::example_family(k,u);let arguments=|a,x|example_arguments(a,x);let outcomes=|a,b|example_outcomes(a,b);
    assert(c::codec(arguments,toggle_argument()));assert(c::codec(arguments,add_argument()));assert(c::codec(arguments,positive_argument()));
    assert(c::codec(outcomes,toggle_outcome()));assert(c::codec(outcomes,add_outcome()));assert(c::codec(outcomes,positive_outcome()));
    let eq=|k,u,v|example_equal(k,u,v);
    assert forall|k:c::ExampleKey| #[trigger] m::key_equivalence(eq,k) by {
        match k {c::ExampleKey::Flag=>{it::codec_equivalence(c::flag_codec(),|a:bool,b:bool|a==b);},
            c::ExampleKey::Count=>{it::codec_equivalence(c::count_codec(),|a:int,b:int|a==b);}}
    }
    let lib=example_library();
    assert forall|a:ExampleOperation,x:ExampleArgument| lib.allowed.contains(a) && (lib.arguments)(a,x) implies
        #[trigger] operation_typed(lib,a,x) && m::operation_admissible(|u:c::ExampleValue,v:c::ExampleValue|example_equal((lib.key)(a),u,v),(lib.apply)(a,x)) by {
        match a {
            ExampleOperation::Toggle=>{transport_admissible(values,arguments,outcomes,c::flag_codec(),toggle_argument(),toggle_outcome(),|a:bool,b:bool|a==b,|x|toggle(x),x);},
            ExampleOperation::Add=>{transport_admissible(values,arguments,outcomes,c::count_codec(),add_argument(),add_outcome(),|a:int,b:int|a==b,|x|add(x),x);},
            ExampleOperation::Positive=>{transport_admissible(values,arguments,outcomes,c::count_codec(),positive_argument(),positive_outcome(),|a:int,b:int|a==b,|x|positive(x),x);},
        }
    }
}
/// The Add and Positive operations share the Count value type but have
/// different argument and outcome types. A foreign outcome tag deliberately
/// points back to the same node; that uninhabited continuation is irrelevant.
pub open spec fn example_program(id:ExampleIndex)->Node<c::ExampleKey,ExampleOperation,ExampleArgument,c::ExampleValue,ExampleOutcome,ExampleIndex> {
    match id {
        ExampleIndex::InstallFlag=>Node::Provision {key:c::ExampleKey::Flag,value:c::ExampleValue::Flag(false),next:Some(ExampleIndex::InstallCount)},
        ExampleIndex::InstallCount=>Node::Provision {key:c::ExampleKey::Count,value:c::ExampleValue::Count(4),next:Some(ExampleIndex::Toggle)},
        ExampleIndex::Toggle=>Node::Operation {operation:ExampleOperation::Toggle,argument:ExampleArgument::Toggle(true),select:|b:ExampleOutcome|match b {ExampleOutcome::PreviousFlag(_)=>Some(ExampleIndex::Add),_=>Some(ExampleIndex::Toggle)}},
        ExampleIndex::Add=>Node::Operation {operation:ExampleOperation::Add,argument:ExampleArgument::Add(3),select:|b:ExampleOutcome|match b {ExampleOutcome::PreviousCount(_)=>Some(ExampleIndex::Positive),_=>Some(ExampleIndex::Add)}},
        ExampleIndex::Positive=>Node::Operation {operation:ExampleOperation::Positive,argument:ExampleArgument::Read,select:|b:ExampleOutcome|match b {ExampleOutcome::Positive(_)=>None,_=>Some(ExampleIndex::Positive)}},
    }
}
pub proof fn heterogeneous_grammar()
    ensures member(example_library(),|i|example_program(i),ISet::full(),ISet::full(),ExampleIndex::InstallFlag),
        it::paper_partial_witnessed(|s:Map<c::ExampleKey,c::ExampleValue>,t:Map<c::ExampleKey,c::ExampleValue>|context_equal(|k,u,v|example_equal(k,u,v),ISet::full(),s,t),family(example_library(),|i|example_program(i)),ExampleIndex::InstallFlag),
{
    let lib=example_library();let program=|i|example_program(i);let keys=ISet::full();
    heterogeneous_primitives();
    constructor_member(lib,program,keys,keys,ExampleIndex::Positive);
    constructor_member(lib,program,keys,keys,ExampleIndex::Add);
    constructor_member(lib,program,keys,keys,ExampleIndex::Toggle);
    constructor_member(lib,program,keys,keys,ExampleIndex::InstallCount);
    constructor_member(lib,program,keys,keys,ExampleIndex::InstallFlag);
    assert forall|i:ExampleIndex| ISet::<ExampleIndex>::full().contains(i) implies covers(lib,keys,program(i)) && continuations(lib,program(i),ISet::full()) by { }
    assert(ISet::<ExampleIndex>::full().contains(ExampleIndex::InstallFlag));
    assert(covered(lib,program,keys,ExampleIndex::InstallFlag));
    grammar_paper_witnessed(|k,u,v|example_equal(k,u,v),lib,program,keys,keys,keys,ExampleIndex::InstallFlag);
}
/// Concrete evaluation validates the transport, including both original
/// outcome types, exact local undo, and rejection of a mistyped argument.
pub proof fn heterogeneous_execution()
    ensures {
        let lib=example_library();let table=Map::empty().insert(c::ExampleKey::Flag,c::ExampleValue::Flag(false)).insert(c::ExampleKey::Count,c::ExampleValue::Count(4));
        let flag=run(lib,example_program(ExampleIndex::Toggle),table).unwrap();
        let count=run(lib,example_program(ExampleIndex::Add),flag.state).unwrap();
        let done=run(lib,example_program(ExampleIndex::Positive),count.state).unwrap();
        &&& flag.state[c::ExampleKey::Flag]==c::ExampleValue::Flag(true)
        &&& count.state[c::ExampleKey::Count]==c::ExampleValue::Count(7)
        &&& done.next==None
        &&& (flag.undo)((count.undo)((done.undo)(done.state).unwrap()).unwrap())==Some(table)
        &&& (lib.apply)(ExampleOperation::Add,ExampleArgument::Add(3))(c::ExampleValue::Count(4)).unwrap().outcome==ExampleOutcome::PreviousCount(4)
        &&& (lib.apply)(ExampleOperation::Positive,ExampleArgument::Read)(c::ExampleValue::Count(7)).unwrap().outcome==ExampleOutcome::Positive(true)
        &&& (lib.apply)(ExampleOperation::Add,ExampleArgument::Read)(c::ExampleValue::Count(4))==None
    },
{
    let table=Map::empty().insert(c::ExampleKey::Flag,c::ExampleValue::Flag(false)).insert(c::ExampleKey::Count,c::ExampleValue::Count(4));
    let restored=table.insert(c::ExampleKey::Flag,c::ExampleValue::Flag(true)).insert(c::ExampleKey::Count,c::ExampleValue::Count(7)).insert(c::ExampleKey::Count,c::ExampleValue::Count(7)).insert(c::ExampleKey::Count,c::ExampleValue::Count(4)).insert(c::ExampleKey::Flag,c::ExampleValue::Flag(false));
    assert(restored =~= table);
}

/// The inverse may be applied at any well-typed current context, not only the
/// original output. Its failure remains observable and every other key stays
/// unchanged, including values of unrelated types.
pub proof fn inverse_preserves_typing<K,A,X,U,B,I>(eq:spec_fn(K,U,U)->bool,lib:Library<K,A,X,U,B>,node:Node<K,A,X,U,B,I>,declared:ISet<K>,provisions:ISet<K>,input:Map<K,U>,current:Map<K,U>)
    requires primitive_theory(eq,lib),permitted(lib,declared,provisions,node),run(lib,node,input).is_some(),c::typed(lib.values,current),
    ensures (run(lib,node,input).unwrap().undo)(current).is_some() ==> c::typed(lib.values,(run(lib,node,input).unwrap().undo)(current).unwrap()),
{
    match node {
        Node::Operation {operation:a,argument:x,..}=>{
            let k=(lib.key)(a);let yielded=(lib.apply)(a,x)(input[k]).unwrap();assert(operation_typed(lib,a,x));
            if (run(lib,node,input).unwrap().undo)(current).is_some() {
                assert((yielded.undo)(current[k]).is_some());
                assert((lib.values)(k,(yielded.undo)(current[k]).unwrap()));
            }
        },
        Node::Provision {key,..}=>{c::revoke_preserves_typing(lib.values,current,key);},
        _=>{},
    }
}
/// The constructor language observes operation failure and restriction failure
/// separately. In particular, withdrawing an already absent binding is not
/// silently treated as the identity map.
pub proof fn strict_domains<K,A,X,U,B,I>(lib:Library<K,A,X,U,B>,key:K,value:U,next:Option<I>,input:Map<K,U>,current:Map<K,U>,a:A,x:X,select:spec_fn(B)->Option<I>)
    ensures run(lib,Node::Provision {key,value,next},input).is_some()==!input.dom().contains(key),
        !input.dom().contains(key) ==> (run(lib,Node::Provision {key,value,next},input).unwrap().undo)(current).is_some()==current.dom().contains(key),
        run(lib,Node::Operation {operation:a,argument:x,select},input).is_some()==(input.dom().contains((lib.key)(a)) && (lib.apply)(a,x)(input[(lib.key)(a)]).is_some()),
{ }
}
