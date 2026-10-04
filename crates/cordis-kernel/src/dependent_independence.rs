//! Strict iterator independence for the original dependent finite grammar.
//!
//! Indices I and J are retained, including every raw-outcome-selected next.
//! A single-stage projection forgets only its continuation for reuse of local
//! key algebra; it is not an encoding of either whole program into nat.
//! Foreign yield comparison is guarded by successful strict application, as
//! in iterator_bridge, and does not establish the unguarded original claim.
use crate::dependent_grammar as d;
#[cfg(verus_keep_ghost)]
use crate::{
    calculus as c, contexts as ctx, iterator_bridge as ib, iterators as it, mediated as m,
    observation as o, observational_grammar as og, partial_independence as p, quotient as q,
};
use vstd::prelude::*;

verus! {

#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(A)]
#[verifier::reject_recursive_types(X)]
#[verifier::reject_recursive_types(U)]
#[verifier::reject_recursive_types(B)]
#[verifier::reject_recursive_types(I)]
pub struct Grammar<K,A,X,U,B,I> {
    pub library:d::Library<K,A,X,U,B>,
    pub program:d::Program<K,A,X,U,B,I>,
    pub keys:ISet<K>,
    pub provisions:ISet<K>,
    pub root:I,
}
pub open spec fn valid<K,A,X,U,B,I>(eq:spec_fn(K,U,U)->bool,g:Grammar<K,A,X,U,B,I>)->bool {
    og::primitive_theory(eq,g.library) && g.provisions.subset_of(g.keys)
        && d::member(g.library,g.program,g.keys,g.provisions,g.root)
}
pub open spec fn equality<K,U>(eq:spec_fn(K,U,U)->bool)->spec_fn(Map<K,U>,Map<K,U>)->bool {
    |s:Map<K,U>,t:Map<K,U>|d::context_equal(eq,ISet::full(),s,t)
}
/// Only the effect and inverse are projected. The raw result in `outcome`
/// below retains enough information to compare arbitrary-I selectors.
pub open spec fn stage<K,A,X,U,B,I>(lib:d::Library<K,A,X,U,B>,node:d::Node<K,A,X,U,B,I>)->m::Node<K,U,B> {
    match node {
        d::Node::Unit=>m::Node::Unit,
        d::Node::Operation {operation,argument,..}=>m::Node::Operation {key:(lib.key)(operation),operation:(lib.apply)(operation,argument),select:|_:B|None},
        d::Node::Provision {key,value,..}=>m::Node::Provision {key,value,next:None},
    }
}
pub open spec fn forward<K,A,X,U,B,I>(lib:d::Library<K,A,X,U,B>,node:d::Node<K,A,X,U,B,I>)->m::PartialMap<Map<K,U>> {
    |s:Map<K,U>|match d::run(lib,node,s) {Some(y)=>Some(y.state),None=>None}
}
pub open spec fn generators<K,A,X,U,B,I>(lib:d::Library<K,A,X,U,B>,node:d::Node<K,A,X,U,B,I>)->ISet<m::PartialMap<Map<K,U>>> {
    ISet::new(|f:m::PartialMap<Map<K,U>>|f==forward(lib,node) || exists|s:Map<K,U>| #[trigger] d::run(lib,node,s).is_some() && d::run(lib,node,s).unwrap().undo==f)
}
pub open spec fn outcome<K,A,X,U,B,I>(lib:d::Library<K,A,X,U,B>,node:d::Node<K,A,X,U,B,I>,s:Map<K,U>)->Option<B> {
    match node {
        d::Node::Operation {operation,argument,..}=>{let k=(lib.key)(operation);let op=(lib.apply)(operation,argument);
            if s.dom().contains(k) && op(s[k]).is_some() {Some(op(s[k]).unwrap().outcome)} else {None}},
        _=>None,
    }
}
/// The ambient map agrees exactly on embedded finite inputs, including None.
pub open spec fn embedding<K,U>(finite:m::PartialMap<Map<K,U>>,ambient:m::PartialMap<IMap<K,U>>)->bool {
    forall|s:Map<K,U>| #![trigger finite(s),ambient(ctx::embed(s))] {
        &&& finite(s).is_some()==ambient(ctx::embed(s)).is_some()
        &&& (finite(s).is_some() ==> ctx::embed(finite(s).unwrap())==ambient(ctx::embed(s)).unwrap())
    }
}
pub proof fn interpreter<K,A,X,U,B,I>(lib:d::Library<K,A,X,U,B>,node:d::Node<K,A,X,U,B,I>,input:Map<K,U>)
    ensures d::run(lib,node,input).is_some()==m::run(stage(lib,node),ctx::embed(input)).is_some(),
        outcome(lib,node,input)==p::outcome(stage(lib,node),ctx::embed(input)),
        d::run(lib,node,input).is_some() ==> {
            let actual=d::run(lib,node,input).unwrap();let projected=m::run(stage(lib,node),ctx::embed(input)).unwrap();
            ctx::embed(actual.state)==projected.state && embedding(actual.undo,projected.undo)
        },
{
    match node {
        d::Node::Operation {operation,argument,..}=>{
            let k=(lib.key)(operation);let op=(lib.apply)(operation,argument);
            if d::run(lib,node,input).is_some() {ctx::finite_embedding(input,input,k,op(input[k]).unwrap().value);}
        },
        d::Node::Provision {key,value,..}=>{ctx::finite_embedding(input,input,key,value);},
        _=>{},
    }
    if d::run(lib,node,input).is_some() {
        let f=d::run(lib,node,input).unwrap().undo;let g=m::run(stage(lib,node),ctx::embed(input)).unwrap().undo;
        assert forall|s:Map<K,U>| #![trigger f(s),g(ctx::embed(s))] {
            &&& f(s).is_some()==g(ctx::embed(s)).is_some()
            &&& (f(s).is_some() ==> ctx::embed(f(s).unwrap())==g(ctx::embed(s)).unwrap())
        } by {
            match node {
                d::Node::Operation {operation,argument,..}=>{
                    let k=(lib.key)(operation);let undo=(lib.apply)(operation,argument)(input[k]).unwrap().undo;
                    if f(s).is_some() {ctx::finite_embedding(s,s,k,undo(s[k]).unwrap());}
                },
                d::Node::Provision {key,value,..}=>{ctx::finite_embedding(s,s,key,value);},
                _=>{},
            }
        }
    }
}
pub proof fn forward_embedding<K,A,X,U,B,I>(lib:d::Library<K,A,X,U,B>,node:d::Node<K,A,X,U,B,I>)
    ensures embedding(forward(lib,node),p::forward(stage(lib,node))),
{
    let f=forward(lib,node);let g=p::forward(stage(lib,node));
    assert forall|s:Map<K,U>| #![trigger f(s),g(ctx::embed(s))] {
        &&& f(s).is_some()==g(ctx::embed(s)).is_some()
        &&& (f(s).is_some() ==> ctx::embed(f(s).unwrap())==g(ctx::embed(s)).unwrap())
    } by {interpreter(lib,node,s);}
}
pub proof fn generator_embedding<K,A,X,U,B,I>(lib:d::Library<K,A,X,U,B>,node:d::Node<K,A,X,U,B,I>,f:m::PartialMap<Map<K,U>>)
    requires generators(lib,node).contains(f),
    ensures exists|g:m::PartialMap<IMap<K,U>>|p::generators(stage(lib,node)).contains(g) && #[trigger] embedding(f,g),
{
    if f==forward(lib,node) {forward_embedding(lib,node);assert(p::generators(stage(lib,node)).contains(p::forward(stage(lib,node))));}
    else {
        let input=choose|s:Map<K,U>| #[trigger] d::run(lib,node,s).is_some() && d::run(lib,node,s).unwrap().undo==f;
        interpreter(lib,node,input);let g=m::run(stage(lib,node),ctx::embed(input)).unwrap().undo;
        assert(p::generators(stage(lib,node)).contains(g));
    }
}
pub proof fn embedding_related<K,U>(eq:spec_fn(K,U,U)->bool,f:m::PartialMap<Map<K,U>>,g:m::PartialMap<Map<K,U>>,a:m::PartialMap<IMap<K,U>>,b:m::PartialMap<IMap<K,U>>)
    requires embedding(f,a),embedding(g,b),m::partial_related(p::context_eq(eq),a,b),
    ensures m::partial_related(equality(eq),f,g),
{
    assert forall|x:Map<K,U>,y:Map<K,U>| #![trigger f(x),g(y)] equality(eq)(x,y) implies {
        &&& f(x).is_some()==g(y).is_some()
        &&& (f(x).is_some() ==> equality(eq)(f(x).unwrap(),g(y).unwrap()))
    } by {
        assert(p::context_eq(eq)(ctx::embed(x),ctx::embed(y)));
        assert(f(x).is_some()==a(ctx::embed(x)).is_some());assert(g(y).is_some()==b(ctx::embed(y)).is_some());
        assert(a(ctx::embed(x)).is_some()==b(ctx::embed(y)).is_some());
        if f(x).is_some() {
            assert(ctx::embed(f(x).unwrap())==a(ctx::embed(x)).unwrap());assert(ctx::embed(g(y).unwrap())==b(ctx::embed(y)).unwrap());
            assert(p::context_eq(eq)(a(ctx::embed(x)).unwrap(),b(ctx::embed(y)).unwrap()));
        }
    }
}
pub proof fn embedding_commutes<K,U>(eq:spec_fn(K,U,U)->bool,f:m::PartialMap<Map<K,U>>,g:m::PartialMap<Map<K,U>>,a:m::PartialMap<IMap<K,U>>,b:m::PartialMap<IMap<K,U>>)
    requires embedding(f,a),embedding(g,b),p::commutes(p::context_eq(eq),a,b),
    ensures p::commutes(equality(eq),f,g),
{
    assert forall|s:Map<K,U>| #[trigger] p::optional_equal(equality(eq),p::compose(f,g)(s),p::compose(g,f)(s)) by {
        assert(p::optional_equal(p::context_eq(eq),p::compose(a,b)(ctx::embed(s)),p::compose(b,a)(ctx::embed(s))));
        if g(s).is_some() {assert(embedding(f,a));assert(a(ctx::embed(g(s).unwrap())).is_some()==f(g(s).unwrap()).is_some());}
        if f(s).is_some() {assert(embedding(g,b));assert(b(ctx::embed(f(s).unwrap())).is_some()==g(f(s).unwrap()).is_some());}
    }
}

pub proof fn stage_respects<K,A,X,U,B,I>(eq:spec_fn(K,U,U)->bool,lib:d::Library<K,A,X,U,B>,node:d::Node<K,A,X,U,B,I>,keys:ISet<K>,provided:ISet<K>)
    requires og::primitive_theory(eq,lib),d::permitted(lib,keys,provided,node),
    ensures m::stage_respects(eq,ISet::full(),stage(lib,node)),c::equivalence(p::context_eq(eq)),
{
    assert forall|k:K| ISet::<K>::full().contains(k) implies c::equivalence(|a:U,b:U|eq(k,a,b)) by {assert(m::key_equivalence(eq,k));}
    o::context_equivalence(eq,ISet::full());
    let projected=stage(lib,node);
    assert forall|a:IMap<K,U>,b:IMap<K,U>| #![trigger m::run(projected,a),m::run(projected,b)] p::context_eq(eq)(a,b) implies {
        &&& m::run(projected,a).is_some()==m::run(projected,b).is_some()
        &&& (m::run(projected,a).is_some() ==> {
            let x=m::run(projected,a).unwrap();let y=m::run(projected,b).unwrap();
            &&& p::context_eq(eq)(x.state,y.state) && m::partial_related(p::context_eq(eq),x.undo,y.undo) && x.next==y.next
        })
    } by {
        match node {
            d::Node::Operation {operation,argument,..}=>{
                let k=(lib.key)(operation);let op=(lib.apply)(operation,argument);
                assert(d::operation_typed(lib,operation,argument));assert(og::operation_respects(|u:U,v:U|eq(k,u,v),op));
                assert(o::context_equal(eq,ISet::full(),a,b));assert(ISet::<K>::full().contains(k));
                assert(a.dom().contains(k)==b.dom().contains(k));
                if a.dom().contains(k) && op(a[k]).is_some() {
                    assert(eq(k,a[k],b[k]));let x=op(a[k]).unwrap();let y=op(b[k]).unwrap();
                    m::update_related(eq,ISet::full(),k,a,b,x.value,y.value);m::inverse_lift_respects(eq,ISet::full(),k,x.undo,y.undo);
                }
            },
            d::Node::Provision {key,value,..}=>{assert(m::key_equivalence(eq,key));let local=|u:U,v:U|eq(key,u,v);assert(c::equivalence(local));assert(local(value,value));m::provision_admissible::<K,U,B>(eq,ISet::full(),key,value,None);},
            _=>{},
        }
    }
}

pub open spec fn separated<K,A,X,U,B,I,C,Y,D,J>(left:Grammar<K,A,X,U,B,I>,right:Grammar<K,C,Y,U,D,J>)->bool {
    left.provisions.disjoint(right.keys) && right.provisions.disjoint(left.keys)
}
/// Only cross-library pairs at shared declared keys need a local law.
/// Outcomes retain each library's own carrier and actual inverse witnesses.
pub open spec fn witnessed_keys<K,A,X,U,B,I,C,Y,D,J>(eq:spec_fn(K,U,U)->bool,left:Grammar<K,A,X,U,B,I>,right:Grammar<K,C,Y,U,D,J>)->bool {
    let l=left.library;let r=right.library;
    forall|a:A,x:X,b:C,y:Y| #![trigger (l.apply)(a,x),(r.apply)(b,y)]
        l.allowed.contains(a) && (l.arguments)(a,x) && r.allowed.contains(b) && (r.arguments)(b,y)
        && left.keys.contains((l.key)(a)) && right.keys.contains((r.key)(b)) && (l.key)(a)==(r.key)(b)
        ==> p::value_independent(|u:U,v:U|eq((l.key)(a),u,v),(l.apply)(a,x),(r.apply)(b,y))
}
pub proof fn local_independence<K,A,X,U,B,I,C,Y,D,J>(eq:spec_fn(K,U,U)->bool,left:Grammar<K,A,X,U,B,I>,right:Grammar<K,C,Y,U,D,J>,a:d::Node<K,A,X,U,B,I>,b:d::Node<K,C,Y,U,D,J>)
    requires valid(eq,left),valid(eq,right),separated(left,right),witnessed_keys(eq,left,right),
        d::permitted(left.library,left.keys,left.provisions,a),d::permitted(right.library,right.keys,right.provisions,b),
    ensures p::independent(eq,stage(left.library,a),stage(right.library,b)),
{
    let l=left.library;let r=right.library;let an=stage(l,a);let bn=stage(r,b);
    stage_respects(eq,l,a,left.keys,left.provisions);stage_respects(eq,r,b,right.keys,right.provisions);
    match a {
        d::Node::Unit=>{p::unit_independence::<K,U,D,B>(eq,bn);},
        _=>match b {
            d::Node::Unit=>{p::unit_independence::<K,U,B,D>(eq,an);},
            _=>{
                if p::key(an)!=p::key(bn) {p::distinct_nodes(eq,an,bn);}
                else {
                    match a {
                        d::Node::Operation {operation:op,argument:x,..}=>match b {
                            d::Node::Operation {operation:other,argument:y,..}=>{
                                assert((l.key)(op)==(r.key)(other));
                                assert(p::value_independent(|u:U,v:U|eq((l.key)(op),u,v),(l.apply)(op,x),(r.apply)(other,y)));
                                p::shared_operations(eq,(l.key)(op),(l.apply)(op,x),(r.apply)(other,y),|_:B|None,|_:D|None);
                            },_=>{},
                        },_=>{},
                    }
                }
            },
        },
    }
}

pub open spec fn stable<K,A,X,U,B,I>(eq:spec_fn(K,U,U)->bool,lib:d::Library<K,A,X,U,B>,node:d::Node<K,A,X,U,B,I>,f:m::PartialMap<Map<K,U>>)->bool {
    forall|s:Map<K,U>| #[trigger] f(s).is_some() ==> {
        let a=d::run(lib,node,s);let b=d::run(lib,node,f(s).unwrap());
        &&& a.is_some()==b.is_some()
        &&& (a.is_some() ==> m::partial_related(equality(eq),a.unwrap().undo,b.unwrap().undo)
            && a.unwrap().next==b.unwrap().next && outcome(lib,node,s)==outcome(lib,node,f(s).unwrap()))
    }
}
pub proof fn embedding_stable<K,A,X,U,B,I>(eq:spec_fn(K,U,U)->bool,lib:d::Library<K,A,X,U,B>,node:d::Node<K,A,X,U,B,I>,f:m::PartialMap<Map<K,U>>,g:m::PartialMap<IMap<K,U>>)
    requires embedding(f,g),p::stable(eq,stage(lib,node),g),
    ensures stable(eq,lib,node,f),
{
    assert forall|s:Map<K,U>| #[trigger] f(s).is_some() implies {
        let a=d::run(lib,node,s);let b=d::run(lib,node,f(s).unwrap());
        &&& a.is_some()==b.is_some()
        &&& (a.is_some() ==> m::partial_related(equality(eq),a.unwrap().undo,b.unwrap().undo)
            && a.unwrap().next==b.unwrap().next && outcome(lib,node,s)==outcome(lib,node,f(s).unwrap()))
    } by {
        assert(g(ctx::embed(s)).is_some());assert(g(ctx::embed(s)).unwrap()==ctx::embed(f(s).unwrap()));
        interpreter(lib,node,s);interpreter(lib,node,f(s).unwrap());
        let x=m::run(stage(lib,node),ctx::embed(s));let y=m::run(stage(lib,node),ctx::embed(f(s).unwrap()));
        assert(x.is_some()==y.is_some());
        if x.is_some() {
            assert(m::partial_related(p::context_eq(eq),x.unwrap().undo,y.unwrap().undo));
            embedding_related(eq,d::run(lib,node,s).unwrap().undo,d::run(lib,node,f(s).unwrap()).unwrap().undo,x.unwrap().undo,y.unwrap().undo);
            assert(p::outcome(stage(lib,node),ctx::embed(s))==p::outcome(stage(lib,node),ctx::embed(f(s).unwrap())));
            match node {d::Node::Operation {operation,argument,select}=>{
                assert(select(outcome(lib,node,s).unwrap())==select(outcome(lib,node,f(s).unwrap()).unwrap()));
            },_=>{},}
        }
    }
}
pub proof fn generator_respects<K,A,X,U,B,I>(eq:spec_fn(K,U,U)->bool,lib:d::Library<K,A,X,U,B>,node:d::Node<K,A,X,U,B,I>,keys:ISet<K>,provided:ISet<K>,f:m::PartialMap<Map<K,U>>)
    requires og::primitive_theory(eq,lib),d::permitted(lib,keys,provided,node),generators(lib,node).contains(f),
    ensures p::respects(equality(eq),f),
{
    stage_respects(eq,lib,node,keys,provided);generator_embedding(lib,node,f);
    let g=choose|g:m::PartialMap<IMap<K,U>>|p::generators(stage(lib,node)).contains(g) && #[trigger] embedding(f,g);
    p::generator_respects(eq,stage(lib,node),g);embedding_related(eq,f,f,g,g);
}
pub proof fn generator_pair<K,A,X,U,B,I,C,Y,D,J>(eq:spec_fn(K,U,U)->bool,left:Grammar<K,A,X,U,B,I>,right:Grammar<K,C,Y,U,D,J>,a:d::Node<K,A,X,U,B,I>,b:d::Node<K,C,Y,U,D,J>,f:m::PartialMap<Map<K,U>>,g:m::PartialMap<Map<K,U>>)
    requires valid(eq,left),valid(eq,right),separated(left,right),witnessed_keys(eq,left,right),
        d::permitted(left.library,left.keys,left.provisions,a),d::permitted(right.library,right.keys,right.provisions,b),
        generators(left.library,a).contains(f),generators(right.library,b).contains(g),
    ensures p::commutes(equality(eq),f,g),stable(eq,left.library,a,g),stable(eq,right.library,b,f),
{
    local_independence(eq,left,right,a,b);generator_embedding(left.library,a,f);generator_embedding(right.library,b,g);
    let l=choose|map:m::PartialMap<IMap<K,U>>|p::generators(stage(left.library,a)).contains(map) && #[trigger] embedding(f,map);
    let r=choose|map:m::PartialMap<IMap<K,U>>|p::generators(stage(right.library,b)).contains(map) && #[trigger] embedding(g,map);
    embedding_commutes(eq,f,g,l,r);embedding_stable(eq,left.library,a,g,r);embedding_stable(eq,right.library,b,f,l);
}

/// Every actual reachable continuation remains in the least dependent grammar.
pub proof fn reachable_member<K,A,X,U,B,I>(eq:spec_fn(K,U,U)->bool,g:Grammar<K,A,X,U,B,I>,id:I)
    requires valid(eq,g),ib::reach(d::family(g.library,g.program),g.root).contains(id),
    ensures d::member(g.library,g.program,g.keys,g.provisions,id),d::permitted(g.library,g.keys,g.provisions,(g.program)(id)),
{
    let names=d::members(g.library,g.program,g.keys,g.provisions);let family=d::family(g.library,g.program);
    assert(ib::closed(family,names)) by {
        assert forall|i:I,s:Map<K,U>|names.contains(i) && (#[trigger] family(i,s)).is_some() && family(i,s).unwrap().next.is_some()
            implies names.contains(family(i,s).unwrap().next.unwrap()) by {
            d::member_unfolding(g.library,g.program,g.keys,g.provisions,i);
            og::selected_continuation(eq,g.library,(g.program)(i),g.keys,g.provisions,names,s);
        }
    }
    assert(names.contains(g.root));assert(names.contains(id));d::member_unfolding(g.library,g.program,g.keys,g.provisions,id);
}
pub open spec fn reachable_generators<K,A,X,U,B,I>(g:Grammar<K,A,X,U,B,I>)->ISet<m::PartialMap<Map<K,U>>> {
    ISet::new(|f:m::PartialMap<Map<K,U>>|exists|id:I|ib::reach(d::family(g.library,g.program),g.root).contains(id)
        && #[trigger] generators(g.library,(g.program)(id)).contains(f))
}
pub proof fn grammar_generators<K,A,X,U,B,I>(g:Grammar<K,A,X,U,B,I>)
    ensures reachable_generators(g)==ib::generators(d::family(g.library,g.program),g.root),
{
    let family=d::family(g.library,g.program);
    assert forall|id:I| #[trigger] ib::forward(family,id)==forward(g.library,(g.program)(id)) by {
        assert(ib::forward(family,id) =~= forward(g.library,(g.program)(id)));
    }
    assert(reachable_generators(g) =~= ib::generators(family,g.root)) by {
        assert forall|f:m::PartialMap<Map<K,U>>|reachable_generators(g).contains(f) implies ib::generators(family,g.root).contains(f) by {
            let id=choose|id:I|ib::reach(family,g.root).contains(id) && #[trigger] generators(g.library,(g.program)(id)).contains(f);
            assert(ib::forward(family,id)==forward(g.library,(g.program)(id)));
            if f!=forward(g.library,(g.program)(id)) {
                let s=choose|s:Map<K,U>| #[trigger] d::run(g.library,(g.program)(id),s).is_some() && d::run(g.library,(g.program)(id),s).unwrap().undo==f;
                assert(family(id,s).is_some());assert(family(id,s).unwrap().undo==f);
                assert(exists|s:Map<K,U>| (#[trigger] family(id,s)).is_some() && family(id,s).unwrap().undo==f);
            }
            assert(ib::reach(family,g.root).contains(id));
            assert(f==ib::forward(family,id) || exists|s:Map<K,U>| (#[trigger] family(id,s)).is_some() && family(id,s).unwrap().undo==f);
            assert(exists|id:I|ib::reach(family,g.root).contains(id) && (f==ib::forward(family,id) || exists|s:Map<K,U>| (#[trigger] family(id,s)).is_some() && family(id,s).unwrap().undo==f));
        }
        assert forall|f:m::PartialMap<Map<K,U>>|ib::generators(family,g.root).contains(f) implies reachable_generators(g).contains(f) by {
            assert(exists|id:I|ib::reach(family,g.root).contains(id) && (f==ib::forward(family,id) || exists|s:Map<K,U>| (#[trigger] family(id,s)).is_some() && family(id,s).unwrap().undo==f));
            let id=choose|id:I|ib::reach(family,g.root).contains(id) && (f==ib::forward(family,id) || exists|s:Map<K,U>| (#[trigger] family(id,s)).is_some() && family(id,s).unwrap().undo==f);
            assert(ib::forward(family,id)==forward(g.library,(g.program)(id)));
            if f!=ib::forward(family,id) {
                let s=choose|s:Map<K,U>| (#[trigger] family(id,s)).is_some() && family(id,s).unwrap().undo==f;
                assert(d::run(g.library,(g.program)(id),s).is_some());
            }
            assert(generators(g.library,(g.program)(id)).contains(f));
        }
    }
}

pub proof fn reachable_generators_respect<K,A,X,U,B,I>(eq:spec_fn(K,U,U)->bool,g:Grammar<K,A,X,U,B,I>)
    requires valid(eq,g),
    ensures forall|f:m::PartialMap<Map<K,U>>|reachable_generators(g).contains(f) ==> #[trigger] p::respects(equality(eq),f),
{
    assert forall|f:m::PartialMap<Map<K,U>>|reachable_generators(g).contains(f) implies #[trigger] p::respects(equality(eq),f) by {
        let id=choose|id:I|ib::reach(d::family(g.library,g.program),g.root).contains(id) && #[trigger] generators(g.library,(g.program)(id)).contains(f);
        reachable_member(eq,g,id);generator_respects(eq,g.library,(g.program)(id),g.keys,g.provisions,f);
    }
}
pub proof fn grammar_monoids_commute<K,A,X,U,B,I,C,Y,D,J>(eq:spec_fn(K,U,U)->bool,left:Grammar<K,A,X,U,B,I>,right:Grammar<K,C,Y,U,D,J>,f:m::PartialMap<Map<K,U>>,g:m::PartialMap<Map<K,U>>)
    requires valid(eq,left),valid(eq,right),separated(left,right),witnessed_keys(eq,left,right),
        p::generated(reachable_generators(left),f),p::generated(reachable_generators(right),g),
    ensures p::commutes(equality(eq),f,g),
{
    og::context_equivalence(eq,left.library,ISet::full());reachable_generators_respect(eq,left);reachable_generators_respect(eq,right);
    assert forall|a:m::PartialMap<Map<K,U>>,b:m::PartialMap<Map<K,U>>|reachable_generators(left).contains(a) && reachable_generators(right).contains(b)
        implies #[trigger] p::commutes(equality(eq),a,b) by {
        let i=choose|id:I|ib::reach(d::family(left.library,left.program),left.root).contains(id) && #[trigger] generators(left.library,(left.program)(id)).contains(a);
        let j=choose|id:J|ib::reach(d::family(right.library,right.program),right.root).contains(id) && #[trigger] generators(right.library,(right.program)(id)).contains(b);
        reachable_member(eq,left,i);reachable_member(eq,right,j);generator_pair(eq,left,right,(left.program)(i),(right.program)(j),a,b);
    }
    p::generated_commutation(equality(eq),reachable_generators(left),reachable_generators(right),f,g);
}

pub proof fn stable_word<K,A,X,U,B,I>(eq:spec_fn(K,U,U)->bool,lib:d::Library<K,A,X,U,B>,node:d::Node<K,A,X,U,B,I>,keys:ISet<K>,provided:ISet<K>,id:I,word:Seq<m::PartialMap<Map<K,U>>>)
    requires og::primitive_theory(eq,lib),d::permitted(lib,keys,provided,node),
        forall|i:int|0<=i<word.len() ==> stable(eq,lib,node,#[trigger] word[i]),
    ensures stable(eq,lib,node,|s:Map<K,U>|p::run(word,s)),
    decreases word.len(),
{
    og::context_equivalence(eq,lib,ISet::full());og::stage_admissible(id,eq,lib,node,keys,provided,ISet::full());
    if word.len()>0 {stable_word(eq,lib,node,keys,provided,id,word.drop_last());}
    assert forall|s:Map<K,U>| #[trigger] p::run(word,s).is_some() implies {
        let a=d::run(lib,node,s);let b=d::run(lib,node,p::run(word,s).unwrap());
        &&& a.is_some()==b.is_some()
        &&& (a.is_some() ==> m::partial_related(equality(eq),a.unwrap().undo,b.unwrap().undo)
            && a.unwrap().next==b.unwrap().next && outcome(lib,node,s)==outcome(lib,node,p::run(word,s).unwrap()))
    } by {
        if word.len()==0 {
            assert(equality(eq)(s,s));let family=|_:I,x:Map<K,U>|d::run(lib,node,x);
            assert(it::partial_respects(equality(eq),family,id));assert(family(id,s)==d::run(lib,node,s));
        } else {
            let previous=|x:Map<K,U>|p::run(word.drop_last(),x);let middle=previous(s).unwrap();
            assert(stable(eq,lib,node,previous));assert(previous(s).is_some());assert(stable(eq,lib,node,word.last()));assert((word.last())(middle).is_some());
            if d::run(lib,node,s).is_some() {
                p::partial_relation_transitive(equality(eq),d::run(lib,node,s).unwrap().undo,d::run(lib,node,middle).unwrap().undo,d::run(lib,node,p::run(word,s).unwrap()).unwrap().undo);
            }
        }
    }
}
pub proof fn grammar_yields_stable<K,A,X,U,B,I,C,Y,D,J>(eq:spec_fn(K,U,U)->bool,left:Grammar<K,A,X,U,B,I>,right:Grammar<K,C,Y,U,D,J>,id:I,g:m::PartialMap<Map<K,U>>)
    requires valid(eq,left),valid(eq,right),separated(left,right),witnessed_keys(eq,left,right),
        ib::reach(d::family(left.library,left.program),left.root).contains(id),p::generated(reachable_generators(right),g),
    ensures stable(eq,left.library,(left.program)(id),g),
{
    reachable_member(eq,left,id);let node=(left.program)(id);
    let word=choose|word:Seq<m::PartialMap<Map<K,U>>>|p::word_in(reachable_generators(right),word) && g==(|s:Map<K,U>|p::run(word,s));
    assert forall|n:int|0<=n<word.len() implies stable(eq,left.library,node,#[trigger] word[n]) by {
        let j=choose|j:J|ib::reach(d::family(right.library,right.program),right.root).contains(j) && #[trigger] generators(right.library,(right.program)(j)).contains(word[n]);
        reachable_member(eq,right,j);assert(generators(left.library,node).contains(forward(left.library,node)));
        generator_pair(eq,left,right,node,(right.program)(j),forward(left.library,node),word[n]);
    }
    stable_word(eq,left.library,node,left.keys,left.provisions,id,word);
}

pub proof fn grammar_self_related<K,A,X,U,B,I>(eq:spec_fn(K,U,U)->bool,g:Grammar<K,A,X,U,B,I>,id:I)
    requires valid(eq,g),ib::reach(d::family(g.library,g.program),g.root).contains(id),
    ensures q::iterator_related(|a:Option<Map<K,U>>,b:Option<Map<K,U>>|it::optional_eq(equality(eq),a,b),it::encode_partial(d::family(g.library,g.program)),id,id),
{
    reachable_member(eq,g,id);
    let names=ISet::<I>::full();
    assert forall|i:I|names.contains(i) implies d::covers(g.library,ISet::full(),(g.program)(i)) && d::continuations(g.library,(g.program)(i),names) by {match (g.program)(i){d::Node::Operation {..}=>{},_=>{},}}
    assert(names.contains(id));
    assert(exists|names:ISet<I>|names.contains(id) && forall|i:I|names.contains(i) ==> d::covers(g.library,ISet::full(),(g.program)(i)) && d::continuations(g.library,(g.program)(i),names));
    assert(d::covered(g.library,g.program,ISet::full(),id));
    og::grammar_self_related(eq,g.library,g.program,g.keys,g.provisions,ISet::full(),id);
}
pub proof fn iterator_stable<K,A,X,U,B,I,C,Y,D,J>(eq:spec_fn(K,U,U)->bool,left:Grammar<K,A,X,U,B,I>,right:Grammar<K,C,Y,U,D,J>,id:I,g:m::PartialMap<Map<K,U>>)
    requires valid(eq,left),valid(eq,right),separated(left,right),witnessed_keys(eq,left,right),
        ib::reach(d::family(left.library,left.program),left.root).contains(id),ib::transforms(d::family(right.library,right.program),right.root,g),
    ensures ib::stable(equality(eq),d::family(left.library,left.program),id,g),
{
    grammar_generators(right);grammar_yields_stable(eq,left,right,id,g);let family=d::family(left.library,left.program);let names=ib::reach(family,left.root);
    ib::reach_encoding(family,left.root);
    assert forall|s:Map<K,U>| #[trigger] g(s).is_some() implies {
        let a=family(id,s);let b=family(id,g(s).unwrap());
        &&& a.is_some()==b.is_some()
        &&& (a.is_some() ==> ib::yields_related(equality(eq),family,a.unwrap(),b.unwrap()))
    } by {
        assert(d::run(left.library,(left.program)(id),s).is_some()==d::run(left.library,(left.program)(id),g(s).unwrap()).is_some());
        if family(id,s).is_some() && family(id,s).unwrap().next.is_some() {
            let next=family(id,s).unwrap().next.unwrap();assert(names.contains(next));grammar_self_related(eq,left,next);
        }
    }
}
pub proof fn symmetric_witnesses<K,A,X,U,B,I,C,Y,D,J>(eq:spec_fn(K,U,U)->bool,left:Grammar<K,A,X,U,B,I>,right:Grammar<K,C,Y,U,D,J>)
    requires valid(eq,left),witnessed_keys(eq,left,right),
    ensures witnessed_keys(eq,right,left),
{
    let l=left.library;let r=right.library;
    assert forall|b:C,y:Y,a:A,x:X| #![trigger (r.apply)(b,y),(l.apply)(a,x)]
        r.allowed.contains(b) && (r.arguments)(b,y) && l.allowed.contains(a) && (l.arguments)(a,x)
        && right.keys.contains((r.key)(b)) && left.keys.contains((l.key)(a)) && (r.key)(b)==(l.key)(a)
        implies p::value_independent(|u:U,v:U|eq((r.key)(b),u,v),(r.apply)(b,y),(l.apply)(a,x)) by {
        let e=|u:U,v:U|eq((l.key)(a),u,v);let op=(l.apply)(a,x);let other=(r.apply)(b,y);
        assert(m::key_equivalence(eq,(l.key)(a)));assert(c::equivalence(e));assert(p::value_independent(e,op,other));
        assert forall|f:m::PartialMap<U>,g:m::PartialMap<U>|p::value_generators(other).contains(f) && p::value_generators(op).contains(g)
            implies #[trigger] p::commutes(e,f,g) by {assert(p::commutes(e,g,f));p::commute_symmetric(e,g,f);}
    }
}

/// Strict Theorem 47 for both actual arbitrary-index families: every pair of
/// generated transformations commutes, and all reachable yields preserve the
/// real inverses and greatest-related continuations on the foreign domain.
pub proof fn grammar_independence<K,A,X,U,B,I,C,Y,D,J>(eq:spec_fn(K,U,U)->bool,left:Grammar<K,A,X,U,B,I>,right:Grammar<K,C,Y,U,D,J>)
    requires valid(eq,left),valid(eq,right),separated(left,right),witnessed_keys(eq,left,right),
    ensures ib::independent(equality(eq),d::family(left.library,left.program),left.root,d::family(right.library,right.program),right.root),
{
    grammar_generators(left);grammar_generators(right);let l=d::family(left.library,left.program);let r=d::family(right.library,right.program);
    assert forall|f:m::PartialMap<Map<K,U>>,g:m::PartialMap<Map<K,U>>|ib::transforms(l,left.root,f) && ib::transforms(r,right.root,g)
        implies p::commutes(equality(eq),f,g) by {grammar_monoids_commute(eq,left,right,f,g);}
    assert forall|id:I,g:m::PartialMap<Map<K,U>>|ib::reach(l,left.root).contains(id) && ib::transforms(r,right.root,g)
        implies ib::stable(equality(eq),l,id,g) by {iterator_stable(eq,left,right,id,g);}
    symmetric_witnesses(eq,left,right);assert(separated(right,left));
    assert forall|id:J,f:m::PartialMap<Map<K,U>>|ib::reach(r,right.root).contains(id) && ib::transforms(l,left.root,f)
        implies ib::stable(equality(eq),r,id,f) by {iterator_stable(eq,right,left,id,f);}
}
}
