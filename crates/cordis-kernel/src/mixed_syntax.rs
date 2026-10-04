//! A single least grammar for dependent operations and child installation.
//!
//! Membership ranges over actor identities, declared interfaces and arbitrary
//! continuation indices together. Child roots are premises of the same least
//! fixed point, rather than an independently assumed invariant of the result.
use crate::{dependent_grammar as d, dependent_lift as dep, Port};
#[cfg(verus_keep_ghost)]
use crate::{grammar_lift as lift, semantics as s};
use vstd::prelude::*;

verus! {

pub type Library<A,X,U,B> = dep::Library<A,X,U,B>;

#[verifier::reject_recursive_types(B)]
pub enum Node<A,X,U,B,I> {
    Dependent {node:d::Node<Port,A,X,U,B,I>},
    Child {child:usize,dependencies:ISet<Port>,provisions:ISet<Port>,root:I,next:Option<I>},
}
pub type Programs<A,X,U,B,I> = spec_fn(usize)->spec_fn(I)->Node<A,X,U,B,I>;
pub type Name<I> = (usize,ISet<Port>,ISet<Port>,I);
pub type Names<I> = ISet<Name<I>>;

pub open spec fn local<I>(names:Names<I>,actor:usize,keys:ISet<Port>,provisions:ISet<Port>)->ISet<I> {
    ISet::new(|id:I|names.contains((actor,keys,provisions,id)))
}
pub open spec fn permitted<A,X,U,B,I>(lib:Library<A,X,U,B>,keys:ISet<Port>,provisions:ISet<Port>,node:Node<A,X,U,B,I>)->bool {
    match node {
        Node::Dependent {node}=>d::permitted(lib,keys,provisions,node),
        Node::Child {..}=>true,
    }
}
pub open spec fn continuations<A,X,U,B,I>(lib:Library<A,X,U,B>,node:Node<A,X,U,B,I>,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,names:Names<I>)->bool {
    match node {
        Node::Dependent {node}=>d::continuations(lib,node,local(names,actor,keys,provisions)),
        Node::Child {child,dependencies,provisions:provided,root,next}=>
            names.contains((child,dependencies.union(provided),provided,root))
                && (next.is_some() ==> names.contains((actor,keys,provisions,next.unwrap()))),
    }
}
pub open spec fn obligation<A,X,U,B,I>(lib:Library<A,X,U,B>,node:Node<A,X,U,B,I>,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,names:Names<I>)->bool {
    permitted(lib,keys,provisions,node) && continuations(lib,node,actor,keys,provisions,names)
}
pub open spec fn closed<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,names:Names<I>)->bool {
    forall|name:Name<I>| obligation(lib,programs(name.0)(name.3),name.0,name.1,name.2,names) ==> names.contains(name)
}
pub open spec fn member<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,id:I)->bool {
    forall|names:Names<I>| closed(lib,programs,names) ==> names.contains((actor,keys,provisions,id))
}
pub open spec fn members<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>)->Names<I> {
    ISet::new(|name:Name<I>|member(lib,programs,name.0,name.1,name.2,name.3))
}

pub proof fn continuations_monotone<A,X,U,B,I>(lib:Library<A,X,U,B>,node:Node<A,X,U,B,I>,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,a:Names<I>,b:Names<I>)
    requires a.subset_of(b),continuations(lib,node,actor,keys,provisions,a),
    ensures continuations(lib,node,actor,keys,provisions,b),
{
    match node {
        Node::Dependent {node}=>{
            assert(local(a,actor,keys,provisions).subset_of(local(b,actor,keys,provisions)));
            d::continuations_monotone(lib,node,local(a,actor,keys,provisions),local(b,actor,keys,provisions));
        },
        _=>{},
    }
}
pub proof fn constructor_member<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,id:I)
    requires obligation(lib,programs(actor)(id),actor,keys,provisions,members(lib,programs)),
    ensures member(lib,programs,actor,keys,provisions,id),
{
    assert forall|names:Names<I>| closed(lib,programs,names) implies names.contains((actor,keys,provisions,id)) by {
        assert(members(lib,programs).subset_of(names));
        continuations_monotone(lib,programs(actor)(id),actor,keys,provisions,members(lib,programs),names);
        assert(obligation(lib,programs(actor)(id),actor,keys,provisions,names));
    }
}
/// The least grammar unfolds without a rank or an encoding of `I` as naturals.
pub proof fn member_unfolding<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,id:I)
    ensures member(lib,programs,actor,keys,provisions,id)
        == obligation(lib,programs(actor)(id),actor,keys,provisions,members(lib,programs)),
{
    let all=members(lib,programs);
    if obligation(lib,programs(actor)(id),actor,keys,provisions,all) {constructor_member(lib,programs,actor,keys,provisions,id);}
    let good=ISet::new(|name:Name<I>|all.contains(name)
        && obligation(lib,programs(name.0)(name.3),name.0,name.1,name.2,all));
    assert(good.subset_of(all));
    assert(closed(lib,programs,good)) by {
        assert forall|name:Name<I>| obligation(lib,programs(name.0)(name.3),name.0,name.1,name.2,good) implies good.contains(name) by {
            continuations_monotone(lib,programs(name.0)(name.3),name.0,name.1,name.2,good,all);
            constructor_member(lib,programs,name.0,name.1,name.2,name.3);
        }
    }
    if member(lib,programs,actor,keys,provisions,id) {assert(good.contains((actor,keys,provisions,id)));}
}

/// A successful dependent landing selects a continuation of the same mixed
/// grammar, using the operation's actual typed outcome and the original `I`.
pub proof fn member_continuation<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,id:I,a:s::State<U>,actor:usize)
    requires d::primitive_theory(eq,lib),
        member(lib,programs,actor,dep::declarations(a,actor),a.control.fibers[actor].provisions,id),
        matches!(programs(actor)(id),Node::Dependent {..}),
        dep::run(lib,programs(actor)(id)->node,a,actor).is_some(),
    ensures dep::run(lib,programs(actor)(id)->node,a,actor).unwrap().next.is_some() ==>
        member(lib,programs,actor,dep::declarations(a,actor),a.control.fibers[actor].provisions,
            dep::run(lib,programs(actor)(id)->node,a,actor).unwrap().next.unwrap()),
{
    let keys=dep::declarations(a,actor);let provisions=a.control.fibers[actor].provisions;
    member_unfolding(lib,programs,actor,keys,provisions,id);
    let node=programs(actor)(id)->node;
    match node {
        d::Node::Operation {operation:op,argument:x,select}=>{
            let k=(lib.key)(op);let provider=lift::resolve(a,actor,k).unwrap();
            let y=(lib.apply)(op,x)(a.tables[provider][k]).unwrap();
            assert(d::operation_typed(lib,op,x));assert((lib.outcomes)(op,y.outcome));
            if select(y.outcome).is_some() {
                assert(local(members(lib,programs),actor,keys,provisions).contains(select(y.outcome).unwrap()));
            }
        },
        _=>{},
    }
}

pub open spec fn embed<A,X,U,B,I>(programs:dep::Programs<A,X,U,B,I>)->Programs<A,X,U,B,I> {
    |actor:usize| |id:I|Node::Dependent {node:programs(actor)(id)}
}
/// Adding the child constructor conservatively extends the original dependent
/// grammar: a registry of programs without child nodes has exactly its old
/// members, at every actor and declared interface.
pub proof fn dependent_embedding<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:dep::Programs<A,X,U,B,I>,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,id:I)
    ensures d::member(lib,programs(actor),keys,provisions,id)
        == member(lib,embed(programs),actor,keys,provisions,id),
{
    let mixed=embed(programs);
    if d::member(lib,programs(actor),keys,provisions,id) {
        assert forall|names:Names<I>| closed(lib,mixed,names) implies names.contains((actor,keys,provisions,id)) by {
            let here=local(names,actor,keys,provisions);
            assert(d::closed(lib,programs(actor),keys,provisions,here)) by {
                assert forall|i:I| d::permitted(lib,keys,provisions,programs(actor)(i))
                    && d::continuations(lib,programs(actor)(i),here) implies here.contains(i) by {
                    assert(obligation(lib,mixed(actor)(i),actor,keys,provisions,names));
                    assert(names.contains((actor,keys,provisions,i)));
                }
            }
            assert(here.contains(id));
        }
    }
    let good=ISet::new(|name:Name<I>|d::member(lib,programs(name.0),name.1,name.2,name.3));
    assert(closed(lib,mixed,good)) by {
        assert forall|name:Name<I>| obligation(lib,mixed(name.0)(name.3),name.0,name.1,name.2,good)
            implies good.contains(name) by {
            assert(local(good,name.0,name.1,name.2) =~= d::members(lib,programs(name.0),name.1,name.2));
            d::constructor_member(lib,programs(name.0),name.1,name.2,name.3);
        }
    }
    if member(lib,mixed,actor,keys,provisions,id) {assert(good.contains((actor,keys,provisions,id)));}
}

}
