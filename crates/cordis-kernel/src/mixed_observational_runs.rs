//! Actual mixed calls respect observations and retain their captured inverses.
//!
//! Control identities and table domains agree, while journal indices and raw
//! value representatives may differ. Undefined callbacks remain undefined;
//! raw outcomes retain the original, arbitrary continuation index.
#[cfg(verus_keep_ghost)]
use crate::{
    calculus, dependent_grammar as d, dependent_lift as dep, grammar_lift as lift, mediated as m,
    mixed_grammar as g, mixed_iteration_exchange as exchange, mixed_syntax as syntax,
    observation as o, observational_grammar as og, partial_independence as pi, preservation as inv,
    projection as p, semantics as s, Port,
};
use vstd::prelude::*;

verus! {

/// Journal tokens are deliberately absent: a separately justified renaming
/// relates their actual, potentially different history positions.
pub open spec fn tables_related<U>(eq:spec_fn(Port,U,U)->bool,a:s::State<U>,b:s::State<U>)->bool {
    &&& a.control==b.control
    &&& forall|id:usize| s::registered(a,id) ==> {
        &&& a.tables[id].dom()==b.tables[id].dom()
        &&& forall|key:Port| a.tables[id].dom().contains(key) ==> eq(key,a.tables[id][key],b.tables[id][key])
    }
}

pub open spec fn receipt_related<U>(eq:spec_fn(Port,U,U)->bool,left:g::Receipt<U>,right:g::Receipt<U>)->bool {
    match (left,right) {
        (g::Receipt::Table {receipt:a},g::Receipt::Table {receipt:b})=>a.actor==b.actor && match (a.inverse,b.inverse) {
            (lift::Inverse::Unit,lift::Inverse::Unit)=>true,
            (lift::Inverse::Operation {provider:p,key:k,undo:f},lift::Inverse::Operation {provider:q,key:j,undo:h})=>
                p==q && k==j && m::partial_related(|u:U,v:U|eq(k,u,v),f,h),
            (lift::Inverse::Provision {key:k},lift::Inverse::Provision {key:j})=>k==j,
            _=>false,
        },
        (g::Receipt::Child {actor:a,child:x},g::Receipt::Child {actor:b,child:y})=>a==b && x==y,
        _=>false,
    }
}

pub proof fn tables_reflexive<U>(eq:spec_fn(Port,U,U)->bool,a:s::State<U>)
    requires forall|key:Port| #[trigger] m::key_equivalence(eq,key),
    ensures tables_related(eq,a,a),
{
    assert forall|id:usize| s::registered(a,id) implies {
        &&& a.tables[id].dom()==a.tables[id].dom()
        &&& forall|key:Port| a.tables[id].dom().contains(key) ==> eq(key,a.tables[id][key],a.tables[id][key])
    } by {
        assert forall|key:Port| a.tables[id].dom().contains(key) implies eq(key,a.tables[id][key],a.tables[id][key]) by {
            assert(m::key_equivalence(eq,key));let local=|u:U,v:U|eq(key,u,v);
            assert(calculus::equivalence(local));assert(local(a.tables[id][key],a.tables[id][key]));
        }
    }
}

/// A returned inverse respects observation even if its raw representative is
/// not recovered literally. This is derived from the actual permitted call.
pub proof fn actual_receipt_reflexive<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,node:g::Node<A,X,U,B,I>,a:s::State<U>,actor:usize)
    requires og::primitive_theory(eq,lib),syntax::permitted(lib,dep::declarations(a,actor),a.control.fibers[actor].provisions,node),
        g::run(lib,node,a,actor).is_some(),
    ensures receipt_related(eq,g::run(lib,node,a,actor).unwrap().receipt,g::run(lib,node,a,actor).unwrap().receipt),
{
    tables_reflexive(eq,a);run_transport(eq,lib,node,a,a,actor);
}

pub proof fn update_related<U>(eq:spec_fn(Port,U,U)->bool,a:s::State<U>,b:s::State<U>,id:usize,key:Port,left:Option<U>,right:Option<U>)
    requires tables_related(eq,a,b),left.is_some()==right.is_some(),left.is_some() ==> eq(key,left.unwrap(),right.unwrap()),
    ensures tables_related(eq,p::update_slot(a,id,key,left),p::update_slot(b,id,key,right)),
{
    let x=p::update_slot(a,id,key,left);let y=p::update_slot(b,id,key,right);
    assert forall|n:usize| s::registered(x,n) implies {
        &&& x.tables[n].dom()==y.tables[n].dom()
        &&& forall|k:Port| x.tables[n].dom().contains(k) ==> eq(k,x.tables[n][k],y.tables[n][k])
    } by {
        assert(s::registered(a,n));
        if n==id {assert(x.tables[n].dom() =~= y.tables[n].dom());}
        assert forall|k:Port| x.tables[n].dom().contains(k) implies eq(k,x.tables[n][k],y.tables[n][k]) by {
            if n!=id || k!=key {assert(a.tables[n].dom().contains(k));}
        }
    }
}

/// Both contexts really resolve through the same installed commitment.
/// Availability of the target call follows from the source call and primitive
/// respect, including the actual raw outcome and returned partial inverse.
pub proof fn run_transport<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,node:g::Node<A,X,U,B,I>,a:s::State<U>,b:s::State<U>,actor:usize)
    requires og::primitive_theory(eq,lib),tables_related(eq,a,b),
        syntax::permitted(lib,dep::declarations(a,actor),a.control.fibers[actor].provisions,node),g::run(lib,node,a,actor).is_some(),
    ensures {
        let left=g::run(lib,node,a,actor).unwrap();let right=g::run(lib,node,b,actor).unwrap();
        &&& g::run(lib,node,b,actor).is_some()
        &&& tables_related(eq,left.state,right.state)
        &&& left.next==right.next && left.spawn==right.spawn
        &&& receipt_related(eq,left.receipt,right.receipt)
    },
{
    match node {
        g::Node::Dependent {node}=>{match node {
            d::Node::Unit=>{},
            d::Node::Operation {operation,argument,..}=>{
                let key=(lib.key)(operation);let op=(lib.apply)(operation,argument);
                let provider=lift::resolve(a,actor,key).unwrap();
                assert(lift::resolve(a,actor,key)==lift::resolve(b,actor,key));
                assert(s::registered(a,provider));assert(a.tables[provider].dom().contains(key));
                assert(eq(key,a.tables[provider][key],b.tables[provider][key]));
                assert(d::operation_typed(lib,operation,argument));
                assert(og::operation_respects(|u:U,v:U|eq(key,u,v),op));
                assert(op(a.tables[provider][key]).is_some());assert(op(b.tables[provider][key]).is_some());
                let x=op(a.tables[provider][key]).unwrap();let y=op(b.tables[provider][key]).unwrap();
                assert(x.outcome==y.outcome);
                update_related(eq,a,b,provider,key,Some(x.value),Some(y.value));
            },
            d::Node::Provision {key,value,..}=>{
                assert(m::key_equivalence(eq,key));let local=|u:U,v:U|eq(key,u,v);
                assert(calculus::equivalence(local));assert(local(value,value));
                update_related(eq,a,b,actor,key,Some(value),Some(value));
            },
        }},
        g::Node::Child {child,dependencies,provisions,..}=>{
            let x=g::create(a,actor,child,dependencies,provisions);let y=g::create(b,actor,child,dependencies,provisions);
            assert(x.control==y.control);
            assert forall|id:usize| s::registered(x,id) implies {
                &&& x.tables[id].dom()==y.tables[id].dom()
                &&& forall|key:Port| x.tables[id].dom().contains(key) ==> eq(key,x.tables[id][key],y.tables[id][key])
            } by {if id!=child {assert(s::registered(a,id));}}
        },
    }
}

/// Reassemble fixed-owner table observations into the paper's all-table view.
pub proof fn tables_to_projection<U>(eq:spec_fn(Port,U,U)->bool,a:s::State<U>,b:s::State<U>)
    requires inv::well_formed(a),inv::well_formed(b),tables_related(eq,a,b),
    ensures pi::context_eq(eq)(p::project(a,ISet::full()),p::project(b,ISet::full())),
{
    p::unique_owner(a);p::unique_owner(b);
    assert forall|key:Port| p::project(a,ISet::full()).dom().contains(key)==p::project(b,ISet::full()).dom().contains(key) by {
        if p::project(a,ISet::full()).dom().contains(key) {
            let id=choose|id:usize|p::owns(a,key,id);assert(p::owns(b,key,id));
        }
        if p::project(b,ISet::full()).dom().contains(key) {
            let id=choose|id:usize|p::owns(b,key,id);assert(s::registered(a,id));
            assert(a.tables[id].dom()==b.tables[id].dom());assert(p::owns(a,key,id));
        }
    }
    assert forall|key:Port| p::project(a,ISet::full()).dom().contains(key) implies
        eq(key,p::project(a,ISet::full())[key],p::project(b,ISet::full())[key]) by {
        let id=choose|id:usize|p::owns(a,key,id);assert(p::owns(b,key,id));
        p::lookup(a,ISet::full(),key,id);p::lookup(b,ISet::full(),key,id);
    }
}

/// Equal control fixes the owner even when the raw projected value differs.
pub proof fn projection_to_tables<U>(eq:spec_fn(Port,U,U)->bool,a:s::State<U>,b:s::State<U>)
    requires inv::well_formed(a),inv::well_formed(b),a.control==b.control,
        pi::context_eq(eq)(p::project(a,ISet::full()),p::project(b,ISet::full())),
    ensures tables_related(eq,a,b),
{
    p::unique_owner(a);p::unique_owner(b);
    assert forall|id:usize| s::registered(a,id) implies {
        &&& a.tables[id].dom()==b.tables[id].dom()
        &&& forall|key:Port| a.tables[id].dom().contains(key) ==> eq(key,a.tables[id][key],b.tables[id][key])
    } by {
        assert(a.tables[id].dom() =~= b.tables[id].dom()) by {
            assert forall|key:Port| a.tables[id].dom().contains(key)==b.tables[id].dom().contains(key) by {
                if a.tables[id].dom().contains(key) {
                    p::lookup(a,ISet::full(),key,id);
                    assert(p::project(b,ISet::full()).dom().contains(key));
                    let other=choose|n:usize|p::owns(b,key,n);
                    assert(a.control.fibers[id].provisions.contains(key));
                    assert(b.control.fibers[other].provisions.contains(key));assert(other==id);
                }
                if b.tables[id].dom().contains(key) {
                    p::lookup(b,ISet::full(),key,id);
                    assert(p::project(a,ISet::full()).dom().contains(key));
                    let other=choose|n:usize|p::owns(a,key,n);
                    assert(b.control.fibers[id].provisions.contains(key));
                    assert(a.control.fibers[other].provisions.contains(key));assert(other==id);
                }
            }
        }
        assert forall|key:Port| a.tables[id].dom().contains(key) implies eq(key,a.tables[id][key],b.tables[id][key]) by {
            p::lookup(a,ISet::full(),key,id);p::lookup(b,ISet::full(),key,id);
        }
    }
}

/// Testing singleton contexts extracts strict scalar inverse definedness and
/// output equivalence from the projected inverse relation.
pub proof fn inverse_from_projection<U>(eq:spec_fn(Port,U,U)->bool,key:Port,left:m::PartialMap<U>,right:m::PartialMap<U>)
    requires m::partial_related(pi::context_eq(eq),m::lift_inverse(key,left),m::lift_inverse(key,right)),
    ensures m::partial_related(|u:U,v:U|eq(key,u,v),left,right),
{
    let lf=m::lift_inverse(key,left);let rf=m::lift_inverse(key,right);
    assert forall|a:U,b:U| #![trigger left(a),right(b)] eq(key,a,b) implies {
        &&& left(a).is_some()==right(b).is_some()
        &&& (left(a).is_some() ==> eq(key,left(a).unwrap(),right(b).unwrap()))
    } by {
        let x=IMap::<Port,U>::empty().insert(key,a);let y=IMap::<Port,U>::empty().insert(key,b);
        assert(pi::context_eq(eq)(x,y));
        assert(lf(x).is_some()==rf(y).is_some());
        if left(a).is_some() {
            assert(pi::context_eq(eq)(lf(x).unwrap(),rf(y).unwrap()));
            assert(o::context_equal(eq,ISet::full(),lf(x).unwrap(),rf(y).unwrap()));
            assert(ISet::<Port>::full().contains(key));
            assert(lf(x).unwrap().dom().contains(key));
            assert(eq(key,lf(x).unwrap()[key],rf(y).unwrap()[key]));
        }
    }
}

/// The exchange theorem supplies names and actual projected receipts; this
/// bridge recovers the scalar relation needed by full-state strict recovery.
pub proof fn projected_receipts<U>(eq:spec_fn(Port,U,U)->bool,left:g::Receipt<U>,right:g::Receipt<U>)
    requires exchange::mixed_names(left,right),m::partial_related(pi::context_eq(eq),exchange::inverse(left),exchange::inverse(right)),
    ensures receipt_related(eq,left,right),
{
    if let g::Receipt::Table {receipt:a}=left {
        if let g::Receipt::Table {receipt:b}=right {
            if let lift::Inverse::Operation {key,undo:f,..}=a.inverse {
                if let lift::Inverse::Operation {undo:h,..}=b.inverse {inverse_from_projection(eq,key,f,h);}
            }
        }
    }
}

}
