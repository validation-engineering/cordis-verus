//! Derive controlled partial bisimulation from the actual Table grammar.
//!
//! Static operation/argument/value validity and continuation closure suffice.
//! Tests range over every legal registered input, not only a chosen execution.
//! Both failed calls and every returned inverse's failure domain are preserved.
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_grammar as d, dependent_lift as dep, grammar_lift as lift, iterators as it,
    mediated as m, mixed_grammar as g, mixed_observational_runs as rows,
    mixed_observational_transport as mt, mixed_syntax as syntax, observation as o,
    observational_grammar as og, preservation as inv, quotient as q, semantics as s,
    strict_partial_quotient as controlled, Port,
};
use vstd::prelude::*;

verus! {

/// The declarations of a particular test state are not silently fixed. A call
/// which succeeds supplies its own key/declaration guard in `actual_permission`.
pub open spec fn closed_tables<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,actor:usize,names:ISet<I>)->bool {
    forall|id:I| names.contains(id) ==> match #[trigger] programs(actor)(id) {
        g::Node::Dependent {node}=>d::permitted(lib,ISet::full(),ISet::full(),node) && d::continuations(lib,node,names),
        _=>false,
    }
}

pub proof fn actual_permission<A,X,U,B,I>(lib:g::Library<A,X,U,B>,node:dep::Node<A,X,U,B,I>,a:s::State<U>,actor:usize)
    requires inv::well_formed(a),d::permitted(lib,ISet::full(),ISet::full(),node),dep::run(lib,node,a,actor).is_some(),
    ensures d::permitted(lib,dep::declarations(a,actor),a.control.fibers[actor].provisions,node),
{
    match node {
        d::Node::Operation {operation,..}=>{
            let key=(lib.key)(operation);lift::resolution_sound(a,actor,key);
            assert(a.control.fibers[actor].provisions.contains(key) || a.control.fibers[actor].dependencies.contains(key));
        },
        _=>{},
    }
}

/// Real outcomes select the original arbitrary-I continuation. No marker or
/// finite index encoding is used to justify membership of that continuation.
pub proof fn actual_continuation<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,node:dep::Node<A,X,U,B,I>,names:ISet<I>,a:s::State<U>,actor:usize)
    requires og::primitive_theory(eq,lib),d::permitted(lib,ISet::full(),ISet::full(),node),d::continuations(lib,node,names),dep::run(lib,node,a,actor).is_some(),
    ensures dep::run(lib,node,a,actor).unwrap().next.is_some() ==> names.contains(dep::run(lib,node,a,actor).unwrap().next.unwrap()),
{
    match node {
        d::Node::Operation {operation,argument,select}=>{
            let key=(lib.key)(operation);let provider=lift::resolve(a,actor,key).unwrap();
            let out=(lib.apply)(operation,argument)(a.tables[provider][key]).unwrap();
            assert(d::operation_typed(lib,operation,argument));assert((lib.outcomes)(operation,out.outcome));
            if select(out.outcome).is_some() {assert(names.contains(select(out.outcome).unwrap()));}
        },
        _=>{},
    }
}

pub proof fn inverse_pair<U>(eq:spec_fn(Port,U,U)->bool,actor:usize,left:lift::Receipt<U>,right:lift::Receipt<U>)
    requires forall|key:Port| #[trigger] m::key_equivalence(eq,key),
        rows::receipt_related(eq,g::Receipt::Table {receipt:left},g::Receipt::Table {receipt:right}),
        rows::receipt_related(eq,g::Receipt::Table {receipt:right},g::Receipt::Table {receipt:left}),
    ensures m::partial_related(controlled::input_relation(eq,actor),|a:s::State<U>|lift::undo(left,a),|a:s::State<U>|lift::undo(right,a)),
{
    assert forall|a:s::State<U>,b:s::State<U>| #![trigger lift::undo(left,a),lift::undo(right,b)] controlled::legal_input(eq,actor,a,b) implies {
        &&& lift::undo(left,a).is_some()==lift::undo(right,b).is_some()
        &&& (lift::undo(left,a).is_some() ==> controlled::legal_input(eq,actor,lift::undo(left,a).unwrap(),lift::undo(right,b).unwrap()))
    } by {
        controlled::legal_input_per(eq,actor,a,b,a);
        if lift::undo(left,a).is_some() {
            mt::undo_observations(eq,g::Receipt::Table {receipt:left},g::Receipt::Table {receipt:right},a,b);
            lift::undo_preservation(left,a);lift::undo_preservation(right,b);
        }
        if lift::undo(right,b).is_some() {
            mt::undo_observations(eq,g::Receipt::Table {receipt:right},g::Receipt::Table {receipt:left},b,a);
        }
    }
}

pub proof fn table_call<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,node:dep::Node<A,X,U,B,I>,actor:usize,a:s::State<U>,b:s::State<U>)
    requires og::primitive_theory(eq,lib),controlled::legal_input(eq,actor,a,b),d::permitted(lib,ISet::full(),ISet::full(),node),
    ensures {
        let left=dep::run(lib,node,a,actor);let right=dep::run(lib,node,b,actor);
        &&& left.is_some()==right.is_some()
        &&& (left.is_some() ==> {
            &&& controlled::legal_input(eq,actor,left.unwrap().state,right.unwrap().state)
            &&& left.unwrap().next==right.unwrap().next
            &&& m::partial_related(controlled::input_relation(eq,actor),
                |t:s::State<U>|lift::undo(left.unwrap().receipt,t),|t:s::State<U>|lift::undo(right.unwrap().receipt,t))
        })
    },
{
    controlled::legal_input_per(eq,actor,a,b,a);
    let mixed=g::Node::Dependent {node};
    if dep::run(lib,node,b,actor).is_some() {
        actual_permission(lib,node,b,actor);rows::run_transport(eq,lib,mixed,b,a,actor);
    }
    if dep::run(lib,node,a,actor).is_some() {
        actual_permission(lib,node,a,actor);rows::run_transport(eq,lib,mixed,a,b,actor);
        actual_permission(lib,node,b,actor);rows::run_transport(eq,lib,mixed,b,a,actor);
        dep::stage_projection(lib,node,a,actor);dep::stage_projection(lib,node,b,actor);
        lift::run_preservation(dep::stage(lib,node),a,actor);lift::run_preservation(dep::stage(lib,node),b,actor);
        inverse_pair(eq,actor,dep::run(lib,node,a,actor).unwrap().receipt,dep::run(lib,node,b,actor).unwrap().receipt);
    }
}

/// Even two different indices may denote the same node. Continuation closure
/// gives a concrete postfixed relation; self-respect is a conclusion.
#[verifier::spinoff_prover]
pub proof fn table_aliases<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,actor:usize,names:ISet<I>,left:I,right:I)
    requires og::primitive_theory(eq,lib),closed_tables(lib,programs,actor,names),names.contains(left),names.contains(right),programs(actor)(left)==programs(actor)(right),
    ensures controlled::iterator_related(eq,lib,programs,actor,left,right),
{
    let relation=controlled::input_relation(eq,actor);let base=|a:Option<s::State<U>>,b:Option<s::State<U>>|it::optional_eq(relation,a,b);
    let family=controlled::family(lib,programs,actor);let encoded=it::encode_partial(family);
    let aliases=|i:I,j:I|names.contains(i) && names.contains(j) && programs(actor)(i)==programs(actor)(j);
    assert(q::bisimulation(base,encoded,aliases)) by {
        assert forall|i:I,j:I,a:Option<s::State<U>>,b:Option<s::State<U>>| #![trigger encoded(i,a),encoded(j,b)] aliases(i,j) && base(a,b) implies {
            let x=encoded(i,a);let y=encoded(j,b);
            &&& base(x.state,y.state) && o::related_maps(base,x.undo,y.undo) && q::continuation(aliases,x.next,y.next)
        } by {
            match (a,b) {
                (Some(u),Some(v))=>{
                    let node=match programs(actor)(i) {g::Node::Dependent {node}=>node,_=>arbitrary()};
                    assert(programs(actor)(i)==g::Node::Dependent {node});
                    table_call(eq,lib,node,actor,u,v);
                    if family(i,u).is_some() {
                        let x=family(i,u).unwrap();let y=family(j,v).unwrap();
                        actual_continuation(eq,lib,node,names,u,actor);
                        let px=dep::run(lib,node,u,actor).unwrap();let py=dep::run(lib,node,v,actor).unwrap();
                        assert(x.undo =~= (|t:s::State<U>|lift::undo(px.receipt,t)));
                        assert(y.undo =~= (|t:s::State<U>|lift::undo(py.receipt,t)));
                        assert(m::partial_related(relation,x.undo,y.undo));it::partial_inverse_encoding(relation,x.undo,y.undo);
                        assert(x.next==y.next);
                        if x.next.is_some() {let k=x.next.unwrap();assert(names.contains(k));assert(aliases(k,k));}
                    }
                },
                _=>{},
            }
        }
    }
    assert(aliases(left,right));
}

pub proof fn table_reflexive<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,actor:usize,names:ISet<I>,root:I)
    requires og::primitive_theory(eq,lib),closed_tables(lib,programs,actor,names),names.contains(root),
    ensures controlled::iterator_related(eq,lib,programs,actor,root,root),
{table_aliases(eq,lib,programs,actor,names,root,root);}

/// Least dependent membership supplies the continuation-closed set used above.
/// Static declaration bounds may be arbitrary; test-state domains still come
/// from the real interpreter, not a restriction to that component's own traces.
pub proof fn least_member<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,program:d::Program<Port,A,X,U,B,I>,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,root:I)
    requires og::primitive_theory(eq,lib),d::member(lib,program,keys,provisions,root),
        forall|id:I| #[trigger] programs(actor)(id)==(g::Node::Dependent {node:program(id)}),
    ensures controlled::iterator_related(eq,lib,programs,actor,root,root),
{
    let names=d::members(lib,program,keys,provisions);
    assert(closed_tables(lib,programs,actor,names)) by {
        assert forall|id:I| names.contains(id) implies match #[trigger] programs(actor)(id) {
            g::Node::Dependent {node}=>d::permitted(lib,ISet::full(),ISet::full(),node) && d::continuations(lib,node,names),
            _=>false,
        } by {d::member_unfolding(lib,program,keys,provisions,id);}
    }
    table_reflexive(eq,lib,programs,actor,names,root);
}

}
