//! A strict, indexed Component contract on the complete legal context carrier.
//!
//! This is an explicit revision of the paper's single total-map witness:
//! admission observes registry control; recovery observes service tables.
//! Child retirement restores the latter, not the former. No failed call is
//! converted to success. All roots, continuations and spawned roots are covered
//! independently of reachability from a particular execution.
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_grammar as d, dependent_lift as dep, fresh_grammar as f, fresh_semantics as fs,
    mixed_grammar as m, mixed_syntax as syntax, observational_grammar as og, preservation as inv,
    projection as p, refinement as r, semantics as s, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn carrier<A,X,U,B>(lib:f::Library<A,X,U,B>,a:s::State<U>)->bool {
    inv::well_formed(a) && dep::typed(lib,a) && dep::finite_context(a)
}
pub open spec fn interface<U>(a:s::State<U>,actor:usize,keys:ISet<Port>,provisions:ISet<Port>)->bool {
    s::registered(a,actor) && dep::declarations(a,actor)==keys && a.control.fibers[actor].provisions==provisions
}
/// Control fixes admission, ownership and committed resolution. Function
/// fields are interpreted separately, rather than compared as integer tokens.
pub open spec fn input_equal<U>(a:s::State<U>,b:s::State<U>)->bool {
    a.control==b.control && a.tables==b.tables
}
pub open spec fn recovery_equal<U>(a:s::State<U>,b:s::State<U>)->bool {
    p::project(a,ISet::full())==p::project(b,ISet::full())
}
pub open spec fn result_equal<U,I>(a:Option<m::Landed<U,I>>,b:Option<m::Landed<U,I>>)->bool {
    a.is_some()==b.is_some() && (a.is_some() ==> input_equal(a.unwrap().state,b.unwrap().state)
        && a.unwrap().receipt==b.unwrap().receipt && a.unwrap().next==b.unwrap().next && a.unwrap().spawn==b.unwrap().spawn)
}

/// Exact success/failure, outcome-selected continuation, fresh name, and the
/// actual returned inverse are preserved on every input, not just a trace.
pub proof fn strict_transport<A,X,U,B,I>(lib:f::Library<A,X,U,B>,node:f::Node<A,X,U,B,I>,a:s::State<U>,b:s::State<U>,actor:usize,choice:Option<usize>)
    requires input_equal(a,b),
    ensures result_equal(f::run(lib,node,a,actor,choice),f::run(lib,node,b,actor,choice)),
{
    match node {
        f::Node::Dependent {node}=>{match node {
            d::Node::Unit=>{},d::Node::Provision {..}=>{},d::Node::Operation {..}=>{},
        }},
        f::Node::FreshChild {..}=>{},
    }
}

/// Admission may inspect control; value reads are limited to the declared
/// interface. Unrelated service values may differ arbitrarily.
pub open spec fn declared_input<U>(keys:ISet<Port>,a:s::State<U>,b:s::State<U>)->bool {
    &&& a.control==b.control
    &&& forall|n:usize,key:Port| #![trigger a.tables[n].dom().contains(key)] #![trigger b.tables[n].dom().contains(key)]
        s::registered(a,n) && keys.contains(key) ==> {
        &&& a.tables[n].dom().contains(key)==b.tables[n].dom().contains(key)
        &&& (a.tables[n].dom().contains(key) ==> a.tables[n][key]==b.tables[n][key])
    }
}
pub open spec fn declared_result<U,I>(keys:ISet<Port>,a:Option<m::Landed<U,I>>,b:Option<m::Landed<U,I>>)->bool {
    a.is_some()==b.is_some() && (a.is_some() ==> declared_input(keys,a.unwrap().state,b.unwrap().state)
        && a.unwrap().receipt==b.unwrap().receipt && a.unwrap().next==b.unwrap().next && a.unwrap().spawn==b.unwrap().spawn)
}
pub proof fn update_declared<U>(keys:ISet<Port>,a:s::State<U>,b:s::State<U>,provider:usize,key:Port,value:Option<U>)
    requires declared_input(keys,a,b),
    ensures declared_input(keys,p::update_slot(a,provider,key,value),p::update_slot(b,provider,key,value)),
{
    let x=p::update_slot(a,provider,key,value);let y=p::update_slot(b,provider,key,value);
    assert forall|n:usize,k:Port| s::registered(x,n) && keys.contains(k) implies {
        &&& x.tables[n].dom().contains(k)==y.tables[n].dom().contains(k)
        &&& (x.tables[n].dom().contains(k) ==> x.tables[n][k]==y.tables[n][k])
    } by {if n!=provider || k!=key {assert(a.tables[n].dom().contains(k)==b.tables[n].dom().contains(k));}}
}
pub proof fn declared_transport<A,X,U,B,I>(lib:f::Library<A,X,U,B>,node:f::Node<A,X,U,B,I>,a:s::State<U>,b:s::State<U>,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,choice:Option<usize>)
    requires declared_input(keys,a,b),provisions.subset_of(keys),f::permitted(lib,keys,provisions,node),
    ensures declared_result(keys,f::run(lib,node,a,actor,choice),f::run(lib,node,b,actor,choice)),
{
    match node {
        f::Node::Dependent {node}=>{if choice.is_none() {match node {
            d::Node::Unit=>{},
            d::Node::Provision {key,value,..}=>{
                assert(keys.contains(key));
                if s::registered(a,actor) {assert(a.tables[actor].dom().contains(key)==b.tables[actor].dom().contains(key));}
                update_declared(keys,a,b,actor,key,Some(value));
            },
            d::Node::Operation {operation,argument,..}=>{
                let key=(lib.key)(operation);assert(keys.contains(key));
                let provider=crate::grammar_lift::resolve(a,actor,key);
                assert(provider==crate::grammar_lift::resolve(b,actor,key));
                if provider.is_some() && s::registered(a,provider.unwrap()) {
                    let n=provider.unwrap();assert(a.tables[n].dom().contains(key)==b.tables[n].dom().contains(key));
                    if a.tables[n].dom().contains(key) {
                        assert(a.tables[n][key]==b.tables[n][key]);
                        let out=(lib.apply)(operation,argument)(a.tables[n][key]);
                        if out.is_some() {update_declared(keys,a,b,n,key,Some(out.unwrap().value));}
                    }
                }
            },
        }}},
        f::Node::FreshChild {dependencies,provisions:provided,..}=>{if choice.is_some() {
            let child=choice.unwrap();
            let x=m::create(a,actor,child,dependencies,provided);let y=m::create(b,actor,child,dependencies,provided);
            assert(declared_input(keys,x,y)) by {
                assert forall|n:usize,key:Port| s::registered(x,n) && keys.contains(key) implies {
                    &&& x.tables[n].dom().contains(key)==y.tables[n].dom().contains(key)
                    &&& (x.tables[n].dom().contains(key) ==> x.tables[n][key]==y.tables[n][key])
                } by {if n!=child {assert(s::registered(a,n));}}
            }
        }},
    }
}

pub open spec fn stage_law<A,X,U,B,I>(lib:f::Library<A,X,U,B>,programs:f::Programs<A,X,U,B,I>,a:s::State<U>,actor:usize,id:I,choice:Option<usize>)->bool {
    match f::run(lib,programs(actor)(id),a,actor,choice) {
        None=>true,
        Some(out)=>{
            &&& carrier(lib,out.state) && inv::forward_map(a,out.state,actor)
            &&& m::owner(out.receipt)==actor && m::captured_child(out.receipt)==choice
            &&& m::receipt_typed(lib,out.receipt)
            &&& m::undo(out.receipt,out.state).is_some()
            &&& recovery_equal(m::undo(out.receipt,out.state).unwrap(),a)
            &&& forall|test:s::State<U>| carrier(lib,test) && m::undo(out.receipt,test).is_some()
                ==> carrier(lib,m::undo(out.receipt,test).unwrap()) && inv::inverse_map(test,m::undo(out.receipt,test).unwrap(),actor)
            &&& (out.next.is_some() ==> fs::component_member(lib,programs,a,actor,out.next.unwrap()))
            &&& (out.spawn.is_some() ==> fs::component_member(lib,programs,out.state,out.spawn.unwrap().0,out.spawn.unwrap().1))
            &&& (out.spawn.is_none() ==> out.state.control==a.control && out.state.effects==a.effects
                && out.state.iterators==a.iterators && out.state.accumulators==a.accumulators)
            &&& (out.spawn.is_some() ==> inv::child_map(a,out.state,actor,out.spawn.unwrap().0))
        },
    }
}

/// The carrier is every finite, typed, well-formed registry with this interface.
/// It is not the set of successful inputs or a single recorded execution.
pub open spec fn component<A,X,U,B,I>(lib:f::Library<A,X,U,B>,programs:f::Programs<A,X,U,B,I>,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,root:I)->bool {
    &&& f::member(lib,programs,actor,keys,provisions,root)
    &&& forall|a:s::State<U>,choice:Option<usize>| carrier(lib,a) && interface(a,actor,keys,provisions)
        ==> #[trigger] stage_law(lib,programs,a,actor,root,choice)
    &&& forall|a:s::State<U>,b:s::State<U>,choice:Option<usize>| interface(a,actor,keys,provisions) && declared_input(keys,a,b)
        ==> #[trigger] declared_result(keys,f::run(lib,programs(actor)(root),a,actor,choice),f::run(lib,programs(actor)(root),b,actor,choice))
    &&& forall|a:s::State<U>,b:s::State<U>,choice:Option<usize>| input_equal(a,b)
        ==> #[trigger] result_equal(f::run(lib,programs(actor)(root),a,actor,choice),f::run(lib,programs(actor)(root),b,actor,choice))
}

/// A semantic all-carrier witness, derived from constructor membership and
/// scalar primitive laws. In particular this covers the spawning parent.
pub proof fn member_is_component<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:f::Library<A,X,U,B>,programs:f::Programs<A,X,U,B,I>,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,root:I)
    requires d::primitive_theory(eq,lib),f::member(lib,programs,actor,keys,provisions,root),
    ensures component(lib,programs,actor,keys,provisions,root),
{
    og::exact_theory(eq,lib);
    f::member_unfolding(lib,programs,actor,keys,provisions,root);
    assert forall|a:s::State<U>,choice:Option<usize>| carrier(lib,a) && interface(a,actor,keys,provisions)
        implies #[trigger] stage_law(lib,programs,a,actor,root,choice) by {
        if f::run(lib,programs(actor)(root),a,actor,choice).is_some() {
            fs::run_members(eq,lib,programs,a,actor,root,choice);
            fs::run_admissible(eq,lib,programs(actor)(root),a,actor,choice);
            let concrete=f::instantiate(programs(actor)(root),choice).unwrap();
            assert(syntax::permitted(lib,keys,provisions,concrete)) by {
                match programs(actor)(root) {f::Node::Dependent {..}=>{},f::Node::FreshChild {..}=>{}}
            }
            m::run_admissible(eq,lib,concrete,a,actor);
            let out=f::run(lib,programs(actor)(root),a,actor,choice).unwrap();
            assert forall|test:s::State<U>| carrier(lib,test) && m::undo(out.receipt,test).is_some()
                implies carrier(lib,m::undo(out.receipt,test).unwrap()) && inv::inverse_map(test,m::undo(out.receipt,test).unwrap(),actor) by {
                m::inverse_preservation(lib,out.receipt,test);
            }
        }
    }
    assert forall|a:s::State<U>,b:s::State<U>,choice:Option<usize>| interface(a,actor,keys,provisions) && declared_input(keys,a,b)
        implies #[trigger] declared_result(keys,f::run(lib,programs(actor)(root),a,actor,choice),f::run(lib,programs(actor)(root),b,actor,choice)) by {
        assert(provisions.subset_of(keys));
        declared_transport(lib,programs(actor)(root),a,b,actor,keys,provisions,choice);
    }
    assert forall|a:s::State<U>,b:s::State<U>,choice:Option<usize>| input_equal(a,b)
        implies #[trigger] result_equal(f::run(lib,programs(actor)(root),a,actor,choice),f::run(lib,programs(actor)(root),b,actor,choice)) by {
        strict_transport(lib,programs(actor)(root),a,b,actor,choice);
    }
}

/// The same semantic witness holds at every actual continuation and at the
/// dynamically allocated child's root, rather than only at the initial root.
pub proof fn continuation_components<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:f::Library<A,X,U,B>,programs:f::Programs<A,X,U,B,I>,a:s::State<U>,actor:usize,root:I,choice:Option<usize>)
    requires d::primitive_theory(eq,lib),fs::component_member(lib,programs,a,actor,root),
        f::run(lib,programs(actor)(root),a,actor,choice).is_some(),
    ensures {
        let out=f::run(lib,programs(actor)(root),a,actor,choice).unwrap();
        &&& (out.next.is_some() ==> component(lib,programs,actor,dep::declarations(a,actor),a.control.fibers[actor].provisions,out.next.unwrap()))
        &&& (out.spawn.is_some() ==> component(lib,programs,out.spawn.unwrap().0,dep::declarations(out.state,out.spawn.unwrap().0),
            out.state.control.fibers[out.spawn.unwrap().0].provisions,out.spawn.unwrap().1))
    },
{
    og::exact_theory(eq,lib);fs::run_members(eq,lib,programs,a,actor,root,choice);
    let out=f::run(lib,programs(actor)(root),a,actor,choice).unwrap();
    if out.next.is_some() {member_is_component(eq,lib,programs,actor,dep::declarations(a,actor),a.control.fibers[actor].provisions,out.next.unwrap());}
    if out.spawn.is_some() {
        let (child,id)=out.spawn.unwrap();
        member_is_component(eq,lib,programs,child,dep::declarations(out.state,child),out.state.control.fibers[child].provisions,id);
    }
}

/// Unlike token equality, this compares the returned functions on all test
/// inputs, including ones on which the captured inverse is undefined.
pub proof fn returned_functions<A,X,U,B,I>(lib:f::Library<A,X,U,B>,node:f::Node<A,X,U,B,I>,a:s::State<U>,b:s::State<U>,actor:usize,choice:Option<usize>,test:s::State<U>)
    requires input_equal(a,b),f::run(lib,node,a,actor,choice).is_some(),
    ensures f::run(lib,node,b,actor,choice).is_some(),
        m::undo(f::run(lib,node,a,actor,choice).unwrap().receipt,test)==m::undo(f::run(lib,node,b,actor,choice).unwrap().receipt,test),
{strict_transport(lib,node,a,b,actor,choice);}

pub proof fn child_domain<A,X,U,B,I>(lib:f::Library<A,X,U,B>,a:s::State<U>,actor:usize,child:usize,dependencies:ISet<Port>,provisions:ISet<Port>,body:spec_fn(usize)->(I,Option<I>))
    ensures f::run(lib,f::Node::FreshChild {dependencies,provisions,body},a,actor,Some(child)).is_some()
        ==(!s::registered(a,child) && r::insertion_domain(a.control,Some(actor),provisions)),
{
    let z=m::create(a,actor,child,dependencies,provisions);
    assert(z.control.fibers.dom() =~= a.control.fibers.dom().insert(child));
}

} // verus!
