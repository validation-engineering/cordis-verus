//! Guard-aware external orchestration across actual mixed landings.
//!
//! Continuation choices and inverse receipts come from the original interpreter.
//! This module constructs local reverse executions and transports given finite
//! suffixes; it does not assert a global canonical form or arbitrary callbacks.
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_grammar as d, dependent_lift as dep, grammar_lift as lift, mixed_grammar as g,
    mixed_transport as transport, mixed_transposition as t, observational_grammar as og,
    observational_lift as ol, preservation as inv, refinement as r, semantics as s, Binding, Port,
};
use vstd::prelude::*;

verus! {

/// A later insertion may only read a parent name that already existed before
/// the landing. Its remaining guards are supplied by the real later Insert.
pub open spec fn parent_present<U,I>(a:g::Configuration<U,I>,parent:Option<usize>)->bool {
    match parent {None=>true,Some(p)=>s::registered(a.state,p)}
}

/// Reconstruct an actual external Insert from its independent transition rule.
pub proof fn insertion_form<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,id:usize)
    requires g::step(lib,programs,a,z,id,r::Rule::Insert),
    ensures {
        let f=z.state.control.fibers[id];
        &&& z==t::insert(a,id,f.parent,f.dependencies,f.provisions,z.roots[id])
        &&& t::insertion_ready(lib,programs,a,id,f.parent,f.dependencies,f.provisions,z.roots[id])
    },
{
    let f=z.state.control.fibers[id];let canonical=t::insert(a,id,f.parent,f.dependencies,f.provisions,z.roots[id]);
    assert(r::step(a.state.control,z.state.control,id,r::Rule::Insert));
    assert(f.committed =~= ISet::<Binding>::empty());
    assert(f==canonical.state.control.fibers[id]);
    assert(z.state.control.fibers.dom() =~= canonical.state.control.fibers.dom()) by {
        assert forall|n:usize| z.state.control.fibers.dom().contains(n)==canonical.state.control.fibers.dom().contains(n) by {
            if n!=id {assert(r::frame(a.state.control,z.state.control,id));assert(s::registered(a.state,n)==s::registered(z.state,n));}
        }
    }
    assert(z.state.control.fibers =~= canonical.state.control.fibers) by {
        assert forall|n:usize| z.state.control.fibers.dom().contains(n) implies z.state.control.fibers[n]==canonical.state.control.fibers[n] by {
            if n!=id {assert(r::frame(a.state.control,z.state.control,id));assert(s::registered(a.state,n));}
        }
    }
    assert(z==canonical);
}

/// A fresh Inactive empty entry cannot change the committed resolution, raw
/// operation input, chosen arbitrary continuation, or captured table inverse.
pub proof fn dependent_insert_run<A,X,U,B,I>(lib:g::Library<A,X,U,B>,node:d::Node<Port,A,X,U,B,I>,a:g::Configuration<U,I>,actor:usize,
    id:usize,parent:Option<usize>,dependencies:ISet<Port>,provisions:ISet<Port>,root:I)
    requires inv::well_formed(a.state),!s::registered(a.state,id),dep::run(lib,node,a.state,actor).is_some(),
    ensures {
        let middle=t::insert(a,id,parent,dependencies,provisions,root);
        let old=dep::run(lib,node,a.state,actor).unwrap();let new=dep::run(lib,node,middle.state,actor).unwrap();
        let out=g::Configuration {state:old.state,roots:a.roots,current:a.current,history:a.history};
        &&& dep::run(lib,node,middle.state,actor).is_some()
        &&& new.receipt==old.receipt && new.next==old.next
        &&& new.state==t::insert(out,id,parent,dependencies,provisions,root).state
    },
{
    let middle=t::insert(a,id,parent,dependencies,provisions,root);
    assert(s::registered(a.state,actor));assert(actor!=id);
    match node {
        d::Node::Operation {operation,argument,..}=>{
            let key=(lib.key)(operation);
            assert(lift::resolve(a.state,actor,key)==lift::resolve(middle.state,actor,key));
            lift::resolution_sound(a.state,actor,key);
            let provider=lift::resolve(a.state,actor,key).unwrap();assert(provider!=id);
            assert(a.state.tables[provider]==middle.state.tables[provider]);
        },
        _=>{},
    }
    let old=dep::run(lib,node,a.state,actor).unwrap();let new=dep::run(lib,node,middle.state,actor).unwrap();
    let out=g::Configuration {state:old.state,roots:a.roots,current:a.current,history:a.history};
    assert(new.state.tables =~= t::insert(out,id,parent,dependencies,provisions,root).state.tables);
}

/// Insertion crosses every mixed Node, including real dependent Operations.
/// Freshness and provision exclusion are derived from the observed second
/// Insert; only its causal parent-name read is checked in the original state.
pub proof fn insert_diamond<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,b:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,id:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,b,actor,rule),g::landing(a,b,rule),
        g::step(lib,programs,b,z,id,r::Rule::Insert),parent_present(a,z.state.control.fibers[id].parent),
    ensures {
        let f=z.state.control.fibers[id];let middle=t::insert(a,id,f.parent,f.dependencies,f.provisions,z.roots[id]);
        let reverse=g::land(lib,programs,middle,actor,t::landing_phase(rule));
        &&& g::step(lib,programs,a,middle,id,r::Rule::Insert) && g::step(lib,programs,middle,reverse,actor,rule)
        &&& transport::related(z,reverse)
        &&& g::well_formed(lib,programs,middle) && g::well_formed(lib,programs,reverse)
        &&& z.history.last().input==a.state && reverse.history.last().input==middle.state
        &&& z.history.last().landed.receipt==reverse.history.last().landed.receipt
    },
{
    insertion_form(lib,programs,b,z,id);
    ol::frame(eq,lib,programs,a,b,actor,rule);
    ol::run_members(eq,lib,programs,a.state,actor,a.current[actor].unwrap());
    let f=z.state.control.fibers[id];let middle=t::insert(a,id,f.parent,f.dependencies,f.provisions,z.roots[id]);
    let reverse=g::land(lib,programs,middle,actor,t::landing_phase(rule));
    assert(b==g::land(lib,programs,a,actor,t::landing_phase(rule)));
    assert(!s::registered(a.state,id));assert(actor!=id);
    assert forall|n:usize,k:Port| s::registered(a.state,n) && a.state.control.fibers[n].provisions.contains(k) implies !f.provisions.contains(k) by {
        assert(s::registered(b.state,n));assert(b.state.control.fibers[n].provisions.contains(k));
    }
    assert(t::insertion_ready(lib,programs,a,id,f.parent,f.dependencies,f.provisions,z.roots[id]));
    t::insertion_step(lib,programs,a,id,f.parent,f.dependencies,f.provisions,z.roots[id]);
    t::insertion_target(a,id,f.parent,f.dependencies,f.provisions,z.roots[id],actor,a.state.control.fibers[actor].committed);
    match programs(actor)(a.current[actor].unwrap()) {
        g::Node::Child {child,dependencies,provisions,..}=>{
            assert(!s::registered(a.state,child));assert(s::registered(b.state,child));assert(child!=id);
            let context=g::create(middle.state,actor,child,dependencies,provisions);
            assert(r::frame(middle.state.control,context.control,child));
            assert forall|n:usize,k:Port| s::registered(middle.state,n) && middle.state.control.fibers[n].provisions.contains(k)
                implies !provisions.contains(k) by {
                if n==id {if provisions.contains(k) {assert(b.state.control.fibers[child].provisions.contains(k));assert(!f.provisions.contains(k));}}
                else {assert(s::registered(a.state,n));}
            }
            assert(r::step(middle.state.control,context.control,child,r::Rule::Insert));
        },
        g::Node::Dependent {node}=>{
            ol::dependent_run_admissible(eq,lib,node,a.state,actor);
            dependent_insert_run(lib,node,a,actor,id,f.parent,f.dependencies,f.provisions,z.roots[id]);
        },
    }
    assert(g::step(lib,programs,middle,reverse,actor,rule));
    assert(z.state.control.fibers =~= reverse.state.control.fibers);
    assert(z.state.tables =~= reverse.state.tables);assert(z.state.effects =~= reverse.state.effects);
    assert(z.state.iterators =~= reverse.state.iterators);assert(z.state.accumulators =~= reverse.state.accumulators);
    assert(z.roots =~= reverse.roots);assert(z.current =~= reverse.current);
    assert(t::same_receipts(z,reverse)) by {
        assert forall|i:int| 0<=i<z.history.len() implies {
            &&& z.history[i].iterator==reverse.history[i].iterator
            &&& z.history[i].landed.receipt==reverse.history[i].landed.receipt
            &&& z.history[i].landed.next==reverse.history[i].landed.next
            &&& z.history[i].landed.spawn==reverse.history[i].landed.spawn
        } by {if i<a.history.len() {assert(z.history[i]==a.history[i]);assert(reverse.history[i]==a.history[i]);} else {assert(i==a.history.len());}}
    }
    ol::configuration_preservation(eq,lib,programs,a,middle,id,r::Rule::Insert);
    ol::configuration_preservation(eq,lib,programs,middle,reverse,actor,rule);
}

pub proof fn insert_suffix<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,b:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,id:usize,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,b,actor,rule),g::landing(a,b,rule),
        g::step(lib,programs,b,z,id,r::Rule::Insert),parent_present(a,z.state.control.fibers[id].parent),
        g::execution(lib,programs,source,labels),source.first()==z,
    ensures {
        let f=z.state.control.fibers[id];let middle=t::insert(a,id,f.parent,f.dependencies,f.provisions,z.roots[id]);
        let reverse=g::land(lib,programs,middle,actor,t::landing_phase(rule));let moved=transport::transport(source,labels,reverse);
        &&& g::step(lib,programs,a,middle,id,r::Rule::Insert) && g::step(lib,programs,middle,reverse,actor,rule)
        &&& moved.first()==reverse && moved.len()==source.len() && g::execution(lib,programs,moved,labels)
        &&& forall|i:int| 0<=i<source.len() ==> transport::related(source[i],moved[i]) && g::well_formed(lib,programs,moved[i])
    },
{
    insert_diamond(eq,lib,programs,a,b,z,actor,rule,id);
    let f=z.state.control.fibers[id];let middle=t::insert(a,id,f.parent,f.dependencies,f.provisions,z.roots[id]);
    let reverse=g::land(lib,programs,middle,actor,t::landing_phase(rule));
    transport::suffix_transport(lib,programs,source,labels,reverse);transport::observational_safe_suffix(eq,lib,programs,source,labels,reverse);
}

/// A concrete real Operation changes 7 to 12 while an unrelated nonempty
/// declaration is inserted. Both orders preserve the actual subtraction receipt.
pub proof fn actual_operation_insert()
    ensures {
        let a=crate::recovery_examples::trace()[7];let b=crate::recovery_examples::trace()[8];
        let lib=crate::recovery_examples::library();let programs=crate::recovery_examples::programs();
        let z=t::insert(b,2,Some(0),ISet::empty(),crate::recovery_examples::provided(2),crate::recovery_examples::Stage::Spawn);
        let middle=t::insert(a,2,Some(0),ISet::empty(),crate::recovery_examples::provided(2),crate::recovery_examples::Stage::Spawn);
        let reverse=g::land(lib,programs,middle,0,crate::Phase::Active);
        &&& g::step(lib,programs,a,b,0,r::Rule::Finish) && g::step(lib,programs,b,z,2,r::Rule::Insert)
        &&& g::step(lib,programs,a,middle,2,r::Rule::Insert) && g::step(lib,programs,middle,reverse,0,r::Rule::Finish)
        &&& transport::related(z,reverse) && z.history!=reverse.history
        &&& a.state.tables[0usize][crate::recovery_examples::key(0)]==7 && z.state.tables[0usize][crate::recovery_examples::key(0)]==12
        &&& z.history.last().landed.receipt==(g::Receipt::Table {receipt:lift::Receipt {actor:0usize,
            inverse:lift::Inverse::Operation {provider:0usize,key:crate::recovery_examples::key(0),undo:|v:int|Some(v-5)}}})
    },
{
    crate::recovery_examples::actual_execution();crate::recovery_examples::primitive_theory();
    og::exact_theory(crate::recovery_examples::equality(),crate::recovery_examples::library());
    let lib=crate::recovery_examples::library();let programs=crate::recovery_examples::programs();
    ol::from_empty_safe(crate::recovery_examples::equality(),lib,programs,crate::recovery_examples::trace(),crate::recovery_examples::labels());
    reveal(crate::recovery_examples::trace);
    let a=crate::recovery_examples::trace()[7];let b=crate::recovery_examples::trace()[8];
    let root=crate::recovery_examples::Stage::Spawn;let provided=crate::recovery_examples::provided(2);
    crate::mixed_syntax::constructor_member(lib,programs,2,provided,provided,root);
    assert(ISet::<Port>::empty().union(provided) =~= provided);
    assert(t::insertion_ready(lib,programs,b,2,Some(0),ISet::empty(),provided,root));
    t::insertion_step(lib,programs,b,2,Some(0),ISet::empty(),provided,root);
    let z=t::insert(b,2,Some(0),ISet::empty(),provided,root);
    insert_diamond(crate::recovery_examples::equality(),lib,programs,a,b,z,0,r::Rule::Finish,2);
    let middle=t::insert(a,2,Some(0),ISet::empty(),provided,root);let reverse=g::land(lib,programs,middle,0,crate::Phase::Active);
    assert(!s::registered(z.history.last().input,2));assert(s::registered(reverse.history.last().input,2));
}

pub open spec fn retire<U,I>(a:g::Configuration<U,I>,id:usize)->g::Configuration<U,I> {
    g::Configuration {state:s::with_control(a.state,crate::global::retire_fiber(a.state.control,id)),
        roots:a.roots,current:a.current,history:a.history}
}

/// Retirement of a different actor preserves current publication, including
/// that of the retired provider. The flag does not participate in publication.
pub proof fn retire_target<U,I>(a:g::Configuration<U,I>,id:usize,actor:usize,view:ISet<Binding>)
    requires s::registered(a.state,id),s::registered(a.state,actor),id!=actor,
    ensures s::target(a.state,actor,view)==s::target(retire(a,id).state,actor,view),
        s::coherent(a.state,actor)==s::coherent(retire(a,id).state,actor),
{
    let z=retire(a,id);
    assert forall|key:Port,n:usize| s::publishes(a.state,key,n)==s::publishes(z.state,key,n) by { }
}

pub proof fn retire_run<A,X,U,B,I>(lib:g::Library<A,X,U,B>,node:g::Node<A,X,U,B,I>,a:g::Configuration<U,I>,actor:usize,id:usize)
    requires s::registered(a.state,id),id!=actor,g::run(lib,node,a.state,actor).is_some(),
    ensures {
        let middle=retire(a,id);let old=g::run(lib,node,a.state,actor).unwrap();let new=g::run(lib,node,middle.state,actor).unwrap();
        let out=g::Configuration {state:old.state,roots:a.roots,current:a.current,history:a.history};
        &&& g::run(lib,node,middle.state,actor).is_some()
        &&& new.receipt==old.receipt && new.next==old.next && new.spawn==old.spawn
        &&& new.state==retire(out,id).state
    },
{
    let middle=retire(a,id);
    match node {
        g::Node::Dependent {node}=>{match node {
            d::Node::Operation {operation,..}=>{
                let key=(lib.key)(operation);assert(lift::resolve(a.state,actor,key)==lift::resolve(middle.state,actor,key));
            },
            _=>{},
        }},
        g::Node::Child {child,dependencies,provisions,..}=>{
            assert(!s::registered(a.state,child));assert(child!=id);
            let created=g::create(middle.state,actor,child,dependencies,provisions);
            assert(r::frame(middle.state.control,created.control,child));
            assert(r::step(middle.state.control,created.control,child,r::Rule::Insert));
            assert(created.control.fibers =~= retire(g::Configuration {state:g::create(a.state,actor,child,dependencies,provisions),
                roots:a.roots,current:a.current,history:a.history},id).state.control.fibers);
        },
    }
}

/// Every Node commutes with retirement of an already registered other name.
/// Retiring the landing actor itself or its just-created child is deliberately
/// excluded by explicit name reads, not by assuming the reverse transition.
pub proof fn retire_diamond<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,b:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,id:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,b,actor,rule),g::landing(a,b,rule),
        g::step(lib,programs,b,z,id,r::Rule::Retire),s::registered(a.state,id),id!=actor,
    ensures {
        let middle=retire(a,id);let reverse=g::land(lib,programs,middle,actor,t::landing_phase(rule));
        &&& g::step(lib,programs,a,middle,id,r::Rule::Retire) && g::step(lib,programs,middle,reverse,actor,rule)
        &&& transport::related(z,reverse) && g::well_formed(lib,programs,middle) && g::well_formed(lib,programs,reverse)
        &&& z.history.last().input==a.state && reverse.history.last().input==middle.state
        &&& z.history.last().landed.receipt==reverse.history.last().landed.receipt
    },
{
    ol::frame(eq,lib,programs,a,b,actor,rule);
    let middle=retire(a,id);let reverse=g::land(lib,programs,middle,actor,t::landing_phase(rule));
    assert(r::step(b.state.control,z.state.control,id,r::Rule::Retire));
    assert(z.state.control.fibers.dom() =~= retire(b,id).state.control.fibers.dom()) by {
        assert forall|n:usize| z.state.control.fibers.dom().contains(n)==retire(b,id).state.control.fibers.dom().contains(n) by {
            if n!=id {assert(r::frame(b.state.control,z.state.control,id));assert(s::registered(z.state,n)==s::registered(b.state,n));}
        }
    }
    assert(z.state.control.fibers =~= retire(b,id).state.control.fibers) by {
        assert forall|n:usize| z.state.control.fibers.dom().contains(n) implies z.state.control.fibers[n]==retire(b,id).state.control.fibers[n] by {
            if n!=id {assert(r::frame(b.state.control,z.state.control,id));assert(s::registered(b.state,n));}
        }
    }
    assert(z==retire(b,id));
    crate::child_history::concrete_child_retirement(a.state,id);
    assert(g::step(lib,programs,a,middle,id,r::Rule::Retire));
    retire_target(a,id,actor,a.state.control.fibers[actor].committed);
    retire_run(lib,programs(actor)(a.current[actor].unwrap()),a,actor,id);
    assert(g::step(lib,programs,middle,reverse,actor,rule));
    assert(z.state.control.fibers =~= reverse.state.control.fibers);
    assert(t::same_receipts(z,reverse)) by {
        assert forall|i:int| 0<=i<z.history.len() implies {
            &&& z.history[i].iterator==reverse.history[i].iterator
            &&& z.history[i].landed.receipt==reverse.history[i].landed.receipt
            &&& z.history[i].landed.next==reverse.history[i].landed.next
            &&& z.history[i].landed.spawn==reverse.history[i].landed.spawn
        } by {if i<a.history.len() {assert(z.history[i]==a.history[i]);assert(reverse.history[i]==a.history[i]);} else {assert(i==a.history.len());}}
    }
    ol::configuration_preservation(eq,lib,programs,a,middle,id,r::Rule::Retire);
    ol::configuration_preservation(eq,lib,programs,middle,reverse,actor,rule);
}

pub proof fn retire_suffix<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,b:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,id:usize,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,b,actor,rule),g::landing(a,b,rule),
        g::step(lib,programs,b,z,id,r::Rule::Retire),s::registered(a.state,id),id!=actor,
        g::execution(lib,programs,source,labels),source.first()==z,
    ensures {
        let middle=retire(a,id);let reverse=g::land(lib,programs,middle,actor,t::landing_phase(rule));let moved=transport::transport(source,labels,reverse);
        &&& g::step(lib,programs,a,middle,id,r::Rule::Retire) && g::step(lib,programs,middle,reverse,actor,rule)
        &&& moved.first()==reverse && moved.len()==source.len() && g::execution(lib,programs,moved,labels)
        &&& forall|i:int| 0<=i<source.len() ==> transport::related(source[i],moved[i]) && g::well_formed(lib,programs,moved[i])
    },
{
    retire_diamond(eq,lib,programs,a,b,z,actor,rule,id);
    let reverse=g::land(lib,programs,retire(a,id),actor,t::landing_phase(rule));
    transport::suffix_transport(lib,programs,source,labels,reverse);transport::observational_safe_suffix(eq,lib,programs,source,labels,reverse);
}

pub open spec fn remove<U,I>(a:g::Configuration<U,I>,id:usize)->g::Configuration<U,I> {
    g::Configuration {state:s::erase(a.state,id),roots:a.roots.remove(id),current:a.current.remove(id),history:a.history}
}

pub proof fn remove_target<U,I>(a:g::Configuration<U,I>,id:usize,actor:usize,view:ISet<Binding>)
    requires s::registered(a.state,id),a.state.control.fibers[id].phase==crate::Phase::Inactive,
        s::registered(a.state,actor),id!=actor,
    ensures s::target(a.state,actor,view)==s::target(remove(a,id).state,actor,view),
        s::coherent(a.state,actor)==s::coherent(remove(a,id).state,actor),
{
    let z=remove(a,id);
    assert forall|key:Port,n:usize| s::publishes(a.state,key,n)==s::publishes(z.state,key,n) by {if n==id {assert(!s::publishes(a.state,key,n));}}
}

/// A removable Inactive entry cannot be the installed provider of a successful
/// operation in a well-formed state. Deletion therefore preserves its real
/// input and outcome without any assumption on the operation implementation.
pub proof fn remove_run<A,X,U,B,I>(lib:g::Library<A,X,U,B>,node:g::Node<A,X,U,B,I>,a:g::Configuration<U,I>,actor:usize,id:usize)
    requires inv::well_formed(a.state),s::registered(a.state,id),a.state.control.fibers[id].phase==crate::Phase::Inactive,
        id!=actor,g::run(lib,node,a.state,actor).is_some(),
    ensures {
        let middle=remove(a,id);let old=g::run(lib,node,a.state,actor).unwrap();let new=g::run(lib,node,middle.state,actor).unwrap();
        let out=g::Configuration {state:old.state,roots:a.roots,current:a.current,history:a.history};
        &&& g::run(lib,node,middle.state,actor).is_some()
        &&& new.receipt==old.receipt && new.next==old.next && new.spawn==old.spawn
        &&& new.state==remove(out,id).state && old.state.tables[id]==a.state.tables[id]
    },
{
    let middle=remove(a,id);
    match node {
        g::Node::Dependent {node}=>{match node {
            d::Node::Operation {operation,..}=>{
                let key=(lib.key)(operation);assert(lift::resolve(a.state,actor,key)==lift::resolve(middle.state,actor,key));
                lift::resolution_sound(a.state,actor,key);let provider=lift::resolve(a.state,actor,key).unwrap();
                if provider!=actor {assert(a.state.control.fibers[actor].committed.contains(Binding {key:key.key,realm:key.realm,provider}));
                    assert(a.state.control.fibers[provider].phase!=crate::Phase::Inactive);}
                assert(provider!=id);
            },
            _=>{},
        }},
        g::Node::Child {child,dependencies,provisions,..}=>{
            assert(!s::registered(a.state,child));assert(child!=id);
            let created=g::create(middle.state,actor,child,dependencies,provisions);
            assert(r::frame(middle.state.control,created.control,child));
            assert(r::step(middle.state.control,created.control,child,r::Rule::Insert));
            assert(created.control.fibers =~= remove(g::Configuration {state:g::create(a.state,actor,child,dependencies,provisions),
                roots:a.roots,current:a.current,history:a.history},id).state.control.fibers);
        },
    }
    let old=g::run(lib,node,a.state,actor).unwrap();let new=g::run(lib,node,middle.state,actor).unwrap();
    assert(new.state.tables =~= old.state.tables.remove(id));
    assert(new.state.effects =~= old.state.effects.remove(id));
    assert(new.state.iterators =~= old.state.iterators.remove(id));
    assert(new.state.accumulators =~= old.state.accumulators.remove(id));
}

/// Forward landings never retire an old name or change another old name's
/// phase. Every newly born child is unretired. These are interpreter facts,
/// stronger than the resource-safety projection alone.
pub proof fn landing_names<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,b:g::Configuration<U,I>,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,b,actor,rule),g::landing(a,b,rule),
    ensures
        forall|n:usize| s::registered(a.state,n) && n!=actor ==> b.state.control.fibers[n]==a.state.control.fibers[n],
        forall|n:usize| s::registered(b.state,n) && !s::registered(a.state,n) ==> !b.state.control.fibers[n].retired,
        b.state.control.fibers[actor].phase!=crate::Phase::Inactive,
{
    ol::frame(eq,lib,programs,a,b,actor,rule);
    assert forall|n:usize| s::registered(a.state,n) && n!=actor implies b.state.control.fibers[n]==a.state.control.fibers[n] by { }
    assert forall|n:usize| s::registered(b.state,n) && !s::registered(a.state,n) implies !b.state.control.fibers[n].retired by {
        assert(g::entry(lib,programs,a,actor).landed.spawn.is_some());
    }
}

/// Unlike Retire, a legal post-landing Remove already supplies every required
/// name-read exclusion: its target is old, Inactive, empty, parent-free and has
/// no outstanding child inverse reference. Those facts are derived here.
pub proof fn remove_diamond<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,b:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,id:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,b,actor,rule),g::landing(a,b,rule),
        g::step(lib,programs,b,z,id,r::Rule::Remove),
    ensures {
        let middle=remove(a,id);let reverse=g::land(lib,programs,middle,actor,t::landing_phase(rule));
        &&& s::registered(a.state,id) && id!=actor && a.state.control.fibers[id].phase==crate::Phase::Inactive
        &&& g::step(lib,programs,a,middle,id,r::Rule::Remove) && g::step(lib,programs,middle,reverse,actor,rule)
        &&& transport::related(z,reverse) && g::well_formed(lib,programs,middle) && g::well_formed(lib,programs,reverse)
        &&& z.history.last().input==a.state && reverse.history.last().input==middle.state
        &&& z.history.last().landed.receipt==reverse.history.last().landed.receipt
    },
{
    ol::frame(eq,lib,programs,a,b,actor,rule);landing_names(eq,lib,programs,a,b,actor,rule);
    let middle=remove(a,id);let reverse=g::land(lib,programs,middle,actor,t::landing_phase(rule));
    assert(r::step(b.state.control,z.state.control,id,r::Rule::Remove));
    assert(z==remove(b,id));assert(id!=actor);assert(s::registered(a.state,id));
    assert(b.state.control.fibers[id]==a.state.control.fibers[id]);
    assert(a.state.control.fibers[id].phase==crate::Phase::Inactive);
    assert(a.state.control.fibers[id].retired);assert(a.state.control.fibers[id].committed.is_empty());
    remove_run(lib,programs(actor)(a.current[actor].unwrap()),a,actor,id);
    assert(a.state.tables[id].is_empty());
    assert(r::frame(a.state.control,middle.state.control,id));
    assert(!s::registered(middle.state,id));
    assert forall|n:usize| r::registered(a.state.control,n) implies a.state.control.fibers[n].parent!=Some(id) by {
        assert(s::registered(b.state,n));assert(r::interface_same(a.state.control.fibers[n],b.state.control.fibers[n]));
    }
    assert(r::step(a.state.control,middle.state.control,id,r::Rule::Remove));
    assert(crate::child_history::remove_unreferenced(g::kind(a.history),a.state,id)) by {
        assert forall|n:usize,token:nat| s::registered(a.state,n) && a.state.accumulators[n].contains(token)
            implies g::kind(a.history)(token)!=Some(id) by {
            let i=choose|i:int| 0<=i<a.state.accumulators[n].len() && a.state.accumulators[n][i]==token;
            assert(token<a.history.len());assert(b.history[token as int]==a.history[token as int]);
            assert(s::registered(b.state,n));
            assert(b.state.accumulators[n][i]==token);assert(b.state.accumulators[n].contains(token));
            assert(g::kind(b.history)(token)==g::kind(a.history)(token));
        }
    }
    assert(g::step(lib,programs,a,middle,id,r::Rule::Remove));
    remove_target(a,id,actor,a.state.control.fibers[actor].committed);
    assert(g::step(lib,programs,middle,reverse,actor,rule));
    assert(z.state.control.fibers =~= reverse.state.control.fibers);
    assert(z.state.iterators =~= reverse.state.iterators);assert(z.state.accumulators =~= reverse.state.accumulators);
    assert(z.roots =~= reverse.roots);assert(z.current =~= reverse.current);
    assert(t::same_receipts(z,reverse)) by {
        assert forall|i:int| 0<=i<z.history.len() implies {
            &&& z.history[i].iterator==reverse.history[i].iterator
            &&& z.history[i].landed.receipt==reverse.history[i].landed.receipt
            &&& z.history[i].landed.next==reverse.history[i].landed.next
            &&& z.history[i].landed.spawn==reverse.history[i].landed.spawn
        } by {if i<a.history.len() {assert(z.history[i]==a.history[i]);assert(reverse.history[i]==a.history[i]);} else {assert(i==a.history.len());}}
    }
    ol::configuration_preservation(eq,lib,programs,a,middle,id,r::Rule::Remove);
    ol::configuration_preservation(eq,lib,programs,middle,reverse,actor,rule);
}

pub proof fn remove_suffix<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,b:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,id:usize,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,b,actor,rule),g::landing(a,b,rule),
        g::step(lib,programs,b,z,id,r::Rule::Remove),g::execution(lib,programs,source,labels),source.first()==z,
    ensures {
        let middle=remove(a,id);let reverse=g::land(lib,programs,middle,actor,t::landing_phase(rule));let moved=transport::transport(source,labels,reverse);
        &&& g::step(lib,programs,a,middle,id,r::Rule::Remove) && g::step(lib,programs,middle,reverse,actor,rule)
        &&& moved.first()==reverse && moved.len()==source.len() && g::execution(lib,programs,moved,labels)
        &&& forall|i:int| 0<=i<source.len() ==> transport::related(source[i],moved[i]) && g::well_formed(lib,programs,moved[i])
    },
{
    remove_diamond(eq,lib,programs,a,b,z,actor,rule,id);
    let reverse=g::land(lib,programs,remove(a,id),actor,t::landing_phase(rule));
    transport::suffix_transport(lib,programs,source,labels,reverse);transport::observational_safe_suffix(eq,lib,programs,source,labels,reverse);
}

/// These are name-read conditions, not a predicate on the reverse execution.
/// Remove contributes no new side condition beyond its observed legal rule.
pub open spec fn crossing_guard<U,I>(a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,id:usize,external:r::Rule)->bool {
    match external {
        r::Rule::Insert=>parent_present(a,z.state.control.fibers[id].parent),
        r::Rule::Retire=>s::registered(a.state,id) && id!=actor,
        r::Rule::Remove=>true,
        _=>false,
    }
}
pub open spec fn intermediate<U,I>(a:g::Configuration<U,I>,z:g::Configuration<U,I>,id:usize,external:r::Rule)->g::Configuration<U,I> {
    match external {
        r::Rule::Insert=>{let f=z.state.control.fibers[id];t::insert(a,id,f.parent,f.dependencies,f.provisions,z.roots[id])},
        r::Rule::Retire=>retire(a,id),
        r::Rule::Remove=>remove(a,id),
        _=>a,
    }
}

/// A single interface for all three external rules and every mixed Node.
pub proof fn orchestration_diamond<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,b:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,id:usize,external:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,b,actor,rule),g::landing(a,b,rule),
        g::step(lib,programs,b,z,id,external),crossing_guard(a,z,actor,id,external),
    ensures {
        let middle=intermediate(a,z,id,external);let reverse=g::land(lib,programs,middle,actor,t::landing_phase(rule));
        &&& g::step(lib,programs,a,middle,id,external) && g::step(lib,programs,middle,reverse,actor,rule)
        &&& transport::related(z,reverse) && g::well_formed(lib,programs,middle) && g::well_formed(lib,programs,reverse)
        &&& z.history.last().input==a.state && reverse.history.last().input==middle.state
    },
{
    match external {
        r::Rule::Insert=>{insert_diamond(eq,lib,programs,a,b,z,actor,rule,id);},
        r::Rule::Retire=>{retire_diamond(eq,lib,programs,a,b,z,actor,rule,id);},
        r::Rule::Remove=>{remove_diamond(eq,lib,programs,a,b,z,actor,rule,id);},
        _=>{},
    }
}

pub proof fn orchestration_suffix<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,b:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,id:usize,external:r::Rule,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,b,actor,rule),g::landing(a,b,rule),
        g::step(lib,programs,b,z,id,external),crossing_guard(a,z,actor,id,external),
        g::execution(lib,programs,source,labels),source.first()==z,
    ensures {
        let middle=intermediate(a,z,id,external);let reverse=g::land(lib,programs,middle,actor,t::landing_phase(rule));
        let moved=transport::transport(source,labels,reverse);
        &&& g::step(lib,programs,a,middle,id,external) && g::step(lib,programs,middle,reverse,actor,rule)
        &&& moved.first()==reverse && moved.len()==source.len() && g::execution(lib,programs,moved,labels)
        &&& forall|i:int| 0<=i<source.len() ==> transport::related(source[i],moved[i]) && g::well_formed(lib,programs,moved[i])
    },
{
    orchestration_diamond(eq,lib,programs,a,b,z,actor,rule,id,external);
    let reverse=g::land(lib,programs,intermediate(a,z,id,external),actor,t::landing_phase(rule));
    transport::suffix_transport(lib,programs,source,labels,reverse);transport::observational_safe_suffix(eq,lib,programs,source,labels,reverse);
}

pub proof fn retiring_actor_blocks_landing<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,candidate:g::Configuration<U,I>,actor:usize)
    requires s::registered(a.state,actor),
    ensures !g::step(lib,programs,retire(a,actor),candidate,actor,r::Rule::Iter)
        && !g::step(lib,programs,retire(a,actor),candidate,actor,r::Rule::Finish),
{ }

/// A retired Active child still publishes its existing value while its parent
/// performs the nonempty +5 Operation. Retiring the parent instead is rejected.
pub proof fn actual_operation_retire()
    ensures {
        let a=crate::recovery_examples::trace()[7];let b=crate::recovery_examples::trace()[8];
        let lib=crate::recovery_examples::library();let programs=crate::recovery_examples::programs();
        let z=retire(b,1);let middle=retire(a,1);let reverse=g::land(lib,programs,middle,0,crate::Phase::Active);
        &&& g::step(lib,programs,a,b,0,r::Rule::Finish) && g::step(lib,programs,b,z,1,r::Rule::Retire)
        &&& g::step(lib,programs,a,middle,1,r::Rule::Retire) && g::step(lib,programs,middle,reverse,0,r::Rule::Finish)
        &&& transport::related(z,reverse) && z.state.tables[0usize][crate::recovery_examples::key(0)]==12
        &&& s::publishes(middle.state,crate::recovery_examples::key(1),1)
        &&& !g::step(lib,programs,retire(a,0),retire(b,0),0,r::Rule::Finish)
    },
{
    crate::recovery_examples::actual_execution();crate::recovery_examples::primitive_theory();
    og::exact_theory(crate::recovery_examples::equality(),crate::recovery_examples::library());
    let lib=crate::recovery_examples::library();let programs=crate::recovery_examples::programs();
    ol::from_empty_safe(crate::recovery_examples::equality(),lib,programs,crate::recovery_examples::trace(),crate::recovery_examples::labels());
    reveal(crate::recovery_examples::trace);
    let a=crate::recovery_examples::trace()[7];let b=crate::recovery_examples::trace()[8];
    crate::child_history::concrete_child_retirement(b.state,1);
    assert(g::step(lib,programs,b,retire(b,1),1,r::Rule::Retire));
    retire_diamond(crate::recovery_examples::equality(),lib,programs,a,b,retire(b,1),0,r::Rule::Finish,1);
    retiring_actor_blocks_landing(lib,programs,a,retire(b,0),0);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn actual_operation_remove()
    ensures {
        let lib=crate::recovery_examples::library();let programs=crate::recovery_examples::programs();
        let base=crate::recovery_examples::trace()[7];
        let inserted=t::insert(base,2,None,ISet::empty(),crate::recovery_examples::provided(2),crate::recovery_examples::Stage::Spawn);
        let a=retire(inserted,2);let b=g::land(lib,programs,a,0,crate::Phase::Active);
        let z=remove(b,2);let middle=remove(a,2);let reverse=g::land(lib,programs,middle,0,crate::Phase::Active);
        &&& g::well_formed(lib,programs,a)
        &&& g::step(lib,programs,a,b,0,r::Rule::Finish) && g::step(lib,programs,b,z,2,r::Rule::Remove)
        &&& g::step(lib,programs,a,middle,2,r::Rule::Remove) && g::step(lib,programs,middle,reverse,0,r::Rule::Finish)
        &&& transport::related(z,reverse) && !s::registered(z.state,2)
        &&& a.state.tables[0usize][crate::recovery_examples::key(0)]==7 && z.state.tables[0usize][crate::recovery_examples::key(0)]==12
    },
{
    crate::recovery_examples::actual_execution();crate::recovery_examples::primitive_theory();
    og::exact_theory(crate::recovery_examples::equality(),crate::recovery_examples::library());
    let lib=crate::recovery_examples::library();let programs=crate::recovery_examples::programs();
    ol::from_empty_safe(crate::recovery_examples::equality(),lib,programs,crate::recovery_examples::trace(),crate::recovery_examples::labels());
    reveal(crate::recovery_examples::trace);
    let base=crate::recovery_examples::trace()[7];let provided=crate::recovery_examples::provided(2);let root=crate::recovery_examples::Stage::Spawn;
    crate::mixed_syntax::constructor_member(lib,programs,2,provided,provided,root);
    assert(ISet::<Port>::empty().union(provided) =~= provided);
    t::insertion_step(lib,programs,base,2,None,ISet::empty(),provided,root);
    let inserted=t::insert(base,2,None,ISet::empty(),provided,root);
    ol::configuration_preservation(crate::recovery_examples::equality(),lib,programs,base,inserted,2,r::Rule::Insert);
    let a=retire(inserted,2);crate::child_history::concrete_child_retirement(inserted.state,2);
    assert(g::step(lib,programs,inserted,a,2,r::Rule::Retire));
    ol::configuration_preservation(crate::recovery_examples::equality(),lib,programs,inserted,a,2,r::Rule::Retire);
    let b=g::land(lib,programs,a,0,crate::Phase::Active);let z=remove(b,2);
    assert(g::step(lib,programs,a,b,0,r::Rule::Finish));
    assert(crate::child_history::remove_unreferenced(g::kind(b.history),b.state,2)) by {
        assert forall|n:usize,token:nat| s::registered(b.state,n) && b.state.accumulators[n].contains(token) implies g::kind(b.history)(token)!=Some(2usize) by {
            if n==0 {assert(b.state.accumulators[n] =~= seq![0nat,3nat,4nat]);assert(token==0 || token==3 || token==4);}
            else if n==1 {assert(b.state.accumulators[n] =~= seq![1nat,2nat]);assert(token==1 || token==2);}
            else {assert(n==2);assert(b.state.accumulators[n].len()==0);}
        }
    }
    assert(r::frame(b.state.control,z.state.control,2));
    assert(g::step(lib,programs,b,z,2,r::Rule::Remove));
    remove_diamond(crate::recovery_examples::equality(),lib,programs,a,b,z,0,r::Rule::Finish,2);
}

} // verus!
