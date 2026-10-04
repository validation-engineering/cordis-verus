//! Alpha transport of the actual nine-rule fresh-allocation source semantics.
//!
//! A renaming transports external actors, inserted parents and roots, choices,
//! current continuations and captured history together. Strict undefined run
//! and restoration results remain undefined under the same transport.
#[cfg(verus_keep_ghost)]
use crate::{
    alpha as names, child_history as ch, dependent_grammar as d, dependent_lift as dep,
    fresh_grammar as f, fresh_semantics as g, mixed_grammar as mx, observational_grammar as og,
    preservation as inv, refinement as r, semantics as s, Binding, Phase, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn member_name<I>(rho:names::Renaming,h:f::IndexRenaming<I>,name:f::MemberName<I>)->f::MemberName<I> {
    ((rho.forward)(name.0),name.1,name.2,(h.forward)(name.3))
}
pub open spec fn pullback<I>(rho:names::Renaming,h:f::IndexRenaming<I>,set:f::Members<I>)->f::Members<I> {
    ISet::new(|name:f::MemberName<I>|set.contains(member_name(rho,h,name)))
}
pub proof fn obligation_forward<A,X,U,B,I>(rho:names::Renaming,h:f::IndexRenaming<I>,lib:f::Library<A,X,U,B>,node:f::Node<A,X,U,B,I>,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,set:f::Members<I>)
    requires names::bijective(rho),f::index_bijective(h),f::obligation(lib,node,actor,keys,provisions,pullback(rho,h,set)),
    ensures f::obligation(lib,f::node(rho,h,node),(rho.forward)(actor),keys,provisions,set),
{
    match node {
        f::Node::Dependent {node}=>{
            match node {d::Node::Unit=>{},d::Node::Provision {..}=>{},
                d::Node::Operation {operation,argument,select}=>{
                    assert forall|b:B| #![trigger select(b)] (lib.outcomes)(operation,b) && f::next(h,select(b)).is_some() implies
                        f::local(set,(rho.forward)(actor),keys,provisions).contains(f::next(h,select(b)).unwrap()) by {
                        assert(f::local(pullback(rho,h,set),actor,keys,provisions).contains(select(b).unwrap()));
                    }
                },
            }
        },
        f::Node::FreshChild {dependencies,provisions:provided,body}=>{
            assert forall|child:usize| #![trigger body((rho.backward)(child))] {
                let old=body((rho.backward)(child));
                &&& set.contains((child,dependencies.union(provided),provided,(h.forward)(old.0)))
                &&& (old.1.is_some() ==> set.contains(((rho.forward)(actor),keys,provisions,(h.forward)(old.1.unwrap()))))
            } by {
                assert(pullback(rho,h,set).contains(((rho.backward)(child),dependencies.union(provided),provided,body((rho.backward)(child)).0)));
            }
        },
    }
}

/// Membership is transported using closed sets, not replaced with a new
/// membership premise for the chosen allocation or successor configuration.
pub proof fn member_forward<A,X,U,B,I>(rho:names::Renaming,h:f::IndexRenaming<I>,lib:f::Library<A,X,U,B>,programs:f::Programs<A,X,U,B,I>,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,id:I)
    requires names::bijective(rho),f::index_bijective(h),f::member(lib,programs,actor,keys,provisions,id),
    ensures f::member(lib,f::programs(rho,h,programs),(rho.forward)(actor),keys,provisions,(h.forward)(id)),
{
    let target=f::programs(rho,h,programs);
    assert forall|set:f::Members<I>|f::closed(lib,target,set) implies set.contains(((rho.forward)(actor),keys,provisions,(h.forward)(id))) by {
        let source=pullback(rho,h,set);
        assert(f::closed(lib,programs,source)) by {
            assert forall|name:f::MemberName<I>|f::obligation(lib,programs(name.0)(name.3),name.0,name.1,name.2,source) implies source.contains(name) by {
                obligation_forward(rho,h,lib,programs(name.0)(name.3),name.0,name.1,name.2,set);
                assert(f::obligation(lib,target((rho.forward)(name.0))((h.forward)(name.3)),(rho.forward)(name.0),name.1,name.2,set));
                assert(set.contains(member_name(rho,h,name)));
            }
        }
        assert(source.contains((actor,keys,provisions,id)));
    }
}

pub proof fn root_insert<U,I>(rho:names::Renaming,h:f::IndexRenaming<I>,a:mx::Configuration<U,I>,actor:usize,root:I,current:Option<I>)
    requires names::bijective(rho),
    ensures f::configuration(rho,h,mx::Configuration {roots:a.roots.insert(actor,root),current:a.current.insert(actor,current),..a}).roots
        ==f::configuration(rho,h,a).roots.insert((rho.forward)(actor),(h.forward)(root)),
        f::configuration(rho,h,mx::Configuration {roots:a.roots.insert(actor,root),current:a.current.insert(actor,current),..a}).current
        ==f::configuration(rho,h,a).current.insert((rho.forward)(actor),f::next(h,current)),
{
    let changed=mx::Configuration {roots:a.roots.insert(actor,root),current:a.current.insert(actor,current),..a};
    assert(f::configuration(rho,h,changed).roots =~= f::configuration(rho,h,a).roots.insert((rho.forward)(actor),(h.forward)(root)));
    assert(f::configuration(rho,h,changed).current =~= f::configuration(rho,h,a).current.insert((rho.forward)(actor),f::next(h,current)));
}
pub proof fn edit_forward<U,I>(rho:names::Renaming,h:f::IndexRenaming<I>,a:mx::Configuration<U,I>,actor:usize,phase:Phase,committed:ISet<Binding>,next:Option<I>,tokens:Seq<nat>)
    requires names::bijective(rho),s::registered(a.state,actor),
    ensures f::configuration(rho,h,mx::edit(a,actor,phase,committed,next,tokens))
        ==mx::edit(f::configuration(rho,h,a),(rho.forward)(actor),phase,names::view(rho,committed),f::next(h,next),tokens),
{
    names::edit_commutes(rho,a.state,actor,phase,committed,dep::marker(next),tokens);
    root_insert(rho,h,a,actor,a.roots[actor],next);
}

pub proof fn landed_registered<A,X,U,B,I>(lib:f::Library<A,X,U,B>,node:f::Node<A,X,U,B,I>,a:s::State<U>,actor:usize,choice:Option<usize>)
    requires f::run(lib,node,a,actor,choice).is_some(),
    ensures s::registered(f::run(lib,node,a,actor,choice).unwrap().state,actor),
{
    f::allocation_guard(lib,node,a,actor,choice);
    match node {f::Node::Dependent {node}=>{match node {d::Node::Unit=>{},d::Node::Operation {..}=>{},d::Node::Provision {..}=>{}}},f::Node::FreshChild {..}=>{}}
}
pub proof fn land_forward<A,X,U,B,I>(rho:names::Renaming,h:f::IndexRenaming<I>,lib:f::Library<A,X,U,B>,programs:f::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,actor:usize,phase:Phase,choice:Option<usize>)
    requires names::bijective(rho),f::index_bijective(h),inv::well_formed(a.state),a.current.dom().contains(actor),a.current[actor].is_some(),
        f::run(lib,programs(actor)(a.current[actor].unwrap()),a.state,actor,choice).is_some(),
    ensures f::configuration(rho,h,g::land(lib,programs,a,actor,phase,choice))
        ==g::land(lib,f::programs(rho,h,programs),f::configuration(rho,h,a),(rho.forward)(actor),phase,names::parent(rho,choice)),
{
    let id=a.current[actor].unwrap();let e=g::entry(lib,programs,a,actor,choice);let out=e.landed;
    f::run_forward(rho,h,lib,programs(actor)(id),a.state,actor,choice);
    landed_registered(lib,programs(actor)(id),a.state,actor,choice);
    let following=if phase==Phase::Loading {out.next}else{None};
    names::edit_commutes(rho,out.state,actor,phase,a.state.control.fibers[actor].committed,dep::marker(following),a.state.accumulators[actor].push(a.history.len()));
    let before=mx::Configuration {state:out.state,roots:match out.spawn {None=>a.roots,Some((child,root))=>a.roots.insert(child,root)},
        current:match out.spawn {None=>a.current,Some((child,_))=>a.current.insert(child,None)},history:a.history.push(e)};
    root_insert(rho,h,before,actor,before.roots[actor],following);
    if out.spawn.is_some() {root_insert(rho,h,a,out.spawn.unwrap().0,out.spawn.unwrap().1,None);}
    assert(a.history.push(e).map(|_:int,v:mx::Entry<U,I>|f::entry(rho,h,v)) =~= f::configuration(rho,h,a).history.push(f::entry(rho,h,e)));
}

pub proof fn component_forward<A,X,U,B,I>(rho:names::Renaming,h:f::IndexRenaming<I>,lib:f::Library<A,X,U,B>,programs:f::Programs<A,X,U,B,I>,a:s::State<U>,actor:usize,id:I)
    requires names::bijective(rho),f::index_bijective(h),s::registered(a,actor),g::component_member(lib,programs,a,actor,id),
    ensures g::component_member(lib,f::programs(rho,h,programs),names::context(rho,a),(rho.forward)(actor),(h.forward)(id)),
{
    names::observations(rho,a.control,actor);
    member_forward(rho,h,lib,programs,actor,dep::declarations(a,actor),a.control.fibers[actor].provisions,id);
}
pub proof fn insert_map_forward<U>(rho:names::Renaming,a:s::State<U>,z:s::State<U>,actor:usize)
    requires names::bijective(rho),inv::insert_map(a,z,actor),
    ensures inv::insert_map(names::context(rho,a),names::context(rho,z),(rho.forward)(actor)),
{
    names::step_forward(rho,a.control,z.control,actor,r::Rule::Insert);
    names::observations(rho,z.control,actor);
    names::indexed_insert(rho,a.tables,actor,IMap::empty());
    names::indexed_insert(rho,a.effects,actor,z.effects[actor]);
    names::indexed_insert(rho,a.iterators,actor,None);
    names::indexed_insert(rho,a.accumulators,actor,Seq::empty());
}
pub proof fn erase_forward<U>(rho:names::Renaming,a:s::State<U>,actor:usize)
    requires names::bijective(rho),
    ensures names::context(rho,s::erase(a,actor))==s::erase(names::context(rho,a),(rho.forward)(actor)),
{
    names::indexed_remove(rho,a.tables,actor);names::indexed_remove(rho,a.effects,actor);
    names::indexed_remove(rho,a.iterators,actor);names::indexed_remove(rho,a.accumulators,actor);
    assert(names::context(rho,s::erase(a,actor)).control.fibers =~= s::erase(names::context(rho,a),(rho.forward)(actor)).control.fibers);
}
pub proof fn remove_unreferenced_forward<U,I>(rho:names::Renaming,h:f::IndexRenaming<I>,a:mx::Configuration<U,I>,actor:usize)
    requires names::bijective(rho),s::shaped(a.state),ch::remove_unreferenced(mx::kind(a.history),a.state,actor),
    ensures ch::remove_unreferenced(mx::kind(f::configuration(rho,h,a).history),names::context(rho,a.state),(rho.forward)(actor)),
{
    let z=f::configuration(rho,h,a);
    let renamed_kind=mx::kind(z.history);
    assert forall|owner:usize,token:nat| s::registered(z.state,owner) && #[trigger] z.state.accumulators[owner].contains(token) implies renamed_kind(token)!=Some((rho.forward)(actor)) by {
        let old_owner=(rho.backward)(owner);
        assert(s::registered(a.state,old_owner));
        assert(a.state.accumulators[old_owner].contains(token));
        assert(mx::kind(a.history)(token)!=Some(actor));
        if token<a.history.len() {
            let receipt=a.history[token as int].landed.receipt;
            assert(mx::captured_child(f::receipt(rho,receipt))==names::parent(rho,mx::captured_child(receipt)));
            if mx::captured_child(receipt).is_some() {assert((rho.backward)((rho.forward)(mx::captured_child(receipt).unwrap()))==mx::captured_child(receipt).unwrap());}
        }
    }
    assert(ch::remove_unreferenced(renamed_kind,z.state,(rho.forward)(actor)));
}
pub proof fn unload_forward<A,X,U,B,I>(rho:names::Renaming,h:f::IndexRenaming<I>,lib:f::Library<A,X,U,B>,programs:f::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,actor:usize)
    requires names::bijective(rho),g::well_formed(lib,programs,a),s::registered(a.state,actor),mx::restore(a.history,a.state.accumulators[actor],a.state,actor).is_some(),
    ensures f::configuration(rho,h,mx::unload(a,actor))==mx::unload(f::configuration(rho,h,a),(rho.forward)(actor)),
{
    f::restore_forward(rho,h,a.history,a.state.accumulators[actor],a.state,actor);
    g::restore_preservation(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);
    let restored=mx::restore(a.history,a.state.accumulators[actor],a.state,actor).unwrap();
    names::edit_commutes(rho,restored,actor,Phase::Inactive,ISet::empty(),None,Seq::empty());
    assert(names::view(rho,ISet::<Binding>::empty()) =~= ISet::empty());
    root_insert(rho,h,a,actor,a.roots[actor],None);
}

/// This is a theorem about each actual source rule. No renamed successor
/// condition, abstract model, or choice-specific grammar is supplied.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn step_forward<A,X,U,B,I>(rho:names::Renaming,h:f::IndexRenaming<I>,lib:f::Library<A,X,U,B>,programs:f::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize,rule:r::Rule,choice:Option<usize>)
    requires names::bijective(rho),f::index_bijective(h),g::well_formed(lib,programs,a),g::step(lib,programs,a,z,actor,rule,choice),
    ensures g::step(lib,f::programs(rho,h,programs),f::configuration(rho,h,a),f::configuration(rho,h,z),(rho.forward)(actor),rule,names::parent(rho,choice)),
{
    let before=f::configuration(rho,h,a);let after=f::configuration(rho,h,z);let target=(rho.forward)(actor);
    names::observations(rho,a.state.control,actor);names::observations(rho,z.state.control,actor);
    if s::registered(a.state,actor) {
        assert(before.current[target]==f::next(h,a.current[actor]));
        assert(before.roots[target]==(h.forward)(a.roots[actor]));
        names::full_target_equivariant(rho,a.state,actor,a.state.control.fibers[actor].committed);
    }
    if g::landing(a,z,rule) {
        let id=a.current[actor].unwrap();
        f::run_forward(rho,h,lib,programs(actor)(id),a.state,actor,choice);
        land_forward(rho,h,lib,programs,a,actor,if rule==r::Rule::Iter {Phase::Loading}else if rule==r::Rule::Finish {Phase::Active}else{Phase::Unloading},choice);
    }
    match rule {
        r::Rule::Insert=>{
            insert_map_forward(rho,a.state,z.state,actor);
            root_insert(rho,h,a,actor,z.roots[actor],None);
            component_forward(rho,h,lib,programs,z.state,actor,z.roots[actor]);
        },
        r::Rule::Retire=>{names::child_retire_forward(rho,a.state,z.state,actor);},
        r::Rule::Remove=>{
            names::step_forward(rho,a.state.control,z.state.control,actor,rule);erase_forward(rho,a.state,actor);
            remove_unreferenced_forward(rho,h,a,actor);
            assert(after.roots =~= before.roots.remove(target));assert(after.current =~= before.current.remove(target));
        },
        r::Rule::Begin=>{
            names::full_target_equivariant(rho,a.state,actor,z.state.control.fibers[actor].committed);
            edit_forward(rho,h,a,actor,Phase::Loading,z.state.control.fibers[actor].committed,Some(a.roots[actor]),Seq::empty());
        },
        r::Rule::Divert | r::Rule::Leave=>{
            if !g::landing(a,z,rule) {edit_forward(rho,h,a,actor,Phase::Unloading,a.state.control.fibers[actor].committed,None,a.state.accumulators[actor]);}
        },
        r::Rule::Unload=>{
            names::relied_equivariant(rho,a.state.control,actor);
            f::restore_forward(rho,h,a.history,a.state.accumulators[actor],a.state,actor);
            unload_forward(rho,h,lib,programs,a,actor);
        },_=>{},
    }
}

pub proof fn strict_inverse_domains<U,I>(rho:names::Renaming,h:f::IndexRenaming<I>,receipt:mx::Receipt<U>,history:Seq<mx::Entry<U,I>>,tokens:Seq<nat>,a:s::State<U>,actor:usize)
    requires names::bijective(rho),inv::well_formed(a),
    ensures mx::undo(f::receipt(rho,receipt),names::context(rho,a)).is_some()==mx::undo(receipt,a).is_some(),
        mx::restore(history.map(|_:int,e:mx::Entry<U,I>|f::entry(rho,h,e)),tokens,names::context(rho,a),(rho.forward)(actor)).is_some()
            ==mx::restore(history,tokens,a,actor).is_some(),
{
    f::undo_forward(rho,receipt,a);f::restore_forward(rho,h,history,tokens,a,actor);
}
pub open spec fn configurations<U,I>(rho:names::Renaming,h:f::IndexRenaming<I>,trace:Seq<mx::Configuration<U,I>>)->Seq<mx::Configuration<U,I>> {
    trace.map(|_:int,a:mx::Configuration<U,I>|f::configuration(rho,h,a))
}
pub open spec fn labels(rho:names::Renaming,trace:Seq<g::Label>)->Seq<g::Label> {
    trace.map(|_:int,label:g::Label|((rho.forward)(label.0),label.1,names::parent(rho,label.2)))
}

/// External Insert payloads are the renamed successor's parent and root;
/// Retire/Remove actors and landing allocation choices are renamed by labels.
pub proof fn execution_forward<A,X,U,B,I>(rho:names::Renaming,h:f::IndexRenaming<I>,eq:spec_fn(Port,U,U)->bool,lib:f::Library<A,X,U,B>,programs:f::Programs<A,X,U,B,I>,trace:Seq<mx::Configuration<U,I>>,events:Seq<g::Label>)
    requires names::bijective(rho),f::index_bijective(h),og::primitive_theory(eq,lib),g::execution(lib,programs,trace,events),g::well_formed(lib,programs,trace.first()),
    ensures g::execution(lib,f::programs(rho,h,programs),configurations(rho,h,trace),labels(rho,events)),
{
    g::execution_preservation(eq,lib,programs,trace,events);
    assert forall|i:int| 0<=i<events.len() implies g::step(lib,f::programs(rho,h,programs),configurations(rho,h,trace)[i],configurations(rho,h,trace)[i+1],labels(rho,events)[i].0,labels(rho,events)[i].1,labels(rho,events)[i].2) by {
        step_forward(rho,h,lib,programs,trace[i],trace[i+1],events[i].0,events[i].1,events[i].2);
    }
}
pub proof fn empty_forward<U,I>(rho:names::Renaming,h:f::IndexRenaming<I>)
    ensures f::configuration(rho,h,g::empty::<U,I>())==g::empty::<U,I>(),
{
    let z=f::configuration(rho,h,g::empty::<U,I>());
    assert(z.state.control.fibers =~= IMap::empty());assert(z.state.tables =~= IMap::empty());
    assert(z.state.effects =~= IMap::empty());assert(z.state.iterators =~= IMap::empty());assert(z.state.accumulators =~= IMap::empty());
    assert(z.roots =~= IMap::empty());assert(z.current =~= IMap::empty());assert(z.history =~= Seq::empty());
}
pub proof fn from_empty_forward<A,X,U,B,I>(rho:names::Renaming,h:f::IndexRenaming<I>,eq:spec_fn(Port,U,U)->bool,lib:f::Library<A,X,U,B>,programs:f::Programs<A,X,U,B,I>,trace:Seq<mx::Configuration<U,I>>,events:Seq<g::Label>)
    requires names::bijective(rho),f::index_bijective(h),og::primitive_theory(eq,lib),g::execution(lib,programs,trace,events),trace.first()==g::empty::<U,I>(),
    ensures g::execution(lib,f::programs(rho,h,programs),configurations(rho,h,trace),labels(rho,events)),
        configurations(rho,h,trace).first()==g::empty::<U,I>(),
        forall|i:int|0<=i<trace.len() ==> g::well_formed(lib,f::programs(rho,h,programs),configurations(rho,h,trace)[i])
            && inv::resource_safe(configurations(rho,h,trace)[i].state),
{
    g::empty_well_formed(lib,programs);empty_forward::<U,I>(rho,h);
    execution_forward(rho,h,eq,lib,programs,trace,events);
    g::from_empty_safe(eq,lib,f::programs(rho,h,programs),configurations(rho,h,trace),labels(rho,events));
}

pub proof fn instantiate_extensional<A,X,U,B,I>(left:f::Node<A,X,U,B,I>,right:f::Node<A,X,U,B,I>)
    requires forall|choice:Option<usize>| #[trigger] f::instantiate(left,choice)==f::instantiate(right,choice),
    ensures left==right,
{
    assert(f::instantiate(left,None)==f::instantiate(right,None));
    match left {
        f::Node::Dependent {..}=>{},
        f::Node::FreshChild {dependencies,provisions,body}=>{
            assert(f::instantiate(left,Some(0usize))==f::instantiate(right,Some(0usize)));
            match right {f::Node::Dependent {..}=>{},f::Node::FreshChild {body:other,..}=>{
                assert(body =~= other) by {
                    assert forall|child:usize| #[trigger] body(child)==other(child) by {assert(f::instantiate(left,Some(child))==f::instantiate(right,Some(child)));}
                }
            }}
        },
    }
}

/// Whole-program naturality is a syntactic condition on all binder choices.
/// It supplies equality with the original installed program, not an assumed
/// simulation or execution relation.
pub proof fn natural_program<A,X,U,B,I>(rho:names::Renaming,action:f::NameAction<I>,programs:f::Programs<A,X,U,B,I>)
    requires names::bijective(rho),f::supported_action(action),f::natural(action,programs),
    ensures f::programs(rho,f::action_map(action,rho),programs)==programs,
{
    let h=f::action_map(action,rho);let target=f::programs(rho,h,programs);
    assert(f::index_bijective(h));
    assert forall|actor:usize| #[trigger] target(actor)==programs(actor) by {
        assert forall|id:I| #[trigger] target(actor)(id)==programs(actor)(id) by {
            let old_actor=(rho.backward)(actor);let old_id=(h.backward)(id);
            assert((rho.forward)(old_actor)==actor);assert((h.forward)(old_id)==id);
            assert forall|choice:Option<usize>| #[trigger] f::instantiate(programs(actor)(id),choice)==f::instantiate(target(actor)(id),choice) by {
                let old_choice=names::parent(names::inverse(rho),choice);
                assert(names::parent(rho,old_choice)==choice) by {match choice {None=>{},Some(_)=>{}}}
                assert(f::instantiate(programs((rho.forward)(old_actor))((action.apply)(rho,old_id)),names::parent(rho,old_choice))
                    ==f::instantiate(f::node(rho,h,programs(old_actor)(old_id)),names::parent(rho,old_choice)));
            }
            instantiate_extensional(programs(actor)(id),target(actor)(id));
        }
        assert(target(actor) =~= programs(actor));
    }
    assert(target =~= programs);
}
pub proof fn natural_step<A,X,U,B,I>(rho:names::Renaming,action:f::NameAction<I>,lib:f::Library<A,X,U,B>,programs:f::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize,rule:r::Rule,choice:Option<usize>)
    requires names::bijective(rho),f::supported_action(action),f::natural(action,programs),g::well_formed(lib,programs,a),g::step(lib,programs,a,z,actor,rule,choice),
    ensures g::step(lib,programs,f::configuration(rho,f::action_map(action,rho),a),f::configuration(rho,f::action_map(action,rho),z),(rho.forward)(actor),rule,names::parent(rho,choice)),
{
    natural_program(rho,action,programs);step_forward(rho,f::action_map(action,rho),lib,programs,a,z,actor,rule,choice);
}
pub proof fn natural_execution<A,X,U,B,I>(rho:names::Renaming,action:f::NameAction<I>,eq:spec_fn(Port,U,U)->bool,lib:f::Library<A,X,U,B>,programs:f::Programs<A,X,U,B,I>,trace:Seq<mx::Configuration<U,I>>,events:Seq<g::Label>)
    requires names::bijective(rho),f::supported_action(action),f::natural(action,programs),og::primitive_theory(eq,lib),g::execution(lib,programs,trace,events),g::well_formed(lib,programs,trace.first()),
    ensures g::execution(lib,programs,configurations(rho,f::action_map(action,rho),trace),labels(rho,events)),
{
    natural_program(rho,action,programs);execution_forward(rho,f::action_map(action,rho),eq,lib,programs,trace,events);
}

/// An external insertion keeps service declarations but transports its actor,
/// optional parent and actual root continuation. This is the concrete payload
/// carried by the Insert case of the source transition relation.
pub proof fn insert_payload_forward<U,I>(rho:names::Renaming,h:f::IndexRenaming<I>,a:mx::Configuration<U,I>,actor:usize,parent:Option<usize>,dependencies:ISet<Port>,provisions:ISet<Port>,root:I)
    requires names::bijective(rho),
    ensures f::configuration(rho,h,crate::mixed_transposition::insert(a,actor,parent,dependencies,provisions,root))
        ==crate::mixed_transposition::insert(f::configuration(rho,h,a),(rho.forward)(actor),names::parent(rho,parent),dependencies,provisions,(h.forward)(root)),
{
    root_insert(rho,h,a,actor,root,None);
    names::indexed_insert(rho,a.state.tables,actor,IMap::empty());names::indexed_insert(rho,a.state.effects,actor,0);
    names::indexed_insert(rho,a.state.iterators,actor,None);names::indexed_insert(rho,a.state.accumulators,actor,Seq::empty());
    let left=f::configuration(rho,h,crate::mixed_transposition::insert(a,actor,parent,dependencies,provisions,root));
    let right=crate::mixed_transposition::insert(f::configuration(rho,h,a),(rho.forward)(actor),names::parent(rho,parent),dependencies,provisions,(h.forward)(root));
    assert(names::view(rho,ISet::<Binding>::empty()) =~= ISet::empty());
    assert(left.state.control.fibers =~= right.state.control.fibers);
}
pub proof fn natural_from_empty<A,X,U,B,I>(rho:names::Renaming,action:f::NameAction<I>,eq:spec_fn(Port,U,U)->bool,lib:f::Library<A,X,U,B>,programs:f::Programs<A,X,U,B,I>,trace:Seq<mx::Configuration<U,I>>,events:Seq<g::Label>)
    requires names::bijective(rho),f::supported_action(action),f::natural(action,programs),og::primitive_theory(eq,lib),g::execution(lib,programs,trace,events),trace.first()==g::empty::<U,I>(),
    ensures g::execution(lib,programs,configurations(rho,f::action_map(action,rho),trace),labels(rho,events)),
        configurations(rho,f::action_map(action,rho),trace).first()==g::empty::<U,I>(),
        forall|i:int|0<=i<trace.len() ==> g::well_formed(lib,programs,configurations(rho,f::action_map(action,rho),trace)[i])
            && inv::resource_safe(configurations(rho,f::action_map(action,rho),trace)[i].state),
{
    natural_program(rho,action,programs);from_empty_forward(rho,f::action_map(action,rho),eq,lib,programs,trace,events);
}

}
