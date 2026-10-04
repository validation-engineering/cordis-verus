//! Fresh child names are binders, not mutable constants in installed programs.
//!
//! A fixed program accepts an explicit allocation choice only at FreshChild.
//! The choice is checked by the original strict insertion rule and recorded in
//! the actual child receipt. Historical entries recover it from that receipt.
//! Local allocation freshness means absence from the current registry. Keeping
//! an already executed history fixed requires the stronger historical support
//! condition below; removed names and name-carrying continuations still matter.
use crate::{
    alpha as names, dependent_grammar as d, dependent_lift as dep, mixed_grammar as mx, Port,
};
#[cfg(verus_keep_ghost)]
use crate::{
    global, grammar_lift as lift, preservation as inv, projection, refinement as r, semantics as s,
    Binding, Phase,
};
use vstd::prelude::*;

verus! {

#[verifier::reject_recursive_types(B)]
pub enum Node<A,X,U,B,I> {
    Dependent {node:d::Node<Port,A,X,U,B,I>},
    FreshChild {dependencies:ISet<Port>,provisions:ISet<Port>,body:spec_fn(usize)->(I,Option<I>)},
}
pub type Programs<A,X,U,B,I> = spec_fn(usize)->spec_fn(I)->Node<A,X,U,B,I>;
pub type Configuration<U,I> = mx::Configuration<U,I>;
pub type Library<A,X,U,B> = dep::Library<A,X,U,B>;

pub open spec fn instantiate<A,X,U,B,I>(node:Node<A,X,U,B,I>,choice:Option<usize>)->Option<mx::Node<A,X,U,B,I>> {
    match node {
        Node::Dependent {node}=>if choice.is_none() {Some(mx::Node::Dependent {node})} else {None},
        Node::FreshChild {dependencies,provisions,body}=>match choice {
            None=>None,Some(child)=>Some(mx::Node::Child {child,dependencies,provisions,root:body(child).0,next:body(child).1}),
        },
    }
}
pub open spec fn run<A,X,U,B,I>(lib:Library<A,X,U,B>,node:Node<A,X,U,B,I>,a:s::State<U>,actor:usize,choice:Option<usize>)->Option<mx::Landed<U,I>> {
    match instantiate(node,choice) {None=>None,Some(concrete)=>mx::run(lib,concrete,a,actor)}
}

/// This reconstruction is checked against the same installed program. A later
/// activation cannot rewrite an earlier entry's allocation choice or inverse.
pub open spec fn history_sound<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,history:Seq<mx::Entry<U,I>>)->bool {
    forall|i:int| #![trigger history[i]] 0<=i<history.len() ==> {
        let e=history[i];let actor=mx::owner(e.landed.receipt);
        run(lib,programs(actor)(e.iterator),e.input,actor,mx::captured_child(e.landed.receipt))==Some(e.landed)
            && mx::receipt_typed(lib,e.landed.receipt) && mx::undo(e.landed.receipt,e.landed.state).is_some()
    }
}
pub proof fn allocation_guard<A,X,U,B,I>(lib:Library<A,X,U,B>,node:Node<A,X,U,B,I>,a:s::State<U>,actor:usize,choice:Option<usize>)
    requires run(lib,node,a,actor,choice).is_some(),
    ensures mx::owner(run(lib,node,a,actor,choice).unwrap().receipt)==actor,
        mx::captured_child(run(lib,node,a,actor,choice).unwrap().receipt)==choice,
        choice.is_some() ==> !s::registered(a,choice.unwrap()) && choice.unwrap()!=actor
            && s::registered(run(lib,node,a,actor,choice).unwrap().state,choice.unwrap())
            && run(lib,node,a,actor,choice).unwrap().state.control.fibers[choice.unwrap()].parent==Some(actor),
{match node {Node::Dependent {..}=>{},Node::FreshChild {..}=>{}}}

/// Two successful activations while the first child remains registered must
/// allocate different identities, irrespective of the child being retired.
pub proof fn reactivation_identity<A,X,U,B,I>(lib:Library<A,X,U,B>,node:Node<A,X,U,B,I>,a:s::State<U>,actor:usize,old_child:usize,new_child:usize)
    requires s::registered(a,old_child),run(lib,node,a,actor,Some(new_child)).is_some(),
    ensures new_child!=old_child,
        mx::captured_child(run(lib,node,a,actor,Some(new_child)).unwrap().receipt)==Some(new_child),
        mx::captured_child(mx::Receipt::<U>::Child {actor,child:old_child})==Some(old_child),
{allocation_guard(lib,node,a,actor,Some(new_child));}

#[verifier::reject_recursive_types(I)]
pub struct IndexRenaming<I> {pub forward:spec_fn(I)->I,pub backward:spec_fn(I)->I}
pub open spec fn index_bijective<I>(h:IndexRenaming<I>)->bool {
    (forall|id:I| #[trigger] (h.backward)((h.forward)(id))==id)
        && (forall|id:I| #[trigger] (h.forward)((h.backward)(id))==id)
}
pub open spec fn next<I>(h:IndexRenaming<I>,id:Option<I>)->Option<I> {match id {None=>None,Some(id)=>Some((h.forward)(id))}}
pub open spec fn dependent_node<A,X,U,B,I>(h:IndexRenaming<I>,node:d::Node<Port,A,X,U,B,I>)->d::Node<Port,A,X,U,B,I> {
    match node {
        d::Node::Unit=>d::Node::Unit,
        d::Node::Operation {operation,argument,select}=>d::Node::Operation {operation,argument,select:|outcome:B|next(h,select(outcome))},
        d::Node::Provision {key,value,next:following}=>d::Node::Provision {key,value,next:next(h,following)},
    }
}
pub open spec fn node<A,X,U,B,I>(rho:names::Renaming,h:IndexRenaming<I>,source:Node<A,X,U,B,I>)->Node<A,X,U,B,I> {
    match source {
        Node::Dependent {node}=>Node::Dependent {node:dependent_node(h,node)},
        Node::FreshChild {dependencies,provisions,body}=>Node::FreshChild {dependencies,provisions,body:|child:usize| {
            let prior=body((rho.backward)(child));((h.forward)(prior.0),next(h,prior.1))
        }},
    }
}
pub open spec fn programs<A,X,U,B,I>(rho:names::Renaming,h:IndexRenaming<I>,source:Programs<A,X,U,B,I>)->Programs<A,X,U,B,I> {
    |actor:usize| |id:I|node(rho,h,source((rho.backward)(actor))((h.backward)(id)))
}
pub open spec fn table_receipt<U>(rho:names::Renaming,receipt:lift::Receipt<U>)->lift::Receipt<U> {
    lift::Receipt {actor:(rho.forward)(receipt.actor),inverse:match receipt.inverse {
        lift::Inverse::Unit=>lift::Inverse::Unit,
        lift::Inverse::Provision {key}=>lift::Inverse::Provision {key},
        lift::Inverse::Operation {provider,key,undo}=>lift::Inverse::Operation {provider:(rho.forward)(provider),key,undo},
    }}
}
pub open spec fn receipt<U>(rho:names::Renaming,receipt:mx::Receipt<U>)->mx::Receipt<U> {
    match receipt {
        mx::Receipt::Table {receipt}=>mx::Receipt::Table {receipt:table_receipt(rho,receipt)},
        mx::Receipt::Child {actor,child}=>mx::Receipt::Child {actor:(rho.forward)(actor),child:(rho.forward)(child)},
    }
}
pub open spec fn landed<U,I>(rho:names::Renaming,h:IndexRenaming<I>,y:mx::Landed<U,I>)->mx::Landed<U,I> {
    mx::Landed {state:names::context(rho,y.state),receipt:receipt(rho,y.receipt),next:next(h,y.next),
        spawn:match y.spawn {None=>None,Some((child,root))=>Some(((rho.forward)(child),(h.forward)(root)))}}
}
pub open spec fn entry<U,I>(rho:names::Renaming,h:IndexRenaming<I>,e:mx::Entry<U,I>)->mx::Entry<U,I> {
    mx::Entry {input:names::context(rho,e.input),iterator:(h.forward)(e.iterator),landed:landed(rho,h,e.landed)}
}
pub open spec fn configuration<U,I>(rho:names::Renaming,h:IndexRenaming<I>,a:Configuration<U,I>)->Configuration<U,I> {
    mx::Configuration {state:names::context(rho,a.state),
        roots:IMap::new(|n:usize|a.roots.dom().contains((rho.backward)(n)),|n:usize|(h.forward)(a.roots[(rho.backward)(n)])),
        current:IMap::new(|n:usize|a.current.dom().contains((rho.backward)(n)),|n:usize|next(h,a.current[(rho.backward)(n)])),
        history:a.history.map(|_:int,e:mx::Entry<U,I>|entry(rho,h,e))}
}

pub proof fn resolve_forward<U>(rho:names::Renaming,a:s::State<U>,actor:usize,key:Port)
    requires names::bijective(rho),r::well_formed(a.control),
    ensures lift::resolve(names::context(rho,a),(rho.forward)(actor),key)==names::parent(rho,lift::resolve(a,actor,key)),
{
    names::observations(rho,a.control,actor);names::well_formed_forward(rho,a.control);
    let z=names::context(rho,a);let target=(rho.forward)(actor);
    if s::registered(a,actor) && !a.control.fibers[actor].provisions.contains(key) {
        if exists|b:Binding|a.control.fibers[actor].committed.contains(b) && lift::names_key(b,key) {
            let old=choose|b:Binding|a.control.fibers[actor].committed.contains(b) && lift::names_key(b,key);
            let renamed=names::binding(rho,old);
            assert(z.control.fibers[target].committed.contains(renamed));
            assert(lift::names_key(renamed,key));
            assert(exists|b:Binding|z.control.fibers[target].committed.contains(b) && lift::names_key(b,key));
            let selected=choose|b:Binding|z.control.fibers[target].committed.contains(b) && lift::names_key(b,key);
            assert(selected.provider==renamed.provider);
        } else {
            assert forall|b:Binding| z.control.fibers[target].committed.contains(b) implies !lift::names_key(b,key) by {
                assert(a.control.fibers[actor].committed.contains(names::binding(names::inverse(rho),b)));
                assert(lift::names_key(names::binding(names::inverse(rho),b),key)==lift::names_key(b,key));
            }
        }
    }
}
pub proof fn update_forward<U>(rho:names::Renaming,a:s::State<U>,actor:usize,key:Port,value:Option<U>)
    requires names::bijective(rho),s::registered(a,actor),a.tables.dom().contains(actor),
    ensures names::context(rho,projection::update_slot(a,actor,key,value))
        ==projection::update_slot(names::context(rho,a),(rho.forward)(actor),key,value),
{
    let updated=match value {Some(v)=>a.tables[actor].insert(key,v),None=>a.tables[actor].remove(key)};
    names::indexed_insert(rho,a.tables,actor,updated);
    assert(names::context(rho,a).tables[(rho.forward)(actor)]==a.tables[actor]);
}
pub proof fn create_forward<U>(rho:names::Renaming,a:s::State<U>,actor:usize,child:usize,deps:ISet<Port>,provisions:ISet<Port>)
    requires names::bijective(rho),
    ensures names::context(rho,mx::create(a,actor,child,deps,provisions))
        ==mx::create(names::context(rho,a),(rho.forward)(actor),(rho.forward)(child),deps,provisions),
{
    names::indexed_insert(rho,a.tables,child,IMap::empty());names::indexed_insert(rho,a.effects,child,0);
    names::indexed_insert(rho,a.iterators,child,None);names::indexed_insert(rho,a.accumulators,child,Seq::empty());
    let left=names::context(rho,mx::create(a,actor,child,deps,provisions));
    let right=mx::create(names::context(rho,a),(rho.forward)(actor),(rho.forward)(child),deps,provisions);
    assert(names::view(rho,ISet::<Binding>::empty()) =~= ISet::empty());
    assert(left.control.fibers =~= right.control.fibers) by {
        assert forall|n:usize| n==(rho.forward)(child) <==> #[trigger] (rho.backward)(n)==child by { }
    }
}

/// Name transport covers failure as well as success. Primitive domains, raw
/// values and actual inverse closures are unchanged by a fiber-name bijection.
#[verifier::spinoff_prover]
pub proof fn run_forward<A,X,U,B,I>(rho:names::Renaming,h:IndexRenaming<I>,lib:Library<A,X,U,B>,source:Node<A,X,U,B,I>,a:s::State<U>,actor:usize,choice:Option<usize>)
    requires names::bijective(rho),r::well_formed(a.control),s::shaped(a),
    ensures run(lib,node(rho,h,source),names::context(rho,a),(rho.forward)(actor),names::parent(rho,choice))
        ==match run(lib,source,a,actor,choice) {None=>None,Some(y)=>Some(landed(rho,h,y))},
{
    names::observations(rho,a.control,actor);
    match source {
        Node::Dependent {node:source_node}=>{
            if choice.is_none() {match source_node {
                d::Node::Unit=>{},
                d::Node::Provision {key,value,..}=>{
                    if s::registered(a,actor) {update_forward(rho,a,actor,key,Some(value));}
                },
                d::Node::Operation {operation,argument,..}=>{
                    let key=(lib.key)(operation);resolve_forward(rho,a,actor,key);
                    if lift::resolve(a,actor,key).is_some() {
                        let provider=lift::resolve(a,actor,key).unwrap();names::observations(rho,a.control,provider);
                        if s::registered(a,provider) && a.tables[provider].dom().contains(key) {
                            let y=(lib.apply)(operation,argument)(a.tables[provider][key]);
                            if y.is_some() {update_forward(rho,a,provider,key,Some(y.unwrap().value));}
                        }
                    }
                },
            }}
        },
        Node::FreshChild {dependencies,provisions,..}=>{
            if choice.is_some() {
                let child=choice.unwrap();create_forward(rho,a,actor,child,dependencies,provisions);
                names::step_equivariant(rho,a.control,mx::create(a,actor,child,dependencies,provisions).control,child,r::Rule::Insert);
            }
        },
    }
}

#[verifier::spinoff_prover]
pub proof fn undo_forward<U>(rho:names::Renaming,source:mx::Receipt<U>,a:s::State<U>)
    requires names::bijective(rho),inv::well_formed(a),
    ensures mx::undo(receipt(rho,source),names::context(rho,a))
        ==match mx::undo(source,a) {None=>None,Some(z)=>Some(names::context(rho,z))},
{
    match source {
        mx::Receipt::Table {receipt:original}=>{
            let actor=original.actor;names::observations(rho,a.control,actor);
            match original.inverse {
                lift::Inverse::Unit=>{},
                lift::Inverse::Provision {key}=>{if s::registered(a,actor) {update_forward(rho,a,actor,key,None);}},
                lift::Inverse::Operation {provider,key,undo}=>{
                    resolve_forward(rho,a,actor,key);names::observations(rho,a.control,provider);
                    if s::registered(a,provider) && a.tables[provider].dom().contains(key) && undo(a.tables[provider][key]).is_some() {
                        update_forward(rho,a,provider,key,undo(a.tables[provider][key]));
                    }
                },
            }
        },
        mx::Receipt::Child {child,..}=>{
            names::observations(rho,a.control,child);
            if s::registered(a,child) {
                let z=s::with_control(a,global::retire_fiber(a.control,child));
                assert(s::child_retire(a,z,child));names::child_retire_forward(rho,a,z,child);
                let target=s::with_control(names::context(rho,a),global::retire_fiber(names::context(rho,a).control,(rho.forward)(child)));
                assert(names::context(rho,z).control.fibers =~= target.control.fibers) by {
                    assert forall|n:usize|s::registered(target,n) implies names::context(rho,z).control.fibers[n]==target.control.fibers[n] by {
                        if n!=(rho.forward)(child) {assert(names::context(rho,z).control.fibers[n]==names::context(rho,a).control.fibers[n]);}
                    }
                }
            }
        },
    }
}

pub proof fn inverse_well_formed<U>(receipt:mx::Receipt<U>,a:s::State<U>)
    requires inv::well_formed(a),mx::undo(receipt,a).is_some(),
    ensures inv::well_formed(mx::undo(receipt,a).unwrap()),
{
    match receipt {
        mx::Receipt::Table {receipt}=>lift::undo_preservation(receipt,a),
        mx::Receipt::Child {child,..}=>inv::retire_preservation(a,mx::undo(receipt,a).unwrap(),child),
    }
}

/// Partial restoration transports the same actual token sequence and history.
/// Undefined inverse application remains undefined after the name change.
pub proof fn restore_forward<U,I>(rho:names::Renaming,h:IndexRenaming<I>,history:Seq<mx::Entry<U,I>>,tokens:Seq<nat>,a:s::State<U>,actor:usize)
    requires names::bijective(rho),inv::well_formed(a),
    ensures mx::restore(history.map(|_:int,e:mx::Entry<U,I>|entry(rho,h,e)),tokens,names::context(rho,a),(rho.forward)(actor))
        ==match mx::restore(history,tokens,a,actor) {None=>None,Some(z)=>Some(names::context(rho,z))},
    decreases tokens.len(),
{
    if tokens.len()>0 && tokens.last()<history.len() {
        let original=history[tokens.last() as int].landed.receipt;
        assert(mx::owner(receipt(rho,original))==(rho.forward)(mx::owner(original)));
        assert((rho.backward)((rho.forward)(mx::owner(original)))==mx::owner(original));
        assert((rho.backward)((rho.forward)(actor))==actor);
        assert(((rho.forward)(mx::owner(original))==(rho.forward)(actor)) == (mx::owner(original)==actor));
        if mx::owner(original)==actor {
            undo_forward(rho,original,a);
            if mx::undo(original,a).is_some() {
                inverse_well_formed(original,a);
                restore_forward(rho,h,history,tokens.drop_last(),mx::undo(original,a).unwrap(),actor);
            }
        }
    }
}

pub proof fn history_forward<A,X,U,B,I>(rho:names::Renaming,h:IndexRenaming<I>,lib:Library<A,X,U,B>,source:Programs<A,X,U,B,I>,history:Seq<mx::Entry<U,I>>)
    requires names::bijective(rho),index_bijective(h),history_sound(lib,source,history),
        forall|i:int|0<=i<history.len() ==> inv::well_formed(history[i].input) && inv::well_formed(history[i].landed.state),
    ensures history_sound(lib,programs(rho,h,source),history.map(|_:int,e:mx::Entry<U,I>|entry(rho,h,e))),
{
    let renamed=history.map(|_:int,e:mx::Entry<U,I>|entry(rho,h,e));
    assert forall|i:int| #![trigger renamed[i]] 0<=i<renamed.len() implies {
        let e=renamed[i];let actor=mx::owner(e.landed.receipt);
        run(lib,programs(rho,h,source)(actor)(e.iterator),e.input,actor,mx::captured_child(e.landed.receipt))==Some(e.landed)
            && mx::receipt_typed(lib,e.landed.receipt) && mx::undo(e.landed.receipt,e.landed.state).is_some()
    } by {
        let old=history[i];let actor=mx::owner(old.landed.receipt);
        run_forward(rho,h,lib,source(actor)(old.iterator),old.input,actor,mx::captured_child(old.landed.receipt));
        undo_forward(rho,old.landed.receipt,old.landed.state);
        match old.landed.receipt {mx::Receipt::Child {..}=>{},mx::Receipt::Table {receipt:original}=>{
            match original.inverse {lift::Inverse::Unit=>{},lift::Inverse::Provision {..}=>{},lift::Inverse::Operation {..}=>{}}
        }}
    }
}

/// Continuation carriers may contain names. The support contract says exactly
/// when extending a name bijection leaves an existing continuation unchanged.
#[verifier::reject_recursive_types(I)]
pub struct NameAction<I> {pub apply:spec_fn(names::Renaming,I)->I,pub support:spec_fn(I)->ISet<usize>}
pub open spec fn action_map<I>(action:NameAction<I>,rho:names::Renaming)->IndexRenaming<I> {
    IndexRenaming {forward:|id:I|(action.apply)(rho,id),backward:|id:I|(action.apply)(names::inverse(rho),id)}
}
pub open spec fn supported_action<I>(action:NameAction<I>)->bool {
    &&& forall|rho:names::Renaming| names::bijective(rho) ==> index_bijective(action_map(action,rho))
    &&& forall|rho:names::Renaming,other:names::Renaming,id:I| #![trigger (action.apply)(rho,id),(action.apply)(other,id)] names::bijective(rho) && names::bijective(other)
        && names::agrees_on(rho,other,(action.support)(id)) ==> (action.apply)(rho,id)==(action.apply)(other,id)
}
pub open spec fn name_free<I>()->NameAction<I> {
    NameAction {apply:|_:names::Renaming,id:I|id,support:|_:I|ISet::empty()}
}
pub proof fn name_free_action<I>() ensures supported_action(name_free::<I>()), { }
pub open spec fn atomic_indices()->NameAction<usize> {
    NameAction {apply:|rho:names::Renaming,id:usize|(rho.forward)(id),support:|id:usize|ISet::empty().insert(id)}
}
pub proof fn atomic_action() ensures supported_action(atomic_indices()), {
    let action=atomic_indices();
    assert forall|rho:names::Renaming| names::bijective(rho) implies index_bijective(action_map(action,rho)) by {
        assert forall|id:usize| #[trigger] (action_map(action,rho).backward)((action_map(action,rho).forward)(id))==id by {
            assert((rho.backward)((rho.forward)(id))==id);
        }
        assert forall|id:usize| #[trigger] (action_map(action,rho).forward)((action_map(action,rho).backward)(id))==id by {
            assert((rho.forward)((rho.backward)(id))==id);
        }
    }
    assert forall|rho:names::Renaming,other:names::Renaming,id:usize| #![trigger (action.apply)(rho,id),(action.apply)(other,id)]
        names::bijective(rho) && names::bijective(other) && names::agrees_on(rho,other,(action.support)(id))
        implies (action.apply)(rho,id)==(action.apply)(other,id) by {assert((action.support)(id).contains(id));}
}

pub open spec fn receipt_names<U>(value:mx::Receipt<U>)->ISet<usize> {
    match value {
        mx::Receipt::Child {actor,child}=>ISet::empty().insert(actor).insert(child),
        mx::Receipt::Table {receipt}=>match receipt.inverse {
            lift::Inverse::Operation {provider,..}=>ISet::empty().insert(receipt.actor).insert(provider),
            _=>ISet::empty().insert(receipt.actor),
        },
    }
}
pub open spec fn next_names<I>(action:NameAction<I>,id:Option<I>)->ISet<usize> {
    match id {None=>ISet::empty(),Some(id)=>(action.support)(id)}
}
pub open spec fn entry_names<U,I>(action:NameAction<I>,e:mx::Entry<U,I>)->ISet<usize> {
    e.input.control.fibers.dom().union(e.landed.state.control.fibers.dom()).union(receipt_names(e.landed.receipt))
        .union((action.support)(e.iterator)).union(next_names(action,e.landed.next)).union(match e.landed.spawn {
            None=>ISet::empty(),Some((child,root))=>(action.support)(root).insert(child),
        })
}
pub open spec fn configuration_names<U,I>(action:NameAction<I>,a:Configuration<U,I>)->ISet<usize> {
    a.state.control.fibers.dom()
        .union(ISet::new(|name:usize|exists|n:usize|a.roots.dom().contains(n) && (action.support)(a.roots[n]).contains(name)))
        .union(ISet::new(|name:usize|exists|n:usize|a.current.dom().contains(n) && next_names(action,a.current[n]).contains(name)))
        .union(ISet::new(|name:usize|exists|i:int|0<=i<a.history.len() && entry_names(action,a.history[i]).contains(name)))
}
pub open spec fn supported_configuration<U,I>(a:Configuration<U,I>)->bool {
    &&& s::shaped(a.state) && r::well_formed(a.state.control)
    &&& a.roots.dom()==a.state.control.fibers.dom() && a.current.dom()==a.roots.dom()
    &&& forall|i:int|0<=i<a.history.len() ==> s::shaped(a.history[i].input) && r::well_formed(a.history[i].input.control)
        && s::shaped(a.history[i].landed.state) && r::well_formed(a.history[i].landed.state.control)
}
pub proof fn agree_subset(rho:names::Renaming,other:names::Renaming,big:ISet<usize>,small:ISet<usize>)
    requires names::agrees_on(rho,other,big),small.subset_of(big),
    ensures names::agrees_on(rho,other,small),
{
    assert forall|name:usize| #[trigger] small.contains(name) implies (rho.forward)(name)==(other.forward)(name) by {assert(big.contains(name));}
}
pub proof fn receipt_agrees<U>(rho:names::Renaming,other:names::Renaming,value:mx::Receipt<U>)
    requires names::agrees_on(rho,other,receipt_names(value)),
    ensures receipt(rho,value)==receipt(other,value),
{match value {
    mx::Receipt::Child {actor,child}=>{assert(receipt_names(value).contains(actor));assert(receipt_names(value).contains(child));},
    mx::Receipt::Table {receipt}=>{
        assert(receipt_names(value).contains(receipt.actor));
        match receipt.inverse {lift::Inverse::Operation {provider,..}=>{assert(receipt_names(value).contains(provider));},_=>{}}
    }
}}
pub proof fn entry_agrees<U,I>(action:NameAction<I>,rho:names::Renaming,other:names::Renaming,e:mx::Entry<U,I>)
    requires supported_action(action),names::bijective(rho),names::bijective(other),names::agrees_on(rho,other,entry_names(action,e)),
        s::shaped(e.input),r::well_formed(e.input.control),s::shaped(e.landed.state),r::well_formed(e.landed.state.control),
    ensures entry(rho,action_map(action,rho),e)==entry(other,action_map(action,other),e),
{
    let support=entry_names(action,e);
    agree_subset(rho,other,support,e.input.control.fibers.dom());agree_subset(rho,other,support,e.landed.state.control.fibers.dom());
    names::context_agrees(rho,other,e.input);names::context_agrees(rho,other,e.landed.state);
    agree_subset(rho,other,support,receipt_names(e.landed.receipt));receipt_agrees(rho,other,e.landed.receipt);
    agree_subset(rho,other,support,(action.support)(e.iterator));
    assert((action.apply)(rho,e.iterator)==(action.apply)(other,e.iterator));
    if e.landed.next.is_some() {
        let id=e.landed.next.unwrap();agree_subset(rho,other,support,(action.support)(id));
        assert((action.apply)(rho,id)==(action.apply)(other,id));
    }
    if e.landed.spawn.is_some() {
        let (child,root)=e.landed.spawn.unwrap();agree_subset(rho,other,support,(action.support)(root));
        assert((action.apply)(rho,root)==(action.apply)(other,root));assert(support.contains(child));
    }
}

/// All old history is fixed by an extension protecting this support, including
/// removed child identities, captured providers and name-bearing continuations.
#[verifier::spinoff_prover]
pub proof fn configuration_agrees<U,I>(action:NameAction<I>,rho:names::Renaming,other:names::Renaming,a:Configuration<U,I>)
    requires supported_action(action),supported_configuration(a),names::bijective(rho),names::bijective(other),
        names::agrees_on(rho,other,configuration_names(action,a)),
    ensures configuration(rho,action_map(action,rho),a)==configuration(other,action_map(action,other),a),
{
    agree_subset(rho,other,configuration_names(action,a),a.state.control.fibers.dom());
    names::context_agrees(rho,other,a.state);names::image_agrees(rho,other,a.roots.dom());
    let left=configuration(rho,action_map(action,rho),a);let right=configuration(other,action_map(action,other),a);
    assert(left.roots =~= right.roots) by {
        assert forall|n:usize|left.roots.dom().contains(n) implies left.roots[n]==right.roots[n] by {
            let old=(rho.backward)(n);let id=a.roots[old];
            assert(names::agrees_on(rho,other,(action.support)(id))) by {
                assert forall|name:usize| #[trigger] (action.support)(id).contains(name) implies (rho.forward)(name)==(other.forward)(name) by {
                    assert(configuration_names(action,a).contains(name));
                }
            }
        }
    }
    assert(left.current =~= right.current) by {
        assert forall|n:usize|left.current.dom().contains(n) implies left.current[n]==right.current[n] by {
            let old=(rho.backward)(n);
            if a.current[old].is_some() {
                let id=a.current[old].unwrap();
                assert(names::agrees_on(rho,other,(action.support)(id))) by {
                    assert forall|name:usize| #[trigger] (action.support)(id).contains(name) implies (rho.forward)(name)==(other.forward)(name) by {
                        assert(configuration_names(action,a).contains(name));
                    }
                }
            }
        }
    }
    assert(left.history =~= right.history) by {
        assert forall|i:int|0<=i<a.history.len() implies left.history[i]==right.history[i] by {
            assert(names::agrees_on(rho,other,entry_names(action,a.history[i]))) by {
                assert forall|name:usize| #[trigger] entry_names(action,a.history[i]).contains(name) implies (rho.forward)(name)==(other.forward)(name) by {
                    assert(configuration_names(action,a).contains(name));
                }
            }
            entry_agrees(action,rho,other,a.history[i]);
        }
    }
}

/// A structural, whole-program naturality condition. It compares syntax after
/// instantiating binders; it does not assume any execution or inverse theorem.
pub open spec fn natural<A,X,U,B,I>(action:NameAction<I>,source:Programs<A,X,U,B,I>)->bool {
    forall|rho:names::Renaming,actor:usize,id:I,choice:Option<usize>| names::bijective(rho) ==>
        #[trigger] instantiate(source((rho.forward)(actor))((action.apply)(rho,id)),names::parent(rho,choice))
            ==instantiate(node(rho,action_map(action,rho),source(actor)(id)),names::parent(rho,choice))
}

/// Different fresh choices keep the complete past fixed and produce related
/// actual yields in the same installed program. Subsequent external names must
/// be transported by the resulting bijection; literal-name confluence is not claimed.
#[verifier::spinoff_prover]
pub proof fn fresh_choice<A,X,U,B,I>(action:NameAction<I>,rho:names::Renaming,lib:Library<A,X,U,B>,source:Programs<A,X,U,B,I>,a:Configuration<U,I>,actor:usize,id:I,child:usize,destination:usize,protected:ISet<usize>)
    requires supported_action(action),natural(action,source),supported_configuration(a),names::bijective(rho),
        configuration_names(action,a).subset_of(protected),(action.support)(id).subset_of(protected),
        !protected.contains(child),!names::name_image(rho,protected).contains(destination),
        run(lib,source(actor)(id),a.state,actor,Some(child)).is_some(),
    ensures {
        let extended=names::extend(rho,child,destination);let h=action_map(action,extended);
        &&& names::bijective(extended) && names::agrees_on(rho,extended,protected)
        &&& configuration(rho,action_map(action,rho),a)==configuration(extended,h,a)
        &&& run(lib,source((rho.forward)(actor))((action.apply)(rho,id)),configuration(rho,action_map(action,rho),a).state,(rho.forward)(actor),Some(destination))
            ==Some(landed(extended,h,run(lib,source(actor)(id),a.state,actor,Some(child)).unwrap()))
    },
{
    allocation_guard(lib,source(actor)(id),a.state,actor,Some(child));
    names::fresh_extension(rho,protected,child,destination);
    let extended=names::extend(rho,child,destination);let h=action_map(action,extended);
    assert(names::agrees_on(rho,extended,configuration_names(action,a)));
    configuration_agrees(action,rho,extended,a);
    assert(s::registered(a.state,actor));assert(protected.contains(actor));
    assert(names::agrees_on(rho,extended,(action.support)(id)));
    run_forward(extended,h,lib,source(actor)(id),a.state,actor,Some(child));
    assert(instantiate(source((extended.forward)(actor))((action.apply)(extended,id)),Some(destination))
        ==instantiate(node(extended,h,source(actor)(id)),Some(destination)));
}

/// An old child inverse targets its captured identity even after another child
/// is allocated. Retirement is idempotent and does not redirect by program ID.
pub proof fn old_receipt_keeps_identity<U>(a:s::State<U>,actor:usize,old_child:usize,new_child:usize)
    requires s::registered(a,old_child),s::registered(a,new_child),old_child!=new_child,
    ensures mx::undo(mx::Receipt::Child {actor,child:old_child},a).is_some(),
        mx::undo(mx::Receipt::Child {actor,child:old_child},a).unwrap().control.fibers[old_child].retired,
        mx::undo(mx::Receipt::Child {actor,child:old_child},a).unwrap().control.fibers[new_child]==a.control.fibers[new_child],
{ }
pub proof fn occupied_choice_fails<A,X,U,B,I>(lib:Library<A,X,U,B>,node:Node<A,X,U,B,I>,a:s::State<U>,actor:usize,child:usize)
    requires s::registered(a,child),
    ensures run(lib,node,a,actor,Some(child)).is_none(),
{match node {Node::Dependent {..}=>{},Node::FreshChild {..}=>{}}}

/// A nontrivial name-carrying family: the child root is the allocated name.
/// At its own root that child terminates; any other index invokes the binder.
pub open spec fn atomic_program()->Programs<(),(),(),(),usize> {
    |actor:usize| |id:usize|if id==actor {Node::Dependent {node:d::Node::Unit}}
        else {Node::FreshChild {dependencies:ISet::empty(),provisions:ISet::empty(),body:|child:usize|(child,None)}}
}
pub proof fn atomic_program_natural()
    ensures natural(atomic_indices(),atomic_program()),
{
    assert forall|rho:names::Renaming,actor:usize,id:usize,choice:Option<usize>|names::bijective(rho) implies
        #[trigger] instantiate(atomic_program()((rho.forward)(actor))((atomic_indices().apply)(rho,id)),names::parent(rho,choice))
            ==instantiate(node(rho,action_map(atomic_indices(),rho),atomic_program()(actor)(id)),names::parent(rho,choice)) by {
        assert((rho.backward)((rho.forward)(id))==id);assert((rho.backward)((rho.forward)(actor))==actor);
        if choice.is_some() {assert((rho.backward)((rho.forward)(choice.unwrap()))==choice.unwrap());}
    }
}

// The fresh constructor belongs to one least grammar with its child roots.
// The binder's universal child premise is syntactic and independent of the
// current registry; runtime freshness remains a separate strict guard.
pub type MemberName<I> = (usize,ISet<Port>,ISet<Port>,I);
pub type Members<I> = ISet<MemberName<I>>;
pub open spec fn local<I>(members:Members<I>,actor:usize,keys:ISet<Port>,provisions:ISet<Port>)->ISet<I> {
    ISet::new(|id:I|members.contains((actor,keys,provisions,id)))
}
pub open spec fn permitted<A,X,U,B,I>(lib:Library<A,X,U,B>,keys:ISet<Port>,provisions:ISet<Port>,source:Node<A,X,U,B,I>)->bool {
    match source {Node::Dependent {node}=>d::permitted(lib,keys,provisions,node),Node::FreshChild {..}=>true}
}
pub open spec fn continuations<A,X,U,B,I>(lib:Library<A,X,U,B>,source:Node<A,X,U,B,I>,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,members:Members<I>)->bool {
    match source {
        Node::Dependent {node}=>d::continuations(lib,node,local(members,actor,keys,provisions)),
        Node::FreshChild {dependencies,provisions:provided,body}=>forall|child:usize| #![trigger body(child)] {
            let (root,next)=body(child);
            members.contains((child,dependencies.union(provided),provided,root))
                && (next.is_some() ==> members.contains((actor,keys,provisions,next.unwrap())))
        },
    }
}
pub open spec fn obligation<A,X,U,B,I>(lib:Library<A,X,U,B>,source:Node<A,X,U,B,I>,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,members:Members<I>)->bool {
    permitted(lib,keys,provisions,source) && continuations(lib,source,actor,keys,provisions,members)
}
pub open spec fn closed<A,X,U,B,I>(lib:Library<A,X,U,B>,source:Programs<A,X,U,B,I>,members:Members<I>)->bool {
    forall|name:MemberName<I>| obligation(lib,source(name.0)(name.3),name.0,name.1,name.2,members) ==> members.contains(name)
}
pub open spec fn member<A,X,U,B,I>(lib:Library<A,X,U,B>,source:Programs<A,X,U,B,I>,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,id:I)->bool {
    forall|members:Members<I>|closed(lib,source,members) ==> members.contains((actor,keys,provisions,id))
}
pub open spec fn members<A,X,U,B,I>(lib:Library<A,X,U,B>,source:Programs<A,X,U,B,I>)->Members<I> {
    ISet::new(|name:MemberName<I>|member(lib,source,name.0,name.1,name.2,name.3))
}
pub proof fn continuations_monotone<A,X,U,B,I>(lib:Library<A,X,U,B>,source:Node<A,X,U,B,I>,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,a:Members<I>,z:Members<I>)
    requires a.subset_of(z),continuations(lib,source,actor,keys,provisions,a),
    ensures continuations(lib,source,actor,keys,provisions,z),
{
    match source {
        Node::Dependent {node}=>{
            assert(local(a,actor,keys,provisions).subset_of(local(z,actor,keys,provisions)));
            d::continuations_monotone(lib,node,local(a,actor,keys,provisions),local(z,actor,keys,provisions));
        },
        Node::FreshChild {dependencies,provisions:provided,body}=>{
            assert forall|child:usize| #![trigger body(child)] z.contains((child,dependencies.union(provided),provided,body(child).0))
                && (body(child).1.is_some() ==> z.contains((actor,keys,provisions,body(child).1.unwrap()))) by {
                assert(a.contains((child,dependencies.union(provided),provided,body(child).0)));
            }
        },
    }
}
pub proof fn constructor_member<A,X,U,B,I>(lib:Library<A,X,U,B>,source:Programs<A,X,U,B,I>,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,id:I)
    requires obligation(lib,source(actor)(id),actor,keys,provisions,members(lib,source)),
    ensures member(lib,source,actor,keys,provisions,id),
{
    assert forall|set:Members<I>|closed(lib,source,set) implies set.contains((actor,keys,provisions,id)) by {
        assert(members(lib,source).subset_of(set));
        continuations_monotone(lib,source(actor)(id),actor,keys,provisions,members(lib,source),set);
        assert(obligation(lib,source(actor)(id),actor,keys,provisions,set));
    }
}
pub proof fn member_unfolding<A,X,U,B,I>(lib:Library<A,X,U,B>,source:Programs<A,X,U,B,I>,actor:usize,keys:ISet<Port>,provisions:ISet<Port>,id:I)
    ensures member(lib,source,actor,keys,provisions,id)==obligation(lib,source(actor)(id),actor,keys,provisions,members(lib,source)),
{
    let all=members(lib,source);
    if obligation(lib,source(actor)(id),actor,keys,provisions,all) {constructor_member(lib,source,actor,keys,provisions,id);}
    let good=ISet::new(|name:MemberName<I>|all.contains(name) && obligation(lib,source(name.0)(name.3),name.0,name.1,name.2,all));
    assert(good.subset_of(all));
    assert(closed(lib,source,good)) by {
        assert forall|name:MemberName<I>|obligation(lib,source(name.0)(name.3),name.0,name.1,name.2,good) implies good.contains(name) by {
            continuations_monotone(lib,source(name.0)(name.3),name.0,name.1,name.2,good,all);
            constructor_member(lib,source,name.0,name.1,name.2,name.3);
        }
    }
    if member(lib,source,actor,keys,provisions,id) {assert(good.contains((actor,keys,provisions,id)));}
}

pub proof fn atomic_program_member(lib:Library<(),(),(),()>,actor:usize,id:usize)
    ensures member(lib,atomic_program(),actor,ISet::empty(),ISet::empty(),id),
{
    assert forall|child:usize|member(lib,atomic_program(),child,ISet::empty(),ISet::empty(),child) by {
        constructor_member(lib,atomic_program(),child,ISet::empty(),ISet::empty(),child);
    }
    constructor_member(lib,atomic_program(),actor,ISet::empty(),ISet::empty(),id);
}

}
