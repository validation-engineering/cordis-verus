//! Dependent table operations and child creation in one strict partial grammar.
//!
//! Continuations retain their original type. Actual receipts capture either a
//! table inverse or the child returned by creation. Removal retains all child
//! references in live journals; table inverse failure remains a strict domain.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, contexts as c, dependent_grammar as d, global, preservation as inv,
    projection as p, refinement as r, Phase, Port,
};
use crate::{dependent_lift as dep, grammar_lift as lift, mixed_syntax as syntax, semantics as s};
use vstd::prelude::*;

verus! {
pub type Library<A,X,U,B> = dep::Library<A,X,U,B>;
pub type Node<A,X,U,B,I> = syntax::Node<A,X,U,B,I>;
pub type Programs<A,X,U,B,I> = syntax::Programs<A,X,U,B,I>;

#[verifier::reject_recursive_types(U)]
pub enum Receipt<U> { Table {receipt:lift::Receipt<U>}, Child {actor:usize,child:usize} }
pub open spec fn owner<U>(receipt:Receipt<U>)->usize {
    match receipt {Receipt::Table {receipt}=>receipt.actor,Receipt::Child {actor,..}=>actor}
}
pub open spec fn captured_child<U>(receipt:Receipt<U>)->Option<usize> {
    match receipt {Receipt::Table {..}=>None,Receipt::Child {child,..}=>Some(child)}
}
#[verifier::reject_recursive_types(U)]
pub struct Landed<U,I> {pub state:s::State<U>,pub receipt:Receipt<U>,pub next:Option<I>,pub spawn:Option<(usize,I)>}

pub open spec fn create<U>(a:s::State<U>,actor:usize,child:usize,dependencies:ISet<Port>,provisions:ISet<Port>)->s::State<U> {
    s::State {
        control:r::State {fibers:a.control.fibers.insert(child,r::Fiber {parent:Some(actor),retired:false,
            phase:Phase::Inactive,dependencies,provisions,committed:ISet::empty()})},
        tables:a.tables.insert(child,IMap::empty()),effects:a.effects.insert(child,0),
        iterators:a.iterators.insert(child,None),accumulators:a.accumulators.insert(child,Seq::empty()),
    }
}
/// The child branch checks the ordinary Insert guards, not a successor safety
/// predicate. Thus a duplicate identity or conflicting provision stays undefined.
pub open spec fn run<A,X,U,B,I>(lib:Library<A,X,U,B>,node:Node<A,X,U,B,I>,a:s::State<U>,actor:usize)->Option<Landed<U,I>> {
    match node {
        Node::Dependent {node}=>match dep::run(lib,node,a,actor) {
            None=>None,Some(y)=>Some(Landed {state:y.state,receipt:Receipt::Table {receipt:y.receipt},next:y.next,spawn:None}),
        },
        Node::Child {child,dependencies,provisions,root,next}=>{
            let z=create(a,actor,child,dependencies,provisions);
            if !s::registered(a,actor) || !r::step(a.control,z.control,child,r::Rule::Insert) {None}
            else {Some(Landed {state:z,receipt:Receipt::Child {actor,child},next,spawn:Some((child,root))})}
        },
    }
}
pub open spec fn undo<U>(receipt:Receipt<U>,a:s::State<U>)->Option<s::State<U>> {
    match receipt {
        Receipt::Table {receipt}=>lift::undo(receipt,a),
        Receipt::Child {child,..}=>if s::registered(a,child) {Some(s::with_control(a,global::retire_fiber(a.control,child)))} else {None},
    }
}
pub open spec fn receipt_typed<A,X,U,B>(lib:Library<A,X,U,B>,receipt:Receipt<U>)->bool {
    match receipt {Receipt::Table {receipt}=>dep::receipt_typed(lib,receipt),Receipt::Child {..}=>true}
}
pub open spec fn component_member<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:s::State<U>,actor:usize,id:I)->bool {
    syntax::member(lib,programs,actor,dep::declarations(a,actor),a.control.fibers[actor].provisions,id)
}

/// The child inverse restores the all-table observation, not literal registry
/// identity. Its captured child remains present and becomes retired.
pub proof fn run_admissible<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,node:Node<A,X,U,B,I>,a:s::State<U>,actor:usize)
    requires d::primitive_theory(eq,lib),inv::well_formed(a),dep::typed(lib,a),dep::finite_context(a),
        syntax::permitted(lib,dep::declarations(a,actor),a.control.fibers[actor].provisions,node),run(lib,node,a,actor).is_some(),
    ensures {
        let out=run(lib,node,a,actor).unwrap();
        &&& owner(out.receipt)==actor && s::registered(a,actor)
        &&& inv::forward_map(a,out.state,actor) && inv::well_formed(out.state)
        &&& dep::typed(lib,out.state) && dep::finite_context(out.state) && receipt_typed(lib,out.receipt)
        &&& undo(out.receipt,out.state).is_some()
        &&& (out.spawn.is_none() ==> out.state.control==a.control && out.state.effects==a.effects
            && out.state.iterators==a.iterators && out.state.accumulators==a.accumulators)
        &&& (out.spawn.is_some() ==> {
            let child=out.spawn.unwrap().0;
            &&& captured_child(out.receipt)==Some(child) && child!=actor && !s::registered(a,child)
            &&& inv::child_map(a,out.state,actor,child) && out.state.effects[child]==0
        })
        &&& p::project(undo(out.receipt,out.state).unwrap(),ISet::full())==p::project(a,ISet::full())
    },
{
    match node {
        Node::Dependent {node}=>{dep::run_admissible(eq,lib,node,a,actor);},
        Node::Child {child,dependencies,provisions,..}=>{
            let z=create(a,actor,child,dependencies,provisions);
            assert(inv::child_map(a,z,actor,child));inv::child_preservation(a,z,actor,child);
            assert(dep::typed(lib,z)) by {assert forall|n:usize,k:Port| s::registered(z,n) && z.tables[n].dom().contains(k)
                implies #[trigger] (lib.values)(k,z.tables[n][k]) by {if n!=child {assert(s::registered(a,n));}}}
            p::unique_owner(a);p::empty_insertion(a,z,child,ISet::full());
            let table=dep::context(a);assert(c::embed(table)==p::project(z,ISet::full()));
            ch::concrete_child_retirement(z,child);
            let retired=undo(Receipt::Child {actor,child},z).unwrap();
            s::child_inverse_observation(a,z,retired,actor,child);
            inv::retire_preservation(z,retired,child);p::unique_owner(z);p::unique_owner(retired);
            assert(p::bindings_equal(z,retired)) by {assert forall|key:Port,n:usize| p::owns(z,key,n)==p::owns(retired,key,n)
                && (p::owns(z,key,n) ==> z.tables[n][key]==retired.tables[n][key]) by { }}
            p::projection_equal(z,retired,ISet::full());
        },
    }
}

/// Successful inverse application preserves registry identities and journals.
/// Retirement is the only control change allowed by the child receipt.
pub proof fn inverse_preservation<A,X,U,B>(lib:Library<A,X,U,B>,receipt:Receipt<U>,a:s::State<U>)
    requires inv::well_formed(a),dep::typed(lib,a),dep::finite_context(a),receipt_typed(lib,receipt),undo(receipt,a).is_some(),
    ensures inv::well_formed(undo(receipt,a).unwrap()),dep::typed(lib,undo(receipt,a).unwrap()),dep::finite_context(undo(receipt,a).unwrap()),
        inv::inverse_map(a,undo(receipt,a).unwrap(),owner(receipt)),
        ch::recovery_frame(a,undo(receipt,a).unwrap()),
        undo(receipt,a).unwrap().effects==a.effects,undo(receipt,a).unwrap().iterators==a.iterators,
        undo(receipt,a).unwrap().accumulators==a.accumulators,
        forall|n:usize| s::registered(a,n) ==> a.control.fibers[n].committed==undo(receipt,a).unwrap().control.fibers[n].committed,
{
    match receipt {
        Receipt::Table {receipt}=>{dep::typed_inverse(lib,receipt,a);lift::undo_preservation(receipt,a);},
        Receipt::Child {child,..}=>{
            let z=undo(receipt,a).unwrap();ch::concrete_child_retirement(a,child);inv::retire_preservation(a,z,child);
            assert(a.control.fibers.dom() =~= z.control.fibers.dom());
            p::unique_owner(a);p::unique_owner(z);
            assert(p::bindings_equal(a,z)) by {assert forall|key:Port,n:usize| p::owns(a,key,n)==p::owns(z,key,n)
                && (p::owns(a,key,n) ==> a.tables[n][key]==z.tables[n][key]) by { }}
            p::projection_equal(a,z,ISet::full());let table=dep::context(a);assert(c::embed(table)==p::project(z,ISet::full()));
        },
    }
}

#[verifier::reject_recursive_types(U)]
pub struct Entry<U,I> {pub input:s::State<U>,pub iterator:I,pub landed:Landed<U,I>}
#[verifier::reject_recursive_types(U)]
pub struct Configuration<U,I> {pub state:s::State<U>,pub roots:IMap<usize,I>,pub current:IMap<usize,Option<I>>,pub history:Seq<Entry<U,I>>}
pub open spec fn metadata<U,I>(a:Configuration<U,I>)->bool {
    &&& a.roots.dom()==a.state.control.fibers.dom() && a.current.dom()==a.roots.dom()
    &&& forall|n:usize| s::registered(a.state,n) ==> a.state.effects[n]==0 && a.state.iterators[n]==#[trigger] dep::marker(a.current[n])
}
pub open spec fn members<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>)->bool {
    forall|n:usize| s::registered(a.state,n) ==> component_member(lib,programs,a.state,n,a.roots[n])
        && (a.current[n].is_some() ==> component_member(lib,programs,a.state,n,a.current[n].unwrap()))
}
pub open spec fn history_sound<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,history:Seq<Entry<U,I>>)->bool {
    forall|i:int| #![trigger history[i]] 0<=i<history.len() ==> {
        let e=history[i];let actor=owner(e.landed.receipt);
        &&& run(lib,programs(actor)(e.iterator),e.input,actor)==Some(e.landed)
        &&& receipt_typed(lib,e.landed.receipt) && undo(e.landed.receipt,e.landed.state).is_some()
    }
}
pub open spec fn kind<U,I>(history:Seq<Entry<U,I>>)->spec_fn(nat)->Option<usize> {
    |token:nat|if token<history.len() {captured_child(history[token as int].landed.receipt)} else {None}
}
pub open spec fn tokens_valid<U,I>(a:Configuration<U,I>)->bool {
    forall|actor:usize,i:int| #![trigger a.state.accumulators[actor][i]] s::registered(a.state,actor) && 0<=i<a.state.accumulators[actor].len() ==> {
        let token=a.state.accumulators[actor][i];
        &&& token<a.history.len() && owner(a.history[token as int].landed.receipt)==actor
    }
}
pub open spec fn well_formed<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>)->bool {
    inv::well_formed(a.state) && dep::typed(lib,a.state) && dep::finite_context(a.state) && metadata(a) && members(lib,programs,a)
        && history_sound(lib,programs,a.history) && tokens_valid(a) && ch::retained(kind(a.history),a.state)
}
pub open spec fn restore<U,I>(history:Seq<Entry<U,I>>,tokens:Seq<nat>,a:s::State<U>,actor:usize)->Option<s::State<U>>
    decreases tokens.len(),
{
    if tokens.len()==0 {Some(a)}
    else if tokens.last()>=history.len() || owner(history[tokens.last() as int].landed.receipt)!=actor {None}
    else {match undo(history[tokens.last() as int].landed.receipt,a) {
        None=>None,Some(next)=>restore(history,tokens.drop_last(),next,actor),
    }}
}
pub proof fn restore_preservation<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,history:Seq<Entry<U,I>>,tokens:Seq<nat>,a:s::State<U>,actor:usize)
    requires inv::well_formed(a),dep::typed(lib,a),dep::finite_context(a),history_sound(lib,programs,history),restore(history,tokens,a,actor).is_some(),
    ensures inv::well_formed(restore(history,tokens,a,actor).unwrap()),dep::typed(lib,restore(history,tokens,a,actor).unwrap()),dep::finite_context(restore(history,tokens,a,actor).unwrap()),
        ch::recovery_frame(a,restore(history,tokens,a,actor).unwrap()),
        restore(history,tokens,a,actor).unwrap().effects==a.effects,
        restore(history,tokens,a,actor).unwrap().iterators==a.iterators,
        restore(history,tokens,a,actor).unwrap().accumulators==a.accumulators,
        forall|n:usize| s::registered(a,n) ==> a.control.fibers[n].committed==restore(history,tokens,a,actor).unwrap().control.fibers[n].committed,
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let receipt=history[tokens.last() as int].landed.receipt;
        inverse_preservation(lib,receipt,a);
        let b=undo(receipt,a).unwrap();restore_preservation(lib,programs,history,tokens.drop_last(),b,actor);
        let z=restore(history,tokens,a,actor).unwrap();
        assert forall|n:usize| s::registered(a,n) implies r::interface_same(a.control.fibers[n],z.control.fibers[n])
            && a.control.fibers[n].phase==z.control.fibers[n].phase && (a.control.fibers[n].retired ==> z.control.fibers[n].retired)
            && a.control.fibers[n].committed==z.control.fibers[n].committed by {assert(s::registered(b,n));}
    }
}

pub open spec fn entry<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,actor:usize)->Entry<U,I> {
    let iterator=a.current[actor].unwrap();Entry {input:a.state,iterator,landed:run(lib,programs(actor)(iterator),a.state,actor).unwrap()}
}
pub open spec fn land<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,actor:usize,phase:Phase)->Configuration<U,I> {
    let e=entry(lib,programs,a,actor);let next=if phase==Phase::Loading {e.landed.next} else {None};
    let roots=match e.landed.spawn {None=>a.roots,Some((child,root))=>a.roots.insert(child,root)};
    let current=match e.landed.spawn {None=>a.current,Some((child,_))=>a.current.insert(child,None)};
    Configuration {state:s::edit(e.landed.state,actor,phase,a.state.control.fibers[actor].committed,dep::marker(next),a.state.accumulators[actor].push(a.history.len())),
        roots,current:current.insert(actor,next),history:a.history.push(e)}
}
pub open spec fn edit<U,I>(a:Configuration<U,I>,actor:usize,phase:Phase,committed:ISet<crate::Binding>,next:Option<I>,tokens:Seq<nat>)->Configuration<U,I> {
    Configuration {state:s::edit(a.state,actor,phase,committed,dep::marker(next),tokens),roots:a.roots,current:a.current.insert(actor,next),history:a.history}
}
pub open spec fn unload<U,I>(a:Configuration<U,I>,actor:usize)->Configuration<U,I> {
    Configuration {state:s::edit(restore(a.history,a.state.accumulators[actor],a.state,actor).unwrap(),actor,Phase::Inactive,ISet::empty(),None,Seq::empty()),
        roots:a.roots,current:a.current.insert(actor,None),history:a.history}
}
pub open spec fn step<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,z:Configuration<U,I>,actor:usize,rule:r::Rule)->bool {
    match rule {
        r::Rule::Insert=>inv::insert_map(a.state,z.state,actor) && z.state.effects[actor]==0
            && z.roots==a.roots.insert(actor,z.roots[actor]) && z.current==a.current.insert(actor,None) && z.history==a.history
            && component_member(lib,programs,z.state,actor,z.roots[actor]),
        r::Rule::Retire=>s::child_retire(a.state,z.state,actor) && z.roots==a.roots && z.current==a.current && z.history==a.history,
        r::Rule::Remove=>r::step(a.state.control,z.state.control,actor,rule) && a.state.tables[actor].is_empty()
            && ch::remove_unreferenced(kind(a.history),a.state,actor)
            && z.state==s::erase(a.state,actor) && z.roots==a.roots.remove(actor) && z.current==a.current.remove(actor) && z.history==a.history,
        r::Rule::Begin=>s::registered(a.state,actor) && a.state.control.fibers[actor].phase==Phase::Inactive
            && s::target(a.state,actor,z.state.control.fibers[actor].committed)
            && z==edit(a,actor,Phase::Loading,z.state.control.fibers[actor].committed,Some(a.roots[actor]),Seq::empty()),
        r::Rule::Iter | r::Rule::Finish=>{
            let out=run(lib,programs(actor)(a.current[actor].unwrap()),a.state,actor);
            &&& s::registered(a.state,actor) && a.state.control.fibers[actor].phase==Phase::Loading && a.current[actor].is_some()
            &&& s::coherent(a.state,actor) && out.is_some()
            &&& (rule==r::Rule::Iter)==out.unwrap().next.is_some()
            &&& z==land(lib,programs,a,actor,if rule==r::Rule::Iter {Phase::Loading} else {Phase::Active})
        },
        r::Rule::Divert=>s::registered(a.state,actor) && a.state.control.fibers[actor].phase==Phase::Loading && a.current[actor].is_some() && !s::coherent(a.state,actor)
            && (z==edit(a,actor,Phase::Unloading,a.state.control.fibers[actor].committed,None,a.state.accumulators[actor])
                || (run(lib,programs(actor)(a.current[actor].unwrap()),a.state,actor).is_some() && z==land(lib,programs,a,actor,Phase::Unloading))),
        r::Rule::Leave=>s::registered(a.state,actor) && a.state.control.fibers[actor].phase==Phase::Active && !s::coherent(a.state,actor)
            && z==edit(a,actor,Phase::Unloading,a.state.control.fibers[actor].committed,None,a.state.accumulators[actor]),
        r::Rule::Unload=>s::registered(a.state,actor) && a.state.control.fibers[actor].phase==Phase::Unloading && !r::relied(a.state.control,actor)
            && restore(a.history,a.state.accumulators[actor],a.state,actor).is_some() && z==unload(a,actor),
        _=>false,
    }
}
pub open spec fn landing<U,I>(a:Configuration<U,I>,z:Configuration<U,I>,rule:r::Rule)->bool {
    rule==r::Rule::Iter || rule==r::Rule::Finish || (rule==r::Rule::Divert && z.history!=a.history)
}

/// This model is a per-step interpretation of the actual index and history.
/// It is not an encoding of arbitrary I as nat or a single whole-trace model.
pub open spec fn local_model<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>)->s::Model<U> {
    s::Model {
        iterate:|actor:usize,_id:nat,input:s::State<U>| {
            let out=run(lib,programs(actor)(a.current[actor].unwrap()),input,actor).unwrap();
            s::Yield {state:out.state,inverse:a.history.len(),next:dep::marker(out.next)}
        },
        undo:|token:nat,input:s::State<U>|undo(a.history[token as int].landed.receipt,input).unwrap(),
    }
}
pub proof fn restore_refines<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,source:Configuration<U,I>,tokens:Seq<nat>,a:s::State<U>,actor:usize)
    requires inv::well_formed(a),dep::typed(lib,a),dep::finite_context(a),history_sound(lib,programs,source.history),
        restore(source.history,tokens,a,actor).is_some(),
    ensures restore(source.history,tokens,a,actor).unwrap()==s::restore(local_model(lib,programs,source),tokens,a),
        inv::admissible_restore(local_model(lib,programs,source),tokens,a,actor),
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let receipt=source.history[tokens.last() as int].landed.receipt;
        inverse_preservation(lib,receipt,a);
        restore_refines(lib,programs,source,tokens.drop_last(),undo(receipt,a).unwrap(),actor);
    }
}
pub proof fn run_members<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:s::State<U>,actor:usize,id:I)
    requires d::primitive_theory(eq,lib),component_member(lib,programs,a,actor,id),run(lib,programs(actor)(id),a,actor).is_some(),
    ensures {
        let out=run(lib,programs(actor)(id),a,actor).unwrap();
        &&& syntax::permitted(lib,dep::declarations(a,actor),a.control.fibers[actor].provisions,programs(actor)(id))
        &&& (out.next.is_some() ==> component_member(lib,programs,a,actor,out.next.unwrap()))
        &&& (out.spawn.is_some() ==> component_member(lib,programs,out.state,out.spawn.unwrap().0,out.spawn.unwrap().1))
    },
{
    syntax::member_unfolding(lib,programs,actor,dep::declarations(a,actor),a.control.fibers[actor].provisions,id);
    match programs(actor)(id) {
        Node::Dependent {..}=>{syntax::member_continuation(eq,lib,programs,id,a,actor);},
        Node::Child {child,dependencies,provisions,root,next}=>{
            assert(syntax::members(lib,programs).contains((child,dependencies.union(provisions),provisions,root)));
            if next.is_some() {assert(syntax::members(lib,programs).contains((actor,dep::declarations(a,actor),a.control.fibers[actor].provisions,next.unwrap())));}
        },
    }
}
/// Every mixed transition has an admissible nine-rule full-state step. Local
/// admissibility is derived from actual syntax and receipts, not postulated.
pub proof fn step_refines<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,z:Configuration<U,I>,actor:usize,rule:r::Rule)
    requires d::primitive_theory(eq,lib),well_formed(lib,programs,a),step(lib,programs,a,z,actor,rule),
    ensures s::step(local_model(lib,programs,a),a.state,z.state,actor,rule),
        inv::admissible_step(local_model(lib,programs,a),a.state,z.state,actor,rule),inv::well_formed(z.state),
{
    if landing(a,z,rule) {
        let id=a.current[actor].unwrap();run_members(eq,lib,programs,a.state,actor,id);
        run_admissible(eq,lib,programs(actor)(id),a.state,actor);
    }
    match rule {
        r::Rule::Insert=>{inv::insert_preservation(a.state,z.state,actor);},
        r::Rule::Unload=>{restore_refines(lib,programs,a,a.state.accumulators[actor],a.state,actor);},
        _=>{},
    }
    let model=local_model(lib,programs,a);
    assert(s::step(model,a.state,z.state,actor,rule));
    assert(inv::admissible_step(model,a.state,z.state,actor,rule));
    inv::full_preservation(model,a.state,z.state,actor,rule);
}

pub proof fn frame<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,z:Configuration<U,I>,actor:usize,rule:r::Rule)
    requires d::primitive_theory(eq,lib),well_formed(lib,programs,a),step(lib,programs,a,z,actor,rule),
    ensures {
        &&& forall|n:usize| s::registered(a.state,n) && s::registered(z.state,n) ==> r::interface_same(a.state.control.fibers[n],z.state.control.fibers[n])
            && a.state.effects[n]==z.state.effects[n] && a.roots[n]==z.roots[n]
        &&& forall|n:usize| n!=actor && s::registered(a.state,n) ==> s::registered(z.state,n)
            && a.current[n]==z.current[n] && a.state.accumulators[n]==z.state.accumulators[n]
        &&& forall|n:usize| s::registered(z.state,n) && !s::registered(a.state,n) ==> {
            &&& z.current[n].is_none() && z.state.accumulators[n].len()==0
            &&& (n==actor && rule==r::Rule::Insert || landing(a,z,rule) && entry(lib,programs,a,actor).landed.spawn.is_some()
                && n==entry(lib,programs,a,actor).landed.spawn.unwrap().0)
        }
        &&& (landing(a,z,rule) ==> {
            let e=entry(lib,programs,a,actor);
            &&& s::registered(a.state,actor) && a.current[actor].is_some()
            &&& run(lib,programs(actor)(a.current[actor].unwrap()),a.state,actor).is_some()
            &&& owner(e.landed.receipt)==actor && z.history==a.history.push(e)
            &&& z.state.accumulators[actor]==a.state.accumulators[actor].push(a.history.len())
            &&& z.current[actor]==if rule==r::Rule::Iter {e.landed.next} else {None}
            &&& (e.landed.spawn.is_some() ==> {
                let child=e.landed.spawn.unwrap().0;
                &&& !s::registered(a.state,child) && s::registered(z.state,child) && child!=actor
                &&& z.roots[child]==e.landed.spawn.unwrap().1
                &&& r::interface_same(e.landed.state.control.fibers[child],z.state.control.fibers[child])
            })
        })
        &&& (!landing(a,z,rule) ==> z.history==a.history)
    },
{
    if landing(a,z,rule) {
        let id=a.current[actor].unwrap();run_members(eq,lib,programs,a.state,actor,id);
        run_admissible(eq,lib,programs(actor)(id),a.state,actor);
        inv::forward_preservation(a.state,entry(lib,programs,a,actor).landed.state,actor);
    }
    if rule==r::Rule::Unload {restore_preservation(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);}
    assert forall|n:usize| s::registered(a.state,n) && s::registered(z.state,n) implies r::interface_same(a.state.control.fibers[n],z.state.control.fibers[n])
        && a.state.effects[n]==z.state.effects[n] && a.roots[n]==z.roots[n] by {
        match rule {r::Rule::Insert | r::Rule::Remove=>{assert(n!=actor);},_=>{},}
    }
    assert forall|n:usize| n!=actor && s::registered(a.state,n) implies s::registered(z.state,n)
        && a.current[n]==z.current[n] && a.state.accumulators[n]==z.state.accumulators[n] by { }
    assert forall|n:usize| s::registered(z.state,n) && !s::registered(a.state,n) implies {
        &&& z.current[n].is_none() && z.state.accumulators[n].len()==0
        &&& (n==actor && rule==r::Rule::Insert || landing(a,z,rule) && entry(lib,programs,a,actor).landed.spawn.is_some()
            && n==entry(lib,programs,a,actor).landed.spawn.unwrap().0)
    } by { }
}

pub proof fn state_preservation<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,z:Configuration<U,I>,actor:usize,rule:r::Rule)
    requires d::primitive_theory(eq,lib),well_formed(lib,programs,a),step(lib,programs,a,z,actor,rule),
    ensures inv::well_formed(z.state),dep::typed(lib,z.state),metadata(z),dep::finite_context(z.state),
{
    step_refines(eq,lib,programs,a,z,actor,rule);frame(eq,lib,programs,a,z,actor,rule);
    if landing(a,z,rule) {
        let id=a.current[actor].unwrap();run_members(eq,lib,programs,a.state,actor,id);
        run_admissible(eq,lib,programs(actor)(id),a.state,actor);
    }
    if rule==r::Rule::Unload {restore_preservation(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);}
    assert forall|n:usize,k:Port| s::registered(z.state,n) && z.state.tables[n].dom().contains(k)
        implies #[trigger] (lib.values)(k,z.state.tables[n][k]) by {
        match rule {
            r::Rule::Insert | r::Rule::Remove=>{assert(n!=actor);assert(a.state.tables[n]==z.state.tables[n]);},
            r::Rule::Iter | r::Rule::Finish=>{assert(dep::typed(lib,entry(lib,programs,a,actor).landed.state));},
            r::Rule::Divert=>{if landing(a,z,rule) {assert(dep::typed(lib,entry(lib,programs,a,actor).landed.state));}},
            r::Rule::Unload=>{assert(dep::typed(lib,restore(a.history,a.state.accumulators[actor],a.state,actor).unwrap()));},
            _=>{},
        }
    }
    p::unique_owner(a.state);
    match rule {
        r::Rule::Insert=>{p::empty_insertion(a.state,z.state,actor,ISet::full());},
        r::Rule::Remove=>{p::empty_erasure(a.state,actor,ISet::full());},
        r::Rule::Retire=>{
            p::unique_owner(z.state);
            assert(p::bindings_equal(a.state,z.state)) by {assert forall|key:Port,n:usize| p::owns(a.state,key,n)==p::owns(z.state,key,n)
                && (p::owns(a.state,key,n) ==> a.state.tables[n][key]==z.state.tables[n][key]) by { }}
            p::projection_equal(a.state,z.state,ISet::full());
        },
        r::Rule::Iter | r::Rule::Finish | r::Rule::Divert=>{
            if landing(a,z,rule) {
                let out=entry(lib,programs,a,actor).landed;p::unique_owner(out.state);
                p::lifecycle_edit(out.state,actor,z.state.control.fibers[actor].phase,a.state.control.fibers[actor].committed,z.state.iterators[actor],z.state.accumulators[actor],ISet::full());
                let table=dep::context(out.state);assert(c::embed(table)==p::project(z.state,ISet::full()));
            } else {p::lifecycle_edit(a.state,actor,Phase::Unloading,a.state.control.fibers[actor].committed,None,a.state.accumulators[actor],ISet::full());}
        },
        r::Rule::Unload=>{
            let restored=restore(a.history,a.state.accumulators[actor],a.state,actor).unwrap();p::unique_owner(restored);
            p::lifecycle_edit(restored,actor,Phase::Inactive,ISet::empty(),None,Seq::empty(),ISet::full());
            let table=dep::context(restored);assert(c::embed(table)==p::project(z.state,ISet::full()));
        },
        r::Rule::Begin | r::Rule::Leave=>{p::lifecycle_edit(a.state,actor,z.state.control.fibers[actor].phase,z.state.control.fibers[actor].committed,z.state.iterators[actor],z.state.accumulators[actor],ISet::full());},
        _=>{},
    }
    if p::project(a.state,ISet::full())==p::project(z.state,ISet::full()) {
        let table=dep::context(a.state);assert(c::embed(table)==p::project(z.state,ISet::full()));
    }
    assert forall|n:usize| s::registered(z.state,n) implies z.state.effects[n]==0 && z.state.iterators[n]==#[trigger] dep::marker(z.current[n]) by {
        if s::registered(a.state,n) {assert(a.state.effects[n]==0);}
        else if landing(a,z,rule) {assert(entry(lib,programs,a,actor).landed.spawn==Some((n,z.roots[n])));}
    }
    assert(z.roots.dom() =~= z.state.control.fibers.dom());
    assert(z.current.dom() =~= z.roots.dom());
}

// Keep the independent preservation obligations in separate solver contexts.
// In particular, removal retention must be checked without expanding component
// membership and the full history quantifiers in the same query.
#[verifier::spinoff_prover]
proof fn step_history_sound<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,z:Configuration<U,I>,actor:usize,rule:r::Rule)
    requires d::primitive_theory(eq,lib),well_formed(lib,programs,a),step(lib,programs,a,z,actor,rule),
    ensures history_sound(lib,programs,z.history),
{
    frame(eq,lib,programs,a,z,actor,rule);state_preservation(eq,lib,programs,a,z,actor,rule);
    if landing(a,z,rule) {
        let id=a.current[actor].unwrap();let e=entry(lib,programs,a,actor);
        run_members(eq,lib,programs,a.state,actor,id);run_admissible(eq,lib,programs(actor)(id),a.state,actor);
        assert(history_sound(lib,programs,z.history)) by {
            assert forall|i:int| #![trigger z.history[i]] 0<=i<z.history.len() implies {
                let h=z.history[i];let n=owner(h.landed.receipt);
                &&& run(lib,programs(n)(h.iterator),h.input,n)==Some(h.landed)
                &&& receipt_typed(lib,h.landed.receipt) && undo(h.landed.receipt,h.landed.state).is_some()
            } by {if i<a.history.len() {assert(z.history[i]==a.history[i]);} else {assert(i==a.history.len());assert(z.history[i]==e);}}
        }
    }
}

proof fn step_tokens_valid<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,z:Configuration<U,I>,actor:usize,rule:r::Rule)
    requires d::primitive_theory(eq,lib),well_formed(lib,programs,a),step(lib,programs,a,z,actor,rule),
    ensures tokens_valid(z),
{
    frame(eq,lib,programs,a,z,actor,rule);state_preservation(eq,lib,programs,a,z,actor,rule);
    assert(tokens_valid(z)) by {
        assert forall|n:usize,i:int| #![trigger z.state.accumulators[n][i]] s::registered(z.state,n) && 0<=i<z.state.accumulators[n].len() implies {
            let token=z.state.accumulators[n][i];
            &&& token<z.history.len() && owner(z.history[token as int].landed.receipt)==n
        } by {
            assert(s::registered(a.state,n));
            if n==actor && landing(a,z,rule) && i==a.state.accumulators[n].len() {
                assert(z.state.accumulators[n][i]==a.history.len());assert(z.history[a.history.len() as int]==entry(lib,programs,a,actor));
            } else {
                assert(i<a.state.accumulators[n].len());assert(z.state.accumulators[n][i]==a.state.accumulators[n][i]);
                let token=a.state.accumulators[n][i];assert(token<a.history.len());assert(z.history[token as int]==a.history[token as int]);
            }
        }
    }
}

proof fn step_members<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,z:Configuration<U,I>,actor:usize,rule:r::Rule)
    requires d::primitive_theory(eq,lib),well_formed(lib,programs,a),step(lib,programs,a,z,actor,rule),
    ensures members(lib,programs,z),
{
    frame(eq,lib,programs,a,z,actor,rule);state_preservation(eq,lib,programs,a,z,actor,rule);
    if landing(a,z,rule) {
        let id=a.current[actor].unwrap();
        run_members(eq,lib,programs,a.state,actor,id);
        run_admissible(eq,lib,programs(actor)(id),a.state,actor);
    }
    assert(members(lib,programs,z)) by {
        assert forall|n:usize| s::registered(z.state,n) implies component_member(lib,programs,z.state,n,z.roots[n])
            && (z.current[n].is_some() ==> component_member(lib,programs,z.state,n,z.current[n].unwrap())) by {
            if !s::registered(a.state,n) {
                if rule!=r::Rule::Insert {
                    let e=entry(lib,programs,a,actor);assert(e.landed.spawn==Some((n,z.roots[n])));
                    assert(component_member(lib,programs,e.landed.state,n,z.roots[n]));
                }
            } else {
                assert(a.roots[n]==z.roots[n]);assert(component_member(lib,programs,a.state,n,a.roots[n]));
                if z.current[n].is_some() {
                    if n!=actor {assert(a.current[n]==z.current[n]);}
                    else if rule==r::Rule::Begin {assert(z.current[n]==Some(a.roots[n]));}
                    else if rule==r::Rule::Iter {
                        let e=entry(lib,programs,a,actor);assert(z.current[n]==e.landed.next);
                        assert(component_member(lib,programs,a.state,n,e.landed.next.unwrap()));
                    } else {assert(a.current[n]==z.current[n]);}
                }
            }
        }
    }
}

proof fn step_retains_children<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,z:Configuration<U,I>,actor:usize,rule:r::Rule)
    requires d::primitive_theory(eq,lib),well_formed(lib,programs,a),step(lib,programs,a,z,actor,rule),tokens_valid(z),
    ensures ch::retained(kind(z.history),z.state),
{
    frame(eq,lib,programs,a,z,actor,rule);state_preservation(eq,lib,programs,a,z,actor,rule);
    assert(ch::retained(kind(z.history),z.state)) by {
        assert forall|n:usize,token:nat,child:usize| s::registered(z.state,n) && z.state.accumulators[n].contains(token)
            && kind(z.history)(token)==Some(child) implies s::registered(z.state,child) by {
            let i=choose|i:int| 0<=i<z.state.accumulators[n].len() && z.state.accumulators[n][i]==token;
            assert(s::registered(a.state,n));
            if landing(a,z,rule) && token==a.history.len() {
                let e=entry(lib,programs,a,actor);assert(z.history[token as int]==e);
                assert(e.landed.spawn.is_some());assert(e.landed.spawn.unwrap().0==child);
            } else {
                assert(token<a.history.len());assert(z.history[token as int]==a.history[token as int]);
                assert(a.state.accumulators[n].contains(token));assert(kind(a.history)(token)==Some(child));
                assert(s::registered(a.state,child));
                if rule==r::Rule::Remove {
                    ch::removal_excludes_retained_token(kind(a.history),a.state,actor,n,token);
                    assert(child!=actor);
                }
                assert(s::registered(z.state,child));
            }
        }
    }
}

pub proof fn configuration_preservation<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,z:Configuration<U,I>,actor:usize,rule:r::Rule)
    requires d::primitive_theory(eq,lib),well_formed(lib,programs,a),step(lib,programs,a,z,actor,rule),
    ensures well_formed(lib,programs,z),
{
    frame(eq,lib,programs,a,z,actor,rule);state_preservation(eq,lib,programs,a,z,actor,rule);
    step_history_sound(eq,lib,programs,a,z,actor,rule);
    step_tokens_valid(eq,lib,programs,a,z,actor,rule);
    step_members(eq,lib,programs,a,z,actor,rule);
    step_retains_children(eq,lib,programs,a,z,actor,rule);
}

pub open spec fn execution<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,states:Seq<Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)->bool {
    states.len()==labels.len()+1 && forall|i:int| 0<=i<labels.len() ==> step(lib,programs,states[i],states[i+1],labels[i].0,labels[i].1)
}
pub proof fn execution_preservation<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,states:Seq<Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires d::primitive_theory(eq,lib),execution(lib,programs,states,labels),well_formed(lib,programs,states.first()),
    ensures forall|i:int| 0<=i<states.len() ==> well_formed(lib,programs,states[i]),
    decreases labels.len(),
{
    if labels.len()>0 {
        let previous=states.drop_last();let prefix=labels.drop_last();
        assert(execution(lib,programs,previous,prefix)) by {
            assert forall|i:int| 0<=i<prefix.len() implies step(lib,programs,previous[i],previous[i+1],prefix[i].0,prefix[i].1) by { }
        }
        execution_preservation(eq,lib,programs,previous,prefix);
        configuration_preservation(eq,lib,programs,previous.last(),states.last(),labels.last().0,labels.last().1);
        assert forall|i:int| 0<=i<states.len() implies well_formed(lib,programs,states[i]) by {
            if i<previous.len() {assert(states[i]==previous[i]);} else {assert(i==states.len()-1);}
        }
    }
}
pub open spec fn empty<U,I>()->Configuration<U,I> {
    Configuration {state:inv::empty(),roots:IMap::empty(),current:IMap::empty(),history:Seq::empty()}
}
pub proof fn empty_well_formed<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>)
    ensures well_formed(lib,programs,empty::<U,I>()),
{inv::empty_well_formed::<U>();assert(c::embed(Map::<Port,U>::empty()) =~= p::project(empty::<U,I>().state,ISet::full()));}
/// The trace supplies only actual rule transitions. All intermediate full-state
/// safety, typing, least membership, receipt authenticity and retention follow.
pub proof fn from_empty_safe<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,states:Seq<Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires d::primitive_theory(eq,lib),execution(lib,programs,states,labels),states.first()==empty::<U,I>(),
    ensures forall|i:int| 0<=i<states.len() ==> well_formed(lib,programs,states[i]) && inv::resource_safe(states[i].state),
{
    empty_well_formed(lib,programs);execution_preservation(eq,lib,programs,states,labels);
    assert forall|i:int| 0<=i<states.len() implies well_formed(lib,programs,states[i]) && inv::resource_safe(states[i].state) by {
        assert(well_formed(lib,programs,states[i]));
        assert forall|key:Port,left:usize,right:usize| s::publishes(states[i].state,key,left) && s::publishes(states[i].state,key,right) implies left==right by {
            assert(states[i].state.control.fibers[left].provisions.contains(key));assert(states[i].state.control.fibers[right].provisions.contains(key));
        }
    }
}

/// Every actual child inverse reached by the partial LIFO interpreter is in
/// domain. If a table inverse fails, the interpreter stops there; it does not
/// pretend to visit (or to recover) the remaining stack.
pub open spec fn child_domains<U,I>(history:Seq<Entry<U,I>>,tokens:Seq<nat>,a:s::State<U>,actor:usize)->bool
    decreases tokens.len(),
{
    if tokens.len()==0 {true}
    else {
        let token=tokens.last();let receipt=history[token as int].landed.receipt;
        &&& token<history.len() && owner(receipt)==actor
        &&& (captured_child(receipt).is_some() ==> undo(receipt,a).is_some())
        &&& (undo(receipt,a).is_some() ==> child_domains(history,tokens.drop_last(),undo(receipt,a).unwrap(),actor))
    }
}
pub proof fn retained_child_domain<U,I>(history:Seq<Entry<U,I>>,a:s::State<U>,actor:usize,token:nat,child:usize)
    requires ch::retained(kind(history),a),s::registered(a,actor),a.accumulators[actor].contains(token),
        token<history.len(),captured_child(history[token as int].landed.receipt)==Some(child),
    ensures undo(history[token as int].landed.receipt,a).is_some(),
        s::child_retire(a,undo(history[token as int].landed.receipt,a).unwrap(),child),
{
    assert(kind(history)(token)==Some(child));assert(s::registered(a,child));
    ch::concrete_child_retirement(a,child);
}
pub proof fn recovery_child_domains<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,history:Seq<Entry<U,I>>,tokens:Seq<nat>,a:s::State<U>,actor:usize)
    requires inv::well_formed(a),dep::typed(lib,a),dep::finite_context(a),history_sound(lib,programs,history),
        ch::retained(kind(history),a),s::registered(a,actor),
        forall|token:nat| tokens.contains(token) ==> a.accumulators[actor].contains(token)
            && token<history.len() && owner(history[token as int].landed.receipt)==actor,
    ensures child_domains(history,tokens,a,actor),
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let token=tokens.last();assert(tokens.contains(token));let receipt=history[token as int].landed.receipt;
        if captured_child(receipt).is_some() {retained_child_domain(history,a,actor,token,captured_child(receipt).unwrap());}
        if undo(receipt,a).is_some() {
            inverse_preservation(lib,receipt,a);let next=undo(receipt,a).unwrap();
            assert(ch::retained(kind(history),next)) by {
                assert forall|n:usize,t:nat,child:usize| s::registered(next,n) && next.accumulators[n].contains(t)
                    && kind(history)(t)==Some(child) implies s::registered(next,child) by {
                    assert(s::registered(a,n));assert(a.accumulators[n].contains(t));assert(s::registered(a,child));
                }
            }
            assert forall|t:nat| tokens.drop_last().contains(t) implies next.accumulators[actor].contains(t)
                && t<history.len() && owner(history[t as int].landed.receipt)==actor by {
                let j=choose|j:int| 0<=j<tokens.drop_last().len() && tokens.drop_last()[j]==t;
                assert(tokens[j]==t);assert(tokens.contains(t));
            }
            recovery_child_domains(lib,programs,history,tokens.drop_last(),next,actor);
        }
    }
}
/// This conclusion holds before attempting recovery, without assuming success
/// of the final restore. Only the actual table inverse domain may still fail.
pub proof fn journal_child_domains<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,actor:usize)
    requires well_formed(lib,programs,a),s::registered(a.state,actor),
    ensures child_domains(a.history,a.state.accumulators[actor],a.state,actor),
{
    assert forall|token:nat| a.state.accumulators[actor].contains(token) implies a.state.accumulators[actor].contains(token)
        && token<a.history.len() && owner(a.history[token as int].landed.receipt)==actor by {
        let i=choose|i:int| 0<=i<a.state.accumulators[actor].len() && a.state.accumulators[actor][i]==token;
    }
    recovery_child_domains(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);
}
pub open spec fn states<U,I>(trace:Seq<Configuration<U,I>>)->Seq<s::State<U>> {
    Seq::new(trace.len(),|i:int|trace[i].state)
}
/// Arbitrary-index mixed executions supply real per-step semantic witnesses to
/// the general ordering layer. No global nat encoding of I is needed.
pub proof fn execution_ordering<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,trace:Seq<Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires d::primitive_theory(eq,lib),execution(lib,programs,trace,labels),well_formed(lib,programs,trace.first()),
    ensures crate::indexed_ordering::trace(states(trace),labels),
{
    execution_preservation(eq,lib,programs,trace,labels);
    assert forall|i:int| 0<=i<labels.len() implies crate::indexed_ordering::step(states(trace)[i],states(trace)[i+1],labels[i].0,labels[i].1) by {
        step_refines(eq,lib,programs,trace[i],trace[i+1],labels[i].0,labels[i].1);
        assert(s::step(local_model(lib,programs,trace[i]),states(trace)[i],states(trace)[i+1],labels[i].0,labels[i].1)
            && inv::admissible_step(local_model(lib,programs,trace[i]),states(trace)[i],states(trace)[i+1],labels[i].0,labels[i].1));
    }
}

/// A completed mixed LIFO restore retires every captured child, including a
/// child that is still Active. Other inverses cannot undo that retirement bit.
pub proof fn restore_retires<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,history:Seq<Entry<U,I>>,tokens:Seq<nat>,a:s::State<U>,actor:usize)
    requires inv::well_formed(a),dep::typed(lib,a),dep::finite_context(a),history_sound(lib,programs,history),
        restore(history,tokens,a,actor).is_some(),
    ensures forall|token:nat,child:usize| tokens.contains(token) && kind(history)(token)==Some(child)
        ==> s::registered(restore(history,tokens,a,actor).unwrap(),child)
            && restore(history,tokens,a,actor).unwrap().control.fibers[child].retired,
    decreases tokens.len(),
{
    assert forall|token:nat,child:usize| tokens.contains(token) && kind(history)(token)==Some(child)
        implies s::registered(restore(history,tokens,a,actor).unwrap(),child)
            && restore(history,tokens,a,actor).unwrap().control.fibers[child].retired by {
        let i=choose|i:int| 0<=i<tokens.len() && tokens[i]==token;
        assert(tokens.len()>0);
        let last=tokens.last();let receipt=history[last as int].landed.receipt;
        inverse_preservation(lib,receipt,a);let next=undo(receipt,a).unwrap();
        restore_preservation(lib,programs,history,tokens.drop_last(),next,actor);
        restore_retires(lib,programs,history,tokens.drop_last(),next,actor);
        let z=restore(history,tokens,a,actor).unwrap();
        assert(z==restore(history,tokens.drop_last(),next,actor).unwrap());
        assert(ch::recovery_frame(next,z));
        if token==last {
            assert(captured_child(receipt)==Some(child));assert(s::registered(next,child));assert(next.control.fibers[child].retired);
            assert(s::registered(z,child));assert(z.control.fibers[child].retired);
        } else {
            assert(i<tokens.len()-1);assert(tokens.drop_last()[i]==token);assert(tokens.drop_last().contains(token));
            assert(s::registered(z,child));assert(z.control.fibers[child].retired);
        }
    }
}
pub proof fn unload_retires<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,z:Configuration<U,I>,actor:usize)
    requires well_formed(lib,programs,a),step(lib,programs,a,z,actor,r::Rule::Unload),
    ensures forall|token:nat,child:usize| a.state.accumulators[actor].contains(token) && kind(a.history)(token)==Some(child)
        ==> s::registered(z.state,child) && z.state.control.fibers[child].retired,
{
    restore_retires(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);
    let recovered=restore(a.history,a.state.accumulators[actor],a.state,actor).unwrap();
    assert forall|token:nat,child:usize| a.state.accumulators[actor].contains(token) && kind(a.history)(token)==Some(child)
        implies s::registered(z.state,child) && z.state.control.fibers[child].retired by {
        assert(s::registered(recovered,child));assert(recovered.control.fibers[child].retired);
    }
}

} // verus!
