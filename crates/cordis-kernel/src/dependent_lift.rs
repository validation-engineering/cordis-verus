//! Dependent context grammar on the complete registry, with arbitrary indices.
//!
//! The generic iterator index lives in `Configuration::current`; the older
//! full-state nat iterator field is only its presence marker. Actual callbacks,
//! outcomes and partial inverse receipts are interpreted without numeric casts.
#[cfg(verus_keep_ghost)]
use crate::{
    contexts as c, mediated as m, preservation as inv, projection as p, refinement as r, Phase,
};
use crate::{dependent_grammar as d, grammar_lift as lift, semantics as s, Port};
use vstd::prelude::*;

verus! {

pub type Library<A,X,U,B> = d::Library<Port,A,X,U,B>;
pub type Node<A,X,U,B,I> = d::Node<Port,A,X,U,B,I>;
pub type Programs<A,X,U,B,I> = spec_fn(usize)->d::Program<Port,A,X,U,B,I>;

/// This projection forgets the continuation's identity, but preserves whether
/// it terminates. The original `I` is retained separately by `run` below.
pub open spec fn marker<I>(next:Option<I>)->Option<nat> {if next.is_some() {Some(0)} else {None}}
pub open spec fn stage<A,X,U,B,I>(lib:Library<A,X,U,B>,node:Node<A,X,U,B,I>)->m::Node<Port,U,B> {
    match node {
        d::Node::Unit=>m::Node::Unit,
        d::Node::Operation {operation:a,argument:x,select}=>m::Node::Operation {
            key:(lib.key)(a),operation:(lib.apply)(a,x),select:|b:B|marker(select(b)),
        },
        d::Node::Provision {key,value,next}=>m::Node::Provision {key,value,next:marker(next)},
    }
}
pub open spec fn actual_next<A,X,U,B,I>(lib:Library<A,X,U,B>,node:Node<A,X,U,B,I>,a:s::State<U>,actor:usize)->Option<I> {
    match node {
        d::Node::Unit=>None,
        d::Node::Operation {operation:op,argument:x,select}=>{
            let key=(lib.key)(op);let provider=lift::resolve(a,actor,key).unwrap();
            select((lib.apply)(op,x)(a.tables[provider][key]).unwrap().outcome)
        },
        d::Node::Provision {next,..}=>next,
    }
}
#[verifier::reject_recursive_types(U)]
pub struct Landed<U,I> {pub state:s::State<U>,pub receipt:lift::Receipt<U>,pub next:Option<I>}
pub open spec fn run<A,X,U,B,I>(lib:Library<A,X,U,B>,node:Node<A,X,U,B,I>,a:s::State<U>,actor:usize)->Option<Landed<U,I>> {
    match lift::run(stage(lib,node),a,actor) {
        None=>None,
        Some(y)=>Some(Landed {state:y.state,receipt:y.receipt,next:actual_next(lib,node,a,actor)}),
    }
}
pub open spec fn typed<U,A,X,B>(lib:Library<A,X,U,B>,a:s::State<U>)->bool {
    forall|n:usize,k:Port| s::registered(a,n) && a.tables[n].dom().contains(k) ==> #[trigger] (lib.values)(k,a.tables[n][k])
}
/// The actual all-table observation has finite support, independently of the
/// ambient IMap representation used by the original full-state model.
pub open spec fn finite_context<U>(a:s::State<U>)->bool {
    exists|table:Map<Port,U>| c::embed(table)==p::project(a,ISet::full())
}
pub open spec fn context<U>(a:s::State<U>)->Map<Port,U> {
    choose|table:Map<Port,U>| c::embed(table)==p::project(a,ISet::full())
}
pub proof fn update_finite<U>(a:s::State<U>,n:usize,key:Port,value:Option<U>)
    requires inv::well_formed(a),s::registered(a,n),a.control.fibers[n].provisions.contains(key),finite_context(a),
    ensures finite_context(p::update_slot(a,n,key,value)),
{
    p::update_slot_projection(a,n,key,value);
    let table=context(a);assert(c::embed(table)==p::project(a,ISet::full()));
    match value {
        Some(v)=>{c::finite_embedding(table,table,key,v);assert(c::embed(table.insert(key,v))==p::project(p::update_slot(a,n,key,value),ISet::full()));},
        None=>{
            assert(c::embed(table.remove(key)) =~= c::embed(table).remove(key));
            assert(c::embed(table.remove(key))==p::project(p::update_slot(a,n,key,value),ISet::full()));
        },
    }
}
pub proof fn stage_projection<A,X,U,B,I>(lib:Library<A,X,U,B>,node:Node<A,X,U,B,I>,a:s::State<U>,actor:usize)
    ensures run(lib,node,a,actor).is_some()==lift::run(stage(lib,node),a,actor).is_some(),
        run(lib,node,a,actor).is_some() ==> {
            let x=run(lib,node,a,actor).unwrap();let y=lift::run(stage(lib,node),a,actor).unwrap();
            &&& x.state==y.state && x.receipt==y.receipt && marker(x.next)==y.next
        },
{ }
pub proof fn update_typed<A,X,U,B>(lib:Library<A,X,U,B>,a:s::State<U>,n:usize,key:Port,value:Option<U>)
    requires typed(lib,a),value.is_some() ==> (lib.values)(key,value.unwrap()),
    ensures typed(lib,p::update_slot(a,n,key,value)),
{
    assert forall|m:usize,k:Port| s::registered(p::update_slot(a,n,key,value),m) && p::update_slot(a,n,key,value).tables[m].dom().contains(k)
        implies #[trigger] (lib.values)(k,p::update_slot(a,n,key,value).tables[m][k]) by {
        if m!=n || k!=key {assert(a.tables[m].dom().contains(k));}
    }
}
/// An inverse receipt keeps a partial, type-preserving map on its actual key.
pub open spec fn receipt_typed<A,X,U,B>(lib:Library<A,X,U,B>,receipt:lift::Receipt<U>)->bool {
    match receipt.inverse {
        lift::Inverse::Operation {key,undo,..}=>forall|u:U| #[trigger] undo(u).is_some() ==> (lib.values)(key,u) && (lib.values)(key,undo(u).unwrap()),
        _=>true,
    }
}
pub proof fn typed_inverse<A,X,U,B>(lib:Library<A,X,U,B>,receipt:lift::Receipt<U>,a:s::State<U>)
    requires inv::well_formed(a),typed(lib,a),finite_context(a),receipt_typed(lib,receipt),lift::undo(receipt,a).is_some(),
    ensures inv::well_formed(lift::undo(receipt,a).unwrap()),typed(lib,lift::undo(receipt,a).unwrap()),finite_context(lift::undo(receipt,a).unwrap()),
{
    lift::undo_preservation(receipt,a);
    match receipt.inverse {
        lift::Inverse::Operation {provider,key,undo}=>{
            assert(undo(a.tables[provider][key]).is_some());
            update_typed(lib,a,provider,key,Some(undo(a.tables[provider][key]).unwrap()));
            lift::resolution_sound(a,receipt.actor,key);update_finite(a,provider,key,Some(undo(a.tables[provider][key]).unwrap()));
        },
        lift::Inverse::Provision {key}=>{update_typed(lib,a,receipt.actor,key,None);update_finite(a,receipt.actor,key,None);},
        _=>{},
    }
}
pub open spec fn declarations<U>(a:s::State<U>,actor:usize)->ISet<Port> {
    a.control.fibers[actor].dependencies.union(a.control.fibers[actor].provisions)
}
/// The dependent primitive theory proves exact recovery and receipt typing at
/// the actual full-state application. Continuation selection uses the original
/// raw outcome, including operations with distinct outcome fibers.
pub proof fn run_admissible<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,node:Node<A,X,U,B,I>,a:s::State<U>,actor:usize)
    requires d::primitive_theory(eq,lib),inv::well_formed(a),typed(lib,a),finite_context(a),
        d::permitted(lib,declarations(a,actor),a.control.fibers[actor].provisions,node),run(lib,node,a,actor).is_some(),
    ensures {
        let out=run(lib,node,a,actor).unwrap();
        &&& out.receipt.actor==actor && s::registered(a,actor)
        &&& inv::well_formed(out.state) && inv::table_map(a,out.state,actor) && typed(lib,out.state) && finite_context(out.state)
        &&& out.state.control==a.control && out.state.effects==a.effects
        &&& out.state.iterators==a.iterators && out.state.accumulators==a.accumulators
        &&& receipt_typed(lib,out.receipt) && lift::undo(out.receipt,out.state)==Some(a)
    },
{
    stage_projection(lib,node,a,actor);lift::run_preservation(stage(lib,node),a,actor);
    match node {
        d::Node::Unit=>{},
        d::Node::Operation {operation:op,argument:x,select}=>{
            let k=(lib.key)(op);let provider=lift::resolve(a,actor,k).unwrap();let operation=(lib.apply)(op,x);
            let y=operation(a.tables[provider][k]).unwrap();
            assert(d::operation_typed(lib,op,x));assert(m::operation_admissible(|u:U,v:U|eq(k,u,v),operation));
            assert((y.undo)(y.value)==Some(a.tables[provider][k]));
            lift::resolution_sound(a,actor,k);update_typed(lib,a,provider,k,Some(y.value));update_finite(a,provider,k,Some(y.value));
            p::operation_stage_lift(a,actor,provider,k,operation,|b:B|marker(select(b)));
        },
        d::Node::Provision {key,value,next}=>{
            update_typed(lib,a,actor,key,Some(value));update_finite(a,actor,key,Some(value));p::provision_stage_lift::<U,B>(a,actor,key,value,marker(next));
        },
    }
}
pub proof fn member_continuation<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,program:d::Program<Port,A,X,U,B,I>,id:I,a:s::State<U>,actor:usize)
    requires d::primitive_theory(eq,lib),d::member(lib,program,declarations(a,actor),a.control.fibers[actor].provisions,id),run(lib,program(id),a,actor).is_some(),
    ensures run(lib,program(id),a,actor).unwrap().next.is_some() ==> d::member(lib,program,declarations(a,actor),a.control.fibers[actor].provisions,run(lib,program(id),a,actor).unwrap().next.unwrap()),
{
    d::member_unfolding(lib,program,declarations(a,actor),a.control.fibers[actor].provisions,id);
    match program(id) {
        d::Node::Operation {operation:op,argument:x,select}=>{
            let k=(lib.key)(op);let provider=lift::resolve(a,actor,k).unwrap();let y=(lib.apply)(op,x)(a.tables[provider][k]).unwrap();
            assert(d::operation_typed(lib,op,x));assert((lib.outcomes)(op,y.outcome));
            if select(y.outcome).is_some() {assert(d::members(lib,program,declarations(a,actor),a.control.fibers[actor].provisions).contains(select(y.outcome).unwrap()));}
        },
        _=>{},
    }
}

#[verifier::reject_recursive_types(U)]
pub struct Entry<U,I> {pub input:s::State<U>,pub iterator:I,pub landed:Landed<U,I>}
#[verifier::reject_recursive_types(U)]
pub struct Configuration<U,I> {
    pub state:s::State<U>,pub roots:IMap<usize,I>,pub current:IMap<usize,Option<I>>,pub history:Seq<Entry<U,I>>,
}
pub open spec fn metadata<U,I>(a:Configuration<U,I>)->bool {
    &&& a.roots.dom()==a.state.control.fibers.dom() && a.current.dom()==a.roots.dom()
    &&& forall|n:usize| s::registered(a.state,n) ==> a.state.effects[n]==0 && a.state.iterators[n]==#[trigger] marker(a.current[n])
}
pub open spec fn component_member<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:s::State<U>,actor:usize,id:I)->bool {
    d::member(lib,programs(actor),declarations(a,actor),a.control.fibers[actor].provisions,id)
}
pub open spec fn members<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>)->bool {
    forall|n:usize| s::registered(a.state,n) ==> component_member(lib,programs,a.state,n,a.roots[n])
        && (a.current[n].is_some() ==> component_member(lib,programs,a.state,n,a.current[n].unwrap()))
}
pub open spec fn history_sound<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,history:Seq<Entry<U,I>>)->bool {
    forall|i:int| #![trigger history[i]] 0<=i<history.len() ==> {
        let e=history[i];
        &&& run(lib,programs(e.landed.receipt.actor)(e.iterator),e.input,e.landed.receipt.actor)==Some(e.landed)
        &&& lift::undo(e.landed.receipt,e.landed.state)==Some(e.input)
        &&& receipt_typed(lib,e.landed.receipt)
    }
}
pub open spec fn tokens_valid<U,I>(a:Configuration<U,I>)->bool {
    forall|actor:usize,i:int| #![trigger a.state.accumulators[actor][i]] s::registered(a.state,actor) && 0<=i<a.state.accumulators[actor].len() ==> {
        let token=a.state.accumulators[actor][i];
        &&& token<a.history.len() && a.history[token as int].landed.receipt.actor==actor
    }
}
pub open spec fn well_formed<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>)->bool {
    inv::well_formed(a.state) && typed(lib,a.state) && finite_context(a.state) && metadata(a) && members(lib,programs,a)
        && history_sound(lib,programs,a.history) && tokens_valid(a)
}
pub open spec fn restore<U,I>(history:Seq<Entry<U,I>>,tokens:Seq<nat>,a:s::State<U>,actor:usize)->Option<s::State<U>>
    decreases tokens.len(),
{
    if tokens.len()==0 {Some(a)}
    else if tokens.last()>=history.len() || history[tokens.last() as int].landed.receipt.actor!=actor {None}
    else {match lift::undo(history[tokens.last() as int].landed.receipt,a) {
        None=>None,Some(next)=>restore(history,tokens.drop_last(),next,actor),
    }}
}
pub proof fn restore_preservation<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,history:Seq<Entry<U,I>>,tokens:Seq<nat>,a:s::State<U>,actor:usize)
    requires inv::well_formed(a),typed(lib,a),finite_context(a),history_sound(lib,programs,history),restore(history,tokens,a,actor).is_some(),
    ensures inv::well_formed(restore(history,tokens,a,actor).unwrap()),typed(lib,restore(history,tokens,a,actor).unwrap()),finite_context(restore(history,tokens,a,actor).unwrap()),
        restore(history,tokens,a,actor).unwrap().control==a.control,
        restore(history,tokens,a,actor).unwrap().effects==a.effects,
        restore(history,tokens,a,actor).unwrap().iterators==a.iterators,
        restore(history,tokens,a,actor).unwrap().accumulators==a.accumulators,
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let receipt=history[tokens.last() as int].landed.receipt;
        typed_inverse(lib,receipt,a);lift::undo_preservation(receipt,a);
        restore_preservation(lib,programs,history,tokens.drop_last(),lift::undo(receipt,a).unwrap(),actor);
    }
}

pub open spec fn entry<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,actor:usize)->Entry<U,I> {
    let iterator=a.current[actor].unwrap();
    Entry {input:a.state,iterator,landed:run(lib,programs(actor)(iterator),a.state,actor).unwrap()}
}
pub open spec fn land<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,actor:usize,phase:Phase)->Configuration<U,I> {
    let e=entry(lib,programs,a,actor);let next=if phase==Phase::Loading {e.landed.next} else {None};
    Configuration {state:s::edit(e.landed.state,actor,phase,a.state.control.fibers[actor].committed,marker(next),a.state.accumulators[actor].push(a.history.len())),
        roots:a.roots,current:a.current.insert(actor,next),history:a.history.push(e)}
}
pub open spec fn edit<U,I>(a:Configuration<U,I>,actor:usize,phase:Phase,committed:ISet<crate::Binding>,next:Option<I>,tokens:Seq<nat>)->Configuration<U,I> {
    Configuration {state:s::edit(a.state,actor,phase,committed,marker(next),tokens),roots:a.roots,current:a.current.insert(actor,next),history:a.history}
}
pub open spec fn unload<U,I>(a:Configuration<U,I>,actor:usize)->Configuration<U,I> {
    Configuration {state:s::edit(restore(a.history,a.state.accumulators[actor],a.state,actor).unwrap(),actor,Phase::Inactive,ISet::empty(),None,Seq::empty()),
        roots:a.roots,current:a.current.insert(actor,None),history:a.history}
}
/// Nine actual rules with dependent iterator metadata. New components supply
/// a least-grammar root; inverse safety and intermediate typing are derived.
pub open spec fn step<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,z:Configuration<U,I>,actor:usize,rule:r::Rule)->bool {
    match rule {
        r::Rule::Insert=>inv::insert_map(a.state,z.state,actor) && z.state.effects[actor]==0
            && z.roots==a.roots.insert(actor,z.roots[actor]) && z.current==a.current.insert(actor,None) && z.history==a.history
            && component_member(lib,programs,z.state,actor,z.roots[actor]),
        r::Rule::Retire=>s::child_retire(a.state,z.state,actor) && z.roots==a.roots && z.current==a.current && z.history==a.history,
        r::Rule::Remove=>r::step(a.state.control,z.state.control,actor,rule) && a.state.tables[actor].is_empty()
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
pub proof fn frame<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,z:Configuration<U,I>,actor:usize,rule:r::Rule)
    requires well_formed(lib,programs,a),step(lib,programs,a,z,actor,rule),
    ensures {
        &&& forall|n:usize| s::registered(a.state,n) && s::registered(z.state,n) ==> r::interface_same(a.state.control.fibers[n],z.state.control.fibers[n])
            && a.state.effects[n]==z.state.effects[n] && a.roots[n]==z.roots[n]
        &&& forall|n:usize| n!=actor ==> s::registered(a.state,n)==s::registered(z.state,n)
            && (s::registered(a.state,n) ==> a.current[n]==z.current[n] && a.state.accumulators[n]==z.state.accumulators[n])
        &&& (landing(a,z,rule) ==> {
            let e=entry(lib,programs,a,actor);
            &&& s::registered(a.state,actor) && a.current[actor].is_some()
            &&& run(lib,programs(actor)(a.current[actor].unwrap()),a.state,actor).is_some()
            &&& e.landed.receipt.actor==actor && z.history==a.history.push(e)
            &&& z.state.accumulators[actor]==a.state.accumulators[actor].push(a.history.len())
            &&& z.current[actor]==if rule==r::Rule::Iter {e.landed.next} else {None}
        })
        &&& (!landing(a,z,rule) ==> z.history==a.history)
    },
{
    if landing(a,z,rule) {lift::run_preservation(stage(lib,programs(actor)(a.current[actor].unwrap())),a.state,actor);}
    if rule==r::Rule::Unload {restore_preservation(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);}
    assert forall|n:usize| s::registered(a.state,n) && s::registered(z.state,n) implies r::interface_same(a.state.control.fibers[n],z.state.control.fibers[n])
        && a.state.effects[n]==z.state.effects[n] && a.roots[n]==z.roots[n] by {
        match rule {r::Rule::Insert | r::Rule::Remove=>{assert(n!=actor);},_=>{},}
    }
    assert forall|n:usize| n!=actor implies s::registered(a.state,n)==s::registered(z.state,n)
        && (s::registered(a.state,n) ==> a.current[n]==z.current[n] && a.state.accumulators[n]==z.state.accumulators[n]) by { }
}
pub proof fn state_preservation<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,z:Configuration<U,I>,actor:usize,rule:r::Rule)
    requires d::primitive_theory(eq,lib),well_formed(lib,programs,a),step(lib,programs,a,z,actor,rule),
    ensures inv::well_formed(z.state),typed(lib,z.state),metadata(z),finite_context(z.state),
{
    frame(lib,programs,a,z,actor,rule);
    if landing(a,z,rule) {
        let id=a.current[actor].unwrap();
        d::member_unfolding(lib,programs(actor),declarations(a.state,actor),a.state.control.fibers[actor].provisions,id);
        run_admissible(eq,lib,programs(actor)(id),a.state,actor);
    }
    match rule {
        r::Rule::Insert=>{inv::insert_preservation(a.state,z.state,actor);},
        r::Rule::Retire=>{inv::retire_preservation(a.state,z.state,actor);},
        r::Rule::Remove=>{lift::removal_preservation(a.state,actor);},
        r::Rule::Begin=>{assert(a.state.effects[actor]==0);inv::begin_preservation(a.state,z.state,actor);},
        r::Rule::Iter | r::Rule::Finish=>{
            let out=entry(lib,programs,a,actor).landed;
            if rule==r::Rule::Finish {inv::finish_preservation(a.state,out.state,actor,a.state.accumulators[actor].push(a.history.len()));}
            else {
                inv::shaped_edit(out.state,actor,Phase::Loading,a.state.control.fibers[actor].committed,marker(out.next),a.state.accumulators[actor].push(a.history.len()));
                assert(z.state.control.fibers =~= a.state.control.fibers) by {
                    assert forall|n:usize| z.state.control.fibers.dom().contains(n) implies z.state.control.fibers[n]==a.state.control.fibers[n] by { }
                }
            }
        },
        r::Rule::Divert=>{
            if landing(a,z,rule) {inv::unloading_edit_preservation(entry(lib,programs,a,actor).landed.state,actor,a.state.accumulators[actor].push(a.history.len()));}
            else {inv::unloading_edit_preservation(a.state,actor,a.state.accumulators[actor]);}
        },
        r::Rule::Leave=>{inv::unloading_edit_preservation(a.state,actor,a.state.accumulators[actor]);},
        r::Rule::Unload=>{
            restore_preservation(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);
            let context=restore(a.history,a.state.accumulators[actor],a.state,actor).unwrap();
            assert(r::frame(context.control,z.state.control,actor)) by {
                assert forall|n:usize| n!=actor implies r::registered(context.control,n)==r::registered(z.state.control,n)
                    && (r::registered(context.control,n) ==> context.control.fibers[n]==z.state.control.fibers[n]) by { }
            }
            assert(r::step(context.control,z.state.control,actor,r::Rule::Unload));
            inv::control_preservation(context.control,z.state.control,actor,r::Rule::Unload);
            inv::shaped_edit(context,actor,Phase::Inactive,ISet::empty(),None,Seq::empty());
        },
        _=>{},
    }
    assert forall|n:usize,k:Port| s::registered(z.state,n) && z.state.tables[n].dom().contains(k)
        implies #[trigger] (lib.values)(k,z.state.tables[n][k]) by {
        match rule {
            r::Rule::Insert=>{assert(n!=actor);assert(a.state.tables[n]==z.state.tables[n]);},
            r::Rule::Remove=>{assert(n!=actor);assert(a.state.tables[n]==z.state.tables[n]);},
            r::Rule::Iter | r::Rule::Finish=>{assert(typed(lib,entry(lib,programs,a,actor).landed.state));},
            r::Rule::Divert=>{if landing(a,z,rule) {assert(typed(lib,entry(lib,programs,a,actor).landed.state));}},
            r::Rule::Unload=>{assert(typed(lib,restore(a.history,a.state.accumulators[actor],a.state,actor).unwrap()));},
            _=>{},
        }
    }
    p::unique_owner(a.state);
    match rule {
        r::Rule::Insert=>{p::empty_insertion(a.state,z.state,actor,ISet::full());},
        r::Rule::Remove=>{p::empty_erasure(a.state,actor,ISet::full());},
        r::Rule::Retire=>{
            p::unique_owner(z.state);
            assert(p::bindings_equal(a.state,z.state)) by {assert forall|key:Port,n:usize| p::owns(a.state,key,n)==p::owns(z.state,key,n) && (p::owns(a.state,key,n) ==> a.state.tables[n][key]==z.state.tables[n][key]) by { }}
            p::projection_equal(a.state,z.state,ISet::full());
        },
        r::Rule::Iter | r::Rule::Finish | r::Rule::Divert=>{
            if landing(a,z,rule) {
                let out=entry(lib,programs,a,actor).landed;
                p::unique_owner(out.state);
                p::lifecycle_edit(out.state,actor,z.state.control.fibers[actor].phase,a.state.control.fibers[actor].committed,z.state.iterators[actor],z.state.accumulators[actor],ISet::full());
                let table=context(out.state);assert(c::embed(table)==p::project(z.state,ISet::full()));
            } else {p::lifecycle_edit(a.state,actor,Phase::Unloading,a.state.control.fibers[actor].committed,None,a.state.accumulators[actor],ISet::full());}
        },
        r::Rule::Unload=>{
            let restored=restore(a.history,a.state.accumulators[actor],a.state,actor).unwrap();p::unique_owner(restored);
            p::lifecycle_edit(restored,actor,Phase::Inactive,ISet::empty(),None,Seq::empty(),ISet::full());
            let table=context(restored);assert(c::embed(table)==p::project(z.state,ISet::full()));
        },
        r::Rule::Begin | r::Rule::Leave=>{p::lifecycle_edit(a.state,actor,z.state.control.fibers[actor].phase,z.state.control.fibers[actor].committed,z.state.iterators[actor],z.state.accumulators[actor],ISet::full());},
        _=>{},
    }
    if p::project(a.state,ISet::full())==p::project(z.state,ISet::full()) {
        let table=context(a.state);assert(c::embed(table)==p::project(z.state,ISet::full()));
    }
    assert forall|n:usize| s::registered(z.state,n) implies z.state.effects[n]==0 && z.state.iterators[n]==#[trigger] marker(z.current[n]) by {
        if n!=actor {assert(s::registered(a.state,n));}
        else {
            match rule {
                r::Rule::Insert=>{},
                r::Rule::Remove=>{assert(false);},
                _=>{assert(s::registered(a.state,n));},
            }
        }
    }
}

/// Actual returned receipts enter the journal; all outstanding tokens name
/// their actor's receipt. Membership and value typing follow each real yield.
pub proof fn configuration_preservation<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,z:Configuration<U,I>,actor:usize,rule:r::Rule)
    requires d::primitive_theory(eq,lib),well_formed(lib,programs,a),step(lib,programs,a,z,actor,rule),
    ensures well_formed(lib,programs,z),
{
    frame(lib,programs,a,z,actor,rule);state_preservation(eq,lib,programs,a,z,actor,rule);
    if landing(a,z,rule) {
        let id=a.current[actor].unwrap();let e=entry(lib,programs,a,actor);
        d::member_unfolding(lib,programs(actor),declarations(a.state,actor),a.state.control.fibers[actor].provisions,id);
        run_admissible(eq,lib,programs(actor)(id),a.state,actor);
        member_continuation(eq,lib,programs(actor),id,a.state,actor);
        assert(history_sound(lib,programs,z.history)) by {
            assert forall|i:int| #![trigger z.history[i]] 0<=i<z.history.len() implies {
                let h=z.history[i];
                &&& run(lib,programs(h.landed.receipt.actor)(h.iterator),h.input,h.landed.receipt.actor)==Some(h.landed)
                &&& lift::undo(h.landed.receipt,h.landed.state)==Some(h.input)
                &&& receipt_typed(lib,h.landed.receipt)
            } by {if i<a.history.len() {assert(z.history[i]==a.history[i]);} else {assert(i==a.history.len());assert(z.history[i]==e);}}
        }
    }
    assert(tokens_valid(z)) by {
        assert forall|n:usize,i:int| #![trigger z.state.accumulators[n][i]] s::registered(z.state,n) && 0<=i<z.state.accumulators[n].len() implies {
            let token=z.state.accumulators[n][i];
            &&& token<z.history.len() && z.history[token as int].landed.receipt.actor==n
        } by {
            if n!=actor {assert(s::registered(a.state,n));}
            if n==actor && landing(a,z,rule) && i==a.state.accumulators[n].len() {
                assert(z.state.accumulators[n][i]==a.history.len());assert(z.history[a.history.len() as int]==entry(lib,programs,a,actor));
            } else {
                assert(s::registered(a.state,n));assert(i<a.state.accumulators[n].len());assert(z.state.accumulators[n][i]==a.state.accumulators[n][i]);
                let token=a.state.accumulators[n][i];assert(token<a.history.len());assert(z.history[token as int]==a.history[token as int]);
            }
        }
    }
    assert(members(lib,programs,z)) by {
        assert forall|n:usize| s::registered(z.state,n) implies component_member(lib,programs,z.state,n,z.roots[n])
            && (z.current[n].is_some() ==> component_member(lib,programs,z.state,n,z.current[n].unwrap())) by {
            if rule==r::Rule::Insert && n==actor {}
            else {
                assert(s::registered(a.state,n));assert(a.roots[n]==z.roots[n]);
                assert(component_member(lib,programs,a.state,n,a.roots[n]));
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
/// An arbitrary-length execution of all nine rules derives typed service
/// tables, resource safety, least-grammar continuations and authentic receipts
/// at every prefix. No intermediate invariant or desired final value is input.
pub proof fn from_empty_safe<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,states:Seq<Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires d::primitive_theory(eq,lib),execution(lib,programs,states,labels),states.first()==empty::<U,I>(),
    ensures forall|i:int| 0<=i<states.len() ==> inv::resource_safe(states[i].state) && typed(lib,states[i].state)
        && finite_context(states[i].state) && metadata(states[i]) && members(lib,programs,states[i]) && history_sound(lib,programs,states[i].history) && tokens_valid(states[i]),
{
    empty_well_formed(lib,programs);execution_preservation(eq,lib,programs,states,labels);
    assert forall|i:int| 0<=i<states.len() implies inv::resource_safe(states[i].state) && typed(lib,states[i].state)
        && finite_context(states[i].state) && metadata(states[i]) && members(lib,programs,states[i]) && history_sound(lib,programs,states[i].history) && tokens_valid(states[i]) by {
        assert(well_formed(lib,programs,states[i]));
        assert forall|key:Port,left:usize,right:usize| s::publishes(states[i].state,key,left) && s::publishes(states[i].state,key,right) implies left==right by {
            assert(states[i].state.control.fibers[left].provisions.contains(key));assert(states[i].state.control.fibers[right].provisions.contains(key));
        }
    }
}

pub proof fn context_unique<U>(a:s::State<U>,table:Map<Port,U>)
    requires finite_context(a),c::embed(table)==p::project(a,ISet::full()),
    ensures context(a)==table,
{
    let other=context(a);assert(c::embed(other)==c::embed(table));
    assert(other =~= table) by {
        assert forall|key:Port| other.dom().contains(key)==table.dom().contains(key) by {assert(c::embed(other).dom().contains(key)==c::embed(table).dom().contains(key));}
        assert forall|key:Port| other.dom().contains(key) implies other[key]==table[key] by {assert(c::embed(other)[key]==c::embed(table)[key]);}
    }
}
pub proof fn context_typed<A,X,U,B>(lib:Library<A,X,U,B>,a:s::State<U>)
    requires inv::well_formed(a),typed(lib,a),finite_context(a),
    ensures c::typed(lib.values,context(a)),
{
    let table=context(a);assert(c::embed(table)==p::project(a,ISet::full()));p::unique_owner(a);
    assert forall|key:Port| table.dom().contains(key) implies (lib.values)(key,table[key]) by {
        assert(c::embed(table).dom().contains(key));assert(p::project(a,ISet::full()).dom().contains(key));
        assert(exists|n:usize| p::owns(a,key,n));let provider=choose|n:usize| p::owns(a,key,n);p::lookup(a,ISet::full(),key,provider);
    }
}
/// The full-registry interpreter and the finite dependent context interpreter
/// execute the same actual operation and select the identical arbitrary-I
/// continuation. This is stronger than comparing termination markers.
pub proof fn run_projects<A,X,U,B,I>(lib:Library<A,X,U,B>,node:Node<A,X,U,B,I>,a:s::State<U>,actor:usize)
    requires inv::well_formed(a),finite_context(a),run(lib,node,a,actor).is_some(),
    ensures {
        let full=run(lib,node,a,actor).unwrap();let projected=d::run(lib,node,context(a));
        &&& projected.is_some() && finite_context(full.state)
        &&& projected.unwrap().state==context(full.state)
        &&& projected.unwrap().next==full.next
    },
{
    let table=context(a);assert(c::embed(table)==p::project(a,ISet::full()));
    let full=run(lib,node,a,actor).unwrap();
    lift::run_projects(stage(lib,node),a,actor);p::unique_owner(a);
    match node {
        d::Node::Unit=>{assert(c::embed(table)==p::project(full.state,ISet::full()));context_unique(full.state,table);},
        d::Node::Operation {operation:op,argument:x,select:_}=>{
            let key=(lib.key)(op);let provider=lift::resolve(a,actor,key).unwrap();
            lift::resolution_sound(a,actor,key);p::lookup(a,ISet::full(),key,provider);
            let y=(lib.apply)(op,x)(a.tables[provider][key]).unwrap();
            c::finite_embedding(table,table,key,y.value);p::update_slot_projection(a,provider,key,Some(y.value));
            assert(c::embed(table.insert(key,y.value))==p::project(full.state,ISet::full()));
            assert(finite_context(full.state));context_unique(full.state,table.insert(key,y.value));
        },
        d::Node::Provision {key,value,..}=>{
            assert(!table.dom().contains(key));c::finite_embedding(table,table,key,value);p::update_slot_projection(a,actor,key,Some(value));
            assert(c::embed(table.insert(key,value))==p::project(full.state,ISet::full()));
            assert(finite_context(full.state));context_unique(full.state,table.insert(key,value));
        },
    }
}
/// For installed members, the lift adds no failure to the dependent context
/// grammar. No undefined application is totalized as an identity operation.
pub proof fn run_definedness<A,X,U,B,I>(lib:Library<A,X,U,B>,node:Node<A,X,U,B,I>,a:s::State<U>,actor:usize)
    requires inv::well_formed(a),finite_context(a),s::registered(a,actor),a.control.fibers[actor].phase!=Phase::Inactive,
        d::permitted(lib,declarations(a,actor),a.control.fibers[actor].provisions,node),
    ensures run(lib,node,a,actor).is_some()==d::run(lib,node,context(a)).is_some(),
{
    let table=context(a);assert(c::embed(table)==p::project(a,ISet::full()));
    let allowed=|_:Port,_:m::Operation<U,B>|true;
    lift::run_definedness(stage(lib,node),allowed,a,actor);
}
/// A successful full inverse follows the same finite-context inverse. The
/// converse needs lifetime/commitment conditions: a flat key alone must never
/// authorize redirecting a receipt to a replacement provider.
pub proof fn inverse_projects<A,X,U,B,I>(lib:Library<A,X,U,B>,node:Node<A,X,U,B,I>,input:s::State<U>,actor:usize,current:s::State<U>)
    requires inv::well_formed(input),finite_context(input),run(lib,node,input,actor).is_some(),
        inv::well_formed(current),finite_context(current),lift::undo(run(lib,node,input,actor).unwrap().receipt,current).is_some(),
    ensures {
        let receipt=run(lib,node,input,actor).unwrap().receipt;
        let restored=lift::undo(receipt,current).unwrap();
        let local=d::run(lib,node,context(input)).unwrap();
        &&& finite_context(restored)
        &&& (local.undo)(context(current))==Some(context(restored))
    },
{
    run_projects(lib,node,input,actor);let original=context(input);let now=context(current);
    assert(c::embed(original)==p::project(input,ISet::full()));assert(c::embed(now)==p::project(current,ISet::full()));
    let receipt=run(lib,node,input,actor).unwrap().receipt;let restored=lift::undo(receipt,current).unwrap();
    lift::inverse_projects(receipt,current);
    match node {
        d::Node::Unit=>{context_unique(restored,now);},
        d::Node::Operation {operation:op,argument:x,..}=>{
            let key=(lib.key)(op);let provider=lift::resolve(input,actor,key).unwrap();let y=(lib.apply)(op,x)(input.tables[provider][key]).unwrap();
            p::unique_owner(input);p::lookup(input,ISet::full(),key,provider);
            lift::resolution_sound(current,actor,key);p::unique_owner(current);p::lookup(current,ISet::full(),key,provider);
            let value=(y.undo)(current.tables[provider][key]).unwrap();
            c::finite_embedding(now,now,key,value);
            assert(c::embed(now.insert(key,value))==p::project(restored,ISet::full()));assert(finite_context(restored));
            context_unique(restored,now.insert(key,value));
        },
        d::Node::Provision {key,..}=>{
            p::unique_owner(current);p::lookup(current,ISet::full(),key,actor);
            assert(c::embed(now.remove(key)) =~= c::embed(now).remove(key));
            assert(c::embed(now.remove(key))==p::project(restored,ISet::full()));assert(finite_context(restored));
            context_unique(restored,now.remove(key));
        },
    }
}

pub proof fn membership_covers<A,X,U,B,I>(lib:Library<A,X,U,B>,program:d::Program<Port,A,X,U,B,I>,declared:ISet<Port>,provisions:ISet<Port>,id:I)
    requires provisions.subset_of(declared),d::member(lib,program,declared,provisions,id),
    ensures d::covered(lib,program,declared,id),
{
    let names=d::members(lib,program,declared,provisions);
    assert forall|i:I| names.contains(i) implies d::covers(lib,declared,program(i)) && d::continuations(lib,program(i),names) by {
        d::member_unfolding(lib,program,declared,provisions,i);
        match program(i) {d::Node::Provision {key,..}=>{assert(provisions.contains(key));},_=>{}}
    }
    assert(names.contains(id));
}
/// A current component in a real registry trace is a recursive witnessed
/// dependent iterator on the finite coeffect observation. This connects the
/// full lifecycle proof to Lemma 39, not just to the erased local stage.
pub proof fn trace_current_witness<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,states:Seq<Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,at:int,actor:usize)
    requires d::primitive_theory(eq,lib),execution(lib,programs,states,labels),states.first()==empty::<U,I>(),
        0<=at<states.len(),s::registered(states[at].state,actor),states[at].current.dom().contains(actor) && states[at].current[actor].is_some(),
    ensures {
        let a=states[at];let id=a.current[actor].unwrap();let keys=declarations(a.state,actor);
        &&& c::typed(lib.values,context(a.state))
        &&& crate::iterators::paper_partial_witnessed(|x:Map<Port,U>,y:Map<Port,U>|d::context_equal(eq,keys,x,y),d::family(lib,programs(actor)),id)
        &&& run(lib,programs(actor)(id),a.state,actor).is_some()==d::run(lib,programs(actor)(id),context(a.state)).is_some()
        &&& (run(lib,programs(actor)(id),a.state,actor).is_some() ==> {
            let full=run(lib,programs(actor)(id),a.state,actor).unwrap();let local=d::run(lib,programs(actor)(id),context(a.state)).unwrap();
            &&& local.state==context(full.state) && local.next==full.next
            &&& lift::undo(full.receipt,full.state)==Some(a.state)
        })
    },
{
    empty_well_formed(lib,programs);execution_preservation(eq,lib,programs,states,labels);
    let a=states[at];let id=a.current[actor].unwrap();let keys=declarations(a.state,actor);let provisions=a.state.control.fibers[actor].provisions;
    assert(well_formed(lib,programs,a));assert(d::member(lib,programs(actor),keys,provisions,id));assert(provisions.subset_of(keys));
    membership_covers(lib,programs(actor),keys,provisions,id);
    d::grammar_paper_witnessed(eq,lib,programs(actor),keys,provisions,keys,id);
    context_typed(lib,a.state);d::member_unfolding(lib,programs(actor),keys,provisions,id);
    assert(a.state.iterators[actor]==marker(a.current[actor]));assert(marker(a.current[actor])==Some(0));
    assert(a.state.iterators[actor].is_some());assert(a.state.control.fibers[actor].phase==Phase::Loading);
    run_definedness(lib,programs(actor)(id),a.state,actor);
    if run(lib,programs(actor)(id),a.state,actor).is_some() {
        run_projects(lib,programs(actor)(id),a.state,actor);run_admissible(eq,lib,programs(actor)(id),a.state,actor);
    }
}

pub proof fn failed_restore_blocks_unload<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,actor:usize)
    requires restore(a.history,a.state.accumulators[actor],a.state,actor).is_none(),
    ensures forall|z:Configuration<U,I>| !step(lib,programs,a,z,actor,r::Rule::Unload),
{ }
}
