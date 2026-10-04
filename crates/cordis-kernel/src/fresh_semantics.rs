//! Nine strict source rules for one fixed fresh-binding program family.
//!
//! Allocation choices occur only in actual FreshChild landings. Original
//! continuation values and authentic receipts remain in the same history.
#[cfg(verus_keep_ghost)]
pub use crate::fresh_grammar::{history_sound, run};
pub use crate::fresh_grammar::{Library, Node, Programs};
#[cfg(verus_keep_ghost)]
pub use crate::mixed_grammar::{
    captured_child, edit, inverse_preservation, kind, landing, metadata, owner, receipt_typed,
    restore, tokens_valid, undo, unload,
};
pub use crate::mixed_grammar::{Configuration, Entry, Landed};
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, contexts as c, dependent_grammar as d, dependent_lift as dep,
    fresh_grammar as syntax, grammar_lift as lift, mixed_syntax, observational_grammar as og,
    observational_lift as ol, preservation as inv, projection as p, refinement as r,
    semantics as s, Phase, Port,
};
use vstd::prelude::*;

verus! {
pub type Label = (usize,crate::refinement::Rule,Option<usize>);
pub open spec fn component_member<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:s::State<U>,actor:usize,id:I)->bool {
    syntax::member(lib,programs,actor,dep::declarations(a,actor),a.control.fibers[actor].provisions,id)
}

pub open spec fn members<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>)->bool {
    forall|n:usize| s::registered(a.state,n) ==> component_member(lib,programs,a.state,n,a.roots[n])
        && (a.current[n].is_some() ==> component_member(lib,programs,a.state,n,a.current[n].unwrap()))
}
pub open spec fn history_well_formed<U,I>(history:Seq<Entry<U,I>>)->bool {
    forall|i:int| #![trigger history[i]] 0<=i<history.len() ==> inv::well_formed(history[i].input) && inv::well_formed(history[i].landed.state)
}
pub open spec fn well_formed<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>)->bool {
    inv::well_formed(a.state) && dep::typed(lib,a.state) && dep::finite_context(a.state) && metadata(a) && members(lib,programs,a)
        && history_sound(lib,programs,a.history) && history_well_formed(a.history) && tokens_valid(a) && ch::retained(kind(a.history),a.state)
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

pub open spec fn entry<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,actor:usize,choice:Option<usize>)->Entry<U,I> {
    let iterator=a.current[actor].unwrap();Entry {input:a.state,iterator,landed:run(lib,programs(actor)(iterator),a.state,actor,choice).unwrap()}
}
pub open spec fn land<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,actor:usize,phase:Phase,choice:Option<usize>)->Configuration<U,I> {
    let e=entry(lib,programs,a,actor,choice);let next=if phase==Phase::Loading {e.landed.next} else {None};
    let roots=match e.landed.spawn {None=>a.roots,Some((child,root))=>a.roots.insert(child,root)};
    let current=match e.landed.spawn {None=>a.current,Some((child,_))=>a.current.insert(child,None)};
    Configuration {state:s::edit(e.landed.state,actor,phase,a.state.control.fibers[actor].committed,dep::marker(next),a.state.accumulators[actor].push(a.history.len())),
        roots,current:current.insert(actor,next),history:a.history.push(e)}
}
pub open spec fn step<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,z:Configuration<U,I>,actor:usize,rule:r::Rule,choice:Option<usize>)->bool {
    match rule {
        r::Rule::Insert=>choice.is_none() && inv::insert_map(a.state,z.state,actor) && z.state.effects[actor]==0
            && z.roots==a.roots.insert(actor,z.roots[actor]) && z.current==a.current.insert(actor,None) && z.history==a.history
            && component_member(lib,programs,z.state,actor,z.roots[actor]),
        r::Rule::Retire=>choice.is_none() && s::child_retire(a.state,z.state,actor) && z.roots==a.roots && z.current==a.current && z.history==a.history,
        r::Rule::Remove=>choice.is_none() && r::step(a.state.control,z.state.control,actor,rule) && a.state.tables[actor].is_empty()
            && ch::remove_unreferenced(kind(a.history),a.state,actor)
            && z.state==s::erase(a.state,actor) && z.roots==a.roots.remove(actor) && z.current==a.current.remove(actor) && z.history==a.history,
        r::Rule::Begin=>choice.is_none() && s::registered(a.state,actor) && a.state.control.fibers[actor].phase==Phase::Inactive
            && s::target(a.state,actor,z.state.control.fibers[actor].committed)
            && z==edit(a,actor,Phase::Loading,z.state.control.fibers[actor].committed,Some(a.roots[actor]),Seq::empty()),
        r::Rule::Iter | r::Rule::Finish=>{
            let out=run(lib,programs(actor)(a.current[actor].unwrap()),a.state,actor,choice);
            &&& s::registered(a.state,actor) && a.state.control.fibers[actor].phase==Phase::Loading && a.current[actor].is_some()
            &&& s::coherent(a.state,actor) && out.is_some()
            &&& (rule==r::Rule::Iter)==out.unwrap().next.is_some()
            &&& z==land(lib,programs,a,actor,if rule==r::Rule::Iter {Phase::Loading} else {Phase::Active},choice)
        },
        r::Rule::Divert=>s::registered(a.state,actor) && a.state.control.fibers[actor].phase==Phase::Loading && a.current[actor].is_some() && !s::coherent(a.state,actor)
            && ((choice.is_none() && z==edit(a,actor,Phase::Unloading,a.state.control.fibers[actor].committed,None,a.state.accumulators[actor]))
                || (run(lib,programs(actor)(a.current[actor].unwrap()),a.state,actor,choice).is_some() && z==land(lib,programs,a,actor,Phase::Unloading,choice))),
        r::Rule::Leave=>choice.is_none() && s::registered(a.state,actor) && a.state.control.fibers[actor].phase==Phase::Active && !s::coherent(a.state,actor)
            && z==edit(a,actor,Phase::Unloading,a.state.control.fibers[actor].committed,None,a.state.accumulators[actor]),
        r::Rule::Unload=>choice.is_none() && s::registered(a.state,actor) && a.state.control.fibers[actor].phase==Phase::Unloading && !r::relied(a.state.control,actor)
            && restore(a.history,a.state.accumulators[actor],a.state,actor).is_some() && z==unload(a,actor),
        _=>false,
    }
}
pub open spec fn local_model<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,choice:Option<usize>)->s::Model<U> {
    s::Model {
        iterate:|actor:usize,_id:nat,input:s::State<U>| {
            let out=run(lib,programs(actor)(a.current[actor].unwrap()),input,actor,choice).unwrap();
            s::Yield {state:out.state,inverse:a.history.len(),next:dep::marker(out.next)}
        },
        undo:|token:nat,input:s::State<U>|undo(a.history[token as int].landed.receipt,input).unwrap(),
    }
}
pub proof fn restore_refines<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,source:Configuration<U,I>,tokens:Seq<nat>,a:s::State<U>,actor:usize,choice:Option<usize>)
    requires inv::well_formed(a),dep::typed(lib,a),dep::finite_context(a),history_sound(lib,programs,source.history),
        restore(source.history,tokens,a,actor).is_some(),
    ensures restore(source.history,tokens,a,actor).unwrap()==s::restore(local_model(lib,programs,source,choice),tokens,a),
        inv::admissible_restore(local_model(lib,programs,source,choice),tokens,a,actor),
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let receipt=source.history[tokens.last() as int].landed.receipt;
        inverse_preservation(lib,receipt,a);
        restore_refines(lib,programs,source,tokens.drop_last(),undo(receipt,a).unwrap(),actor,choice);
    }
}
pub proof fn run_admissible<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,node:Node<A,X,U,B,I>,a:s::State<U>,actor:usize,choice:Option<usize>)
    requires og::primitive_theory(eq,lib),inv::well_formed(a),dep::typed(lib,a),dep::finite_context(a),
        syntax::permitted(lib,dep::declarations(a,actor),a.control.fibers[actor].provisions,node),run(lib,node,a,actor,choice).is_some(),
    ensures {
        let out=run(lib,node,a,actor,choice).unwrap();
        &&& owner(out.receipt)==actor && s::registered(a,actor) && captured_child(out.receipt)==choice
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

    },
{
    let concrete=syntax::instantiate(node,choice).unwrap();
    assert(mixed_syntax::permitted(lib,dep::declarations(a,actor),a.control.fibers[actor].provisions,concrete)) by {
        match node {Node::Dependent {..}=>{},Node::FreshChild {..}=>{}}
    }
    ol::run_admissible(eq,lib,concrete,a,actor);
    syntax::allocation_guard(lib,node,a,actor,choice);
}

pub proof fn run_members<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:s::State<U>,actor:usize,id:I,choice:Option<usize>)
    requires og::primitive_theory(eq,lib),component_member(lib,programs,a,actor,id),run(lib,programs(actor)(id),a,actor,choice).is_some(),
    ensures {
        let out=run(lib,programs(actor)(id),a,actor,choice).unwrap();
        &&& syntax::permitted(lib,dep::declarations(a,actor),a.control.fibers[actor].provisions,programs(actor)(id))
        &&& (out.next.is_some() ==> component_member(lib,programs,a,actor,out.next.unwrap()))
        &&& (out.spawn.is_some() ==> component_member(lib,programs,out.state,out.spawn.unwrap().0,out.spawn.unwrap().1))
    },
{
    syntax::member_unfolding(lib,programs,actor,dep::declarations(a,actor),a.control.fibers[actor].provisions,id);
    match programs(actor)(id) {
        Node::Dependent {node}=>{
            match node {
                d::Node::Operation {operation:op,argument:x,select}=>{
                    let k=(lib.key)(op);let provider=lift::resolve(a,actor,k).unwrap();
                    let y=(lib.apply)(op,x)(a.tables[provider][k]).unwrap();
                    assert(d::operation_typed(lib,op,x));assert((lib.outcomes)(op,y.outcome));
                    if select(y.outcome).is_some() {
                        assert(syntax::local(syntax::members(lib,programs),actor,dep::declarations(a,actor),a.control.fibers[actor].provisions).contains(select(y.outcome).unwrap()));
                    }
                },_=>{},
            }
        },
        Node::FreshChild {dependencies,provisions,body}=>{
            let child=choice.unwrap();let (root,next)=body(child);
            assert(syntax::members(lib,programs).contains((child,dependencies.union(provisions),provisions,root)));
            if next.is_some() {assert(syntax::members(lib,programs).contains((actor,dep::declarations(a,actor),a.control.fibers[actor].provisions,next.unwrap())));}
        },
    }
}
pub proof fn step_refines<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,z:Configuration<U,I>,actor:usize,rule:r::Rule,choice:Option<usize>)
    requires og::primitive_theory(eq,lib),well_formed(lib,programs,a),step(lib,programs,a,z,actor,rule,choice),
    ensures s::step(local_model(lib,programs,a,choice),a.state,z.state,actor,rule),
        inv::admissible_step(local_model(lib,programs,a,choice),a.state,z.state,actor,rule),inv::well_formed(z.state),
{
    if landing(a,z,rule) {
        let id=a.current[actor].unwrap();run_members(eq,lib,programs,a.state,actor,id,choice);
        run_admissible(eq,lib,programs(actor)(id),a.state,actor,choice);
    }
    match rule {
        r::Rule::Insert=>{inv::insert_preservation(a.state,z.state,actor);},
        r::Rule::Unload=>{restore_refines(lib,programs,a,a.state.accumulators[actor],a.state,actor,choice);},
        _=>{},
    }
    let model=local_model(lib,programs,a,choice);
    assert(s::step(model,a.state,z.state,actor,rule));
    assert(inv::admissible_step(model,a.state,z.state,actor,rule));
    inv::full_preservation(model,a.state,z.state,actor,rule);
}

pub proof fn frame<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,z:Configuration<U,I>,actor:usize,rule:r::Rule,choice:Option<usize>)
    requires og::primitive_theory(eq,lib),well_formed(lib,programs,a),step(lib,programs,a,z,actor,rule,choice),
    ensures {
        &&& forall|n:usize| s::registered(a.state,n) && s::registered(z.state,n) ==> r::interface_same(a.state.control.fibers[n],z.state.control.fibers[n])
            && a.state.effects[n]==z.state.effects[n] && a.roots[n]==z.roots[n]
        &&& forall|n:usize| n!=actor && s::registered(a.state,n) ==> s::registered(z.state,n)
            && a.current[n]==z.current[n] && a.state.accumulators[n]==z.state.accumulators[n]
        &&& forall|n:usize| s::registered(z.state,n) && !s::registered(a.state,n) ==> {
            &&& z.current[n].is_none() && z.state.accumulators[n].len()==0
            &&& (n==actor && rule==r::Rule::Insert || landing(a,z,rule) && entry(lib,programs,a,actor,choice).landed.spawn.is_some()
                && n==entry(lib,programs,a,actor,choice).landed.spawn.unwrap().0)
        }
        &&& (landing(a,z,rule) ==> {
            let e=entry(lib,programs,a,actor,choice);
            &&& s::registered(a.state,actor) && a.current[actor].is_some()
            &&& run(lib,programs(actor)(a.current[actor].unwrap()),a.state,actor,choice).is_some()
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
        let id=a.current[actor].unwrap();run_members(eq,lib,programs,a.state,actor,id,choice);
        run_admissible(eq,lib,programs(actor)(id),a.state,actor,choice);
        inv::forward_preservation(a.state,entry(lib,programs,a,actor,choice).landed.state,actor);
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
        &&& (n==actor && rule==r::Rule::Insert || landing(a,z,rule) && entry(lib,programs,a,actor,choice).landed.spawn.is_some()
            && n==entry(lib,programs,a,actor,choice).landed.spawn.unwrap().0)
    } by { }
}

pub proof fn state_preservation<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,z:Configuration<U,I>,actor:usize,rule:r::Rule,choice:Option<usize>)
    requires og::primitive_theory(eq,lib),well_formed(lib,programs,a),step(lib,programs,a,z,actor,rule,choice),
    ensures inv::well_formed(z.state),dep::typed(lib,z.state),metadata(z),dep::finite_context(z.state),
{
    step_refines(eq,lib,programs,a,z,actor,rule,choice);frame(eq,lib,programs,a,z,actor,rule,choice);
    if landing(a,z,rule) {
        let id=a.current[actor].unwrap();run_members(eq,lib,programs,a.state,actor,id,choice);
        run_admissible(eq,lib,programs(actor)(id),a.state,actor,choice);
    }
    if rule==r::Rule::Unload {restore_preservation(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);}
    assert forall|n:usize,k:Port| s::registered(z.state,n) && z.state.tables[n].dom().contains(k)
        implies #[trigger] (lib.values)(k,z.state.tables[n][k]) by {
        match rule {
            r::Rule::Insert | r::Rule::Remove=>{assert(n!=actor);assert(a.state.tables[n]==z.state.tables[n]);},
            r::Rule::Iter | r::Rule::Finish=>{assert(dep::typed(lib,entry(lib,programs,a,actor,choice).landed.state));},
            r::Rule::Divert=>{if landing(a,z,rule) {assert(dep::typed(lib,entry(lib,programs,a,actor,choice).landed.state));}},
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
                let out=entry(lib,programs,a,actor,choice).landed;p::unique_owner(out.state);
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
        else if landing(a,z,rule) {assert(entry(lib,programs,a,actor,choice).landed.spawn==Some((n,z.roots[n])));}
    }
    assert(z.roots.dom() =~= z.state.control.fibers.dom());
    assert(z.current.dom() =~= z.roots.dom());
}

#[verifier::rlimit(20)]
#[verifier::spinoff_prover]
pub proof fn configuration_preservation<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,a:Configuration<U,I>,z:Configuration<U,I>,actor:usize,rule:r::Rule,choice:Option<usize>)
    requires og::primitive_theory(eq,lib),well_formed(lib,programs,a),step(lib,programs,a,z,actor,rule,choice),
    ensures well_formed(lib,programs,z),
{
    frame(eq,lib,programs,a,z,actor,rule,choice);state_preservation(eq,lib,programs,a,z,actor,rule,choice);
    if landing(a,z,rule) {
        let id=a.current[actor].unwrap();let e=entry(lib,programs,a,actor,choice);
        run_members(eq,lib,programs,a.state,actor,id,choice);run_admissible(eq,lib,programs(actor)(id),a.state,actor,choice);
        assert(history_sound(lib,programs,z.history)) by {
            assert forall|i:int| #![trigger z.history[i]] 0<=i<z.history.len() implies {
                let h=z.history[i];let n=owner(h.landed.receipt);
                &&& run(lib,programs(n)(h.iterator),h.input,n,captured_child(h.landed.receipt))==Some(h.landed)
                &&& receipt_typed(lib,h.landed.receipt) && undo(h.landed.receipt,h.landed.state).is_some()
            } by {if i<a.history.len() {assert(z.history[i]==a.history[i]);} else {assert(i==a.history.len());assert(z.history[i]==e);}}
        }
    }
    assert(history_well_formed(z.history)) by {
        assert forall|i:int| #![trigger z.history[i]] 0<=i<z.history.len() implies inv::well_formed(z.history[i].input) && inv::well_formed(z.history[i].landed.state) by {
            if i<a.history.len() {assert(z.history[i]==a.history[i]);}
            else {assert(landing(a,z,rule));assert(i==a.history.len());assert(z.history[i]==entry(lib,programs,a,actor,choice));}
        }
    }
    assert(tokens_valid(z)) by {
        assert forall|n:usize,i:int| #![trigger z.state.accumulators[n][i]] s::registered(z.state,n) && 0<=i<z.state.accumulators[n].len() implies {
            let token=z.state.accumulators[n][i];
            &&& token<z.history.len() && owner(z.history[token as int].landed.receipt)==n
        } by {
            assert(s::registered(a.state,n));
            if n==actor && landing(a,z,rule) && i==a.state.accumulators[n].len() {
                assert(z.state.accumulators[n][i]==a.history.len());assert(z.history[a.history.len() as int]==entry(lib,programs,a,actor,choice));
            } else {
                assert(i<a.state.accumulators[n].len());assert(z.state.accumulators[n][i]==a.state.accumulators[n][i]);
                let token=a.state.accumulators[n][i];assert(token<a.history.len());assert(z.history[token as int]==a.history[token as int]);
            }
        }
    }
    assert(members(lib,programs,z)) by {
        assert forall|n:usize| s::registered(z.state,n) implies component_member(lib,programs,z.state,n,z.roots[n])
            && (z.current[n].is_some() ==> component_member(lib,programs,z.state,n,z.current[n].unwrap())) by {
            if !s::registered(a.state,n) {
                if rule!=r::Rule::Insert {
                    let e=entry(lib,programs,a,actor,choice);assert(e.landed.spawn==Some((n,z.roots[n])));
                    assert(component_member(lib,programs,e.landed.state,n,z.roots[n]));
                }
            } else {
                assert(a.roots[n]==z.roots[n]);assert(component_member(lib,programs,a.state,n,a.roots[n]));
                if z.current[n].is_some() {
                    if n!=actor {assert(a.current[n]==z.current[n]);}
                    else if rule==r::Rule::Begin {assert(z.current[n]==Some(a.roots[n]));}
                    else if rule==r::Rule::Iter {
                        let e=entry(lib,programs,a,actor,choice);assert(z.current[n]==e.landed.next);
                        assert(component_member(lib,programs,a.state,n,e.landed.next.unwrap()));
                    } else {assert(a.current[n]==z.current[n]);}
                }
            }
        }
    }
    assert(ch::retained(kind(z.history),z.state)) by {
        assert forall|n:usize,token:nat,child:usize| s::registered(z.state,n) && z.state.accumulators[n].contains(token)
            && kind(z.history)(token)==Some(child) implies s::registered(z.state,child) by {
            let i=choose|i:int| 0<=i<z.state.accumulators[n].len() && z.state.accumulators[n][i]==token;
            assert(s::registered(a.state,n));
            if landing(a,z,rule) && token==a.history.len() {
                let e=entry(lib,programs,a,actor,choice);assert(z.history[token as int]==e);
                assert(e.landed.spawn.is_some());assert(e.landed.spawn.unwrap().0==child);
            } else {
                assert(token<a.history.len());assert(z.history[token as int]==a.history[token as int]);
                assert(a.state.accumulators[n].contains(token));assert(kind(a.history)(token)==Some(child));
                assert(s::registered(a.state,child));
                if rule==r::Rule::Remove {assert(child!=actor);}
                assert(s::registered(z.state,child));
            }
        }
    }
}

pub open spec fn empty<U,I>()->Configuration<U,I> {
    Configuration {state:inv::empty(),roots:IMap::empty(),current:IMap::empty(),history:Seq::empty()}
}
pub proof fn empty_well_formed<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>)
    ensures well_formed(lib,programs,empty::<U,I>()),
{inv::empty_well_formed::<U>();assert(c::embed(Map::<Port,U>::empty()) =~= p::project(empty::<U,I>().state,ISet::full()));}

pub open spec fn states<U,I>(trace:Seq<Configuration<U,I>>)->Seq<s::State<U>> {
    Seq::new(trace.len(),|i:int|trace[i].state)
}
pub open spec fn rules(labels:Seq<(usize,r::Rule,Option<usize>)>)->Seq<(usize,r::Rule)> {
    labels.map(|_:int,label:(usize,r::Rule,Option<usize>)|(label.0,label.1))
}
pub open spec fn execution<A,X,U,B,I>(lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,states:Seq<Configuration<U,I>>,labels:Seq<(usize,r::Rule,Option<usize>)>)->bool {
    states.len()==labels.len()+1 && forall|i:int| 0<=i<labels.len() ==> step(lib,programs,states[i],states[i+1],labels[i].0,labels[i].1,labels[i].2)
}
pub proof fn execution_preservation<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,states:Seq<Configuration<U,I>>,labels:Seq<(usize,r::Rule,Option<usize>)>)
    requires og::primitive_theory(eq,lib),execution(lib,programs,states,labels),well_formed(lib,programs,states.first()),
    ensures forall|i:int| 0<=i<states.len() ==> well_formed(lib,programs,states[i]),
    decreases labels.len(),
{
    if labels.len()>0 {
        let previous=states.drop_last();let prefix=labels.drop_last();
        assert(execution(lib,programs,previous,prefix)) by {
            assert forall|i:int| 0<=i<prefix.len() implies step(lib,programs,previous[i],previous[i+1],prefix[i].0,prefix[i].1,prefix[i].2) by { }
        }
        execution_preservation(eq,lib,programs,previous,prefix);
        configuration_preservation(eq,lib,programs,previous.last(),states.last(),labels.last().0,labels.last().1,labels.last().2);
        assert forall|i:int| 0<=i<states.len() implies well_formed(lib,programs,states[i]) by {
            if i<previous.len() {assert(states[i]==previous[i]);} else {assert(i==states.len()-1);}
        }
    }
}
pub proof fn from_empty_safe<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,states:Seq<Configuration<U,I>>,labels:Seq<(usize,r::Rule,Option<usize>)>)
    requires og::primitive_theory(eq,lib),execution(lib,programs,states,labels),states.first()==empty::<U,I>(),
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

pub proof fn execution_ordering<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:Library<A,X,U,B>,programs:Programs<A,X,U,B,I>,trace:Seq<Configuration<U,I>>,labels:Seq<(usize,r::Rule,Option<usize>)>)
    requires og::primitive_theory(eq,lib),execution(lib,programs,trace,labels),well_formed(lib,programs,trace.first()),
    ensures crate::indexed_ordering::trace(states(trace),rules(labels)),
{
    execution_preservation(eq,lib,programs,trace,labels);
    assert forall|i:int| 0<=i<labels.len() implies crate::indexed_ordering::step(states(trace)[i],states(trace)[i+1],rules(labels)[i].0,rules(labels)[i].1) by {
        step_refines(eq,lib,programs,trace[i],trace[i+1],labels[i].0,labels[i].1,labels[i].2);
        assert(s::step(local_model(lib,programs,trace[i],labels[i].2),states(trace)[i],states(trace)[i+1],labels[i].0,labels[i].1)
            && inv::admissible_step(local_model(lib,programs,trace[i],labels[i].2),states(trace)[i],states(trace)[i+1],labels[i].0,labels[i].1));
    }
}

}
