//! Recovery derived from actual dependent-grammar executions.
//!
//! The value replay is the explicit identity-extension algebra of `entangled`.
//! It is a counterfactual value calculation, never a replay of lifecycle guards.
//! Strict operation/inverse failure remains failure in the source execution.
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_grammar as d, dependent_lift as dl, entangled as e, grammar_lift as gl,
    mediated as m, semantics as s, Port,
};
#[cfg(verus_keep_ghost)]
use crate::{preservation as inv, projection as p, refinement as r, Binding, Phase};
use vstd::prelude::*;

verus! {

pub open spec fn total<V>(f:m::PartialMap<V>)->spec_fn(V)->V { |v:V|match f(v) {Some(w)=>w,None=>v} }
pub open spec fn forward<V,O>(op:m::Operation<V,O>)->spec_fn(V)->V { |v:V|match op(v) {Some(y)=>y.value,None=>v} }
pub open spec fn generator<A,X,U,B>(lib:dl::Library<A,X,U,B>,key:Port,f:spec_fn(U)->U)->bool {
    exists|a:A,x:X| lib.allowed.contains(a) && #[trigger] (lib.arguments)(a,x) && (lib.key)(a)==key && {
        let op=(lib.apply)(a,x);
        f==forward(op) || exists|v:U| #[trigger] op(v).is_some() && f==total(op(v).unwrap().undo)
    }
}
/// A key-local interface obligation, not an episode recovery premise. The
/// identity extension must be checked explicitly; strict Option commutation
/// alone is not silently converted to this exact-value statement.
pub open spec fn independent_keys<A,X,U,B>(lib:dl::Library<A,X,U,B>)->bool {
    forall|key:Port,f:spec_fn(U)->U,g:spec_fn(U)->U| generator(lib,key,f) && generator(lib,key,g)
        ==> forall|v:U| #[trigger] f(g(v))==g(f(v))
}
pub open spec fn receipt_action<U>(receipt:gl::Receipt<U>)->e::Action<U> {
    match receipt.inverse {
        gl::Inverse::Unit=>e::Action::Identity,
        gl::Inverse::Operation {key,undo,..}=>e::Action::Operation {key,update:total(undo)},
        gl::Inverse::Provision {key}=>e::Action::Restriction {key},
    }
}
pub open spec fn action_typed<A,X,U,B>(lib:dl::Library<A,X,U,B>,action:e::Action<U>)->bool {
    match action {e::Action::Operation {key,update}=>generator(lib,key,update),_=>true}
}
pub open spec fn history_typed<A,X,U,B,I>(lib:dl::Library<A,X,U,B>,history:Seq<dl::Entry<U,I>>)->bool {
    forall|i:int| 0<=i<history.len() ==> action_typed(lib,receipt_action(#[trigger] history[i].landed.receipt))
}
pub open spec fn word<U,I>(history:Seq<dl::Entry<U,I>>,tokens:Seq<nat>)->Seq<e::Action<U>> {
    Seq::new(tokens.len(),|i:int|receipt_action(history[tokens[i] as int].landed.receipt))
}
pub open spec fn own_word<U,I>(a:dl::Configuration<U,I>,actor:usize)->Seq<e::Action<U>> {word(a.history,a.state.accumulators[actor])}
pub open spec fn forward_action<A,X,U,B,I>(lib:dl::Library<A,X,U,B>,node:dl::Node<A,X,U,B,I>)->e::Action<U> {
    e::mediated_action(dl::stage(lib,node))
}
pub proof fn node_actions_typed<A,X,U,B,I>(lib:dl::Library<A,X,U,B>,node:dl::Node<A,X,U,B,I>,a:s::State<U>,actor:usize)
    requires d::permitted(lib,dl::declarations(a,actor),a.control.fibers[actor].provisions,node),dl::run(lib,node,a,actor).is_some(),
    ensures action_typed(lib,forward_action(lib,node)),action_typed(lib,receipt_action(dl::run(lib,node,a,actor).unwrap().receipt)),
        e::inverse_action(receipt_action(dl::run(lib,node,a,actor).unwrap().receipt)),
        e::key(receipt_action(dl::run(lib,node,a,actor).unwrap().receipt)).is_some() ==>
            dl::declarations(a,actor).contains(e::key(receipt_action(dl::run(lib,node,a,actor).unwrap().receipt)).unwrap()),
{
    match node {
        d::Node::Operation {operation:op,argument:x,..}=>{
            let k=(lib.key)(op);let operation=(lib.apply)(op,x);let provider=gl::resolve(a,actor,k).unwrap();let v=a.tables[provider][k];
            assert(operation(v).is_some());assert(generator(lib,k,forward(operation)));assert(generator(lib,k,total(operation(v).unwrap().undo)));
        },_=>{}
    }
}
pub proof fn history_typed_step<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,a:dl::Configuration<U,I>,z:dl::Configuration<U,I>,actor:usize,rule:r::Rule)
    requires d::primitive_theory(eq,lib),dl::well_formed(lib,programs,a),history_typed(lib,a.history),dl::step(lib,programs,a,z,actor,rule),
    ensures history_typed(lib,z.history),
{
    dl::frame(lib,programs,a,z,actor,rule);
    if dl::landing(a,z,rule) {
        let id=a.current[actor].unwrap();d::member_unfolding(lib,programs(actor),dl::declarations(a.state,actor),a.state.control.fibers[actor].provisions,id);
        node_actions_typed(lib,programs(actor)(id),a.state,actor);
        assert forall|i:int| 0<=i<z.history.len() implies action_typed(lib,receipt_action(#[trigger] z.history[i].landed.receipt)) by {
            if i<a.history.len() {assert(z.history[i]==a.history[i]);} else {assert(i==a.history.len());assert(z.history[i]==dl::entry(lib,programs,a,actor));}
        }
    }
}
pub proof fn trace_history_typed<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,states:Seq<dl::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires d::primitive_theory(eq,lib),dl::execution(lib,programs,states,labels),dl::well_formed(lib,programs,states.first()),history_typed(lib,states.first().history),
    ensures forall|i:int| 0<=i<states.len() ==> history_typed(lib,states[i].history),
    decreases labels.len(),
{
    if labels.len()>0 {
        let before=states.drop_last();let steps=labels.drop_last();assert(dl::execution(lib,programs,before,steps)) by {
            assert forall|i:int| 0<=i<steps.len() implies dl::step(lib,programs,before[i],before[i+1],steps[i].0,steps[i].1) by {}
        }
        trace_history_typed(eq,lib,programs,before,steps);dl::execution_preservation(eq,lib,programs,states,labels);
        history_typed_step(eq,lib,programs,before.last(),states.last(),labels.last().0,labels.last().1);
        assert forall|i:int| 0<=i<states.len() implies history_typed(lib,states[i].history) by {if i<before.len() {assert(before[i]==states[i]);} else {assert(i==states.len()-1);}}
    }
}
pub proof fn receipt_projection<U>(receipt:gl::Receipt<U>,a:s::State<U>)
    requires inv::well_formed(a),gl::undo(receipt,a).is_some(),
    ensures p::project(gl::undo(receipt,a).unwrap(),ISet::full())==e::apply(receipt_action(receipt),p::project(a,ISet::full())),
{gl::inverse_projects(receipt,a);}
pub proof fn forward_projection<A,X,U,B,I>(lib:dl::Library<A,X,U,B>,node:dl::Node<A,X,U,B,I>,a:s::State<U>,actor:usize)
    requires inv::well_formed(a),dl::run(lib,node,a,actor).is_some(),
    ensures p::project(dl::run(lib,node,a,actor).unwrap().state,ISet::full())==e::apply(forward_action(lib,node),p::project(a,ISet::full())),
{gl::run_projects(dl::stage(lib,node),a,actor);e::mediated_forward_meaning(dl::stage(lib,node),p::project(a,ISet::full()));}
pub proof fn restore_projection<U,I>(history:Seq<dl::Entry<U,I>>,tokens:Seq<nat>,a:s::State<U>,actor:usize)
    requires inv::well_formed(a),dl::restore(history,tokens,a,actor).is_some(),
    ensures p::project(dl::restore(history,tokens,a,actor).unwrap(),ISet::full())==e::restore(word(history,tokens),p::project(a,ISet::full())),
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let receipt=history[tokens.last() as int].landed.receipt;receipt_projection(receipt,a);gl::undo_preservation(receipt,a);
        restore_projection(history,tokens.drop_last(),gl::undo(receipt,a).unwrap(),actor);
        assert(word(history,tokens).drop_last() =~= word(history,tokens.drop_last()));
    }
}
pub open spec fn step_word<A,X,U,B,I>(lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,a:dl::Configuration<U,I>,z:dl::Configuration<U,I>,actor:usize,rule:r::Rule)->Seq<e::Action<U>> {
    if dl::landing(a,z,rule) {seq![forward_action(lib,programs(actor)(a.current[actor].unwrap()))]}
    else if rule==r::Rule::Unload {own_word(a,actor).reverse()} else {Seq::empty()}
}
pub open spec fn event<A,X,U,B,I>(lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,a:dl::Configuration<U,I>,z:dl::Configuration<U,I>,actor:usize,rule:r::Rule,owner:usize)->e::Event<U> {
    e::Event {forward:step_word(lib,programs,a,z,actor,rule),returned:if actor==owner && dl::landing(a,z,rule) {Some(receipt_action(dl::entry(lib,programs,a,actor).landed.receipt))} else {None}}
}
pub proof fn step_projection<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,a:dl::Configuration<U,I>,z:dl::Configuration<U,I>,actor:usize,rule:r::Rule)
    requires d::primitive_theory(eq,lib),dl::well_formed(lib,programs,a),dl::step(lib,programs,a,z,actor,rule),
    ensures p::project(z.state,ISet::full())==e::run(step_word(lib,programs,a,z,actor,rule),p::project(a.state,ISet::full())),
{
    dl::state_preservation(eq,lib,programs,a,z,actor,rule);dl::frame(lib,programs,a,z,actor,rule);
    p::unique_owner(a.state);p::unique_owner(z.state);
    if dl::landing(a,z,rule) {
        let node=programs(actor)(a.current[actor].unwrap());forward_projection(lib,node,a.state,actor);
        gl::run_preservation(dl::stage(lib,node),a.state,actor);let out=dl::entry(lib,programs,a,actor).landed;
        p::unique_owner(out.state);p::lifecycle_edit(out.state,actor,z.state.control.fibers[actor].phase,z.state.control.fibers[actor].committed,z.state.iterators[actor],z.state.accumulators[actor],ISet::full());
        e::run_singleton(forward_action(lib,node),p::project(a.state,ISet::full()));
    } else if rule==r::Rule::Unload {
        restore_projection(a.history,a.state.accumulators[actor],a.state,actor);
        dl::restore_preservation(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);
        let restored=dl::restore(a.history,a.state.accumulators[actor],a.state,actor).unwrap();p::unique_owner(restored);
        p::lifecycle_edit(restored,actor,Phase::Inactive,ISet::empty(),None,Seq::empty(),ISet::full());
        e::reverse_is_restore(own_word(a,actor),p::project(a.state,ISet::full()));
    } else if rule==r::Rule::Insert {p::empty_insertion(a.state,z.state,actor,ISet::full());}
    else {
        assert(p::bindings_equal(a.state,z.state)) by {assert forall|key:Port,n:usize| p::owns(a.state,key,n)==p::owns(z.state,key,n)
            && (p::owns(a.state,key,n) ==> a.state.tables[n][key]==z.state.tables[n][key]) by {}}
        p::projection_equal(a.state,z.state,ISet::full());
    }
}

pub open spec fn installed<U>(a:s::State<U>,owner:usize)->bool {s::registered(a,owner) && a.control.fibers[owner].phase!=Phase::Inactive}
pub open spec fn pinned<U>(a:s::State<U>,owner:usize)->bool {
    forall|b:Binding| a.control.fibers[owner].committed.contains(b) ==> a.control.fibers[b.provider].phase==Phase::Active || a.control.fibers[b.provider].phase==Phase::Unloading
}
pub open spec fn scope<U>(journal:Seq<e::Action<U>>,keys:ISet<Port>)->bool {
    forall|i:int| 0<=i<journal.len() && e::key(#[trigger] journal[i]).is_some() ==> keys.contains(e::key(journal[i]).unwrap())
}
pub proof fn episode_step<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,a:dl::Configuration<U,I>,z:dl::Configuration<U,I>,actor:usize,rule:r::Rule,owner:usize)
    requires d::primitive_theory(eq,lib),dl::well_formed(lib,programs,a),dl::step(lib,programs,a,z,actor,rule),installed(a.state,owner),installed(z.state,owner),
    ensures a.state.control.fibers[owner].committed==z.state.control.fibers[owner].committed,
        dl::declarations(a.state,owner)==dl::declarations(z.state,owner),
        a.state.control.fibers[owner].provisions==z.state.control.fibers[owner].provisions,
        own_word(z,owner)==if actor==owner && dl::landing(a,z,rule) {own_word(a,owner).push(receipt_action(dl::entry(lib,programs,a,actor).landed.receipt))} else {own_word(a,owner)},
        pinned(a.state,owner) ==> pinned(z.state,owner),
{
    dl::frame(lib,programs,a,z,actor,rule);dl::state_preservation(eq,lib,programs,a,z,actor,rule);
    if dl::landing(a,z,rule) {gl::run_preservation(dl::stage(lib,programs(actor)(a.current[actor].unwrap())),a.state,actor);}
    if rule==r::Rule::Unload {dl::restore_preservation(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);}
    if actor==owner {assert(rule!=r::Rule::Begin && rule!=r::Rule::Unload && rule!=r::Rule::Insert && rule!=r::Rule::Remove);}
    assert(a.state.control.fibers[owner].committed==z.state.control.fibers[owner].committed);
    let own=actor==owner && dl::landing(a,z,rule);
    assert(z.state.accumulators[owner]==if own {a.state.accumulators[owner].push(a.history.len())} else {a.state.accumulators[owner]});
    assert(own_word(z,owner) =~= if own {own_word(a,owner).push(receipt_action(dl::entry(lib,programs,a,actor).landed.receipt))} else {own_word(a,owner)}) by {
        assert forall|i:int| 0<=i<own_word(z,owner).len() implies own_word(z,owner)[i]==(if own {own_word(a,owner).push(receipt_action(dl::entry(lib,programs,a,actor).landed.receipt))} else {own_word(a,owner)})[i] by {
            if own && i==a.state.accumulators[owner].len() {assert(z.history[a.history.len() as int]==dl::entry(lib,programs,a,actor));}
            else {let token=a.state.accumulators[owner][i];assert(token<a.history.len());assert(z.history[token as int]==a.history[token as int]);}
        }
    }
    if pinned(a.state,owner) {
        assert forall|b:Binding| z.state.control.fibers[owner].committed.contains(b) implies z.state.control.fibers[b.provider].phase==Phase::Active || z.state.control.fibers[b.provider].phase==Phase::Unloading by {
            assert(a.state.control.fibers[owner].committed.contains(b));assert(s::registered(a.state,b.provider));
            if actor==b.provider {
                assert(owner!=actor);assert(r::relied(a.state.control,actor));assert(rule!=r::Rule::Unload);
                assert(rule==r::Rule::Retire || rule==r::Rule::Leave);
            } else {assert(a.state.control.fibers[b.provider].phase==z.state.control.fibers[b.provider].phase);}
        }
    }
}
pub proof fn begin_pin<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,a:dl::Configuration<U,I>,z:dl::Configuration<U,I>,owner:usize)
    requires d::primitive_theory(eq,lib),dl::well_formed(lib,programs,a),dl::step(lib,programs,a,z,owner,r::Rule::Begin),
    ensures installed(z.state,owner),pinned(z.state,owner),z.state.accumulators[owner].len()==0,
        z.state.tables[owner]==a.state.tables[owner],
{
    dl::state_preservation(eq,lib,programs,a,z,owner,r::Rule::Begin);
    assert forall|b:Binding| z.state.control.fibers[owner].committed.contains(b) implies z.state.control.fibers[b.provider].phase==Phase::Active || z.state.control.fibers[b.provider].phase==Phase::Unloading by {
        assert(s::publishes(a.state,Port {key:b.key,realm:b.realm},b.provider));assert(b.provider!=owner);
    }
}
pub proof fn provision_separated<A,X,U,B,I>(lib:dl::Library<A,X,U,B>,node:dl::Node<A,X,U,B,I>,a:s::State<U>,actor:usize,owner:usize,key:Port,value:U,next:Option<I>)
    requires inv::well_formed(a),installed(a,owner),pinned(a,owner),actor!=owner,a.control.fibers[actor].phase==Phase::Loading,
        node==(d::Node::Provision {key,value,next}),dl::run(lib,node,a,actor).is_some(),
    ensures !dl::declarations(a,owner).contains(key),
{
    assert(a.control.fibers[actor].provisions.contains(key));
    assert(!a.control.fibers[owner].provisions.contains(key));
    if a.control.fibers[owner].dependencies.contains(key) {
        let b=choose|b:Binding| a.control.fibers[owner].committed.contains(b) && b.key==key.key && b.realm==key.realm;
        assert(a.control.fibers[b.provider].provisions.contains(key));assert(b.provider==actor);assert(false);
    }
}
pub proof fn interface_compatible<A,X,U,B>(lib:dl::Library<A,X,U,B>,journal:Seq<e::Action<U>>,foreign:e::Action<U>,keys:ISet<Port>)
    requires independent_keys(lib),e::inverse_journal(journal),scope(journal,keys),
        forall|i:int| 0<=i<journal.len() ==> action_typed(lib,#[trigger] journal[i]),action_typed(lib,foreign),
        match foreign {e::Action::Provision {key,..}=>!keys.contains(key),_=>true},
    ensures e::compatible(journal,foreign),
{
    assert forall|i:int| 0<=i<journal.len() implies e::atom_compatible(#[trigger] journal[i],foreign) by {
        match (journal[i],foreign) {
            (e::Action::Operation {key:k,update:f},e::Action::Operation {key:j,update:g})=>{
                if k==j {assert(generator(lib,k,f));assert(generator(lib,k,g));}
            },
            (_,e::Action::Provision {key,..})=>{if e::key(journal[i]).is_some() {assert(keys.contains(e::key(journal[i]).unwrap()));}},
            _=>{},
        }
    }
}
pub proof fn word_facts<A,X,U,B,I>(lib:dl::Library<A,X,U,B>,a:dl::Configuration<U,I>,owner:usize)
    requires dl::tokens_valid(a),history_typed(lib,a.history),s::registered(a.state,owner),
    ensures e::inverse_journal(own_word(a,owner)),forall|i:int| 0<=i<own_word(a,owner).len() ==> action_typed(lib,#[trigger] own_word(a,owner)[i]),
{
    assert forall|i:int| 0<=i<own_word(a,owner).len() implies e::inverse_action(#[trigger] own_word(a,owner)[i]) && action_typed(lib,own_word(a,owner)[i]) by {
        let token=a.state.accumulators[owner][i];assert(token<a.history.len());
    }
}
pub open spec fn no_provision<U>(actions:Seq<e::Action<U>>,keys:ISet<Port>)->bool {
    forall|i:int| 0<=i<actions.len() ==> match #[trigger] actions[i] {e::Action::Provision {key,..}=>!keys.contains(key),_=>true}
}
pub proof fn foreign_compatible<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,a:dl::Configuration<U,I>,z:dl::Configuration<U,I>,actor:usize,rule:r::Rule,owner:usize)
    requires d::primitive_theory(eq,lib),independent_keys(lib),dl::well_formed(lib,programs,a),history_typed(lib,a.history),dl::step(lib,programs,a,z,actor,rule),
        installed(a.state,owner),installed(z.state,owner),pinned(a.state,owner),scope(own_word(a,owner),dl::declarations(a.state,owner)),
        !(actor==owner && dl::landing(a,z,rule)),
    ensures e::word_compatible(own_word(a,owner),step_word(lib,programs,a,z,actor,rule)),
        no_provision(step_word(lib,programs,a,z,actor,rule),dl::declarations(a.state,owner)),
{
    word_facts(lib,a,owner);dl::frame(lib,programs,a,z,actor,rule);
    if dl::landing(a,z,rule) {
        assert(actor!=owner);let id=a.current[actor].unwrap();let node=programs(actor)(id);
        d::member_unfolding(lib,programs(actor),dl::declarations(a.state,actor),a.state.control.fibers[actor].provisions,id);
        node_actions_typed(lib,node,a.state,actor);
        if let d::Node::Provision {key,value,next}=node {provision_separated(lib,node,a.state,actor,owner,key,value,next);}
        interface_compatible(lib,own_word(a,owner),forward_action(lib,node),dl::declarations(a.state,owner));
    } else if rule==r::Rule::Unload {
        assert(actor!=owner);word_facts(lib,a,actor);
        assert forall|i:int| 0<=i<step_word(lib,programs,a,z,actor,rule).len() implies e::compatible(own_word(a,owner),#[trigger] step_word(lib,programs,a,z,actor,rule)[i]) by {
            let j=own_word(a,actor).len()-1-i;assert(0<=j<own_word(a,actor).len());
            assert(step_word(lib,programs,a,z,actor,rule)[i]==own_word(a,actor)[j]);
            interface_compatible(lib,own_word(a,owner),own_word(a,actor)[j],dl::declarations(a.state,owner));
        }
    }
}

pub open spec fn events<A,X,U,B,I>(lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,states:Seq<dl::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)->Seq<e::Event<U>>
    decreases labels.len(),
{
    if labels.len()==0 {Seq::empty()} else {events(lib,programs,states.drop_last(),labels.drop_last(),owner).push(event(lib,programs,states[labels.len()-1],states[labels.len() as int],labels.last().0,labels.last().1,owner))}
}
pub open spec fn clear_foreign<U>(events:Seq<e::Event<U>>,keys:ISet<Port>)->bool {
    forall|i:int| 0<=i<events.len() && #[trigger] events[i].returned.is_none() ==> no_provision(events[i].forward,keys)
}
/// Actual source execution and one key-local scalar interface derive the
/// complete entangled event invariant, including projected states and the
/// inverse word actually present in the accumulator. No projection/witness/
/// interference diagram or final recovery equation is assumed by the caller.
#[verifier::rlimit(40)]
pub proof fn episode_recovery<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,states:Seq<dl::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires d::primitive_theory(eq,lib),independent_keys(lib),dl::execution(lib,programs,states,labels),dl::well_formed(lib,programs,states.first()),
        history_typed(lib,states.first().history),states.first().state.accumulators[owner].len()==0,pinned(states.first().state,owner),
        forall|i:int| 0<=i<states.len() ==> installed(states[i].state,owner),
    ensures {
        let es=events(lib,programs,states,labels,owner);let initial=p::project(states.first().state,ISet::full());let last=states.last();
        &&& e::admissible_trace(es,initial)
        &&& p::project(last.state,ISet::full())==e::trace_state(es,initial)
        &&& own_word(last,owner)==e::journal(es)
        &&& e::restore(own_word(last,owner),p::project(last.state,ISet::full()))==e::foreign_state(es,initial)
        &&& scope(own_word(last,owner),dl::declarations(last.state,owner))
        &&& dl::declarations(last.state,owner)==dl::declarations(states.first().state,owner)
        &&& last.state.control.fibers[owner].provisions==states.first().state.control.fibers[owner].provisions
        &&& pinned(last.state,owner) && history_typed(lib,last.history)
        &&& clear_foreign(es,dl::declarations(states.first().state,owner))
    },
    decreases labels.len(),
{
    let es=events(lib,programs,states,labels,owner);let initial=p::project(states.first().state,ISet::full());
    dl::execution_preservation(eq,lib,programs,states,labels);
    if labels.len()==0 {
        assert(states.last()==states.first());assert(own_word(states.last(),owner) =~= Seq::empty());
    } else {
        let before=states.drop_last();let steps=labels.drop_last();let a=before.last();let z=states.last();let actor=labels.last().0;let rule=labels.last().1;
        assert(dl::execution(lib,programs,before,steps)) by {assert forall|i:int| 0<=i<steps.len() implies dl::step(lib,programs,before[i],before[i+1],steps[i].0,steps[i].1) by {}}
        assert forall|i:int| 0<=i<before.len() implies installed(before[i].state,owner) by {assert(before[i]==states[i]);}
        episode_recovery(eq,lib,programs,before,steps,owner);
        assert(dl::well_formed(lib,programs,a));assert(installed(a.state,owner));assert(installed(z.state,owner));
        episode_step(eq,lib,programs,a,z,actor,rule,owner);history_typed_step(eq,lib,programs,a,z,actor,rule);step_projection(eq,lib,programs,a,z,actor,rule);
        let prefix=events(lib,programs,before,steps,owner);let last=event(lib,programs,a,z,actor,rule,owner);
        assert(es.drop_last()==prefix);assert(es.last()==last);
        if actor==owner && dl::landing(a,z,rule) {
            let id=a.current[owner].unwrap();let node=programs(owner)(id);let out=dl::entry(lib,programs,a,owner).landed;
            d::member_unfolding(lib,programs(owner),dl::declarations(a.state,owner),a.state.control.fibers[owner].provisions,id);
            dl::run_admissible(eq,lib,node,a.state,owner);node_actions_typed(lib,node,a.state,owner);
            forward_projection(lib,node,a.state,owner);receipt_projection(out.receipt,out.state);e::run_singleton(forward_action(lib,node),p::project(a.state,ISet::full()));
            assert(e::apply(receipt_action(out.receipt),e::run(last.forward,p::project(a.state,ISet::full())))==p::project(a.state,ISet::full()));
            assert(scope(own_word(z,owner),dl::declarations(z.state,owner))) by {
                assert forall|i:int| 0<=i<own_word(z,owner).len() && e::key(#[trigger] own_word(z,owner)[i]).is_some() implies dl::declarations(z.state,owner).contains(e::key(own_word(z,owner)[i]).unwrap()) by {
                    if i<own_word(a,owner).len() {assert(own_word(z,owner)[i]==own_word(a,owner)[i]);} else {assert(i==own_word(a,owner).len());}
                }
            }
        } else {
            foreign_compatible(eq,lib,programs,a,z,actor,rule,owner);
        }
        assert(own_word(z,owner)==e::journal(es));
        assert(e::admissible_trace(es,initial));
        assert(clear_foreign(es,dl::declarations(states.first().state,owner))) by {
            assert forall|i:int| 0<=i<es.len() && #[trigger] es[i].returned.is_none() implies no_provision(es[i].forward,dl::declarations(states.first().state,owner)) by {
                if i<prefix.len() {assert(es[i]==prefix[i]);} else {assert(i==es.len()-1);}
            }
        }
    }
    e::entangled_recovery(es,initial);
}

pub proof fn word_preserves_absence<U>(actions:Seq<e::Action<U>>,keys:ISet<Port>,state:IMap<Port,U>,key:Port)
    requires no_provision(actions,keys),keys.contains(key),!state.dom().contains(key),
    ensures !e::run(actions,state).dom().contains(key),
    decreases actions.len(),
{
    if actions.len()>0 {
        assert(no_provision(actions.drop_last(),keys)) by {assert forall|i:int| 0<=i<actions.drop_last().len() implies match #[trigger] actions.drop_last()[i] {e::Action::Provision {key,..}=>!keys.contains(key),_=>true} by {assert(actions.drop_last()[i]==actions[i]);}}
        word_preserves_absence(actions.drop_last(),keys,state,key);
        match actions.last() {e::Action::Provision {key:other,..}=>{assert(!keys.contains(other));},_=>{}}
    }
}
pub proof fn foreign_preserves_absence<U>(events:Seq<e::Event<U>>,keys:ISet<Port>,initial:IMap<Port,U>,key:Port)
    requires clear_foreign(events,keys),keys.contains(key),!initial.dom().contains(key),
    ensures !e::foreign_state(events,initial).dom().contains(key),
    decreases events.len(),
{
    if events.len()>0 {
        assert(clear_foreign(events.drop_last(),keys)) by {assert forall|i:int| 0<=i<events.drop_last().len() && #[trigger] events.drop_last()[i].returned.is_none() implies no_provision(events.drop_last()[i].forward,keys) by {assert(events.drop_last()[i]==events[i]);}}
        foreign_preserves_absence(events.drop_last(),keys,initial,key);
        if events.last().returned.is_none() {word_preserves_absence(events.last().forward,keys,e::foreign_state(events.drop_last(),initial),key);}
    }
}
/// Corollary 69 for an actual successful Unload. Counterfactual replay stays
/// at the value layer; this does not claim its lifecycle guards are enabled.
pub proof fn terminal_recovery<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,states:Seq<dl::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize,after:dl::Configuration<U,I>)
    requires d::primitive_theory(eq,lib),independent_keys(lib),dl::execution(lib,programs,states,labels),dl::well_formed(lib,programs,states.first()),
        history_typed(lib,states.first().history),states.first().state.accumulators[owner].len()==0,pinned(states.first().state,owner),states.first().state.tables[owner].is_empty(),
        forall|i:int| 0<=i<states.len() ==> installed(states[i].state,owner),
        dl::step(lib,programs,states.last(),after,owner,r::Rule::Unload),
    ensures p::project(after.state,ISet::full())==e::foreign_state(events(lib,programs,states,labels,owner),p::project(states.first().state,ISet::full())),
        after.state.tables[owner].is_empty(),
{
    episode_recovery(eq,lib,programs,states,labels,owner);dl::execution_preservation(eq,lib,programs,states,labels);
    let a=states.last();let initial=p::project(states.first().state,ISet::full());let es=events(lib,programs,states,labels,owner);
    step_projection(eq,lib,programs,a,after,owner,r::Rule::Unload);e::reverse_is_restore(own_word(a,owner),p::project(a.state,ISet::full()));
    dl::state_preservation(eq,lib,programs,a,after,owner,r::Rule::Unload);dl::frame(lib,programs,a,after,owner,r::Rule::Unload);
    dl::restore_preservation(lib,programs,a.history,a.state.accumulators[owner],a.state,owner);
    assert(s::registered(after.state,owner));assert(after.state.control.fibers[owner].provisions==a.state.control.fibers[owner].provisions);
    let keys=dl::declarations(states.first().state,owner);
    assert(after.state.tables[owner].is_empty()) by {
        p::unique_owner(states.first().state);p::unique_owner(after.state);
        assert forall|key:Port| !after.state.tables[owner].dom().contains(key) by {
            if after.state.tables[owner].dom().contains(key) {
                assert(after.state.control.fibers[owner].provisions.contains(key));assert(states.first().state.control.fibers[owner].provisions.contains(key));assert(keys.contains(key));
                assert(!initial.dom().contains(key)) by {
                    if initial.dom().contains(key) {let provider=choose|n:usize|p::owns(states.first().state,key,n);assert(states.first().state.control.fibers[provider].provisions.contains(key));assert(provider==owner);}
                }
                foreign_preserves_absence(es,keys,initial,key);p::lookup(after.state,ISet::full(),key,owner);
            }
        }
    }
}

pub open spec fn provided_journals<U,I>(a:dl::Configuration<U,I>)->bool {
    forall|n:usize,k:Port| s::registered(a.state,n) && a.state.tables[n].dom().contains(k) ==> #[trigger] e::erases(own_word(a,n),k)
}
pub proof fn unchanged_word<U,I>(a:dl::Configuration<U,I>,z:dl::Configuration<U,I>,actor:usize)
    requires dl::tokens_valid(a),s::registered(a.state,actor),a.state.accumulators[actor]==z.state.accumulators[actor],
        a.history.len()<=z.history.len(),forall|i:int| 0<=i<a.history.len() ==> #[trigger] a.history[i]==z.history[i],
    ensures own_word(a,actor)==own_word(z,actor),
{
    assert(own_word(a,actor) =~= own_word(z,actor)) by {
        assert forall|i:int| 0<=i<own_word(a,actor).len() implies own_word(a,actor)[i]==own_word(z,actor)[i] by {let token=a.state.accumulators[actor][i];assert(token<a.history.len());assert(a.history[token as int]==z.history[token as int]);}
    }
}
pub proof fn restore_domains<U,I>(history:Seq<dl::Entry<U,I>>,tokens:Seq<nat>,a:s::State<U>,actor:usize)
    requires inv::well_formed(a),dl::restore(history,tokens,a,actor).is_some(),
    ensures dl::restore(history,tokens,a,actor).unwrap().control==a.control,
        forall|n:usize| s::registered(a,n) ==> dl::restore(history,tokens,a,actor).unwrap().tables[n].dom().subset_of(a.tables[n].dom())
            && (n!=actor ==> dl::restore(history,tokens,a,actor).unwrap().tables[n].dom()==a.tables[n].dom()),
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let receipt=history[tokens.last() as int].landed.receipt;let next=gl::undo(receipt,a).unwrap();gl::undo_preservation(receipt,a);
        assert forall|n:usize| s::registered(a,n) implies next.tables[n].dom().subset_of(a.tables[n].dom()) && (n!=actor ==> next.tables[n].dom()==a.tables[n].dom()) by {
            match receipt.inverse {gl::Inverse::Unit=>{},gl::Inverse::Operation {..}=>{},gl::Inverse::Provision {..}=>{}}
        }
        restore_domains(history,tokens.drop_last(),next,actor);
        assert forall|n:usize| s::registered(a,n) implies dl::restore(history,tokens,a,actor).unwrap().tables[n].dom().subset_of(a.tables[n].dom())
            && (n!=actor ==> dl::restore(history,tokens,a,actor).unwrap().tables[n].dom()==a.tables[n].dom()) by {
            assert(s::registered(next,n));
        }
    }
}
pub proof fn restored_owner_empty<U,I>(a:dl::Configuration<U,I>,owner:usize)
    requires inv::well_formed(a.state),s::registered(a.state,owner),provided_journals(a),dl::restore(a.history,a.state.accumulators[owner],a.state,owner).is_some(),
    ensures dl::restore(a.history,a.state.accumulators[owner],a.state,owner).unwrap().tables[owner].is_empty(),
{
    restore_domains(a.history,a.state.accumulators[owner],a.state,owner);restore_projection(a.history,a.state.accumulators[owner],a.state,owner);
    let restored=dl::restore(a.history,a.state.accumulators[owner],a.state,owner).unwrap();
    assert(e::inverse_journal(own_word(a,owner))) by {assert forall|i:int| 0<=i<own_word(a,owner).len() implies e::inverse_action(#[trigger] own_word(a,owner)[i]) by {}}
    assert forall|key:Port| !restored.tables[owner].dom().contains(key) by {
        if restored.tables[owner].dom().contains(key) {
            assert(a.state.tables[owner].dom().contains(key));assert(e::erases(own_word(a,owner),key));
            e::actual_restriction_erases(own_word(a,owner),p::project(a.state,ISet::full()),key);
            assert(p::owns(restored,key,owner));assert(p::project(restored,ISet::full()).dom().contains(key));
        }
    }
}
/// Every own provision has its actual restriction in the live journal. This
/// invariant alone (without commutativity) makes successful Unload empty the
/// owner's table and makes every subsequent Begin start with an empty table.
pub proof fn provided_journals_step<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,a:dl::Configuration<U,I>,z:dl::Configuration<U,I>,actor:usize,rule:r::Rule)
    requires d::primitive_theory(eq,lib),dl::well_formed(lib,programs,a),provided_journals(a),dl::step(lib,programs,a,z,actor,rule),
    ensures provided_journals(z),
{
    dl::frame(lib,programs,a,z,actor,rule);dl::state_preservation(eq,lib,programs,a,z,actor,rule);
    assert(a.history.len()<=z.history.len());assert forall|i:int| 0<=i<a.history.len() implies #[trigger] a.history[i]==z.history[i] by {}
    if dl::landing(a,z,rule) {
        gl::run_preservation(dl::stage(lib,programs(actor)(a.current[actor].unwrap())),a.state,actor);
        episode_step(eq,lib,programs,a,z,actor,rule,actor);
    }
    if rule==r::Rule::Unload {restored_owner_empty(a,actor);restore_domains(a.history,a.state.accumulators[actor],a.state,actor);}
    assert forall|n:usize,k:Port| s::registered(z.state,n) && z.state.tables[n].dom().contains(k) implies #[trigger] e::erases(own_word(z,n),k) by {
        if rule==r::Rule::Insert && n==actor {assert(false);}
        else {
            assert(s::registered(a.state,n));
            if n==actor && dl::landing(a,z,rule) {
                let node=programs(actor)(a.current[actor].unwrap());let receipt=dl::entry(lib,programs,a,actor).landed.receipt;
                if !a.state.tables[n].dom().contains(k) {
                    match node {
                        d::Node::Provision {key,..}=>{assert(key==k);assert(receipt_action(receipt)==(e::Action::Restriction {key:k}));},
                        _=>{assert(false);},
                    }
                    assert(own_word(z,n).last()==(e::Action::Restriction {key:k}));
                } else {
                    assert(e::erases(own_word(a,n),k));let i=choose|i:int| 0<=i<own_word(a,n).len() && own_word(a,n)[i]==(e::Action::Restriction {key:k});
                    assert(own_word(z,n)[i]==(e::Action::Restriction {key:k}));
                }
            } else if n==actor && rule==r::Rule::Unload {assert(false);}
            else if n==actor && rule==r::Rule::Begin {
                assert(a.state.tables[n].dom().contains(k));assert(e::erases(own_word(a,n),k));assert(a.state.accumulators[n].len()==0);assert(own_word(a,n).len()==0);assert(false);
            } else {
                assert(a.state.tables[n].dom().contains(k));assert(a.state.accumulators[n]==z.state.accumulators[n]);
                unchanged_word(a,z,n);
            }
        }
    }
}
pub proof fn trace_provided_journals<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,states:Seq<dl::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires d::primitive_theory(eq,lib),dl::execution(lib,programs,states,labels),dl::well_formed(lib,programs,states.first()),provided_journals(states.first()),
    ensures forall|i:int| 0<=i<states.len() ==> provided_journals(states[i]),
    decreases labels.len(),
{
    if labels.len()>0 {
        let before=states.drop_last();let steps=labels.drop_last();assert(dl::execution(lib,programs,before,steps)) by {assert forall|i:int| 0<=i<steps.len() implies dl::step(lib,programs,before[i],before[i+1],steps[i].0,steps[i].1) by {}}
        trace_provided_journals(eq,lib,programs,before,steps);dl::execution_preservation(eq,lib,programs,states,labels);
        provided_journals_step(eq,lib,programs,before.last(),states.last(),labels.last().0,labels.last().1);
        assert forall|i:int| 0<=i<states.len() implies provided_journals(states[i]) by {if i<before.len() {assert(before[i]==states[i]);} else {assert(i==states.len()-1);}}
    }
}

/// Instantiate the whole-trace invariants only at the actual Begin boundary.
/// Keeping this cut separate avoids carrying three quantified trace invariants
/// through the subsequent segment/recovery calculation.
#[verifier::spinoff_prover]
proof fn actual_begin_facts<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,
    states:Seq<dl::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize,b:int)
    requires d::primitive_theory(eq,lib),dl::execution(lib,programs,states,labels),states.first()==dl::empty::<U,I>(),
        0<b<states.len(),labels[b-1]==(owner,r::Rule::Begin),
    ensures dl::well_formed(lib,programs,states[b]),history_typed(lib,states[b].history),
        pinned(states[b].state,owner),states[b].state.accumulators[owner].len()==0,
        states[b].state.tables[owner].is_empty(),
{
    dl::empty_well_formed(lib,programs);
    assert(dl::well_formed(lib,programs,states.first()));
    dl::execution_preservation(eq,lib,programs,states,labels);
    assert(history_typed(lib,states.first().history));
    assert(provided_journals(states.first()));
    trace_history_typed(eq,lib,programs,states,labels);
    trace_provided_journals(eq,lib,programs,states,labels);
    let before=states[b-1];let after=states[b];
    assert(dl::well_formed(lib,programs,before));
    assert(dl::well_formed(lib,programs,after));
    assert(history_typed(lib,after.history));
    assert(provided_journals(before));
    assert(0<=b-1<labels.len());
    assert(dl::step(lib,programs,before,after,owner,r::Rule::Begin));
    begin_pin(eq,lib,programs,before,after,owner);
    assert(before.state.control.fibers[owner].phase==Phase::Inactive);
    assert(before.state.accumulators[owner].len()==0);
    assert(own_word(before,owner).len()==0);
    assert(before.state.tables[owner].is_empty()) by {
        assert forall|k:Port| !#[trigger] before.state.tables[owner].dom().contains(k) by {
            if before.state.tables[owner].dom().contains(k) {
                assert(e::erases(own_word(before,owner),k));
                assert(!own_word(before,owner).contains(e::Action::Restriction {key:k}));
            }
        }
    }
    assert(after.state.tables[owner]==before.state.tables[owner]);
}

/// Derive the episode hypotheses from a concrete Begin in a whole trace from
/// the empty registry. No invented past receipt, projection equation, or
/// end-state recovery assertion appears among the inputs.
#[verifier::spinoff_prover]
pub proof fn actual_episode_recovery<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,states:Seq<dl::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize,b:int,u:int)
    requires d::primitive_theory(eq,lib),independent_keys(lib),dl::execution(lib,programs,states,labels),states.first()==dl::empty::<U,I>(),
        0<b<=u<states.len(),labels[b-1]==(owner,r::Rule::Begin),forall|i:int| b<=i<=u ==> installed(states[i].state,owner),
    ensures {
        let segment=states.subrange(b,u+1);let steps=labels.subrange(b,u);let es=events(lib,programs,segment,steps,owner);
        &&& e::admissible_trace(es,p::project(states[b].state,ISet::full()))
        &&& own_word(states[u],owner)==e::journal(es)
        &&& e::restore(own_word(states[u],owner),p::project(states[u].state,ISet::full()))==e::foreign_state(es,p::project(states[b].state,ISet::full()))
        &&& states[b].state.tables[owner].is_empty()
    },
{
    actual_begin_facts(eq,lib,programs,states,labels,owner,b);
    let segment=states.subrange(b,u+1);let steps=labels.subrange(b,u);
    assert(segment.len()==u-b+1);
    assert(steps.len()==u-b);
    assert(segment.first()==states[b]);
    assert(segment.last()==states[u]);
    assert(dl::execution(lib,programs,segment,steps)) by {
        assert forall|i:int| 0<=i<steps.len() implies dl::step(lib,programs,segment[i],segment[i+1],steps[i].0,steps[i].1) by {
            assert(0<=b+i<labels.len());
            assert(segment[i]==states[b+i]);
            assert(segment[i+1]==states[b+i+1]);
            assert(steps[i]==labels[b+i]);
            assert(dl::step(lib,programs,states[b+i],states[b+i+1],labels[b+i].0,labels[b+i].1));
        }
    }
    assert forall|i:int| 0<=i<segment.len() implies installed(segment[i].state,owner) by {
        assert(b<=b+i<=u);
        assert(segment[i]==states[b+i]);
        assert(installed(states[b+i].state,owner));
    }
    episode_recovery(eq,lib,programs,segment,steps,owner);
}
/// The actual terminal Unload recovers the foreign value replay and empties
/// the table, all derived from the original empty-origin execution.
pub proof fn actual_terminal_recovery<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,states:Seq<dl::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize,b:int,u:int)
    requires d::primitive_theory(eq,lib),independent_keys(lib),dl::execution(lib,programs,states,labels),states.first()==dl::empty::<U,I>(),
        0<b<=u<labels.len(),labels[b-1]==(owner,r::Rule::Begin),labels[u]==(owner,r::Rule::Unload),forall|i:int| b<=i<=u ==> installed(states[i].state,owner),
    ensures states[u+1].state.tables[owner].is_empty(),
        p::project(states[u+1].state,ISet::full())==e::foreign_state(events(lib,programs,states.subrange(b,u+1),labels.subrange(b,u),owner),p::project(states[b].state,ISet::full())),
{
    actual_episode_recovery(eq,lib,programs,states,labels,owner,b,u);
    dl::empty_well_formed(lib,programs);dl::execution_preservation(eq,lib,programs,states,labels);
    step_projection(eq,lib,programs,states[u],states[u+1],owner,r::Rule::Unload);
    e::reverse_is_restore(own_word(states[u],owner),p::project(states[u].state,ISet::full()));
    assert(provided_journals(states.first()));trace_provided_journals(eq,lib,programs,states,labels);restored_owner_empty(states[u],owner);
}
}
