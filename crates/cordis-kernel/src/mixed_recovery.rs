//! Recovery of all-table observations for the actual mixed grammar.
//!
//! Table receipts retain the exact returned inverse. Child receipts denote the
//! identity value action because insertion is empty and retirement preserves
//! tables. Counterfactual replay remains a value calculation, not a lifecycle
//! trace. Scalar interference uses `grammar_recovery::independent_keys`.
#[cfg(verus_keep_ghost)]
use crate::grammar_recovery::{
    action_typed, clear_foreign, independent_keys, installed, interface_compatible, no_provision,
    pinned, scope,
};
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_grammar as d, dependent_lift as dep, entangled as e, grammar_lift as gl,
    grammar_recovery as gr, mixed_grammar as mx, mixed_syntax as syntax, preservation as inv,
    projection as p, refinement as r, semantics as s, Binding, Phase, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn receipt_action<U>(receipt:mx::Receipt<U>)->e::Action<U> {
    match receipt {mx::Receipt::Table {receipt}=>gr::receipt_action(receipt),mx::Receipt::Child {..}=>e::Action::Identity}
}
pub open spec fn forward_action<A,X,U,B,I>(lib:mx::Library<A,X,U,B>,node:mx::Node<A,X,U,B,I>)->e::Action<U> {
    match node {syntax::Node::Dependent {node}=>gr::forward_action(lib,node),syntax::Node::Child {..}=>e::Action::Identity}
}
pub open spec fn history_typed<A,X,U,B,I>(lib:mx::Library<A,X,U,B>,history:Seq<mx::Entry<U,I>>)->bool {
    forall|i:int| 0<=i<history.len() ==> action_typed(lib,receipt_action(#[trigger] history[i].landed.receipt))
}

pub open spec fn word<U,I>(history:Seq<mx::Entry<U,I>>,tokens:Seq<nat>)->Seq<e::Action<U>> {
    Seq::new(tokens.len(),|i:int|receipt_action(history[tokens[i] as int].landed.receipt))
}

pub open spec fn own_word<U,I>(a:mx::Configuration<U,I>,actor:usize)->Seq<e::Action<U>> {word(a.history,a.state.accumulators[actor])}

pub proof fn node_actions_typed<A,X,U,B,I>(lib:mx::Library<A,X,U,B>,node:mx::Node<A,X,U,B,I>,a:s::State<U>,actor:usize)
    requires syntax::permitted(lib,dep::declarations(a,actor),a.control.fibers[actor].provisions,node),mx::run(lib,node,a,actor).is_some(),
    ensures action_typed(lib,forward_action(lib,node)),action_typed(lib,receipt_action(mx::run(lib,node,a,actor).unwrap().receipt)),
        e::inverse_action(receipt_action(mx::run(lib,node,a,actor).unwrap().receipt)),
        e::key(receipt_action(mx::run(lib,node,a,actor).unwrap().receipt)).is_some() ==>
            dep::declarations(a,actor).contains(e::key(receipt_action(mx::run(lib,node,a,actor).unwrap().receipt)).unwrap()),
{
    match node {syntax::Node::Dependent {node}=>{gr::node_actions_typed(lib,node,a,actor);},syntax::Node::Child {..}=>{}}
}

pub proof fn history_typed_step<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize,rule:r::Rule)
    requires d::primitive_theory(eq,lib),mx::well_formed(lib,programs,a),history_typed(lib,a.history),mx::step(lib,programs,a,z,actor,rule),
    ensures history_typed(lib,z.history),
{
    mx::frame(eq,lib,programs,a,z,actor,rule);
    if mx::landing(a,z,rule) {
        let id=a.current[actor].unwrap();syntax::member_unfolding(lib,programs,actor,dep::declarations(a.state,actor),a.state.control.fibers[actor].provisions,id);
        node_actions_typed(lib,programs(actor)(id),a.state,actor);
        assert forall|i:int| 0<=i<z.history.len() implies action_typed(lib,receipt_action(#[trigger] z.history[i].landed.receipt)) by {
            if i<a.history.len() {assert(z.history[i]==a.history[i]);} else {assert(i==a.history.len());assert(z.history[i]==mx::entry(lib,programs,a,actor));}
        }
    }
}

pub proof fn trace_history_typed<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires d::primitive_theory(eq,lib),mx::execution(lib,programs,states,labels),mx::well_formed(lib,programs,states.first()),history_typed(lib,states.first().history),
    ensures forall|i:int| 0<=i<states.len() ==> history_typed(lib,states[i].history),
    decreases labels.len(),
{
    if labels.len()>0 {
        let before=states.drop_last();let steps=labels.drop_last();assert(mx::execution(lib,programs,before,steps)) by {
            assert forall|i:int| 0<=i<steps.len() implies mx::step(lib,programs,before[i],before[i+1],steps[i].0,steps[i].1) by {}
        }
        trace_history_typed(eq,lib,programs,before,steps);mx::execution_preservation(eq,lib,programs,states,labels);
        history_typed_step(eq,lib,programs,before.last(),states.last(),labels.last().0,labels.last().1);
        assert forall|i:int| 0<=i<states.len() implies history_typed(lib,states[i].history) by {if i<before.len() {assert(before[i]==states[i]);} else {assert(i==states.len()-1);}}
    }
}

pub proof fn receipt_projection<U>(receipt:mx::Receipt<U>,a:s::State<U>)
    requires inv::well_formed(a),mx::undo(receipt,a).is_some(),
    ensures inv::well_formed(mx::undo(receipt,a).unwrap()),
        p::project(mx::undo(receipt,a).unwrap(),ISet::full())==e::apply(receipt_action(receipt),p::project(a,ISet::full())),
{
    match receipt {
        mx::Receipt::Table {receipt}=>{gr::receipt_projection(receipt,a);gl::undo_preservation(receipt,a);},
        mx::Receipt::Child {child,..}=>{
            let z=mx::undo(receipt,a).unwrap();inv::retire_preservation(a,z,child);p::unique_owner(a);p::unique_owner(z);
            assert(p::bindings_equal(a,z)) by {assert forall|key:Port,n:usize| p::owns(a,key,n)==p::owns(z,key,n)
                && (p::owns(a,key,n) ==> a.tables[n][key]==z.tables[n][key]) by {}}
            p::projection_equal(a,z,ISet::full());
        }
    }
}

pub proof fn forward_projection<A,X,U,B,I>(lib:mx::Library<A,X,U,B>,node:mx::Node<A,X,U,B,I>,a:s::State<U>,actor:usize)
    requires inv::well_formed(a),mx::run(lib,node,a,actor).is_some(),
    ensures p::project(mx::run(lib,node,a,actor).unwrap().state,ISet::full())==e::apply(forward_action(lib,node),p::project(a,ISet::full())),
{
    match node {
        syntax::Node::Dependent {node}=>{gr::forward_projection(lib,node,a,actor);},
        syntax::Node::Child {child,..}=>{p::unique_owner(a);p::empty_insertion(a,mx::run(lib,node,a,actor).unwrap().state,child,ISet::full());},
    }
}

pub proof fn restore_projection<U,I>(history:Seq<mx::Entry<U,I>>,tokens:Seq<nat>,a:s::State<U>,actor:usize)
    requires inv::well_formed(a),mx::restore(history,tokens,a,actor).is_some(),
    ensures p::project(mx::restore(history,tokens,a,actor).unwrap(),ISet::full())==e::restore(word(history,tokens),p::project(a,ISet::full())),
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let receipt=history[tokens.last() as int].landed.receipt;receipt_projection(receipt,a);
        restore_projection(history,tokens.drop_last(),mx::undo(receipt,a).unwrap(),actor);
        assert(word(history,tokens).drop_last() =~= word(history,tokens.drop_last()));
    }
}

pub open spec fn step_word<A,X,U,B,I>(lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize,rule:r::Rule)->Seq<e::Action<U>> {
    if mx::landing(a,z,rule) {seq![forward_action(lib,programs(actor)(a.current[actor].unwrap()))]}
    else if rule==r::Rule::Unload {own_word(a,actor).reverse()} else {Seq::empty()}
}

pub open spec fn event<A,X,U,B,I>(lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize,rule:r::Rule,owner:usize)->e::Event<U> {
    e::Event {forward:step_word(lib,programs,a,z,actor,rule),returned:if actor==owner && mx::landing(a,z,rule) {Some(receipt_action(mx::entry(lib,programs,a,actor).landed.receipt))} else {None}}
}

pub proof fn step_projection<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize,rule:r::Rule)
    requires d::primitive_theory(eq,lib),mx::well_formed(lib,programs,a),mx::step(lib,programs,a,z,actor,rule),
    ensures p::project(z.state,ISet::full())==e::run(step_word(lib,programs,a,z,actor,rule),p::project(a.state,ISet::full())),
{
    mx::state_preservation(eq,lib,programs,a,z,actor,rule);mx::frame(eq,lib,programs,a,z,actor,rule);
    p::unique_owner(a.state);p::unique_owner(z.state);
    if mx::landing(a,z,rule) {
        let node=programs(actor)(a.current[actor].unwrap());forward_projection(lib,node,a.state,actor);
        mx::run_members(eq,lib,programs,a.state,actor,a.current[actor].unwrap());mx::run_admissible(eq,lib,node,a.state,actor);let out=mx::entry(lib,programs,a,actor).landed;
        p::unique_owner(out.state);p::lifecycle_edit(out.state,actor,z.state.control.fibers[actor].phase,z.state.control.fibers[actor].committed,z.state.iterators[actor],z.state.accumulators[actor],ISet::full());
        e::run_singleton(forward_action(lib,node),p::project(a.state,ISet::full()));
    } else if rule==r::Rule::Unload {
        restore_projection(a.history,a.state.accumulators[actor],a.state,actor);
        mx::restore_preservation(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);
        let restored=mx::restore(a.history,a.state.accumulators[actor],a.state,actor).unwrap();p::unique_owner(restored);
        p::lifecycle_edit(restored,actor,Phase::Inactive,ISet::empty(),None,Seq::empty(),ISet::full());
        e::reverse_is_restore(own_word(a,actor),p::project(a.state,ISet::full()));
    } else if rule==r::Rule::Insert {p::empty_insertion(a.state,z.state,actor,ISet::full());}
    else {
        assert(p::bindings_equal(a.state,z.state)) by {assert forall|key:Port,n:usize| p::owns(a.state,key,n)==p::owns(z.state,key,n)
            && (p::owns(a.state,key,n) ==> a.state.tables[n][key]==z.state.tables[n][key]) by {}}
        p::projection_equal(a.state,z.state,ISet::full());
    }
}

pub proof fn episode_step<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize,rule:r::Rule,owner:usize)
    requires d::primitive_theory(eq,lib),mx::well_formed(lib,programs,a),mx::step(lib,programs,a,z,actor,rule),installed(a.state,owner),installed(z.state,owner),
    ensures a.state.control.fibers[owner].committed==z.state.control.fibers[owner].committed,
        dep::declarations(a.state,owner)==dep::declarations(z.state,owner),
        a.state.control.fibers[owner].provisions==z.state.control.fibers[owner].provisions,
        own_word(z,owner)==if actor==owner && mx::landing(a,z,rule) {own_word(a,owner).push(receipt_action(mx::entry(lib,programs,a,actor).landed.receipt))} else {own_word(a,owner)},
        pinned(a.state,owner) ==> pinned(z.state,owner),
{
    mx::frame(eq,lib,programs,a,z,actor,rule);mx::state_preservation(eq,lib,programs,a,z,actor,rule);
    if mx::landing(a,z,rule) {mx::run_members(eq,lib,programs,a.state,actor,a.current[actor].unwrap());mx::run_admissible(eq,lib,programs(actor)(a.current[actor].unwrap()),a.state,actor);}
    if rule==r::Rule::Unload {mx::restore_preservation(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);}
    if actor==owner {assert(rule!=r::Rule::Begin && rule!=r::Rule::Unload && rule!=r::Rule::Insert && rule!=r::Rule::Remove);}
    assert(a.state.control.fibers[owner].committed==z.state.control.fibers[owner].committed);
    let own=actor==owner && mx::landing(a,z,rule);
    assert(z.state.accumulators[owner]==if own {a.state.accumulators[owner].push(a.history.len())} else {a.state.accumulators[owner]});
    assert(own_word(z,owner) =~= if own {own_word(a,owner).push(receipt_action(mx::entry(lib,programs,a,actor).landed.receipt))} else {own_word(a,owner)}) by {
        assert forall|i:int| 0<=i<own_word(z,owner).len() implies own_word(z,owner)[i]==(if own {own_word(a,owner).push(receipt_action(mx::entry(lib,programs,a,actor).landed.receipt))} else {own_word(a,owner)})[i] by {
            if own && i==a.state.accumulators[owner].len() {assert(z.history[a.history.len() as int]==mx::entry(lib,programs,a,actor));}
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

pub proof fn begin_pin<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,owner:usize)
    requires d::primitive_theory(eq,lib),mx::well_formed(lib,programs,a),mx::step(lib,programs,a,z,owner,r::Rule::Begin),
    ensures installed(z.state,owner),pinned(z.state,owner),z.state.accumulators[owner].len()==0,
        z.state.tables[owner]==a.state.tables[owner],
{
    mx::state_preservation(eq,lib,programs,a,z,owner,r::Rule::Begin);
    assert forall|b:Binding| z.state.control.fibers[owner].committed.contains(b) implies z.state.control.fibers[b.provider].phase==Phase::Active || z.state.control.fibers[b.provider].phase==Phase::Unloading by {
        assert(s::publishes(a.state,Port {key:b.key,realm:b.realm},b.provider));assert(b.provider!=owner);
    }
}

pub proof fn word_facts<A,X,U,B,I>(lib:mx::Library<A,X,U,B>,a:mx::Configuration<U,I>,owner:usize)
    requires mx::tokens_valid(a),history_typed(lib,a.history),s::registered(a.state,owner),
    ensures e::inverse_journal(own_word(a,owner)),forall|i:int| 0<=i<own_word(a,owner).len() ==> action_typed(lib,#[trigger] own_word(a,owner)[i]),
{
    assert forall|i:int| 0<=i<own_word(a,owner).len() implies e::inverse_action(#[trigger] own_word(a,owner)[i]) && action_typed(lib,own_word(a,owner)[i]) by {
        let token=a.state.accumulators[owner][i];assert(token<a.history.len());
    }
}

pub proof fn foreign_compatible<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize,rule:r::Rule,owner:usize)
    requires d::primitive_theory(eq,lib),independent_keys(lib),mx::well_formed(lib,programs,a),history_typed(lib,a.history),mx::step(lib,programs,a,z,actor,rule),
        installed(a.state,owner),installed(z.state,owner),pinned(a.state,owner),scope(own_word(a,owner),dep::declarations(a.state,owner)),
        !(actor==owner && mx::landing(a,z,rule)),
    ensures e::word_compatible(own_word(a,owner),step_word(lib,programs,a,z,actor,rule)),
        no_provision(step_word(lib,programs,a,z,actor,rule),dep::declarations(a.state,owner)),
{
    word_facts(lib,a,owner);mx::frame(eq,lib,programs,a,z,actor,rule);
    if mx::landing(a,z,rule) {
        assert(actor!=owner);let id=a.current[actor].unwrap();let node=programs(actor)(id);
        syntax::member_unfolding(lib,programs,actor,dep::declarations(a.state,actor),a.state.control.fibers[actor].provisions,id);
        node_actions_typed(lib,node,a.state,actor);
        if let syntax::Node::Dependent {node:table}=node {if let d::Node::Provision {key,value,next}=table {gr::provision_separated(lib,table,a.state,actor,owner,key,value,next);}}
        interface_compatible(lib,own_word(a,owner),forward_action(lib,node),dep::declarations(a.state,owner));
    } else if rule==r::Rule::Unload {
        assert(actor!=owner);word_facts(lib,a,actor);
        assert forall|i:int| 0<=i<step_word(lib,programs,a,z,actor,rule).len() implies e::compatible(own_word(a,owner),#[trigger] step_word(lib,programs,a,z,actor,rule)[i]) by {
            let j=own_word(a,actor).len()-1-i;assert(0<=j<own_word(a,actor).len());
            assert(step_word(lib,programs,a,z,actor,rule)[i]==own_word(a,actor)[j]);
            interface_compatible(lib,own_word(a,owner),own_word(a,actor)[j],dep::declarations(a.state,owner));
        }
    }
}

pub open spec fn events<A,X,U,B,I>(lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)->Seq<e::Event<U>>
    decreases labels.len(),
{
    if labels.len()==0 {Seq::empty()} else {events(lib,programs,states.drop_last(),labels.drop_last(),owner).push(event(lib,programs,states[labels.len()-1],states[labels.len() as int],labels.last().0,labels.last().1,owner))}
}

/// Local restoration follows from the returned mixed receipt. In the Child
/// branch this is equality of table observations, not equality of registries.
pub proof fn own_landing_witness<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize,rule:r::Rule)
    requires d::primitive_theory(eq,lib),mx::well_formed(lib,programs,a),mx::step(lib,programs,a,z,actor,rule),mx::landing(a,z,rule),
    ensures {
        let action=receipt_action(mx::entry(lib,programs,a,actor).landed.receipt);
        &&& e::inverse_action(action)
        &&& (e::key(action).is_some() ==> dep::declarations(a.state,actor).contains(e::key(action).unwrap()))
        &&& e::apply(action,e::run(step_word(lib,programs,a,z,actor,rule),p::project(a.state,ISet::full())))==p::project(a.state,ISet::full())
    },
{
    mx::frame(eq,lib,programs,a,z,actor,rule);
    let id=a.current[actor].unwrap();let node=programs(actor)(id);let out=mx::entry(lib,programs,a,actor).landed;
    syntax::member_unfolding(lib,programs,actor,dep::declarations(a.state,actor),a.state.control.fibers[actor].provisions,id);
    mx::run_admissible(eq,lib,node,a.state,actor);node_actions_typed(lib,node,a.state,actor);
    forward_projection(lib,node,a.state,actor);receipt_projection(out.receipt,out.state);e::run_singleton(forward_action(lib,node),p::project(a.state,ISet::full()));
}

/// Derive the entangled event contract from actual mixed steps. Foreign
/// retirement is observation-neutral; successful table inverses retain their
/// strict domains and exact captured providers.
#[verifier::rlimit(40)]
pub proof fn episode_recovery<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires d::primitive_theory(eq,lib),independent_keys(lib),mx::execution(lib,programs,states,labels),mx::well_formed(lib,programs,states.first()),
        history_typed(lib,states.first().history),states.first().state.accumulators[owner].len()==0,pinned(states.first().state,owner),
        forall|i:int| 0<=i<states.len() ==> installed(states[i].state,owner),
    ensures {
        let es=events(lib,programs,states,labels,owner);let initial=p::project(states.first().state,ISet::full());let last=states.last();
        &&& mx::well_formed(lib,programs,last)
        &&& e::admissible_trace(es,initial)
        &&& p::project(last.state,ISet::full())==e::trace_state(es,initial)
        &&& own_word(last,owner)==e::journal(es)
        &&& e::restore(own_word(last,owner),p::project(last.state,ISet::full()))==e::foreign_state(es,initial)
        &&& scope(own_word(last,owner),dep::declarations(last.state,owner))
        &&& dep::declarations(last.state,owner)==dep::declarations(states.first().state,owner)
        &&& last.state.control.fibers[owner].provisions==states.first().state.control.fibers[owner].provisions
        &&& pinned(last.state,owner) && history_typed(lib,last.history)
        &&& clear_foreign(es,dep::declarations(states.first().state,owner))
    },
    decreases labels.len(),
{
    let es=events(lib,programs,states,labels,owner);let initial=p::project(states.first().state,ISet::full());
    if labels.len()==0 {
        assert(states.last()==states.first());assert(own_word(states.last(),owner) =~= Seq::empty());
    } else {
        let before=states.drop_last();let steps=labels.drop_last();let a=before.last();let z=states.last();let actor=labels.last().0;let rule=labels.last().1;
        assert(mx::execution(lib,programs,before,steps)) by {assert forall|i:int| 0<=i<steps.len() implies mx::step(lib,programs,before[i],before[i+1],steps[i].0,steps[i].1) by {}}
        assert forall|i:int| 0<=i<before.len() implies installed(before[i].state,owner) by {assert(before[i]==states[i]);}
        episode_recovery(eq,lib,programs,before,steps,owner);
        mx::configuration_preservation(eq,lib,programs,a,z,actor,rule);
        assert(mx::well_formed(lib,programs,a));assert(installed(a.state,owner));assert(installed(z.state,owner));
        episode_step(eq,lib,programs,a,z,actor,rule,owner);history_typed_step(eq,lib,programs,a,z,actor,rule);step_projection(eq,lib,programs,a,z,actor,rule);
        let prefix=events(lib,programs,before,steps,owner);let last=event(lib,programs,a,z,actor,rule,owner);
        assert(es.drop_last()==prefix);assert(es.last()==last);
        if actor==owner && mx::landing(a,z,rule) {
            own_landing_witness(eq,lib,programs,a,z,owner,rule);
            assert(scope(own_word(z,owner),dep::declarations(z.state,owner))) by {
                assert forall|i:int| 0<=i<own_word(z,owner).len() && e::key(#[trigger] own_word(z,owner)[i]).is_some() implies dep::declarations(z.state,owner).contains(e::key(own_word(z,owner)[i]).unwrap()) by {
                    if i<own_word(a,owner).len() {assert(own_word(z,owner)[i]==own_word(a,owner)[i]);} else {assert(i==own_word(a,owner).len());}
                }
            }
        } else {
            foreign_compatible(eq,lib,programs,a,z,actor,rule,owner);
        }
        assert(own_word(z,owner)==e::journal(es));
        assert(e::admissible_trace(es,initial));
        assert(clear_foreign(es,dep::declarations(states.first().state,owner))) by {
            assert forall|i:int| 0<=i<es.len() && #[trigger] es[i].returned.is_none() implies no_provision(es[i].forward,dep::declarations(states.first().state,owner)) by {
                if i<prefix.len() {assert(es[i]==prefix[i]);} else {assert(i==es.len()-1);}
            }
        }
    }
    e::entangled_recovery(es,initial);
}

pub open spec fn provided_journals<U,I>(a:mx::Configuration<U,I>)->bool {
    forall|n:usize,k:Port| s::registered(a.state,n) && a.state.tables[n].dom().contains(k) ==> #[trigger] e::erases(own_word(a,n),k)
}

pub proof fn unchanged_word<U,I>(a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize)
    requires mx::tokens_valid(a),s::registered(a.state,actor),a.state.accumulators[actor]==z.state.accumulators[actor],
        a.history.len()<=z.history.len(),forall|i:int| 0<=i<a.history.len() ==> #[trigger] a.history[i]==z.history[i],
    ensures own_word(a,actor)==own_word(z,actor),
{
    assert(own_word(a,actor) =~= own_word(z,actor)) by {
        assert forall|i:int| 0<=i<own_word(a,actor).len() implies own_word(a,actor)[i]==own_word(z,actor)[i] by {let token=a.state.accumulators[actor][i];assert(token<a.history.len());assert(a.history[token as int]==z.history[token as int]);}
    }
}

pub proof fn restore_domains<U,I>(history:Seq<mx::Entry<U,I>>,tokens:Seq<nat>,a:s::State<U>,actor:usize)
    requires inv::well_formed(a),mx::restore(history,tokens,a,actor).is_some(),
    ensures mx::restore(history,tokens,a,actor).unwrap().control.fibers.dom()==a.control.fibers.dom(),
        forall|n:usize| s::registered(a,n) ==> mx::restore(history,tokens,a,actor).unwrap().tables[n].dom().subset_of(a.tables[n].dom())
            && (n!=actor ==> mx::restore(history,tokens,a,actor).unwrap().tables[n].dom()==a.tables[n].dom()),
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let receipt=history[tokens.last() as int].landed.receipt;let next=mx::undo(receipt,a).unwrap();receipt_projection(receipt,a);
        assert forall|n:usize| s::registered(a,n) implies next.tables[n].dom().subset_of(a.tables[n].dom()) && (n!=actor ==> next.tables[n].dom()==a.tables[n].dom()) by {
            match receipt {mx::Receipt::Table {receipt}=>{match receipt.inverse {gl::Inverse::Unit=>{},gl::Inverse::Operation {..}=>{},gl::Inverse::Provision {..}=>{}}},mx::Receipt::Child {..}=>{}}
        }
        restore_domains(history,tokens.drop_last(),next,actor);
        assert forall|n:usize| s::registered(a,n) implies mx::restore(history,tokens,a,actor).unwrap().tables[n].dom().subset_of(a.tables[n].dom())
            && (n!=actor ==> mx::restore(history,tokens,a,actor).unwrap().tables[n].dom()==a.tables[n].dom()) by {
            assert(s::registered(next,n));
        }
    }
}

pub proof fn restored_owner_empty<U,I>(a:mx::Configuration<U,I>,owner:usize)
    requires inv::well_formed(a.state),s::registered(a.state,owner),provided_journals(a),mx::restore(a.history,a.state.accumulators[owner],a.state,owner).is_some(),
    ensures mx::restore(a.history,a.state.accumulators[owner],a.state,owner).unwrap().tables[owner].is_empty(),
{
    restore_domains(a.history,a.state.accumulators[owner],a.state,owner);restore_projection(a.history,a.state.accumulators[owner],a.state,owner);
    let restored=mx::restore(a.history,a.state.accumulators[owner],a.state,owner).unwrap();
    assert(e::inverse_journal(own_word(a,owner))) by {assert forall|i:int| 0<=i<own_word(a,owner).len() implies e::inverse_action(#[trigger] own_word(a,owner)[i]) by {}}
    assert forall|key:Port| !restored.tables[owner].dom().contains(key) by {
        if restored.tables[owner].dom().contains(key) {
            assert(a.state.tables[owner].dom().contains(key));assert(e::erases(own_word(a,owner),key));
            e::actual_restriction_erases(own_word(a,owner),p::project(a.state,ISet::full()),key);
            assert(p::owns(restored,key,owner));assert(p::project(restored,ISet::full()).dom().contains(key));
        }
    }
}

pub proof fn provided_journals_step<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize,rule:r::Rule)
    requires d::primitive_theory(eq,lib),mx::well_formed(lib,programs,a),provided_journals(a),mx::step(lib,programs,a,z,actor,rule),
    ensures provided_journals(z),
{
    mx::frame(eq,lib,programs,a,z,actor,rule);mx::state_preservation(eq,lib,programs,a,z,actor,rule);
    assert(a.history.len()<=z.history.len());assert forall|i:int| 0<=i<a.history.len() implies #[trigger] a.history[i]==z.history[i] by {}
    if mx::landing(a,z,rule) {
        mx::run_members(eq,lib,programs,a.state,actor,a.current[actor].unwrap());mx::run_admissible(eq,lib,programs(actor)(a.current[actor].unwrap()),a.state,actor);
        episode_step(eq,lib,programs,a,z,actor,rule,actor);
    }
    if rule==r::Rule::Unload {restored_owner_empty(a,actor);restore_domains(a.history,a.state.accumulators[actor],a.state,actor);}
    assert forall|n:usize,k:Port| s::registered(z.state,n) && z.state.tables[n].dom().contains(k) implies #[trigger] e::erases(own_word(z,n),k) by {
        if !s::registered(a.state,n) {
            if mx::landing(a,z,rule) {let out=mx::entry(lib,programs,a,actor).landed;assert(out.spawn.unwrap().0==n);assert(z.state.tables[n].is_empty());}
            assert(false);
        }
        else {
            assert(s::registered(a.state,n));
            if n==actor && mx::landing(a,z,rule) {
                let node=programs(actor)(a.current[actor].unwrap());let receipt=mx::entry(lib,programs,a,actor).landed.receipt;
                if !a.state.tables[n].dom().contains(k) {
                    match node {
                        syntax::Node::Dependent {node:d::Node::Provision {key,..}}=>{assert(key==k);assert(receipt_action(receipt)==(e::Action::Restriction {key:k}));},
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

pub proof fn trace_provided_journals<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires d::primitive_theory(eq,lib),mx::execution(lib,programs,states,labels),mx::well_formed(lib,programs,states.first()),provided_journals(states.first()),
    ensures forall|i:int| 0<=i<states.len() ==> provided_journals(states[i]),
    decreases labels.len(),
{
    if labels.len()>0 {
        let before=states.drop_last();let steps=labels.drop_last();assert(mx::execution(lib,programs,before,steps)) by {assert forall|i:int| 0<=i<steps.len() implies mx::step(lib,programs,before[i],before[i+1],steps[i].0,steps[i].1) by {}}
        trace_provided_journals(eq,lib,programs,before,steps);mx::execution_preservation(eq,lib,programs,states,labels);
        provided_journals_step(eq,lib,programs,before.last(),states.last(),labels.last().0,labels.last().1);
        assert forall|i:int| 0<=i<states.len() implies provided_journals(states[i]) by {if i<before.len() {assert(before[i]==states[i]);} else {assert(i==states.len()-1);}}
    }
}

/// Select an episode from an empty-origin execution. All receipt provenance,
/// provider pinning, initial emptiness and action typing follow from that
/// execution; the caller supplies only the primitive scalar interface.
#[verifier::rlimit(100)]
pub proof fn actual_episode_recovery<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize,b:int,u:int)
    requires d::primitive_theory(eq,lib),independent_keys(lib),mx::execution(lib,programs,states,labels),states.first()==mx::empty::<U,I>(),
        0<b<=u<states.len(),labels[b-1]==(owner,r::Rule::Begin),forall|i:int| b<=i<=u ==> installed(states[i].state,owner),
    ensures {
        let segment=states.subrange(b,u+1);let steps=labels.subrange(b,u);let es=events(lib,programs,segment,steps,owner);
        &&& e::admissible_trace(es,p::project(states[b].state,ISet::full()))
        &&& own_word(states[u],owner)==e::journal(es)
        &&& e::restore(own_word(states[u],owner),p::project(states[u].state,ISet::full()))==e::foreign_state(es,p::project(states[b].state,ISet::full()))
        &&& states[b].state.tables[owner].is_empty()
    },
{
    mx::empty_well_formed(lib,programs);mx::execution_preservation(eq,lib,programs,states,labels);
    assert(history_typed(lib,states.first().history));assert(provided_journals(states.first()));
    trace_history_typed(eq,lib,programs,states,labels);trace_provided_journals(eq,lib,programs,states,labels);
    begin_pin(eq,lib,programs,states[b-1],states[b],owner);
    assert(states[b-1].state.control.fibers[owner].phase==Phase::Inactive);
    assert(states[b-1].state.accumulators[owner].len()==0);
    assert(states[b-1].state.tables[owner].is_empty()) by {
        assert forall|k:Port| !#[trigger] states[b-1].state.tables[owner].dom().contains(k) by {
            if states[b-1].state.tables[owner].dom().contains(k) {assert(e::erases(own_word(states[b-1],owner),k));assert(own_word(states[b-1],owner).len()==0);}
        }
    }
    let segment=states.subrange(b,u+1);let steps=labels.subrange(b,u);
    assert(mx::execution(lib,programs,segment,steps)) by {assert forall|i:int| 0<=i<steps.len() implies mx::step(lib,programs,segment[i],segment[i+1],steps[i].0,steps[i].1) by {assert(segment[i]==states[b+i]);assert(segment[i+1]==states[b+i+1]);assert(steps[i]==labels[b+i]);}}
    assert forall|i:int| 0<=i<segment.len() implies installed(segment[i].state,owner) by {assert(segment[i]==states[b+i]);}
    episode_recovery(eq,lib,programs,segment,steps,owner);
}

/// The actual successful Unload recovers the foreign value replay and empties
/// this actor's table. Children can remain registered and retired; this theorem
/// asserts table observation recovery, not full registry equality.
pub proof fn actual_terminal_recovery<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize,b:int,u:int)
    requires d::primitive_theory(eq,lib),independent_keys(lib),mx::execution(lib,programs,states,labels),states.first()==mx::empty::<U,I>(),
        0<b<=u<labels.len(),labels[b-1]==(owner,r::Rule::Begin),labels[u]==(owner,r::Rule::Unload),forall|i:int| b<=i<=u ==> installed(states[i].state,owner),
    ensures states[u+1].state.tables[owner].is_empty(),
        p::project(states[u+1].state,ISet::full())==e::foreign_state(events(lib,programs,states.subrange(b,u+1),labels.subrange(b,u),owner),p::project(states[b].state,ISet::full())),
{
    actual_episode_recovery(eq,lib,programs,states,labels,owner,b,u);
    mx::empty_well_formed(lib,programs);mx::execution_preservation(eq,lib,programs,states,labels);
    step_projection(eq,lib,programs,states[u],states[u+1],owner,r::Rule::Unload);
    e::reverse_is_restore(own_word(states[u],owner),p::project(states[u].state,ISet::full()));
    assert(provided_journals(states.first()));trace_provided_journals(eq,lib,programs,states,labels);restored_owner_empty(states[u],owner);
}

}
