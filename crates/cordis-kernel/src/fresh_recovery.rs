//! Value recovery from authentic Fresh executions and their allocation choices.
//!
//! Reuses the Mixed receipt algebra; only the source-step/event bridge differs.
//! The selected child belongs to this landing, never a rewritten fixed program.
#[cfg(verus_keep_ghost)]
use crate::grammar_recovery::{
    action_typed, clear_foreign, independent_keys, installed, interface_compatible, no_provision,
    pinned, scope,
};
#[cfg(verus_keep_ghost)]
use crate::mixed_recovery::{
    forward_action, forward_projection, history_typed, node_actions_typed, own_word,
    provided_journals, receipt_action, receipt_projection, restore_projection,
    restored_owner_empty, word_facts,
};
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_grammar as d, dependent_lift as dep, entangled as e, fresh_grammar as fg,
    fresh_semantics as fs, grammar_recovery as gr, mixed_grammar as mx, mixed_syntax as syntax,
    observational_grammar as og, preservation as inv, projection as p, provision_coverage as pc,
    refinement as r, semantics as s, Binding, Phase, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn concrete<A,X,U,B,I>(programs:fs::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,actor:usize,choice:Option<usize>)->mx::Node<A,X,U,B,I> {
    fg::instantiate(programs(actor)(a.current[actor].unwrap()),choice).unwrap()
}

proof fn landing_node<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:fs::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,actor:usize,choice:Option<usize>)
    requires d::primitive_theory(eq,lib),fs::well_formed(lib,programs,a),s::registered(a.state,actor),
        a.current[actor].is_some(),fg::run(lib,programs(actor)(a.current[actor].unwrap()),a.state,actor,choice).is_some(),
    ensures syntax::permitted(lib,dep::declarations(a.state,actor),a.state.control.fibers[actor].provisions,concrete(programs,a,actor,choice)),
        mx::run(lib,concrete(programs,a,actor,choice),a.state,actor)==fg::run(lib,programs(actor)(a.current[actor].unwrap()),a.state,actor,choice),
{
    og::exact_theory(eq,lib);
    fs::run_members(eq,lib,programs,a.state,actor,a.current[actor].unwrap(),choice);
    match programs(actor)(a.current[actor].unwrap()) {fg::Node::Dependent {..}=>{},fg::Node::FreshChild {..}=>{}}
}

pub proof fn history_typed_step<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize,rule:r::Rule,choice:Option<usize>)
    requires d::primitive_theory(eq,lib),fs::well_formed(lib,programs,a),history_typed(lib,a.history),fs::step(lib,programs,a,z,actor,rule,choice),
    ensures history_typed(lib,z.history),
{
    og::exact_theory(eq,lib);
    fs::frame(eq,lib,programs,a,z,actor,rule,choice);
    if mx::landing(a,z,rule) {
        let id=a.current[actor].unwrap();landing_node(eq,lib,programs,a,actor,choice);
        node_actions_typed(lib,concrete(programs,a,actor,choice),a.state,actor);
        assert forall|i:int| 0<=i<z.history.len() implies action_typed(lib,receipt_action(#[trigger] z.history[i].landed.receipt)) by {
            if i<a.history.len() {assert(z.history[i]==a.history[i]);} else {assert(i==a.history.len());assert(z.history[i]==fs::entry(lib,programs,a,actor,choice));}
        }
    }
}

pub proof fn trace_history_typed<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<fs::Label>)
    requires d::primitive_theory(eq,lib),fs::execution(lib,programs,states,labels),fs::well_formed(lib,programs,states.first()),history_typed(lib,states.first().history),
    ensures forall|i:int| 0<=i<states.len() ==> history_typed(lib,states[i].history),
    decreases labels.len(),
{
    og::exact_theory(eq,lib);
    if labels.len()>0 {
        let before=states.drop_last();let steps=labels.drop_last();assert(fs::execution(lib,programs,before,steps)) by {
            assert forall|i:int| 0<=i<steps.len() implies fs::step(lib,programs,before[i],before[i+1],steps[i].0,steps[i].1,steps[i].2) by {}
        }
        trace_history_typed(eq,lib,programs,before,steps);fs::execution_preservation(eq,lib,programs,states,labels);
        history_typed_step(eq,lib,programs,before.last(),states.last(),labels.last().0,labels.last().1,labels.last().2);
        assert forall|i:int| 0<=i<states.len() implies history_typed(lib,states[i].history) by {if i<before.len() {assert(before[i]==states[i]);} else {assert(i==states.len()-1);}}
    }
}


pub open spec fn step_word<A,X,U,B,I>(lib:mx::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize,rule:r::Rule,choice:Option<usize>)->Seq<e::Action<U>> {
    if mx::landing(a,z,rule) {seq![forward_action(lib,concrete(programs,a,actor,choice))]}
    else if rule==r::Rule::Unload {own_word(a,actor).reverse()} else {Seq::empty()}
}

pub open spec fn event<A,X,U,B,I>(lib:mx::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize,rule:r::Rule,choice:Option<usize>,owner:usize)->e::Event<U> {
    e::Event {forward:step_word(lib,programs,a,z,actor,rule,choice),returned:if actor==owner && mx::landing(a,z,rule) {Some(receipt_action(fs::entry(lib,programs,a,actor,choice).landed.receipt))} else {None}}
}

pub proof fn step_projection<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize,rule:r::Rule,choice:Option<usize>)
    requires d::primitive_theory(eq,lib),fs::well_formed(lib,programs,a),fs::step(lib,programs,a,z,actor,rule,choice),
    ensures p::project(z.state,ISet::full())==e::run(step_word(lib,programs,a,z,actor,rule,choice),p::project(a.state,ISet::full())),
{
    og::exact_theory(eq,lib);
    fs::state_preservation(eq,lib,programs,a,z,actor,rule,choice);fs::frame(eq,lib,programs,a,z,actor,rule,choice);
    p::unique_owner(a.state);p::unique_owner(z.state);
    if mx::landing(a,z,rule) {
        let node=concrete(programs,a,actor,choice);forward_projection(lib,node,a.state,actor);
        landing_node(eq,lib,programs,a,actor,choice);mx::run_admissible(eq,lib,node,a.state,actor);let out=fs::entry(lib,programs,a,actor,choice).landed;
        p::unique_owner(out.state);p::lifecycle_edit(out.state,actor,z.state.control.fibers[actor].phase,z.state.control.fibers[actor].committed,z.state.iterators[actor],z.state.accumulators[actor],ISet::full());
        e::run_singleton(forward_action(lib,node),p::project(a.state,ISet::full()));
    } else if rule==r::Rule::Unload {
        restore_projection(a.history,a.state.accumulators[actor],a.state,actor);
        fs::restore_preservation(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);
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

pub proof fn episode_step<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize,rule:r::Rule,choice:Option<usize>,owner:usize)
    requires d::primitive_theory(eq,lib),fs::well_formed(lib,programs,a),fs::step(lib,programs,a,z,actor,rule,choice),installed(a.state,owner),installed(z.state,owner),
    ensures a.state.control.fibers[owner].committed==z.state.control.fibers[owner].committed,
        dep::declarations(a.state,owner)==dep::declarations(z.state,owner),
        a.state.control.fibers[owner].provisions==z.state.control.fibers[owner].provisions,
        own_word(z,owner)==if actor==owner && mx::landing(a,z,rule) {own_word(a,owner).push(receipt_action(fs::entry(lib,programs,a,actor,choice).landed.receipt))} else {own_word(a,owner)},
        pinned(a.state,owner) ==> pinned(z.state,owner),
{
    og::exact_theory(eq,lib);
    fs::frame(eq,lib,programs,a,z,actor,rule,choice);fs::state_preservation(eq,lib,programs,a,z,actor,rule,choice);
    if mx::landing(a,z,rule) {landing_node(eq,lib,programs,a,actor,choice);mx::run_admissible(eq,lib,concrete(programs,a,actor,choice),a.state,actor);}
    if rule==r::Rule::Unload {fs::restore_preservation(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);}
    if actor==owner {assert(rule!=r::Rule::Begin && rule!=r::Rule::Unload && rule!=r::Rule::Insert && rule!=r::Rule::Remove);}
    assert(a.state.control.fibers[owner].committed==z.state.control.fibers[owner].committed);
    let own=actor==owner && mx::landing(a,z,rule);
    assert(z.state.accumulators[owner]==if own {a.state.accumulators[owner].push(a.history.len())} else {a.state.accumulators[owner]});
    assert(own_word(z,owner) =~= if own {own_word(a,owner).push(receipt_action(fs::entry(lib,programs,a,actor,choice).landed.receipt))} else {own_word(a,owner)}) by {
        assert forall|i:int| 0<=i<own_word(z,owner).len() implies own_word(z,owner)[i]==(if own {own_word(a,owner).push(receipt_action(fs::entry(lib,programs,a,actor,choice).landed.receipt))} else {own_word(a,owner)})[i] by {
            if own && i==a.state.accumulators[owner].len() {assert(z.history[a.history.len() as int]==fs::entry(lib,programs,a,actor,choice));}
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

pub proof fn begin_pin<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,owner:usize)
    requires d::primitive_theory(eq,lib),fs::well_formed(lib,programs,a),fs::step(lib,programs,a,z,owner,r::Rule::Begin,None),
    ensures installed(z.state,owner),pinned(z.state,owner),z.state.accumulators[owner].len()==0,
        z.state.tables[owner]==a.state.tables[owner],
{
    og::exact_theory(eq,lib);
    fs::state_preservation(eq,lib,programs,a,z,owner,r::Rule::Begin,None);
    assert forall|b:Binding| z.state.control.fibers[owner].committed.contains(b) implies z.state.control.fibers[b.provider].phase==Phase::Active || z.state.control.fibers[b.provider].phase==Phase::Unloading by {
        assert(s::publishes(a.state,Port {key:b.key,realm:b.realm},b.provider));assert(b.provider!=owner);
    }
}


pub proof fn foreign_compatible<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize,rule:r::Rule,choice:Option<usize>,owner:usize)
    requires d::primitive_theory(eq,lib),independent_keys(lib),fs::well_formed(lib,programs,a),history_typed(lib,a.history),fs::step(lib,programs,a,z,actor,rule,choice),
        installed(a.state,owner),installed(z.state,owner),pinned(a.state,owner),scope(own_word(a,owner),dep::declarations(a.state,owner)),
        !(actor==owner && mx::landing(a,z,rule)),
    ensures e::word_compatible(own_word(a,owner),step_word(lib,programs,a,z,actor,rule,choice)),
        no_provision(step_word(lib,programs,a,z,actor,rule,choice),dep::declarations(a.state,owner)),
{
    og::exact_theory(eq,lib);
    word_facts(lib,a,owner);fs::frame(eq,lib,programs,a,z,actor,rule,choice);
    if mx::landing(a,z,rule) {
        assert(actor!=owner);let id=a.current[actor].unwrap();let node=concrete(programs,a,actor,choice);
        landing_node(eq,lib,programs,a,actor,choice);
        node_actions_typed(lib,node,a.state,actor);
        if let syntax::Node::Dependent {node:table}=node {if let d::Node::Provision {key,value,next}=table {gr::provision_separated(lib,table,a.state,actor,owner,key,value,next);}}
        interface_compatible(lib,own_word(a,owner),forward_action(lib,node),dep::declarations(a.state,owner));
    } else if rule==r::Rule::Unload {
        assert(actor!=owner);word_facts(lib,a,actor);
        assert forall|i:int| 0<=i<step_word(lib,programs,a,z,actor,rule,choice).len() implies e::compatible(own_word(a,owner),#[trigger] step_word(lib,programs,a,z,actor,rule,choice)[i]) by {
            let j=own_word(a,actor).len()-1-i;assert(0<=j<own_word(a,actor).len());
            assert(step_word(lib,programs,a,z,actor,rule,choice)[i]==own_word(a,actor)[j]);
            interface_compatible(lib,own_word(a,owner),own_word(a,actor)[j],dep::declarations(a.state,owner));
        }
    }
}

pub open spec fn events<A,X,U,B,I>(lib:mx::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<fs::Label>,owner:usize)->Seq<e::Event<U>>
    decreases labels.len(),
{
    if labels.len()==0 {Seq::empty()} else {events(lib,programs,states.drop_last(),labels.drop_last(),owner).push(event(lib,programs,states[labels.len()-1],states[labels.len() as int],labels.last().0,labels.last().1,labels.last().2,owner))}
}

/// Local restoration follows from the returned mixed receipt. In the Child
/// branch this is equality of table observations, not equality of registries.
pub proof fn own_landing_witness<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize,rule:r::Rule,choice:Option<usize>)
    requires d::primitive_theory(eq,lib),fs::well_formed(lib,programs,a),fs::step(lib,programs,a,z,actor,rule,choice),mx::landing(a,z,rule),
    ensures {
        let action=receipt_action(fs::entry(lib,programs,a,actor,choice).landed.receipt);
        &&& e::inverse_action(action)
        &&& (e::key(action).is_some() ==> dep::declarations(a.state,actor).contains(e::key(action).unwrap()))
        &&& e::apply(action,e::run(step_word(lib,programs,a,z,actor,rule,choice),p::project(a.state,ISet::full())))==p::project(a.state,ISet::full())
    },
{
    og::exact_theory(eq,lib);
    fs::frame(eq,lib,programs,a,z,actor,rule,choice);
    let id=a.current[actor].unwrap();let node=concrete(programs,a,actor,choice);let out=fs::entry(lib,programs,a,actor,choice).landed;
    landing_node(eq,lib,programs,a,actor,choice);
    mx::run_admissible(eq,lib,node,a.state,actor);node_actions_typed(lib,node,a.state,actor);
    forward_projection(lib,node,a.state,actor);receipt_projection(out.receipt,out.state);e::run_singleton(forward_action(lib,node),p::project(a.state,ISet::full()));
}

/// Derive the entangled event contract from actual mixed steps. Foreign
/// retirement is observation-neutral; successful table inverses retain their
/// strict domains and exact captured providers.
#[verifier::rlimit(40)]
pub proof fn episode_recovery<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<fs::Label>,owner:usize)
    requires d::primitive_theory(eq,lib),independent_keys(lib),fs::execution(lib,programs,states,labels),fs::well_formed(lib,programs,states.first()),
        history_typed(lib,states.first().history),states.first().state.accumulators[owner].len()==0,pinned(states.first().state,owner),
        forall|i:int| 0<=i<states.len() ==> installed(states[i].state,owner),
    ensures {
        let es=events(lib,programs,states,labels,owner);let initial=p::project(states.first().state,ISet::full());let last=states.last();
        &&& fs::well_formed(lib,programs,last)
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
    og::exact_theory(eq,lib);
    let es=events(lib,programs,states,labels,owner);let initial=p::project(states.first().state,ISet::full());
    if labels.len()==0 {
        assert(states.last()==states.first());assert(own_word(states.last(),owner) =~= Seq::empty());
    } else {
        let before=states.drop_last();let steps=labels.drop_last();let a=before.last();let z=states.last();let actor=labels.last().0;let rule=labels.last().1;let choice=labels.last().2;
        assert(fs::execution(lib,programs,before,steps)) by {assert forall|i:int| 0<=i<steps.len() implies fs::step(lib,programs,before[i],before[i+1],steps[i].0,steps[i].1,steps[i].2) by {}}
        assert forall|i:int| 0<=i<before.len() implies installed(before[i].state,owner) by {assert(before[i]==states[i]);}
        episode_recovery(eq,lib,programs,before,steps,owner);
        fs::configuration_preservation(eq,lib,programs,a,z,actor,rule,choice);
        assert(fs::well_formed(lib,programs,a));assert(installed(a.state,owner));assert(installed(z.state,owner));
        episode_step(eq,lib,programs,a,z,actor,rule,choice,owner);history_typed_step(eq,lib,programs,a,z,actor,rule,choice);step_projection(eq,lib,programs,a,z,actor,rule,choice);
        let prefix=events(lib,programs,before,steps,owner);let last=event(lib,programs,a,z,actor,rule,choice,owner);
        assert(es.drop_last()==prefix);assert(es.last()==last);
        if actor==owner && mx::landing(a,z,rule) {
            own_landing_witness(eq,lib,programs,a,z,owner,rule,choice);
            assert(scope(own_word(z,owner),dep::declarations(z.state,owner))) by {
                assert forall|i:int| 0<=i<own_word(z,owner).len() && e::key(#[trigger] own_word(z,owner)[i]).is_some() implies dep::declarations(z.state,owner).contains(e::key(own_word(z,owner)[i]).unwrap()) by {
                    if i<own_word(a,owner).len() {assert(own_word(z,owner)[i]==own_word(a,owner)[i]);} else {assert(i==own_word(a,owner).len());}
                }
            }
        } else {
            foreign_compatible(eq,lib,programs,a,z,actor,rule,choice,owner);
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


proof fn actual_episode_origin<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<fs::Label>,owner:usize,b:int)
    requires d::primitive_theory(eq,lib),fs::execution(lib,programs,states,labels),states.first()==mx::empty::<U,I>(),
        0<b<states.len(),(labels[b-1].0,labels[b-1].1)==(owner,r::Rule::Begin),
    ensures fs::well_formed(lib,programs,states[b]),history_typed(lib,states[b].history),
        pinned(states[b].state,owner),states[b].state.accumulators[owner].len()==0,states[b].state.tables[owner].is_empty(),
{
    og::exact_theory(eq,lib);
    fs::empty_well_formed(lib,programs);fs::execution_preservation(eq,lib,programs,states,labels);
    assert(history_typed(lib,states.first().history));assert(provided_journals(states.first()));
    trace_history_typed(eq,lib,programs,states,labels);pc::fresh_from_empty(eq,lib,programs,states,labels);
    begin_pin(eq,lib,programs,states[b-1],states[b],owner);
    assert(states[b-1].state.control.fibers[owner].phase==Phase::Inactive);
    assert(states[b-1].state.accumulators[owner].len()==0);
    assert(states[b-1].state.tables[owner].is_empty()) by {
        assert forall|k:Port| !#[trigger] states[b-1].state.tables[owner].dom().contains(k) by {
            if states[b-1].state.tables[owner].dom().contains(k) {assert(e::erases(own_word(states[b-1],owner),k));assert(own_word(states[b-1],owner).len()==0);}
        }
    }
}

/// Select an episode from an empty-origin execution. All receipt provenance,
/// provider pinning, initial emptiness and action typing follow from that
/// execution; the caller supplies only the primitive scalar interface.
#[verifier::rlimit(100)]
pub proof fn actual_episode_recovery<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<fs::Label>,owner:usize,b:int,u:int)
    requires d::primitive_theory(eq,lib),independent_keys(lib),fs::execution(lib,programs,states,labels),states.first()==mx::empty::<U,I>(),
        0<b<=u<states.len(),(labels[b-1].0,labels[b-1].1)==(owner,r::Rule::Begin),forall|i:int| b<=i<=u ==> installed(states[i].state,owner),
    ensures {
        let segment=states.subrange(b,u+1);let steps=labels.subrange(b,u);let es=events(lib,programs,segment,steps,owner);
        &&& e::admissible_trace(es,p::project(states[b].state,ISet::full()))
        &&& own_word(states[u],owner)==e::journal(es)
        &&& e::restore(own_word(states[u],owner),p::project(states[u].state,ISet::full()))==e::foreign_state(es,p::project(states[b].state,ISet::full()))
        &&& states[b].state.tables[owner].is_empty()
    },
{
    og::exact_theory(eq,lib);
    actual_episode_origin(eq,lib,programs,states,labels,owner,b);
    let segment=states.subrange(b,u+1);let steps=labels.subrange(b,u);
    assert(fs::execution(lib,programs,segment,steps)) by {assert forall|i:int| 0<=i<steps.len() implies fs::step(lib,programs,segment[i],segment[i+1],steps[i].0,steps[i].1,steps[i].2) by {assert(segment[i]==states[b+i]);assert(segment[i+1]==states[b+i+1]);assert(steps[i]==labels[b+i]);}}
    assert forall|i:int| 0<=i<segment.len() implies installed(segment[i].state,owner) by {assert(segment[i]==states[b+i]);}
    episode_recovery(eq,lib,programs,segment,steps,owner);
}

/// The actual successful Unload recovers the foreign value replay and empties
/// this actor's table. Children can remain registered and retired; this theorem
/// asserts table observation recovery, not full registry equality.
pub proof fn actual_terminal_recovery<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<fs::Label>,owner:usize,b:int,u:int)
    requires d::primitive_theory(eq,lib),independent_keys(lib),fs::execution(lib,programs,states,labels),states.first()==mx::empty::<U,I>(),
        0<b<=u<labels.len(),(labels[b-1].0,labels[b-1].1)==(owner,r::Rule::Begin),(labels[u].0,labels[u].1)==(owner,r::Rule::Unload),forall|i:int| b<=i<=u ==> installed(states[i].state,owner),
    ensures states[u+1].state.tables[owner].is_empty(),
        p::project(states[u+1].state,ISet::full())==e::foreign_state(events(lib,programs,states.subrange(b,u+1),labels.subrange(b,u),owner),p::project(states[b].state,ISet::full())),
{
    og::exact_theory(eq,lib);
    actual_episode_recovery(eq,lib,programs,states,labels,owner,b,u);
    fs::empty_well_formed(lib,programs);fs::execution_preservation(eq,lib,programs,states,labels);
    step_projection(eq,lib,programs,states[u],states[u+1],owner,r::Rule::Unload,None);
    e::reverse_is_restore(own_word(states[u],owner),p::project(states[u].state,ISet::full()));
    assert(provided_journals(states.first()));pc::fresh_from_empty(eq,lib,programs,states,labels);restored_owner_empty(states[u],owner);
}

}
