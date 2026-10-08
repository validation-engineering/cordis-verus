//! Operation provenance inside the unified dependent-and-child execution.
//!
//! Child inverses are actually evaluated along the restoration path. Their
//! retirement changes are preserved, while a changed table value must come
//! from a table-operation receipt at the exact provider and key.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, dependent_grammar as d, grammar_lift as g, grammar_ordering as go,
    indexed_ordering as indexed, lifecycle_ordering as order, mixed_grammar as mix,
    observational_grammar as og, observational_lift as ol, preservation as inv, refinement as r,
    semantics as s, Binding, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn operation<A,X,U,B,I>(lib:mix::Library<A,X,U,B>,node:mix::Node<A,X,U,B,I>,input:s::State<U>,actor:usize,provider:usize,key:Port)->bool {
    match node {
        mix::Node::Dependent {node}=>indexed::dependent_operation(lib,node,input,actor,provider,key),
        mix::Node::Child {..}=>false,
    }
}
pub open spec fn operation_receipt<U>(receipt:mix::Receipt<U>,provider:usize,key:Port)->bool {
    match receipt {
        mix::Receipt::Table {receipt}=>go::operation_receipt(receipt,provider,key),
        mix::Receipt::Child {..}=>false,
    }
}

pub proof fn forward_origin<A,X,U,B,I>(lib:mix::Library<A,X,U,B>,node:mix::Node<A,X,U,B,I>,input:s::State<U>,actor:usize,provider:usize,key:Port)
    requires mix::run(lib,node,input,actor).is_some(),actor!=provider,go::changed(input,mix::run(lib,node,input,actor).unwrap().state,provider,key),
    ensures operation(lib,node,input,actor,provider,key),operation_receipt(mix::run(lib,node,input,actor).unwrap().receipt,provider,key),
{
    match node {
        mix::Node::Dependent {node}=>{indexed::dependent_forward_origin(lib,node,input,actor,provider,key);},
        mix::Node::Child {child,..}=>{assert(!s::registered(input,child));assert(child!=provider);},
    }
}
pub proof fn inverse_origin<U>(receipt:mix::Receipt<U>,input:s::State<U>,provider:usize,key:Port)
    requires mix::undo(receipt,input).is_some(),mix::owner(receipt)!=provider,go::changed(input,mix::undo(receipt,input).unwrap(),provider,key),
    ensures operation_receipt(receipt,provider,key),
{
    match receipt {
        mix::Receipt::Table {receipt}=>{go::inverse_operation_origin(receipt,input,provider,key);},
        mix::Receipt::Child {..}=>{assert(mix::undo(receipt,input).unwrap().tables==input.tables);},
    }
}

/// This small adapter derives inverse admissibility from the concrete receipt
/// variant. It does not assume the successor invariant or a table footprint.
pub proof fn inverse_shape<U>(receipt:mix::Receipt<U>,input:s::State<U>)
    requires inv::well_formed(input),s::registered(input,mix::owner(receipt)),mix::undo(receipt,input).is_some(),
    ensures inv::inverse_map(input,mix::undo(receipt,input).unwrap(),mix::owner(receipt)),
        inv::well_formed(mix::undo(receipt,input).unwrap()),s::registered(mix::undo(receipt,input).unwrap(),mix::owner(receipt)),
{
    match receipt {
        mix::Receipt::Table {receipt}=>{g::undo_preservation(receipt,input);},
        mix::Receipt::Child {child,..}=>{ch::concrete_child_retirement(input,child);},
    }
    inv::inverse_preservation(input,mix::undo(receipt,input).unwrap(),mix::owner(receipt));
}

/// The actual mixed LIFO call path, with child retirements retained in each
/// intermediate state. This is not a filtered table-only restoration.
pub open spec fn invokes<U,I>(history:Seq<mix::Entry<U,I>>,tokens:Seq<nat>,input:s::State<U>,actor:usize,
    token:nat,before:s::State<U>,after:s::State<U>)->bool
    decreases tokens.len(),
{
    if tokens.len()==0 {false}
    else if tokens.last()>=history.len() || mix::owner(history[tokens.last() as int].landed.receipt)!=actor {false}
    else {match mix::undo(history[tokens.last() as int].landed.receipt,input) {
        None=>false,
        Some(next)=>(token==tokens.last() && before==input && after==next)
            || invokes(history,tokens.drop_last(),next,actor,token,before,after),
    }}
}
pub open spec fn changed_invocation<U,I>(history:Seq<mix::Entry<U,I>>,tokens:Seq<nat>,input:s::State<U>,actor:usize,
    provider:usize,key:Port,token:nat,before:s::State<U>,after:s::State<U>)->bool {
    &&& invokes(history,tokens,input,actor,token,before,after)
    &&& token<history.len() && mix::owner(history[token as int].landed.receipt)==actor
    &&& inv::well_formed(before) && go::changed(before,after,provider,key)
    &&& operation_receipt(history[token as int].landed.receipt,provider,key)
    &&& mix::undo(history[token as int].landed.receipt,before)==Some(after)
}

pub proof fn restore_origin<U,I>(history:Seq<mix::Entry<U,I>>,tokens:Seq<nat>,input:s::State<U>,actor:usize,provider:usize,key:Port)
    requires inv::well_formed(input),s::registered(input,actor),actor!=provider,mix::restore(history,tokens,input,actor).is_some(),
        go::changed(input,mix::restore(history,tokens,input,actor).unwrap(),provider,key),
    ensures exists|token:nat,before:s::State<U>,after:s::State<U>|
        changed_invocation(history,tokens,input,actor,provider,key,token,before,after),
    decreases tokens.len(),
{
    assert(tokens.len()>0);
    let token=tokens.last();let receipt=history[token as int].landed.receipt;let next=mix::undo(receipt,input).unwrap();
    inverse_shape(receipt,input);order::inverse_table_frame(input,next,actor,provider);
    if input.tables[provider][key]!=next.tables[provider][key] {
        inverse_origin(receipt,input,provider,key);
        assert(changed_invocation(history,tokens,input,actor,provider,key,token,input,next));
    } else {
        restore_origin(history,tokens.drop_last(),next,actor,provider,key);
        let (inner,before,after)=choose|inner:nat,before:s::State<U>,after:s::State<U>|
            changed_invocation(history,tokens.drop_last(),next,actor,provider,key,inner,before,after);
        assert(changed_invocation(history,tokens,input,actor,provider,key,inner,before,after));
    }
}

pub proof fn retained_origin<A,X,U,B,I>(lib:mix::Library<A,X,U,B>,programs:mix::Programs<A,X,U,B,I>,history:Seq<mix::Entry<U,I>>,token:nat,provider:usize,key:Port)
    requires mix::history_sound(lib,programs,history),token<history.len(),operation_receipt(history[token as int].landed.receipt,provider,key),
    ensures operation(lib,programs(mix::owner(history[token as int].landed.receipt))(history[token as int].iterator),
        history[token as int].input,mix::owner(history[token as int].landed.receipt),provider,key),
{
    let recorded=history[token as int];let actor=mix::owner(recorded.landed.receipt);let node=programs(actor)(recorded.iterator);
    assert(mix::run(lib,node,recorded.input,actor)==Some(recorded.landed));
    match node {
        mix::Node::Dependent {node}=>{
            match node {d::Node::Operation {..}=>{},_=>{},}
        },
        mix::Node::Child {..}=>{},
    }
}

pub open spec fn step_origin<A,X,U,B,I>(lib:mix::Library<A,X,U,B>,programs:mix::Programs<A,X,U,B,I>,
    a:mix::Configuration<U,I>,z:mix::Configuration<U,I>,actor:usize,rule:r::Rule,provider:usize,key:Port)->bool {
    (mix::landing(a,z,rule)
        && operation(lib,programs(actor)(a.current[actor].unwrap()),a.state,actor,provider,key)
        && operation_receipt(mix::entry(lib,programs,a,actor).landed.receipt,provider,key)
        && go::changed(a.state,mix::entry(lib,programs,a,actor).landed.state,provider,key))
    || (rule==r::Rule::Unload && exists|token:nat,before:s::State<U>,after:s::State<U>| {
        &&& changed_invocation(a.history,a.state.accumulators[actor],a.state,actor,provider,key,token,before,after)
        &&& operation(lib,programs(actor)(a.history[token as int].iterator),a.history[token as int].input,actor,provider,key)
    })
}
pub proof fn observational_foreign_step_origin<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mix::Library<A,X,U,B>,programs:mix::Programs<A,X,U,B,I>,
    a:mix::Configuration<U,I>,z:mix::Configuration<U,I>,actor:usize,rule:r::Rule,provider:usize,key:Port)
    requires og::primitive_theory(eq,lib),mix::well_formed(lib,programs,a),mix::step(lib,programs,a,z,actor,rule),actor!=provider,go::changed(a.state,z.state,provider,key),
    ensures step_origin(lib,programs,a,z,actor,rule,provider,key),
{
    ol::frame(eq,lib,programs,a,z,actor,rule);
    if mix::landing(a,z,rule) {forward_origin(lib,programs(actor)(a.current[actor].unwrap()),a.state,actor,provider,key);}
    else if rule==r::Rule::Unload {
        restore_origin(a.history,a.state.accumulators[actor],a.state,actor,provider,key);
        let (token,before,after)=choose|token:nat,before:s::State<U>,after:s::State<U>|
            changed_invocation(a.history,a.state.accumulators[actor],a.state,actor,provider,key,token,before,after);
        retained_origin(lib,programs,a.history,token,provider,key);
        assert(operation(lib,programs(actor)(a.history[token as int].iterator),a.history[token as int].input,actor,provider,key));
    } else {assert(a.state.tables[provider]==z.state.tables[provider]);}
}

/// Exact-recovery specialization of the observational contract above.
pub proof fn foreign_step_origin<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mix::Library<A,X,U,B>,programs:mix::Programs<A,X,U,B,I>,
    a:mix::Configuration<U,I>,z:mix::Configuration<U,I>,actor:usize,rule:r::Rule,provider:usize,key:Port)
    requires d::primitive_theory(eq,lib),mix::well_formed(lib,programs,a),mix::step(lib,programs,a,z,actor,rule),actor!=provider,go::changed(a.state,z.state,provider,key),
    ensures step_origin(lib,programs,a,z,actor,rule,provider,key),
{
    og::exact_theory(eq,lib);
    observational_foreign_step_origin(eq,lib,programs,a,z,actor,rule,provider,key);
}

/// Every record from an empty initial journal corresponds to a real landing,
/// including records interspersed with arbitrary child creations/retirements.
pub proof fn history_entry_origin<A,X,U,B,I>(lib:mix::Library<A,X,U,B>,programs:mix::Programs<A,X,U,B,I>,
    states:Seq<mix::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,token:nat)
    requires mix::execution(lib,programs,states,labels),states.first().history.len()==0,token<states.last().history.len(),
    ensures exists|i:int| 0<=i<labels.len() && mix::landing(states[i],states[i+1],labels[i].1)
        && states.last().history[token as int]==mix::entry(lib,programs,states[i],labels[i].0),
    decreases labels.len(),
{
    assert(labels.len()>0);
    let previous=states.drop_last();let prefix=labels.drop_last();
    let a=previous.last();let z=states.last();let actor=labels.last().0;let rule=labels.last().1;
    assert(mix::execution(lib,programs,previous,prefix)) by {
        assert forall|i:int| 0<=i<prefix.len() implies mix::step(lib,programs,previous[i],previous[i+1],prefix[i].0,prefix[i].1) by { }
    }
    assert(z.history==a.history || z.history==a.history.push(mix::entry(lib,programs,a,actor)));
    if token<a.history.len() {
        history_entry_origin(lib,programs,previous,prefix,token);
        let i=choose|i:int| 0<=i<prefix.len() && mix::landing(previous[i],previous[i+1],prefix[i].1)
            && previous.last().history[token as int]==mix::entry(lib,programs,previous[i],prefix[i].0);
        assert(z.history[token as int]==a.history[token as int]);
        assert(mix::landing(states[i],states[i+1],labels[i].1)
            && states.last().history[token as int]==mix::entry(lib,programs,states[i],labels[i].0));
    } else {
        assert(token==a.history.len());assert(mix::landing(a,z,rule));
        assert(z.history[token as int]==mix::entry(lib,programs,a,actor));assert(a==states[labels.len()-1]);
    }
}
// Only the retained record metadata is needed to find its prior landing.
// Keep recursive inverse-call evaluation in the origin proof that establishes it.
proof fn invocation_record_metadata<U,I>(history:Seq<mix::Entry<U,I>>,tokens:Seq<nat>,input:s::State<U>,actor:usize,
    provider:usize,key:Port,token:nat,before:s::State<U>,after:s::State<U>)
    requires changed_invocation(history,tokens,input,actor,provider,key,token,before,after),
    ensures token<history.len(),mix::owner(history[token as int].landed.receipt)==actor,
        operation_receipt(history[token as int].landed.receipt,provider,key),
{
    hide(invokes);
}

proof fn retained_invocation_prior_landing<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mix::Library<A,X,U,B>,programs:mix::Programs<A,X,U,B,I>,
    states:Seq<mix::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,t:int,actor:usize,provider:usize,key:Port,
    token:nat)
    requires og::primitive_theory(eq,lib),mix::execution(lib,programs,states,labels),mix::well_formed(lib,programs,states.first()),
        states.first().history.len()==0,0<=t<states.len(),
        token<states[t].history.len(),mix::owner(states[t].history[token as int].landed.receipt)==actor,
        operation_receipt(states[t].history[token as int].landed.receipt,provider,key),
    ensures exists|i:int| 0<=i<t && labels[i].0==actor && mix::landing(states[i],states[i+1],labels[i].1)
        && states[t].history[token as int]==mix::entry(lib,programs,states[i],actor)
        && operation(lib,programs(actor)(states[i].current[actor].unwrap()),states[i].state,actor,provider,key),
{
    ol::execution_preservation(eq,lib,programs,states,labels);
    let prefix=states.take(t+1);let steps=labels.take(t);
    assert(mix::execution(lib,programs,prefix,steps)) by {
        assert forall|i:int| 0<=i<steps.len() implies mix::step(lib,programs,prefix[i],prefix[i+1],steps[i].0,steps[i].1) by { }
    }
    history_entry_origin(lib,programs,prefix,steps,token);
    let i=choose|i:int| 0<=i<steps.len() && mix::landing(prefix[i],prefix[i+1],steps[i].1)
        && prefix.last().history[token as int]==mix::entry(lib,programs,prefix[i],steps[i].0);
    ol::frame(eq,lib,programs,states[i],states[i+1],labels[i].0,labels[i].1);
    assert(labels[i].0==actor);retained_origin(lib,programs,states[t].history,token,provider,key);
    assert(operation(lib,programs(actor)(states[i].current[actor].unwrap()),states[i].state,actor,provider,key));
}

pub proof fn observational_invocation_prior_landing<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mix::Library<A,X,U,B>,programs:mix::Programs<A,X,U,B,I>,
    states:Seq<mix::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,t:int,actor:usize,provider:usize,key:Port,
    token:nat,before:s::State<U>,after:s::State<U>)
    requires og::primitive_theory(eq,lib),mix::execution(lib,programs,states,labels),mix::well_formed(lib,programs,states.first()),
        states.first().history.len()==0,0<=t<states.len(),
        changed_invocation(states[t].history,states[t].state.accumulators[actor],states[t].state,actor,provider,key,token,before,after),
    ensures exists|i:int| 0<=i<t && labels[i].0==actor && mix::landing(states[i],states[i+1],labels[i].1)
        && states[t].history[token as int]==mix::entry(lib,programs,states[i],actor)
        && operation(lib,programs(actor)(states[i].current[actor].unwrap()),states[i].state,actor,provider,key),
{
    hide(changed_invocation);
    invocation_record_metadata(states[t].history,states[t].state.accumulators[actor],states[t].state,actor,provider,key,token,before,after);
    retained_invocation_prior_landing(eq,lib,programs,states,labels,t,actor,provider,key,token);
}

/// Exact-recovery specialization of the observational contract above.
pub proof fn invocation_prior_landing<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mix::Library<A,X,U,B>,programs:mix::Programs<A,X,U,B,I>,
    states:Seq<mix::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,t:int,actor:usize,provider:usize,key:Port,
    token:nat,before:s::State<U>,after:s::State<U>)
    requires d::primitive_theory(eq,lib),mix::execution(lib,programs,states,labels),mix::well_formed(lib,programs,states.first()),
        states.first().history.len()==0,0<=t<states.len(),
        changed_invocation(states[t].history,states[t].state.accumulators[actor],states[t].state,actor,provider,key,token,before,after),
    ensures exists|i:int| 0<=i<t && labels[i].0==actor && mix::landing(states[i],states[i+1],labels[i].1)
        && states[t].history[token as int]==mix::entry(lib,programs,states[i],actor)
        && operation(lib,programs(actor)(states[i].current[actor].unwrap()),states[i].state,actor,provider,key),
{
    og::exact_theory(eq,lib);
    observational_invocation_prior_landing(eq,lib,programs,states,labels,t,actor,provider,key,token,before,after);
}

pub open spec fn historical_origin<A,X,U,B,I>(lib:mix::Library<A,X,U,B>,programs:mix::Programs<A,X,U,B,I>,
    states:Seq<mix::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,t:int,provider:usize,key:Port)->bool {
    let a=states[t];let z=states[t+1];let actor=labels[t].0;let rule=labels[t].1;
    (mix::landing(a,z,rule) && step_origin(lib,programs,a,z,actor,rule,provider,key))
    || (rule==r::Rule::Unload && exists|token:nat,before:s::State<U>,after:s::State<U>,i:int| {
        &&& changed_invocation(a.history,a.state.accumulators[actor],a.state,actor,provider,key,token,before,after)
        &&& 0<=i<t && labels[i].0==actor && mix::landing(states[i],states[i+1],labels[i].1)
        &&& a.history[token as int]==mix::entry(lib,programs,states[i],actor)
        &&& operation(lib,programs(actor)(states[i].current[actor].unwrap()),states[i].state,actor,provider,key)
    })
}

pub proof fn observational_step_historical_origin<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mix::Library<A,X,U,B>,programs:mix::Programs<A,X,U,B,I>,
    states:Seq<mix::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,t:int,provider:usize,key:Port)
    requires og::primitive_theory(eq,lib),mix::execution(lib,programs,states,labels),mix::well_formed(lib,programs,states.first()),
        states.first().history.len()==0,0<=t<labels.len(),step_origin(lib,programs,states[t],states[t+1],labels[t].0,labels[t].1,provider,key),
    ensures historical_origin(lib,programs,states,labels,t,provider,key),
{
    let a=states[t];let z=states[t+1];let actor=labels[t].0;let rule=labels[t].1;
    if !mix::landing(a,z,rule) {
        let (token,before,after)=choose|token:nat,before:s::State<U>,after:s::State<U>| {
            &&& changed_invocation(a.history,a.state.accumulators[actor],a.state,actor,provider,key,token,before,after)
            &&& operation(lib,programs(actor)(a.history[token as int].iterator),a.history[token as int].input,actor,provider,key)
        };
        observational_invocation_prior_landing(eq,lib,programs,states,labels,t,actor,provider,key,token,before,after);
        let i=choose|i:int| 0<=i<t && labels[i].0==actor && mix::landing(states[i],states[i+1],labels[i].1)
            && a.history[token as int]==mix::entry(lib,programs,states[i],actor)
            && operation(lib,programs(actor)(states[i].current[actor].unwrap()),states[i].state,actor,provider,key);
        assert(changed_invocation(a.history,a.state.accumulators[actor],a.state,actor,provider,key,token,before,after)
            && 0<=i<t && labels[i].0==actor && mix::landing(states[i],states[i+1],labels[i].1)
            && a.history[token as int]==mix::entry(lib,programs,states[i],actor)
            && operation(lib,programs(actor)(states[i].current[actor].unwrap()),states[i].state,actor,provider,key));
    }
}

/// Exact-recovery specialization of the observational contract above.
pub proof fn step_historical_origin<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mix::Library<A,X,U,B>,programs:mix::Programs<A,X,U,B,I>,
    states:Seq<mix::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,t:int,provider:usize,key:Port)
    requires d::primitive_theory(eq,lib),mix::execution(lib,programs,states,labels),mix::well_formed(lib,programs,states.first()),
        states.first().history.len()==0,0<=t<labels.len(),step_origin(lib,programs,states[t],states[t+1],labels[t].0,labels[t].1,provider,key),
    ensures historical_origin(lib,programs,states,labels,t,provider,key),
{
    og::exact_theory(eq,lib);
    observational_step_historical_origin(eq,lib,programs,states,labels,t,provider,key);
}

/// Theorem 70 and Theorem 71's phase/coherence clauses for one unified actual
/// arbitrary-index grammar, including child creation and child retirement.
/// Successful source execution remains a premise; arbitrary callbacks and
/// eventual closure or global recovery equivalence are not claimed here.
pub proof fn observational_episode_ordering<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mix::Library<A,X,U,B>,programs:mix::Programs<A,X,U,B,I>,
    states:Seq<mix::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,consumer:usize,binding:Binding,b:int,u:int,pb:int,pu:int)
    requires og::primitive_theory(eq,lib),mix::execution(lib,programs,states,labels),mix::well_formed(lib,programs,states.first()),
        order::episode(mix::states(states),consumer,b,u),states[b].state.control.fibers[consumer].committed.contains(binding),
        order::episode(mix::states(states),binding.provider,pb,pu),pb<=b<=pu,
    ensures indexed::lifetime(mix::states(states),labels,consumer,binding,b,u),pb<b,pu<labels.len() ==> u<pu,
        indexed::coherent_interval(mix::states(states),labels,consumer,b,u),
        forall|key:Port| #[trigger] states[b-1].state.control.fibers[consumer].dependencies.contains(key)
            ==> exists|provider:usize| #[trigger] s::publishes(states[b-1].state,key,provider),
        forall|t:int,key:Port| b<=t<=u && t<labels.len() && states[t].state.tables[binding.provider].dom().contains(key)
            && states[t].state.tables[binding.provider][key]!=states[t+1].state.tables[binding.provider][key]
            ==> step_origin(lib,programs,states[t],states[t+1],labels[t].0,labels[t].1,binding.provider,key),
{
    ol::execution_ordering(eq,lib,programs,states,labels);ol::execution_preservation(eq,lib,programs,states,labels);
    indexed::episode_ordering(mix::states(states),labels,consumer,binding,b,u,pb,pu);
    indexed::loading_coherence(mix::states(states),labels,consumer,b,u);
    assert forall|t:int,key:Port| b<=t<=u && t<labels.len() && states[t].state.tables[binding.provider].dom().contains(key)
        && states[t].state.tables[binding.provider][key]!=states[t+1].state.tables[binding.provider][key]
        implies step_origin(lib,programs,states[t],states[t+1],labels[t].0,labels[t].1,binding.provider,key) by {
        observational_foreign_step_origin(eq,lib,programs,states[t],states[t+1],labels[t].0,labels[t].1,binding.provider,key);
    }
}

/// Exact-recovery specialization of the observational contract above.
pub proof fn episode_ordering<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mix::Library<A,X,U,B>,programs:mix::Programs<A,X,U,B,I>,
    states:Seq<mix::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,consumer:usize,binding:Binding,b:int,u:int,pb:int,pu:int)
    requires d::primitive_theory(eq,lib),mix::execution(lib,programs,states,labels),mix::well_formed(lib,programs,states.first()),
        order::episode(mix::states(states),consumer,b,u),states[b].state.control.fibers[consumer].committed.contains(binding),
        order::episode(mix::states(states),binding.provider,pb,pu),pb<=b<=pu,
    ensures indexed::lifetime(mix::states(states),labels,consumer,binding,b,u),pb<b,pu<labels.len() ==> u<pu,
        indexed::coherent_interval(mix::states(states),labels,consumer,b,u),
        forall|key:Port| #[trigger] states[b-1].state.control.fibers[consumer].dependencies.contains(key)
            ==> exists|provider:usize| #[trigger] s::publishes(states[b-1].state,key,provider),
        forall|t:int,key:Port| b<=t<=u && t<labels.len() && states[t].state.tables[binding.provider].dom().contains(key)
            && states[t].state.tables[binding.provider][key]!=states[t+1].state.tables[binding.provider][key]
            ==> step_origin(lib,programs,states[t],states[t+1],labels[t].0,labels[t].1,binding.provider,key),
{
    og::exact_theory(eq,lib);
    observational_episode_ordering(eq,lib,programs,states,labels,consumer,binding,b,u,pb,pu);
}

/// The paper's empty-registry specialization includes full historical source
/// evidence: an inverse changing a provider value was both actually invoked
/// now and actually produced by an earlier operation in this same mixed trace.
pub proof fn observational_empty_episode_ordering<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mix::Library<A,X,U,B>,programs:mix::Programs<A,X,U,B,I>,
    states:Seq<mix::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,consumer:usize,binding:Binding,b:int,u:int,pb:int,pu:int)
    requires og::primitive_theory(eq,lib),mix::execution(lib,programs,states,labels),states.first()==mix::empty::<U,I>(),
        order::episode(mix::states(states),consumer,b,u),states[b].state.control.fibers[consumer].committed.contains(binding),
        order::episode(mix::states(states),binding.provider,pb,pu),pb<=b<=pu,
    ensures indexed::lifetime(mix::states(states),labels,consumer,binding,b,u),pb<b,pu<labels.len() ==> u<pu,
        indexed::coherent_interval(mix::states(states),labels,consumer,b,u),
        forall|key:Port| #[trigger] states[b-1].state.control.fibers[consumer].dependencies.contains(key)
            ==> exists|provider:usize| #[trigger] s::publishes(states[b-1].state,key,provider),
        forall|t:int,key:Port| b<=t<=u && t<labels.len() && states[t].state.tables[binding.provider].dom().contains(key)
            && states[t].state.tables[binding.provider][key]!=states[t+1].state.tables[binding.provider][key]
            ==> historical_origin(lib,programs,states,labels,t,binding.provider,key),
{
    mix::empty_well_formed(lib,programs);observational_episode_ordering(eq,lib,programs,states,labels,consumer,binding,b,u,pb,pu);
    assert forall|t:int,key:Port| b<=t<=u && t<labels.len() && states[t].state.tables[binding.provider].dom().contains(key)
        && states[t].state.tables[binding.provider][key]!=states[t+1].state.tables[binding.provider][key]
        implies historical_origin(lib,programs,states,labels,t,binding.provider,key) by {
        observational_step_historical_origin(eq,lib,programs,states,labels,t,binding.provider,key);
    }
}

/// Exact-recovery specialization of the observational contract above.
pub proof fn empty_episode_ordering<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mix::Library<A,X,U,B>,programs:mix::Programs<A,X,U,B,I>,
    states:Seq<mix::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,consumer:usize,binding:Binding,b:int,u:int,pb:int,pu:int)
    requires d::primitive_theory(eq,lib),mix::execution(lib,programs,states,labels),states.first()==mix::empty::<U,I>(),
        order::episode(mix::states(states),consumer,b,u),states[b].state.control.fibers[consumer].committed.contains(binding),
        order::episode(mix::states(states),binding.provider,pb,pu),pb<=b<=pu,
    ensures indexed::lifetime(mix::states(states),labels,consumer,binding,b,u),pb<b,pu<labels.len() ==> u<pu,
        indexed::coherent_interval(mix::states(states),labels,consumer,b,u),
        forall|key:Port| #[trigger] states[b-1].state.control.fibers[consumer].dependencies.contains(key)
            ==> exists|provider:usize| #[trigger] s::publishes(states[b-1].state,key,provider),
        forall|t:int,key:Port| b<=t<=u && t<labels.len() && states[t].state.tables[binding.provider].dom().contains(key)
            && states[t].state.tables[binding.provider][key]!=states[t+1].state.tables[binding.provider][key]
            ==> historical_origin(lib,programs,states,labels,t,binding.provider,key),
{
    og::exact_theory(eq,lib);
    observational_empty_episode_ordering(eq,lib,programs,states,labels,consumer,binding,b,u,pb,pu);
}

} // verus!
