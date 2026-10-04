//! Operation provenance for the historical ordering theorem.
//!
//! Unlike a generic admissible table map, a grammar application identifies the
//! operation at the changed key. Recovery witnesses below follow the actual
//! recursive LIFO evaluation, including its intermediate full states.
#[cfg(verus_keep_ghost)]
use crate::{
    grammar_lift as g, lifecycle_ordering as order, mediated as grammar, preservation as inv,
    refinement as control, semantics as full, Binding, Phase, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn changed<V>(a:full::State<V>,z:full::State<V>,provider:usize,key:Port)->bool {
    full::registered(a,provider) && full::registered(z,provider)
        && a.tables[provider].dom().contains(key) && z.tables[provider].dom().contains(key)
        && a.tables[provider][key]!=z.tables[provider][key]
}

pub open spec fn operation_at<V,O>(node:grammar::Node<Port,V,O>,input:full::State<V>,actor:usize,provider:usize,key:Port)->bool {
    match node {
        grammar::Node::Operation {key:actual,..} => actual==key && g::resolve(input,actor,actual)==Some(provider),
        _=>false,
    }
}

pub open spec fn operation_receipt<V>(receipt:g::Receipt<V>,provider:usize,key:Port)->bool {
    match receipt.inverse {
        g::Inverse::Operation {provider:actual,key:slot,..} => actual==provider && slot==key,
        _=>false,
    }
}

/// Successful foreign writes identify the concrete operation node and the
/// captured provider, not merely a declaration that would permit a write.
pub proof fn forward_operation_origin<V,O>(node:grammar::Node<Port,V,O>,a:full::State<V>,actor:usize,provider:usize,key:Port)
    requires g::run(node,a,actor).is_some(),actor!=provider,
        changed(a,g::run(node,a,actor).unwrap().state,provider,key),
    ensures operation_at(node,a,actor,provider,key),
        operation_receipt(g::run(node,a,actor).unwrap().receipt,provider,key),
{
    match node {
        grammar::Node::Operation {key:actual,..} => {
            assert(g::resolve(a,actor,actual)==Some(provider));
            assert(actual==key);
        },
        _=>{},
    }
}

pub proof fn inverse_operation_origin<V>(receipt:g::Receipt<V>,a:full::State<V>,provider:usize,key:Port)
    requires g::undo(receipt,a).is_some(),receipt.actor!=provider,
        changed(a,g::undo(receipt,a).unwrap(),provider,key),
    ensures operation_receipt(receipt,provider,key),g::resolve(a,receipt.actor,key)==Some(provider),
{
    match receipt.inverse {
        g::Inverse::Operation {provider:actual,key:slot,..} => {
            assert(actual==provider);assert(slot==key);
        },
        _=>{},
    }
}

/// The paper's child-instantiation alternative cannot account for a change in
/// an existing provider's table. Its concrete insert shape is checked here,
/// rather than replaced with an assumed operation-origin conclusion.
pub proof fn forward_or_child_origin<V,O>(node:grammar::Node<Port,V,O>,a:full::State<V>,z:full::State<V>,actor:usize,provider:usize,key:Port)
    requires actor!=provider,changed(a,z,provider,key),
        (g::run(node,a,actor).is_some() && z==g::run(node,a,actor).unwrap().state)
            || (exists|child:usize| inv::child_map(a,z,actor,child)),
    ensures g::run(node,a,actor).is_some(),z==g::run(node,a,actor).unwrap().state,
        operation_at(node,a,actor,provider,key),operation_receipt(g::run(node,a,actor).unwrap().receipt,provider,key),
{
    if exists|child:usize| inv::child_map(a,z,actor,child) {
        let child=choose|child:usize|inv::child_map(a,z,actor,child);
        assert(child!=provider);assert(a.tables[provider]==z.tables[provider]);
    }
    forward_operation_origin(node,a,actor,provider,key);
}

/// Likewise, actual child retirement changes only its retirement metadata.
pub proof fn inverse_or_child_origin<V>(receipt:g::Receipt<V>,a:full::State<V>,z:full::State<V>,provider:usize,key:Port)
    requires receipt.actor!=provider,changed(a,z,provider,key),
        g::undo(receipt,a)==Some(z) || (exists|child:usize| full::child_retire(a,z,child)),
    ensures g::undo(receipt,a)==Some(z),operation_receipt(receipt,provider,key),
{
    if exists|child:usize| full::child_retire(a,z,child) {assert(a.tables==z.tables);}
    inverse_operation_origin(receipt,a,provider,key);
}

/// One invocation along restore's actual recursive evaluation. The witness
/// includes the exact pre-state and post-state of the call, not just a token
/// that happens to occur somewhere in a journal.
pub open spec fn invokes<V>(history:Seq<g::Entry<V>>,tokens:Seq<nat>,input:full::State<V>,actor:usize,
    token:nat,before:full::State<V>,after:full::State<V>)->bool
    decreases tokens.len(),
{
    if tokens.len()==0 {false}
    else if tokens.last()>=history.len() || history[tokens.last() as int].landed.receipt.actor!=actor {false}
    else {match g::undo(history[tokens.last() as int].landed.receipt,input) {
        None=>false,
        Some(next)=>(token==tokens.last() && before==input && after==next)
            || invokes(history,tokens.drop_last(),next,actor,token,before,after),
    }}
}

pub open spec fn changed_invocation<V>(history:Seq<g::Entry<V>>,tokens:Seq<nat>,input:full::State<V>,actor:usize,
    provider:usize,key:Port,token:nat,before:full::State<V>,after:full::State<V>)->bool {
    &&& invokes(history,tokens,input,actor,token,before,after)
    &&& token<history.len() && history[token as int].landed.receipt.actor==actor
    &&& inv::well_formed(before)
    &&& changed(before,after,provider,key)
    &&& operation_receipt(history[token as int].landed.receipt,provider,key)
    &&& g::undo(history[token as int].landed.receipt,before)==Some(after)
}

/// If the final value differs, at least one actual inverse application on the
/// evaluated stack changed it. Cancellation by later inverses is allowed; no
/// claim that every retained token changes the value is needed.
pub proof fn restore_operation_origin<V>(history:Seq<g::Entry<V>>,tokens:Seq<nat>,input:full::State<V>,actor:usize,provider:usize,key:Port)
    requires inv::well_formed(input),full::registered(input,actor),actor!=provider,
        g::restore(history,tokens,input,actor).is_some(),
        changed(input,g::restore(history,tokens,input,actor).unwrap(),provider,key),
    ensures exists|token:nat,before:full::State<V>,after:full::State<V>|
        changed_invocation(history,tokens,input,actor,provider,key,token,before,after),
    decreases tokens.len(),
{
    assert(tokens.len()>0);
    let token=tokens.last();
    let receipt=history[token as int].landed.receipt;
    let next=g::undo(receipt,input).unwrap();
    g::undo_preservation(receipt,input);
    assert(input.tables[provider].dom()==next.tables[provider].dom());
    if input.tables[provider][key]!=next.tables[provider][key] {
        inverse_operation_origin(receipt,input,provider,key);
        assert(changed_invocation(history,tokens,input,actor,provider,key,token,input,next));
    } else {
        restore_operation_origin(history,tokens.drop_last(),next,actor,provider,key);
        let (inner,before,after)=choose|inner:nat,before:full::State<V>,after:full::State<V>|
            changed_invocation(history,tokens.drop_last(),next,actor,provider,key,inner,before,after);
        assert(changed_invocation(history,tokens,input,actor,provider,key,inner,before,after));
    }
}

/// Authentic history ties an invoked operation inverse to the exact forward
/// node which produced the retained receipt, including its provider identity.
pub proof fn retained_operation_origin<V,O>(programs:g::Programs<V,O>,history:Seq<g::Entry<V>>,token:nat,provider:usize,key:Port)
    requires g::history_sound(programs,history),token<history.len(),
        operation_receipt(history[token as int].landed.receipt,provider,key),
    ensures operation_at(programs(history[token as int].landed.receipt.actor)(history[token as int].iterator),
        history[token as int].input,history[token as int].landed.receipt.actor,provider,key),
{
    let recorded=history[token as int];
    let actor=recorded.landed.receipt.actor;
    let node=programs(actor)(recorded.iterator);
    assert(g::run(node,recorded.input,actor)==Some(recorded.landed));
    match node {
        grammar::Node::Operation {..}=>{},
        _=>{},
    }
}

/// The forward branch names this step's node and actual result. The recovery
/// branch names an actually invoked retained inverse and its original node.
pub open spec fn step_operation_origin<V,O>(programs:g::Programs<V,O>,a:g::Configuration<V>,z:g::Configuration<V>,
    actor:usize,rule:control::Rule,provider:usize,key:Port)->bool {
    (g::landing_rule(a,z,rule)
        && operation_at(programs(actor)(a.state.iterators[actor].unwrap()),a.state,actor,provider,key)
        && operation_receipt(g::entry(programs,a.state,actor).landed.receipt,provider,key)
        && changed(a.state,g::entry(programs,a.state,actor).landed.state,provider,key))
    || (rule==control::Rule::Unload && exists|token:nat,before:full::State<V>,after:full::State<V>| {
        &&& changed_invocation(a.history,a.state.accumulators[actor],a.state,actor,provider,key,token,before,after)
        &&& operation_at(programs(actor)(a.history[token as int].iterator),a.history[token as int].input,actor,provider,key)
    })
}

pub proof fn foreign_step_operation_origin<V,O>(programs:g::Programs<V,O>,allowed:grammar::Allowed<Port,V,O>,
    a:g::Configuration<V>,z:g::Configuration<V>,actor:usize,rule:control::Rule,provider:usize,key:Port)
    requires inv::well_formed(a.state),g::history_sound(programs,a.history),g::step(programs,allowed,a,z,actor,rule),
        actor!=provider,changed(a.state,z.state,provider,key),
    ensures step_operation_origin(programs,a,z,actor,rule,provider,key),
{
    g::metadata_frame(programs,allowed,a,z,actor,rule);
    if g::landing_rule(a,z,rule) {
        forward_operation_origin(programs(actor)(a.state.iterators[actor].unwrap()),a.state,actor,provider,key);
    } else if rule==control::Rule::Unload {
        restore_operation_origin(a.history,a.state.accumulators[actor],a.state,actor,provider,key);
        let (token,before,after)=choose|token:nat,before:full::State<V>,after:full::State<V>|
            changed_invocation(a.history,a.state.accumulators[actor],a.state,actor,provider,key,token,before,after);
        retained_operation_origin(programs,a.history,token,provider,key);
        assert(operation_at(programs(actor)(a.history[token as int].iterator),a.history[token as int].input,actor,provider,key));
    } else {assert(a.state.tables[provider]==z.state.tables[provider]);}
}

/// An empty initial journal contains no supplied past. Every subsequent entry
/// is the exact record appended by a landing at an earlier position in this
/// execution, even when a live token reuses an older identical call's index.
pub proof fn history_entry_origin<V,O>(programs:g::Programs<V,O>,allowed:grammar::Allowed<Port,V,O>,
    states:Seq<g::Configuration<V>>,labels:Seq<(usize,control::Rule)>,token:nat)
    requires g::execution(programs,allowed,states,labels),states.first().history.len()==0,token<states.last().history.len(),
    ensures exists|i:int| 0<=i<labels.len()
        && g::landing_rule(states[i],states[i+1],labels[i].1)
        && states.last().history[token as int]==g::entry(programs,states[i].state,labels[i].0),
    decreases labels.len(),
{
    assert(labels.len()>0);
    let previous=states.drop_last();let prefix=labels.drop_last();
    let a=previous.last();let z=states.last();let actor=labels.last().0;let rule=labels.last().1;
    assert(g::execution(programs,allowed,previous,prefix)) by {
        assert forall|i:int| 0<=i<prefix.len() implies g::step(programs,allowed,previous[i],previous[i+1],prefix[i].0,prefix[i].1) by { }
    }
    if token<a.history.len() {
        history_entry_origin(programs,allowed,previous,prefix,token);
        let i=choose|i:int| 0<=i<prefix.len() && g::landing_rule(previous[i],previous[i+1],prefix[i].1)
            && previous.last().history[token as int]==g::entry(programs,previous[i].state,prefix[i].0);
        g::step_history_prefix(programs,allowed,a,z,actor,rule);
        assert(z.history[token as int]==a.history[token as int]);
        assert(g::landing_rule(states[i],states[i+1],labels[i].1)
            && states.last().history[token as int]==g::entry(programs,states[i].state,labels[i].0));
    } else {
        assert(z.history==a.history || z.history==a.history.push(g::entry(programs,a.state,actor)));
        assert(token==a.history.len());
        assert(g::landing_rule(a,z,rule));
        assert(z.history[token as int]==g::entry(programs,a.state,actor));
        assert(a==states[labels.len()-1]);
    }
}

/// Strengthen a recovery witness with the actual prior landing that generated
/// its retained entry. An occurrence in an initial invented journal cannot
/// satisfy the empty-history premise used here.
pub proof fn invocation_prior_landing<V,O>(eq:spec_fn(Port,V,V)->bool,programs:g::Programs<V,O>,allowed:grammar::Allowed<Port,V,O>,
    states:Seq<g::Configuration<V>>,labels:Seq<(usize,control::Rule)>,t:int,actor:usize,provider:usize,key:Port,
    token:nat,before:full::State<V>,after:full::State<V>)
    requires grammar::primitive_theory(eq,allowed),g::execution(programs,allowed,states,labels),g::well_formed(programs,allowed,states.first()),
        states.first().history.len()==0,0<=t<states.len(),
        changed_invocation(states[t].history,states[t].state.accumulators[actor],states[t].state,actor,provider,key,token,before,after),
    ensures exists|i:int| 0<=i<t && labels[i].0==actor && g::landing_rule(states[i],states[i+1],labels[i].1)
        && states[t].history[token as int]==g::entry(programs,states[i].state,actor)
        && operation_at(programs(actor)(states[i].state.iterators[actor].unwrap()),states[i].state,actor,provider,key),
{
    g::execution_preservation(eq,programs,allowed,states,labels);
    let prefix=states.take(t+1);let steps=labels.take(t);
    assert(g::execution(programs,allowed,prefix,steps)) by {
        assert forall|i:int| 0<=i<steps.len() implies g::step(programs,allowed,prefix[i],prefix[i+1],steps[i].0,steps[i].1) by { }
    }
    history_entry_origin(programs,allowed,prefix,steps,token);
    let i=choose|i:int| 0<=i<steps.len() && g::landing_rule(prefix[i],prefix[i+1],steps[i].1)
        && prefix.last().history[token as int]==g::entry(programs,prefix[i].state,steps[i].0);
    g::metadata_frame(programs,allowed,states[i],states[i+1],labels[i].0,labels[i].1);
    assert(labels[i].0==actor);
    retained_operation_origin(programs,states[t].history,token,provider,key);
    assert(operation_at(programs(actor)(states[i].state.iterators[actor].unwrap()),states[i].state,actor,provider,key));
}

/// Theorem 70 on actual finite grammar executions: begin publication, fixed
/// commitments, provider episode order and persistent domains all follow from
/// the catalog refinement. Every changed provider value additionally identifies
/// its concrete operation or an actual LIFO invocation of a retained inverse.
/// The grammar here contains unit, operation and provision nodes. Child and
/// arbitrary host effects are not asserted to have this grammar provenance.
pub proof fn episode_operation_ordering<V,O>(eq:spec_fn(Port,V,V)->bool,programs:g::Programs<V,O>,allowed:grammar::Allowed<Port,V,O>,
    states:Seq<g::Configuration<V>>,labels:Seq<(usize,control::Rule)>,consumer:usize,binding:Binding,b:int,u:int,pb:int,pu:int)
    requires grammar::primitive_theory(eq,allowed),g::execution(programs,allowed,states,labels),g::well_formed(programs,allowed,states.first()),
        order::episode(g::erase_history(states),consumer,b,u),states[b].state.control.fibers[consumer].committed.contains(binding),
        order::episode(g::erase_history(states),binding.provider,pb,pu),pb<=b<=pu,
    ensures labels[b-1]==(consumer,control::Rule::Begin),
        forall|key:Port| #[trigger] states[b-1].state.control.fibers[consumer].dependencies.contains(key) ==>
            exists|provider:usize| #[trigger] full::publishes(states[b-1].state,key,provider),
        pb<b,pu<labels.len() ==> u<pu,
        forall|t:int| b<=t<=u ==> {
            &&& states[t].state.control.fibers[consumer].committed==states[b].state.control.fibers[consumer].committed
            &&& full::registered(states[t].state,binding.provider)
            &&& (states[t].state.control.fibers[binding.provider].phase==Phase::Active || states[t].state.control.fibers[binding.provider].phase==Phase::Unloading)
            &&& states[t].state.tables[binding.provider].dom()==states[b].state.tables[binding.provider].dom()
            &&& states[t].state.tables[binding.provider].dom().contains(Port{key:binding.key,realm:binding.realm})
            &&& (t<labels.len() ==> forall|key:Port| states[t].state.tables[binding.provider].dom().contains(key)
                && states[t].state.tables[binding.provider][key]!=states[t+1].state.tables[binding.provider][key] ==> {
                &&& states[t].state.control.fibers[labels[t].0].dependencies.contains(key)
                &&& step_operation_origin(programs,states[t],states[t+1],labels[t].0,labels[t].1,binding.provider,key)
            })
        },
{
    g::execution_preservation(eq,programs,allowed,states,labels);
    g::catalog_execution_refines(eq,programs,allowed,states,labels);
    let erased=g::erase_history(states);
    let model=g::catalog_model(states.last().history);
    assert(order::trace(model,erased,labels));
    order::episode_boundaries(model,erased,labels,consumer,b,u);
    order::begin_provided(model,states[b-1].state,states[b].state,consumer);
    order::dependency_lifetime(model,erased,labels,consumer,binding,b,u);
    order::episode_order(model,erased,labels,consumer,binding,b,u,pb,pu);
    assert forall|t:int| b<=t<=u implies {
        &&& states[t].state.control.fibers[consumer].committed==states[b].state.control.fibers[consumer].committed
        &&& full::registered(states[t].state,binding.provider)
        &&& (states[t].state.control.fibers[binding.provider].phase==Phase::Active || states[t].state.control.fibers[binding.provider].phase==Phase::Unloading)
        &&& states[t].state.tables[binding.provider].dom()==states[b].state.tables[binding.provider].dom()
        &&& states[t].state.tables[binding.provider].dom().contains(Port{key:binding.key,realm:binding.realm})
        &&& (t<labels.len() ==> forall|key:Port| states[t].state.tables[binding.provider].dom().contains(key)
            && states[t].state.tables[binding.provider][key]!=states[t+1].state.tables[binding.provider][key] ==> {
            &&& states[t].state.control.fibers[labels[t].0].dependencies.contains(key)
            &&& step_operation_origin(programs,states[t],states[t+1],labels[t].0,labels[t].1,binding.provider,key)
        })
    } by {
        if t<labels.len() {
            order::pinned_table_step(model,states[t].state,states[t+1].state,labels[t].0,labels[t].1,consumer,binding);
            assert forall|key:Port| states[t].state.tables[binding.provider].dom().contains(key)
                && states[t].state.tables[binding.provider][key]!=states[t+1].state.tables[binding.provider][key] implies {
                &&& states[t].state.control.fibers[labels[t].0].dependencies.contains(key)
                &&& step_operation_origin(programs,states[t],states[t+1],labels[t].0,labels[t].1,binding.provider,key)
            } by {
                foreign_step_operation_origin(programs,allowed,states[t],states[t+1],labels[t].0,labels[t].1,binding.provider,key);
            }
        }
    }
}

} // verus!
