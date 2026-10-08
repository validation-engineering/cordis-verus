//! Lifecycle ordering from actual per-step semantic evidence.
//!
//! A continuation index need not fit in nat. Each actual transition can supply
//! its own mathematical Model; the ordering proof uses only that transition's
//! rule and primitive admissibility. No common interpreter identity is claimed.
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_grammar as d, dependent_lift as dl, entangled as e, grammar_lift as g,
    grammar_ordering as go, lifecycle_ordering as order, preservation as inv, refinement as r,
    rule_frames as frames, semantics as s, Binding, Phase, Port,
};
use vstd::prelude::*;

verus! {

/// Primitive semantic evidence, not a premise about ordering or lifetimes.
pub open spec fn step<V>(a:s::State<V>,z:s::State<V>,actor:usize,rule:r::Rule)->bool {
    exists|model:s::Model<V>| #[trigger] s::step(model,a,z,actor,rule) && inv::admissible_step(model,a,z,actor,rule)
}
pub open spec fn trace<V>(states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>)->bool {
    states.len()==labels.len()+1 && inv::well_formed(states.first())
        && forall|i:int| 0<=i<labels.len() ==> step(states[i],states[i+1],labels[i].0,labels[i].1)
}
pub open spec fn at<V>(states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>,i:int)->s::Model<V> {
    choose|model:s::Model<V>| #[trigger] s::step(model,states[i],states[i+1],labels[i].0,labels[i].1)
        && inv::admissible_step(model,states[i],states[i+1],labels[i].0,labels[i].1)
}

pub proof fn fixed_model_trace<V>(model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>)
    requires order::trace(model,states,labels),
    ensures trace(states,labels),
{
    assert forall|i:int| 0<=i<labels.len() implies step(states[i],states[i+1],labels[i].0,labels[i].1) by {
        assert(s::step(model,states[i],states[i+1],labels[i].0,labels[i].1)
            && inv::admissible_step(model,states[i],states[i+1],labels[i].0,labels[i].1));
    }
}

pub proof fn preservation<V>(states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>)
    requires trace(states,labels),
    ensures forall|i:int| 0<=i<states.len() ==> inv::well_formed(states[i]),
    decreases labels.len(),
{
    if labels.len()>0 {
        let previous=states.drop_last();let prefix=labels.drop_last();
        assert(previous.len()==prefix.len()+1);
        assert(trace(previous,prefix)) by {
            assert forall|i:int| 0<=i<prefix.len() implies step(previous[i],previous[i+1],prefix[i].0,prefix[i].1) by { }
        }
        preservation(previous,prefix);
        let i=labels.len()-1;
        assert(previous[i]==states[i]);assert(inv::well_formed(previous[i]));
        inv::full_preservation(at(states,labels,i),states[i],states[i+1],labels[i].0,labels[i].1);
        assert forall|j:int| 0<=j<states.len() implies inv::well_formed(states[j]) by {
            if j<previous.len() {assert(previous[j]==states[j]);}
        }
    }
}

/// The same single-step frame theorems cover child insertion and retirement.
pub proof fn step_frames<V>(states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>,i:int,n:usize)
    requires trace(states,labels),0<=i<labels.len(),s::registered(states[i],n),
    ensures s::registered(states[i+1],n) ==> frames::metadata(states[i],states[i+1],n),
        labels[i].0!=n ==> order::table_frame(states[i],states[i+1],labels[i].0,n),
{
    preservation(states,labels);
    let model=at(states,labels,i);
    if s::registered(states[i+1],n) {frames::step_metadata(model,states[i],states[i+1],labels[i].0,labels[i].1,n);}
    if labels[i].0!=n {order::foreign_table_step(model,states[i],states[i+1],labels[i].0,labels[i].1,n);}
}

pub proof fn episode_boundaries<V>(states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>,n:usize,b:int,u:int)
    requires trace(states,labels),order::episode(states,n,b,u),
    ensures labels[b-1]==(n,r::Rule::Begin),states[b].control.fibers[n].phase==Phase::Loading,
        u<labels.len() ==> labels[u]==(n,r::Rule::Unload),
{
    preservation(states,labels);
    order::installation_step(at(states,labels,b-1),states[b-1],states[b],labels[b-1].0,labels[b-1].1,n);
    if u<labels.len() {order::installation_step(at(states,labels,u),states[u],states[u+1],labels[u].0,labels[u].1,n);}
}

pub proof fn committed_interval<V>(states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>,n:usize,b:int,t:int)
    requires trace(states,labels),0<=b<=t<states.len(),forall|j:int| b<=j<=t ==> order::installed(states[j],n),
    ensures states[t].control.fibers[n].committed==states[b].control.fibers[n].committed,
    decreases t-b,
{
    if t>b {
        committed_interval(states,labels,n,b,t-1);preservation(states,labels);
        order::installation_step(at(states,labels,t-1),states[t-1],states[t],labels[t-1].0,labels[t-1].1,n);
    }
}

pub proof fn pinned_interval<V>(states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>,consumer:usize,binding:Binding,b:int,t:int)
    requires trace(states,labels),0<=b<=t<states.len(),forall|j:int| b<=j<=t ==> order::installed(states[j],consumer),
        states[b].control.fibers[consumer].committed.contains(binding),states[b].control.fibers[binding.provider].phase==Phase::Active,
    ensures s::registered(states[t],binding.provider),
        states[t].control.fibers[binding.provider].phase==Phase::Active || states[t].control.fibers[binding.provider].phase==Phase::Unloading,
        states[t].tables[binding.provider].dom()==states[b].tables[binding.provider].dom(),
    decreases t-b,
{
    preservation(states,labels);
    if t>b {
        pinned_interval(states,labels,consumer,binding,b,t-1);committed_interval(states,labels,consumer,b,t-1);
        order::pinned_table_step(at(states,labels,t-1),states[t-1],states[t],labels[t-1].0,labels[t-1].1,consumer,binding);
    }
}

pub open spec fn lifetime<V>(states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>,consumer:usize,binding:Binding,b:int,u:int)->bool {
    forall|t:int| b<=t<=u ==> {
        &&& states[t].control.fibers[consumer].committed==states[b].control.fibers[consumer].committed
        &&& s::registered(states[t],binding.provider)
        &&& (states[t].control.fibers[binding.provider].phase==Phase::Active || states[t].control.fibers[binding.provider].phase==Phase::Unloading)
        &&& states[t].tables[binding.provider].dom()==states[b].tables[binding.provider].dom()
        &&& states[t].tables[binding.provider].dom().contains(Port{key:binding.key,realm:binding.realm})
        &&& (t<labels.len() ==> {
            &&& labels[t]!=(binding.provider,r::Rule::Unload)
            &&& s::registered(states[t+1],binding.provider)
            &&& states[t].tables[binding.provider].dom()==states[t+1].tables[binding.provider].dom()
            &&& forall|key:Port| states[t].tables[binding.provider].dom().contains(key)
                && states[t].tables[binding.provider][key]!=states[t+1].tables[binding.provider][key]
                ==> labels[t].0!=binding.provider && states[t].control.fibers[labels[t].0].dependencies.contains(key)
        })
    }
}

#[verifier::rlimit(20)]
#[verifier::spinoff_prover]
pub proof fn dependency_lifetime<V>(states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>,consumer:usize,binding:Binding,b:int,u:int)
    requires trace(states,labels),order::episode(states,consumer,b,u),states[b].control.fibers[consumer].committed.contains(binding),
    ensures lifetime(states,labels,consumer,binding,b,u),
{
    preservation(states,labels);episode_boundaries(states,labels,consumer,b,u);
    e::begin_establishes_provider_pin(at(states,labels,b-1),states[b-1],states[b],consumer,binding);
    assert forall|t:int| b<=t<=u implies {
        &&& states[t].control.fibers[consumer].committed==states[b].control.fibers[consumer].committed
        &&& s::registered(states[t],binding.provider)
        &&& (states[t].control.fibers[binding.provider].phase==Phase::Active || states[t].control.fibers[binding.provider].phase==Phase::Unloading)
        &&& states[t].tables[binding.provider].dom()==states[b].tables[binding.provider].dom()
        &&& states[t].tables[binding.provider].dom().contains(Port{key:binding.key,realm:binding.realm})
        &&& (t<labels.len() ==> {
            &&& labels[t]!=(binding.provider,r::Rule::Unload)
            &&& s::registered(states[t+1],binding.provider)
            &&& states[t].tables[binding.provider].dom()==states[t+1].tables[binding.provider].dom()
            &&& forall|key:Port| states[t].tables[binding.provider].dom().contains(key)
                && states[t].tables[binding.provider][key]!=states[t+1].tables[binding.provider][key]
                ==> labels[t].0!=binding.provider && states[t].control.fibers[labels[t].0].dependencies.contains(key)
        })
    } by {
        committed_interval(states,labels,consumer,b,t);pinned_interval(states,labels,consumer,binding,b,t);
        if t<labels.len() {
            let model=at(states,labels,t);
            order::pinned_table_step(model,states[t],states[t+1],labels[t].0,labels[t].1,consumer,binding);
            e::committed_provider_blocks_unload(model,states[t],states[t+1],consumer,binding.provider,binding);
        }
    }
}

/// Theorem 70, independent of continuation representation and a fixed Model.
pub proof fn episode_ordering<V>(states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>,consumer:usize,binding:Binding,b:int,u:int,pb:int,pu:int)
    requires trace(states,labels),order::episode(states,consumer,b,u),states[b].control.fibers[consumer].committed.contains(binding),
        order::episode(states,binding.provider,pb,pu),pb<=b<=pu,
    ensures lifetime(states,labels,consumer,binding,b,u),pb<b,pu<labels.len() ==> u<pu,
        forall|key:Port| #[trigger] states[b-1].control.fibers[consumer].dependencies.contains(key)
            ==> exists|provider:usize| #[trigger] s::publishes(states[b-1],key,provider),
{
    dependency_lifetime(states,labels,consumer,binding,b,u);preservation(states,labels);
    episode_boundaries(states,labels,consumer,b,u);episode_boundaries(states,labels,binding.provider,pb,pu);
    order::begin_provided(at(states,labels,b-1),states[b-1],states[b],consumer);
    e::begin_establishes_provider_pin(at(states,labels,b-1),states[b-1],states[b],consumer,binding);
    if pb==b {assert(states[b].control.fibers[binding.provider].phase==Phase::Loading);}
    if pu<labels.len() && pu<=u {assert(labels[pu]!=(binding.provider,r::Rule::Unload));}
}

pub proof fn no_loading_reentry<V>(states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>,n:usize,b:int,t:int)
    requires trace(states,labels),0<=b<=t<states.len(),forall|j:int| b<=j<=t ==> order::installed(states[j],n),
        states[b].control.fibers[n].phase!=Phase::Loading,
    ensures states[t].control.fibers[n].phase!=Phase::Loading,
        states[b].control.fibers[n].phase==Phase::Unloading ==> states[t].control.fibers[n].phase==Phase::Unloading,
    decreases t-b,
{
    if t>b {
        no_loading_reentry(states,labels,n,b,t-1);preservation(states,labels);
        order::phase_step(at(states,labels,t-1),states[t-1],states[t],labels[t-1].0,labels[t-1].1,n);
    }
}
pub open spec fn coherent_interval<V>(states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>,n:usize,b:int,u:int)->bool {
    let end=order::loading_end(states,n,b,u);
    &&& b<=end<=u
    &&& forall|t:int| b<=t<=u ==> (states[t].control.fibers[n].phase==Phase::Loading)==(t<=end)
    &&& forall|t:int| b<=t<=end && t<labels.len() && (labels[t]==(n,r::Rule::Iter) || labels[t]==(n,r::Rule::Finish))
        ==> s::target(states[t],n,states[b].control.fibers[n].committed)
    &&& (end<u ==> {
        &&& ((labels[end]==(n,r::Rule::Finish) && states[end+1].control.fibers[n].phase==Phase::Active)
            || (labels[end]==(n,r::Rule::Divert) && states[end+1].control.fibers[n].phase==Phase::Unloading))
        &&& states[end+1].control.fibers[n].committed==states[b].control.fibers[n].committed
    })
}

// Isolate the Iter/Finish target clause from the rest of a model's effect
// admissibility. The interval proof only needs this single-step consequence.
proof fn loading_step_target<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,n:usize,rule:r::Rule)
    requires s::step(model,a,z,n,rule),rule==r::Rule::Iter || rule==r::Rule::Finish,
    ensures s::target(a,n,a.control.fibers[n].committed),
{
}

/// Theorem 71's complete phase/coherence clauses. Eventual closure and the
/// recovery equation are separate obligations, not consequences of a prefix.
pub proof fn loading_coherence<V>(states:Seq<s::State<V>>,labels:Seq<(usize,r::Rule)>,n:usize,b:int,u:int)
    requires trace(states,labels),order::episode(states,n,b,u),
    ensures coherent_interval(states,labels,n,b,u),
{
    hide(s::step);hide(inv::admissible_step);
    preservation(states,labels);episode_boundaries(states,labels,n,b,u);
    order::loading_end_bounds(states,n,b,u);let end=order::loading_end(states,n,b,u);
    assert forall|t:int| b<=t<=u implies (states[t].control.fibers[n].phase==Phase::Loading)==(t<=end) by {
        if t>end {no_loading_reentry(states,labels,n,end+1,t);}
    }
    assert forall|t:int| b<=t<=end && t<labels.len() && (labels[t]==(n,r::Rule::Iter) || labels[t]==(n,r::Rule::Finish))
        implies s::target(states[t],n,states[b].control.fibers[n].committed) by {
        committed_interval(states,labels,n,b,t);
        loading_step_target(at(states,labels,t),states[t],states[t+1],n,labels[t].1);
    }
    if end<u {
        order::phase_step(at(states,labels,end),states[end],states[end+1],labels[end].0,labels[end].1,n);
        committed_interval(states,labels,n,b,end+1);
    }
}

/// Erase only continuation indices for receipt interpretation. No assertion
/// relates the placeholder iterator 0 to an original I or a fixed interpreter.
pub open spec fn receipt_history<U,I>(history:Seq<dl::Entry<U,I>>)->Seq<g::Entry<U>> {
    Seq::new(history.len(),|i:int|g::Entry {
        input:history[i].input,iterator:0,
        landed:g::Landed {state:history[i].landed.state,receipt:history[i].landed.receipt,next:dl::marker(history[i].landed.next)},
    })
}
pub proof fn restore_erasure<U,I>(history:Seq<dl::Entry<U,I>>,tokens:Seq<nat>,input:s::State<U>,actor:usize)
    ensures dl::restore(history,tokens,input,actor)==g::restore(receipt_history(history),tokens,input,actor),
    decreases tokens.len(),
{
    if tokens.len()>0 && tokens.last()<history.len() && history[tokens.last() as int].landed.receipt.actor==actor {
        let receipt=history[tokens.last() as int].landed.receipt;
        if g::undo(receipt,input).is_some() {restore_erasure(history,tokens.drop_last(),g::undo(receipt,input).unwrap(),actor);}
    }
}

/// A mathematical witness for one transition. Its sole observed forward call
/// returns the actual result, while each undo interprets its actual receipt.
/// Arbitrary off-domain completion is not an executable recovery fallback.
pub open spec fn local_model<U>(result:s::Yield<U>,history:Seq<g::Entry<U>>)->s::Model<U> {
    s::Model {iterate:|actor:usize,id:nat,input:s::State<U>|result,undo:(g::catalog_model(history)).undo}
}
pub proof fn local_restore_agreement<U>(result:s::Yield<U>,history:Seq<g::Entry<U>>,tokens:Seq<nat>,input:s::State<U>,actor:usize)
    requires g::restore(history,tokens,input,actor).is_some(),
    ensures g::restore_calls_agree(local_model(result,history),history,tokens,input,actor),
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let next=g::undo(history[tokens.last() as int].landed.receipt,input).unwrap();
        local_restore_agreement(result,history,tokens.drop_last(),next,actor);
    }
}
pub open spec fn dependent_model<A,X,U,B,I>(lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,a:dl::Configuration<U,I>,actor:usize)->s::Model<U> {
    let out=dl::entry(lib,programs,a,actor).landed;
    local_model(s::Yield {state:out.state,inverse:a.history.len(),next:dl::marker(out.next)},receipt_history(a.history))
}

/// The adapter derives the step's primitive admissibility from the actual
/// dependent node and actual partial restoration, not from a footprint premise.
pub proof fn dependent_step<A,X,U,B,I>(lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,
    a:dl::Configuration<U,I>,z:dl::Configuration<U,I>,actor:usize,rule:r::Rule)
    requires dl::well_formed(lib,programs,a),dl::step(lib,programs,a,z,actor,rule),
    ensures s::step(dependent_model(lib,programs,a,actor),a.state,z.state,actor,rule),
        inv::admissible_step(dependent_model(lib,programs,a,actor),a.state,z.state,actor,rule),
        step(a.state,z.state,actor,rule),
{
    let model=dependent_model(lib,programs,a,actor);
    dl::frame(lib,programs,a,z,actor,rule);
    if dl::landing(a,z,rule) {
        let node=programs(actor)(a.current[actor].unwrap());
        dl::stage_projection(lib,node,a.state,actor);g::run_preservation(dl::stage(lib,node),a.state,actor);
        assert(a.state.iterators[actor].is_some());
    }
    if rule==r::Rule::Insert {
        inv::insert_preservation(a.state,z.state,actor);
        assert(s::auxiliary_frame(a.state,z.state,actor)) by {
            assert forall|n:usize| n!=actor && s::registered(a.state,n) implies z.state.tables[n]==a.state.tables[n]
                && z.state.effects[n]==a.state.effects[n] && z.state.iterators[n]==a.state.iterators[n]
                && z.state.accumulators[n]==a.state.accumulators[n] by { }
        }
    }
    if rule==r::Rule::Unload {
        restore_erasure(a.history,a.state.accumulators[actor],a.state,actor);
        let result=s::Yield {state:dl::entry(lib,programs,a,actor).landed.state,inverse:a.history.len(),next:dl::marker(dl::entry(lib,programs,a,actor).landed.next)};
        local_restore_agreement(result,receipt_history(a.history),a.state.accumulators[actor],a.state,actor);
        g::restore_refines(model,receipt_history(a.history),a.state.accumulators[actor],a.state,actor);
    }
    match rule {
        r::Rule::Insert=>{assert(s::step(model,a.state,z.state,actor,rule));},
        r::Rule::Retire=>{assert(s::step(model,a.state,z.state,actor,rule));},
        r::Rule::Remove=>{assert(s::step(model,a.state,z.state,actor,rule));},
        r::Rule::Begin=>{assert(a.state.effects[actor]==0);assert(s::step(model,a.state,z.state,actor,rule));},
        r::Rule::Iter=>{assert(s::step(model,a.state,z.state,actor,rule));},
        r::Rule::Finish=>{assert(s::step(model,a.state,z.state,actor,rule));},
        r::Rule::Divert=>{assert(s::step(model,a.state,z.state,actor,rule));},
        r::Rule::Leave=>{assert(s::step(model,a.state,z.state,actor,rule));},
        r::Rule::Unload=>{assert(s::step(model,a.state,z.state,actor,rule));},
        _=>{},
    }
    assert(inv::admissible_step(model,a.state,z.state,actor,rule));
}

pub open spec fn project<U,I>(states:Seq<dl::Configuration<U,I>>)->Seq<s::State<U>> {
    Seq::new(states.len(),|i:int|states[i].state)
}
pub proof fn dependent_trace<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,
    states:Seq<dl::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires d::primitive_theory(eq,lib),dl::execution(lib,programs,states,labels),dl::well_formed(lib,programs,states.first()),
    ensures trace(project(states),labels),
{
    dl::execution_preservation(eq,lib,programs,states,labels);
    assert forall|i:int| 0<=i<labels.len() implies step(project(states)[i],project(states)[i+1],labels[i].0,labels[i].1) by {
        dependent_step(lib,programs,states[i],states[i+1],labels[i].0,labels[i].1);
    }
}

pub open spec fn dependent_operation<A,X,U,B,I>(lib:dl::Library<A,X,U,B>,node:dl::Node<A,X,U,B,I>,input:s::State<U>,actor:usize,provider:usize,key:Port)->bool {
    match node {
        d::Node::Operation {operation,..}=>(lib.key)(operation)==key && g::resolve(input,actor,key)==Some(provider),
        _=>false,
    }
}
pub proof fn dependent_forward_origin<A,X,U,B,I>(lib:dl::Library<A,X,U,B>,node:dl::Node<A,X,U,B,I>,input:s::State<U>,actor:usize,provider:usize,key:Port)
    requires dl::run(lib,node,input,actor).is_some(),actor!=provider,go::changed(input,dl::run(lib,node,input,actor).unwrap().state,provider,key),
    ensures dependent_operation(lib,node,input,actor,provider,key),go::operation_receipt(dl::run(lib,node,input,actor).unwrap().receipt,provider,key),
{
    dl::stage_projection(lib,node,input,actor);go::forward_operation_origin(dl::stage(lib,node),input,actor,provider,key);
}
pub proof fn dependent_retained_origin<A,X,U,B,I>(lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,history:Seq<dl::Entry<U,I>>,token:nat,provider:usize,key:Port)
    requires dl::history_sound(lib,programs,history),token<history.len(),go::operation_receipt(history[token as int].landed.receipt,provider,key),
    ensures dependent_operation(lib,programs(history[token as int].landed.receipt.actor)(history[token as int].iterator),
        history[token as int].input,history[token as int].landed.receipt.actor,provider,key),
{
    let recorded=history[token as int];let actor=recorded.landed.receipt.actor;let node=programs(actor)(recorded.iterator);
    assert(dl::run(lib,node,recorded.input,actor)==Some(recorded.landed));
    dl::stage_projection(lib,node,recorded.input,actor);
    match node {d::Node::Operation {..}=>{},_=>{},}
}

/// Receipt erasure preserves every token, captured receipt and intermediate
/// input. Thus changed_invocation still describes this restoration's real
/// evaluation, not membership of an unused token in a journal.
pub open spec fn dependent_origin<A,X,U,B,I>(lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,
    a:dl::Configuration<U,I>,z:dl::Configuration<U,I>,actor:usize,rule:r::Rule,provider:usize,key:Port)->bool {
    (dl::landing(a,z,rule)
        && dependent_operation(lib,programs(actor)(a.current[actor].unwrap()),a.state,actor,provider,key)
        && go::operation_receipt(dl::entry(lib,programs,a,actor).landed.receipt,provider,key)
        && go::changed(a.state,dl::entry(lib,programs,a,actor).landed.state,provider,key))
    || (rule==r::Rule::Unload && exists|token:nat,before:s::State<U>,after:s::State<U>| {
        &&& go::changed_invocation(receipt_history(a.history),a.state.accumulators[actor],a.state,actor,provider,key,token,before,after)
        &&& dependent_operation(lib,programs(actor)(a.history[token as int].iterator),a.history[token as int].input,actor,provider,key)
    })
}
pub proof fn dependent_step_origin<A,X,U,B,I>(lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,
    a:dl::Configuration<U,I>,z:dl::Configuration<U,I>,actor:usize,rule:r::Rule,provider:usize,key:Port)
    requires dl::well_formed(lib,programs,a),dl::step(lib,programs,a,z,actor,rule),actor!=provider,go::changed(a.state,z.state,provider,key),
    ensures dependent_origin(lib,programs,a,z,actor,rule,provider,key),
{
    dl::frame(lib,programs,a,z,actor,rule);
    if dl::landing(a,z,rule) {
        dependent_forward_origin(lib,programs(actor)(a.current[actor].unwrap()),a.state,actor,provider,key);
    } else if rule==r::Rule::Unload {
        restore_erasure(a.history,a.state.accumulators[actor],a.state,actor);
        let h=receipt_history(a.history);
        go::restore_operation_origin(h,a.state.accumulators[actor],a.state,actor,provider,key);
        let (token,before,after)=choose|token:nat,before:s::State<U>,after:s::State<U>|
            go::changed_invocation(h,a.state.accumulators[actor],a.state,actor,provider,key,token,before,after);
        dependent_retained_origin(lib,programs,a.history,token,provider,key);
        assert(dependent_operation(lib,programs(actor)(a.history[token as int].iterator),a.history[token as int].input,actor,provider,key));
    } else {assert(a.state.tables[provider]==z.state.tables[provider]);}
}

/// No initial invented journal is accepted here: each retained record was
/// appended by a real earlier landing with its original continuation index I.
pub proof fn dependent_history_entry_origin<A,X,U,B,I>(lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,
    states:Seq<dl::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,token:nat)
    requires dl::execution(lib,programs,states,labels),states.first().history.len()==0,token<states.last().history.len(),
    ensures exists|i:int| 0<=i<labels.len() && dl::landing(states[i],states[i+1],labels[i].1)
        && states.last().history[token as int]==dl::entry(lib,programs,states[i],labels[i].0),
    decreases labels.len(),
{
    assert(labels.len()>0);
    let previous=states.drop_last();let prefix=labels.drop_last();
    let a=previous.last();let z=states.last();let actor=labels.last().0;let rule=labels.last().1;
    assert(dl::execution(lib,programs,previous,prefix)) by {
        assert forall|i:int| 0<=i<prefix.len() implies dl::step(lib,programs,previous[i],previous[i+1],prefix[i].0,prefix[i].1) by { }
    }
    assert(z.history==a.history || z.history==a.history.push(dl::entry(lib,programs,a,actor)));
    if token<a.history.len() {
        dependent_history_entry_origin(lib,programs,previous,prefix,token);
        let i=choose|i:int| 0<=i<prefix.len() && dl::landing(previous[i],previous[i+1],prefix[i].1)
            && previous.last().history[token as int]==dl::entry(lib,programs,previous[i],prefix[i].0);
        assert(z.history[token as int]==a.history[token as int]);
        assert(dl::landing(states[i],states[i+1],labels[i].1)
            && states.last().history[token as int]==dl::entry(lib,programs,states[i],labels[i].0));
    } else {
        assert(token==a.history.len());assert(dl::landing(a,z,rule));
        assert(z.history[token as int]==dl::entry(lib,programs,a,actor));assert(a==states[labels.len()-1]);
    }
}

/// The invoked receipt's original forward node occurred strictly before this
/// restoration. This is stronger than history_sound's pure interpreter equality.
pub proof fn dependent_invocation_prior_landing<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,
    states:Seq<dl::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,t:int,actor:usize,provider:usize,key:Port,
    token:nat,before:s::State<U>,after:s::State<U>)
    requires d::primitive_theory(eq,lib),dl::execution(lib,programs,states,labels),dl::well_formed(lib,programs,states.first()),
        states.first().history.len()==0,0<=t<states.len(),
        go::changed_invocation(receipt_history(states[t].history),states[t].state.accumulators[actor],states[t].state,actor,provider,key,token,before,after),
    ensures exists|i:int| 0<=i<t && labels[i].0==actor && dl::landing(states[i],states[i+1],labels[i].1)
        && states[t].history[token as int]==dl::entry(lib,programs,states[i],actor)
        && dependent_operation(lib,programs(actor)(states[i].current[actor].unwrap()),states[i].state,actor,provider,key),
{
    dl::execution_preservation(eq,lib,programs,states,labels);
    let prefix=states.take(t+1);let steps=labels.take(t);
    assert(dl::execution(lib,programs,prefix,steps)) by {
        assert forall|i:int| 0<=i<steps.len() implies dl::step(lib,programs,prefix[i],prefix[i+1],steps[i].0,steps[i].1) by { }
    }
    dependent_history_entry_origin(lib,programs,prefix,steps,token);
    let i=choose|i:int| 0<=i<steps.len() && dl::landing(prefix[i],prefix[i+1],steps[i].1)
        && prefix.last().history[token as int]==dl::entry(lib,programs,prefix[i],steps[i].0);
    dl::frame(lib,programs,states[i],states[i+1],labels[i].0,labels[i].1);
    assert(labels[i].0==actor);
    dependent_retained_origin(lib,programs,states[t].history,token,provider,key);
    assert(dependent_operation(lib,programs(actor)(states[i].current[actor].unwrap()),states[i].state,actor,provider,key));
}

/// Main arbitrary-I bridge. The source execution carries exact continuation
/// identities; the projection only forgets their identity for lifecycle facts.
/// Every changed provider value retains its concrete operation provenance.
pub proof fn dependent_episode_ordering<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:dl::Library<A,X,U,B>,programs:dl::Programs<A,X,U,B,I>,
    states:Seq<dl::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,consumer:usize,binding:Binding,b:int,u:int,pb:int,pu:int)
    requires d::primitive_theory(eq,lib),dl::execution(lib,programs,states,labels),dl::well_formed(lib,programs,states.first()),
        order::episode(project(states),consumer,b,u),states[b].state.control.fibers[consumer].committed.contains(binding),
        order::episode(project(states),binding.provider,pb,pu),pb<=b<=pu,
    ensures lifetime(project(states),labels,consumer,binding,b,u),pb<b,pu<labels.len() ==> u<pu,
        coherent_interval(project(states),labels,consumer,b,u),
        forall|key:Port| #[trigger] states[b-1].state.control.fibers[consumer].dependencies.contains(key)
            ==> exists|provider:usize| #[trigger] s::publishes(states[b-1].state,key,provider),
        forall|t:int,key:Port| b<=t<=u && t<labels.len() && states[t].state.tables[binding.provider].dom().contains(key)
            && states[t].state.tables[binding.provider][key]!=states[t+1].state.tables[binding.provider][key]
            ==> dependent_origin(lib,programs,states[t],states[t+1],labels[t].0,labels[t].1,binding.provider,key),
{
    dependent_trace(eq,lib,programs,states,labels);dl::execution_preservation(eq,lib,programs,states,labels);
    episode_ordering(project(states),labels,consumer,binding,b,u,pb,pu);loading_coherence(project(states),labels,consumer,b,u);
    assert forall|t:int,key:Port| b<=t<=u && t<labels.len() && states[t].state.tables[binding.provider].dom().contains(key)
        && states[t].state.tables[binding.provider][key]!=states[t+1].state.tables[binding.provider][key]
        implies dependent_origin(lib,programs,states[t],states[t+1],labels[t].0,labels[t].1,binding.provider,key) by {
        dependent_step_origin(lib,programs,states[t],states[t+1],labels[t].0,labels[t].1,binding.provider,key);
    }
}

} // verus!
