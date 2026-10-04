//! Actual Lemma 67(3): entangled actors have no value effect during Loading.
//!
//! The committed-provider phase invariant is derived from the complete mixed
//! trace, including real child creation and strict restoration. It is stronger
//! than structural well-formedness alone and is not a caller-supplied history
//! or replay conclusion.
#[cfg(verus_keep_ghost)]
use crate::{
    entangled as e, grammar_recovery as gr, lifecycle_ordering as order, mixed_grammar as g,
    mixed_recovery as recovery, observational_execution as execution, observational_grammar as og,
    observational_lift as ol, projection as p, refinement as r, semantics as s, Binding, Phase,
    Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn all_pinned<U>(state:s::State<U>)->bool {
    forall|owner:usize| gr::installed(state,owner) ==> gr::pinned(state,owner)
}

pub proof fn pin_step<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),all_pinned(a.state),g::step(lib,programs,a,z,actor,rule),
    ensures all_pinned(z.state),
{
    ol::configuration_preservation(eq,lib,programs,a,z,actor,rule);
    ol::step_refines(eq,lib,programs,a,z,actor,rule);
    assert forall|owner:usize| gr::installed(z.state,owner) implies gr::pinned(z.state,owner) by {
        if gr::installed(a.state,owner) {
            assert(gr::pinned(a.state,owner));
            execution::episode_step(eq,lib,programs,a,z,actor,rule,owner);
        } else {
            order::installation_step(g::local_model(lib,programs,a),a.state,z.state,actor,rule,owner);
            assert(actor==owner && rule==r::Rule::Begin);
            execution::begin_pin(eq,lib,programs,a,z,owner);
        }
    }
}

pub proof fn trace_pins<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    states:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires og::primitive_theory(eq,lib),g::execution(lib,programs,states,labels),states.first()==g::empty(),
    ensures forall|i:int| 0<=i<states.len() ==> all_pinned(states[i].state),
    decreases labels.len(),
{
    ol::from_empty_safe(eq,lib,programs,states,labels);
    if labels.len()>0 {
        let before=states.drop_last();let steps=labels.drop_last();
        assert(g::execution(lib,programs,before,steps)) by {
            assert forall|i:int| 0<=i<steps.len() implies g::step(lib,programs,before[i],before[i+1],steps[i].0,steps[i].1) by {}
        }
        trace_pins(eq,lib,programs,before,steps);
        pin_step(eq,lib,programs,before.last(),states.last(),labels.last().0,labels.last().1);
        assert forall|i:int| 0<=i<states.len() implies all_pinned(states[i].state) by {
            if i<before.len() {assert(states[i]==before[i]);} else {assert(i==states.len()-1);}
        }
    }
}

pub open spec fn entangled<U>(state:s::State<U>,owner:usize,actor:usize)->bool {
    exists|key:Port| (state.control.fibers[owner].provisions.contains(key) && state.control.fibers[actor].dependencies.contains(key))
        || (state.control.fibers[actor].provisions.contains(key) && state.control.fibers[owner].dependencies.contains(key))
}

/// A Loading provider cannot have an installed consumer. Conversely every
/// provider of the Loading actor is already Active or Unloading and held by
/// the actor's actual committed view. These facts eliminate every effect rule.
pub proof fn loading_identity<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,owner:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),all_pinned(a.state),g::step(lib,programs,a,z,actor,rule),
        s::registered(a.state,owner),s::registered(a.state,actor),owner!=actor,
        a.state.control.fibers[owner].phase==Phase::Loading,entangled(a.state,owner,actor),
    ensures rule==r::Rule::Retire || rule==r::Rule::Remove || rule==r::Rule::Leave,
        !g::landing(a,z,rule),rule!=r::Rule::Unload,
        recovery::step_word(lib,programs,a,z,actor,rule)==Seq::<e::Action<U>>::empty(),
        p::project(a.state,ISet::full())==p::project(z.state,ISet::full()),
{
    let state=a.state;let control=state.control;
    let key=choose|key:Port| (control.fibers[owner].provisions.contains(key) && control.fibers[actor].dependencies.contains(key))
        || (control.fibers[actor].provisions.contains(key) && control.fibers[owner].dependencies.contains(key));
    if control.fibers[actor].provisions.contains(key) && control.fibers[owner].dependencies.contains(key) {
        let binding=choose|binding:Binding| control.fibers[owner].committed.contains(binding) && binding.key==key.key && binding.realm==key.realm;
        assert(control.fibers[binding.provider].provisions.contains(key));assert(binding.provider==actor);
        assert(gr::pinned(state,owner));
        assert(control.fibers[actor].phase==Phase::Active || control.fibers[actor].phase==Phase::Unloading);
        assert(r::relied(control,actor));
    } else {
        assert(control.fibers[owner].provisions.contains(key) && control.fibers[actor].dependencies.contains(key));
        if control.fibers[actor].phase!=Phase::Inactive {
            let binding=choose|binding:Binding| control.fibers[actor].committed.contains(binding) && binding.key==key.key && binding.realm==key.realm;
            assert(control.fibers[binding.provider].provisions.contains(key));assert(binding.provider==owner);
            assert(gr::pinned(state,actor));assert(false);
        }
        assert(control.fibers[actor].phase==Phase::Inactive);
        if rule==r::Rule::Begin {
            let view=z.state.control.fibers[actor].committed;
            let binding=choose|binding:Binding| view.contains(binding) && binding.key==key.key && binding.realm==key.realm;
            assert(s::publishes(state,key,binding.provider));
            assert(control.fibers[binding.provider].provisions.contains(key));assert(binding.provider==owner);assert(false);
        }
    }
    assert(rule==r::Rule::Retire || rule==r::Rule::Remove || rule==r::Rule::Leave);
    execution::step_projection(eq,lib,programs,a,z,actor,rule);
}

/// Reachable-trace form: no extra pinning invariant, successful erasure, or
/// callback independence premise is supplied by the caller.
pub proof fn actual_loading_identity<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    states:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,index:int,owner:usize)
    requires og::primitive_theory(eq,lib),g::execution(lib,programs,states,labels),states.first()==g::empty(),0<=index<labels.len(),
        s::registered(states[index].state,owner),s::registered(states[index].state,labels[index].0),owner!=labels[index].0,
        states[index].state.control.fibers[owner].phase==Phase::Loading,entangled(states[index].state,owner,labels[index].0),
    ensures labels[index].1==r::Rule::Retire || labels[index].1==r::Rule::Remove || labels[index].1==r::Rule::Leave,
        recovery::step_word(lib,programs,states[index],states[index+1],labels[index].0,labels[index].1)==Seq::<e::Action<U>>::empty(),
        p::project(states[index].state,ISet::full())==p::project(states[index+1].state,ISet::full()),
{
    ol::from_empty_safe(eq,lib,programs,states,labels);trace_pins(eq,lib,programs,states,labels);
    loading_identity(eq,lib,programs,states[index],states[index+1],labels[index].0,labels[index].1,owner);
}

/// Retiring the provider of two Loading clients is a real permitted step and
/// keeps their already modified shared value at 15.
#[verifier::spinoff_prover]
pub proof fn actual_provider_retirement()
    ensures {
        let a=crate::mixed_iteration_exchange::example_trace().last();
        let z=crate::mixed_orchestration::retire(a,0);
        &&& a.state.control.fibers[1].phase==Phase::Loading
        &&& entangled(a.state,1,0)
        &&& g::step(crate::recovery_examples::library(),crate::mixed_iteration_exchange::example_programs(),a,z,0,r::Rule::Retire)
        &&& p::project(a.state,ISet::full())==p::project(z.state,ISet::full())
        &&& z.state.tables[0][crate::mixed_iteration_exchange::example_key()]==15
    },
{
    use crate::mixed_iteration_exchange as example;
    use crate::recovery_examples as primitive;
    example::example_execution();example::shared_provider();primitive::primitive_theory();
    og::exact_theory(primitive::equality(),primitive::library());
    let states=example::example_trace();let labels=example::example_labels();
    ol::from_empty_safe(primitive::equality(),primitive::library(),example::example_programs(),states,labels);
    trace_pins(primitive::equality(),primitive::library(),example::example_programs(),states,labels);
    reveal(example::example_trace);
    let a=states.last();let z=crate::mixed_orchestration::retire(a,0);
    assert(entangled(a.state,1,0)) by {
        assert(a.state.control.fibers[0].provisions.contains(example::example_key()));
        assert(a.state.control.fibers[1].dependencies.contains(example::example_key()));
    }
    assert(g::step(primitive::library(),example::example_programs(),a,z,0,r::Rule::Retire));
    loading_identity(primitive::equality(),primitive::library(),example::example_programs(),a,z,0,r::Rule::Retire,1);
}

} // verus!
