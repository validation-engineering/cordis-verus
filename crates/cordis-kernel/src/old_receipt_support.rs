//! Historical inputs and strict crossing for authentic old operation receipts.
//!
//! Historical typing and permission come from actual execution from empty.
//! Current successful undo supplies the old operation's current declaration;
//! no equality of old and current interfaces or target success is assumed.
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_grammar as d, dependent_lift as dep, foreign_unload as fu, grammar_lift as lift,
    mixed_grammar as g, mixed_observational_runs as obs, mixed_observational_transport as mt,
    mixed_syntax as syntax, observational_grammar as og, observational_lift as ol,
    partial_independence as p, preservation as inv, providing_owner_deletion as source_proof,
    refinement as r, semantics as s, shared_execution as shared, shared_replay as replay, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn input_supported<A,X,U,B,I>(lib:g::Library<A,X,U,B>,entry:g::Entry<U,I>)->bool {
    inv::well_formed(entry.input) && dep::typed(lib,entry.input) && dep::finite_context(entry.input)
}

pub open spec fn history_inputs<A,X,U,B,I>(lib:g::Library<A,X,U,B>,history:Seq<g::Entry<U,I>>)->bool {
    forall|i:int| 0<=i<history.len() ==> input_supported(lib,#[trigger] history[i])
}

pub proof fn inputs_step<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),history_inputs(lib,a.history),g::step(lib,programs,a,z,actor,rule),
    ensures history_inputs(lib,z.history),
{
    ol::frame(eq,lib,programs,a,z,actor,rule);
    assert forall|i:int| 0<=i<z.history.len() implies input_supported(lib,#[trigger] z.history[i]) by {
        if i<a.history.len() {assert(z.history[i]==a.history[i]);}
        else {assert(g::landing(a,z,rule));assert(i==a.history.len());assert(z.history[i]==g::entry(lib,programs,a,actor));}
    }
}

/// This includes obsolete entries, not just tokens in current live journals.
pub proof fn history_from_empty<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires og::primitive_theory(eq,lib),g::execution(lib,programs,source,labels),source.first()==g::empty::<U,I>(),
    ensures g::well_formed(lib,programs,source.last()),mt::permitted_history(lib,programs,source.last().history),history_inputs(lib,source.last().history),
    decreases labels.len(),
{
    g::empty_well_formed(lib,programs);
    if labels.len()>0 {
        let prefix=source.drop_last();let previous=labels.drop_last();let label=labels.last();
        assert(g::execution(lib,programs,prefix,previous)) by {
            assert forall|i:int| 0<=i<previous.len() implies g::step(lib,programs,prefix[i],prefix[i+1],previous[i].0,previous[i].1) by {}
        }
        history_from_empty(eq,lib,programs,prefix,previous);
        inputs_step(eq,lib,programs,prefix.last(),source.last(),label.0,label.1);
        mt::permitted_step(eq,lib,programs,prefix.last(),source.last(),label.0,label.1);
        ol::configuration_preservation(eq,lib,programs,prefix.last(),source.last(),label.0,label.1);
    } else {assert(source.len()==1);}
}

pub proof fn history_receipt_reflexive<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,i:int)
    requires og::primitive_theory(eq,lib),g::execution(lib,programs,source,labels),source.first()==g::empty::<U,I>(),0<=i<source.last().history.len(),
    ensures obs::receipt_related(eq,source.last().history[i].landed.receipt,source.last().history[i].landed.receipt),
{
    history_from_empty(eq,lib,programs,source,labels);
    mt::history_reflexive(eq,lib,programs,source.last().history,i);
}

/// A successful current inverse still resolves the operation's captured key.
/// Only that one key is transferred to the current declarations.
pub proof fn old_permitted_now<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    old:g::Entry<U,I>,current:s::State<U>,actor:usize)
    requires inv::well_formed(current),s::registered(current,actor),g::owner(old.landed.receipt)==actor,
        replay::operational_mixed(programs(actor)(old.iterator)),
        syntax::permitted(lib,dep::declarations(old.input,actor),old.input.control.fibers[actor].provisions,programs(actor)(old.iterator)),
        g::run(lib,programs(actor)(old.iterator),old.input,actor)==Some(old.landed),g::undo(old.landed.receipt,current).is_some(),
    ensures d::permitted(lib,dep::declarations(current,actor),current.control.fibers[actor].provisions,replay::dependent(programs(actor)(old.iterator))),
{
    let node=replay::dependent(programs(actor)(old.iterator));
    match node {
        d::Node::Operation {operation,..}=>{
            let key=(lib.key)(operation);
            assert(lift::resolve(current,actor,key).is_some());
            lift::resolution_sound(current,actor,key);
            assert(dep::declarations(current,actor).contains(key));
        },
        _=>{},
    }
}

/// Strict generator crossing for an old Unit/Operation receipt that actually
/// executes now. The own receipt may also be a Provision. Its actual birth
/// input fixes the own private interface; old foreign interfaces may differ.
pub proof fn cross_old_entry<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    own:g::Entry<U,I>,old:g::Entry<U,I>,current:s::State<U>,owner:usize,actor:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),
        source_proof::historical(lib,programs,own,owner,current.control.fibers[owner].provisions),g::owner(own.landed.receipt)==owner,
        input_supported(lib,old),g::owner(old.landed.receipt)==actor,replay::operational_mixed(programs(actor)(old.iterator)),
        syntax::permitted(lib,dep::declarations(old.input,actor),old.input.control.fibers[actor].provisions,programs(actor)(old.iterator)),
        g::run(lib,programs(actor)(old.iterator),old.input,actor)==Some(old.landed),
        inv::well_formed(current),source_proof::separated(current,owner),s::registered(current,actor),actor!=owner,
        g::undo(old.landed.receipt,current).is_some(),
    ensures p::respects(p::context_eq(eq),shared::flat(old.landed.receipt)),
        p::commutes(p::context_eq(eq),shared::flat(old.landed.receipt),fu::entry_pair(lib,programs,own,owner).forward),
        p::commutes(p::context_eq(eq),shared::flat(old.landed.receipt),fu::entry_pair(lib,programs,own,owner).inverse),
        p::commutes(p::context_eq(eq),fu::entry_pair(lib,programs,own,owner).forward,shared::flat(old.landed.receipt)),
        p::commutes(p::context_eq(eq),fu::entry_pair(lib,programs,own,owner).inverse,shared::flat(old.landed.receipt)),
{
    let left=replay::dependent(programs(owner)(own.iterator));
    let right=replay::dependent(programs(actor)(old.iterator));
    old_permitted_now(lib,programs,old,current,actor);
    replay::context_equivalence(eq,lib);
    replay::actual_receipt_projects(lib,left,own.input,owner);
    replay::actual_receipt_projects(lib,right,old.input,actor);
    replay::stage_respects(eq,lib,right,dep::declarations(current,actor),current.control.fibers[actor].provisions);
    assert(p::generators(dep::stage(lib,right)).contains(shared::flat(old.landed.receipt)));
    p::generator_respects(eq,dep::stage(lib,right),shared::flat(old.landed.receipt));
    assert(own.input.control.fibers[owner].provisions.disjoint(dep::declarations(current,actor)));
    source_proof::stages_cross(eq,lib,left,right,dep::declarations(own.input,owner),own.input.control.fibers[owner].provisions,
        dep::declarations(current,actor),current.control.fibers[actor].provisions,true,false);
    let call=fu::entry_pair(lib,programs,own,owner);let inverse=shared::flat(old.landed.receipt);
    assert(p::generators(dep::stage(lib,left)).contains(call.forward));
    assert(p::generators(dep::stage(lib,left)).contains(call.inverse));
    p::commute_symmetric(p::context_eq(eq),call.forward,inverse);
    p::commute_symmetric(p::context_eq(eq),call.inverse,inverse);
}

} // verus!
