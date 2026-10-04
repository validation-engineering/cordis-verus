//! Actual deletion of a private table episode across registry changes.
//!
//! The owner remains registered. Foreign names may be inserted, retired,
//! unloaded, removed, and reused. Each Insert checks only its new dependencies
//! against the owner's private provisions; source O-Insert supplies provision
//! freshness. Every prefix's separation follows from these local inputs.
//! Historical foreign receipts retain their original input interfaces, so no
//! contract reads the present interface of an already removed foreign name.
#[cfg(verus_keep_ghost)]
use crate::{
    dynamic_table_registry as registry, foreign_provision_transport as fp, foreign_unload as fu,
    generalized_table_deletion as generalized, internal_old_unload as base, mixed_grammar as g,
    mixed_observational_runs as obs, mixed_observational_transport as mt,
    observational_grammar as og, observational_lift as ol, old_journal_closure as closure,
    old_provision_journal as table, old_receipt_support as support, partial_independence as pi,
    projection as p, providing_owner_deletion as source_proof,
    providing_owner_transport as target_proof, refinement as r, semantics as s,
    shared_execution as sh, shared_replay as replay, strict_batch_recovery as batch,
    strict_journal as sj, Phase, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn fragment<A,X,U,B,I>(programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)->bool {
    &&& forall|i:int| 0<=i<labels.len() && g::landing(source[i],source[i+1],labels[i].1) ==> {
        let node=programs(labels[i].0)(source[i].current[labels[i].0].unwrap());
        source_proof::table_node(node)
    }
    &&& forall|i:int| #![trigger labels[i]] 0<=i<labels.len() ==> {
        let label=labels[i];
        &&& ((label.1==r::Rule::Insert || label.1==r::Rule::Remove) ==> registry::guard(source[i],source[i+1],label.0,label.1,owner))
        &&& (label.1==r::Rule::Unload ==> label.0!=owner && table::table_tokens(programs,source[i].history,source[i].state.accumulators[label.0],label.0))
    }
}


/// This constructor retains the source Insert payload and uses a real erase
/// for Remove. Only this owner's non-Retire lifecycle steps are omitted.
pub open spec fn delete<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)->Seq<g::Configuration<U,I>>
    decreases labels.len(),
{
    if labels.len()==0 {seq![source.first()]} else {
        let before=delete(lib,programs,source.drop_last(),labels.drop_last(),owner);let label=labels.last();
        if sh::keep(label.0,label.1,owner) {before.push(registry::advance(lib,programs,source[source.len()-2],source.last(),before.last(),label.0,label.1,owner))}
        else {before}
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn source_metadata<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires og::primitive_theory(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),source_proof::separated(source.first().state,owner),fragment(programs,source,labels,owner),
        support::history_inputs(lib,source.first().history),mt::permitted_history(lib,programs,source.first().history),
    ensures g::well_formed(lib,programs,source.last()),source_proof::separated(source.last().state,owner),
        s::registered(source.last().state,owner),r::interface_same(source.first().state.control.fibers[owner],source.last().state.control.fibers[owner]),
        forall|i:int|0<=i<source.len() ==> g::well_formed(lib,programs,source[i]) && source_proof::separated(source[i].state,owner)
            && r::interface_same(source.first().state.control.fibers[owner],source[i].state.control.fibers[owner]),
        source.first().history.len()<=source.last().history.len(),
        forall|i:int| 0<=i<source.first().history.len() ==> source.last().history[i]==source.first().history[i],
        forall|i:int| source.first().history.len()<=i<source.last().history.len() ==> fp::historical(lib,programs,#[trigger] source.last().history[i],owner,source.first().state.control.fibers[owner].provisions),
        support::history_inputs(lib,source.last().history),mt::permitted_history(lib,programs,source.last().history),
        forall|i:int| source.first().history.len()<=i<source.last().history.len() && g::owner(#[trigger] source.last().history[i].landed.receipt)==owner ==> r::interface_same(source.last().history[i].input.control.fibers[owner],source.last().state.control.fibers[owner]),
        fu::catalog(base::landing_catalogue(lib,programs,source,labels,owner))==fu::fresh_records(lib,programs,source.last().history,source.first().history.len(),owner),
    decreases labels.len(),
{
    let offset=source.first().history.len();let actions=base::landing_catalogue(lib,programs,source,labels,owner);
    if labels.len()==0 {
        assert(source.first()==source.last());assert(fu::fresh_records(lib,programs,source.last().history,offset,owner) =~= Seq::empty());
    } else {
        let prefix=source.drop_last();let previous=labels.drop_last();let label=labels.last();let a=prefix.last();let z=source.last();
        assert(g::execution(lib,programs,prefix,previous));assert(fragment(programs,prefix,previous,owner));
        source_metadata(eq,lib,programs,prefix,previous,owner);
        ol::frame(eq,lib,programs,a,z,label.0,label.1);ol::configuration_preservation(eq,lib,programs,a,z,label.0,label.1);
        if label.1==r::Rule::Insert || label.1==r::Rule::Remove {
            registry::source_frame(eq,lib,programs,a,z,label.0,label.1,owner);
        } else {source_proof::interface_frame(eq,lib,programs,a,z,label.0,label.1,owner);}
        assert(r::interface_same(a.state.control.fibers[owner],z.state.control.fibers[owner]));
        support::inputs_step(eq,lib,programs,a,z,label.0,label.1);mt::permitted_step(eq,lib,programs,a,z,label.0,label.1);
        let before=base::landing_catalogue(lib,programs,prefix,previous,owner);let records=fu::catalog(before);
        assert(actions.drop_last() =~= before);
        if g::landing(a,z,label.1) {
            fp::landing_historical(eq,lib,programs,a,z,label.0,label.1,owner);
            let entry=g::entry(lib,programs,a,label.0);let call=fu::entry_pair(lib,programs,entry,owner);
            assert(actions==before.push(fu::Action::Forward {call}));
            assert(fu::fresh_records(lib,programs,z.history,offset,owner) =~= records.push(call));
        } else {assert(z.history==a.history);}
        assert forall|i:int| offset<=i<z.history.len() implies fp::historical(lib,programs,#[trigger] z.history[i],owner,source.first().state.control.fibers[owner].provisions) by {
            if i<a.history.len() {assert(z.history[i]==a.history[i]);} else {assert(i==a.history.len());}
        }
        assert forall|i:int|0<=i<source.len() implies g::well_formed(lib,programs,source[i]) && source_proof::separated(source[i].state,owner)
            && r::interface_same(source.first().state.control.fibers[owner],source[i].state.control.fibers[owner]) by {
            if i<prefix.len() {assert(source[i]==prefix[i]);}else{assert(i==prefix.len());assert(source[i]==z);}
        }
        assert forall|i:int| offset<=i<z.history.len() && g::owner(#[trigger] z.history[i].landed.receipt)==owner implies r::interface_same(z.history[i].input.control.fibers[owner],z.state.control.fibers[owner]) by {
            if i<a.history.len() {assert(z.history[i]==a.history[i]);} else {assert(i==a.history.len());assert(z.history[i].input==a.state);}
        }
    }
}

/// The own word remains the real live LIFO journal even across old Unloads.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn actual_journal<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires og::primitive_theory(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),source_proof::separated(source.first().state,owner),fragment(programs,source,labels,owner),
        support::history_inputs(lib,source.first().history),mt::permitted_history(lib,programs,source.first().history),source.first().state.control.fibers[owner].phase==Phase::Inactive,
    ensures source_proof::pinned_tokens(source.last().history,source.last().state.accumulators[owner],source.last().state,owner),
        sh::receipt_word(source.last().history,source.last().state.accumulators[owner])==sj::journal(fu::events(base::landing_catalogue(lib,programs,source,labels,owner))),
    decreases labels.len(),
{
    source_metadata(eq,lib,programs,source,labels,owner);
    if labels.len()==0 {assert(source.first()==source.last());assert(source.last().state.accumulators[owner].len()==0);}
    else {
        let states=source.drop_last();let previous=labels.drop_last();let label=labels.last();let a=states.last();let z=source.last();let actor=label.0;let rule=label.1;
        assert(g::execution(lib,programs,states,previous));assert(fragment(programs,states,previous,owner));
        actual_journal(eq,lib,programs,states,previous,owner);source_metadata(eq,lib,programs,states,previous,owner);
        let before=base::landing_catalogue(lib,programs,states,previous,owner);let actions=base::landing_catalogue(lib,programs,source,labels,owner);let es=fu::events(before);
        assert(actions.drop_last() =~= before);assert(fu::events(actions).drop_last() =~= es);
        if rule==r::Rule::Insert || rule==r::Rule::Remove {
            registry::pinned_journal(eq,lib,programs,a,z,actor,rule,owner);
            assert(actions==before.push(fu::Action::Identity));base::own_words_push(before,fu::Action::Identity);
        } else if rule==r::Rule::Unload {
            table::journal_after_foreign(eq,lib,programs,a,z,owner,actor);
            assert(actions.last()==fu::Action::Identity);assert(!fu::events(actions).last().own);
        } else {
            source_proof::journal_step(eq,lib,programs,a,z,es,owner,actor,rule);
            if g::landing(a,z,rule) {
                assert(fu::events(actions).last()==replay::event(lib,programs,a,z,actor,rule,owner));
            } else {
                assert(fu::identity::<IMap<Port,U>>() =~= replay::identity::<U>());
                assert(fu::events(actions).last()==replay::event(lib,programs,a,z,actor,rule,owner));
            }
            assert(fu::events(actions) =~= es.push(replay::event(lib,programs,a,z,actor,rule,owner)));
        }
    }
}


/// All surviving lifecycle steps are constructed, at their original positions.
/// This induction uses actual state values; no catalogue replay is assumed.
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub proof fn delete_execution<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,setup:Seq<g::Configuration<U,I>>,setup_labels:Seq<(usize,r::Rule)>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,setup,setup_labels),setup.first()==g::empty::<U,I>(),setup.last()==source.first(),
        g::execution(lib,programs,source,labels),source_proof::separated(source.first().state,owner),fragment(programs,source,labels,owner),
        source.first().state.control.fibers[owner].phase==Phase::Inactive,source.first().state.tables[owner].is_empty(),
    ensures {
        let target=delete(lib,programs,source,labels,owner);let actions=base::landing_catalogue(lib,programs,source,labels,owner);
        &&& g::execution(lib,programs,target,sh::labels_without(labels,owner)) && target.first()==source.first()
        &&& g::well_formed(lib,programs,source.last()) && forall|i:int| 0<=i<target.len() ==> g::well_formed(lib,programs,target[i])
        &&& target_proof::related(eq,source.last(),target.last(),source.first().history.len(),owner)
        &&& base::synchronized(eq,actions,source.last(),target.last())
    },
    decreases labels.len(),
{
    support::history_from_empty(eq,lib,programs,setup,setup_labels);source_metadata(eq,lib,programs,source,labels,owner);
    reveal(delete);reveal(sh::labels_without);
    let target=delete(lib,programs,source,labels,owner);let kept=sh::labels_without(labels,owner);let offset=source.first().history.len();
    let actions=base::landing_catalogue(lib,programs,source,labels,owner);
    if labels.len()==0 {
        assert(source.len()==1);assert(source.first()==source.last());target_proof::initial_related(lib,programs,source.first(),owner,eq);
        replay::context_equivalence(eq,lib);let x=p::project(source.first().state,ISet::full());batch::empty_batch(pi::context_eq(eq),x);
        assert(batch::redo(fu::events(actions)) =~= fu::identity());assert(batch::undo(fu::events(actions)) =~= fu::identity());
        assert(pi::context_eq(eq)(x,x));
    } else {
        let states=source.drop_last();let previous=labels.drop_last();let label=labels.last();let a=states.last();let z=source.last();let actor=label.0;let rule=label.1;
        assert(g::execution(lib,programs,states,previous));assert(fragment(programs,states,previous,owner));
        delete_execution(eq,lib,programs,setup,setup_labels,states,previous,owner);source_metadata(eq,lib,programs,states,previous,owner);
        let before=delete(lib,programs,states,previous,owner);let earlier=sh::labels_without(previous,owner);let input=before.last();
        let prefix=base::landing_catalogue(lib,programs,states,previous,owner);let out=registry::advance(lib,programs,a,z,input,actor,rule,owner);
        actual_journal(eq,lib,programs,states,previous,owner);
        if rule==r::Rule::Insert || rule==r::Rule::Remove {
            registry::synchronized_registry(eq,lib,programs,a,z,input,prefix,offset,owner,actor,rule);
        } else {generalized::step_transport(eq,lib,programs,a,z,input,prefix,offset,owner,actor,rule);}
        if sh::keep(actor,rule,owner) {
            assert(target==before.push(out));assert(kept==earlier.push(label));
            assert forall|i:int| 0<=i<target.len() implies g::well_formed(lib,programs,target[i]) by {
                if i<before.len() {assert(target[i]==before[i]);} else {assert(i==before.len());}
            }
            assert(g::execution(lib,programs,target,kept)) by {
                assert forall|i:int| 0<=i<kept.len() implies g::step(lib,programs,target[i],target[i+1],kept[i].0,kept[i].1) by {
                    if i<earlier.len() {assert(target[i]==before[i]);assert(target[i+1]==before[i+1]);}
                    else {assert(i==earlier.len());assert(target[i]==before.last());}
                }
            }
        } else {assert(out==input);}
    }
}

/// The owner's final actual Unload closes the whole constructed deletion,
/// including arbitrary-age interior foreign table journals, before or after Begin.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn closed_deletion<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,setup:Seq<g::Configuration<U,I>>,setup_labels:Seq<(usize,r::Rule)>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,setup,setup_labels),setup.first()==g::empty::<U,I>(),setup.last()==source.first(),
        g::execution(lib,programs,source,labels),source_proof::separated(source.first().state,owner),fragment(programs,source,labels,owner),
        source.first().state.control.fibers[owner].phase==Phase::Inactive,source.first().state.tables[owner].is_empty(),source.last().state.control.fibers[owner].phase==Phase::Unloading,
    ensures {
        let target=delete(lib,programs,source,labels,owner);let terminal=g::unload(source.last(),owner);
        &&& g::restore(source.last().history,source.last().state.accumulators[owner],source.last().state,owner).is_some()
        &&& g::step(lib,programs,source.last(),terminal,owner,r::Rule::Unload) && g::well_formed(lib,programs,terminal)
        &&& g::execution(lib,programs,source.push(terminal),labels.push((owner,r::Rule::Unload)))
        &&& g::execution(lib,programs,target,sh::labels_without(labels,owner)) && target.first()==source.first()
        &&& forall|i:int| 0<=i<target.len() ==> g::well_formed(lib,programs,target[i])
        &&& terminal.state.control==target.last().state.control && obs::tables_related(eq,terminal.state,target.last().state)
        &&& terminal.state.tables[owner].is_empty() && target.last().state.tables[owner].is_empty()
    },
{
    delete_execution(eq,lib,programs,setup,setup_labels,source,labels,owner);
    support::history_from_empty(eq,lib,programs,setup,setup_labels);source_metadata(eq,lib,programs,source,labels,owner);actual_journal(eq,lib,programs,source,labels,owner);
    let a=source.last();let target=delete(lib,programs,source,labels,owner);
    closure::close_from_strict_word(eq,lib,programs,a,target.last(),owner);
    closure::append_execution(lib,programs,source,labels,g::unload(a,owner),owner,r::Rule::Unload);
}

} // verus!
