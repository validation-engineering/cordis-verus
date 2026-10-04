//! Old foreign receipts after a genuinely interleaved deletion window.
//!
//! New foreign Unit/Operation landings and new foreign Unloads are admitted by
//! the existing actual-source fragment. Their original forward/inverse pairs
//! derive crossings with both accumulated own words. Target replay success is
//! not assumed, and old receipts consumed by the final Unload remain original
//! history entries with original token numbers.
#[cfg(verus_keep_ghost)]
use crate::{
    calculus as c, foreign_unload as fu, mixed_grammar as g, mixed_observational_runs as obs,
    observational_grammar as og, observational_lift as ol, old_journal_closure as closure,
    old_journal_unload as old, old_receipt_support as support, partial_independence as pi,
    projection as p, providing_owner_deletion as source_proof,
    providing_owner_execution as execution, providing_owner_transport as target_proof,
    refinement as r, selective_foreign_recovery as selective, semantics as s,
    shared_execution as sh, shared_replay as replay, shared_unload_execution as history,
    strict_batch_recovery as batch, strict_journal as sj, Phase, Port,
};
use vstd::prelude::*;

verus! {

/// A foreign action is either a new actual call, an authentic new receipt's
/// inverse, or a control identity. All three cross each historical own pair.
pub proof fn foreign_crosses_record<S>(eq:spec_fn(S,S)->bool,actions:Seq<fu::Action<S>>,initial:S,j:int)
    requires c::equivalence(eq),selective::local_source(eq,actions,initial),actions.len()>0,
        0<=j<fu::catalog(actions.drop_last()).len(),fu::catalog(actions.drop_last())[j].own,
        !fu::event(fu::catalog(actions.drop_last()),actions.last()).own,
    ensures {
        let record=fu::catalog(actions.drop_last())[j];let event=fu::event(fu::catalog(actions.drop_last()),actions.last());
        &&& fu::respectful(eq,record)
        &&& pi::commutes(eq,record.forward,event.forward) && pi::commutes(eq,record.inverse,event.forward)
    },
{
    let prefix=actions.drop_last();let records=fu::catalog(prefix);let record=records[j];
    selective::catalog_theory(eq,prefix,initial);
    match actions.last() {
        fu::Action::Forward {call}=>{assert(!call.own);assert(fu::compatible(eq,record,call));},
        fu::Action::Inverse {token}=>{assert(!records[token as int].own);assert(fu::compatible(eq,record,records[token as int]));},
        fu::Action::Identity=>{fu::identity_contract(eq,record.forward);fu::identity_contract(eq,record.inverse);},
    }
}

pub proof fn foreign_crosses_words<S>(eq:spec_fn(S,S)->bool,actions:Seq<fu::Action<S>>,initial:S)
    requires c::equivalence(eq),selective::local_source(eq,actions,initial),actions.len()>0,
        !fu::event(fu::catalog(actions.drop_last()),actions.last()).own,
    ensures {
        let prefix=fu::events(actions.drop_last());let event=fu::event(fu::catalog(actions.drop_last()),actions.last());
        &&& pi::commutes(eq,event.forward,batch::redo(prefix)) && pi::commutes(eq,event.forward,batch::undo(prefix))
    },
{
    let prior=actions.drop_last();let records=fu::catalog(prior);let es=fu::events(prior);let event=fu::event(records,actions.last());
    old::forward_origins(prior);fu::journal_origins(prior);
    assert forall|i:int| 0<=i<batch::forwards(es).len() implies pi::respects(eq,#[trigger] batch::forwards(es)[i])
        && pi::commutes(eq,batch::forwards(es)[i],event.forward) by {
        let j=choose|j:int| 0<=j<records.len() && records[j].own && records[j].forward==batch::forwards(es)[i];
        foreign_crosses_record(eq,actions,initial,j);
    }
    assert forall|i:int| 0<=i<sj::journal(es).len() implies pi::respects(eq,#[trigger] sj::journal(es)[i])
        && pi::commutes(eq,sj::journal(es)[i],event.forward) by {
        let j=choose|j:int| 0<=j<records.len() && records[j].own && records[j].inverse==sj::journal(es)[i];
        foreign_crosses_record(eq,actions,initial,j);
    }
    sj::word_commutes(eq,batch::forwards(es),event.forward);sj::word_commutes(eq,sj::journal(es),event.forward);
}

/// The stronger bidirectional batch invariant is derived for all the actual
/// interleaved actions, including foreign inverse calls minted in this window.
pub proof fn batch_source<S>(eq:spec_fn(S,S)->bool,actions:Seq<fu::Action<S>>,initial:S)
    requires c::equivalence(eq),selective::local_source(eq,actions,initial),
    ensures batch::admissible(eq,fu::events(actions),initial),
    decreases actions.len(),
{
    selective::source_invariant(eq,actions,initial);
    if actions.len()>0 {
        let prefix=actions.drop_last();batch_source(eq,prefix,initial);
        let es=fu::events(prefix);let event=fu::event(fu::catalog(prefix),actions.last());
        assert(fu::events(actions).drop_last() =~= es);assert(fu::events(actions).last()==event);
        if !event.own {foreign_crosses_words(eq,actions,initial);}
    }
}

/// Construct a real target suffix after an interleaved source window.
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub proof fn delete_with_old_unload<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    setup:Seq<g::Configuration<U,I>>,setup_labels:Seq<(usize,r::Rule)>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,z:g::Configuration<U,I>,owner:usize,actor:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,setup,setup_labels),setup.first()==g::empty::<U,I>(),setup.last()==source.first(),
        g::execution(lib,programs,source,labels),source_proof::separated(source.first().state,owner),
        source_proof::fragment(programs,source,labels,source.first().history.len(),owner),
        source.first().state.control.fibers[owner].phase==Phase::Inactive,source.first().state.tables[owner].is_empty(),
        actor!=owner,g::step(lib,programs,source.last(),z,actor,r::Rule::Unload),
        old::old_tokens(programs,source.last().history,source.last().state.accumulators[actor],source.first().history.len(),actor),
    ensures {
        let target=execution::delete(lib,programs,source,labels,owner);let out=g::unload(target.last(),actor);
        let es=fu::events(fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner));
        &&& batch::batch(pi::context_eq(eq),batch::redo(es),batch::undo(es),p::project(z.state,ISet::full()))
        &&& pi::context_eq(eq)(batch::undo(es)(p::project(z.state,ISet::full())).unwrap(),p::project(out.state,ISet::full()))
        &&& g::execution(lib,programs,target.push(out),sh::labels_without(labels,owner).push((actor,r::Rule::Unload)))
        &&& g::step(lib,programs,target.last(),out,actor,r::Rule::Unload) && g::well_formed(lib,programs,out)
        &&& target.first()==source.first()
        &&& target_proof::related(eq,z,out,source.first().history.len(),owner)
        &&& target.last().state.accumulators[actor]==source.last().state.accumulators[actor]
        &&& g::restore(target.last().history,target.last().state.accumulators[actor],target.last().state,actor).is_some()
    },
{
    support::history_from_empty(eq,lib,programs,setup,setup_labels);
    old::preserved_permissions(eq,lib,programs,source,labels);
    source_proof::fresh_historical(eq,lib,programs,source,labels,owner);
    source_proof::actual_source(eq,lib,programs,source,labels,owner);
    execution::delete_execution(eq,lib,programs,source,labels,owner);
    let a=source.last();let offset=source.first().history.len();let actions=fu::trace_actions(lib,programs,source,labels,offset,owner);
    let initial=p::project(source.first().state,ISet::full());let es=fu::events(actions);
    replay::context_equivalence(eq,lib);batch_source(pi::context_eq(eq),actions,initial);batch::recovery(pi::context_eq(eq),es,initial);
    let target=execution::delete(lib,programs,source,labels,owner);let input=target.last();let tokens=a.state.accumulators[actor];
    assert(pi::context_eq(eq)(batch::undo(es)(p::project(a.state,ISet::full())).unwrap(),p::project(input.state,ISet::full())));
    assert forall|i:int| 0<=i<offset implies support::input_supported(lib,#[trigger] a.history[i]) by {
        assert(a.history[i]==source.first().history[i]);
    }
    old::old_indices(a.history,offset,owner,tokens);
    assert(input.state.accumulators[actor]==tokens);
    old::restore_old(eq,lib,programs,a.history,input.history,tokens,actions,offset,owner,actor,a.state,input.state);
    let source_restored=g::restore(a.history,tokens,a.state,actor).unwrap();let target_restored=g::restore(input.history,tokens,input.state,actor).unwrap();
    p::unique_owner(source_restored);p::unique_owner(target_restored);
    p::lifecycle_edit(source_restored,actor,Phase::Inactive,ISet::empty(),None,Seq::empty(),ISet::full());
    p::lifecycle_edit(target_restored,actor,Phase::Inactive,ISet::empty(),None,Seq::empty(),ISet::full());
    target_proof::no_users(a,input,owner,actor);
    let out=g::unload(input,actor);assert(g::step(lib,programs,input,out,actor,r::Rule::Unload));
    ol::configuration_preservation(eq,lib,programs,input,out,actor,r::Rule::Unload);
    ol::frame(eq,lib,programs,a,z,actor,r::Rule::Unload);ol::frame(eq,lib,programs,input,out,actor,r::Rule::Unload);
    assert forall|n:usize| s::registered(z.state,n) && n!=owner implies {
        &&& z.state.tables[n].dom()==out.state.tables[n].dom()
        &&& z.state.control.fibers[n]==out.state.control.fibers[n] && z.current[n]==out.current[n]
    } by {assert(s::registered(a.state,n));assert(s::registered(input.state,n));}
    assert forall|n:usize| s::registered(z.state,n) && n!=owner implies out.state.accumulators[n]==history::rename(z.history,offset,owner,z.state.accumulators[n]) by {
        assert(s::registered(a.state,n));if n==actor {history::rename_laws(a.history,offset,owner,Seq::empty(),0);}
    }
    let kept=sh::labels_without(labels,owner);
    assert forall|i:int| 0<=i<kept.push((actor,r::Rule::Unload)).len() implies
        g::step(lib,programs,target.push(out)[i],target.push(out)[i+1],kept.push((actor,r::Rule::Unload))[i].0,kept.push((actor,r::Rule::Unload))[i].1) by {
        if i<kept.len() {assert(target.push(out)[i]==target[i]);assert(target.push(out)[i+1]==target[i+1]);} else {assert(i==kept.len());}
    }
}



/// Close the actual owner episode and recover all final table observations.
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub proof fn closed_deletion<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    setup:Seq<g::Configuration<U,I>>,setup_labels:Seq<(usize,r::Rule)>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,z:g::Configuration<U,I>,owner:usize,actor:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,setup,setup_labels),setup.first()==g::empty::<U,I>(),setup.last()==source.first(),
        g::execution(lib,programs,source,labels),source_proof::separated(source.first().state,owner),
        source_proof::fragment(programs,source,labels,source.first().history.len(),owner),
        source.first().state.control.fibers[owner].phase==Phase::Inactive,source.first().state.tables[owner].is_empty(),
        actor!=owner,g::step(lib,programs,source.last(),z,actor,r::Rule::Unload),
        old::old_tokens(programs,source.last().history,source.last().state.accumulators[actor],source.first().history.len(),actor),
        source.last().state.control.fibers[owner].phase==Phase::Unloading,
    ensures {
        let target=execution::delete(lib,programs,source,labels,owner);let out=g::unload(target.last(),actor);let terminal=g::unload(z,owner);
        &&& g::restore(z.history,z.state.accumulators[owner],z.state,owner).is_some()
        &&& g::step(lib,programs,z,terminal,owner,r::Rule::Unload) && g::well_formed(lib,programs,terminal)
        &&& g::execution(lib,programs,source.push(z).push(terminal),labels.push((actor,r::Rule::Unload)).push((owner,r::Rule::Unload)))
        &&& g::execution(lib,programs,target.push(out),sh::labels_without(labels,owner).push((actor,r::Rule::Unload)))
        &&& g::well_formed(lib,programs,out) && target.first()==source.first()
        &&& terminal.state.control==out.state.control && obs::tables_related(eq,terminal.state,out.state)
        &&& terminal.state.tables[owner].is_empty() && out.state.tables[owner].is_empty()
    },
{
    delete_with_old_unload(eq,lib,programs,setup,setup_labels,source,labels,z,owner,actor);
    support::history_from_empty(eq,lib,programs,setup,setup_labels);
    source_proof::fresh_historical(eq,lib,programs,source,labels,owner);
    source_proof::actual_journal(eq,lib,programs,source,labels,owner);
    let a=source.last();let target=execution::delete(lib,programs,source,labels,owner);let out=g::unload(target.last(),actor);
    let es=fu::events(fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner));
    closure::journal_after_foreign(eq,lib,programs,a,z,owner,actor,source.first().history.len());
    assert(sh::receipt_word(z.history,z.state.accumulators[owner])==sj::journal(es));
    assert(pi::run(sh::receipt_word(z.history,z.state.accumulators[owner]),p::project(z.state,ISet::full())).is_some());
    closure::close_from_strict_word(eq,lib,programs,z,out,owner);let terminal=g::unload(z,owner);
    closure::append_execution(lib,programs,source,labels,z,actor,r::Rule::Unload);
    closure::append_execution(lib,programs,source.push(z),labels.push((actor,r::Rule::Unload)),terminal,owner,r::Rule::Unload);
}

} // verus!
