//! Internal table-journal cleanup before and after the deleted owner begins.
//!
//! Installed owners use the real no-user guard to separate a foreign revoked
//! provision. Inactive owners have no live own journal; actual journal
//! provenance derives both own words as identities. Neither branch assumes a
//! successful target inverse or a legal surviving execution.
#[cfg(verus_keep_ghost)]
use crate::{
    foreign_unload as fu, grammar_lift as lift, internal_old_unload as base, mixed_grammar as g,
    mixed_observational_runs as obs, mixed_observational_transport as mt,
    observational_grammar as og, observational_lift as ol, old_journal_closure as closure,
    old_provision_journal as table, old_provision_support as prov, old_receipt_support as support,
    partial_independence as pi, preservation as inv, projection as p,
    providing_owner_deletion as source_proof, providing_owner_execution as execution,
    providing_owner_transport as target_proof, refinement as r, semantics as s,
    shared_execution as sh, shared_replay as replay, shared_unload_execution as history,
    strict_batch_recovery as batch, strict_journal as sj, Phase, Port,
};
use vstd::prelude::*;

verus! {

/// Each real own landing contributes one forward and one inverse.
pub proof fn word_lengths<S>(events:Seq<sj::Event<S>>)
    ensures batch::forwards(events).len()==sj::journal(events).len(),
    decreases events.len(),
{
    if events.len()>0 {word_lengths(events.drop_last());}
}

/// Structural lifecycle metadata and the actual own journal force both words
/// to be empty before Begin. No equality of current table values is assumed.
pub proof fn inactive_words<U,I>(a:g::Configuration<U,I>,actions:Seq<fu::Action<IMap<Port,U>>>,owner:usize)
    requires s::shaped(a.state),s::registered(a.state,owner),a.state.control.fibers[owner].phase==Phase::Inactive,
        sh::receipt_word(a.history,a.state.accumulators[owner])==sj::journal(fu::events(actions)),
    ensures a.state.accumulators[owner].len()==0,sj::journal(fu::events(actions)).len()==0,batch::forwards(fu::events(actions)).len()==0,
        batch::redo(fu::events(actions))==fu::identity(),batch::undo(fu::events(actions))==fu::identity(),
{
    let es=fu::events(actions);assert(a.state.accumulators[owner].len()==0);assert(sj::journal(es).len()==0);word_lengths(es);
    assert(batch::redo(es) =~= fu::identity());assert(batch::undo(es) =~= fu::identity());
}

/// Equal current observations transport an arbitrary-age actual table journal.
/// Only the foreign actor's domain may shrink, identically on both sides.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn restore_equal<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    left:Seq<g::Entry<U,I>>,right:Seq<g::Entry<U,I>>,tokens:Seq<nat>,offset:nat,owner:usize,actor:usize,source:s::State<U>,target:s::State<U>)
    requires og::primitive_theory(eq,lib),inv::well_formed(source),inv::well_formed(target),actor!=owner,
        s::registered(source,actor),s::registered(target,actor),source.control.fibers[actor]==target.control.fibers[actor],
        history::histories(eq,left,right,offset,owner),table::table_tokens(programs,left,tokens,actor),g::restore(left,tokens,source,actor).is_some(),
        mt::permitted_history(lib,programs,left),g::history_sound(lib,programs,left),pi::context_eq(eq)(p::project(source,ISet::full()),p::project(target,ISet::full())),
    ensures {
        let a=g::restore(left,tokens,source,actor).unwrap();let b=g::restore(right,history::rename(left,offset,owner,tokens),target,actor);
        &&& b.is_some() && inv::well_formed(a) && inv::well_formed(b.unwrap())
        &&& a.control==source.control && b.unwrap().control==target.control
        &&& forall|n:usize| s::registered(target,n) && n!=actor ==> b.unwrap().tables[n].dom()==target.tables[n].dom()
        &&& forall|n:usize| s::registered(source,n) && n!=actor ==> a.tables[n].dom()==source.tables[n].dom()
        &&& forall|n:usize| s::registered(source,n) && s::registered(target,n) && source.tables[n].dom()==target.tables[n].dom() ==> a.tables[n].dom()==b.unwrap().tables[n].dom()
        &&& pi::context_eq(eq)(p::project(a,ISet::full()),p::project(b.unwrap(),ISet::full()))
    },
    decreases tokens.len(),
{
    replay::context_equivalence(eq,lib);history::rename_laws(left,offset,owner,tokens,0);
    if tokens.len()>0 {
        let token=tokens.last();let mapped=history::index(left,offset,owner,token);let e=left[token as int];let receipt=e.landed.receipt;let replacement=right[mapped as int].landed.receipt;
        assert(token<left.len());assert(g::owner(receipt)==actor);assert(match receipt {g::Receipt::Table {..}=>true,_=>false});
        if token<offset {reveal(history::index);assert(mapped==token);assert(right[mapped as int]==e);mt::history_reflexive(eq,lib,programs,left,token as int);}
        else {assert(g::owner(left[token as int].landed.receipt)!=owner);}
        assert(mapped<right.len());assert(obs::receipt_related(eq,receipt,replacement));
        let reference=p::project(source,ISet::full());fu::table_inverse_projects(receipt,source);table::one_frame(receipt,source,actor);
        if history::simple(receipt) {history::one_inverse(eq,receipt,replacement,source,target,actor,reference);}
        else {
            if let g::Receipt::Table {receipt:record}=receipt {if let lift::Inverse::Provision {key}=record.inverse {
                assert(receipt==prov::receipt::<U>(actor,key));assert(replacement==receipt);
                prov::cut_contract(eq,actor,key);prov::one_inverse(eq,source,target,actor,key,reference);prov::domains_frame(source,target,actor,key);
            }}
        }
        let sa=g::undo(receipt,source).unwrap();let ta=g::undo(replacement,target).unwrap();
        assert(pi::context_eq(eq)(p::project(sa,ISet::full()),p::project(ta,ISet::full())));
        assert(table::table_tokens(programs,left,tokens.drop_last(),actor)) by {
            assert forall|i:int| #![trigger tokens.drop_last()[i]] 0<=i<tokens.drop_last().len() implies {
                let token=tokens.drop_last()[i];let entry=left[token as int];token<left.len() && g::owner(entry.landed.receipt)==actor && source_proof::table_node(programs(actor)(entry.iterator))
            } by {assert(tokens.drop_last()[i]==tokens[i]);}
        }
        restore_equal(eq,lib,programs,left,right,tokens.drop_last(),offset,owner,actor,sa,ta);
        assert forall|n:usize|s::registered(source,n) && s::registered(target,n) && source.tables[n].dom()==target.tables[n].dom() implies
            g::restore(left,tokens,source,actor).unwrap().tables[n].dom()==g::restore(right,history::rename(left,offset,owner,tokens),target,actor).unwrap().tables[n].dom() by {
            assert(s::registered(sa,n));assert(s::registered(ta,n));assert(sa.tables[n].dom()==ta.tables[n].dom());
        }
        assert forall|n:usize|s::registered(source,n) && n!=actor implies g::restore(left,tokens,source,actor).unwrap().tables[n].dom()==source.tables[n].dom() by {assert(s::registered(sa,n));}
        assert forall|n:usize|s::registered(target,n) && n!=actor implies g::restore(right,history::rename(left,offset,owner,tokens),target,actor).unwrap().tables[n].dom()==target.tables[n].dom() by {assert(s::registered(ta,n));}
    }
}

/// Dispatch on the actual owner's current phase. The inactive branch derives
/// an empty own batch from its real journal, not from a global profile premise.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn restore_any<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,target:g::Configuration<U,I>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize,actor:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),base::prepared(eq,lib,programs,a,target,actions,offset,owner),actor!=owner,
        g::restore(a.history,a.state.accumulators[actor],a.state,actor).is_some(),!r::relied(a.state.control,actor),s::registered(a.state,actor),
        table::table_tokens(programs,a.history,a.state.accumulators[actor],actor),
        sh::receipt_word(a.history,a.state.accumulators[owner])==sj::journal(fu::events(actions)),
        forall|i:int| offset<=i<a.history.len() && g::owner(#[trigger] a.history[i].landed.receipt)==owner ==> r::interface_same(a.history[i].input.control.fibers[owner],a.state.control.fibers[owner]),
    ensures {
        let tokens=a.state.accumulators[actor];let sa=g::restore(a.history,tokens,a.state,actor).unwrap();let tb=g::restore(target.history,history::rename(a.history,offset,owner,tokens),target.state,actor);let es=fu::events(actions);
        &&& tb.is_some() && inv::well_formed(sa) && inv::well_formed(tb.unwrap())
        &&& sa.control==a.state.control && tb.unwrap().control==target.state.control
        &&& forall|n:usize| s::registered(target.state,n) && n!=actor ==> tb.unwrap().tables[n].dom()==target.state.tables[n].dom()
        &&& forall|n:usize| s::registered(a.state,n) && n!=actor ==> sa.tables[n].dom()==a.state.tables[n].dom()
        &&& forall|n:usize| s::registered(a.state,n) && s::registered(target.state,n) && a.state.tables[n].dom()==target.state.tables[n].dom() ==> sa.tables[n].dom()==tb.unwrap().tables[n].dom()
        &&& batch::batch(pi::context_eq(eq),batch::redo(es),batch::undo(es),p::project(sa,ISet::full()))
        &&& pi::context_eq(eq)(batch::undo(es)(p::project(sa,ISet::full())).unwrap(),p::project(tb.unwrap(),ISet::full()))
    },
{
    let tokens=a.state.accumulators[actor];let es=fu::events(actions);
    if a.state.control.fibers[owner].phase==Phase::Inactive {
        inactive_words(a,actions,owner);
        assert(pi::context_eq(eq)(p::project(a.state,ISet::full()),p::project(target.state,ISet::full())));
        restore_equal(eq,lib,programs,a.history,target.history,tokens,offset,owner,actor,a.state,target.state);
        replay::context_equivalence(eq,lib);batch::empty_batch(pi::context_eq(eq),p::project(g::restore(a.history,tokens,a.state,actor).unwrap(),ISet::full()));
    } else {table::restore_mixed(eq,lib,programs,a.history,target.history,tokens,actions,offset,owner,actor,a.state,target.state);}
}

pub open spec fn fragment<A,X,U,B,I>(programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)->bool {
    &&& forall|i:int| 0<=i<labels.len() && g::landing(source[i],source[i+1],labels[i].1) ==> {
        let node=programs(labels[i].0)(source[i].current[labels[i].0].unwrap());
        source_proof::table_node(node) && (labels[i].0!=owner ==> replay::operational_mixed(node))
    }
    &&& forall|i:int| #![trigger labels[i]] 0<=i<labels.len() ==> {
        let label=labels[i];
        &&& label.1!=r::Rule::Insert && label.1!=r::Rule::Remove
        &&& (label.1==r::Rule::Unload ==> label.0!=owner && table::table_tokens(programs,source[i].history,source[i].state.accumulators[label.0],label.0))
    }
}


#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn source_metadata<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires og::primitive_theory(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),source_proof::separated(source.first().state,owner),fragment(programs,source,labels,owner),
        support::history_inputs(lib,source.first().history),mt::permitted_history(lib,programs,source.first().history),
    ensures g::well_formed(lib,programs,source.last()),source_proof::separated(source.last().state,owner),
        source.first().state.control.fibers.dom()==source.last().state.control.fibers.dom(),
        forall|n:usize| s::registered(source.first().state,n) ==> r::interface_same(source.first().state.control.fibers[n],source.last().state.control.fibers[n]),
        source.first().history.len()<=source.last().history.len(),
        forall|i:int| 0<=i<source.first().history.len() ==> source.last().history[i]==source.first().history[i],
        forall|i:int| source.first().history.len()<=i<source.last().history.len() ==> source_proof::historical(lib,programs,#[trigger] source.last().history[i],owner,source.first().state.control.fibers[owner].provisions),
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
        source_proof::interface_frame(eq,lib,programs,a,z,label.0,label.1,owner);
        support::inputs_step(eq,lib,programs,a,z,label.0,label.1);mt::permitted_step(eq,lib,programs,a,z,label.0,label.1);
        let before=base::landing_catalogue(lib,programs,prefix,previous,owner);let records=fu::catalog(before);
        assert(actions.drop_last() =~= before);
        if g::landing(a,z,label.1) {
            source_proof::landing_historical(eq,lib,programs,a,z,label.0,label.1,owner);
            let entry=g::entry(lib,programs,a,label.0);let call=fu::entry_pair(lib,programs,entry,owner);
            assert(actions==before.push(fu::Action::Forward {call}));
            assert(fu::fresh_records(lib,programs,z.history,offset,owner) =~= records.push(call));
        } else {assert(z.history==a.history);}
        assert forall|i:int| offset<=i<z.history.len() implies source_proof::historical(lib,programs,#[trigger] z.history[i],owner,source.first().state.control.fibers[owner].provisions) by {
            if i<a.history.len() {assert(z.history[i]==a.history[i]);} else {assert(i==a.history.len());}
        }
        assert forall|n:usize| s::registered(source.first().state,n) implies r::interface_same(source.first().state.control.fibers[n],z.state.control.fibers[n]) by {assert(s::registered(a.state,n));}
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
        if rule==r::Rule::Unload {
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


/// Construct one real target transition, including arbitrary-age Unload.
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub proof fn step_transport<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),base::prepared(eq,lib,programs,a,target,actions,offset,owner),g::step(lib,programs,a,z,actor,rule),
        rule!=r::Rule::Insert,rule!=r::Rule::Remove,
        sh::receipt_word(a.history,a.state.accumulators[owner])==sj::journal(fu::events(actions)),
        forall|i:int| offset<=i<a.history.len() && g::owner(#[trigger] a.history[i].landed.receipt)==owner ==> r::interface_same(a.history[i].input.control.fibers[owner],a.state.control.fibers[owner]),
        g::landing(a,z,rule) ==> source_proof::table_node(programs(actor)(a.current[actor].unwrap())) && (actor!=owner ==> replay::operational_mixed(programs(actor)(a.current[actor].unwrap()))),
        rule==r::Rule::Unload ==> actor!=owner && table::table_tokens(programs,a.history,a.state.accumulators[actor],actor),
    ensures {
        let out=target_proof::advance(lib,programs,a,z,target,actor,rule,owner);
        let action=if g::landing(a,z,rule) {fu::Action::Forward {call:fu::entry_pair(lib,programs,g::entry(lib,programs,a,actor),owner)}} else {fu::Action::Identity};
        &&& g::well_formed(lib,programs,out) && target_proof::related(eq,z,out,offset,owner)
        &&& (sh::keep(actor,rule,owner) ==> g::step(lib,programs,target,out,actor,rule))
        &&& base::synchronized(eq,actions.push(action),z,out)
    },
{
    if rule!=r::Rule::Unload {base::step_transport(eq,lib,programs,a,z,target,actions,offset,owner,actor,rule);}
    else {
        replay::context_equivalence(eq,lib);ol::frame(eq,lib,programs,a,z,actor,rule);ol::configuration_preservation(eq,lib,programs,a,z,actor,rule);
        let out=target_proof::advance(lib,programs,a,z,target,actor,rule,owner);
        base::own_words_push(actions,fu::Action::Identity);
        let tokens=a.state.accumulators[actor];let renamed=history::rename(a.history,offset,owner,tokens);
        restore_any(eq,lib,programs,a,target,actions,offset,owner,actor);
        let source_restored=g::restore(a.history,tokens,a.state,actor).unwrap();let target_restored=g::restore(target.history,renamed,target.state,actor).unwrap();
        p::unique_owner(source_restored);p::unique_owner(target_restored);
        p::lifecycle_edit(source_restored,actor,Phase::Inactive,ISet::empty(),None,Seq::empty(),ISet::full());
        p::lifecycle_edit(target_restored,actor,Phase::Inactive,ISet::empty(),None,Seq::empty(),ISet::full());
        target_proof::no_users(a,target,owner,actor);assert(g::step(lib,programs,target,out,actor,r::Rule::Unload));
        ol::configuration_preservation(eq,lib,programs,target,out,actor,r::Rule::Unload);ol::frame(eq,lib,programs,target,out,actor,r::Rule::Unload);
        assert forall|n:usize| s::registered(z.state,n) && n!=owner implies {
            &&& z.state.tables[n].dom()==out.state.tables[n].dom()
            &&& z.state.control.fibers[n]==out.state.control.fibers[n] && z.current[n]==out.current[n]
        } by {assert(s::registered(a.state,n));assert(s::registered(target.state,n));}
        assert forall|n:usize| s::registered(z.state,n) && n!=owner implies out.state.accumulators[n]==history::rename(z.history,offset,owner,z.state.accumulators[n]) by {
            assert(s::registered(a.state,n));if n==actor {history::rename_laws(a.history,offset,owner,Seq::empty(),0);}
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
        let target=execution::delete(lib,programs,source,labels,owner);let actions=base::landing_catalogue(lib,programs,source,labels,owner);
        &&& g::execution(lib,programs,target,sh::labels_without(labels,owner)) && target.first()==source.first()
        &&& g::well_formed(lib,programs,source.last()) && forall|i:int| 0<=i<target.len() ==> g::well_formed(lib,programs,target[i])
        &&& target_proof::related(eq,source.last(),target.last(),source.first().history.len(),owner)
        &&& base::synchronized(eq,actions,source.last(),target.last())
    },
    decreases labels.len(),
{
    support::history_from_empty(eq,lib,programs,setup,setup_labels);source_metadata(eq,lib,programs,source,labels,owner);
    reveal(execution::delete);reveal(sh::labels_without);
    let target=execution::delete(lib,programs,source,labels,owner);let kept=sh::labels_without(labels,owner);let offset=source.first().history.len();
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
        let before=execution::delete(lib,programs,states,previous,owner);let earlier=sh::labels_without(previous,owner);let input=before.last();
        let prefix=base::landing_catalogue(lib,programs,states,previous,owner);let out=target_proof::advance(lib,programs,a,z,input,actor,rule,owner);
        actual_journal(eq,lib,programs,states,previous,owner);
        step_transport(eq,lib,programs,a,z,input,prefix,offset,owner,actor,rule);
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
        let target=execution::delete(lib,programs,source,labels,owner);let terminal=g::unload(source.last(),owner);
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
    let a=source.last();let target=execution::delete(lib,programs,source,labels,owner);
    closure::close_from_strict_word(eq,lib,programs,a,target.last(),owner);
    closure::append_execution(lib,programs,source,labels,g::unload(a,owner),owner,r::Rule::Unload);
}

} // verus!
