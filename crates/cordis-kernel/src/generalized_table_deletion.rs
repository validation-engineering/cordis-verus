//! Full table-fragment deletion with new foreign provisions and old receipts.
//!
//! The provenance catalogue records real landings; its identity entry for an
//! Unload is not a value replay. Actual states carry the inductive strict batch,
//! and every target call, receipt, journal cleanup, and final owner recovery is
//! constructed from that witness and the original execution's real guards.
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_grammar as d, dependent_lift as dep, foreign_provision_transport as fp,
    foreign_unload as fu, grammar_lift as lift, internal_old_unload as base,
    internal_table_unload as prior, mixed_grammar as g, mixed_observational_runs as obs,
    mixed_observational_transport as mt, observational_grammar as og, observational_lift as ol,
    old_journal_closure as closure, old_journal_unload as old, old_provision_journal as table,
    old_provision_support as prov, old_receipt_support as support, partial_independence as pi,
    preservation as inv, projection as p, providing_owner_deletion as source_proof,
    providing_owner_execution as execution, providing_owner_transport as target_proof,
    refinement as r, semantics as s, shared_execution as sh, shared_replay as replay,
    shared_unload_execution as history, strict_batch_recovery as batch, strict_journal as sj,
    Phase, Port,
};
use vstd::prelude::*;

verus! {

pub proof fn pending_words<A,X,U,B,I,J>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,entries:Seq<g::Entry<U,I>>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,current:s::State<U>,owner:usize,actor:usize,node:dep::Node<A,X,U,B,J>)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),offset<=entries.len(),fu::catalog(actions)==fu::fresh_records(lib,programs,entries,offset,owner),
        forall|i:int| offset<=i<entries.len() ==> fp::historical(lib,programs,#[trigger] entries[i],owner,current.control.fibers[owner].provisions),
        source_proof::separated(current,owner),s::registered(current,actor),actor!=owner,replay::operational(node),
        d::permitted(lib,dep::declarations(current,actor),current.control.fibers[actor].provisions,node),
    ensures {
        let es=fu::events(actions);let forward=pi::forward(dep::stage(lib,node));
        &&& pi::commutes(pi::context_eq(eq),forward,batch::redo(es)) && pi::commutes(pi::context_eq(eq),forward,batch::undo(es))
        &&& forall|i:int| 0<=i<sj::journal(es).len() ==> pi::stable(eq,dep::stage(lib,node),#[trigger] sj::journal(es)[i])
    },
{
    replay::context_equivalence(eq,lib);let records=fu::catalog(actions);let es=fu::events(actions);let forward=pi::forward(dep::stage(lib,node));
    old::forward_origins(actions);fu::journal_origins(actions);
    assert forall|i:int| 0<=i<batch::forwards(es).len() implies pi::respects(pi::context_eq(eq),#[trigger] batch::forwards(es)[i]) && pi::commutes(pi::context_eq(eq),batch::forwards(es)[i],forward) by {
        let j=choose|j:int|0<=j<records.len() && records[j].own && records[j].forward==batch::forwards(es)[i];let entry=entries[offset as int+j];
        assert(records[j]==fu::entry_pair(lib,programs,entry,owner));fp::restricted_metadata(lib,programs,entry,owner,current.control.fibers[owner].provisions);base::pending_record(eq,lib,programs,entry,current,owner,actor,node);
    }
    assert forall|i:int| 0<=i<sj::journal(es).len() implies pi::respects(pi::context_eq(eq),#[trigger] sj::journal(es)[i]) && pi::commutes(pi::context_eq(eq),sj::journal(es)[i],forward) && pi::stable(eq,dep::stage(lib,node),sj::journal(es)[i]) by {
        let j=choose|j:int|0<=j<records.len() && records[j].own && records[j].inverse==sj::journal(es)[i];let entry=entries[offset as int+j];
        assert(records[j]==fu::entry_pair(lib,programs,entry,owner));fp::restricted_metadata(lib,programs,entry,owner,current.control.fibers[owner].provisions);base::pending_record(eq,lib,programs,entry,current,owner,actor,node);
    }
    sj::word_commutes(pi::context_eq(eq),batch::forwards(es),forward);sj::word_commutes(pi::context_eq(eq),sj::journal(es),forward);
}


pub proof fn receipt_crosses_batch<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    entries:Seq<g::Entry<U,I>>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize,actor:usize,token:nat,current:s::State<U>)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),inv::well_formed(current),source_proof::separated(current,owner),actor!=owner,
        s::registered(current,actor),offset<=entries.len(),token<entries.len(),g::owner(entries[token as int].landed.receipt)==actor,
        support::input_supported(lib,entries[token as int]),mt::permitted_history(lib,programs,entries),g::history_sound(lib,programs,entries),
        replay::operational_mixed(programs(actor)(entries[token as int].iterator)),g::undo(entries[token as int].landed.receipt,current).is_some(),
        fu::catalog(actions)==fu::fresh_records(lib,programs,entries,offset,owner),
        forall|i:int| offset<=i<entries.len() ==> fp::historical(lib,programs,#[trigger] entries[i],owner,current.control.fibers[owner].provisions),
    ensures {
        let f=sh::flat(entries[token as int].landed.receipt);let es=fu::events(actions);
        &&& pi::respects(pi::context_eq(eq),f)
        &&& pi::commutes(pi::context_eq(eq),f,batch::redo(es)) && pi::commutes(pi::context_eq(eq),f,batch::undo(es))
    },
{
    replay::context_equivalence(eq,lib);let records=fu::catalog(actions);let es=fu::events(actions);let old_entry=entries[token as int];let f=sh::flat(old_entry.landed.receipt);
    mt::history_reflexive(eq,lib,programs,entries,token as int);assert(history::simple(old_entry.landed.receipt));
    history::flat_related(eq,old_entry.landed.receipt,old_entry.landed.receipt);
    old::forward_origins(actions);fu::journal_origins(actions);
    assert forall|i:int| 0<=i<batch::forwards(es).len() implies pi::respects(pi::context_eq(eq),#[trigger] batch::forwards(es)[i])
        && pi::commutes(pi::context_eq(eq),batch::forwards(es)[i],f) by {
        let j=choose|j:int| 0<=j<records.len() && records[j].own && records[j].forward==batch::forwards(es)[i];
        let entry=entries[offset as int+j];assert(records[j]==fu::entry_pair(lib,programs,entry,owner));
        assert(g::owner(entry.landed.receipt)==owner);
        fp::restricted_metadata(lib,programs,entry,owner,current.control.fibers[owner].provisions);
        source_proof::historical_contract(eq,lib,programs,entry,owner,current.control.fibers[owner].provisions);
        support::cross_old_entry(eq,lib,programs,entry,old_entry,current,owner,actor);
    }
    assert forall|i:int| 0<=i<sj::journal(es).len() implies pi::respects(pi::context_eq(eq),#[trigger] sj::journal(es)[i])
        && pi::commutes(pi::context_eq(eq),sj::journal(es)[i],f) by {
        let j=choose|j:int| 0<=j<records.len() && records[j].own && records[j].inverse==sj::journal(es)[i];
        let entry=entries[offset as int+j];assert(records[j]==fu::entry_pair(lib,programs,entry,owner));
        assert(g::owner(entry.landed.receipt)==owner);
        fp::restricted_metadata(lib,programs,entry,owner,current.control.fibers[owner].provisions);
        source_proof::historical_contract(eq,lib,programs,entry,owner,current.control.fibers[owner].provisions);
        support::cross_old_entry(eq,lib,programs,entry,old_entry,current,owner,actor);
    }
    sj::word_commutes(pi::context_eq(eq),batch::forwards(es),f);sj::word_commutes(pi::context_eq(eq),sj::journal(es),f);
}

pub proof fn provision_cut_crosses<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    entries:Seq<g::Entry<U,I>>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,current:s::State<U>,owner:usize,actor:usize,key:Port)
    requires og::primitive_theory(eq,lib),inv::well_formed(current),s::registered(current,owner),s::registered(current,actor),owner!=actor,
        current.control.fibers[owner].phase!=Phase::Inactive,!r::relied(current.control,actor),g::undo(prov::receipt::<U>(actor,key),current).is_some(),
        offset<=entries.len(),fu::catalog(actions)==fu::fresh_records(lib,programs,entries,offset,owner),
        forall|i:int| offset<=i<entries.len() ==> fp::historical(lib,programs,#[trigger] entries[i],owner,current.control.fibers[owner].provisions),
        forall|i:int| offset<=i<entries.len() && g::owner(#[trigger] entries[i].landed.receipt)==owner
            ==> r::interface_same(entries[i].input.control.fibers[owner],current.control.fibers[owner]),
    ensures pi::respects(pi::context_eq(eq),prov::cut(key)),pi::commutes(pi::context_eq(eq),prov::cut(key),batch::redo(fu::events(actions))),
        pi::commutes(pi::context_eq(eq),prov::cut(key),batch::undo(fu::events(actions))),
{
    replay::context_equivalence(eq,lib);prov::cut_contract(eq,actor,key);old::forward_origins(actions);fu::journal_origins(actions);
    let records=fu::catalog(actions);let es=fu::events(actions);
    assert forall|i:int| 0<=i<batch::forwards(es).len() implies pi::respects(pi::context_eq(eq),#[trigger] batch::forwards(es)[i])
        && pi::commutes(pi::context_eq(eq),batch::forwards(es)[i],prov::cut(key)) by {
        let j=choose|j:int|0<=j<records.len() && records[j].own && records[j].forward==batch::forwards(es)[i];
        let entry=entries[offset as int+j];assert(records[j]==fu::entry_pair(lib,programs,entry,owner));fp::restricted_metadata(lib,programs,entry,owner,current.control.fibers[owner].provisions);prov::entry_cross(eq,lib,programs,entry,current,owner,actor,key);
    }
    assert forall|i:int| 0<=i<sj::journal(es).len() implies pi::respects(pi::context_eq(eq),#[trigger] sj::journal(es)[i])
        && pi::commutes(pi::context_eq(eq),sj::journal(es)[i],prov::cut(key)) by {
        let j=choose|j:int|0<=j<records.len() && records[j].own && records[j].inverse==sj::journal(es)[i];
        let entry=entries[offset as int+j];assert(records[j]==fu::entry_pair(lib,programs,entry,owner));fp::restricted_metadata(lib,programs,entry,owner,current.control.fibers[owner].provisions);prov::entry_cross(eq,lib,programs,entry,current,owner,actor,key);
    }
    sj::word_commutes(pi::context_eq(eq),batch::forwards(es),prov::cut(key));sj::word_commutes(pi::context_eq(eq),sj::journal(es),prov::cut(key));
}

/// Restore the same logical journal using each side's authentic receipt.
/// Source success is a fact of the original step; target success is proved.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn restore_mixed<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    left:Seq<g::Entry<U,I>>,right:Seq<g::Entry<U,I>>,tokens:Seq<nat>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize,actor:usize,source:s::State<U>,target:s::State<U>)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),inv::well_formed(source),inv::well_formed(target),
        source_proof::separated(source,owner),actor!=owner,s::registered(target,actor),source.control.fibers[actor]==target.control.fibers[actor],s::registered(source,actor),
        source.control.fibers[owner].phase!=Phase::Inactive,!r::relied(source.control,actor),
        history::histories(eq,left,right,offset,owner),table::table_tokens(programs,left,tokens,actor),g::restore(left,tokens,source,actor).is_some(),
        mt::permitted_history(lib,programs,left),g::history_sound(lib,programs,left),
        support::history_inputs(lib,left),
        fu::catalog(actions)==fu::fresh_records(lib,programs,left,offset,owner),
        forall|i:int| offset<=i<left.len() ==> fp::historical(lib,programs,#[trigger] left[i],owner,source.control.fibers[owner].provisions),
        forall|i:int| offset<=i<left.len() && g::owner(#[trigger] left[i].landed.receipt)==owner
            ==> r::interface_same(left[i].input.control.fibers[owner],source.control.fibers[owner]),
        batch::batch(pi::context_eq(eq),batch::redo(fu::events(actions)),batch::undo(fu::events(actions)),p::project(source,ISet::full())),
        pi::context_eq(eq)(batch::undo(fu::events(actions))(p::project(source,ISet::full())).unwrap(),p::project(target,ISet::full())),
    ensures {
        let a=g::restore(left,tokens,source,actor).unwrap();let b=g::restore(right,history::rename(left,offset,owner,tokens),target,actor);
        &&& b.is_some() && inv::well_formed(a) && inv::well_formed(b.unwrap())
        &&& a.control==source.control && b.unwrap().control==target.control
        &&& forall|n:usize| s::registered(target,n) && n!=actor ==> b.unwrap().tables[n].dom()==target.tables[n].dom()
        &&& forall|n:usize| s::registered(source,n) && n!=actor ==> a.tables[n].dom()==source.tables[n].dom()
        &&& forall|n:usize| s::registered(source,n) && s::registered(target,n) && source.tables[n].dom()==target.tables[n].dom()
            ==> a.tables[n].dom()==b.unwrap().tables[n].dom()
        &&& batch::batch(pi::context_eq(eq),batch::redo(fu::events(actions)),batch::undo(fu::events(actions)),p::project(a,ISet::full()))
        &&& pi::context_eq(eq)(batch::undo(fu::events(actions))(p::project(a,ISet::full())).unwrap(),p::project(b.unwrap(),ISet::full()))
    },
    decreases tokens.len(),
{
    replay::context_equivalence(eq,lib);history::rename_laws(left,offset,owner,tokens,0);
    if tokens.len()>0 {
        let token=tokens.last();let mapped=history::index(left,offset,owner,token);
        let e=left[token as int];let receipt=e.landed.receipt;let replacement=right[mapped as int].landed.receipt;let es=fu::events(actions);
        assert(token<left.len());assert(g::owner(receipt)==actor);assert(match receipt {g::Receipt::Table {..}=>true,_=>false});
        if token<offset {
            reveal(history::index);assert(mapped==token);assert(right[mapped as int]==e);
            mt::history_reflexive(eq,lib,programs,left,token as int);
        } else {assert(g::owner(left[token as int].landed.receipt)!=owner);}
        assert(mapped<right.len());assert(obs::receipt_related(eq,receipt,replacement));
        let before=p::project(source,ISet::full());let reference=batch::undo(es)(before).unwrap();
        fu::table_inverse_projects(receipt,source);table::one_frame(receipt,source,actor);let sa=g::undo(receipt,source).unwrap();
        if history::simple(receipt) {
            assert(replay::operational_mixed(programs(actor)(e.iterator)));
            receipt_crosses_batch(eq,lib,programs,left,actions,offset,owner,actor,token,source);
            batch::foreign_cross(pi::context_eq(eq),batch::redo(es),batch::undo(es),sh::flat(receipt),before);
            history::one_inverse(eq,receipt,replacement,source,target,actor,reference);
        } else {
            if let g::Receipt::Table {receipt:table}=receipt {
                if let lift::Inverse::Provision {key}=table.inverse {
                    assert(receipt==prov::receipt::<U>(actor,key));assert(replacement==receipt);
                    provision_cut_crosses(eq,lib,programs,left,actions,offset,source,owner,actor,key);
                    prov::cut_contract(eq,actor,key);
                    batch::foreign_cross(pi::context_eq(eq),batch::redo(es),batch::undo(es),prov::cut(key),before);
                    prov::one_inverse(eq,source,target,actor,key,reference);
                    prov::domains_frame(source,target,actor,key);
                }
            }
        }
        let ta=g::undo(replacement,target).unwrap();
        assert(pi::context_eq(eq)(batch::undo(es)(p::project(sa,ISet::full())).unwrap(),p::project(ta,ISet::full())));
        assert(sa.control==source.control);
        assert(source_proof::separated(sa,owner)) by {
            assert forall|n:usize| s::registered(sa,n) && n!=owner implies crate::dependent_lift::declarations(sa,n).disjoint(sa.control.fibers[owner].provisions) by {
                assert(s::registered(source,n));assert(crate::dependent_lift::declarations(sa,n)==crate::dependent_lift::declarations(source,n));
            }
        }
        assert(table::table_tokens(programs,left,tokens.drop_last(),actor)) by {
            assert forall|i:int| #![trigger tokens.drop_last()[i]] 0<=i<tokens.drop_last().len() implies {
                let token=tokens.drop_last()[i];let e=left[token as int];
                &&& token<left.len() && g::owner(e.landed.receipt)==actor
                &&& source_proof::table_node(programs(actor)(e.iterator))
            } by {assert(tokens.drop_last()[i]==tokens[i]);}
        }
        restore_mixed(eq,lib,programs,left,right,tokens.drop_last(),actions,offset,owner,actor,sa,ta);
        assert forall|n:usize|s::registered(source,n) && s::registered(target,n) && source.tables[n].dom()==target.tables[n].dom() implies
            g::restore(left,tokens,source,actor).unwrap().tables[n].dom()==g::restore(right,history::rename(left,offset,owner,tokens),target,actor).unwrap().tables[n].dom() by {
            assert(s::registered(sa,n));assert(s::registered(ta,n));assert(sa.tables[n].dom()==ta.tables[n].dom());
        }
        assert forall|n:usize| s::registered(source,n) && n!=actor implies g::restore(left,tokens,source,actor).unwrap().tables[n].dom()==source.tables[n].dom() by {
            assert(s::registered(sa,n));
        }
        assert forall|n:usize| s::registered(target,n) && n!=actor implies g::restore(right,history::rename(left,offset,owner,tokens),target,actor).unwrap().tables[n].dom()==target.tables[n].dom() by {
            assert(s::registered(ta,n));
        }
    }
}


pub open spec fn prepared<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,target:g::Configuration<U,I>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize)->bool {
    &&& g::well_formed(lib,programs,a) && g::well_formed(lib,programs,target)
    &&& target_proof::related(eq,a,target,offset,owner) && source_proof::separated(a.state,owner)
    &&& support::history_inputs(lib,a.history) && mt::permitted_history(lib,programs,a.history)
    &&& offset<=a.history.len() && fu::catalog(actions)==fu::fresh_records(lib,programs,a.history,offset,owner)
    &&& forall|i:int| offset<=i<a.history.len() ==> fp::historical(lib,programs,#[trigger] a.history[i],owner,a.state.control.fibers[owner].provisions)
    &&& base::synchronized(eq,actions,a,target)
}

/// Dispatch on the actual owner's current phase. The inactive branch derives
/// an empty own batch from its real journal, not from a global profile premise.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn restore_any<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,target:g::Configuration<U,I>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize,actor:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),prepared(eq,lib,programs,a,target,actions,offset,owner),actor!=owner,
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
        prior::inactive_words(a,actions,owner);
        assert(pi::context_eq(eq)(p::project(a.state,ISet::full()),p::project(target.state,ISet::full())));
        prior::restore_equal(eq,lib,programs,a.history,target.history,tokens,offset,owner,actor,a.state,target.state);
        replay::context_equivalence(eq,lib);batch::empty_batch(pi::context_eq(eq),p::project(g::restore(a.history,tokens,a.state,actor).unwrap(),ISet::full()));
    } else {restore_mixed(eq,lib,programs,a.history,target.history,tokens,actions,offset,owner,actor,a.state,target.state);}
}

pub open spec fn fragment<A,X,U,B,I>(programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)->bool {
    &&& forall|i:int| 0<=i<labels.len() && g::landing(source[i],source[i+1],labels[i].1) ==> {
        let node=programs(labels[i].0)(source[i].current[labels[i].0].unwrap());
        source_proof::table_node(node)
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
        source_proof::interface_frame(eq,lib,programs,a,z,label.0,label.1,owner);
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
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),prepared(eq,lib,programs,a,target,actions,offset,owner),g::step(lib,programs,a,z,actor,rule),
        rule!=r::Rule::Insert,rule!=r::Rule::Remove,
        sh::receipt_word(a.history,a.state.accumulators[owner])==sj::journal(fu::events(actions)),
        forall|i:int| offset<=i<a.history.len() && g::owner(#[trigger] a.history[i].landed.receipt)==owner ==> r::interface_same(a.history[i].input.control.fibers[owner],a.state.control.fibers[owner]),
        g::landing(a,z,rule) ==> source_proof::table_node(programs(actor)(a.current[actor].unwrap())),
        rule==r::Rule::Unload ==> actor!=owner && table::table_tokens(programs,a.history,a.state.accumulators[actor],actor),
    ensures {
        let out=target_proof::advance(lib,programs,a,z,target,actor,rule,owner);
        let action=if g::landing(a,z,rule) {fu::Action::Forward {call:fu::entry_pair(lib,programs,g::entry(lib,programs,a,actor),owner)}} else {fu::Action::Identity};
        &&& g::well_formed(lib,programs,out) && target_proof::related(eq,z,out,offset,owner)
        &&& (sh::keep(actor,rule,owner) ==> g::step(lib,programs,target,out,actor,rule))
        &&& base::synchronized(eq,actions.push(action),z,out)
    },
{
    replay::context_equivalence(eq,lib);ol::frame(eq,lib,programs,a,z,actor,rule);ol::configuration_preservation(eq,lib,programs,a,z,actor,rule);
    let out=target_proof::advance(lib,programs,a,z,target,actor,rule,owner);let es=fu::events(actions);
    let action=if g::landing(a,z,rule) {fu::Action::Forward {call:fu::entry_pair(lib,programs,g::entry(lib,programs,a,actor),owner)}} else {fu::Action::Identity};
    base::own_words_push(actions,action);
    if g::landing(a,z,rule) {
        let entry=g::entry(lib,programs,a,actor);let node=replay::dependent(programs(actor)(a.current[actor].unwrap()));let call=fu::entry_pair(lib,programs,entry,owner);
        fp::landing_historical(eq,lib,programs,a,z,actor,rule,owner);
        fp::historical_contract(eq,lib,programs,entry,owner,a.state.control.fibers[owner].provisions);
        lift::run_preservation(dep::stage(lib,node),a.state,actor);p::unique_owner(entry.landed.state);
        p::lifecycle_edit(entry.landed.state,actor,z.state.control.fibers[actor].phase,a.state.control.fibers[actor].committed,z.state.iterators[actor],z.state.accumulators[actor],ISet::full());
        assert(p::project(z.state,ISet::full())==p::project(entry.landed.state,ISet::full()));
        if actor==owner {
            target_proof::own_landing(eq,lib,programs,a,z,target,offset,owner,rule);
            batch::own_push(pi::context_eq(eq),batch::redo(es),batch::undo(es),call.forward,call.inverse,p::project(a.state,ISet::full()));
            assert(out==target);assert(call.own);
        } else if let d::Node::Provision {key,value,next}=node {
            fp::synchronized_landing(eq,lib,programs,a,z,target,actions,offset,owner,actor,rule,key,value,next);
        } else {
            assert(replay::operational(node));
            pending_words(eq,lib,programs,a.history,actions,offset,a.state,owner,actor,node);
            let word=sj::journal(es);replay::run_after_word(eq,lib,node,a.state,target.state,actor,word);history::actual_names(lib,node,a.state,target.state,actor);
            let left=g::Receipt::Table {receipt:dep::run(lib,node,a.state,actor).unwrap().receipt};let right=g::Receipt::Table {receipt:dep::run(lib,node,target.state,actor).unwrap().receipt};
            obs::projected_receipts(eq,left,right);
            target_proof::landing_from_call(eq,lib,programs,a,z,target,offset,owner,actor,rule);
            batch::foreign_cross(pi::context_eq(eq),batch::redo(es),batch::undo(es),call.forward,p::project(a.state,ISet::full()));
            lift::run_projects(dep::stage(lib,node),target.state,actor);
            let reference=batch::undo(es)(p::project(a.state,ISet::full())).unwrap();
            assert(pi::context_eq(eq)((call.forward)(reference).unwrap(),(call.forward)(p::project(target.state,ISet::full())).unwrap()));
            assert((call.forward)(p::project(target.state,ISet::full()))==Some(p::project(out.state,ISet::full())));
        }
    } else if rule==r::Rule::Unload {
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
    } else {
        target_proof::control_transport(eq,lib,programs,a,z,target,offset,owner,actor,rule);
        sh::source_domains(eq,lib,programs,a,z,actor,rule);
        p::unique_owner(a.state);p::unique_owner(z.state);p::projection_equal(a.state,z.state,ISet::full());
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
