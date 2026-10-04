//! A final foreign Unload may contain both pre-cut and newly minted receipts.
//!
//! Old entries keep their exact history positions. New entries use the actual
//! target history and compressed tokens; their inverse callbacks need only be
//! observationally related. Every inverse's target domain is derived from its
//! current successful source call and the strict owner batch witness.
#[cfg(verus_keep_ghost)]
use crate::{
    foreign_unload as fu, mixed_grammar as g, mixed_observational_runs as obs,
    mixed_observational_transport as mt, observational_grammar as og, observational_lift as ol,
    old_journal_closure as closure, old_journal_interleaving as interleaving,
    old_journal_unload as old, old_receipt_support as support, partial_independence as pi,
    preservation as inv, projection as p, providing_owner_deletion as source_proof,
    providing_owner_execution as execution, providing_owner_transport as target_proof,
    refinement as r, semantics as s, shared_execution as sh, shared_replay as replay,
    shared_unload_execution as history, strict_batch_recovery as batch, strict_journal as sj,
    Phase, Port,
};
use vstd::prelude::*;

verus! {

/// An actual operational journal with no restriction on token age.
pub open spec fn operational_tokens<A,X,U,B,I>(programs:g::Programs<A,X,U,B,I>,entries:Seq<g::Entry<U,I>>,tokens:Seq<nat>,actor:usize)->bool {
    // This bound validates token positions; it is not the compression cut.
    old::old_tokens(programs,entries,tokens,entries.len(),actor)
}

/// A token's actual receipt crosses the own batch independently of its age.
pub proof fn receipt_crosses_batch<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    entries:Seq<g::Entry<U,I>>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize,actor:usize,token:nat,current:s::State<U>)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),inv::well_formed(current),source_proof::separated(current,owner),actor!=owner,
        s::registered(current,actor),offset<=entries.len(),token<entries.len(),g::owner(entries[token as int].landed.receipt)==actor,
        support::input_supported(lib,entries[token as int]),mt::permitted_history(lib,programs,entries),g::history_sound(lib,programs,entries),
        replay::operational_mixed(programs(actor)(entries[token as int].iterator)),g::undo(entries[token as int].landed.receipt,current).is_some(),
        fu::catalog(actions)==fu::fresh_records(lib,programs,entries,offset,owner),
        forall|i:int| offset<=i<entries.len() ==> source_proof::historical(lib,programs,#[trigger] entries[i],owner,current.control.fibers[owner].provisions),
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
        source_proof::historical_contract(eq,lib,programs,entry,owner,current.control.fibers[owner].provisions);
        support::cross_old_entry(eq,lib,programs,entry,old_entry,current,owner,actor);
    }
    assert forall|i:int| 0<=i<sj::journal(es).len() implies pi::respects(pi::context_eq(eq),#[trigger] sj::journal(es)[i])
        && pi::commutes(pi::context_eq(eq),sj::journal(es)[i],f) by {
        let j=choose|j:int| 0<=j<records.len() && records[j].own && records[j].inverse==sj::journal(es)[i];
        let entry=entries[offset as int+j];assert(records[j]==fu::entry_pair(lib,programs,entry,owner));
        assert(g::owner(entry.landed.receipt)==owner);
        source_proof::historical_contract(eq,lib,programs,entry,owner,current.control.fibers[owner].provisions);
        support::cross_old_entry(eq,lib,programs,entry,old_entry,current,owner,actor);
    }
    sj::word_commutes(pi::context_eq(eq),batch::forwards(es),f);sj::word_commutes(pi::context_eq(eq),sj::journal(es),f);
}

/// Restore the same logical journal using each side's authentic receipt.
/// Source success is a fact of the original step; target success is proved.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn restore_mixed<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    left:Seq<g::Entry<U,I>>,right:Seq<g::Entry<U,I>>,tokens:Seq<nat>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize,actor:usize,source:s::State<U>,target:s::State<U>)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),inv::well_formed(source),inv::well_formed(target),
        source_proof::separated(source,owner),actor!=owner,s::registered(target,actor),source.control.fibers[actor]==target.control.fibers[actor],s::registered(source,actor),
        history::histories(eq,left,right,offset,owner),operational_tokens(programs,left,tokens,actor),g::restore(left,tokens,source,actor).is_some(),
        mt::permitted_history(lib,programs,left),g::history_sound(lib,programs,left),
        support::history_inputs(lib,left),
        fu::catalog(actions)==fu::fresh_records(lib,programs,left,offset,owner),
        forall|i:int| offset<=i<left.len() ==> source_proof::historical(lib,programs,#[trigger] left[i],owner,source.control.fibers[owner].provisions),
        batch::batch(pi::context_eq(eq),batch::redo(fu::events(actions)),batch::undo(fu::events(actions)),p::project(source,ISet::full())),
        pi::context_eq(eq)(batch::undo(fu::events(actions))(p::project(source,ISet::full())).unwrap(),p::project(target,ISet::full())),
    ensures {
        let a=g::restore(left,tokens,source,actor).unwrap();let b=g::restore(right,history::rename(left,offset,owner,tokens),target,actor);
        &&& b.is_some() && inv::well_formed(a) && inv::well_formed(b.unwrap())
        &&& a.control==source.control && b.unwrap().control==target.control
        &&& forall|n:usize| s::registered(target,n) ==> b.unwrap().tables[n].dom()==target.tables[n].dom()
        &&& forall|n:usize| s::registered(source,n) ==> a.tables[n].dom()==source.tables[n].dom()
        &&& batch::batch(pi::context_eq(eq),batch::redo(fu::events(actions)),batch::undo(fu::events(actions)),p::project(a,ISet::full()))
        &&& pi::context_eq(eq)(batch::undo(fu::events(actions))(p::project(a,ISet::full())).unwrap(),p::project(b.unwrap(),ISet::full()))
    },
    decreases tokens.len(),
{
    replay::context_equivalence(eq,lib);history::rename_laws(left,offset,owner,tokens,0);
    if tokens.len()>0 {
        let token=tokens.last();let mapped=history::index(left,offset,owner,token);
        let e=left[token as int];let receipt=e.landed.receipt;let replacement=right[mapped as int].landed.receipt;let es=fu::events(actions);
        assert(token<left.len());assert(g::owner(receipt)==actor);assert(history::simple(receipt));
        if token<offset {
            reveal(history::index);assert(mapped==token);assert(right[mapped as int]==e);
            mt::history_reflexive(eq,lib,programs,left,token as int);
        } else {assert(g::owner(left[token as int].landed.receipt)!=owner);}
        assert(mapped<right.len());assert(obs::receipt_related(eq,receipt,replacement));
        receipt_crosses_batch(eq,lib,programs,left,actions,offset,owner,actor,token,source);
        fu::table_inverse_projects(receipt,source);let sa=g::undo(receipt,source).unwrap();
        let before=p::project(source,ISet::full());let reference=batch::undo(es)(before).unwrap();
        batch::foreign_cross(pi::context_eq(eq),batch::redo(es),batch::undo(es),sh::flat(receipt),before);
        history::one_inverse(eq,receipt,replacement,source,target,actor,reference);let ta=g::undo(replacement,target).unwrap();
        assert(pi::context_eq(eq)(batch::undo(es)(p::project(sa,ISet::full())).unwrap(),p::project(ta,ISet::full())));
        assert(sa.control==source.control);
        assert(source_proof::separated(sa,owner)) by {
            assert forall|n:usize| s::registered(sa,n) && n!=owner implies crate::dependent_lift::declarations(sa,n).disjoint(sa.control.fibers[owner].provisions) by {
                assert(s::registered(source,n));assert(crate::dependent_lift::declarations(sa,n)==crate::dependent_lift::declarations(source,n));
            }
        }
        assert(operational_tokens(programs,left,tokens.drop_last(),actor)) by {
            assert forall|i:int| #![trigger tokens.drop_last()[i]] 0<=i<tokens.drop_last().len() implies {
                let token=tokens.drop_last()[i];let e=left[token as int];
                &&& token<left.len() && g::owner(e.landed.receipt)==actor
                &&& replay::operational_mixed(programs(actor)(e.iterator))
            } by {assert(tokens.drop_last()[i]==tokens[i]);}
        }
        restore_mixed(eq,lib,programs,left,right,tokens.drop_last(),actions,offset,owner,actor,sa,ta);
        assert forall|n:usize| s::registered(source,n) implies g::restore(left,tokens,source,actor).unwrap().tables[n].dom()==source.tables[n].dom() by {
            assert(s::registered(sa,n));
        }
        assert forall|n:usize| s::registered(target,n) implies g::restore(right,history::rename(left,offset,owner,tokens),target,actor).unwrap().tables[n].dom()==target.tables[n].dom() by {
            assert(s::registered(ta,n));
        }
    }
}


/// Construct a real target suffix after an interleaved source window.
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub proof fn delete_with_mixed_unload<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    setup:Seq<g::Configuration<U,I>>,setup_labels:Seq<(usize,r::Rule)>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,z:g::Configuration<U,I>,owner:usize,actor:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,setup,setup_labels),setup.first()==g::empty::<U,I>(),setup.last()==source.first(),
        g::execution(lib,programs,source,labels),source_proof::separated(source.first().state,owner),
        source_proof::fragment(programs,source,labels,source.first().history.len(),owner),
        source.first().state.control.fibers[owner].phase==Phase::Inactive,source.first().state.tables[owner].is_empty(),
        actor!=owner,g::step(lib,programs,source.last(),z,actor,r::Rule::Unload),
        operational_tokens(programs,source.last().history,source.last().state.accumulators[actor],actor),
    ensures {
        let target=execution::delete(lib,programs,source,labels,owner);let out=g::unload(target.last(),actor);
        let es=fu::events(fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner));
        &&& batch::batch(pi::context_eq(eq),batch::redo(es),batch::undo(es),p::project(z.state,ISet::full()))
        &&& pi::context_eq(eq)(batch::undo(es)(p::project(z.state,ISet::full())).unwrap(),p::project(out.state,ISet::full()))
        &&& g::execution(lib,programs,target.push(out),sh::labels_without(labels,owner).push((actor,r::Rule::Unload)))
        &&& g::step(lib,programs,target.last(),out,actor,r::Rule::Unload) && g::well_formed(lib,programs,out)
        &&& target.first()==source.first()
        &&& target_proof::related(eq,z,out,source.first().history.len(),owner)
        &&& target.last().state.accumulators[actor]==history::rename(source.last().history,source.first().history.len(),owner,source.last().state.accumulators[actor])
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
    replay::context_equivalence(eq,lib);interleaving::batch_source(pi::context_eq(eq),actions,initial);batch::recovery(pi::context_eq(eq),es,initial);
    let target=execution::delete(lib,programs,source,labels,owner);let input=target.last();let tokens=a.state.accumulators[actor];
    assert(pi::context_eq(eq)(batch::undo(es)(p::project(a.state,ISet::full())).unwrap(),p::project(input.state,ISet::full())));
    assert forall|i:int| 0<=i<a.history.len() implies support::input_supported(lib,#[trigger] a.history[i]) by {
        if i<offset {assert(a.history[i]==source.first().history[i]);}
        else {assert(source_proof::historical(lib,programs,a.history[i],owner,a.state.control.fibers[owner].provisions));}
    }
    let renamed=history::rename(a.history,offset,owner,tokens);
    assert(input.state.accumulators[actor]==renamed);
    restore_mixed(eq,lib,programs,a.history,input.history,tokens,actions,offset,owner,actor,a.state,input.state);
    let source_restored=g::restore(a.history,tokens,a.state,actor).unwrap();let target_restored=g::restore(input.history,renamed,input.state,actor).unwrap();
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
        operational_tokens(programs,source.last().history,source.last().state.accumulators[actor],actor),
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
    delete_with_mixed_unload(eq,lib,programs,setup,setup_labels,source,labels,z,owner,actor);
    support::history_from_empty(eq,lib,programs,setup,setup_labels);
    source_proof::fresh_historical(eq,lib,programs,source,labels,owner);
    source_proof::actual_journal(eq,lib,programs,source,labels,owner);
    let a=source.last();let target=execution::delete(lib,programs,source,labels,owner);let out=g::unload(target.last(),actor);
    let es=fu::events(fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner));
    // This helper only needs operational receipts with valid token positions.
    // The source/target history correspondence still uses the original cut.
    closure::journal_after_foreign(eq,lib,programs,a,z,owner,actor,a.history.len());
    assert(sh::receipt_word(z.history,z.state.accumulators[owner])==sj::journal(es));
    assert(pi::run(sh::receipt_word(z.history,z.state.accumulators[owner]),p::project(z.state,ISet::full())).is_some());
    closure::close_from_strict_word(eq,lib,programs,z,out,owner);let terminal=g::unload(z,owner);
    closure::append_execution(lib,programs,source,labels,z,actor,r::Rule::Unload);
    closure::append_execution(lib,programs,source.push(z),labels.push((actor,r::Rule::Unload)),terminal,owner,r::Rule::Unload);
}


} // verus!
