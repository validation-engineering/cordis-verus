//! A real foreign Unload may consume Unit/Operation receipts older than the
//! deletion window. The owner window may publish private provisions and use
//! shared keys; only owner landings occur before this final foreign Unload.
//! Actual empty-origin history supplies the old callbacks and receipts. The
//! source guard and source restore are facts of its given legal Unload; target
//! restore and target lifecycle legality are derived, not inputs.
#[cfg(verus_keep_ghost)]
use crate::{
    calculus as c, foreign_unload as fu, mixed_grammar as g, mixed_observational_transport as mt,
    observational_grammar as og, observational_lift as ol, old_receipt_support as old,
    partial_independence as pi, preservation as inv, projection as p,
    providing_owner_deletion as source_proof, providing_owner_execution as execution,
    providing_owner_transport as target_proof, refinement as r,
    selective_foreign_recovery as selective, semantics as s, shared_execution as sh,
    shared_replay as replay, shared_unload_execution as history, strict_batch_recovery as batch,
    strict_journal as sj, Phase, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn owner_window<U,I>(source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)->bool {
    forall|i:int| #![trigger labels[i]] 0<=i<labels.len() ==> labels[i].1!=r::Rule::Unload
        && (g::landing(source[i],source[i+1],labels[i].1) ==> labels[i].0==owner)
}
pub open spec fn own_actions<S>(actions:Seq<fu::Action<S>>)->bool {
    forall|i:int| #![trigger actions[i]] 0<=i<actions.len() ==> match actions[i] {
        fu::Action::Forward {call}=>call.own,fu::Action::Identity=>true,fu::Action::Inverse {..}=>false,
    }
}
pub proof fn only_owner_actions<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize)
    requires g::execution(lib,programs,source,labels),owner_window(source,labels,owner),
    ensures own_actions(fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner)),
    decreases labels.len(),
{
    if labels.len()>0 {
        let states=source.drop_last();let previous=labels.drop_last();let label=labels.last();
        assert(g::execution(lib,programs,states,previous));assert(owner_window(states,previous,owner));
        only_owner_actions(lib,programs,states,previous,owner);
        let before=fu::trace_actions(lib,programs,states,previous,source.first().history.len(),owner);
        let after=fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner);
        let a=states.last();let z=source.last();
        if g::landing(a,z,label.1) {assert(label.0==owner);assert(g::owner(g::entry(lib,programs,a,owner).landed.receipt)==owner);}
        assert(after.len()==before.len()+1);
        assert forall|i:int| #![trigger after[i]] 0<=i<after.len() implies match after[i] {
            fu::Action::Forward {call}=>call.own,fu::Action::Identity=>true,fu::Action::Inverse {..}=>false,
        } by {if i<before.len() {assert(after[i]==before[i]);} else {assert(i==before.len());}}
    }
}

pub proof fn batch_source<S>(eq:spec_fn(S,S)->bool,actions:Seq<fu::Action<S>>,initial:S)
    requires c::equivalence(eq),selective::local_source(eq,actions,initial),own_actions(actions),
    ensures batch::admissible(eq,fu::events(actions),initial),
    decreases actions.len(),
{
    if actions.len()>0 {
        let prefix=actions.drop_last();batch_source(eq,prefix,initial);batch::recovery(eq,fu::events(prefix),initial);
        let es=fu::events(prefix);assert(fu::events(actions).drop_last() =~= es);
        if let fu::Action::Identity=actions.last() {
            fu::identity_contract(eq,batch::redo(es));fu::identity_contract(eq,batch::undo(es));
            pi::commute_symmetric(eq,batch::redo(es),fu::identity());pi::commute_symmetric(eq,batch::undo(es),fu::identity());
        }
    }
}

pub open spec fn forward_origin<S>(records:Seq<fu::Pair<S>>,map:crate::mediated::PartialMap<S>)->bool {
    exists|j:int| 0<=j<records.len() && records[j].own && records[j].forward==map
}
pub proof fn forward_origins<S>(actions:Seq<fu::Action<S>>)
    ensures forall|i:int| 0<=i<batch::forwards(fu::events(actions)).len() ==> forward_origin(fu::catalog(actions),#[trigger] batch::forwards(fu::events(actions))[i]),
    decreases actions.len(),
{
    if actions.len()==0 {
        assert(fu::events(actions)==Seq::empty());assert(batch::forwards(fu::events(actions))==Seq::empty());
    } else {
        let prefix=actions.drop_last();forward_origins(prefix);
        let before=fu::catalog(prefix);let all=fu::catalog(actions);let old=batch::forwards(fu::events(prefix));let word=batch::forwards(fu::events(actions));
        assert(fu::events(actions).drop_last() =~= fu::events(prefix));
        assert forall|i:int| 0<=i<word.len() implies forward_origin(all,#[trigger] word[i]) by {
            if i<old.len() {
                assert(word[i]==old[i]);let j=choose|j:int|0<=j<before.len() && before[j].own && before[j].forward==old[i];
                assert(all[j]==before[j]);assert(all[j].forward==word[i]);
            } else {assert(i==old.len());assert(all[all.len()-1].own);assert(all[all.len()-1].forward==word[i]);}
        }
    }
}

pub proof fn old_indices<U,I>(entries:Seq<g::Entry<U,I>>,offset:nat,owner:usize,tokens:Seq<nat>)
    requires forall|i:int| 0<=i<tokens.len() ==> #[trigger] tokens[i]<offset,
    ensures history::rename(entries,offset,owner,tokens)==tokens,
{
    reveal(history::index);
    assert(history::rename(entries,offset,owner,tokens) =~= tokens);
}

/// The old-token bound is independent of the new-history compression offset.
/// Every word member must be an actual operational receipt owned by actor.
pub open spec fn old_tokens<A,X,U,B,I>(programs:g::Programs<A,X,U,B,I>,entries:Seq<g::Entry<U,I>>,tokens:Seq<nat>,offset:nat,actor:usize)->bool {
    &&& offset<=entries.len()
    &&& forall|i:int| #![trigger tokens[i]] 0<=i<tokens.len() ==> {
        let token=tokens[i];let e=entries[token as int];
        &&& token<offset && g::owner(e.landed.receipt)==actor
        &&& replay::operational_mixed(programs(actor)(e.iterator))
    }
}

pub proof fn preserved_permissions<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires og::primitive_theory(eq,lib),g::execution(lib,programs,source,labels),g::well_formed(lib,programs,source.first()),mt::permitted_history(lib,programs,source.first().history),
    ensures mt::permitted_history(lib,programs,source.last().history),
    decreases labels.len(),
{
    ol::execution_preservation(eq,lib,programs,source,labels);
    if labels.len()>0 {
        let prefix=source.drop_last();let previous=labels.drop_last();assert(g::execution(lib,programs,prefix,previous));
        preserved_permissions(eq,lib,programs,prefix,previous);
        mt::permitted_step(eq,lib,programs,prefix.last(),source.last(),labels.last().0,labels.last().1);
    }
}


/// Derive the two whole-batch crossing laws from actual old and new receipts.
/// There is no assumed reverse witness for the old operation at this state.
pub proof fn receipt_crosses_batch<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    entries:Seq<g::Entry<U,I>>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize,actor:usize,token:nat,current:s::State<U>)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),inv::well_formed(current),source_proof::separated(current,owner),actor!=owner,
        s::registered(current,actor),offset<=entries.len(),token<offset,g::owner(entries[token as int].landed.receipt)==actor,
        old::input_supported(lib,entries[token as int]),mt::permitted_history(lib,programs,entries),g::history_sound(lib,programs,entries),
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
    forward_origins(actions);fu::journal_origins(actions);
    assert forall|i:int| 0<=i<batch::forwards(es).len() implies pi::respects(pi::context_eq(eq),#[trigger] batch::forwards(es)[i])
        && pi::commutes(pi::context_eq(eq),batch::forwards(es)[i],f) by {
        let j=choose|j:int| 0<=j<records.len() && records[j].own && records[j].forward==batch::forwards(es)[i];
        let entry=entries[offset as int+j];assert(records[j]==fu::entry_pair(lib,programs,entry,owner));
        assert(g::owner(entry.landed.receipt)==owner);
        source_proof::historical_contract(eq,lib,programs,entry,owner,current.control.fibers[owner].provisions);
        old::cross_old_entry(eq,lib,programs,entry,old_entry,current,owner,actor);
    }
    assert forall|i:int| 0<=i<sj::journal(es).len() implies pi::respects(pi::context_eq(eq),#[trigger] sj::journal(es)[i])
        && pi::commutes(pi::context_eq(eq),sj::journal(es)[i],f) by {
        let j=choose|j:int| 0<=j<records.len() && records[j].own && records[j].inverse==sj::journal(es)[i];
        let entry=entries[offset as int+j];assert(records[j]==fu::entry_pair(lib,programs,entry,owner));
        assert(g::owner(entry.landed.receipt)==owner);
        source_proof::historical_contract(eq,lib,programs,entry,owner,current.control.fibers[owner].provisions);
        old::cross_old_entry(eq,lib,programs,entry,old_entry,current,owner,actor);
    }
    sj::word_commutes(pi::context_eq(eq),batch::forwards(es),f);sj::word_commutes(pi::context_eq(eq),sj::journal(es),f);
}

/// Simultaneously execute the real source and target LIFO routines. The old
/// token mapping is the identity even though later owner entries were erased.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn restore_old<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    left:Seq<g::Entry<U,I>>,right:Seq<g::Entry<U,I>>,tokens:Seq<nat>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize,actor:usize,source:s::State<U>,target:s::State<U>)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),inv::well_formed(source),inv::well_formed(target),
        source_proof::separated(source,owner),actor!=owner,s::registered(target,actor),source.control.fibers[actor]==target.control.fibers[actor],s::registered(source,actor),
        history::histories(eq,left,right,offset,owner),old_tokens(programs,left,tokens,offset,actor),g::restore(left,tokens,source,actor).is_some(),
        mt::permitted_history(lib,programs,left),g::history_sound(lib,programs,left),
        forall|i:int| 0<=i<offset ==> old::input_supported(lib,#[trigger] left[i]),
        fu::catalog(actions)==fu::fresh_records(lib,programs,left,offset,owner),
        forall|i:int| offset<=i<left.len() ==> source_proof::historical(lib,programs,#[trigger] left[i],owner,source.control.fibers[owner].provisions),
        batch::batch(pi::context_eq(eq),batch::redo(fu::events(actions)),batch::undo(fu::events(actions)),p::project(source,ISet::full())),
        pi::context_eq(eq)(batch::undo(fu::events(actions))(p::project(source,ISet::full())).unwrap(),p::project(target,ISet::full())),
    ensures {
        let a=g::restore(left,tokens,source,actor).unwrap();let b=g::restore(right,tokens,target,actor);
        &&& b.is_some() && inv::well_formed(a) && inv::well_formed(b.unwrap())
        &&& a.control==source.control && b.unwrap().control==target.control
        &&& forall|n:usize| s::registered(target,n) ==> b.unwrap().tables[n].dom()==target.tables[n].dom()
        &&& forall|n:usize| s::registered(source,n) ==> a.tables[n].dom()==source.tables[n].dom()
        &&& batch::batch(pi::context_eq(eq),batch::redo(fu::events(actions)),batch::undo(fu::events(actions)),p::project(a,ISet::full()))
        &&& pi::context_eq(eq)(batch::undo(fu::events(actions))(p::project(a,ISet::full())).unwrap(),p::project(b.unwrap(),ISet::full()))
    },
    decreases tokens.len(),
{
    replay::context_equivalence(eq,lib);
    if tokens.len()>0 {
        let token=tokens.last();let e=left[token as int];let receipt=e.landed.receipt;let es=fu::events(actions);
        assert(token<offset);assert(right[token as int]==e);assert(g::owner(receipt)==actor);assert(history::simple(receipt));
        mt::history_reflexive(eq,lib,programs,left,token as int);
        receipt_crosses_batch(eq,lib,programs,left,actions,offset,owner,actor,token,source);
        fu::table_inverse_projects(receipt,source);let sa=g::undo(receipt,source).unwrap();
        let before=p::project(source,ISet::full());let reference=batch::undo(es)(before).unwrap();
        batch::foreign_cross(pi::context_eq(eq),batch::redo(es),batch::undo(es),sh::flat(receipt),before);
        history::one_inverse(eq,receipt,receipt,source,target,actor,reference);let ta=g::undo(receipt,target).unwrap();
        assert(pi::context_eq(eq)(batch::undo(es)(p::project(sa,ISet::full())).unwrap(),p::project(ta,ISet::full())));
        assert(sa.control==source.control);
        assert(source_proof::separated(sa,owner)) by {
            assert forall|n:usize| s::registered(sa,n) && n!=owner implies crate::dependent_lift::declarations(sa,n).disjoint(sa.control.fibers[owner].provisions) by {
                assert(s::registered(source,n));assert(crate::dependent_lift::declarations(sa,n)==crate::dependent_lift::declarations(source,n));
            }
        }
        assert(old_tokens(programs,left,tokens.drop_last(),offset,actor)) by {
            assert forall|i:int| #![trigger tokens.drop_last()[i]] 0<=i<tokens.drop_last().len() implies {
                let token=tokens.drop_last()[i];let e=left[token as int];
                &&& token<offset && g::owner(e.landed.receipt)==actor
                &&& replay::operational_mixed(programs(actor)(e.iterator))
            } by {assert(tokens.drop_last()[i]==tokens[i]);}
        }
        restore_old(eq,lib,programs,left,right,tokens.drop_last(),actions,offset,owner,actor,sa,ta);
        assert forall|n:usize| s::registered(source,n) implies g::restore(left,tokens,source,actor).unwrap().tables[n].dom()==source.tables[n].dom() by {
            assert(s::registered(sa,n));
        }
        assert forall|n:usize| s::registered(target,n) implies g::restore(right,tokens,target,actor).unwrap().tables[n].dom()==target.tables[n].dom() by {
            assert(s::registered(ta,n));
        }
    }
}


/// The target prefix is constructed by deletion; the target final Unload is
/// newly proved for old tokens. No legal target suffix is supplied as input.
#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub proof fn delete_with_old_unload<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    setup:Seq<g::Configuration<U,I>>,setup_labels:Seq<(usize,r::Rule)>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,z:g::Configuration<U,I>,owner:usize,actor:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,setup,setup_labels),setup.first()==g::empty::<U,I>(),setup.last()==source.first(),
        g::execution(lib,programs,source,labels),source_proof::separated(source.first().state,owner),
        source_proof::fragment(programs,source,labels,source.first().history.len(),owner),owner_window(source,labels,owner),
        source.first().state.control.fibers[owner].phase==Phase::Inactive,source.first().state.tables[owner].is_empty(),
        actor!=owner,g::step(lib,programs,source.last(),z,actor,r::Rule::Unload),
        old_tokens(programs,source.last().history,source.last().state.accumulators[actor],source.first().history.len(),actor),
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
    old::history_from_empty(eq,lib,programs,setup,setup_labels);
    preserved_permissions(eq,lib,programs,source,labels);
    source_proof::fresh_historical(eq,lib,programs,source,labels,owner);
    source_proof::actual_source(eq,lib,programs,source,labels,owner);
    execution::delete_execution(eq,lib,programs,source,labels,owner);
    only_owner_actions(lib,programs,source,labels,owner);
    let a=source.last();let offset=source.first().history.len();let actions=fu::trace_actions(lib,programs,source,labels,offset,owner);
    let initial=p::project(source.first().state,ISet::full());let es=fu::events(actions);
    replay::context_equivalence(eq,lib);batch_source(pi::context_eq(eq),actions,initial);batch::recovery(pi::context_eq(eq),es,initial);
    let target=execution::delete(lib,programs,source,labels,owner);let input=target.last();let tokens=a.state.accumulators[actor];
    assert(pi::context_eq(eq)(batch::undo(es)(p::project(a.state,ISet::full())).unwrap(),p::project(input.state,ISet::full())));
    assert forall|i:int| 0<=i<offset implies old::input_supported(lib,#[trigger] a.history[i]) by {
        assert(a.history[i]==source.first().history[i]);
    }
    old_indices(a.history,offset,owner,tokens);
    assert(input.state.accumulators[actor]==tokens);
    restore_old(eq,lib,programs,a.history,input.history,tokens,actions,offset,owner,actor,a.state,input.state);
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


/// The actual source Unload guard rules out revoking a declared key needed by
/// an installed owner. This prepares the old-Provision extension, but does not
/// claim its domain-changing target restore is handled by restore_old above.
pub proof fn provider_guard_separates_installed_owner<U>(state:s::State<U>,owner:usize,actor:usize)
    requires inv::well_formed(state),s::registered(state,owner),s::registered(state,actor),owner!=actor,
        state.control.fibers[owner].phase!=Phase::Inactive,!r::relied(state.control,actor),
    ensures crate::dependent_lift::declarations(state,owner).disjoint(state.control.fibers[actor].provisions),
{
    assert forall|key:Port| crate::dependent_lift::declarations(state,owner).contains(key)
        implies !state.control.fibers[actor].provisions.contains(key) by {
        if state.control.fibers[owner].provisions.contains(key) {
            assert(owner!=actor);
        } else {
            assert(state.control.fibers[owner].dependencies.contains(key));
            let binding=choose|b:crate::Binding| state.control.fibers[owner].committed.contains(b) && b.key==key.key && b.realm==key.realm;
            assert(state.control.fibers[binding.provider].provisions.contains(key));
            if state.control.fibers[actor].provisions.contains(key) {
                assert(binding.provider==actor);
                assert(r::relied(state.control,actor));
            }
        }
    }
}

} // verus!
