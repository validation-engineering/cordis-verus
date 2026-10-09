//! Mixed foreign journal recovery around a private table owner.
//!
//! Only the deleted owner's newly recorded entries require table metadata.
//! Foreign history retains each genuine Table or Child entry. Child inverses
//! synchronize retirement of the captured identity; Table inverses retain
//! their actual partial domains. No successful target restore is assumed.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, dependent_grammar as d, dependent_lift as dep,
    foreign_child_transport as child, foreign_provision_transport as fp, foreign_unload as fu,
    grammar_lift as lift, internal_old_unload as base, internal_table_unload as prior,
    mixed_grammar as g, mixed_observational_runs as obs, mixed_observational_transport as mt,
    observational_grammar as og, observational_lift as ol, old_journal_unload as old,
    old_provision_journal as table, old_provision_support as prov, old_receipt_support as support,
    partial_independence as pi, preservation as inv, projection as p,
    providing_owner_deletion as source_proof, providing_owner_transport as target_proof,
    refinement as r, semantics as s, shared_execution as sh, shared_replay as replay,
    shared_unload_execution as history, strict_batch_recovery as batch, strict_journal as sj,
    Phase, Port,
};
use vstd::prelude::*;
verus! {

pub proof fn pending_words<A,X,U,B,I,J>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,entries:Seq<g::Entry<U,I>>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,current:s::State<U>,owner:usize,actor:usize,node:dep::Node<A,X,U,B,J>)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),offset<=entries.len(),fu::catalog(actions)==fu::fresh_records(lib,programs,entries,offset,owner),
        forall|i:int| offset<=i<entries.len() && g::owner(entries[i].landed.receipt)==owner ==> fp::historical(lib,programs,#[trigger] entries[i],owner,current.control.fibers[owner].provisions),
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
        forall|i:int| offset<=i<entries.len() && g::owner(entries[i].landed.receipt)==owner ==> fp::historical(lib,programs,#[trigger] entries[i],owner,current.control.fibers[owner].provisions),
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
        forall|i:int| offset<=i<entries.len() && g::owner(entries[i].landed.receipt)==owner ==> fp::historical(lib,programs,#[trigger] entries[i],owner,current.control.fibers[owner].provisions),
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

// Journal shape and per-entry absence use different quantified witnesses.
// Prove them independently so changes to unrelated transition guards cannot
// entangle those instantiations in the aggregate absence theorem.
proof fn pending_inverses_shrink<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,entries:Seq<g::Entry<U,I>>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize,private:ISet<Port>)
    requires offset<=entries.len(),fu::catalog(actions)==fu::fresh_records(lib,programs,entries,offset,owner),
        forall|i:int|offset<=i<entries.len() && g::owner(entries[i].landed.receipt)==owner ==> fp::historical(lib,programs,#[trigger] entries[i],owner,private),
    ensures forall|i:int|0<=i<sj::journal(fu::events(actions)).len() ==> fp::shrinks(#[trigger] sj::journal(fu::events(actions))[i]),
{
    let records=fu::catalog(actions);let word=sj::journal(fu::events(actions));fu::journal_origins(actions);
    assert forall|i:int|0<=i<word.len() implies fp::shrinks(#[trigger] word[i]) by {
        let j=choose|j:int|0<=j<records.len() && records[j].own && records[j].inverse==word[i];let entry=entries[offset as int+j];
        assert(records[j]==fu::entry_pair(lib,programs,entry,owner));fp::inverse_shape(lib,programs,entry,owner,private);
    }

}

proof fn pending_keys_avoid<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,entries:Seq<g::Entry<U,I>>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize,private:ISet<Port>,key:Port)
    requires offset<=entries.len(),fu::catalog(actions)==fu::fresh_records(lib,programs,entries,offset,owner),
        forall|i:int|offset<=i<entries.len() && g::owner(entries[i].landed.receipt)==owner ==> fp::historical(lib,programs,#[trigger] entries[i],owner,private),
        forall|i:int|0<=i<sj::journal(fu::events(actions)).len() ==> !fp::needs(#[trigger] sj::journal(fu::events(actions))[i],key),
    ensures forall|j:int|0<=j<fu::catalog(actions).len() && fu::catalog(actions)[j].own ==>
        pi::key(dep::stage(lib,replay::dependent(programs(owner)(#[trigger] entries[offset as int+j].iterator))))!=Some(key),
{
    let records=fu::catalog(actions);let word=sj::journal(fu::events(actions));
    assert forall|j:int|0<=j<records.len() && records[j].own implies
        pi::key(dep::stage(lib,replay::dependent(programs(owner)(#[trigger] entries[offset as int+j].iterator))))!=Some(key) by {
        let entry=entries[offset as int+j];assert(records[j]==fu::entry_pair(lib,programs,entry,owner));
        fp::inverse_shape(lib,programs,entry,owner,private);fp::inverse_member(actions,j);
        let i=choose|i:int|0<=i<word.len() && #[trigger] word[i]==records[j].inverse;assert(!fp::needs(word[i],key));
    }
}

pub proof fn pending_avoids<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,entries:Seq<g::Entry<U,I>>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize,private:ISet<Port>,input:IMap<Port,U>,key:Port)
    requires offset<=entries.len(),fu::catalog(actions)==fu::fresh_records(lib,programs,entries,offset,owner),
        forall|i:int|offset<=i<entries.len() && g::owner(entries[i].landed.receipt)==owner ==> fp::historical(lib,programs,#[trigger] entries[i],owner,private),
        pi::run(sj::journal(fu::events(actions)),input).is_some(),!input.dom().contains(key),
    ensures forall|j:int|0<=j<fu::catalog(actions).len() && fu::catalog(actions)[j].own ==>
        pi::key(dep::stage(lib,replay::dependent(programs(owner)(#[trigger] entries[offset as int+j].iterator))))!=Some(key),
{
    pending_inverses_shrink(lib,programs,entries,actions,offset,owner,private);
    fp::absent_word(sj::journal(fu::events(actions)),input,key);
    pending_keys_avoid(lib,programs,entries,actions,offset,owner,private,key);
}

/// The strict inverse word is already defined at the actual source state by
/// the prefix induction. Fresh-key absence then derives all required crossing.
pub proof fn provision_crosses<A,X,U,B,I,J>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,entries:Seq<g::Entry<U,I>>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize,private:ISet<Port>,input:IMap<Port,U>,key:Port,value:U,next:Option<J>)
    requires og::primitive_theory(eq,lib),(lib.values)(key,value),offset<=entries.len(),fu::catalog(actions)==fu::fresh_records(lib,programs,entries,offset,owner),
        forall|i:int|offset<=i<entries.len() && g::owner(entries[i].landed.receipt)==owner ==> fp::historical(lib,programs,#[trigger] entries[i],owner,private),
        pi::run(sj::journal(fu::events(actions)),input).is_some(),!input.dom().contains(key),
    ensures {
        let node=dep::stage(lib,d::Node::Provision {key,value,next});let f=pi::forward(node);let es=fu::events(actions);
        &&& pi::respects(pi::context_eq(eq),f)
        &&& pi::commutes(pi::context_eq(eq),f,batch::redo(es)) && pi::commutes(pi::context_eq(eq),f,batch::undo(es))
    },
{
    replay::context_equivalence(eq,lib);pending_avoids(lib,programs,entries,actions,offset,owner,private,input,key);
    let new=d::Node::Provision {key,value,next};let stage=dep::stage(lib,new);let forward=pi::forward(stage);let records=fu::catalog(actions);let es=fu::events(actions);
    source_proof::stage_respects(eq,lib,new,ISet::full(),ISet::full());assert(pi::generators(stage).contains(forward));pi::generator_respects(eq,stage,forward);
    assert forall|j:int|0<=j<records.len() && records[j].own implies pi::commutes(pi::context_eq(eq),records[j].forward,forward)
        && pi::commutes(pi::context_eq(eq),records[j].inverse,forward) && fu::respectful(pi::context_eq(eq),#[trigger] records[j]) by {
        let entry=entries[offset as int+j];assert(records[j]==fu::entry_pair(lib,programs,entry,owner));
        let node=replay::dependent(programs(owner)(entry.iterator));let own_stage=dep::stage(lib,node);
        fp::historical_contract(eq,lib,programs,entry,owner,private);replay::actual_receipt_projects(lib,node,entry.input,owner);
        source_proof::stage_respects(eq,lib,node,dep::declarations(entry.input,owner),entry.input.control.fibers[owner].provisions);
        if let d::Node::Unit=node {pi::unit_independence::<Port,U,B,B>(eq,stage);}else{pi::distinct_nodes(eq,own_stage,stage);}
        assert(pi::generators(own_stage).contains(records[j].forward));assert(pi::generators(own_stage).contains(records[j].inverse));
    }
    old::forward_origins(actions);fu::journal_origins(actions);
    assert forall|i:int|0<=i<batch::forwards(es).len() implies pi::respects(pi::context_eq(eq),#[trigger] batch::forwards(es)[i]) && pi::commutes(pi::context_eq(eq),batch::forwards(es)[i],forward) by {
        let j=choose|j:int|0<=j<records.len() && records[j].own && records[j].forward==batch::forwards(es)[i];
    }
    assert forall|i:int|0<=i<sj::journal(es).len() implies pi::respects(pi::context_eq(eq),#[trigger] sj::journal(es)[i]) && pi::commutes(pi::context_eq(eq),sj::journal(es)[i],forward) by {
        let j=choose|j:int|0<=j<records.len() && records[j].own && records[j].inverse==sj::journal(es)[i];
    }
    sj::word_commutes(pi::context_eq(eq),batch::forwards(es),forward);sj::word_commutes(pi::context_eq(eq),sj::journal(es),forward);
}



pub open spec fn prepared<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,target:g::Configuration<U,I>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize)->bool {
    &&& g::well_formed(lib,programs,a) && g::well_formed(lib,programs,target)
    &&& target_proof::related(eq,a,target,offset,owner) && source_proof::separated(a.state,owner)
    &&& support::history_inputs(lib,a.history) && mt::permitted_history(lib,programs,a.history)
    &&& offset<=a.history.len() && fu::catalog(actions)==fu::fresh_records(lib,programs,a.history,offset,owner)
    &&& forall|i:int| offset<=i<a.history.len() && g::owner(#[trigger] a.history[i].landed.receipt)==owner ==> {
        &&& fp::historical(lib,programs,a.history[i],owner,a.state.control.fibers[owner].provisions)
        &&& r::interface_same(a.history[i].input.control.fibers[owner],a.state.control.fibers[owner])
    }
    &&& base::synchronized(eq,actions,a,target)
    &&& sh::receipt_word(a.history,a.state.accumulators[owner])==sj::journal(fu::events(actions))
}

/// Inverse execution changes values or retired flags, never the syntax
/// interfaces, current iterators, live tokens, or historical calls.
pub proof fn inverse_configuration<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,receipt:g::Receipt<U>)
    requires g::well_formed(lib,programs,a),g::receipt_typed(lib,receipt),g::undo(receipt,a.state).is_some(),
    ensures {
        let z=child::with_state(a,g::undo(receipt,a.state).unwrap());
        &&& g::well_formed(lib,programs,z) && ch::recovery_frame(a.state,z.state)
        &&& forall|n:usize|s::registered(a.state,n) ==> a.state.control.fibers[n].committed==z.state.control.fibers[n].committed
    },
{
    g::inverse_preservation(lib,receipt,a.state);let z=child::with_state(a,g::undo(receipt,a.state).unwrap());
    assert forall|n:usize|s::registered(z.state,n) implies g::component_member(lib,programs,z.state,n,z.roots[n])
        && (z.current[n].is_some() ==> g::component_member(lib,programs,z.state,n,z.current[n].unwrap())) by {
        assert(s::registered(a.state,n));assert(dep::declarations(a.state,n)==dep::declarations(z.state,n));
    }
    assert(g::tokens_valid(z)) by {assert forall|n:usize,i:int| #![trigger z.state.accumulators[n][i]] s::registered(z.state,n) && 0<=i<z.state.accumulators[n].len()
        implies z.state.accumulators[n][i]<z.history.len() && g::owner(z.history[z.state.accumulators[n][i] as int].landed.receipt)==n by {assert(s::registered(a.state,n));}}
    assert(ch::retained(g::kind(z.history),z.state)) by {
        assert forall|n:usize,token:nat,captured:usize|s::registered(z.state,n) && z.state.accumulators[n].contains(token)
            && g::kind(z.history)(token)==Some(captured) implies s::registered(z.state,captured) by {
            assert(s::registered(a.state,n));assert(a.state.accumulators[n].contains(token));assert(g::kind(a.history)(token)==Some(captured));
            assert(s::registered(a.state,captured));
        }
    }
}

/// Transport one authentic Table receipt. Its age selects the receipt map;
/// strict whole-batch crossing is derived from only the owner's true entries.
#[verifier::spinoff_prover]
#[verifier::rlimit(45)]
pub proof fn table_inverse<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,target:g::Configuration<U,I>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize,actor:usize,token:nat)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),prepared(eq,lib,programs,a,target,actions,offset,owner),
        actor!=owner,s::registered(a.state,actor),!r::relied(a.state.control,actor),token<a.history.len(),g::owner(a.history[token as int].landed.receipt)==actor,
        match a.history[token as int].landed.receipt {g::Receipt::Table {..}=>true,_=>false},g::undo(a.history[token as int].landed.receipt,a.state).is_some(),
    ensures {
        let receipt=a.history[token as int].landed.receipt;let mapped=history::index(a.history,offset,owner,token);let other=target.history[mapped as int].landed.receipt;
        let left=child::with_state(a,g::undo(receipt,a.state).unwrap());let right=g::undo(other,target.state);let out=child::with_state(target,right.unwrap());
        &&& mapped<target.history.len() && g::owner(other)==actor && right.is_some()
        &&& prepared(eq,lib,programs,left,out,actions,offset,owner)
        &&& left.state.control==a.state.control && out.state.control==target.state.control
    },
{
    replay::context_equivalence(eq,lib);let receipt=a.history[token as int].landed.receipt;let mapped=history::index(a.history,offset,owner,token);
    if token<offset {reveal(history::index);assert(mapped==token);assert(target.history[mapped as int]==a.history[token as int]);mt::history_reflexive(eq,lib,programs,a.history,token as int);}
    assert(mapped<target.history.len());let other=target.history[mapped as int].landed.receipt;assert(obs::receipt_related(eq,receipt,other));
    let es=fu::events(actions);let before=p::project(a.state,ISet::full());let reference=batch::undo(es)(before).unwrap();
    fu::table_inverse_projects(receipt,a.state);table::one_frame(receipt,a.state,actor);let left=child::with_state(a,g::undo(receipt,a.state).unwrap());
    if history::simple(receipt) {
        assert(replay::operational_mixed(programs(actor)(a.history[token as int].iterator)));
        receipt_crosses_batch(eq,lib,programs,a.history,actions,offset,owner,actor,token,a.state);
        batch::foreign_cross(pi::context_eq(eq),batch::redo(es),batch::undo(es),sh::flat(receipt),before);
        history::one_inverse(eq,receipt,other,a.state,target.state,actor,reference);
    } else {
        if let g::Receipt::Table {receipt:record}=receipt {if let lift::Inverse::Provision {key}=record.inverse {
            assert(receipt==prov::receipt::<U>(actor,key));assert(other==receipt);prov::cut_contract(eq,actor,key);
            if a.state.control.fibers[owner].phase==Phase::Inactive {
                prior::inactive_words(a,actions,owner);assert(reference==before);
                prov::one_inverse(eq,a.state,target.state,actor,key,reference);
                batch::empty_batch(pi::context_eq(eq),p::project(left.state,ISet::full()));
            } else {
                provision_cut_crosses(eq,lib,programs,a.history,actions,offset,a.state,owner,actor,key);
                batch::foreign_cross(pi::context_eq(eq),batch::redo(es),batch::undo(es),prov::cut(key),before);
                prov::one_inverse(eq,a.state,target.state,actor,key,reference);
            }
            prov::domains_frame(a.state,target.state,actor,key);
        }}
    }
    let out=child::with_state(target,g::undo(other,target.state).unwrap());
    table::one_frame(other,target.state,actor);
    assert(g::receipt_typed(lib,receipt));assert(g::receipt_typed(lib,other));
    inverse_configuration(lib,programs,a,receipt);inverse_configuration(lib,programs,target,other);
    assert(source_proof::separated(left.state,owner));
    assert forall|n:usize|s::registered(left.state,n) && n!=owner implies left.state.tables[n].dom()==out.state.tables[n].dom()
        && left.state.control.fibers[n]==out.state.control.fibers[n] && left.current[n]==out.current[n] by {
        assert(s::registered(a.state,n));assert(s::registered(target.state,n));
    }
    assert(target_proof::related(eq,left,out,offset,owner));
}

/// LIFO recursion mixes captured-child retirement with strict Table inverses.
/// Source success comes solely from the original Unload; target success and
/// preservation of the real batch and compressed journals are conclusions.
#[verifier::spinoff_prover]
#[verifier::rlimit(45)]
pub proof fn restore<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,target:g::Configuration<U,I>,tokens:Seq<nat>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize,actor:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),prepared(eq,lib,programs,a,target,actions,offset,owner),
        actor!=owner,s::registered(a.state,actor),!r::relied(a.state.control,actor),g::restore(a.history,tokens,a.state,actor).is_some(),
        forall|i:int| #![trigger tokens[i]] 0<=i<tokens.len() ==> tokens[i]<a.history.len() && g::owner(a.history[tokens[i] as int].landed.receipt)==actor,
    ensures {
        let left=child::with_state(a,g::restore(a.history,tokens,a.state,actor).unwrap());
        let right=g::restore(target.history,history::rename(a.history,offset,owner,tokens),target.state,actor);let out=child::with_state(target,right.unwrap());
        &&& right.is_some() && prepared(eq,lib,programs,left,out,actions,offset,owner)
        &&& ch::recovery_frame(a.state,left.state) && ch::recovery_frame(target.state,out.state)
        &&& forall|n:usize|s::registered(a.state,n) ==> a.state.control.fibers[n].committed==left.state.control.fibers[n].committed
    },
    decreases tokens.len(),
{
    history::rename_laws(a.history,offset,owner,tokens,0);
    if tokens.len()>0 {
        let token=tokens.last();let mapped=history::index(a.history,offset,owner,token);let receipt=a.history[token as int].landed.receipt;
        assert(token<a.history.len());assert(g::owner(receipt)==actor);
        if token<offset {reveal(history::index);assert(mapped==token);assert(target.history[mapped as int]==a.history[token as int]);}
        assert(mapped<target.history.len());let other=target.history[mapped as int].landed.receipt;
        match receipt {
            g::Receipt::Child {child:captured,..}=>{
                assert(receipt==other);child::inverse_transport(eq,lib,programs,a,target,offset,owner,actor,captured);
            },
            g::Receipt::Table {..}=>{table_inverse(eq,lib,programs,a,target,actions,offset,owner,actor,token);},
        }
        let left=child::with_state(a,g::undo(receipt,a.state).unwrap());let out=child::with_state(target,g::undo(other,target.state).unwrap());
        inverse_configuration(lib,programs,a,receipt);inverse_configuration(lib,programs,target,other);
        assert(prepared(eq,lib,programs,left,out,actions,offset,owner));
        assert(!r::relied(left.state.control,actor)) by {assert forall|n:usize,b:crate::Binding|r::registered(left.state.control,n) && n!=actor
            && left.state.control.fibers[n].phase!=Phase::Inactive && left.state.control.fibers[n].committed.contains(b) implies b.provider!=actor by {assert(s::registered(a.state,n));}}
        assert forall|i:int| #![trigger tokens.drop_last()[i]] 0<=i<tokens.drop_last().len() implies tokens.drop_last()[i]<left.history.len()
            && g::owner(left.history[tokens.drop_last()[i] as int].landed.receipt)==actor by {assert(tokens.drop_last()[i]==tokens[i]);}
        restore(eq,lib,programs,left,out,tokens.drop_last(),actions,offset,owner,actor);
        assert forall|n:usize|s::registered(a.state,n) implies r::interface_same(a.state.control.fibers[n],g::restore(a.history,tokens,a.state,actor).unwrap().control.fibers[n])
            && a.state.control.fibers[n].phase==g::restore(a.history,tokens,a.state,actor).unwrap().control.fibers[n].phase
            && (a.state.control.fibers[n].retired ==> g::restore(a.history,tokens,a.state,actor).unwrap().control.fibers[n].retired)
            && a.state.control.fibers[n].committed==g::restore(a.history,tokens,a.state,actor).unwrap().control.fibers[n].committed by {assert(s::registered(left.state,n));}
        assert forall|n:usize|s::registered(target.state,n) implies r::interface_same(target.state.control.fibers[n],g::restore(target.history,history::rename(a.history,offset,owner,tokens),target.state,actor).unwrap().control.fibers[n])
            && target.state.control.fibers[n].phase==g::restore(target.history,history::rename(a.history,offset,owner,tokens),target.state,actor).unwrap().control.fibers[n].phase
            && (target.state.control.fibers[n].retired ==> g::restore(target.history,history::rename(a.history,offset,owner,tokens),target.state,actor).unwrap().control.fibers[n].retired) by {assert(s::registered(out.state,n));}
    }
}

/// Full one-step value/control transport under the prefix's inductive batch
/// invariant. Both the target landing and the updated batch are conclusions.
#[verifier::spinoff_prover]
#[verifier::rlimit(35)]
pub proof fn provision_landing<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize,actor:usize,rule:r::Rule,key:Port,value:U,next:Option<I>)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::well_formed(lib,programs,target),target_proof::related(eq,a,target,offset,owner),actor!=owner,
        source_proof::separated(a.state,owner),g::step(lib,programs,a,z,actor,rule),g::landing(a,z,rule),
        programs(actor)(a.current[actor].unwrap())==(g::Node::Dependent {node:d::Node::Provision {key,value,next}}),
        fu::catalog(actions)==fu::fresh_records(lib,programs,a.history,offset,owner),
        forall|i:int|offset<=i<a.history.len() && g::owner(a.history[i].landed.receipt)==owner ==> fp::historical(lib,programs,#[trigger] a.history[i],owner,a.state.control.fibers[owner].provisions),
        batch::batch(pi::context_eq(eq),batch::redo(fu::events(actions)),batch::undo(fu::events(actions)),p::project(a.state,ISet::full())),
        pi::context_eq(eq)(batch::undo(fu::events(actions))(p::project(a.state,ISet::full())).unwrap(),p::project(target.state,ISet::full())),
    ensures {
        let out=target_proof::advance(lib,programs,a,z,target,actor,rule,owner);let es=fu::events(actions);
        let extended=actions.push(fu::Action::Forward {call:fu::entry_pair(lib,programs,g::entry(lib,programs,a,actor),owner)});
        &&& g::step(lib,programs,target,out,actor,rule) && g::well_formed(lib,programs,out) && target_proof::related(eq,z,out,offset,owner)
        &&& batch::batch(pi::context_eq(eq),batch::redo(es),batch::undo(es),p::project(z.state,ISet::full()))
        &&& pi::context_eq(eq)(batch::undo(es)(p::project(z.state,ISet::full())).unwrap(),p::project(out.state,ISet::full()))
        &&& batch::redo(fu::events(extended))==batch::redo(es) && batch::undo(fu::events(extended))==batch::undo(es)
    },
{
    fp::landing_transport(eq,lib,programs,a,z,target,offset,owner,actor,rule,key,value,next);ol::run_members(eq,lib,programs,a.state,actor,a.current[actor].unwrap());
    let node=d::Node::Provision {key,value,next};let stage=dep::stage(lib,node);let f=pi::forward(stage);let es=fu::events(actions);let input=p::project(a.state,ISet::full());
    replay::context_equivalence(eq,lib);lift::run_projects(stage,a.state,actor);
    provision_crosses(eq,lib,programs,a.history,actions,offset,owner,a.state.control.fibers[owner].provisions,input,key,value,next);
    batch::foreign_cross(pi::context_eq(eq),batch::redo(es),batch::undo(es),f,input);
    let out=target_proof::advance(lib,programs,a,z,target,actor,rule,owner);let left=g::entry(lib,programs,a,actor);let right=g::entry(lib,programs,target,actor);
    lift::run_preservation(stage,a.state,actor);p::unique_owner(left.landed.state);
    p::lifecycle_edit(left.landed.state,actor,z.state.control.fibers[actor].phase,a.state.control.fibers[actor].committed,z.state.iterators[actor],z.state.accumulators[actor],ISet::full());
    ol::frame(eq,lib,programs,a,z,actor,rule);assert(f(input)==Some(p::project(z.state,ISet::full())));
    lift::run_projects(stage,target.state,actor);
    let reference=batch::undo(es)(input).unwrap();assert(pi::context_eq(eq)(f(reference).unwrap(),f(p::project(target.state,ISet::full())).unwrap()));
    base::own_words_push(actions,fu::Action::Forward {call:fu::entry_pair(lib,programs,left,owner)});
}


} // verus!
