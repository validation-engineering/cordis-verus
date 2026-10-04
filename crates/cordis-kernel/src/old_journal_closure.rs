//! Close the deleted owner's actual episode after an old foreign Unload.
//!
//! The retained strict batch witness supplies the final owner's real restore
//! domain. Both terminal lifecycle execution and equality of every table's
//! observation are conclusions; target legality alone is not the endpoint.
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_lift as dep, foreign_unload as fu, grammar_lift as lift, mixed_grammar as g,
    mixed_observational_runs as obs, observational_grammar as og, observational_lift as ol,
    old_journal_unload as old, old_receipt_support as support, partial_independence as pi,
    preservation as inv, projection as p, providing_owner_deletion as source_proof,
    providing_owner_execution as execution, providing_owner_transport as target_proof,
    refinement as r, semantics as s, shared_execution as sh, shared_replay as replay,
    shared_unload_execution as history, strict_journal as sj, Binding, Phase, Port,
};
use vstd::prelude::*;

verus! {

pub proof fn append_execution<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,states:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,next:g::Configuration<U,I>,actor:usize,rule:r::Rule)
    requires g::execution(lib,programs,states,labels),g::step(lib,programs,states.last(),next,actor,rule),
    ensures g::execution(lib,programs,states.push(next),labels.push((actor,rule))),
{
    assert forall|i:int| 0<=i<labels.push((actor,rule)).len() implies g::step(lib,programs,states.push(next)[i],states.push(next)[i+1],labels.push((actor,rule))[i].0,labels.push((actor,rule))[i].1) by {
        if i<labels.len() {assert(states.push(next)[i]==states[i]);assert(states.push(next)[i+1]==states[i+1]);} else {assert(i==labels.len());}
    }
}

pub proof fn separated_no_users<U>(state:s::State<U>,owner:usize)
    requires inv::well_formed(state),source_proof::separated(state,owner),
    ensures !r::relied(state.control,owner),
{
    if r::relied(state.control,owner) {
        let (n,b)=choose|n:usize,b:Binding| s::registered(state,n) && n!=owner && state.control.fibers[n].phase!=Phase::Inactive
            && state.control.fibers[n].committed.contains(b) && b.provider==owner;
        let key=Port {key:b.key,realm:b.realm};
        assert(state.control.fibers[owner].provisions.contains(key));assert(dep::declarations(state,n).contains(key));
        assert(dep::declarations(state,n).disjoint(state.control.fibers[owner].provisions));
    }
}

/// A Unit/Operation foreign cleanup preserves the other owner's exact control
/// and actual journal; pins are retained through the captured committed view.
pub proof fn journal_after_foreign<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,owner:usize,actor:usize,offset:nat)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),source_proof::separated(a.state,owner),actor!=owner,
        g::step(lib,programs,a,z,actor,r::Rule::Unload),old::old_tokens(programs,a.history,a.state.accumulators[actor],offset,actor),
        source_proof::pinned_tokens(a.history,a.state.accumulators[owner],a.state,owner),
    ensures g::well_formed(lib,programs,z),source_proof::separated(z.state,owner),
        z.state.control.fibers[owner]==a.state.control.fibers[owner],z.history==a.history,z.state.accumulators[owner]==a.state.accumulators[owner],
        source_proof::pinned_tokens(z.history,z.state.accumulators[owner],z.state,owner),
{
    ol::configuration_preservation(eq,lib,programs,a,z,actor,r::Rule::Unload);ol::frame(eq,lib,programs,a,z,actor,r::Rule::Unload);
    source_proof::interface_frame(eq,lib,programs,a,z,actor,r::Rule::Unload,owner);
    let tokens=a.state.accumulators[actor];
    assert forall|i:int| 0<=i<tokens.len() implies history::simple(#[trigger] a.history[tokens[i] as int].landed.receipt) by {
        let token=tokens[i];assert(token<a.history.len());assert(g::owner(a.history[token as int].landed.receipt)==actor);
    }
    target_proof::restore_domains(a.history,tokens,0,a.state,actor);
    assert(z.state.control.fibers[owner]==a.state.control.fibers[owner]);
    sh::resolution_frame(a.state,z.state,owner);
    assert forall|i:int| 0<=i<z.state.accumulators[owner].len() implies z.state.accumulators[owner][i]<z.history.len()
        && source_proof::pinned(#[trigger] z.history[z.state.accumulators[owner][i] as int].landed.receipt,z.state,owner) by {
        let token=z.state.accumulators[owner][i];let receipt=z.history[token as int].landed.receipt;
        assert(source_proof::pinned(receipt,a.state,owner));
        if let g::Receipt::Table {receipt}=receipt {if let lift::Inverse::Operation {key,..}=receipt.inverse {
            assert(lift::resolve(a.state,owner,key)==lift::resolve(z.state,owner,key));
        }}
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(20)]
pub proof fn close_from_strict_word<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,z:g::Configuration<U,I>,out:g::Configuration<U,I>,owner:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,z),g::well_formed(lib,programs,out),
        target_proof::controls(z,out,owner),source_proof::separated(z.state,owner),z.state.control.fibers[owner].phase==Phase::Unloading,
        source_proof::pinned_tokens(z.history,z.state.accumulators[owner],z.state,owner),
        pi::run(sh::receipt_word(z.history,z.state.accumulators[owner]),p::project(z.state,ISet::full())).is_some(),
        pi::context_eq(eq)(pi::run(sh::receipt_word(z.history,z.state.accumulators[owner]),p::project(z.state,ISet::full())).unwrap(),p::project(out.state,ISet::full())),
    ensures g::restore(z.history,z.state.accumulators[owner],z.state,owner).is_some(),
        g::step(lib,programs,z,g::unload(z,owner),owner,r::Rule::Unload),g::well_formed(lib,programs,g::unload(z,owner)),
        g::unload(z,owner).state.control==out.state.control,obs::tables_related(eq,g::unload(z,owner).state,out.state),
        g::unload(z,owner).state.tables[owner].is_empty(),out.state.tables[owner].is_empty(),
{
    source_proof::restore_definedness(z.history,z.state.accumulators[owner],z.state,owner);
    separated_no_users(z.state,owner);let terminal=g::unload(z,owner);
    assert(g::step(lib,programs,z,terminal,owner,r::Rule::Unload));ol::configuration_preservation(eq,lib,programs,z,terminal,owner,r::Rule::Unload);
    let restored=g::restore(z.history,z.state.accumulators[owner],z.state,owner).unwrap();p::unique_owner(restored);
    p::lifecycle_edit(restored,owner,Phase::Inactive,ISet::empty(),None,Seq::empty(),ISet::full());
    assert(pi::context_eq(eq)(p::project(terminal.state,ISet::full()),p::project(out.state,ISet::full())));
    assert forall|n:usize| terminal.state.control.fibers.dom().contains(n) implies #[trigger] terminal.state.control.fibers[n]==out.state.control.fibers[n] by {
        assert(s::registered(z.state,n));
        if n==owner {assert(r::interface_same(z.state.control.fibers[n],out.state.control.fibers[n]));assert(terminal.state.control.fibers[n].committed =~= out.state.control.fibers[n].committed);}
        else {assert(z.state.control.fibers[n]==out.state.control.fibers[n]);}
    }
    assert(terminal.state.control.fibers.dom() =~= z.state.control.fibers.dom());assert(terminal.state.control.fibers.dom()==out.state.control.fibers.dom());
    assert(terminal.state.control.fibers =~= out.state.control.fibers);assert(terminal.state.control==out.state.control);
    execution::tables_from_projection(eq,terminal.state,out.state);
    assert(s::registered(terminal.state,owner));assert(s::registered(out.state,owner));
    assert(out.state.tables[owner].is_empty());
    assert(terminal.state.tables[owner].dom()==out.state.tables[owner].dom());
    assert(terminal.state.tables[owner] =~= IMap::empty());
}

#[verifier::spinoff_prover]
#[verifier::rlimit(50)]
pub proof fn closed_deletion<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    setup:Seq<g::Configuration<U,I>>,setup_labels:Seq<(usize,r::Rule)>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,z:g::Configuration<U,I>,owner:usize,actor:usize)
    requires og::primitive_theory(eq,lib),replay::interface(eq,lib),g::execution(lib,programs,setup,setup_labels),setup.first()==g::empty::<U,I>(),setup.last()==source.first(),
        g::execution(lib,programs,source,labels),source_proof::separated(source.first().state,owner),
        source_proof::fragment(programs,source,labels,source.first().history.len(),owner),old::owner_window(source,labels,owner),
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
    old::delete_with_old_unload(eq,lib,programs,setup,setup_labels,source,labels,z,owner,actor);
    support::history_from_empty(eq,lib,programs,setup,setup_labels);
    source_proof::fresh_historical(eq,lib,programs,source,labels,owner);
    source_proof::actual_journal(eq,lib,programs,source,labels,owner);
    let a=source.last();let target=execution::delete(lib,programs,source,labels,owner);let out=g::unload(target.last(),actor);
    let es=fu::events(fu::trace_actions(lib,programs,source,labels,source.first().history.len(),owner));
    journal_after_foreign(eq,lib,programs,a,z,owner,actor,source.first().history.len());
    assert(sh::receipt_word(z.history,z.state.accumulators[owner])==sj::journal(es));
    assert(pi::run(sh::receipt_word(z.history,z.state.accumulators[owner]),p::project(z.state,ISet::full())).is_some());
    close_from_strict_word(eq,lib,programs,z,out,owner);let terminal=g::unload(z,owner);
    append_execution(lib,programs,source,labels,z,actor,r::Rule::Unload);
    append_execution(lib,programs,source.push(z),labels.push((actor,r::Rule::Unload)),terminal,owner,r::Rule::Unload);
}

} // verus!
