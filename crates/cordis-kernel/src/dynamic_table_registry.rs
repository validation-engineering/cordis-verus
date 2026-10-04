//! Real external registry changes while deleting one owner's table episode.
//!
//! Related configurations may change their common registry. An inserted
//! interface excludes the owner's private keys; the original insertion rule
//! itself supplies provision freshness. Removal uses the source's real parent,
//! inactive/retired, empty-table and live-journal-reference guards. No test of
//! target transition success is part of the local input conditions.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, dependent_lift as dep, foreign_unload as fu, internal_old_unload as base,
    mixed_grammar as g, mixed_observational_runs as obs, mixed_orchestration as orchestration,
    mixed_transposition as insert, observational_grammar as og, observational_lift as ol,
    projection as p, providing_owner_deletion as own, providing_owner_transport as transport,
    refinement as r, semantics as s, shared_execution as sh, shared_unload_execution as history,
    Port,
};
use vstd::prelude::*;

verus! {

/// Only the new dependencies need an extra restriction: the genuine Insert
/// provision-conflict guard already separates the new provided keys.
pub open spec fn guard<U,I>(a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,owner:usize)->bool {
    actor!=owner && (rule==r::Rule::Insert ==> z.state.control.fibers[actor].dependencies.disjoint(a.state.control.fibers[owner].provisions))
}
pub open spec fn advance<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,actor:usize,rule:r::Rule,owner:usize)->g::Configuration<U,I> {
    if rule==r::Rule::Insert {
        let f=z.state.control.fibers[actor];insert::insert(target,actor,f.parent,f.dependencies,f.provisions,z.roots[actor])
    } else if rule==r::Rule::Remove {orchestration::remove(target,actor)}
    else {transport::advance(lib,programs,a,z,target,actor,rule,owner)}
}

/// This frame mentions the retained owner, never the current interface of a
/// removed foreign name. Historical entries retain their own original input.
pub proof fn source_frame<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,owner:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,z,actor,rule),
        rule==r::Rule::Insert || rule==r::Rule::Remove,own::separated(a.state,owner),guard(a,z,actor,rule,owner),
    ensures own::separated(z.state,owner),g::well_formed(lib,programs,z),
        s::registered(z.state,owner),z.state.control.fibers[owner]==a.state.control.fibers[owner],
        z.state.tables[owner]==a.state.tables[owner],z.state.accumulators[owner]==a.state.accumulators[owner],
        z.roots[owner]==a.roots[owner],z.current[owner]==a.current[owner],z.history==a.history,
        p::project(z.state,ISet::full())==p::project(a.state,ISet::full()),
{
    ol::frame(eq,lib,programs,a,z,actor,rule);ol::configuration_preservation(eq,lib,programs,a,z,actor,rule);
    if rule==r::Rule::Insert {p::empty_insertion(a.state,z.state,actor,ISet::full());}
    else {p::unique_owner(a.state);p::empty_erasure(a.state,actor,ISet::full());}
    assert forall|n:usize|s::registered(z.state,n) && n!=owner implies dep::declarations(z.state,n).disjoint(z.state.control.fibers[owner].provisions) by {
        if n==actor {
            assert(rule==r::Rule::Insert);assert(!s::registered(a.state,actor));
            assert(z.state.control.fibers[actor].provisions.disjoint(a.state.control.fibers[owner].provisions)) by {
                assert forall|key:Port|z.state.control.fibers[actor].provisions.contains(key) implies !a.state.control.fibers[owner].provisions.contains(key) by {assert(s::registered(a.state,owner));}
            }
        } else {assert(s::registered(a.state,n));assert(z.state.control.fibers[n]==a.state.control.fibers[n]);}
    }
}

/// Every target live token is an authentic source live token under the existing
/// compression. Old entries keep their indices; new foreign receipts keep
/// captured child identities. The omitted owner's target journal is empty.
pub proof fn references_transport<U,I>(eq:spec_fn(Port,U,U)->bool,a:g::Configuration<U,I>,target:g::Configuration<U,I>,offset:nat,owner:usize,child:usize)
    requires transport::related(eq,a,target,offset,owner),g::tokens_valid(a),
        ch::remove_unreferenced(g::kind(a.history),a.state,child),
    ensures ch::remove_unreferenced(g::kind(target.history),target.state,child),
{
    assert forall|actor:usize,token:nat|s::registered(target.state,actor) && target.state.accumulators[actor].contains(token)
        implies g::kind(target.history)(token)!=Some(child) by {
        assert(actor!=owner);assert(s::registered(a.state,actor));
        let i=choose|i:int|0<=i<target.state.accumulators[actor].len() && target.state.accumulators[actor][i]==token;
        let old=a.state.accumulators[actor][i];assert(old<a.history.len());assert(g::owner(a.history[old as int].landed.receipt)==actor);
        assert(token==history::index(a.history,offset,owner,old));assert(a.state.accumulators[actor].contains(old));
        if old<offset {reveal(history::index);assert(token==old);assert(target.history[token as int]==a.history[old as int]);}
        else {assert(obs::receipt_related(eq,a.history[old as int].landed.receipt,target.history[token as int].landed.receipt));}
        assert(token<target.history.len());
        assert(g::captured_child(a.history[old as int].landed.receipt)==g::captured_child(target.history[token as int].landed.receipt));
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(35)]
pub proof fn insert_transport<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,offset:nat,owner:usize,actor:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::well_formed(lib,programs,target),transport::related(eq,a,target,offset,owner),
        own::separated(a.state,owner),g::step(lib,programs,a,z,actor,r::Rule::Insert),guard(a,z,actor,r::Rule::Insert,owner),
    ensures {
        let out=advance(lib,programs,a,z,target,actor,r::Rule::Insert,owner);
        &&& g::step(lib,programs,target,out,actor,r::Rule::Insert) && g::well_formed(lib,programs,out)
        &&& transport::related(eq,z,out,offset,owner) && own::separated(z.state,owner)
        &&& p::project(z.state,ISet::full())==p::project(a.state,ISet::full()) && p::project(out.state,ISet::full())==p::project(target.state,ISet::full())
    },
{
    orchestration::insertion_form(lib,programs,a,z,actor);source_frame(eq,lib,programs,a,z,actor,r::Rule::Insert,owner);
    let f=z.state.control.fibers[actor];let out=advance(lib,programs,a,z,target,actor,r::Rule::Insert,owner);
    assert forall|n:usize,key:Port|s::registered(target.state,n) && target.state.control.fibers[n].provisions.contains(key) implies !f.provisions.contains(key) by {
        assert(s::registered(a.state,n));if n==owner {assert(a.state.control.fibers[n].provisions==target.state.control.fibers[n].provisions);}
    }
    assert(insert::insertion_ready(lib,programs,target,actor,f.parent,f.dependencies,f.provisions,z.roots[actor]));
    insert::insertion_step(lib,programs,target,actor,f.parent,f.dependencies,f.provisions,z.roots[actor]);
    ol::frame(eq,lib,programs,target,out,actor,r::Rule::Insert);ol::configuration_preservation(eq,lib,programs,target,out,actor,r::Rule::Insert);
    p::empty_insertion(target.state,out.state,actor,ISet::full());
    assert(out.state.control.fibers.dom() =~= z.state.control.fibers.dom());
    assert forall|n:usize|s::registered(z.state,n) && n!=owner implies {
        &&& z.state.tables[n].dom()==out.state.tables[n].dom()
        &&& z.state.control.fibers[n]==out.state.control.fibers[n] && z.current[n]==out.current[n]
    } by {if n!=actor {assert(s::registered(a.state,n));}}
    assert forall|n:usize|s::registered(z.state,n) && n!=owner implies out.state.accumulators[n]==history::rename(z.history,offset,owner,z.state.accumulators[n]) by {
        if n==actor {history::rename_laws(a.history,offset,owner,Seq::empty(),0);}else{assert(s::registered(a.state,n));}
    }
}

/// The real source guards suffice on the related registry. This helper has
/// no semantic-theory or preservation assumptions hidden in the guard.
pub proof fn removal_step<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,offset:nat,owner:usize,actor:usize)
    requires transport::related(eq,a,target,offset,owner),g::tokens_valid(a),s::shaped(a.state),s::shaped(target.state),
        g::step(lib,programs,a,z,actor,r::Rule::Remove),actor!=owner,
    ensures g::step(lib,programs,target,orchestration::remove(target,actor),actor,r::Rule::Remove),
{
    let out=orchestration::remove(target,actor);
    references_transport(eq,a,target,offset,owner,actor);
    assert(s::registered(a.state,actor));assert(s::registered(target.state,actor));
    assert(a.state.control.fibers[actor]==target.state.control.fibers[actor]);
    assert(a.state.tables[actor].dom()==target.state.tables[actor].dom());
    assert(target.state.tables[actor] =~= IMap::empty());
    assert forall|n:usize|s::registered(target.state,n) implies target.state.control.fibers[n].parent!=Some(actor) by {
        assert(s::registered(a.state,n));if n==owner {assert(a.state.control.fibers[n].parent==target.state.control.fibers[n].parent);}
    }
    assert(r::frame(target.state.control,out.state.control,actor));
    assert(target.state.control.fibers[actor].retired);
    assert(target.state.control.fibers[actor].phase==crate::Phase::Inactive);
    assert(target.state.control.fibers[actor].committed.is_empty());
    assert(!s::registered(out.state,actor));
    assert forall|n:usize|r::registered(target.state.control,n) implies target.state.control.fibers[n].parent!=Some(actor) by {assert(s::registered(target.state,n));}
    assert(r::step(target.state.control,out.state.control,actor,r::Rule::Remove));
}

pub proof fn removal_relation<U,I>(eq:spec_fn(Port,U,U)->bool,a:g::Configuration<U,I>,target:g::Configuration<U,I>,offset:nat,owner:usize,actor:usize)
    requires transport::related(eq,a,target,offset,owner),actor!=owner,
    ensures transport::related(eq,orchestration::remove(a,actor),orchestration::remove(target,actor),offset,owner),
{
    let z=orchestration::remove(a,actor);let out=orchestration::remove(target,actor);
    assert(out.state.control.fibers.dom() =~= z.state.control.fibers.dom());
    assert forall|n:usize|s::registered(z.state,n) && n!=owner implies {
        &&& z.state.tables[n].dom()==out.state.tables[n].dom()
        &&& z.state.control.fibers[n]==out.state.control.fibers[n] && z.current[n]==out.current[n]
    } by {assert(n!=actor);assert(s::registered(a.state,n));}
    assert forall|n:usize|s::registered(z.state,n) && n!=owner implies out.state.accumulators[n]==history::rename(z.history,offset,owner,z.state.accumulators[n]) by {assert(n!=actor);assert(s::registered(a.state,n));}
}

#[verifier::spinoff_prover]
#[verifier::rlimit(35)]
pub proof fn remove_transport<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,offset:nat,owner:usize,actor:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::well_formed(lib,programs,target),transport::related(eq,a,target,offset,owner),
        own::separated(a.state,owner),g::step(lib,programs,a,z,actor,r::Rule::Remove),actor!=owner,
    ensures {
        let out=advance(lib,programs,a,z,target,actor,r::Rule::Remove,owner);
        &&& g::step(lib,programs,target,out,actor,r::Rule::Remove) && g::well_formed(lib,programs,out)
        &&& transport::related(eq,z,out,offset,owner) && own::separated(z.state,owner)
        &&& p::project(z.state,ISet::full())==p::project(a.state,ISet::full()) && p::project(out.state,ISet::full())==p::project(target.state,ISet::full())
    },
{
    source_frame(eq,lib,programs,a,z,actor,r::Rule::Remove,owner);let out=advance(lib,programs,a,z,target,actor,r::Rule::Remove,owner);
    removal_step(eq,lib,programs,a,z,target,offset,owner,actor);
    assert(z==orchestration::remove(a,actor));removal_relation(eq,a,target,offset,owner,actor);
    ol::configuration_preservation(eq,lib,programs,target,out,actor,r::Rule::Remove);
    p::unique_owner(target.state);p::empty_erasure(target.state,actor,ISet::full());
}

/// Registry edits contain no own value effect. Their identity catalogue item
/// preserves the strict batch on the actual source/target projections.
pub proof fn synchronized_registry<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,actions:Seq<fu::Action<IMap<Port,U>>>,offset:nat,owner:usize,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::well_formed(lib,programs,target),transport::related(eq,a,target,offset,owner),
        own::separated(a.state,owner),g::step(lib,programs,a,z,actor,rule),rule==r::Rule::Insert || rule==r::Rule::Remove,guard(a,z,actor,rule,owner),
        base::synchronized(eq,actions,a,target),
    ensures {
        let out=advance(lib,programs,a,z,target,actor,rule,owner);
        &&& g::step(lib,programs,target,out,actor,rule) && g::well_formed(lib,programs,out) && transport::related(eq,z,out,offset,owner)
        &&& own::separated(z.state,owner) && base::synchronized(eq,actions.push(fu::Action::Identity),z,out)
    },
{
    if rule==r::Rule::Insert {insert_transport(eq,lib,programs,a,z,target,offset,owner,actor);}else{remove_transport(eq,lib,programs,a,z,target,offset,owner,actor);}
    base::own_words_push(actions,fu::Action::Identity);
}

pub proof fn pinned_journal<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,owner:usize)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,z,actor,rule),
        rule==r::Rule::Insert || rule==r::Rule::Remove,own::separated(a.state,owner),guard(a,z,actor,rule,owner),
        own::pinned_tokens(a.history,a.state.accumulators[owner],a.state,owner),
    ensures own::pinned_tokens(z.history,z.state.accumulators[owner],z.state,owner),
        sh::receipt_word(z.history,z.state.accumulators[owner])==sh::receipt_word(a.history,a.state.accumulators[owner]),
{
    source_frame(eq,lib,programs,a,z,actor,rule,owner);sh::resolution_frame(a.state,z.state,owner);
    assert forall|i:int|0<=i<z.state.accumulators[owner].len() implies z.state.accumulators[owner][i]<z.history.len()
        && own::pinned(#[trigger] z.history[z.state.accumulators[owner][i] as int].landed.receipt,z.state,owner) by {
        let token=z.state.accumulators[owner][i];assert(own::pinned(a.history[token as int].landed.receipt,a.state,owner));
        match a.history[token as int].landed.receipt {g::Receipt::Table {receipt}=>{match receipt.inverse {crate::grammar_lift::Inverse::Operation {key,..}=>{assert(crate::grammar_lift::resolve(a.state,owner,key)==crate::grammar_lift::resolve(z.state,owner,key));},_=>{}}},_=>{},}
    }
}

} // verus!
