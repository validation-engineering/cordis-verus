//! Actual surviving lifecycle steps when the deleted owner may provide keys.
//!
//! Foreign declarations exclude those provision keys. Their publication guards
//! therefore survive omission of the owner's table, while common dependencies
//! may still hold different values. Target landings retain their own actual
//! receipts and compressed history tokens. Value replay supplies successful
//! target calls separately; lifecycle legality is a conclusion of this module.
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_lift as dep, foreign_unload as fu, grammar_lift as lift, mixed_grammar as g,
    mixed_observational_runs as obs, observational_grammar as og, observational_lift as ol,
    partial_independence as pi, preservation as inv, projection as p,
    providing_owner_deletion as deletion, refinement as r, semantics as s, shared_execution as sh,
    shared_replay as replay, shared_unload_execution as history, strict_journal as sj, Binding,
    Phase, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn controls<U,I>(source:g::Configuration<U,I>,target:g::Configuration<U,I>,owner:usize)->bool {
    &&& s::registered(source.state,owner)
    &&& target.state.control.fibers.dom()==source.state.control.fibers.dom()
    &&& r::interface_same(source.state.control.fibers[owner],target.state.control.fibers[owner])
    &&& source.state.control.fibers[owner].retired==target.state.control.fibers[owner].retired
    &&& target.state.control.fibers[owner].phase==Phase::Inactive && target.state.control.fibers[owner].committed.is_empty()
    &&& target.state.tables[owner].is_empty() && target.state.accumulators[owner].len()==0
    &&& target.roots==source.roots && target.current[owner].is_none()
    &&& forall|n:usize| s::registered(source.state,n) && n!=owner ==> {
        &&& source.state.tables[n].dom()==target.state.tables[n].dom()
        &&& source.state.control.fibers[n]==target.state.control.fibers[n] && source.current[n]==target.current[n]
    }
}
pub open spec fn related<U,I>(eq:spec_fn(Port,U,U)->bool,source:g::Configuration<U,I>,target:g::Configuration<U,I>,offset:nat,owner:usize)->bool {
    &&& controls(source,target,owner) && history::histories(eq,source.history,target.history,offset,owner)
    &&& forall|actor:usize| s::registered(source.state,actor) && actor!=owner ==>
        target.state.accumulators[actor]==history::rename(source.history,offset,owner,source.state.accumulators[actor])
}
pub open spec fn advance<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:g::Configuration<U,I>,next:g::Configuration<U,I>,target:g::Configuration<U,I>,actor:usize,rule:r::Rule,owner:usize)->g::Configuration<U,I> {
    history::advance(lib,programs,source,next,target,actor,rule,owner)
}

pub proof fn initial_related<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,owner:usize,eq:spec_fn(Port,U,U)->bool)
    requires g::well_formed(lib,programs,a),s::registered(a.state,owner),a.state.control.fibers[owner].phase==Phase::Inactive,
        a.state.tables[owner].is_empty(),
    ensures related(eq,a,a,a.history.len(),owner),
{
    reveal(history::index);
    assert(a.state.iterators[owner]==dep::marker(a.current[owner]));assert(a.current[owner].is_none());
    assert forall|actor:usize| s::registered(a.state,actor) && actor!=owner implies
        a.state.accumulators[actor]==history::rename(a.history,a.history.len(),owner,a.state.accumulators[actor]) by {
        assert(a.state.accumulators[actor] =~= history::rename(a.history,a.history.len(),owner,a.state.accumulators[actor])) by {
            assert forall|i:int| 0<=i<a.state.accumulators[actor].len() implies a.state.accumulators[actor][i]
                ==history::rename(a.history,a.history.len(),owner,a.state.accumulators[actor])[i] by {assert(a.state.accumulators[actor][i]<a.history.len());}
        }
    }
}
pub proof fn separated_target<U,I>(source:g::Configuration<U,I>,target:g::Configuration<U,I>,owner:usize)
    requires controls(source,target,owner),deletion::separated(source.state,owner),
    ensures deletion::separated(target.state,owner),
{
    assert forall|actor:usize| s::registered(target.state,actor) && actor!=owner implies
        dep::declarations(target.state,actor).disjoint(target.state.control.fibers[owner].provisions) by {
        assert(s::registered(source.state,actor));
    }
}

/// Only the foreign actor's dependency keys must retain publication. The
/// omitted owner's provision may change publication at other keys freely.
pub proof fn publication<U,I>(source:g::Configuration<U,I>,target:g::Configuration<U,I>,owner:usize,actor:usize,view:ISet<Binding>)
    requires inv::well_formed(source.state),inv::well_formed(target.state),controls(source,target,owner),
        deletion::separated(source.state,owner),s::registered(source.state,actor),actor!=owner,
    ensures s::target(source.state,actor,view)==s::target(target.state,actor,view),
        s::coherent(source.state,actor)==s::coherent(target.state,actor),
{
    assert forall|key:Port,n:usize| source.state.control.fibers[actor].dependencies.contains(key) implies
        s::publishes(source.state,key,n)==s::publishes(target.state,key,n) by {
        if n==owner {
            assert(dep::declarations(source.state,actor).contains(key));
            assert(!source.state.control.fibers[owner].provisions.contains(key));
            assert(!source.state.tables[owner].dom().contains(key));
        } else if s::registered(source.state,n) {assert(source.state.control.fibers[n]==target.state.control.fibers[n]);}
    }
}

/// Provision changes only the acting table's domain. Operations and Unit
/// preserve every domain, including a shared provider's existing binding.
pub proof fn dependent_domains<A,X,U,B,I>(lib:g::Library<A,X,U,B>,node:dep::Node<A,X,U,B,I>,a:s::State<U>,actor:usize)
    requires inv::well_formed(a),dep::run(lib,node,a,actor).is_some(),
    ensures {
        let z=dep::run(lib,node,a,actor).unwrap().state;
        &&& z.control==a.control && z.effects==a.effects && z.iterators==a.iterators && z.accumulators==a.accumulators
        &&& forall|n:usize| s::registered(a,n) && n!=actor ==> z.tables[n].dom()==a.tables[n].dom()
    },
{
    lift::run_preservation(dep::stage(lib,node),a,actor);
    match node {
        crate::dependent_grammar::Node::Provision {..}=>{},
        _=>{sh::operation_domains(lib,node,a,actor);},
    }
}

#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn landing_related<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,out:g::Configuration<U,I>,offset:nat,owner:usize,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::well_formed(lib,programs,target),related(eq,a,target,offset,owner),actor!=owner,
        g::step(lib,programs,a,z,actor,rule),g::step(lib,programs,target,out,actor,rule),g::landing(a,z,rule),g::landing(target,out,rule),
        replay::operational_mixed(programs(actor)(a.current[actor].unwrap())),
        g::entry(lib,programs,a,actor).landed.next==g::entry(lib,programs,target,actor).landed.next,
        obs::receipt_related(eq,g::entry(lib,programs,a,actor).landed.receipt,g::entry(lib,programs,target,actor).landed.receipt),
    ensures related(eq,z,out,offset,owner),
{
    ol::frame(eq,lib,programs,a,z,actor,rule);ol::frame(eq,lib,programs,target,out,actor,rule);
    let node=replay::dependent(programs(actor)(a.current[actor].unwrap()));
    sh::source_domains(eq,lib,programs,a,z,actor,rule);sh::source_domains(eq,lib,programs,target,out,actor,rule);
    sh::operation_domains(lib,node,a.state,actor);sh::operation_domains(lib,node,target.state,actor);
    let old=g::entry(lib,programs,a,actor);let new=g::entry(lib,programs,target,actor);
    history::histories_push(eq,a.history,target.history,old,new,offset,owner);
    assert forall|n:usize| s::registered(z.state,n) && n!=owner implies {
        &&& z.state.tables[n].dom()==out.state.tables[n].dom()
        &&& z.state.control.fibers[n]==out.state.control.fibers[n] && z.current[n]==out.current[n]
    } by {if n!=actor {assert(a.current[n]==target.current[n]);}}
    assert forall|n:usize| s::registered(z.state,n) && n!=owner implies out.state.accumulators[n]
        ==history::rename(z.history,offset,owner,z.state.accumulators[n]) by {
        assert(s::registered(a.state,n));
        assert forall|i:int| 0<=i<a.state.accumulators[n].len() implies a.state.accumulators[n][i]<=a.history.len() by {assert(a.state.accumulators[n][i]<a.history.len());}
        if n==actor {
            history::rename_laws(a.history,offset,owner,a.state.accumulators[n],a.history.len());
            history::rename_append(a.history,old,offset,owner,a.state.accumulators[n].push(a.history.len()));
        } else {history::rename_append(a.history,old,offset,owner,a.state.accumulators[n]);}
    }
}

/// A value-replay theorem supplies the successful target call and its actual
/// related receipt. This lemma derives every lifecycle guard and target step.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn landing_from_call<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,offset:nat,owner:usize,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::well_formed(lib,programs,target),related(eq,a,target,offset,owner),actor!=owner,
        deletion::separated(a.state,owner),g::step(lib,programs,a,z,actor,rule),g::landing(a,z,rule),
        replay::operational_mixed(programs(actor)(a.current[actor].unwrap())),
        g::run(lib,programs(actor)(a.current[actor].unwrap()),target.state,actor).is_some(),
        g::entry(lib,programs,a,actor).landed.next==g::entry(lib,programs,target,actor).landed.next,
        obs::receipt_related(eq,g::entry(lib,programs,a,actor).landed.receipt,g::entry(lib,programs,target,actor).landed.receipt),
    ensures {
        let out=advance(lib,programs,a,z,target,actor,rule,owner);
        &&& g::step(lib,programs,target,out,actor,rule) && g::well_formed(lib,programs,out) && related(eq,z,out,offset,owner)
        &&& p::project(out.state,ISet::full())==p::project(g::entry(lib,programs,target,actor).landed.state,ISet::full())
    },
{
    ol::frame(eq,lib,programs,a,z,actor,rule);
    publication(a,target,owner,actor,a.state.control.fibers[actor].committed);
    let out=advance(lib,programs,a,z,target,actor,rule,owner);assert(g::step(lib,programs,target,out,actor,rule));
    ol::configuration_preservation(eq,lib,programs,target,out,actor,rule);ol::frame(eq,lib,programs,target,out,actor,rule);
    landing_related(eq,lib,programs,a,z,target,out,offset,owner,actor,rule);
    let node=replay::dependent(programs(actor)(a.current[actor].unwrap()));
    let landed=dep::run(lib,node,target.state,actor).unwrap().state;lift::run_preservation(dep::stage(lib,node),target.state,actor);p::unique_owner(landed);
    p::lifecycle_edit(landed,actor,z.state.control.fibers[actor].phase,target.state.control.fibers[actor].committed,
        dep::marker(out.current[actor]),target.state.accumulators[actor].push(target.history.len()),ISet::full());
}

/// Owner Provision is omitted with its actual receipt. Foreign table domains,
/// lifecycle metadata and compressed journals remain related.
pub proof fn own_landing<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,offset:nat,owner:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),related(eq,a,target,offset,owner),
        deletion::separated(a.state,owner),g::step(lib,programs,a,z,owner,rule),g::landing(a,z,rule),
        deletion::table_node(programs(owner)(a.current[owner].unwrap())),
    ensures related(eq,z,target,offset,owner),
{
    ol::frame(eq,lib,programs,a,z,owner,rule);
    let node=replay::dependent(programs(owner)(a.current[owner].unwrap()));dependent_domains(lib,node,a.state,owner);
    assert(a.state.control.fibers.dom() =~= z.state.control.fibers.dom());
    let entry=g::entry(lib,programs,a,owner);history::histories_skip(eq,a.history,target.history,entry,offset,owner);
    assert forall|n:usize| s::registered(z.state,n) && n!=owner implies {
        &&& z.state.tables[n].dom()==target.state.tables[n].dom()
        &&& z.state.control.fibers[n]==target.state.control.fibers[n] && z.current[n]==target.current[n]
    } by {assert(s::registered(a.state,n));assert(a.state.control.fibers[n]==z.state.control.fibers[n]);}
    assert forall|n:usize| s::registered(z.state,n) && n!=owner implies target.state.accumulators[n]
        ==history::rename(z.history,offset,owner,z.state.accumulators[n]) by {
        assert(s::registered(a.state,n));assert(z.state.accumulators[n]==a.state.accumulators[n]);
        assert forall|i:int| 0<=i<a.state.accumulators[n].len() implies a.state.accumulators[n][i]<=a.history.len() by {assert(a.state.accumulators[n][i]<a.history.len());}
        history::rename_append(a.history,entry,offset,owner,a.state.accumulators[n]);
    }
}

pub proof fn control_transport<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,z:g::Configuration<U,I>,target:g::Configuration<U,I>,offset:nat,owner:usize,actor:usize,rule:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::well_formed(lib,programs,target),related(eq,a,target,offset,owner),
        deletion::separated(a.state,owner),g::step(lib,programs,a,z,actor,rule),replay::fragment_step(programs,a,z,actor,rule),!g::landing(a,z,rule),
    ensures {
        let out=advance(lib,programs,a,z,target,actor,rule,owner);
        &&& related(eq,z,out,offset,owner) && g::well_formed(lib,programs,out)
        &&& (sh::keep(actor,rule,owner) ==> g::step(lib,programs,target,out,actor,rule))
        &&& p::project(out.state,ISet::full())==p::project(target.state,ISet::full())
    },
{
    let out=advance(lib,programs,a,z,target,actor,rule,owner);
    sh::source_domains(eq,lib,programs,a,z,actor,rule);ol::frame(eq,lib,programs,a,z,actor,rule);
    if actor!=owner {publication(a,target,owner,actor,z.state.control.fibers[actor].committed);}
    if sh::keep(actor,rule,owner) {
        if rule==r::Rule::Retire {
            assert(r::frame(target.state.control,out.state.control,actor));assert(s::child_retire(target.state,out.state,actor));
        }
        assert(g::step(lib,programs,target,out,actor,rule));ol::configuration_preservation(eq,lib,programs,target,out,actor,rule);
        p::unique_owner(target.state);p::unique_owner(out.state);
        assert(p::bindings_equal(target.state,out.state));p::projection_equal(target.state,out.state,ISet::full());
    }
    assert forall|n:usize| s::registered(z.state,n) && n!=owner implies {
        &&& z.state.tables[n].dom()==out.state.tables[n].dom()
        &&& z.state.control.fibers[n]==out.state.control.fibers[n] && z.current[n]==out.current[n]
    } by {if n!=actor {assert(a.state.control.fibers[n]==z.state.control.fibers[n]);}}
    assert forall|n:usize| s::registered(z.state,n) && n!=owner implies out.state.accumulators[n]
        ==history::rename(z.history,offset,owner,z.state.accumulators[n]) by {
        if n==actor && rule==r::Rule::Begin {history::rename_laws(a.history,offset,owner,Seq::empty(),0);}
        else {assert(a.state.accumulators[n]==z.state.accumulators[n]);}
    }
}

pub proof fn no_users<U,I>(source:g::Configuration<U,I>,target:g::Configuration<U,I>,owner:usize,actor:usize)
    requires controls(source,target,owner),!r::relied(source.state.control,actor),
    ensures !r::relied(target.state.control,actor),
{
    if r::relied(target.state.control,actor) {
        let (n,b)=choose|n:usize,b:Binding| s::registered(target.state,n) && n!=actor && target.state.control.fibers[n].phase!=Phase::Inactive
            && target.state.control.fibers[n].committed.contains(b) && b.provider==actor;
        assert(n!=owner);assert(s::registered(source.state,n));assert(source.state.control.fibers[n]==target.state.control.fibers[n]);
        assert(r::relied(source.state.control,actor));
    }
}

/// Only receipts actually consumed by this foreign Unload need be Unit or
/// Operation. Intervening owner Provision receipts remain in the source history
/// and do not become an artificial premise on the foreign inverse word.
#[verifier::spinoff_prover]
#[verifier::rlimit(30)]
pub proof fn restore_transport<U,I>(eq:spec_fn(Port,U,U)->bool,
    left:Seq<g::Entry<U,I>>,right:Seq<g::Entry<U,I>>,tokens:Seq<nat>,offset:nat,owner:usize,actor:usize,source:s::State<U>,target:s::State<U>,reference:IMap<Port,U>)
    requires actor!=owner,inv::well_formed(source),inv::well_formed(target),s::registered(target,actor),source.control.fibers[actor]==target.control.fibers[actor],
        history::histories(eq,left,right,offset,owner),fu::tracked_tokens(left,tokens,offset,actor),g::restore(left,tokens,source,actor).is_some(),
        forall|i:int| 0<=i<tokens.len() ==> history::simple(#[trigger] left[tokens[i] as int].landed.receipt),
        pi::run(sh::receipt_word(left,tokens),reference).is_some(),pi::context_eq(eq)(reference,p::project(target,ISet::full())),
    ensures {
        let out=g::restore(right,history::rename(left,offset,owner,tokens),target,actor);
        &&& out.is_some() && inv::well_formed(out.unwrap()) && out.unwrap().control==target.control
        &&& forall|n:usize| s::registered(target,n) ==> out.unwrap().tables[n].dom()==target.tables[n].dom()
        &&& pi::context_eq(eq)(pi::run(sh::receipt_word(left,tokens),reference).unwrap(),p::project(out.unwrap(),ISet::full()))
    },
    decreases tokens.len(),
{
    history::rename_laws(left,offset,owner,tokens,0);
    if tokens.len()>0 {
        let old=tokens.last();let new=history::index(left,offset,owner,old);let a=left[old as int].landed.receipt;let b=right[new as int].landed.receipt;
        assert(offset<=old<left.len());assert(g::owner(a)==actor);assert(obs::receipt_related(eq,a,b));
        assert(history::simple(a));
        sj::run_prepend(sh::flat(a),sh::receipt_word(left,tokens.drop_last()),reference);
        history::one_inverse(eq,a,b,source,target,actor,reference);
        let target_after=g::undo(b,target).unwrap();let source_after=g::undo(a,source).unwrap();let after=sh::flat(a)(reference).unwrap();
        assert forall|i:int| 0<=i<tokens.drop_last().len() implies history::simple(#[trigger] left[tokens.drop_last()[i] as int].landed.receipt) by {assert(tokens.drop_last()[i]==tokens[i]);}
        restore_transport(eq,left,right,tokens.drop_last(),offset,owner,actor,source_after,target_after,after);
        assert forall|n:usize| s::registered(target,n) implies g::restore(right,history::rename(left,offset,owner,tokens),target,actor).unwrap().tables[n].dom()==target.tables[n].dom() by {
            assert(s::registered(target_after,n));
        }
    }
}

/// The source foreign restore also preserves domains; unrelated owner
/// Provision records elsewhere in the history impose no restriction.
pub proof fn restore_domains<U,I>(entries:Seq<g::Entry<U,I>>,tokens:Seq<nat>,offset:nat,input:s::State<U>,actor:usize)
    requires inv::well_formed(input),fu::tracked_tokens(entries,tokens,offset,actor),g::restore(entries,tokens,input,actor).is_some(),
        forall|i:int| 0<=i<tokens.len() ==> history::simple(#[trigger] entries[tokens[i] as int].landed.receipt),
    ensures g::restore(entries,tokens,input,actor).unwrap().control==input.control,
        forall|n:usize| s::registered(input,n) ==> g::restore(entries,tokens,input,actor).unwrap().tables[n].dom()==input.tables[n].dom(),
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let receipt=entries[tokens.last() as int].landed.receipt;assert(history::simple(receipt));
        assert(sh::pinned(receipt,input,actor));fu::table_inverse_projects(receipt,input);
        sh::inverse_definedness(receipt,input,actor);let after=g::undo(receipt,input).unwrap();
        assert forall|i:int| 0<=i<tokens.drop_last().len() implies history::simple(#[trigger] entries[tokens.drop_last()[i] as int].landed.receipt) by {assert(tokens.drop_last()[i]==tokens[i]);}
        restore_domains(entries,tokens.drop_last(),offset,after,actor);
        assert forall|n:usize| s::registered(input,n) implies g::restore(entries,tokens,input,actor).unwrap().tables[n].dom()==input.tables[n].dom() by {assert(s::registered(after,n));}
    }
}

} // verus!
