//! A temporary actor is inserted and removed across a nonempty deleted batch.
//!
//! The shared key is 15 in the source and 10 in the target. Parent 1 exists
//! on both sides with different phases; it is an ownership edge, not an
//! implicit service dependency. The same actual Insert payload is retained.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, dynamic_table_registry as dynamic, foreign_provision_transport as fp,
    mixed_grammar as g, mixed_orchestration as orchestration, mixed_transposition as insert,
    observational_lift as ol, old_journal_closure as closure,
    old_provision_journal_example as base, providing_owner_deletion as own,
    providing_owner_execution as deletion, providing_owner_transport as transport,
    recovery_examples as ex, refinement as r, semantics as s, shared_execution as sh, Phase,
};
use vstd::prelude::*;

verus! {

pub open spec fn prefix()->Seq<g::Configuration<int,nat>> {fp::example_prefix()}
pub open spec fn inserted()->g::Configuration<int,nat> {insert::insert(prefix().last(),3,Some(1),ex::provided(0),ISet::empty(),0nat)}
pub open spec fn retired()->g::Configuration<int,nat> {sh::retire(inserted(),3)}
pub open spec fn removed()->g::Configuration<int,nat> {orchestration::remove(retired(),3)}
pub open spec fn source()->Seq<g::Configuration<int,nat>> {prefix().push(inserted()).push(retired()).push(removed())}
pub open spec fn labels()->Seq<(usize,r::Rule)> {fp::example_labels()+seq![(3usize,r::Rule::Insert),(3usize,r::Rule::Retire),(3usize,r::Rule::Remove)]}
pub open spec fn target_start()->g::Configuration<int,nat> {deletion::delete(ex::library(),base::programs(),prefix(),fp::example_labels(),1).last()}
pub open spec fn target()->Seq<g::Configuration<int,nat>> {
    let a=target_start();let b=dynamic::advance(ex::library(),base::programs(),prefix().last(),inserted(),a,3,r::Rule::Insert,1);
    let c=sh::retire(b,3);let d=dynamic::advance(ex::library(),base::programs(),retired(),removed(),c,3,r::Rule::Remove,1);
    seq![a,b,c,d]
}

pub proof fn cancellation<U,I>(a:g::Configuration<U,I>,id:usize,parent:Option<usize>,deps:ISet<crate::Port>,provisions:ISet<crate::Port>,root:I)
    requires crate::semantics::shaped(a.state),a.roots.dom()==a.state.control.fibers.dom(),a.current.dom()==a.state.control.fibers.dom(),!s::registered(a.state,id),
    ensures orchestration::remove(sh::retire(insert::insert(a,id,parent,deps,provisions,root),id),id)==a,
{
    let out=orchestration::remove(sh::retire(insert::insert(a,id,parent,deps,provisions,root),id),id);
    assert(out.state.control.fibers =~= a.state.control.fibers);
    assert(out.state.tables =~= a.state.tables);assert(out.state.effects =~= a.state.effects);
    assert(out.state.iterators =~= a.state.iterators);assert(out.state.accumulators =~= a.state.accumulators);
    assert(out.roots =~= a.roots);assert(out.current =~= a.current);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn actual_source_registry()
    ensures {
        let lib=ex::library();let programs=base::programs();let a=prefix().last();
        &&& g::execution(lib,programs,base::setup().take(7),base::setup_labels().take(6)) && base::setup().first()==g::empty::<int,nat>() && base::setup()[6]==source().first()
        &&& g::execution(lib,programs,source(),labels()) && g::well_formed(lib,programs,a)
        &&& g::well_formed(lib,programs,inserted()) && g::well_formed(lib,programs,retired()) && g::well_formed(lib,programs,removed())
        &&& own::separated(a.state,1) && own::separated(inserted().state,1) && own::separated(retired().state,1)
        &&& dynamic::guard(a,inserted(),3,r::Rule::Insert,1)
        &&& g::step(lib,programs,a,inserted(),3,r::Rule::Insert) && g::step(lib,programs,inserted(),retired(),3,r::Rule::Retire) && g::step(lib,programs,retired(),removed(),3,r::Rule::Remove)
        &&& !s::registered(a.state,3) && s::registered(inserted().state,3) && !s::registered(removed().state,3)
        &&& inserted().state.control.fibers[3usize].parent==Some(1usize) && inserted().state.control.fibers[3usize].dependencies==ex::provided(0)
        &&& a.state.control.fibers[1usize].phase==Phase::Active && a.state.tables[0usize][ex::key(0)]==15 && a.state.tables[1usize][ex::key(1)]==99
        &&& a.state.accumulators[1usize]==seq![1nat,2nat] && removed()==a
    },
{
    fp::actual_prefix();sh::example_interface();reveal(fp::example_prefix);reveal(base::setup);
    let lib=ex::library();let programs=base::programs();let eq=ex::equality();let a=prefix().last();let b=inserted();let c=retired();let d=removed();
    ol::execution_preservation(eq,lib,programs,prefix(),fp::example_labels());
    assert(insert::insertion_ready(lib,programs,a,3,Some(1),ex::provided(0),ISet::empty(),0nat));
    insert::insertion_step(lib,programs,a,3,Some(1),ex::provided(0),ISet::empty(),0nat);
    assert(dynamic::guard(a,b,3,r::Rule::Insert,1));dynamic::source_frame(eq,lib,programs,a,b,3,r::Rule::Insert,1);
    ch::concrete_child_retirement(b.state,3);assert(g::step(lib,programs,b,c,3,r::Rule::Retire));
    ol::configuration_preservation(eq,lib,programs,b,c,3,r::Rule::Retire);own::interface_frame(eq,lib,programs,b,c,3,r::Rule::Retire,1);
    assert forall|n:usize|s::registered(c.state,n) implies c.state.control.fibers[n].parent!=Some(3usize) by {if n==0{}else if n==1{}else if n==2{}else{assert(n==3);}}
    assert forall|token:nat|token<c.history.len() implies (#[trigger] g::kind(c.history)(token)).is_none() by {if token==0{}else if token==1{}else{assert(token==2);}}
    assert(ch::remove_unreferenced(g::kind(c.history),c.state,3)) by {
        assert forall|actor:usize,token:nat|s::registered(c.state,actor) && c.state.accumulators[actor].contains(token) implies g::kind(c.history)(token)!=Some(3usize) by {
            let i=choose|i:int|0<=i<c.state.accumulators[actor].len() && c.state.accumulators[actor][i]==token;assert(token<c.history.len());
        }
    }
    assert(r::frame(c.state.control,d.state.control,3));assert(g::step(lib,programs,c,d,3,r::Rule::Remove));ol::configuration_preservation(eq,lib,programs,c,d,3,r::Rule::Remove);
    closure::append_execution(lib,programs,prefix(),fp::example_labels(),b,3,r::Rule::Insert);
    closure::append_execution(lib,programs,prefix().push(b),fp::example_labels().push((3usize,r::Rule::Insert)),c,3,r::Rule::Retire);
    closure::append_execution(lib,programs,prefix().push(b).push(c),fp::example_labels().push((3usize,r::Rule::Insert)).push((3usize,r::Rule::Retire)),d,3,r::Rule::Remove);
    assert(labels() =~= fp::example_labels().push((3usize,r::Rule::Insert)).push((3usize,r::Rule::Retire)).push((3usize,r::Rule::Remove)));
    cancellation(a,3,Some(1),ex::provided(0),ISet::empty(),0nat);
}

#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn actual_registry_transport()
    ensures {
        let lib=ex::library();let programs=base::programs();let kept=target();let a=prefix().last();
        &&& g::execution(lib,programs,base::setup().take(7),base::setup_labels().take(6)) && base::setup().first()==g::empty::<int,nat>() && base::setup()[6]==source().first()
        &&& g::execution(lib,programs,source(),labels())
        &&& kept.first()==source().first() && g::execution(lib,programs,kept,seq![(3usize,r::Rule::Insert),(3usize,r::Rule::Retire),(3usize,r::Rule::Remove)])
        &&& transport::related(ex::equality(),removed(),kept.last(),1,1) && g::well_formed(lib,programs,kept.last())
        &&& kept[1].state.control.fibers[3usize]==inserted().state.control.fibers[3usize] && kept[1].roots[3usize]==inserted().roots[3usize]
        &&& kept[1].state.control.fibers[3usize].parent==Some(1usize) && kept[1].state.control.fibers[1usize].phase==Phase::Inactive
        &&& a.state.control.fibers[1usize].phase==Phase::Active && a.state.accumulators[1usize]==seq![1nat,2nat]
        &&& removed()==a && kept.last()==kept.first() && !s::registered(kept.last().state,3)
        &&& removed().state.tables[0usize][ex::key(0)]==15 && kept.last().state.tables[0usize][ex::key(0)]==10
        &&& removed().state.tables[1usize][ex::key(1)]==99 && kept.last().state.tables[1usize].is_empty()
    },
{
    actual_source_registry();fp::actual_prefix();sh::example_interface();
    let lib=ex::library();let programs=base::programs();let eq=ex::equality();let a=prefix().last();let b=inserted();let c=retired();let d=removed();let kept=target();
    fp::prefix_batch(eq,lib,programs,prefix(),fp::example_labels(),1);
    // The deleted prefix contains only owner lifecycle steps. Derive its
    // singleton result from the execution theorem, without unfolding runs.
    deletion::delete_execution(eq,lib,programs,prefix(),fp::example_labels(),1);
    let erased=deletion::delete(lib,programs,prefix(),fp::example_labels(),1);
    reveal_with_fuel(sh::labels_without,4);
    assert(sh::labels_without(fp::example_labels(),1).len()==0);
    assert(erased.len()==1);
    assert(erased.last()==erased.first());
    assert(kept[0]==prefix().first());
    assert(kept[1]==dynamic::advance(lib,programs,a,b,kept[0],3,r::Rule::Insert,1));
    dynamic::insert_transport(eq,lib,programs,a,b,kept[0],1,1,3);
    assert(g::step(lib,programs,kept[0],kept[1],3,r::Rule::Insert));
    assert(g::well_formed(lib,programs,kept[1]));
    assert(transport::related(eq,b,kept[1],1,1));
    transport::control_transport(eq,lib,programs,b,c,kept[1],1,1,3,r::Rule::Retire);
    assert(transport::advance(lib,programs,b,c,kept[1],3,r::Rule::Retire,1)==kept[2]);
    assert(g::step(lib,programs,kept[1],kept[2],3,r::Rule::Retire));
    assert(g::well_formed(lib,programs,kept[2]));
    assert(transport::related(eq,c,kept[2],1,1));
    assert(kept[3]==dynamic::advance(lib,programs,c,d,kept[2],3,r::Rule::Remove,1));
    dynamic::remove_transport(eq,lib,programs,c,d,kept[2],1,1,3);
    assert(g::step(lib,programs,kept[2],kept[3],3,r::Rule::Remove));
    assert(g::well_formed(lib,programs,kept[3]));
    assert(transport::related(eq,d,kept[3],1,1));
    assert forall|i:int|0<=i<3 implies g::step(lib,programs,kept[i],kept[i+1],3,seq![r::Rule::Insert,r::Rule::Retire,r::Rule::Remove][i]) by {if i==0{}else if i==1{}else{assert(i==2);}}
    assert(kept[1]==insert::insert(kept[0],3,Some(1),ex::provided(0),ISet::empty(),0nat));
    cancellation(kept[0],3,Some(1),ex::provided(0),ISet::empty(),0nat);
    assert(kept[3]==kept[0]);
    reveal(fp::example_prefix);reveal(base::setup);
    assert(kept[0]==source().first());
    assert(kept[0].state.tables[0usize][ex::key(0)]==10);
}

/// The extra dependency restriction is not an O-Insert guard: this real
/// insertion is accepted by the source rule but would invalidate private-key
/// separation. The dynamic deletion profile therefore rejects this payload.
#[verifier::spinoff_prover]
#[verifier::rlimit(25)]
pub proof fn private_dependency_boundary()
    ensures {
        let a=prefix().last();let z=insert::insert(a,3,Some(1),ex::provided(0).union(ex::provided(1)),ISet::empty(),0nat);
        &&& g::step(ex::library(),base::programs(),a,z,3,r::Rule::Insert)
        &&& !dynamic::guard(a,z,3,r::Rule::Insert,1) && !own::separated(z.state,1)
    },
{
    actual_source_registry();reveal(fp::example_prefix);reveal(base::setup);
    let a=prefix().last();let deps=ex::provided(0).union(ex::provided(1));let z=insert::insert(a,3,Some(1),deps,ISet::empty(),0nat);
    assert(insert::insertion_ready(ex::library(),base::programs(),a,3,Some(1),deps,ISet::empty(),0nat));
    insert::insertion_step(ex::library(),base::programs(),a,3,Some(1),deps,ISet::empty(),0nat);
    assert(z.state.control.fibers[3usize].dependencies.contains(ex::key(1)));assert(a.state.control.fibers[1usize].provisions.contains(ex::key(1)));
    assert(!dynamic::guard(a,z,3,r::Rule::Insert,1));
    assert(s::registered(z.state,3));assert(crate::dependent_lift::declarations(z.state,3).contains(ex::key(1)));
    assert(z.state.control.fibers[1usize].provisions.contains(ex::key(1)));
    assert(!crate::dependent_lift::declarations(z.state,3).disjoint(z.state.control.fibers[1usize].provisions));
    assert(!own::separated(z.state,1));
}

} // verus!
