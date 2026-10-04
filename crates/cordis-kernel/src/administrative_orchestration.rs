//! Pure-control lifecycle and external orchestration exchange.
//!
//! Begin, Leave and aborting Divert do not run an effect or append a receipt.
//! Inactive insertion/removal and retirement preserve their actual reads,
//! except that Begin cannot move after retirement of its own actor. Reverse
//! steps are constructed and the complete final configuration is unchanged.
#[cfg(verus_keep_ghost)]
use crate::{
    child_history as ch, mixed_grammar as g, mixed_orchestration as o, mixed_transposition as t,
    observational_grammar as og, observational_lift as ol, preservation as inv, refinement as r,
    semantics as s, Binding, Phase, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn administrative<U,I>(a:g::Configuration<U,I>,b:g::Configuration<U,I>,rule:r::Rule)->bool {
    rule==r::Rule::Begin || rule==r::Rule::Leave || rule==r::Rule::Divert && b.history==a.history
}
pub open spec fn crossing_guard(actor:usize,rule:r::Rule,id:usize,external:r::Rule)->bool {
    (external==r::Rule::Insert || external==r::Rule::Retire || external==r::Rule::Remove)
        && !(rule==r::Rule::Begin && external==r::Rule::Retire && actor==id)
}
pub open spec fn reverse<U,I>(a:g::Configuration<U,I>,b:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,id:usize,external:r::Rule)->g::Configuration<U,I> {
    let middle=o::intermediate(a,z,id,external);let f=b.state.control.fibers[actor];
    g::edit(middle,actor,f.phase,f.committed,b.current[actor],b.state.accumulators[actor])
}

/// Registry names, declarations, tables and histories are fixed by these
/// actual lifecycle rules. At Begin the old accumulator was already empty.
pub proof fn control_frame<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,b:g::Configuration<U,I>,actor:usize,rule:r::Rule)
    requires inv::well_formed(a.state),g::step(lib,programs,a,b,actor,rule),administrative(a,b,rule),
    ensures {
        let f=b.state.control.fibers[actor];
        &&& b==g::edit(a,actor,f.phase,f.committed,b.current[actor],b.state.accumulators[actor])
        &&& s::registered(a.state,actor) && s::registered(b.state,actor) && f.phase!=Phase::Inactive
        &&& b.state.control.fibers.dom()==a.state.control.fibers.dom()
        &&& b.state.tables==a.state.tables && b.state.effects==a.state.effects && b.state.accumulators==a.state.accumulators
        &&& b.history==a.history && b.roots==a.roots
        &&& forall|n:usize| s::registered(a.state,n) ==> r::interface_same(a.state.control.fibers[n],b.state.control.fibers[n])
            && (n!=actor ==> a.state.control.fibers[n]==b.state.control.fibers[n])
    },
{
    if rule==r::Rule::Divert {assert(!g::landing(a,b,rule));}
    if rule==r::Rule::Begin {assert(a.state.accumulators[actor] =~= Seq::<nat>::empty());}
    assert(b.state.control.fibers.dom() =~= a.state.control.fibers.dom());
    assert(b.state.accumulators =~= a.state.accumulators);
}

pub proof fn external_form<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,z:g::Configuration<U,I>,id:usize,rule:r::Rule)
    requires g::step(lib,programs,a,z,id,rule),rule==r::Rule::Insert || rule==r::Rule::Retire || rule==r::Rule::Remove,
    ensures z==o::intermediate(a,z,id,rule),
{
    match rule {
        r::Rule::Insert=>{o::insertion_form(lib,programs,a,z,id);},
        r::Rule::Retire=>{
            let expected=o::retire(a,id);
            assert(r::step(a.state.control,z.state.control,id,r::Rule::Retire));
            assert(z.state.control.fibers.dom() =~= expected.state.control.fibers.dom()) by {
                assert forall|n:usize| z.state.control.fibers.dom().contains(n)==expected.state.control.fibers.dom().contains(n) by {
                    if n!=id {assert(r::frame(a.state.control,z.state.control,id));assert(s::registered(a.state,n)==s::registered(z.state,n));}
                }
            }
            assert(z.state.control.fibers =~= expected.state.control.fibers) by {
                assert forall|n:usize| z.state.control.fibers.dom().contains(n) implies z.state.control.fibers[n]==expected.state.control.fibers[n] by {
                    if n!=id {assert(r::frame(a.state.control,z.state.control,id));assert(s::registered(a.state,n));}
                }
            }
        },
        _=>{},
    }
}

/// Only Begin/self-Retire needs an extra guard. In particular an already
/// incoherent Leave or aborting Divert can move after retirement of itself.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn diamond<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,b:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,id:usize,external:r::Rule)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,b,actor,rule),administrative(a,b,rule),
        g::step(lib,programs,b,z,id,external),crossing_guard(actor,rule,id,external),
    ensures {
        let middle=o::intermediate(a,z,id,external);let last=reverse(a,b,z,actor,id,external);
        &&& g::step(lib,programs,a,middle,id,external) && g::step(lib,programs,middle,last,actor,rule)
        &&& last==z && last.history==a.history
        &&& g::well_formed(lib,programs,middle) && g::well_formed(lib,programs,last)
    },
{
    control_frame(lib,programs,a,b,actor,rule);external_form(lib,programs,b,z,id,external);
    let middle=o::intermediate(a,z,id,external);let last=reverse(a,b,z,actor,id,external);
    match external {
        r::Rule::Insert=>{
            o::insertion_form(lib,programs,b,z,id);
            let f=z.state.control.fibers[id];assert(!s::registered(a.state,id));assert(id!=actor);
            assert forall|n:usize,k:Port| s::registered(a.state,n) && a.state.control.fibers[n].provisions.contains(k)
                implies !f.provisions.contains(k) by {assert(s::registered(b.state,n));assert(b.state.control.fibers[n].provisions.contains(k));}
            assert(t::insertion_ready(lib,programs,a,id,f.parent,f.dependencies,f.provisions,z.roots[id]));
            t::insertion_step(lib,programs,a,id,f.parent,f.dependencies,f.provisions,z.roots[id]);
            t::insertion_target(a,id,f.parent,f.dependencies,f.provisions,z.roots[id],actor,b.state.control.fibers[actor].committed);
        },
        r::Rule::Retire=>{
            assert(s::registered(a.state,id));ch::concrete_child_retirement(a.state,id);
            assert(g::step(lib,programs,a,middle,id,r::Rule::Retire));
            if actor!=id {o::retire_target(a,id,actor,b.state.control.fibers[actor].committed);}
            else {assert(rule!=r::Rule::Begin);assert(!s::coherent(middle.state,actor));}
        },
        r::Rule::Remove=>{
            assert(r::step(b.state.control,z.state.control,id,r::Rule::Remove));
            assert(s::registered(a.state,id));assert(id!=actor);
            assert(a.state.control.fibers[id]==b.state.control.fibers[id]);
            assert(r::frame(a.state.control,middle.state.control,id));
            assert forall|n:usize| r::registered(a.state.control,n) implies a.state.control.fibers[n].parent!=Some(id) by {
                assert(s::registered(b.state,n));assert(r::interface_same(a.state.control.fibers[n],b.state.control.fibers[n]));
            }
            assert(r::step(a.state.control,middle.state.control,id,r::Rule::Remove));
            assert(ch::remove_unreferenced(g::kind(a.history),a.state,id));
            assert(g::step(lib,programs,a,middle,id,r::Rule::Remove));
            o::remove_target(a,id,actor,b.state.control.fibers[actor].committed);
        },
        _=>{},
    }
    assert(g::step(lib,programs,middle,last,actor,rule));
    assert(z.state.control.fibers =~= last.state.control.fibers);
    assert(z.state.iterators =~= last.state.iterators);assert(z.state.accumulators =~= last.state.accumulators);
    assert(z.current =~= last.current);
    ol::configuration_preservation(eq,lib,programs,a,middle,id,external);
    ol::configuration_preservation(eq,lib,programs,middle,last,actor,rule);
}

/// The full endpoint, including history, is identical, so every original
/// legal suffix is reused literally in the constructed reverse execution.
pub proof fn suffix<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,b:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,id:usize,external:r::Rule,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,b,actor,rule),administrative(a,b,rule),
        g::step(lib,programs,b,z,id,external),crossing_guard(actor,rule,id,external),g::execution(lib,programs,source,labels),source.first()==z,
    ensures {
        let middle=o::intermediate(a,z,id,external);let result=seq![a,middle]+source;let reordered=seq![(id,external),(actor,rule)]+labels;
        &&& g::execution(lib,programs,result,reordered) && result.first()==a && result.last()==source.last()
        &&& forall|i:int| 0<=i<result.len() ==> g::well_formed(lib,programs,result[i])
    },
{
    diamond(eq,lib,programs,a,b,z,actor,rule,id,external);
    let middle=o::intermediate(a,z,id,external);let result=seq![a,middle]+source;let reordered=seq![(id,external),(actor,rule)]+labels;
    assert(g::execution(lib,programs,result,reordered)) by {
        assert forall|i:int| 0<=i<reordered.len() implies g::step(lib,programs,result[i],result[i+1],reordered[i].0,reordered[i].1) by {
            if i==0 {assert(result[i]==a);assert(result[i+1]==middle);}
            else if i==1 {assert(result[i]==middle);assert(result[i+1]==z);}
            else {assert(2<=i);assert(result[i]==source[i-2]);assert(result[i+1]==source[i-1]);assert(reordered[i]==labels[i-2]);
                assert(g::step(lib,programs,source[i-2],source[i-1],labels[i-2].0,labels[i-2].1));}
        }
    }
    ol::execution_preservation(eq,lib,programs,result,reordered);
}

pub proof fn self_retirement_blocks_begin<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,a:g::Configuration<U,I>,candidate:g::Configuration<U,I>,actor:usize)
    requires s::registered(a.state,actor),
    ensures !g::step(lib,programs,o::retire(a,actor),candidate,actor,r::Rule::Begin),
{ }

/// A real child Begin commutes with retirement of its parent. Parenthood is
/// not an implicit service dependency. The same actor's retirement blocks Begin.
pub proof fn actual_begin_retire()
    ensures {
        let a=crate::recovery_examples::trace()[3];let b=crate::recovery_examples::trace()[4];let z=o::retire(b,0);
        let lib=crate::recovery_examples::library();let programs=crate::recovery_examples::programs();
        &&& g::step(lib,programs,a,b,1,r::Rule::Begin) && g::step(lib,programs,b,z,0,r::Rule::Retire)
        &&& g::step(lib,programs,a,o::retire(a,0),0,r::Rule::Retire) && g::step(lib,programs,o::retire(a,0),z,1,r::Rule::Begin)
        &&& !g::step(lib,programs,o::retire(a,1),o::retire(b,1),1,r::Rule::Begin)
        &&& z.state.control.fibers[0usize].retired && z.state.control.fibers[1usize].phase==Phase::Loading
    },
{
    crate::recovery_examples::actual_execution();crate::recovery_examples::primitive_theory();
    let eq=crate::recovery_examples::equality();let lib=crate::recovery_examples::library();let programs=crate::recovery_examples::programs();
    og::exact_theory(eq,lib);ol::from_empty_safe(eq,lib,programs,crate::recovery_examples::trace(),crate::recovery_examples::labels());
    reveal(crate::recovery_examples::trace);
    let a=crate::recovery_examples::trace()[3];let b=crate::recovery_examples::trace()[4];let z=o::retire(b,0);
    ch::concrete_child_retirement(b.state,0);assert(g::step(lib,programs,b,z,0,r::Rule::Retire));
    diamond(eq,lib,programs,a,b,z,1,r::Rule::Begin,0,r::Rule::Retire);
    self_retirement_blocks_begin(lib,programs,a,o::retire(b,1),1);
}

} // verus!
