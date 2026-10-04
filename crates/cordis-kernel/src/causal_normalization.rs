//! Finite local causal normalization of actual mixed executions.
//!
//! Every move uses a proved orchestration/lifecycle diamond followed by real
//! suffix transport. A decreasing inversion count terminates at a trace with
//! no available adjacent guarded move. The separate rewrite_confluence module
//! proves uniqueness within this rewrite relation. Inapplicable name and inverse
//! read guards can still prevent orchestration from moving across a lifecycle step.
//! All lifecycle rules participate, including strict journal restoration.
#[cfg(verus_keep_ghost)]
use crate::{
    administrative_orchestration as admin, mixed_orchestration as o, mixed_transport as transport,
    mixed_transposition as t, observational_grammar as og, observational_lift as ol,
    unload_orchestration as unload,
};
use crate::{mixed_grammar as g, refinement as r, Port};
use vstd::prelude::*;

verus! {

pub type Label=(usize,r::Rule);
#[verifier::reject_recursive_types(I)]
pub enum ExternalInput<I> {
    Insert {actor:usize,parent:Option<usize>,dependencies:ISet<Port>,provisions:ISet<Port>,root:I},
    Retire {actor:usize},Remove {actor:usize},
}
/// Insertion arguments are read from the actual post-state, including the
/// original continuation type I. Other external rules carry their real name.
pub open spec fn input<U,I>(after:g::Configuration<U,I>,label:Label)->Option<ExternalInput<I>> {
    let actor=label.0;
    match label.1 {
        r::Rule::Insert=>{let f=after.state.control.fibers[actor];Some(ExternalInput::Insert {
            actor,parent:f.parent,dependencies:f.dependencies,provisions:f.provisions,root:after.roots[actor]})},
        r::Rule::Retire=>Some(ExternalInput::Retire {actor}),
        r::Rule::Remove=>Some(ExternalInput::Remove {actor}),
        _=>None,
    }
}
pub open spec fn raw_inputs<U,I>(states:Seq<g::Configuration<U,I>>,labels:Seq<Label>)->Seq<Option<ExternalInput<I>>> {
    Seq::new(labels.len(),|i:int|input(states[i+1],labels[i]))
}
pub open spec fn compact<I>(items:Seq<Option<ExternalInput<I>>>)->Seq<ExternalInput<I>>
    decreases items.len(),
{
    if items.len()==0 {Seq::empty()}
    else {let prefix=compact(items.drop_last());match items.last() {None=>prefix,Some(value)=>prefix.push(value)}}
}
pub open spec fn inputs<U,I>(states:Seq<g::Configuration<U,I>>,labels:Seq<Label>)->Seq<ExternalInput<I>> {
    compact(raw_inputs(states,labels))
}
pub proof fn compact_concat<I>(a:Seq<Option<ExternalInput<I>>>,b:Seq<Option<ExternalInput<I>>>)
    ensures compact(a+b)==compact(a)+compact(b),
    decreases b.len(),
{
    if b.len()>0 {
        compact_concat(a,b.drop_last());assert((a+b).drop_last() =~= a+b.drop_last());
        if b.last().is_some() {assert((compact(a)+compact(b.drop_last())).push(b.last().unwrap()) =~= compact(a)+compact(b.drop_last()).push(b.last().unwrap()));}
    } else {assert(a+b =~= a);}
}
pub proof fn compact_swap<I>(items:Seq<Option<ExternalInput<I>>>,i:int)
    requires 0<=i && i+1<items.len(),items[i].is_none(),
    ensures compact(items.subrange(0,i)+seq![items[i+1],items[i]]+items.subrange(i+2,items.len() as int))==compact(items),
{
    let prefix=items.subrange(0,i);let tail=items.subrange(i+2,items.len() as int);
    let old=seq![items[i],items[i+1]];let new=seq![items[i+1],items[i]];
    compact_concat(prefix,old);compact_concat(prefix+old,tail);compact_concat(prefix,new);compact_concat(prefix+new,tail);
    assert(items =~= prefix+old+tail);reveal_with_fuel(compact,3);assert(compact(old)==compact(new));
}

pub open spec fn external(label:Label)->bool {
    label.1==r::Rule::Insert || label.1==r::Rule::Retire || label.1==r::Rule::Remove
}
pub open spec fn externals(labels:Seq<Label>)->Seq<Label>
    decreases labels.len(),
{
    if labels.len()==0 {Seq::empty()}
    else {let prefix=externals(labels.drop_last());if external(labels.last()) {prefix.push(labels.last())} else {prefix}}
}
pub open spec fn lifecycles(labels:Seq<Label>)->Seq<Label>
    decreases labels.len(),
{
    if labels.len()==0 {Seq::empty()}
    else {let prefix=lifecycles(labels.drop_last());if external(labels.last()) {prefix} else {prefix.push(labels.last())}}
}
/// Number of ordered pairs with a lifecycle label before an external label.
pub open spec fn inversions(labels:Seq<Label>)->nat
    decreases labels.len(),
{
    if labels.len()==0 {0}
    else {inversions(labels.drop_last())+if external(labels.last()) {lifecycles(labels.drop_last()).len()} else {0}}
}

pub proof fn concatenation(a:Seq<Label>,b:Seq<Label>)
    ensures externals(a+b)==externals(a)+externals(b),lifecycles(a+b)==lifecycles(a)+lifecycles(b),
        inversions(a+b)==inversions(a)+inversions(b)+lifecycles(a).len()*externals(b).len(),
    decreases b.len(),
{
    if b.len()>0 {
        let previous=b.drop_last();concatenation(a,previous);
        assert((a+b).drop_last() =~= a+previous);assert((a+b).last()==b.last());
        if external(b.last()) {
            assert((externals(a)+externals(previous)).push(b.last()) =~= externals(a)+externals(previous).push(b.last()));
            assert(lifecycles(a).len()*(externals(previous).len()+1)==lifecycles(a).len()*externals(previous).len()+lifecycles(a).len()) by (nonlinear_arith);
        } else {
            assert((lifecycles(a)+lifecycles(previous)).push(b.last()) =~= lifecycles(a)+lifecycles(previous).push(b.last()));
        }
    } else {assert(a+b =~= a);}
}

pub open spec fn swap_labels(labels:Seq<Label>,i:int)->Seq<Label> {
    labels.subrange(0,i)+seq![labels[i+1],labels[i]]+labels.subrange(i+2,labels.len() as int)
}
pub proof fn swap_order(labels:Seq<Label>,i:int)
    requires 0<=i && i+1<labels.len(),!external(labels[i]),external(labels[i+1]),
    ensures swap_labels(labels,i).len()==labels.len(),
        externals(swap_labels(labels,i))==externals(labels),lifecycles(swap_labels(labels,i))==lifecycles(labels),
        inversions(swap_labels(labels,i))+1==inversions(labels),
{
    reveal_with_fuel(externals,3);reveal_with_fuel(lifecycles,3);reveal_with_fuel(inversions,3);
    let prefix=labels.subrange(0,i);let suffix=labels.subrange(i+2,labels.len() as int);
    let old=seq![labels[i],labels[i+1]];let new=seq![labels[i+1],labels[i]];
    assert(labels =~= prefix+old+suffix);
    concatenation(prefix,old);concatenation(prefix+old,suffix);
    concatenation(prefix,new);concatenation(prefix+new,suffix);
    assert(externals(old) =~= seq![labels[i+1]]);assert(externals(new) =~= seq![labels[i+1]]);
    assert(lifecycles(old) =~= seq![labels[i]]);assert(lifecycles(new) =~= seq![labels[i]]);
    assert(inversions(old)==1);assert(inversions(new)==0);
}

pub open spec fn eligible<U,I>(states:Seq<g::Configuration<U,I>>,labels:Seq<Label>,i:int)->bool {
    &&& 0<=i && i+1<labels.len() && states.len()==labels.len()+1
    &&& external(labels[i+1])
    &&& if g::landing(states[i],states[i+1],labels[i].1) {
        o::crossing_guard(states[i],states[i+2],labels[i].0,labels[i+1].0,labels[i+1].1)
    } else if labels[i].1==r::Rule::Unload {
        unload::crossing_guard(states[i],labels[i].0,labels[i+1].0,labels[i+1].1)
    } else {
        admin::administrative(states[i],states[i+1],labels[i].1)
            && admin::crossing_guard(labels[i].0,labels[i].1,labels[i+1].0,labels[i+1].1)
    }
}
pub open spec fn normal<U,I>(states:Seq<g::Configuration<U,I>>,labels:Seq<Label>)->bool {
    forall|i:int| !eligible(states,labels,i)
}

pub open spec fn swapped_endpoint<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    states:Seq<g::Configuration<U,I>>,labels:Seq<Label>,i:int)->g::Configuration<U,I> {
    let middle=o::intermediate(states[i],states[i+2],labels[i+1].0,labels[i+1].1);
    if g::landing(states[i],states[i+1],labels[i].1) {g::land(lib,programs,middle,labels[i].0,t::landing_phase(labels[i].1))}
    else if labels[i].1==r::Rule::Unload {unload::reverse(states[i],states[i+2],labels[i].0,labels[i+1].0,labels[i+1].1)}
    else {admin::reverse(states[i],states[i+1],states[i+2],labels[i].0,labels[i+1].0,labels[i+1].1)}
}
pub open spec fn swap_states<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    states:Seq<g::Configuration<U,I>>,labels:Seq<Label>,i:int)->Seq<g::Configuration<U,I>> {
    let middle=o::intermediate(states[i],states[i+2],labels[i+1].0,labels[i+1].1);
    let reverse=swapped_endpoint(lib,programs,states,labels,i);
    let moved=transport::transport(states.subrange(i+2,states.len() as int),labels.subrange(i+2,labels.len() as int),reverse);
    states.subrange(0,i+1).push(middle)+moved
}

/// Structural extraction lemma for the states constructed by the diamond.
/// It preserves full insertion payloads, not just actor/rule labels.
pub proof fn payload_swap<U,I>(states:Seq<g::Configuration<U,I>>,labels:Seq<Label>,result:Seq<g::Configuration<U,I>>,i:int)
    requires eligible(states,labels,i),result.len()==states.len(),
        forall|j:int| 0<=j<=i ==> result[j]==states[j],
        result[i+1]==o::intermediate(states[i],states[i+2],labels[i+1].0,labels[i+1].1),
        forall|j:int| i+2<=j<states.len() ==> result[j].state==states[j].state && result[j].roots==states[j].roots,
    ensures inputs(result,swap_labels(labels,i))==inputs(states,labels),
{
    let old=raw_inputs(states,labels);let new=raw_inputs(result,swap_labels(labels,i));
    assert(old[i].is_none());
    let swapped=old.subrange(0,i)+seq![old[i+1],old[i]]+old.subrange(i+2,old.len() as int);
    assert(new =~= swapped) by {
        assert forall|j:int| 0<=j<new.len() implies new[j]==swapped[j] by {
            if j<i {assert(result[j+1]==states[j+1]);assert(swap_labels(labels,i)[j]==labels[j]);}
            else if j==i {
                assert(swap_labels(labels,i)[j]==labels[i+1]);
                assert(input(result[j+1],labels[i+1])==input(states[i+2],labels[i+1]));
            } else if j==i+1 {assert(swap_labels(labels,i)[j]==labels[i]);assert(new[j].is_none());}
            else {assert(i+2<=j);assert(result[j+1].state==states[j+1].state);assert(result[j+1].roots==states[j+1].roots);}
        }
    }
    compact_swap(old,i);
}

/// The only transition premise is the original complete execution. The new
/// middle states and the entire remaining execution are actual constructions.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn adjacent_swap<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    states:Seq<g::Configuration<U,I>>,labels:Seq<Label>,i:int)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,states.first()),g::execution(lib,programs,states,labels),eligible(states,labels,i),
    ensures {
        let result=swap_states(lib,programs,states,labels,i);let reordered=swap_labels(labels,i);
        &&& result.len()==states.len() && result.first()==states.first()
        &&& g::execution(lib,programs,result,reordered)
        &&& transport::related(states.last(),result.last())
        &&& externals(reordered)==externals(labels) && lifecycles(reordered)==lifecycles(labels)
        &&& inputs(result,reordered)==inputs(states,labels)
        &&& inversions(reordered)+1==inversions(labels)
        &&& forall|j:int| 0<=j<result.len() ==> g::well_formed(lib,programs,result[j])
    },
{
    ol::execution_preservation(eq,lib,programs,states,labels);
    let suffix=states.subrange(i+2,states.len() as int);let tail=labels.subrange(i+2,labels.len() as int);
    assert(g::execution(lib,programs,suffix,tail)) by {
        assert forall|j:int| 0<=j<tail.len() implies g::step(lib,programs,suffix[j],suffix[j+1],tail[j].0,tail[j].1) by {
            assert(g::step(lib,programs,states[i+2+j],states[i+3+j],labels[i+2+j].0,labels[i+2+j].1));
        }
    }
    let middle=o::intermediate(states[i],states[i+2],labels[i+1].0,labels[i+1].1);
    let reverse=swapped_endpoint(lib,programs,states,labels,i);
    if g::landing(states[i],states[i+1],labels[i].1) {
        o::orchestration_suffix(eq,lib,programs,states[i],states[i+1],states[i+2],labels[i].0,labels[i].1,labels[i+1].0,labels[i+1].1,suffix,tail);
    } else {
        if labels[i].1==r::Rule::Unload {
            unload::diamond(eq,lib,programs,states[i],states[i+1],states[i+2],labels[i].0,labels[i+1].0,labels[i+1].1);
        } else {
            admin::diamond(eq,lib,programs,states[i],states[i+1],states[i+2],labels[i].0,labels[i].1,labels[i+1].0,labels[i+1].1);
        }
        assert(reverse==states[i+2]);assert(transport::related(suffix.first(),reverse));
        transport::suffix_transport(lib,programs,suffix,tail,reverse);
        transport::observational_safe_suffix(eq,lib,programs,suffix,tail,reverse);
    }
    let moved=transport::transport(suffix,tail,reverse);
    let result=swap_states(lib,programs,states,labels,i);let reordered=swap_labels(labels,i);
    assert(!external(labels[i]));swap_order(labels,i);
    assert(result.len()==states.len());assert(result.first()==states.first());
    assert(result.last()==moved.last());assert(suffix.last()==states.last());
    assert forall|j:int| 0<=j<=i implies result[j]==states[j] by { }
    assert(result[i+1]==middle);
    assert forall|j:int| i+2<=j<states.len() implies result[j].state==states[j].state && result[j].roots==states[j].roots by {
        assert(result[j]==moved[j-i-2]);assert(suffix[j-i-2]==states[j]);
        assert(transport::related(suffix[j-i-2],moved[j-i-2]));
    }
    payload_swap(states,labels,result,i);
    assert(g::execution(lib,programs,result,reordered)) by {
        assert forall|j:int| 0<=j<reordered.len() implies g::step(lib,programs,result[j],result[j+1],reordered[j].0,reordered[j].1) by {
            if j<i {assert(result[j]==states[j]);assert(result[j+1]==states[j+1]);assert(reordered[j]==labels[j]);}
            else if j==i {assert(result[j]==states[i]);assert(result[j+1]==middle);assert(reordered[j]==labels[i+1]);}
            else if j==i+1 {assert(result[j]==middle);assert(result[j+1]==reverse);assert(reordered[j]==labels[i]);}
            else {
                assert(i+2<=j);assert(result[j]==moved[j-i-2]);assert(result[j+1]==moved[j-i-1]);assert(reordered[j]==tail[j-i-2]);
                assert(g::step(lib,programs,moved[j-i-2],moved[j-i-1],tail[j-i-2].0,tail[j-i-2].1));
            }
        }
    }
    ol::execution_preservation(eq,lib,programs,result,reordered);
}

pub proof fn related_transitive<U,I>(a:g::Configuration<U,I>,b:g::Configuration<U,I>,c:g::Configuration<U,I>)
    requires transport::related(a,b),transport::related(b,c),
    ensures transport::related(a,c),
{ }

#[verifier::reject_recursive_types(U)]
pub struct Normalized<U,I> {pub states:Seq<g::Configuration<U,I>>,pub labels:Seq<Label>,pub swaps:nat}

/// Construct a locally normalized execution. Each move consumes one inversion;
/// a blocking guard can leave inversions in the resulting finite trace. No reverse
/// execution, canonical endpoint, or global confluence is an input assumption.
pub proof fn normalize<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    states:Seq<g::Configuration<U,I>>,labels:Seq<Label>)->(result:Normalized<U,I>)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,states.first()),g::execution(lib,programs,states,labels),
    ensures result.states.len()==states.len(),result.states.first()==states.first(),g::execution(lib,programs,result.states,result.labels),
        normal(result.states,result.labels),transport::related(states.last(),result.states.last()),
        externals(result.labels)==externals(labels),lifecycles(result.labels)==lifecycles(labels),
        inputs(result.states,result.labels)==inputs(states,labels),
        inversions(result.labels)+result.swaps==inversions(labels),result.swaps<=inversions(labels),
        (exists|i:int| eligible(states,labels,i)) ==> result.swaps>0,
        normal(states,labels) ==> result.states==states && result.labels==labels && result.swaps==0,
        forall|i:int| 0<=i<result.states.len() ==> g::well_formed(lib,programs,result.states[i]),
    decreases inversions(labels),
{
    if exists|i:int| eligible(states,labels,i) {
        let i=choose|i:int| eligible(states,labels,i);
        adjacent_swap(eq,lib,programs,states,labels,i);
        let reordered=swap_labels(labels,i);let moved=swap_states(lib,programs,states,labels,i);
        let suffix=normalize(eq,lib,programs,moved,reordered);
        related_transitive(states.last(),moved.last(),suffix.states.last());
        Normalized {states:suffix.states,labels:suffix.labels,swaps:suffix.swaps+1}
    } else {
        ol::execution_preservation(eq,lib,programs,states,labels);
        assert(transport::related(states.last(),states.last()));
        Normalized {states,labels,swaps:0}
    }
}

/// A concrete nonempty +5 operation really moves after the other actor's
/// retirement. The construction consumes exactly one inversion.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn operation_moves()->(result:Normalized<int,crate::recovery_examples::Stage>)
    ensures {
        let a=crate::recovery_examples::trace()[7];let b=crate::recovery_examples::trace()[8];
        let lib=crate::recovery_examples::library();let programs=crate::recovery_examples::programs();
        &&& result.swaps==1 && result.labels==seq![(1usize,r::Rule::Retire),(0usize,r::Rule::Finish)]
        &&& result.states.first()==a && transport::related(o::retire(b,1),result.states.last())
        &&& result.states.last().state.tables[0usize][crate::recovery_examples::key(0)]==12
        &&& g::execution(lib,programs,result.states,result.labels) && normal(result.states,result.labels)
    },
{
    crate::recovery_examples::actual_execution();crate::recovery_examples::primitive_theory();o::actual_operation_retire();
    let eq=crate::recovery_examples::equality();let lib=crate::recovery_examples::library();let programs=crate::recovery_examples::programs();
    og::exact_theory(eq,lib);ol::from_empty_safe(eq,lib,programs,crate::recovery_examples::trace(),crate::recovery_examples::labels());
    let a=crate::recovery_examples::trace()[7];let b=crate::recovery_examples::trace()[8];
    let source=seq![a,b,o::retire(b,1)];let labels=seq![(0usize,r::Rule::Finish),(1usize,r::Rule::Retire)];
    assert(g::execution(lib,programs,source,labels)) by {
        assert forall|i:int| 0<=i<labels.len() implies g::step(lib,programs,source[i],source[i+1],labels[i].0,labels[i].1) by {if i==0 {} else {assert(i==1);}}
    }
    assert(g::step(lib,programs,a,o::retire(a,1),1,r::Rule::Retire));
    assert(crate::semantics::registered(a.state,1));assert(eligible(source,labels,0));
    reveal_with_fuel(inversions,3);reveal_with_fuel(lifecycles,3);
    assert(inversions(labels)==1);
    let result=normalize(eq,lib,programs,source,labels);
    assert(result.swaps==1);assert(result.labels.len()==2);
    reveal_with_fuel(externals,3);
    assert(externals(labels) =~= seq![(1usize,r::Rule::Retire)]);assert(lifecycles(labels) =~= seq![(0usize,r::Rule::Finish)]);
    if external(result.labels[1]) {
        assert(result.labels[1]==(1usize,r::Rule::Retire));
        assert(!external(result.labels[0]));assert(inversions(result.labels)==1);
    }
    assert(result.labels =~= seq![(1usize,r::Rule::Retire),(0usize,r::Rule::Finish)]);
    result
}

/// Local normalization can stop with an inversion: insertion of a child of
/// the just-born name cannot be moved before that name exists.
pub proof fn causal_parent_blocks()->(result:Normalized<u64,bool>)
    ensures {
        let a=crate::mixed_examples::trace()[2];let b=crate::mixed_examples::trace()[3];
        let z=t::insert(b,2,Some(1),ISet::empty(),crate::mixed_examples::provided(2),false);
        &&& result.states==seq![a,b,z] && result.labels==seq![(0usize,r::Rule::Iter),(2usize,r::Rule::Insert)]
        &&& result.swaps==0 && inversions(result.labels)==1 && normal(result.states,result.labels)
        &&& g::execution(crate::mixed_examples::library(),crate::mixed_examples::programs(),result.states,result.labels)
    },
{
    crate::mixed_examples::actual_execution();crate::mixed_examples::primitive_theory();t::concrete_parent_rejection();
    let eq=crate::mixed_examples::equality();let lib=crate::mixed_examples::library();let programs=crate::mixed_examples::programs();
    og::exact_theory(eq,lib);ol::from_empty_safe(eq,lib,programs,crate::mixed_examples::trace(),crate::mixed_examples::labels());
    let a=crate::mixed_examples::trace()[2];let b=crate::mixed_examples::trace()[3];
    let z=t::insert(b,2,Some(1),ISet::empty(),crate::mixed_examples::provided(2),false);
    let source=seq![a,b,z];let labels=seq![(0usize,r::Rule::Iter),(2usize,r::Rule::Insert)];
    assert(g::execution(lib,programs,source,labels)) by {
        assert forall|i:int| 0<=i<labels.len() implies g::step(lib,programs,source[i],source[i+1],labels[i].0,labels[i].1) by {if i==0 {} else {assert(i==1);}}
    }
    reveal(crate::mixed_examples::trace);
    assert(normal(source,labels)) by {assert forall|i:int| !eligible(source,labels,i) by {if 0<=i && i+1<labels.len() {assert(i==0);}}}
    reveal_with_fuel(inversions,3);reveal_with_fuel(lifecycles,3);assert(inversions(labels)==1);
    normalize(eq,lib,programs,source,labels)
}

/// A two-event normal ordering is fixed by its preserved class subsequences.
pub proof fn two_event_order(labels:Seq<Label>,e:Label,l:Label)
    requires labels.len()==2,external(e),!external(l),externals(labels)==seq![e],lifecycles(labels)==seq![l],inversions(labels)==0,
    ensures labels==seq![e,l],
{
    assert(labels =~= seq![labels[0],labels[1]]);
    assert(labels.drop_last() =~= seq![labels[0]]);
    assert(labels.drop_last().drop_last() =~= Seq::<Label>::empty());
    reveal_with_fuel(externals,3);reveal_with_fuel(lifecycles,3);reveal_with_fuel(inversions,3);
    if external(labels[1]) {assert(!external(labels[0]));assert(inversions(labels)==1);}
    assert(!external(labels[1]));assert(external(labels[0]));assert(labels[0]==e);
    assert(lifecycles(labels.drop_last()) =~= Seq::<Label>::empty());
    assert(lifecycles(labels)==lifecycles(labels.drop_last()).push(labels[1]));
    assert(lifecycles(labels) =~= seq![labels[1]]);
    assert(seq![l][0]==l);assert(labels[1]==l);
}

/// Normalization crosses the complete nonempty restoration, including its
/// actual table inverses and captured child retirement, with another Retire.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn unload_moves()->(result:Normalized<int,crate::recovery_examples::Stage>)
    ensures {
        let a=crate::recovery_examples::trace()[10];let b=crate::recovery_examples::trace()[11];
        let lib=crate::recovery_examples::library();let programs=crate::recovery_examples::programs();
        &&& result.swaps==1 && result.labels==seq![(1usize,r::Rule::Retire),(0usize,r::Rule::Unload)]
        &&& result.states.first()==a && transport::related(o::retire(b,1),result.states.last())
        &&& result.states.last().state.tables[0usize].is_empty()
        &&& result.states.last().state.tables[1usize][crate::recovery_examples::key(1)]==39
        &&& g::execution(lib,programs,result.states,result.labels) && normal(result.states,result.labels)
    },
{
    crate::recovery_examples::actual_execution();crate::recovery_examples::primitive_theory();unload::actual_operation_retire();
    let eq=crate::recovery_examples::equality();let lib=crate::recovery_examples::library();let programs=crate::recovery_examples::programs();
    og::exact_theory(eq,lib);ol::from_empty_safe(eq,lib,programs,crate::recovery_examples::trace(),crate::recovery_examples::labels());
    let a=crate::recovery_examples::trace()[10];let b=crate::recovery_examples::trace()[11];
    let source=seq![a,b,o::retire(b,1)];let labels=seq![(0usize,r::Rule::Unload),(1usize,r::Rule::Retire)];
    assert(g::execution(lib,programs,source,labels)) by {
        assert forall|i:int| 0<=i<labels.len() implies g::step(lib,programs,source[i],source[i+1],labels[i].0,labels[i].1) by {if i==0 {} else {assert(i==1);}}
    }
    assert(eligible(source,labels,0));reveal_with_fuel(inversions,3);reveal_with_fuel(lifecycles,3);
    assert(inversions(labels)==1);let result=normalize(eq,lib,programs,source,labels);
    assert(result.swaps==1);assert(result.labels.len()==2);reveal_with_fuel(externals,3);
    assert(externals(labels) =~= seq![(1usize,r::Rule::Retire)]);assert(lifecycles(labels) =~= seq![(0usize,r::Rule::Unload)]);
    two_event_order(result.labels,(1usize,r::Rule::Retire),(0usize,r::Rule::Unload));
    result
}

/// A legal Unload/Remove inversion remains when the original owner journal
/// still captures that child. Removing it early would make restoration fail.
pub proof fn captured_child_blocks()->(result:Normalized<u64,bool>)
    ensures {
        let a=unload::retained_source();let b=g::unload(a,0);let z=o::remove(b,1);
        &&& result.states==seq![a,b,z] && result.labels==seq![(0usize,r::Rule::Unload),(1usize,r::Rule::Remove)]
        &&& result.swaps==0 && inversions(result.labels)==1 && normal(result.states,result.labels)
        &&& g::execution(crate::mixed_examples::library(),crate::mixed_examples::programs(),result.states,result.labels)
    },
{
    unload::retained_remove_blocks();crate::mixed_examples::primitive_theory();
    let eq=crate::mixed_examples::equality();let lib=crate::mixed_examples::library();let programs=crate::mixed_examples::programs();
    og::exact_theory(eq,lib);
    let a=unload::retained_source();let b=g::unload(a,0);let z=o::remove(b,1);
    let source=seq![a,b,z];let labels=seq![(0usize,r::Rule::Unload),(1usize,r::Rule::Remove)];
    assert(g::execution(lib,programs,source,labels)) by {
        assert forall|i:int| 0<=i<labels.len() implies g::step(lib,programs,source[i],source[i+1],labels[i].0,labels[i].1) by {if i==0 {} else {assert(i==1);}}
    }
    assert(normal(source,labels)) by {assert forall|i:int| !eligible(source,labels,i) by {if 0<=i && i+1<labels.len() {assert(i==0);}}}
    reveal_with_fuel(inversions,3);reveal_with_fuel(lifecycles,3);assert(inversions(labels)==1);
    normalize(eq,lib,programs,source,labels)
}

} // verus!
