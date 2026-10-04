//! Same-label transport of actual mixed executions after a local diamond.
//!
//! The control/value state and live continuations agree exactly. Historical
//! inputs may differ; corresponding captured receipts give the same strict
//! inverse interpreter. Only already legal finite suffixes are transported.
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_grammar as d, mixed_grammar as g, mixed_transposition as t,
    observational_grammar as og, observational_lift as ol, refinement as r, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn related<U,I>(left:g::Configuration<U,I>,right:g::Configuration<U,I>)->bool {
    left.state==right.state && left.roots==right.roots && left.current==right.current
        && t::same_receipts(left,right)
}

pub proof fn symmetric<U,I>(left:g::Configuration<U,I>,right:g::Configuration<U,I>)
    requires related(left,right),
    ensures related(right,left),
{ }

/// The successor copies the actual observed control/value changes. A landing
/// appends the same freshly computed entry to the other authentic history;
/// the old entries, including their different recorded inputs, are preserved.
pub open spec fn successor<U,I>(left:g::Configuration<U,I>,next:g::Configuration<U,I>,right:g::Configuration<U,I>,rule:r::Rule)->g::Configuration<U,I> {
    g::Configuration {state:next.state,roots:next.roots,current:next.current,
        history:if g::landing(left,next,rule) {right.history.push(next.history.last())} else {right.history}}
}

pub proof fn step_transport<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    left:g::Configuration<U,I>,next:g::Configuration<U,I>,right:g::Configuration<U,I>,actor:usize,rule:r::Rule)
    requires related(left,right),g::step(lib,programs,left,next,actor,rule),
    ensures {
        let result=successor(left,next,right,rule);
        &&& g::step(lib,programs,right,result,actor,rule) && related(next,result)
        &&& g::landing(left,next,rule)==g::landing(right,result,rule)
        &&& (g::landing(left,next,rule) ==> {
            &&& next.history==left.history.push(g::entry(lib,programs,left,actor))
            &&& result.history==right.history.push(g::entry(lib,programs,right,actor))
            &&& result.history.last()==next.history.last()
            &&& result.history.last().input==right.state
        })
        &&& (!g::landing(left,next,rule) ==> next.history==left.history && result.history==right.history)
    },
{
    let result=successor(left,next,right,rule);
    t::corresponding_restore(left,right,left.state.accumulators[actor],left.state,actor);
    assert forall|token:nat| #[trigger] g::kind(left.history)(token)==g::kind(right.history)(token) by { }
    assert(g::entry(lib,programs,left,actor)==g::entry(lib,programs,right,actor));
    if g::landing(left,next,rule) {
        assert(next.history==left.history.push(g::entry(lib,programs,left,actor)));
        assert(result.history==right.history.push(g::entry(lib,programs,right,actor)));
        assert(t::same_receipts(next,result)) by {
            assert forall|i:int| 0<=i<next.history.len() implies {
                &&& next.history[i].iterator==result.history[i].iterator
                &&& next.history[i].landed.receipt==result.history[i].landed.receipt
                &&& next.history[i].landed.next==result.history[i].landed.next
                &&& next.history[i].landed.spawn==result.history[i].landed.spawn
            } by {
                if i<left.history.len() {assert(next.history[i]==left.history[i]);assert(result.history[i]==right.history[i]);}
                else {assert(i==left.history.len());assert(next.history[i]==result.history[i]);}
            }
        }
    } else {assert(next.history==left.history);}
    match rule {
        r::Rule::Remove=>{
            assert(crate::child_history::remove_unreferenced(g::kind(right.history),right.state,actor));
        },
        r::Rule::Unload=>{
            assert(g::restore(left.history,left.state.accumulators[actor],left.state,actor)
                ==g::restore(right.history,right.state.accumulators[actor],right.state,actor));
            assert(result==g::unload(right,actor));
        },
        _=>{},
    }
    assert(g::step(lib,programs,right,result,actor,rule));
}

/// Symmetry of the relation and the constructive forward lemma establish both
/// directions of same-label simulation. No successor on the other side is a
/// premise and inverse failure is preserved exactly.
pub proof fn step_bisimulation<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    left:g::Configuration<U,I>,right:g::Configuration<U,I>,actor:usize,rule:r::Rule)
    requires related(left,right),
    ensures
        (exists|next:g::Configuration<U,I>| g::step(lib,programs,left,next,actor,rule))
            ==(exists|next:g::Configuration<U,I>| g::step(lib,programs,right,next,actor,rule)),
{
    if exists|next:g::Configuration<U,I>| g::step(lib,programs,left,next,actor,rule) {
        let next=choose|next:g::Configuration<U,I>| g::step(lib,programs,left,next,actor,rule);
        step_transport(lib,programs,left,next,right,actor,rule);
        assert(g::step(lib,programs,right,successor(left,next,right,rule),actor,rule));
    }
    if exists|next:g::Configuration<U,I>| g::step(lib,programs,right,next,actor,rule) {
        symmetric(left,right);
        let next=choose|next:g::Configuration<U,I>| g::step(lib,programs,right,next,actor,rule);
        step_transport(lib,programs,right,next,left,actor,rule);
        assert(g::step(lib,programs,left,successor(right,next,left,rule),actor,rule));
    }
}

pub open spec fn transport<U,I>(source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,start:g::Configuration<U,I>)->Seq<g::Configuration<U,I>>
    decreases labels.len(),
{
    if labels.len()==0 {seq![start]}
    else {
        let prefix=transport(source.drop_last(),labels.drop_last(),start);
        prefix.push(successor(source[source.len()-2],source.last(),prefix.last(),labels.last().1))
    }
}

pub proof fn suffix_transport<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,start:g::Configuration<U,I>)
    requires g::execution(lib,programs,source,labels),related(source.first(),start),
    ensures {
        let result=transport(source,labels,start);
        &&& result.len()==source.len() && result.first()==start
        &&& g::execution(lib,programs,result,labels)
        &&& forall|i:int| 0<=i<source.len() ==> related(source[i],result[i])
    },
    decreases labels.len(),
{
    if labels.len()>0 {
        let prefix=source.drop_last();let previous=labels.drop_last();
        assert(prefix.len()==previous.len()+1);
        assert(g::execution(lib,programs,prefix,previous)) by {
            assert forall|i:int| 0<=i<previous.len() implies g::step(lib,programs,prefix[i],prefix[i+1],previous[i].0,previous[i].1) by { }
        }
        suffix_transport(lib,programs,prefix,previous,start);
        let moved=transport(prefix,previous,start);
        step_transport(lib,programs,prefix.last(),source.last(),moved.last(),labels.last().0,labels.last().1);
        let result=transport(source,labels,start);
        let tail=successor(prefix.last(),source.last(),moved.last(),labels.last().1);
        assert(prefix.last()==source[source.len()-2]);
        assert(result==moved.push(tail));
        assert(result.len()==labels.len()+1);
        assert(g::step(lib,programs,moved.last(),tail,labels.last().0,labels.last().1));
        assert(g::execution(lib,programs,result,labels)) by {
            assert forall|i:int| 0<=i<labels.len() implies g::step(lib,programs,result[i],result[i+1],labels[i].0,labels[i].1) by {
                if i<previous.len() {
                    assert(result[i]==moved[i]);assert(result[i+1]==moved[i+1]);
                    assert(g::step(lib,programs,moved[i],moved[i+1],previous[i].0,previous[i].1));
                } else {
                    assert(i==labels.len()-1);assert(result[i]==moved.last());assert(result[i+1]==tail);
                    assert(labels[i]==labels.last());
                }
            }
        }
        assert forall|i:int| 0<=i<source.len() implies related(source[i],result[i]) by {
            if i<prefix.len() {assert(result[i]==moved[i]);assert(source[i]==prefix[i]);}
            else {assert(i==source.len()-1);}
        }
    } else {assert(source.len()==1);}
}

/// This version additionally derives authentic history, typing and retention
/// for the transported suffix from its own initial configuration.
pub proof fn observational_safe_suffix<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,start:g::Configuration<U,I>)
    requires og::primitive_theory(eq,lib),g::execution(lib,programs,source,labels),related(source.first(),start),g::well_formed(lib,programs,start),
    ensures g::execution(lib,programs,transport(source,labels,start),labels),
        forall|i:int| 0<=i<source.len() ==> related(source[i],transport(source,labels,start)[i])
            && g::well_formed(lib,programs,transport(source,labels,start)[i]),
{
    suffix_transport(lib,programs,source,labels,start);
    ol::execution_preservation(eq,lib,programs,transport(source,labels,start),labels);
}

/// Exact-recovery specialization.
pub proof fn safe_suffix<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,start:g::Configuration<U,I>)
    requires d::primitive_theory(eq,lib),g::execution(lib,programs,source,labels),related(source.first(),start),g::well_formed(lib,programs,start),
    ensures g::execution(lib,programs,transport(source,labels,start),labels),
        forall|i:int| 0<=i<source.len() ==> related(source[i],transport(source,labels,start)[i])
            && g::well_formed(lib,programs,transport(source,labels,start)[i]),
{
    og::exact_theory(eq,lib);
    observational_safe_suffix(eq,lib,programs,source,labels,start);
    assert forall|i:int| 0<=i<source.len() implies related(source[i],transport(source,labels,start)[i])
        && g::well_formed(lib,programs,transport(source,labels,start)[i]) by {
        assert(related(source[i],transport(source,labels,start)[i]));
    }
}

/// The corrected child/Insert diamond supports every already legal finite
/// continuation of its endpoint, even though the old forward inputs differ.
pub proof fn child_diamond_suffix<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,b:g::Configuration<U,I>,z:g::Configuration<U,I>,actor:usize,rule:r::Rule,
    child:usize,child_dependencies:ISet<Port>,child_provisions:ISet<Port>,child_root:I,next:Option<I>,id:usize,
    source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires d::primitive_theory(eq,lib),g::well_formed(lib,programs,a),g::step(lib,programs,a,b,actor,rule),g::landing(a,b,rule),
        programs(actor)(a.current[actor].unwrap())==(g::Node::Child {child,dependencies:child_dependencies,provisions:child_provisions,root:child_root,next}),
        g::step(lib,programs,b,z,id,r::Rule::Insert),z.state.control.fibers[id].parent!=Some(child),
        g::execution(lib,programs,source,labels),source.first()==z,
    ensures {
        let f=z.state.control.fibers[id];let middle=t::insert(a,id,f.parent,f.dependencies,f.provisions,z.roots[id]);
        let reverse=g::land(lib,programs,middle,actor,t::landing_phase(rule));
        let moved=transport(source,labels,reverse);
        &&& g::step(lib,programs,a,middle,id,r::Rule::Insert) && g::step(lib,programs,middle,reverse,actor,rule)
        &&& related(z,reverse) && moved.first()==reverse && moved.len()==source.len()
        &&& g::execution(lib,programs,moved,labels)
        &&& forall|i:int| 0<=i<source.len() ==> related(source[i],moved[i]) && g::well_formed(lib,programs,moved[i])
    },
{
    t::observed_pair(eq,lib,programs,a,b,z,actor,rule,child,child_dependencies,child_provisions,child_root,next,id);
    let f=z.state.control.fibers[id];let middle=t::insert(a,id,f.parent,f.dependencies,f.provisions,z.roots[id]);
    let reverse=g::land(lib,programs,middle,actor,t::landing_phase(rule));
    suffix_transport(lib,programs,source,labels,reverse);
    safe_suffix(eq,lib,programs,source,labels,reverse);
}

} // verus!
