//! Construct a legal Fresh execution using each original retained choice.
#[cfg(verus_keep_ghost)]
use super::trace::admissible;
#[cfg(verus_keep_ghost)]
use super::*;
#[cfg(verus_keep_ghost)]
use crate::fresh_semantics as fs;
use vstd::prelude::*;
verus! {
pub open spec fn kept(labels:Seq<fs::Label>,region:Region)->Seq<fs::Label>
    decreases labels.len(),
{if labels.len()==0 {Seq::empty()} else {
    let before=kept(labels.drop_last(),region);let label=labels.last();
    if region.keep(label.0,label.1) {before.push(label)} else {before}
}}
pub open spec fn delete<U,I>(source:Seq<g::Configuration<U,I>>,labels:Seq<fs::Label>,region:Region,rho:spec_fn(nat)->nat)->Seq<g::Configuration<U,I>>
    decreases labels.len(),
{if labels.len()==0 {seq![configuration(source.first(),region,rho)]} else {
    let before=delete(source.drop_last(),labels.drop_last(),region,rho);let label=labels.last();
    if region.keep(label.0,label.1) {before.push(configuration(source.last(),region,rho))} else {before}
}}
pub proof fn histories<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<fs::Label>)
    requires fs::execution(lib,programs,source,labels),
    ensures forall|i:int|0<=i<source.len() ==> prefix(source[i].history,source.last().history),
    decreases labels.len(),
{
    if labels.len()>0 {
        let before=source.drop_last();let steps=labels.drop_last();histories(lib,programs,before,steps);
        let a=before.last();let z=source.last();let label=labels.last();
        assert(fs::step(lib,programs,a,z,label.0,label.1,label.2));assert(prefix(a.history,z.history));
        assert forall|i:int|0<=i<source.len() implies prefix(source[i].history,z.history) by {
            if i<before.len() {assert(prefix(before[i].history,a.history));}
        }
    }
}
#[verifier::spinoff_prover]
pub proof fn construct<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<fs::Label>,region:Region,rho:spec_fn(nat)->nat)
    requires fs::execution(lib,programs,source,labels),admissible(source,region),
        forall|i:int|0<=i<source.len() ==> fs::well_formed(lib,programs,source[i]) && execution::numbered(source[i],region,rho),
    ensures fs::execution(lib,programs,delete(source,labels,region,rho),kept(labels,region)),
        delete(source,labels,region,rho).first()==configuration(source.first(),region,rho),
        delete(source,labels,region,rho).last()==configuration(source.last(),region,rho),
    decreases labels.len(),
{
    histories(lib,programs,source,labels);
    if labels.len()>0 {
        let before=source.drop_last();let steps=labels.drop_last();let label=labels.last();let a=before.last();let z=source.last();
        assert(admissible(before,region)) by {
            assert forall|i:int|0<=i<a.history.len() implies local(a.history[i].landed.receipt,region) by {assert(a.history[i]==z.history[i]);}
        }
        construct(lib,programs,before,steps,region,rho);
        fresh::step(lib,programs,a,z,label.0,label.1,label.2,region,rho);
        let old=delete(before,steps,region,rho);let out=delete(source,labels,region,rho);let target_labels=kept(labels,region);
        if region.keep(label.0,label.1) {
            assert(out==old.push(configuration(z,region,rho)));assert(target_labels==kept(steps,region).push(label));
            assert forall|i:int|0<=i<target_labels.len() implies fs::step(lib,programs,out[i],out[i+1],target_labels[i].0,target_labels[i].1,target_labels[i].2) by {
                if i<kept(steps,region).len() {assert(fs::step(lib,programs,old[i],old[i+1],kept(steps,region)[i].0,kept(steps,region)[i].1,kept(steps,region)[i].2));}
                else {assert(i==kept(steps,region).len());assert(out[i]==configuration(a,region,rho));}
            }
        }
    }
}
pub open spec fn target<U,I>(source:Seq<g::Configuration<U,I>>,labels:Seq<fs::Label>,region:Region)->Seq<g::Configuration<U,I>> {
    delete(source,labels,region,|t:nat|index(source.last().history,region,t))
}
/// No target trace is supplied: source histories fix the inverse renaming and
/// every target state. This handles arbitrary finite interleavings inside the
/// declared closed region, including Child/consumer lifecycles and old Unloads.
pub proof fn from_source<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<fs::Label>,region:Region)
    requires crate::observational_grammar::primitive_theory(eq,lib),fs::execution(lib,programs,source,labels),source.first()==g::empty::<U,I>(),admissible(source,region),
    ensures fs::execution(lib,programs,target(source,labels,region),kept(labels,region)),
        target(source,labels,region).first()==g::empty::<U,I>(),
        target(source,labels,region).last()==configuration(source.last(),region,|t:nat|index(source.last().history,region,t)),
        fs::well_formed(lib,programs,target(source,labels,region).last()),
        crate::mixed_recovery::provided_journals(source.last()),fs::well_formed(lib,programs,source.last()),
{
    crate::provision_coverage::fresh_from_empty(eq,lib,programs,source,labels);
    fs::from_empty_safe(eq,lib,programs,source,labels);histories(lib,programs,source,labels);
    let rho=|t:nat|index(source.last().history,region,t);
    assert forall|i:int|0<=i<source.len() implies execution::numbered(source[i],region,rho) by {
        assert forall|t:nat|t<=source[i].history.len() implies rho(t)==index(source[i].history,region,t) by {
            index_prefix(source[i].history,source.last().history,region,t);
        }
    }
    construct(lib,programs,source,labels,region,rho);trace::empty::<U,I>(region,rho);
    fs::from_empty_safe(eq,lib,programs,target(source,labels,region),kept(labels,region));
}
}
