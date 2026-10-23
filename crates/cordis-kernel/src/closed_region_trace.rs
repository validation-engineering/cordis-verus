//! Legal source-subsequence construction and its observational closing cut.
#[cfg(verus_keep_ghost)]
use super::*;
use vstd::prelude::*;
verus! {
pub open spec fn kept(labels:Seq<(usize,r::Rule)>,region:Region)->Seq<(usize,r::Rule)>
    decreases labels.len(),
{if labels.len()==0 {Seq::empty()} else {
    let before=kept(labels.drop_last(),region);let label=labels.last();
    if region.keep(label.0,label.1) {before.push(label)} else {before}
}}
pub proof fn kept_concat(a:Seq<(usize,r::Rule)>,b:Seq<(usize,r::Rule)>,region:Region)
    ensures kept(a+b,region)==kept(a,region)+kept(b,region),decreases b.len(),
{
    if b.len()==0 {assert(a+b =~= a);assert(kept(a,region)+kept(b,region) =~= kept(a,region));}
    else {kept_concat(a,b.drop_last(),region);assert((a+b).drop_last() =~= a+b.drop_last());
        if region.keep(b.last().0,b.last().1) {assert((kept(a,region)+kept(b.drop_last(),region)).push(b.last()) =~= kept(a,region)+kept(b.drop_last(),region).push(b.last()));}}
}
pub open spec fn delete<U,I>(source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,region:Region,rho:spec_fn(nat)->nat)->Seq<g::Configuration<U,I>>
    decreases labels.len(),
{if labels.len()==0 {seq![configuration(source.first(),region,rho)]} else {
    let before=delete(source.drop_last(),labels.drop_last(),region,rho);let label=labels.last();
    if region.keep(label.0,label.1) {before.push(configuration(source.last(),region,rho))} else {before}
}}
/// Guards examine only the original run. Retained-step legality and successful
/// restoration in the constructed run are deliberately absent from this list.
pub open spec fn admissible<U,I>(source:Seq<g::Configuration<U,I>>,region:Region)->bool {
    &&& region.wf()
    &&& forall|i:int|0<=i<source.len() ==> closed(source[i].state,region)
    &&& local_history(source.last().history,region)
}
pub proof fn histories<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires g::execution(lib,programs,source,labels),
    ensures forall|i:int|0<=i<source.len() ==> prefix(source[i].history,source.last().history),
    decreases labels.len(),
{
    if labels.len()>0 {
        let before=source.drop_last();let steps=labels.drop_last();histories(lib,programs,before,steps);
        let a=before.last();let z=source.last();let label=labels.last();
        assert(g::step(lib,programs,a,z,label.0,label.1));assert(prefix(a.history,z.history));
        assert forall|i:int|0<=i<source.len() implies prefix(source[i].history,z.history) by {
            if i<before.len() {assert(prefix(before[i].history,a.history));}
        }
    }
}
#[verifier::spinoff_prover]
pub proof fn construct<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,region:Region,rho:spec_fn(nat)->nat)
    requires g::execution(lib,programs,source,labels),admissible(source,region),
        forall|i:int|0<=i<source.len() ==> g::well_formed(lib,programs,source[i]) && execution::numbered(source[i],region,rho),
    ensures g::execution(lib,programs,delete(source,labels,region,rho),kept(labels,region)),
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
        execution::step(lib,programs,a,z,label.0,label.1,region,rho);
        let old=delete(before,steps,region,rho);let out=delete(source,labels,region,rho);let target_labels=kept(labels,region);
        if region.keep(label.0,label.1) {
            assert(out==old.push(configuration(z,region,rho)));assert(target_labels==kept(steps,region).push(label));
            assert forall|i:int|0<=i<target_labels.len() implies g::step(lib,programs,out[i],out[i+1],target_labels[i].0,target_labels[i].1) by {
                if i<kept(steps,region).len() {assert(g::step(lib,programs,old[i],old[i+1],kept(steps,region)[i].0,kept(steps,region)[i].1));}
                else {assert(i==kept(steps,region).len());assert(out[i]==configuration(a,region,rho));}
            }
        }
    }
}
pub proof fn empty<U,I>(region:Region,rho:spec_fn(nat)->nat)
    ensures configuration(g::empty::<U,I>(),region,rho)==g::empty::<U,I>(),
{
    let a=configuration(g::empty::<U,I>(),region,rho);let e=g::empty::<U,I>();
    assert(a.state.control.fibers =~= e.state.control.fibers);assert(a.state.tables =~= e.state.tables);
    assert(a.state.effects =~= e.state.effects);assert(a.state.iterators =~= e.state.iterators);assert(a.state.accumulators =~= e.state.accumulators);
    assert(a.roots =~= e.roots);assert(a.current =~= e.current);
}
pub open spec fn target<U,I>(source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,region:Region)->Seq<g::Configuration<U,I>> {
    delete(source,labels,region,|t:nat|index(source.last().history,region,t))
}
/// No target trace is supplied: source histories fix the inverse renaming and
/// every target state. This handles arbitrary finite interleavings inside the
/// declared closed region, including Child/consumer lifecycles and old Unloads.
pub proof fn from_source<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,source:Seq<g::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,region:Region)
    requires d::primitive_theory(eq,lib),g::execution(lib,programs,source,labels),source.first()==g::empty::<U,I>(),admissible(source,region),
    ensures g::execution(lib,programs,target(source,labels,region),kept(labels,region)),
        target(source,labels,region).first()==g::empty::<U,I>(),
        target(source,labels,region).last()==configuration(source.last(),region,|t:nat|index(source.last().history,region,t)),
        g::well_formed(lib,programs,target(source,labels,region).last()),
        crate::mixed_recovery::provided_journals(source.last()),g::well_formed(lib,programs,source.last()),
{
    crate::provision_coverage::mixed_from_empty(eq,lib,programs,source,labels);
    g::from_empty_safe(eq,lib,programs,source,labels);histories(lib,programs,source,labels);
    let rho=|t:nat|index(source.last().history,region,t);
    assert forall|i:int|0<=i<source.len() implies execution::numbered(source[i],region,rho) by {
        assert forall|t:nat|t<=source[i].history.len() implies rho(t)==index(source[i].history,region,t) by {
            index_prefix(source[i].history,source.last().history,region,t);
        }
    }
    construct(lib,programs,source,labels,region,rho);empty::<U,I>(region,rho);
    g::from_empty_safe(eq,lib,programs,target(source,labels,region),kept(labels,region));
}
pub open spec fn settled<U,I>(a:g::Configuration<U,I>,region:Region)->bool {
    forall|n:usize|s::registered(a.state,n) && region.episodes.contains(n) ==> a.state.control.fibers[n].phase==Phase::Inactive
        && (region.born.contains(n) ==> a.state.control.fibers[n].retired)
}
pub proof fn closing_observation<U,I>(a:g::Configuration<U,I>,region:Region,rho:spec_fn(nat)->nat)
    requires region.wf(),inv::well_formed(a.state),crate::mixed_recovery::provided_journals(a),settled(a,region),
    ensures s::same_tables(a.state,state(a.state,region,rho)),p::project(a.state,ISet::full())==p::project(state(a.state,region,rho),ISet::full()),
{
    assert forall|n:usize|s::registered(a.state,n) && region.episodes.contains(n) implies a.state.tables[n].is_empty() by {
        crate::isolated_deletion::inactive_table_empty(a,n);
    }
    assert forall|n:usize,key:Port|s::lookup(a.state,n,key)==s::lookup(state(a.state,region,rho),n,key) by { }
    assert(p::bindings_equal(a.state,state(a.state,region,rho))) by {
        assert forall|key:Port,n:usize|p::owns(a.state,key,n)==p::owns(state(a.state,region,rho),key,n)
            && (p::owns(a.state,key,n) ==> a.state.tables[n][key]==state(a.state,region,rho).tables[n][key]) by { }
    }
    p::unique_owner(a.state);
    assert(p::unambiguous(state(a.state,region,rho))) by {
        assert forall|key:Port,n:usize,m:usize|p::owns(state(a.state,region,rho),key,n) && p::owns(state(a.state,region,rho),key,m) implies n==m by { }
    }
    p::projection_equal(a.state,state(a.state,region,rho),ISet::full());
}
}
