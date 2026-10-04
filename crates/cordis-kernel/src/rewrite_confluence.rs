//! Confluence of the guarded adjacent orchestration rewrite itself.
//!
//! Equivalence compares every control/value state, root, current continuation
//! and actual receipt. Historical forward inputs are intentionally not equated.
//! This concerns descendants of one given trace, not arbitrary paper executions.
#[cfg(verus_keep_ghost)]
use crate::{
    administrative_orchestration as admin, causal_normalization as c, mixed_grammar as g,
    mixed_orchestration as o, mixed_transport as tr, observational_grammar as og,
    observational_lift as ol, refinement as r, unload_orchestration as unload, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn related<U,I>(a:Seq<g::Configuration<U,I>>,z:Seq<g::Configuration<U,I>>)->bool {
    a.len()==z.len() && forall|i:int| 0<=i<a.len() ==> tr::related(a[i],z[i])
}
pub proof fn reflexive<U,I>(a:Seq<g::Configuration<U,I>>)
    ensures related(a,a),
{ }
pub proof fn symmetric<U,I>(a:Seq<g::Configuration<U,I>>,z:Seq<g::Configuration<U,I>>)
    requires related(a,z),ensures related(z,a),
{
    assert forall|i:int| 0<=i<z.len() implies tr::related(z[i],a[i]) by {tr::symmetric(a[i],z[i]);}
}
pub proof fn transitive<U,I>(a:Seq<g::Configuration<U,I>>,b:Seq<g::Configuration<U,I>>,z:Seq<g::Configuration<U,I>>)
    requires related(a,b),related(b,z),ensures related(a,z),
{
    assert forall|i:int| 0<=i<a.len() implies tr::related(a[i],z[i]) by {c::related_transitive(a[i],b[i],z[i]);}
}

/// On real transitions landing is observable from history length, including
/// the two distinct Divert rules. Raw equality of old entries is irrelevant.
pub proof fn landing_shape<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,b:g::Configuration<U,I>,actor:usize,rule:r::Rule)
    requires g::step(lib,programs,a,b,actor,rule),
    ensures g::landing(a,b,rule)==(rule==r::Rule::Iter || rule==r::Rule::Finish || rule==r::Rule::Divert && b.history.len()>a.history.len()),
{
    if rule==r::Rule::Divert && g::landing(a,b,rule) {assert(b.history.len()==a.history.len()+1);}
}

pub proof fn pair_related<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:g::Configuration<U,I>,b:g::Configuration<U,I>,z:g::Configuration<U,I>,
    x:g::Configuration<U,I>,y:g::Configuration<U,I>,w:g::Configuration<U,I>,actor:usize,rule:r::Rule,id:usize,external:r::Rule)
    requires tr::related(a,x),tr::related(b,y),tr::related(z,w),g::step(lib,programs,a,b,actor,rule),g::step(lib,programs,x,y,actor,rule),
    ensures g::landing(a,b,rule)==g::landing(x,y,rule),admin::administrative(a,b,rule)==admin::administrative(x,y,rule),
        o::crossing_guard(a,z,actor,id,external)==o::crossing_guard(x,w,actor,id,external),
        unload::crossing_guard(a,actor,id,external)==unload::crossing_guard(x,actor,id,external),
{
    landing_shape(lib,programs,a,b,actor,rule);landing_shape(lib,programs,x,y,actor,rule);
    assert forall|token:nat| #[trigger] g::kind(a.history)(token)==g::kind(x.history)(token) by {
        if token<a.history.len() {assert(a.history[token as int].landed.receipt==x.history[token as int].landed.receipt);}
    }
    assert forall|tokens:Seq<nat>| unload::no_child(a.history,tokens,id)==unload::no_child(x.history,tokens,id) by {
        if unload::no_child(a.history,tokens,id) {
            assert forall|token:nat| tokens.contains(token) implies #[trigger] g::kind(x.history)(token)!=Some(id) by {
                assert(g::kind(a.history)(token)!=Some(id));
            }
        }
        if unload::no_child(x.history,tokens,id) {
            assert forall|token:nat| tokens.contains(token) implies #[trigger] g::kind(a.history)(token)!=Some(id) by {
                assert(g::kind(x.history)(token)!=Some(id));
            }
        }
    }
}

/// Guard correspondence only needs the three configurations read by the pair.
/// Both traces are actual executions; reverse legality is not an assumption.
pub proof fn eligible_at<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:Seq<g::Configuration<U,I>>,al:Seq<c::Label>,z:Seq<g::Configuration<U,I>>,zl:Seq<c::Label>,i:int)
    requires g::execution(lib,programs,a,al),g::execution(lib,programs,z,zl),a.len()==z.len(),0<=i && i+1<al.len(),
        al[i]==zl[i],al[i+1]==zl[i+1],tr::related(a[i],z[i]),tr::related(a[i+1],z[i+1]),tr::related(a[i+2],z[i+2]),
    ensures c::eligible(a,al,i)==c::eligible(z,zl,i),
{
    pair_related(lib,programs,a[i],a[i+1],a[i+2],z[i],z[i+1],z[i+2],al[i].0,al[i].1,al[i+1].0,al[i+1].1);
}
pub proof fn eligibility<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:Seq<g::Configuration<U,I>>,z:Seq<g::Configuration<U,I>>,labels:Seq<c::Label>)
    requires related(a,z),g::execution(lib,programs,a,labels),g::execution(lib,programs,z,labels),
    ensures (forall|i:int| c::eligible(a,labels,i)==c::eligible(z,labels,i)),c::normal(a,labels)==c::normal(z,labels),
{
    assert forall|i:int| c::eligible(a,labels,i)==c::eligible(z,labels,i) by {
        if 0<=i && i+1<labels.len() {eligible_at(lib,programs,a,labels,z,labels,i);}
    }
}
pub proof fn payloads<U,I>(a:Seq<g::Configuration<U,I>>,z:Seq<g::Configuration<U,I>>,labels:Seq<c::Label>)
    requires related(a,z),a.len()==labels.len()+1,
    ensures c::inputs(a,labels)==c::inputs(z,labels),
{
    assert(c::raw_inputs(a,labels) =~= c::raw_inputs(z,labels));
}

pub proof fn intermediate_related<U,I>(a:g::Configuration<U,I>,z:g::Configuration<U,I>,x:g::Configuration<U,I>,w:g::Configuration<U,I>,id:usize,external:r::Rule)
    requires tr::related(a,x),tr::related(z,w),
    ensures tr::related(o::intermediate(a,z,id,external),o::intermediate(x,w,id,external)),
{ }

/// A constructed swap changes the observation at just the new intermediate
/// position. The original suffix is transported with authentic receipts.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn swap_frame<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:Seq<g::Configuration<U,I>>,labels:Seq<c::Label>,i:int)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a.first()),g::execution(lib,programs,a,labels),c::eligible(a,labels,i),
    ensures {
        let z=c::swap_states(lib,programs,a,labels,i);let zl=c::swap_labels(labels,i);
        &&& z.len()==a.len() && g::execution(lib,programs,z,zl) && g::well_formed(lib,programs,z.first())
        &&& z[i+1]==o::intermediate(a[i],a[i+2],labels[i+1].0,labels[i+1].1)
        &&& forall|j:int| 0<=j<a.len() && j!=i+1 ==> tr::related(a[j],z[j])
        &&& c::inputs(z,zl)==c::inputs(a,labels)
    },
{
    ol::execution_preservation(eq,lib,programs,a,labels);
    c::adjacent_swap(eq,lib,programs,a,labels,i);
    let z=c::swap_states(lib,programs,a,labels,i);let source=a.subrange(i+2,a.len() as int);let tail=labels.subrange(i+2,labels.len() as int);
    let endpoint=c::swapped_endpoint(lib,programs,a,labels,i);
    assert(g::execution(lib,programs,source,tail)) by {
        assert forall|j:int| 0<=j<tail.len() implies g::step(lib,programs,source[j],source[j+1],tail[j].0,tail[j].1) by {
            assert(g::step(lib,programs,a[i+2+j],a[i+3+j],labels[i+2+j].0,labels[i+2+j].1));
        }
    }
    // The endpoint relation follows from each actual local diamond.
    if g::landing(a[i],a[i+1],labels[i].1) {
        o::orchestration_diamond(eq,lib,programs,a[i],a[i+1],a[i+2],labels[i].0,labels[i].1,labels[i+1].0,labels[i+1].1);
    } else if labels[i].1==r::Rule::Unload {
        unload::diamond(eq,lib,programs,a[i],a[i+1],a[i+2],labels[i].0,labels[i+1].0,labels[i+1].1);
    } else {
        admin::diamond(eq,lib,programs,a[i],a[i+1],a[i+2],labels[i].0,labels[i].1,labels[i+1].0,labels[i+1].1);
    }
    assert(tr::related(source.first(),endpoint));tr::suffix_transport(lib,programs,source,tail,endpoint);
    let moved=tr::transport(source,tail,endpoint);
    assert forall|j:int| 0<=j<a.len() && j!=i+1 implies tr::related(a[j],z[j]) by {
        if j<=i {assert(z[j]==a[j]);}
        else {assert(i+2<=j);assert(z[j]==moved[j-i-2]);assert(a[j]==source[j-i-2]);assert(tr::related(source[j-i-2],moved[j-i-2]));}
    }
}

/// Related source histories give related real constructed swaps. In particular
/// full insertion arguments, including the original continuation I, agree.
pub proof fn swap_related<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:Seq<g::Configuration<U,I>>,z:Seq<g::Configuration<U,I>>,labels:Seq<c::Label>,i:int)
    requires og::primitive_theory(eq,lib),related(a,z),g::well_formed(lib,programs,a.first()),g::well_formed(lib,programs,z.first()),
        g::execution(lib,programs,a,labels),g::execution(lib,programs,z,labels),c::eligible(a,labels,i),
    ensures c::eligible(z,labels,i),related(c::swap_states(lib,programs,a,labels,i),c::swap_states(lib,programs,z,labels,i)),
        c::inputs(c::swap_states(lib,programs,a,labels,i),c::swap_labels(labels,i))==c::inputs(c::swap_states(lib,programs,z,labels,i),c::swap_labels(labels,i)),
{
    eligibility(lib,programs,a,z,labels);swap_frame(eq,lib,programs,a,labels,i);swap_frame(eq,lib,programs,z,labels,i);
    let left=c::swap_states(lib,programs,a,labels,i);let right=c::swap_states(lib,programs,z,labels,i);
    assert forall|j:int| 0<=j<left.len() implies tr::related(left[j],right[j]) by {
        if j==i+1 {intermediate_related(a[i],a[i+2],z[i],z[i+2],labels[i+1].0,labels[i+1].1);}
        else {tr::symmetric(a[j],left[j]);c::related_transitive(left[j],a[j],z[j]);c::related_transitive(left[j],z[j],right[j]);}
    }
    payloads(left,right,c::swap_labels(labels,i));
}

pub proof fn label_positions(labels:Seq<c::Label>,i:int)
    requires 0<=i && i+1<labels.len(),
    ensures c::swap_labels(labels,i).len()==labels.len(),
        forall|j:int| 0<=j<labels.len() ==> c::swap_labels(labels,i)[j]==if j==i {labels[i+1]} else if j==i+1 {labels[i]} else {labels[j]},
{ }
pub proof fn label_square(labels:Seq<c::Label>,i:int,j:int)
    requires 0<=i && i+1<labels.len(),0<=j && j+1<labels.len(),i+1<j || j+1<i,
    ensures c::swap_labels(c::swap_labels(labels,i),j)==c::swap_labels(c::swap_labels(labels,j),i),
{
    label_positions(labels,i);label_positions(labels,j);
    label_positions(c::swap_labels(labels,i),j);label_positions(c::swap_labels(labels,j),i);
    assert(c::swap_labels(c::swap_labels(labels,i),j) =~= c::swap_labels(c::swap_labels(labels,j),i));
}
/// Two available L/E redexes cannot overlap: their shared label would have
/// to be both lifecycle and external orchestration.
pub proof fn separate<U,I>(a:Seq<g::Configuration<U,I>>,labels:Seq<c::Label>,i:int,j:int)
    requires c::eligible(a,labels,i),c::eligible(a,labels,j),i!=j,
    ensures i+1<j || j+1<i,
{
    assert(!c::external(labels[i]));assert(!c::external(labels[j]));
}

pub proof fn surviving_redex<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:Seq<g::Configuration<U,I>>,labels:Seq<c::Label>,i:int,j:int)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a.first()),g::execution(lib,programs,a,labels),
        c::eligible(a,labels,i),c::eligible(a,labels,j),i!=j,
    ensures c::eligible(c::swap_states(lib,programs,a,labels,i),c::swap_labels(labels,i),j),
{
    separate(a,labels,i,j);label_positions(labels,i);swap_frame(eq,lib,programs,a,labels,i);
    let moved=c::swap_states(lib,programs,a,labels,i);let reordered=c::swap_labels(labels,i);
    assert(tr::related(a[j],moved[j]));assert(tr::related(a[j+1],moved[j+1]));assert(tr::related(a[j+2],moved[j+2]));
    eligible_at(lib,programs,a,labels,moved,reordered,j);
}

/// The actual two opposite orders of distinct rewrites produce the same labels
/// and pointwise related configurations. Each reverse redex is proved to survive.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn local_diamond<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:Seq<g::Configuration<U,I>>,labels:Seq<c::Label>,i:int,j:int)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a.first()),g::execution(lib,programs,a,labels),
        c::eligible(a,labels,i),c::eligible(a,labels,j),i!=j,
    ensures {
        let first=c::swap_states(lib,programs,a,labels,i);let fl=c::swap_labels(labels,i);
        let second=c::swap_states(lib,programs,a,labels,j);let sl=c::swap_labels(labels,j);
        let left=c::swap_states(lib,programs,first,fl,j);let ll=c::swap_labels(fl,j);
        let right=c::swap_states(lib,programs,second,sl,i);let rl=c::swap_labels(sl,i);
        &&& c::eligible(first,fl,j) && c::eligible(second,sl,i)
        &&& ll==rl && related(left,right)
        &&& g::execution(lib,programs,left,ll) && g::execution(lib,programs,right,rl)
        &&& g::well_formed(lib,programs,left.first()) && g::well_formed(lib,programs,right.first())
        &&& c::inputs(left,ll)==c::inputs(a,labels) && c::inputs(right,rl)==c::inputs(a,labels)
    },
{
    separate(a,labels,i,j);label_square(labels,i,j);label_positions(labels,i);label_positions(labels,j);
    swap_frame(eq,lib,programs,a,labels,i);swap_frame(eq,lib,programs,a,labels,j);
    surviving_redex(eq,lib,programs,a,labels,i,j);surviving_redex(eq,lib,programs,a,labels,j,i);
    let first=c::swap_states(lib,programs,a,labels,i);let fl=c::swap_labels(labels,i);
    let second=c::swap_states(lib,programs,a,labels,j);let sl=c::swap_labels(labels,j);
    swap_frame(eq,lib,programs,first,fl,j);swap_frame(eq,lib,programs,second,sl,i);
    let left=c::swap_states(lib,programs,first,fl,j);let right=c::swap_states(lib,programs,second,sl,i);
    assert forall|k:int| 0<=k<left.len() implies tr::related(left[k],right[k]) by {
        if k==i+1 {
            intermediate_related(a[i],a[i+2],second[i],second[i+2],labels[i+1].0,labels[i+1].1);
            assert(tr::related(first[k],right[k]));tr::symmetric(first[k],left[k]);c::related_transitive(left[k],first[k],right[k]);
        } else if k==j+1 {
            intermediate_related(a[j],a[j+2],first[j],first[j+2],labels[j+1].0,labels[j+1].1);
            assert(tr::related(second[k],left[k]));tr::symmetric(second[k],left[k]);c::related_transitive(left[k],second[k],right[k]);
        } else {
            tr::symmetric(first[k],left[k]);tr::symmetric(a[k],first[k]);
            c::related_transitive(left[k],first[k],a[k]);c::related_transitive(left[k],a[k],second[k]);c::related_transitive(left[k],second[k],right[k]);
        }
    }
}

/// Finite derivation in precisely this guarded rewrite system. A successor
/// is the concrete swap constructor, not an arbitrary equivalent execution.
pub open spec fn reaches<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:Seq<g::Configuration<U,I>>,labels:Seq<c::Label>,z:Seq<g::Configuration<U,I>>,zl:Seq<c::Label>,steps:nat)->bool
    decreases steps,
{
    if steps==0 {a==z && labels==zl}
    else {exists|i:int| c::eligible(a,labels,i) && reaches(lib,programs,c::swap_states(lib,programs,a,labels,i),c::swap_labels(labels,i),z,zl,(steps-1) as nat)}
}

pub proof fn reach_preservation<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:Seq<g::Configuration<U,I>>,labels:Seq<c::Label>,z:Seq<g::Configuration<U,I>>,zl:Seq<c::Label>,steps:nat)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a.first()),g::execution(lib,programs,a,labels),reaches(lib,programs,a,labels,z,zl,steps),
    ensures g::execution(lib,programs,z,zl),g::well_formed(lib,programs,z.first()),z.len()==a.len(),z.first()==a.first(),
        tr::related(a.last(),z.last()),c::inputs(z,zl)==c::inputs(a,labels),c::externals(zl)==c::externals(labels),c::lifecycles(zl)==c::lifecycles(labels),
        c::inversions(zl)+steps==c::inversions(labels),forall|i:int| 0<=i<z.len() ==> g::well_formed(lib,programs,z[i]),
    decreases steps,
{
    if steps==0 {ol::execution_preservation(eq,lib,programs,a,labels);}
    else {
        let i=choose|i:int| c::eligible(a,labels,i) && reaches(lib,programs,c::swap_states(lib,programs,a,labels,i),c::swap_labels(labels,i),z,zl,(steps-1) as nat);
        c::adjacent_swap(eq,lib,programs,a,labels,i);
        let next=c::swap_states(lib,programs,a,labels,i);let nl=c::swap_labels(labels,i);
        reach_preservation(eq,lib,programs,next,nl,z,zl,(steps-1) as nat);
        c::related_transitive(a.last(),next.last(),z.last());
    }
}

/// Construct a normal descendant and retain an actual rewrite derivation.
/// Each recursive call consumes one finite inversion, irrespective of guards.
pub proof fn reachable_normal<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:Seq<g::Configuration<U,I>>,labels:Seq<c::Label>)->(result:c::Normalized<U,I>)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a.first()),g::execution(lib,programs,a,labels),
    ensures reaches(lib,programs,a,labels,result.states,result.labels,result.swaps),c::normal(result.states,result.labels),
        g::execution(lib,programs,result.states,result.labels),g::well_formed(lib,programs,result.states.first()),
        result.states.first()==a.first(),tr::related(a.last(),result.states.last()),
        c::inputs(result.states,result.labels)==c::inputs(a,labels),c::externals(result.labels)==c::externals(labels),c::lifecycles(result.labels)==c::lifecycles(labels),
        c::inversions(result.labels)+result.swaps==c::inversions(labels),result.swaps<=c::inversions(labels),
    decreases c::inversions(labels),
{
    let result=if exists|i:int| c::eligible(a,labels,i) {
        let i=choose|i:int| c::eligible(a,labels,i);c::adjacent_swap(eq,lib,programs,a,labels,i);
        let next=reachable_normal(eq,lib,programs,c::swap_states(lib,programs,a,labels,i),c::swap_labels(labels,i));
        assert(reaches(lib,programs,a,labels,next.states,next.labels,next.swaps+1));
        c::Normalized {states:next.states,labels:next.labels,swaps:next.swaps+1}
    } else {c::Normalized {states:a,labels,swaps:0}};
    reach_preservation(eq,lib,programs,a,labels,result.states,result.labels,result.swaps);
    result
}

/// Lift a real rewrite derivation through pointwise receipt correspondence.
/// The same indices are actually executable in the other starting trace.
pub proof fn lift_reach<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:Seq<g::Configuration<U,I>>,x:Seq<g::Configuration<U,I>>,labels:Seq<c::Label>,z:Seq<g::Configuration<U,I>>,zl:Seq<c::Label>,steps:nat)->(right:Seq<g::Configuration<U,I>>)
    requires og::primitive_theory(eq,lib),related(a,x),g::well_formed(lib,programs,a.first()),g::well_formed(lib,programs,x.first()),
        g::execution(lib,programs,a,labels),g::execution(lib,programs,x,labels),reaches(lib,programs,a,labels,z,zl,steps),
    ensures reaches(lib,programs,x,labels,right,zl,steps),related(z,right),g::execution(lib,programs,right,zl),g::well_formed(lib,programs,right.first()),
        c::normal(z,zl)==c::normal(right,zl),
    decreases steps,
{
    let right=if steps==0 {x}
    else {
        let i=choose|i:int| c::eligible(a,labels,i) && reaches(lib,programs,c::swap_states(lib,programs,a,labels,i),c::swap_labels(labels,i),z,zl,(steps-1) as nat);
        swap_related(eq,lib,programs,a,x,labels,i);swap_frame(eq,lib,programs,a,labels,i);swap_frame(eq,lib,programs,x,labels,i);
        let out=lift_reach(eq,lib,programs,c::swap_states(lib,programs,a,labels,i),c::swap_states(lib,programs,x,labels,i),c::swap_labels(labels,i),z,zl,(steps-1) as nat);
        assert(reaches(lib,programs,x,labels,out,zl,steps));out
    };
    reach_preservation(eq,lib,programs,a,labels,z,zl,steps);reach_preservation(eq,lib,programs,x,labels,right,zl,steps);
    eligibility(lib,programs,z,right,zl);right
}

/// Any two normal descendants of the same original trace have equal labels
/// and pointwise related configurations. This is uniqueness only for this
/// terminating guarded rewrite, modulo actual receipt/history correspondence.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn unique_normal<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:Seq<g::Configuration<U,I>>,labels:Seq<c::Label>,left:Seq<g::Configuration<U,I>>,ll:Seq<c::Label>,ls:nat,
    right:Seq<g::Configuration<U,I>>,rl:Seq<c::Label>,rs:nat)
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a.first()),g::execution(lib,programs,a,labels),
        reaches(lib,programs,a,labels,left,ll,ls),reaches(lib,programs,a,labels,right,rl,rs),c::normal(left,ll),c::normal(right,rl),
    ensures ll==rl,related(left,right),c::inputs(left,ll)==c::inputs(right,rl),
    decreases c::inversions(labels),
{
    if ls==0 {
        if rs>0 {let j=choose|j:int| c::eligible(a,labels,j) && reaches(lib,programs,c::swap_states(lib,programs,a,labels,j),c::swap_labels(labels,j),right,rl,(rs-1) as nat);assert(false);}
        reflexive(left);
    } else if rs==0 {
        let i=choose|i:int| c::eligible(a,labels,i) && reaches(lib,programs,c::swap_states(lib,programs,a,labels,i),c::swap_labels(labels,i),left,ll,(ls-1) as nat);assert(false);
    } else {
        let i=choose|i:int| c::eligible(a,labels,i) && reaches(lib,programs,c::swap_states(lib,programs,a,labels,i),c::swap_labels(labels,i),left,ll,(ls-1) as nat);
        let j=choose|j:int| c::eligible(a,labels,j) && reaches(lib,programs,c::swap_states(lib,programs,a,labels,j),c::swap_labels(labels,j),right,rl,(rs-1) as nat);
        c::adjacent_swap(eq,lib,programs,a,labels,i);c::adjacent_swap(eq,lib,programs,a,labels,j);
        let first=c::swap_states(lib,programs,a,labels,i);let fl=c::swap_labels(labels,i);
        let second=c::swap_states(lib,programs,a,labels,j);let sl=c::swap_labels(labels,j);
        if i==j {unique_normal(eq,lib,programs,first,fl,left,ll,(ls-1) as nat,right,rl,(rs-1) as nat);}
        else {
            local_diamond(eq,lib,programs,a,labels,i,j);
            let dl=c::swap_states(lib,programs,first,fl,j);let dl_labels=c::swap_labels(fl,j);
            let dr=c::swap_states(lib,programs,second,sl,i);
            let normal=reachable_normal(eq,lib,programs,dl,dl_labels);
            let partner=lift_reach(eq,lib,programs,dl,dr,dl_labels,normal.states,normal.labels,normal.swaps);
            assert(reaches(lib,programs,first,fl,normal.states,normal.labels,normal.swaps+1));
            assert(reaches(lib,programs,second,sl,partner,normal.labels,normal.swaps+1));
            unique_normal(eq,lib,programs,first,fl,left,ll,(ls-1) as nat,normal.states,normal.labels,normal.swaps+1);
            unique_normal(eq,lib,programs,second,sl,right,rl,(rs-1) as nat,partner,normal.labels,normal.swaps+1);
            transitive(left,normal.states,partner);symmetric(right,partner);transitive(left,partner,right);
        }
    }
    reach_preservation(eq,lib,programs,a,labels,left,ll,ls);reach_preservation(eq,lib,programs,a,labels,right,rl,rs);
}

pub proof fn reach_concat<A,X,U,B,I>(lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:Seq<g::Configuration<U,I>>,al:Seq<c::Label>,b:Seq<g::Configuration<U,I>>,bl:Seq<c::Label>,z:Seq<g::Configuration<U,I>>,zl:Seq<c::Label>,first:nat,second:nat)
    requires reaches(lib,programs,a,al,b,bl,first),reaches(lib,programs,b,bl,z,zl,second),
    ensures reaches(lib,programs,a,al,z,zl,first+second),
    decreases first,
{
    if first>0 {
        let i=choose|i:int| c::eligible(a,al,i) && reaches(lib,programs,c::swap_states(lib,programs,a,al,i),c::swap_labels(al,i),b,bl,(first-1) as nat);
        reach_concat(lib,programs,c::swap_states(lib,programs,a,al,i),c::swap_labels(al,i),b,bl,z,zl,(first-1) as nat,second);
        assert(reaches(lib,programs,a,al,z,zl,first+second));
    }
}

/// Construct related normal descendants of any two finite rewrite descendants.
/// This is confluence modulo the stated trace relation within this rewrite
/// system, with concrete derivations and a finite bound for both continuations.
pub proof fn normal_join<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:g::Library<A,X,U,B>,programs:g::Programs<A,X,U,B,I>,
    a:Seq<g::Configuration<U,I>>,labels:Seq<c::Label>,left:Seq<g::Configuration<U,I>>,ll:Seq<c::Label>,ls:nat,
    right:Seq<g::Configuration<U,I>>,rl:Seq<c::Label>,rs:nat)->(result:(c::Normalized<U,I>,c::Normalized<U,I>))
    requires og::primitive_theory(eq,lib),g::well_formed(lib,programs,a.first()),g::execution(lib,programs,a,labels),
        reaches(lib,programs,a,labels,left,ll,ls),reaches(lib,programs,a,labels,right,rl,rs),
    ensures {
        let l=result.0;let r=result.1;
        &&& reaches(lib,programs,left,ll,l.states,l.labels,l.swaps) && reaches(lib,programs,right,rl,r.states,r.labels,r.swaps)
        &&& c::normal(l.states,l.labels) && c::normal(r.states,r.labels) && l.labels==r.labels && related(l.states,r.states)
        &&& g::execution(lib,programs,l.states,l.labels) && g::execution(lib,programs,r.states,r.labels)
        &&& l.swaps<=c::inversions(ll) && r.swaps<=c::inversions(rl)
        &&& c::inputs(l.states,l.labels)==c::inputs(a,labels) && c::inputs(r.states,r.labels)==c::inputs(a,labels)
    },
{
    reach_preservation(eq,lib,programs,a,labels,left,ll,ls);reach_preservation(eq,lib,programs,a,labels,right,rl,rs);
    let l=reachable_normal(eq,lib,programs,left,ll);let r=reachable_normal(eq,lib,programs,right,rl);
    reach_concat(lib,programs,a,labels,left,ll,l.states,l.labels,ls,l.swaps);
    reach_concat(lib,programs,a,labels,right,rl,r.states,r.labels,rs,r.swaps);
    unique_normal(eq,lib,programs,a,labels,l.states,l.labels,ls+l.swaps,r.states,r.labels,rs+r.swaps);
    (l,r)
}

pub open spec fn example_states()->Seq<g::Configuration<int,crate::recovery_examples::Stage>> {
    let original=crate::recovery_examples::trace();let retired=o::retire(original[7],1);
    let landed=g::land(crate::recovery_examples::library(),crate::recovery_examples::programs(),retired,0,crate::Phase::Active);
    seq![original[6],original[7],retired,landed,o::retire(landed,1)]
}
pub open spec fn example_labels()->Seq<c::Label> {
    seq![(0usize,r::Rule::Iter),(1usize,r::Rule::Retire),(0usize,r::Rule::Finish),(1usize,r::Rule::Retire)]
}

/// A real provision, captured +5 Operation and two retirements have two
/// simultaneously available rewrite choices. The competing square is nonempty.
#[verifier::spinoff_prover]
#[verifier::rlimit(40)]
pub proof fn actual_choices()
    ensures {
        let lib=crate::recovery_examples::library();let programs=crate::recovery_examples::programs();let a=example_states();let labels=example_labels();
        &&& og::primitive_theory(crate::recovery_examples::equality(),lib)
        &&& g::execution(lib,programs,a,labels) && g::well_formed(lib,programs,a.first())
        &&& c::eligible(a,labels,0) && c::eligible(a,labels,2)
        &&& a[1].state.tables[0usize][crate::recovery_examples::key(0)]==7
        &&& a[3].state.tables[0usize][crate::recovery_examples::key(0)]==12
        &&& related(c::swap_states(lib,programs,c::swap_states(lib,programs,a,labels,0),c::swap_labels(labels,0),2),
            c::swap_states(lib,programs,c::swap_states(lib,programs,a,labels,2),c::swap_labels(labels,2),0))
    },
{
    crate::recovery_examples::actual_execution();crate::recovery_examples::primitive_theory();o::actual_operation_retire();
    let eq=crate::recovery_examples::equality();let lib=crate::recovery_examples::library();let programs=crate::recovery_examples::programs();
    og::exact_theory(eq,lib);ol::from_empty_safe(eq,lib,programs,crate::recovery_examples::trace(),crate::recovery_examples::labels());
    reveal(crate::recovery_examples::trace);let a=example_states();let labels=example_labels();
    assert(g::step(lib,programs,a[0],a[1],0,r::Rule::Iter));
    assert(g::step(lib,programs,a[2],a[3],0,r::Rule::Finish));
    crate::child_history::concrete_child_retirement(a[1].state,1);assert(g::step(lib,programs,a[1],a[2],1,r::Rule::Retire));
    crate::child_history::concrete_child_retirement(a[3].state,1);assert(g::step(lib,programs,a[3],a[4],1,r::Rule::Retire));
    assert(g::execution(lib,programs,a,labels)) by {
        assert forall|i:int| 0<=i<labels.len() implies g::step(lib,programs,a[i],a[i+1],labels[i].0,labels[i].1) by {
            if i==0 {} else if i==1 {} else if i==2 {} else {assert(i==3);}
        }
    }
    local_diamond(eq,lib,programs,a,labels,0,2);
}

/// Starting with different available swaps gives related final normal traces;
/// the witness contains actual derivations after both distinct first choices.
pub proof fn actual_join()->(result:(c::Normalized<int,crate::recovery_examples::Stage>,c::Normalized<int,crate::recovery_examples::Stage>))
    ensures {
        let lib=crate::recovery_examples::library();let programs=crate::recovery_examples::programs();let a=example_states();let labels=example_labels();
        let left=c::swap_states(lib,programs,a,labels,0);let ll=c::swap_labels(labels,0);
        let right=c::swap_states(lib,programs,a,labels,2);let rl=c::swap_labels(labels,2);
        &&& reaches(lib,programs,left,ll,result.0.states,result.0.labels,result.0.swaps)
        &&& reaches(lib,programs,right,rl,result.1.states,result.1.labels,result.1.swaps)
        &&& result.0.labels==result.1.labels && related(result.0.states,result.1.states)
        &&& c::normal(result.0.states,result.0.labels) && c::normal(result.1.states,result.1.labels)
        &&& g::execution(lib,programs,result.0.states,result.0.labels) && g::execution(lib,programs,result.1.states,result.1.labels)
        &&& c::inputs(result.0.states,result.0.labels)==c::inputs(a,labels)
        &&& c::inputs(result.1.states,result.1.labels)==c::inputs(a,labels)
    },
{
    actual_choices();let eq=crate::recovery_examples::equality();let lib=crate::recovery_examples::library();let programs=crate::recovery_examples::programs();
    let a=example_states();let labels=example_labels();
    let left=c::swap_states(lib,programs,a,labels,0);let ll=c::swap_labels(labels,0);
    let right=c::swap_states(lib,programs,a,labels,2);let rl=c::swap_labels(labels,2);
    reveal_with_fuel(reaches,2);
    assert(c::eligible(a,labels,0) && reaches(lib,programs,c::swap_states(lib,programs,a,labels,0),c::swap_labels(labels,0),left,ll,0));
    assert(c::eligible(a,labels,2) && reaches(lib,programs,c::swap_states(lib,programs,a,labels,2),c::swap_labels(labels,2),right,rl,0));
    assert(reaches(lib,programs,a,labels,left,ll,1));assert(reaches(lib,programs,a,labels,right,rl,1));
    normal_join(eq,lib,programs,a,labels,left,ll,1,right,rl,1)
}

} // verus!
