//! Continuous installation derived from actual terminal-episode labels.
//!
//! Begin installs its owner. Until that owner's next Unload, every actual step
//! preserves its registration and non-Inactive phase. Foreign Child recovery
//! may retire the owner, but never removes it or ends the installed episode.
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_grammar as d, grammar_recovery as gr, mixed_grammar as mx, refinement as r,
    semantics as s, Phase, Port,
};
use vstd::prelude::*;

verus! {

/// Recovering another actor can retire a captured Child, but preserves every
/// existing phase. Remove cannot act on this owner while it is installed.
pub proof fn mixed_installed_step<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize,rule:r::Rule,owner:usize)
    requires d::primitive_theory(eq,lib),mx::well_formed(lib,programs,a),
        mx::step(lib,programs,a,z,actor,rule),gr::installed(a.state,owner),
        actor!=owner || rule!=r::Rule::Unload,
    ensures gr::installed(z.state,owner),
{
    mx::frame(eq,lib,programs,a,z,actor,rule);
    if mx::landing(a,z,rule) {
        let id=a.current[actor].unwrap();
        mx::run_members(eq,lib,programs,a.state,actor,id);
        mx::run_admissible(eq,lib,programs(actor)(id),a.state,actor);
    }
    if rule==r::Rule::Unload {
        mx::restore_preservation(lib,programs,a.history,a.state.accumulators[actor],a.state,actor);
    }
    if actor==owner {
        assert(rule!=r::Rule::Insert && rule!=r::Rule::Remove && rule!=r::Rule::Begin);
        match rule {
            r::Rule::Retire=>{},
            r::Rule::Iter | r::Rule::Finish | r::Rule::Divert | r::Rule::Leave=>{},
            _=>{assert(false);},
        }
    } else {
        assert(s::registered(z.state,owner));
        assert(z.state.control.fibers[owner].phase==a.state.control.fibers[owner].phase);
    }
}

proof fn mixed_installed_at<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize,start:int,index:int)
    requires d::primitive_theory(eq,lib),mx::execution(lib,programs,states,labels),
        forall|i:int| 0<=i<states.len() ==> mx::well_formed(lib,programs,states[i]),
        0<=start<=index<states.len(),gr::installed(states[start].state,owner),
        forall|i:int| start<=i<index ==> labels[i]!=(owner,r::Rule::Unload),
    ensures gr::installed(states[index].state,owner),
    decreases index-start,
{
    if index>start {
        mixed_installed_at(eq,lib,programs,states,labels,owner,start,index-1);
        let label=labels[index-1];
        assert(mx::step(lib,programs,states[index-1],states[index],label.0,label.1));
        assert(label!=(owner,r::Rule::Unload));
        mixed_installed_step(eq,lib,programs,states[index-1],states[index],label.0,label.1,owner);
    }
}

/// The observable Begin/Unload cut identifies one continuous installed
/// episode. Installation of intermediate states is a conclusion, not a
/// condition supplied by a caller of the terminal-recovery theorem.
pub proof fn mixed_installed_interval<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>,owner:usize,begin:int,end:int)
    requires d::primitive_theory(eq,lib),mx::execution(lib,programs,states,labels),
        states.first()==mx::empty::<U,I>(),0<=begin<end<labels.len(),
        labels[begin]==(owner,r::Rule::Begin),labels[end]==(owner,r::Rule::Unload),
        forall|i:int| begin<i<end ==> labels[i]!=(owner,r::Rule::Unload),
    ensures forall|i:int| begin<i<=end ==> gr::installed(states[i].state,owner),
{
    mx::empty_well_formed(lib,programs);
    mx::execution_preservation(eq,lib,programs,states,labels);
    assert(mx::step(lib,programs,states[begin],states[begin+1],owner,r::Rule::Begin));
    assert(states[begin+1].state.control.fibers[owner].phase==Phase::Loading);
    assert(gr::installed(states[begin+1].state,owner));
    assert forall|i:int| begin<i<=end implies gr::installed(states[i].state,owner) by {
        mixed_installed_at(eq,lib,programs,states,labels,owner,begin+1,i);
    }
}

}
