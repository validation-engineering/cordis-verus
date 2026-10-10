//! Every occupied owner slot has a Provision inverse in its live source journal.
//!
//! This is the converse of Provision-domain retention: it connects all current
//! table values to the receipts that erase them. It follows from empty-origin
//! Mixed and Fresh executions, including dynamic children and foreign cleanup.
//! Only past successful source Unloads supply restoration definedness here.
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_grammar as d, entangled as e, fresh_grammar as fg, fresh_semantics as fs,
    mixed_grammar as mx, mixed_recovery as mr, observational_grammar as og, refinement as r,
    semantics as s, Port,
};
use vstd::prelude::*;

verus! {

/// Mixed coverage already follows from the existing actual-history induction.
pub proof fn mixed_from_empty<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires d::primitive_theory(eq,lib),mx::execution(lib,programs,states,labels),states.first()==mx::empty::<U,I>(),
    ensures forall|i:int| 0<=i<states.len() ==> mr::provided_journals(states[i]),
{
    mx::empty_well_formed(lib,programs);
    mr::trace_provided_journals(eq,lib,programs,states,labels);
}

/// Allocation is the choice attached to this real Fresh landing. The journal
/// projection appends exactly its returned inverse, with old tokens unchanged.
proof fn fresh_landing_word<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:fs::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize,rule:r::Rule,choice:Option<usize>)
    requires og::primitive_theory(eq,lib),fs::well_formed(lib,programs,a),fs::step(lib,programs,a,z,actor,rule,choice),mx::landing(a,z,rule),
    ensures mr::own_word(z,actor)==mr::own_word(a,actor).push(mr::receipt_action(fs::entry(lib,programs,a,actor,choice).landed.receipt)),
{
    fs::frame(eq,lib,programs,a,z,actor,rule,choice);
    let receipt=fs::entry(lib,programs,a,actor,choice).landed.receipt;
    assert(mr::own_word(z,actor) =~= mr::own_word(a,actor).push(mr::receipt_action(receipt))) by {
        assert forall|i:int| 0<=i<mr::own_word(z,actor).len()
            implies mr::own_word(z,actor)[i]==mr::own_word(a,actor).push(mr::receipt_action(receipt))[i] by {
            if i<a.state.accumulators[actor].len() {
                let token=a.state.accumulators[actor][i];
                assert(token<a.history.len());
                assert(z.state.accumulators[actor][i]==token);
                assert(z.history[token as int]==a.history[token as int]);
            } else {
                assert(i==a.state.accumulators[actor].len());
                assert(z.state.accumulators[actor][i]==a.history.len());
                assert(z.history[a.history.len() as int]==fs::entry(lib,programs,a,actor,choice));
            }
        }
    }
}

pub proof fn fresh_step<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:fs::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize,rule:r::Rule,choice:Option<usize>)
    requires og::primitive_theory(eq,lib),fs::well_formed(lib,programs,a),mr::provided_journals(a),fs::step(lib,programs,a,z,actor,rule,choice),
    ensures mr::provided_journals(z),
{
    fs::frame(eq,lib,programs,a,z,actor,rule,choice);
    fs::state_preservation(eq,lib,programs,a,z,actor,rule,choice);
    assert(a.history.len()<=z.history.len());
    assert forall|i:int| 0<=i<a.history.len() implies #[trigger] a.history[i]==z.history[i] by {}
    if mx::landing(a,z,rule) {
        fresh_landing_word(eq,lib,programs,a,z,actor,rule,choice);
    }
    if rule==r::Rule::Unload {
        mr::restored_owner_empty(a,actor);
        mr::restore_domains(a.history,a.state.accumulators[actor],a.state,actor);
    }
    assert forall|n:usize,k:Port| s::registered(z.state,n) && z.state.tables[n].dom().contains(k)
        implies #[trigger] e::erases(mr::own_word(z,n),k) by {
        if !s::registered(a.state,n) {
            if mx::landing(a,z,rule) {
                let out=fs::entry(lib,programs,a,actor,choice).landed;
                assert(out.spawn.unwrap().0==n);
                assert(z.state.tables[n].is_empty());
            }
            assert(false);
        } else {
            assert(s::registered(a.state,n));
            if n==actor && mx::landing(a,z,rule) {
                let node=fg::instantiate(programs(actor)(a.current[actor].unwrap()),choice).unwrap();
                let receipt=fs::entry(lib,programs,a,actor,choice).landed.receipt;
                assert(mx::run(lib,node,a.state,actor).is_some());
                if !a.state.tables[n].dom().contains(k) {
                    match node {
                        mx::Node::Dependent {node:d::Node::Provision {key,..}}=>{
                            assert(key==k);
                            mr::provision_receipt_action(receipt,k);
                        },
                        _=>{assert(false);},
                    }
                    assert(mr::own_word(z,n).last()==(e::Action::Restriction {key:k}));
                } else {
                    assert(e::erases(mr::own_word(a,n),k));
                    let i=choose|i:int| 0<=i<mr::own_word(a,n).len() && mr::own_word(a,n)[i]==(e::Action::Restriction {key:k});
                    assert(mr::own_word(z,n)[i]==(e::Action::Restriction {key:k}));
                }
            } else if n==actor && rule==r::Rule::Unload {
                assert(false);
            } else if n==actor && rule==r::Rule::Begin {
                assert(a.state.tables[n].dom().contains(k));
                assert(e::erases(mr::own_word(a,n),k));
                assert(a.state.accumulators[n].len()==0);
                assert(mr::own_word(a,n).len()==0);
                assert(false);
            } else {
                assert(a.state.tables[n].dom().contains(k));
                assert(a.state.accumulators[n]==z.state.accumulators[n]);
                mr::unchanged_word(a,z,n);
            }
        }
    }
}

proof fn fresh_execution<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:fs::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<fs::Label>)
    requires og::primitive_theory(eq,lib),fs::execution(lib,programs,states,labels),
        fs::well_formed(lib,programs,states.first()),mr::provided_journals(states.first()),
    ensures forall|i:int| 0<=i<states.len() ==> mr::provided_journals(states[i]),
    decreases labels.len(),
{
    if labels.len()>0 {
        let before=states.drop_last();let steps=labels.drop_last();
        assert(fs::execution(lib,programs,before,steps)) by {
            assert forall|i:int| 0<=i<steps.len()
                implies fs::step(lib,programs,before[i],before[i+1],steps[i].0,steps[i].1,steps[i].2) by {}
        }
        fresh_execution(eq,lib,programs,before,steps);
        fs::execution_preservation(eq,lib,programs,states,labels);
        fresh_step(eq,lib,programs,before.last(),states.last(),labels.last().0,labels.last().1,labels.last().2);
        assert forall|i:int| 0<=i<states.len() implies mr::provided_journals(states[i]) by {
            if i<before.len() {assert(before[i]==states[i]);} else {assert(i==states.len()-1);}
        }
    }
}

pub proof fn fresh_from_empty<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:fs::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<fs::Label>)
    requires og::primitive_theory(eq,lib),fs::execution(lib,programs,states,labels),states.first()==fs::empty::<U,I>(),
    ensures forall|i:int| 0<=i<states.len() ==> mr::provided_journals(states[i]),
{
    fs::empty_well_formed(lib,programs);
    fresh_execution(eq,lib,programs,states,labels);
}

}
