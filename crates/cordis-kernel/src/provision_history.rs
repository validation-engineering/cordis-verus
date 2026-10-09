//! Provision inverse domains reconstructed from actual source journals.
//!
//! A successful Provision adds a previously absent key and records it once.
//! Other forward primitives preserve existing table domains. A foreign unload
//! can change values but cannot remove this actor's keys; an own unload clears
//! its journal. The induction accepts all actual mixed and fresh source steps.
#[cfg(verus_keep_ghost)]
use crate::{
    dependent_grammar as d, fresh_grammar as fg, fresh_semantics as fs, grammar_lift as gl,
    mixed_grammar as mx, mixed_recovery as mr, preservation as inv, refinement as r,
    semantics as s, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn provision_key<U>(receipt:mx::Receipt<U>)->Option<Port> {
    match receipt {
        mx::Receipt::Table {receipt}=>match receipt.inverse {
            gl::Inverse::Provision {key}=>Some(key),_=>None,
        },
        _=>None,
    }
}

pub open spec fn provision_at<U,I>(a:mx::Configuration<U,I>,actor:usize,i:int)->Option<Port> {
    provision_key(a.history[a.state.accumulators[actor][i] as int].landed.receipt)
}

/// Presence and uniqueness concern positions in the live accumulator, not all
/// historical provisions: a later episode may provision the same key again.
pub open spec fn live_provisions<U,I>(a:mx::Configuration<U,I>)->bool {
    &&& forall|n:usize,i:int| s::registered(a.state,n) && 0<=i<a.state.accumulators[n].len()
        && #[trigger] provision_at(a,n,i).is_some()
        ==> a.state.tables[n].dom().contains(provision_at(a,n,i).unwrap())
    &&& forall|n:usize,i:int,j:int| s::registered(a.state,n) && 0<=i<j<a.state.accumulators[n].len()
        && #[trigger] provision_at(a,n,i).is_some()
        ==> provision_at(a,n,i)!=#[trigger] provision_at(a,n,j)
}

/// A common journal projection of the two source grammars. This is derived
/// from each actual rule below; it does not posit the successor invariant.
spec fn journal_step<U,I>(a:mx::Configuration<U,I>,z:mx::Configuration<U,I>)->bool {
    &&& a.history.len()<=z.history.len()
    &&& forall|i:int| 0<=i<a.history.len() ==> #[trigger] a.history[i]==z.history[i]
    &&& forall|n:usize| s::registered(z.state,n) && z.state.accumulators[n].len()>0 ==> {
        &&& s::registered(a.state,n)
        &&& a.state.tables[n].dom().subset_of(z.state.tables[n].dom())
        &&& (z.state.accumulators[n]==a.state.accumulators[n]
            || (z.state.accumulators[n]==a.state.accumulators[n].push(a.history.len())
                && z.history.len()==a.history.len()+1
                && (provision_key(z.history.last().landed.receipt).is_some() ==> {
                    let key=provision_key(z.history.last().landed.receipt).unwrap();
                    &&& !a.state.tables[n].dom().contains(key)
                    &&& z.state.tables[n].dom().contains(key)
                })))
    }
}

proof fn journal_preservation<U,I>(a:mx::Configuration<U,I>,z:mx::Configuration<U,I>)
    requires mx::tokens_valid(a),live_provisions(a),journal_step(a,z),
    ensures live_provisions(z),
{
    assert forall|n:usize,i:int| s::registered(z.state,n) && 0<=i<z.state.accumulators[n].len()
        && #[trigger] provision_at(z,n,i).is_some()
        implies z.state.tables[n].dom().contains(provision_at(z,n,i).unwrap()) by {
        if i<a.state.accumulators[n].len() {
            let token=a.state.accumulators[n][i];
            assert(token<a.history.len());
            assert(z.state.accumulators[n][i]==token);
            assert(z.history[token as int]==a.history[token as int]);
            assert(provision_at(a,n,i)==provision_at(z,n,i));
        } else {
            assert(i==a.state.accumulators[n].len());
            assert(z.state.accumulators[n][i]==a.history.len());
            assert(z.history[a.history.len() as int]==z.history.last());
        }
    }
    assert forall|n:usize,i:int,j:int| s::registered(z.state,n) && 0<=i<j<z.state.accumulators[n].len()
        && #[trigger] provision_at(z,n,i).is_some()
        implies provision_at(z,n,i)!=#[trigger] provision_at(z,n,j) by {
        assert(i<a.state.accumulators[n].len());
        let token=a.state.accumulators[n][i];
        assert(token<a.history.len());
        assert(z.state.accumulators[n][i]==token);
        assert(z.history[token as int]==a.history[token as int]);
        assert(provision_at(a,n,i)==provision_at(z,n,i));
        if j<a.state.accumulators[n].len() {
            let other=a.state.accumulators[n][j];
            assert(other<a.history.len());
            assert(z.state.accumulators[n][j]==other);
            assert(z.history[other as int]==a.history[other as int]);
            assert(provision_at(a,n,j)==provision_at(z,n,j));
        } else {
            assert(j==a.state.accumulators[n].len());
            assert(z.state.accumulators[n][j]==a.history.len());
            assert(z.history[a.history.len() as int]==z.history.last());
            if provision_at(z,n,i)==provision_at(z,n,j) {
                let key=provision_at(z,n,i).unwrap();
                assert(a.state.tables[n].dom().contains(key));
                assert(!a.state.tables[n].dom().contains(key));
            }
        }
    }
}

proof fn run_domains<A,X,U,B,I>(lib:mx::Library<A,X,U,B>,node:mx::Node<A,X,U,B,I>,a:s::State<U>,actor:usize)
    requires inv::well_formed(a),mx::run(lib,node,a,actor).is_some(),
    ensures {
        let out=mx::run(lib,node,a,actor).unwrap();
        &&& forall|n:usize| s::registered(a,n) ==> a.tables[n].dom().subset_of(out.state.tables[n].dom())
        &&& (provision_key(out.receipt).is_some() ==> {
            let key=provision_key(out.receipt).unwrap();
            &&& !a.tables[actor].dom().contains(key)
            &&& out.state.tables[actor].dom().contains(key)
        })
    },
{
    let out=mx::run(lib,node,a,actor).unwrap();
    assert forall|n:usize| s::registered(a,n) implies a.tables[n].dom().subset_of(out.state.tables[n].dom()) by {
        match node {
            mx::Node::Dependent {node}=>match node {
                d::Node::Unit=>{},d::Node::Operation {..}=>{},d::Node::Provision {..}=>{},
            },
            mx::Node::Child {child,..}=>{assert(n!=child);},
        }
    }
    match node {mx::Node::Dependent {node}=>{match node {d::Node::Provision {..}=>{},_=>{}}},_=>{}}
}

pub proof fn mixed_step<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize,rule:r::Rule)
    requires d::primitive_theory(eq,lib),mx::well_formed(lib,programs,a),live_provisions(a),mx::step(lib,programs,a,z,actor,rule),
    ensures live_provisions(z),
{
    mx::frame(eq,lib,programs,a,z,actor,rule);
    if mx::landing(a,z,rule) {run_domains(lib,programs(actor)(a.current[actor].unwrap()),a.state,actor);}
    if rule==r::Rule::Unload {mr::restore_domains(a.history,a.state.accumulators[actor],a.state,actor);}
    assert forall|i:int| 0<=i<a.history.len() implies #[trigger] a.history[i]==z.history[i] by {}
    assert forall|n:usize| s::registered(z.state,n) && z.state.accumulators[n].len()>0 implies {
        &&& s::registered(a.state,n)
        &&& a.state.tables[n].dom().subset_of(z.state.tables[n].dom())
        &&& (z.state.accumulators[n]==a.state.accumulators[n]
            || (z.state.accumulators[n]==a.state.accumulators[n].push(a.history.len())
                && z.history.len()==a.history.len()+1
                && (provision_key(z.history.last().landed.receipt).is_some() ==> {
                    let key=provision_key(z.history.last().landed.receipt).unwrap();
                    &&& !a.state.tables[n].dom().contains(key)
                    &&& z.state.tables[n].dom().contains(key)
                })))
    } by {
        assert(s::registered(a.state,n));
        if mx::landing(a,z,rule) {
            let out=mx::entry(lib,programs,a,actor).landed;
            assert(a.state.tables[n].dom().subset_of(out.state.tables[n].dom()));
            assert(z.state.tables[n]==out.state.tables[n]);
            if n==actor {assert(z.history.last()==mx::entry(lib,programs,a,actor));}
        } else {
            if rule==r::Rule::Unload {assert(n!=actor);}
            match rule {r::Rule::Insert | r::Rule::Remove=>{assert(n!=actor);},_=>{}}
            assert(z.state.accumulators[n]==a.state.accumulators[n]);
            assert(a.state.tables[n].dom()==z.state.tables[n].dom());
        }
    }
    journal_preservation(a,z);
}

pub proof fn fresh_step<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:fs::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,a:mx::Configuration<U,I>,z:mx::Configuration<U,I>,actor:usize,rule:r::Rule,choice:Option<usize>)
    requires crate::observational_grammar::primitive_theory(eq,lib),fs::well_formed(lib,programs,a),live_provisions(a),fs::step(lib,programs,a,z,actor,rule,choice),
    ensures live_provisions(z),
{
    fs::frame(eq,lib,programs,a,z,actor,rule,choice);
    if mx::landing(a,z,rule) {
        let node=fg::instantiate(programs(actor)(a.current[actor].unwrap()),choice).unwrap();
        assert(mx::run(lib,node,a.state,actor).is_some());
        run_domains(lib,node,a.state,actor);
    }
    if rule==r::Rule::Unload {mr::restore_domains(a.history,a.state.accumulators[actor],a.state,actor);}
    assert forall|i:int| 0<=i<a.history.len() implies #[trigger] a.history[i]==z.history[i] by {}
    assert forall|n:usize| s::registered(z.state,n) && z.state.accumulators[n].len()>0 implies {
        &&& s::registered(a.state,n)
        &&& a.state.tables[n].dom().subset_of(z.state.tables[n].dom())
        &&& (z.state.accumulators[n]==a.state.accumulators[n]
            || (z.state.accumulators[n]==a.state.accumulators[n].push(a.history.len())
                && z.history.len()==a.history.len()+1
                && (provision_key(z.history.last().landed.receipt).is_some() ==> {
                    let key=provision_key(z.history.last().landed.receipt).unwrap();
                    &&& !a.state.tables[n].dom().contains(key)
                    &&& z.state.tables[n].dom().contains(key)
                })))
    } by {
        assert(s::registered(a.state,n));
        if mx::landing(a,z,rule) {
            let out=fs::entry(lib,programs,a,actor,choice).landed;
            assert(a.state.tables[n].dom().subset_of(out.state.tables[n].dom()));
            assert(z.state.tables[n]==out.state.tables[n]);
            if n==actor {assert(z.history.last()==fs::entry(lib,programs,a,actor,choice));}
        } else {
            if rule==r::Rule::Unload {assert(n!=actor);}
            match rule {r::Rule::Insert | r::Rule::Remove=>{assert(n!=actor);},_=>{}}
            assert(z.state.accumulators[n]==a.state.accumulators[n]);
            assert(a.state.tables[n].dom()==z.state.tables[n].dom());
        }
    }
    journal_preservation(a,z);
}

proof fn mixed_execution<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires d::primitive_theory(eq,lib),mx::execution(lib,programs,states,labels),mx::well_formed(lib,programs,states.first()),live_provisions(states.first()),
    ensures forall|i:int| 0<=i<states.len() ==> live_provisions(states[i]),
    decreases labels.len(),
{
    if labels.len()>0 {
        let before=states.drop_last();let steps=labels.drop_last();
        assert(mx::execution(lib,programs,before,steps)) by {
            assert forall|i:int| 0<=i<steps.len() implies mx::step(lib,programs,before[i],before[i+1],steps[i].0,steps[i].1) by {}
        }
        mixed_execution(eq,lib,programs,before,steps);
        mx::execution_preservation(eq,lib,programs,states,labels);
        mixed_step(eq,lib,programs,before.last(),states.last(),labels.last().0,labels.last().1);
        assert forall|i:int| 0<=i<states.len() implies live_provisions(states[i]) by {
            if i<before.len() {assert(before[i]==states[i]);} else {assert(i==states.len()-1);}
        }
    }
}

proof fn fresh_execution<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:fs::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<fs::Label>)
    requires crate::observational_grammar::primitive_theory(eq,lib),fs::execution(lib,programs,states,labels),fs::well_formed(lib,programs,states.first()),live_provisions(states.first()),
    ensures forall|i:int| 0<=i<states.len() ==> live_provisions(states[i]),
    decreases labels.len(),
{
    if labels.len()>0 {
        let before=states.drop_last();let steps=labels.drop_last();
        assert(fs::execution(lib,programs,before,steps)) by {
            assert forall|i:int| 0<=i<steps.len() implies fs::step(lib,programs,before[i],before[i+1],steps[i].0,steps[i].1,steps[i].2) by {}
        }
        fresh_execution(eq,lib,programs,before,steps);
        fs::execution_preservation(eq,lib,programs,states,labels);
        fresh_step(eq,lib,programs,before.last(),states.last(),labels.last().0,labels.last().1,labels.last().2);
        assert forall|i:int| 0<=i<states.len() implies live_provisions(states[i]) by {
            if i<before.len() {assert(before[i]==states[i]);} else {assert(i==states.len()-1);}
        }
    }
}

pub proof fn mixed_from_empty<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:mx::Library<A,X,U,B>,programs:mx::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<(usize,r::Rule)>)
    requires d::primitive_theory(eq,lib),mx::execution(lib,programs,states,labels),states.first()==mx::empty::<U,I>(),
    ensures forall|i:int| 0<=i<states.len() ==> live_provisions(states[i]),
{
    mx::empty_well_formed(lib,programs);
    mixed_execution(eq,lib,programs,states,labels);
}

pub proof fn fresh_from_empty<A,X,U,B,I>(eq:spec_fn(Port,U,U)->bool,lib:fs::Library<A,X,U,B>,programs:fs::Programs<A,X,U,B,I>,states:Seq<mx::Configuration<U,I>>,labels:Seq<fs::Label>)
    requires crate::observational_grammar::primitive_theory(eq,lib),fs::execution(lib,programs,states,labels),states.first()==fs::empty::<U,I>(),
    ensures forall|i:int| 0<=i<states.len() ==> live_provisions(states[i]),
{
    fs::empty_well_formed(lib,programs);
    fresh_execution(eq,lib,programs,states,labels);
}

}
