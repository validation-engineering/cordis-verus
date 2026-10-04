//! The state-map/edit factorization and immutable metadata of all nine rules.
//!
//! The source tag records which actual iterator or accumulator was applied;
//! extensionally equal functions do not erase that provenance. Frozen edits
//! and maps are defined away from the actual input, without claiming that the
//! same rule is enabled on those counterfactual states.
#[cfg(verus_keep_ghost)]
use crate::{entangled as e, preservation as p, refinement as c, semantics as s, Phase};
use vstd::prelude::*;

verus! {

pub enum Source {
    Identity,
    Iteration { actor:usize, iterator:nat },
    Restoration { actor:usize, tokens:Seq<nat> },
}

pub open spec fn source<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,actor:usize,rule:c::Rule)->Source {
    if e::lands(model,a,z,actor,rule) {Source::Iteration{actor,iterator:a.iterators[actor].unwrap()}}
    else if rule==c::Rule::Unload {Source::Restoration{actor,tokens:a.accumulators[actor]}}
    else {Source::Identity}
}

pub open spec fn apply<V>(model:s::Model<V>,origin:Source,x:s::State<V>)->s::State<V> {
    match origin {
        Source::Identity=>x,
        Source::Iteration{actor,iterator}=>(model.iterate)(actor,iterator,x).state,
        Source::Restoration{actor:_,tokens}=>s::restore(model,tokens,x),
    }
}

/// All assigned values are frozen from the actual successor. The input x is
/// used for untouched fields, so this is not a constant-successor function.
pub open spec fn bracket<V>(z:s::State<V>,actor:usize,rule:c::Rule,x:s::State<V>)->s::State<V> {
    match rule {
        c::Rule::Insert=>s::State {
            control:c::State{fibers:x.control.fibers.insert(actor,z.control.fibers[actor])},
            tables:x.tables.insert(actor,IMap::empty()),effects:x.effects.insert(actor,z.effects[actor]),
            iterators:x.iterators.insert(actor,None),accumulators:x.accumulators.insert(actor,Seq::empty()),
        },
        c::Rule::Retire=>s::State {
            control:c::State{fibers:x.control.fibers.insert(actor,c::Fiber{retired:true,..x.control.fibers[actor]})},
            ..x
        },
        c::Rule::Remove=>s::erase(x,actor),
        _=>s::edit(x,actor,z.control.fibers[actor].phase,z.control.fibers[actor].committed,z.iterators[actor],z.accumulators[actor]),
    }
}

pub proof fn factorization<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,actor:usize,rule:c::Rule)
    requires s::shaped(a),s::step(model,a,z,actor,rule),
    ensures z==bracket(z,actor,rule,apply(model,source(model,a,z,actor,rule),a)),
        (matches!(source(model,a,z,actor,rule),Source::Restoration{..})) == (rule==c::Rule::Unload),
{
    if rule==c::Rule::Insert || rule==c::Rule::Retire || rule==c::Rule::Remove {
        assert(c::step(a.control,z.control,actor,rule));
        assert forall|n:usize| n!=actor implies s::registered(a,n)==s::registered(z,n)
            && (s::registered(a,n) ==> a.control.fibers[n]==z.control.fibers[n]) by {
            assert(c::frame(a.control,z.control,actor));
        }
    }
    if rule==c::Rule::Insert {
        assert(!c::registered(a.control,actor));
        assert(c::registered(z.control,actor));
        assert forall|n:usize| z.control.fibers.dom().contains(n)==a.control.fibers.dom().insert(actor).contains(n) by {
            if n!=actor {assert(c::registered(a.control,n)==c::registered(z.control,n));
                if c::registered(a.control,n) {assert(a.control.fibers[n]==z.control.fibers[n]);}}
        }
        assert forall|n:usize| z.control.fibers.dom().contains(n) implies z.control.fibers[n]==a.control.fibers.insert(actor,z.control.fibers[actor])[n] by {
            if n!=actor {assert(c::registered(a.control,n)==c::registered(z.control,n));
                if c::registered(a.control,n) {assert(a.control.fibers[n]==z.control.fibers[n]);}}
        }
        assert(z.control.fibers =~= a.control.fibers.insert(actor,z.control.fibers[actor]));
        assert(z.tables[actor] =~= IMap::empty());
        assert(z.accumulators[actor] =~= Seq::empty());
        assert forall|n:usize| z.tables.dom().contains(n) implies z.tables[n]==a.tables.insert(actor,IMap::empty())[n] by {
            if n!=actor {assert(s::registered(a,n));assert(z.tables[n]==a.tables[n]);}
        }
        assert(z.tables =~= a.tables.insert(actor,IMap::empty()));
        assert(z.effects =~= a.effects.insert(actor,z.effects[actor]));
        assert(z.iterators =~= a.iterators.insert(actor,None));
        assert(z.accumulators =~= a.accumulators.insert(actor,Seq::empty()));
    } else if rule==c::Rule::Retire {
        assert(c::registered(a.control,actor));assert(c::registered(z.control,actor));
        assert(z.control.fibers[actor]==c::Fiber{retired:true,..a.control.fibers[actor]});
        assert forall|n:usize| z.control.fibers.dom().contains(n)==a.control.fibers.dom().contains(n) by {
            if n!=actor {assert(c::registered(a.control,n)==c::registered(z.control,n));
                if c::registered(a.control,n) {assert(a.control.fibers[n]==z.control.fibers[n]);}}
        }
        assert forall|n:usize| z.control.fibers.dom().contains(n) implies z.control.fibers[n]==a.control.fibers.insert(actor,c::Fiber{retired:true,..a.control.fibers[actor]})[n] by {
            if n!=actor {assert(c::registered(a.control,n)==c::registered(z.control,n));
                if c::registered(a.control,n) {assert(a.control.fibers[n]==z.control.fibers[n]);}}
        }
        assert(z.control.fibers =~= a.control.fibers.insert(actor,c::Fiber{retired:true,..a.control.fibers[actor]}));
    } else if rule==c::Rule::Remove {
        assert(c::registered(a.control,actor));assert(!c::registered(z.control,actor));
        assert forall|n:usize| z.control.fibers.dom().contains(n)==a.control.fibers.dom().remove(actor).contains(n) by {
            if n!=actor {assert(c::registered(a.control,n)==c::registered(z.control,n));
                if c::registered(a.control,n) {assert(a.control.fibers[n]==z.control.fibers[n]);}}
        }
        assert forall|n:usize| z.control.fibers.dom().contains(n) implies z.control.fibers[n]==a.control.fibers.remove(actor)[n] by {
            assert(n!=actor);assert(c::registered(a.control,n));assert(a.control.fibers[n]==z.control.fibers[n]);
        }
        assert(z.control.fibers =~= a.control.fibers.remove(actor));
    }
}

pub open spec fn metadata<V>(a:s::State<V>,z:s::State<V>,n:usize)->bool {
    &&& c::interface_same(a.control.fibers[n],z.control.fibers[n])
    &&& a.effects[n]==z.effects[n]
    &&& (a.control.fibers[n].retired ==> z.control.fibers[n].retired)
}

pub proof fn forward_metadata<V>(a:s::State<V>,z:s::State<V>,actor:usize,n:usize)
    requires p::well_formed(a),s::registered(a,actor),s::registered(a,n),p::forward_map(a,z,actor),
    ensures s::registered(z,n),metadata(a,z,n),a.control.fibers[n].retired==z.control.fibers[n].retired,
{
    p::forward_preservation(a,z,actor);
    if !p::table_map(a,z,actor) {
        let child=choose|child:usize|p::child_map(a,z,actor,child);
        assert(child!=n);
    }
}

pub proof fn inverse_metadata<V>(a:s::State<V>,z:s::State<V>,actor:usize,n:usize)
    requires p::well_formed(a),s::registered(a,actor),s::registered(a,n),p::inverse_map(a,z,actor),
    ensures s::registered(z,n),metadata(a,z,n),
        !a.control.fibers[n].retired && z.control.fibers[n].retired ==> s::child_retire(a,z,n),
{
    p::inverse_preservation(a,z,actor);
    if !p::table_map(a,z,actor) {
        let child=choose|child:usize|s::child_retire(a,z,child);
        if child!=n {assert(a.control.fibers[n]==z.control.fibers[n]);}
    }
}

/// An inverse application with a child_retire transition along the real LIFO
/// path. This records before/after states, not a captured child-handle opcode.
pub open spec fn retires<V>(model:s::Model<V>,tokens:Seq<nat>,a:s::State<V>,n:usize)->bool
    decreases tokens.len(),
{
    tokens.len()>0 && {
        let next=(model.undo)(tokens.last(),a);
        s::child_retire(a,next,n) || retires(model,tokens.drop_last(),next,n)
    }
}

pub proof fn restore_metadata<V>(model:s::Model<V>,tokens:Seq<nat>,a:s::State<V>,actor:usize,n:usize)
    requires p::well_formed(a),s::registered(a,actor),s::registered(a,n),p::admissible_restore(model,tokens,a,actor),
    ensures s::registered(s::restore(model,tokens,a),n),metadata(a,s::restore(model,tokens,a),n),
        !a.control.fibers[n].retired && s::restore(model,tokens,a).control.fibers[n].retired ==> retires(model,tokens,a,n),
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let next=(model.undo)(tokens.last(),a);
        inverse_metadata(a,next,actor,n);
        p::inverse_preservation(a,next,actor);
        restore_metadata(model,tokens.drop_last(),next,actor,n);
    }
}

/// Lemma 59(5), including nested child retirement within L-Unload.
pub proof fn step_metadata<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,actor:usize,rule:c::Rule,n:usize)
    requires p::well_formed(a),s::step(model,a,z,actor,rule),p::admissible_step(model,a,z,actor,rule),
        s::registered(a,n),s::registered(z,n),
    ensures metadata(a,z,n),
        !a.control.fibers[n].retired && z.control.fibers[n].retired ==>
            (rule==c::Rule::Retire && actor==n)
            || (rule==c::Rule::Unload && retires(model,a.accumulators[actor],a,n)),
{
    if e::lands(model,a,z,actor,rule) {
        forward_metadata(a,(model.iterate)(actor,a.iterators[actor].unwrap(),a).state,actor,n);
    } else if rule==c::Rule::Unload {
        restore_metadata(model,a.accumulators[actor],a,actor,n);
    }
}

/// A continuous registry lifetime, even across reactivation, preserves the
/// insertion metadata; removal and later reuse deliberately start a new one.
pub proof fn metadata_lifetime<V>(model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>,n:usize,b:int,t:int)
    requires crate::lifecycle_ordering::trace(model,states,labels),0<=b<=t<states.len(),
        forall|i:int| b<=i<=t ==> s::registered(states[i],n),
    ensures metadata(states[b],states[t],n),
    decreases t-b,
{
    if t>b {
        p::execution_preservation(model,states,labels);
        metadata_lifetime(model,states,labels,n,b,t-1);
        step_metadata(model,states[t-1],states[t],labels[t-1].0,labels[t-1].1,n);
    }
}

/// Every newly registered entry has a concrete insertion source, including a
/// child inserted inside a landed iterator before its outer lifecycle edit.
pub proof fn entry_origin<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,actor:usize,rule:c::Rule,n:usize)
    requires p::well_formed(a),s::step(model,a,z,actor,rule),p::admissible_step(model,a,z,actor,rule),
        !s::registered(a,n),s::registered(z,n),
    ensures (rule==c::Rule::Insert && actor==n && p::insert_map(a,z,n))
        || (e::lands(model,a,z,actor,rule)
            && p::child_map(a,(model.iterate)(actor,a.iterators[actor].unwrap(),a).state,actor,n)),
{
    if e::lands(model,a,z,actor,rule) {
        let next=(model.iterate)(actor,a.iterators[actor].unwrap(),a).state;
        assert(p::forward_map(a,next,actor));
        assert(actor!=n);
        assert(s::registered(next,n));
        assert(!p::table_map(a,next,actor));
        let child=choose|child:usize|p::child_map(a,next,actor,child);
        assert(child==n);
    } else if rule==c::Rule::Unload {
        p::restore_preservation(model,a.accumulators[actor],a,actor);
    }
}

/// The nonempty intersection in Lemma 59(1) follows from actual inequality of
/// the finite/infinite maps, rather than being an extra footprint premise.
pub proof fn foreign_change_key<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,actor:usize,rule:c::Rule,n:usize)
    requires p::well_formed(a),s::step(model,a,z,actor,rule),p::admissible_step(model,a,z,actor,rule),
        s::registered(a,n),actor!=n,a.tables[n]!=z.tables[n],
    ensures exists|key:crate::Port| a.tables[n].dom().contains(key)
        && a.control.fibers[actor].dependencies.contains(key) && a.tables[n][key]!=z.tables[n][key],
{
    crate::lifecycle_ordering::foreign_table_step(model,a,z,actor,rule,n);
    if forall|key:crate::Port| a.tables[n].dom().contains(key) ==> a.tables[n][key]==z.tables[n][key] {
        assert(a.tables[n] =~= z.tables[n]);
    }
    let key=choose|key:crate::Port|a.tables[n].dom().contains(key) && a.tables[n][key]!=z.tables[n][key];
    assert(a.control.fibers[actor].dependencies.contains(key));
}

} // verus!
