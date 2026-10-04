//! Episode boundaries and dependency lifetime in the full nine-rule semantics.
//!
//! Intermediate invariants follow from actual primitive admissibility, including
//! child creation and retirement. Active providers may publish partial tables;
//! the particular committed key must survive until its consumer has unloaded.
#[cfg(verus_keep_ghost)]
use crate::{
    entangled as e, preservation as p, refinement as c, semantics as s, Binding, Phase, Port,
};
use vstd::prelude::*;

verus! {

pub open spec fn installed<V>(a:s::State<V>,n:usize)->bool {
    s::registered(a,n) && a.control.fibers[n].phase!=Phase::Inactive
}

/// Definition 58, including an open final episode of a finite trace.
pub open spec fn episode<V>(states:Seq<s::State<V>>,n:usize,begin:int,end:int)->bool {
    &&& 0<begin<=end<states.len()
    &&& !installed(states[begin-1],n)
    &&& forall|t:int| begin<=t<=end ==> installed(states[t],n)
    &&& (end+1<states.len() ==> !installed(states[end+1],n))
}

pub open spec fn trace<V>(model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>)->bool {
    p::execution(model,states,labels) && p::well_formed(states.first())
}

/// Primitive frames preserve installation, including names absent initially:
/// their only permitted new entries are Inactive. Instantiate that clause at
/// the queried name before reasoning about the outer lifecycle edit.
proof fn primitive_installation<V>(a:s::State<V>,z:s::State<V>,n:usize)
    requires p::installation_frame(a,z),
    ensures installed(a,n)==installed(z,n),
        installed(a,n) ==> a.control.fibers[n].phase==z.control.fibers[n].phase,
{
    if s::registered(a,n) {
        assert(s::registered(z,n));
        assert(a.control.fibers[n].phase==z.control.fibers[n].phase);
    } else if s::registered(z,n) {
        assert(z.control.fibers[n].phase==Phase::Inactive);
    }
}

/// Only the actor's outer Begin/Unload edits change installed status. Nested
/// child primitives create Inactive entries or change retirement alone.
pub proof fn installation_step<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,actor:usize,rule:c::Rule,n:usize)
    requires p::well_formed(a),s::step(model,a,z,actor,rule),p::admissible_step(model,a,z,actor,rule),
    ensures !installed(a,n) && installed(z,n) ==> actor==n && rule==c::Rule::Begin && z.control.fibers[n].phase==Phase::Loading,
        installed(a,n) && !installed(z,n) ==> actor==n && rule==c::Rule::Unload,
        installed(a,n) && installed(z,n) ==> a.control.fibers[n].committed==z.control.fibers[n].committed,
        actor!=n && installed(a,n) ==> installed(z,n) && a.control.fibers[n].phase==z.control.fibers[n].phase,
{
    if e::lands(model,a,z,actor,rule) {
        let yielded=(model.iterate)(actor,a.iterators[actor].unwrap(),a);
        p::forward_preservation(a,yielded.state,actor);
        primitive_installation(a,yielded.state,n);
        assert(s::registered(yielded.state,actor));
        if actor==n {
            assert(installed(a,n));
            assert(installed(z,n));
        } else {
            assert(s::registered(z,n)==s::registered(yielded.state,n));
            if s::registered(yielded.state,n) {
                assert(z.control.fibers[n]==yielded.state.control.fibers[n]);
            }
        }
    } else if rule==c::Rule::Unload {
        let recovered=s::restore(model,a.accumulators[actor],a);
        p::restore_preservation(model,a.accumulators[actor],a,actor);
        primitive_installation(a,recovered,n);
        if actor==n {
            assert(installed(a,n));
            assert(!installed(z,n));
        } else {
            assert(s::registered(z,n)==s::registered(recovered,n));
            if s::registered(recovered,n) {
                assert(z.control.fibers[n]==recovered.control.fibers[n]);
            }
        }
    } else {
        match rule {
            c::Rule::Insert | c::Rule::Retire | c::Rule::Remove => {
                assert(c::step(a.control,z.control,actor,rule));
                assert(c::frame(a.control,z.control,actor));
                if actor!=n {
                    assert(s::registered(a,n)==s::registered(z,n));
                    if s::registered(a,n) {
                        assert(a.control.fibers[n]==z.control.fibers[n]);
                    }
                }
            },
            c::Rule::Begin | c::Rule::Divert | c::Rule::Leave => {
                // Here Divert is its immediate branch; landed Divert was
                // handled above with the actual primitive frame.
                assert(s::registered(a,actor));
                if actor!=n {
                    assert(s::registered(a,n)==s::registered(z,n));
                    if s::registered(a,n) {
                        assert(a.control.fibers[n]==z.control.fibers[n]);
                    }
                }
            },
            _ => {assert(false);},
        }
    }
    if installed(a,n) && installed(z,n) {e::actual_accumulator_step(model,a,z,actor,rule,n);}
}

pub proof fn episode_boundaries<V>(model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>,n:usize,b:int,u:int)
    requires trace(model,states,labels),episode(states,n,b,u),
    ensures labels[b-1]==(n,c::Rule::Begin),states[b].control.fibers[n].phase==Phase::Loading,
        u<labels.len() ==> labels[u]==(n,c::Rule::Unload),
{
    p::execution_preservation(model,states,labels);
    assert(installed(states[b],n));
    installation_step(model,states[b-1],states[b],labels[b-1].0,labels[b-1].1,n);
    if u<labels.len() {
        assert(installed(states[u],n));
        installation_step(model,states[u],states[u+1],labels[u].0,labels[u].1,n);
    }
}

pub proof fn committed_prefix<V>(model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>,n:usize,b:int,t:int)
    requires trace(model,states,labels),0<=b<=t<states.len(),
        forall|i:int| b<=i<=t ==> installed(states[i],n),
    ensures states[t].control.fibers[n].committed==states[b].control.fibers[n].committed,
    decreases t-b,
{
    if t>b {
        committed_prefix(model,states,labels,n,b,t-1);
        p::execution_preservation(model,states,labels);
        installation_step(model,states[t-1],states[t],labels[t-1].0,labels[t-1].1,n);
    }
}

/// Theorem 70's first assertion uses actual publication, not declaration alone.
pub proof fn begin_provided<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,actor:usize)
    requires s::step(model,a,z,actor,c::Rule::Begin),
    ensures forall|k:Port| a.control.fibers[actor].dependencies.contains(k) ==>
        exists|provider:usize| #[trigger] s::publishes(a,k,provider),
{
    let view=z.control.fibers[actor].committed;
    assert(s::target(a,actor,view));
    assert forall|k:Port| a.control.fibers[actor].dependencies.contains(k) implies
        exists|provider:usize| #[trigger] s::publishes(a,k,provider) by {
        let binding=choose|b:Binding| view.contains(b) && b.key==k.key && b.realm==k.realm;
        assert(s::publishes(a,k,binding.provider));
    }
}

/// A foreign primitive may change values only at the actor's dependency keys.
pub open spec fn table_frame<V>(a:s::State<V>,z:s::State<V>,actor:usize,n:usize)->bool {
    &&& s::registered(z,n)
    &&& a.tables[n].dom()==z.tables[n].dom()
    &&& forall|key:Port| a.tables[n].dom().contains(key) && !a.control.fibers[actor].dependencies.contains(key)
        ==> a.tables[n][key]==z.tables[n][key]
}

pub proof fn forward_table_frame<V>(a:s::State<V>,z:s::State<V>,actor:usize,n:usize)
    requires p::well_formed(a),s::registered(a,actor),s::registered(a,n),actor!=n,p::forward_map(a,z,actor),
    ensures table_frame(a,z,actor,n),
{
    p::forward_preservation(a,z,actor);
    if !p::table_map(a,z,actor) {
        let child=choose|child:usize|p::child_map(a,z,actor,child);
        assert(child!=n);
    }
}

pub proof fn inverse_table_frame<V>(a:s::State<V>,z:s::State<V>,actor:usize,n:usize)
    requires p::well_formed(a),s::registered(a,actor),s::registered(a,n),actor!=n,p::inverse_map(a,z,actor),
    ensures table_frame(a,z,actor,n),
{
    p::inverse_preservation(a,z,actor);
}

pub proof fn restore_table_frame<V>(model:s::Model<V>,tokens:Seq<nat>,a:s::State<V>,actor:usize,n:usize)
    requires p::well_formed(a),s::registered(a,actor),s::registered(a,n),actor!=n,p::admissible_restore(model,tokens,a,actor),
    ensures table_frame(a,s::restore(model,tokens,a),actor,n),
    decreases tokens.len(),
{
    if tokens.len()>0 {
        let next=(model.undo)(tokens.last(),a);
        inverse_table_frame(a,next,actor,n);
        p::inverse_preservation(a,next,actor);
        restore_table_frame(model,tokens.drop_last(),next,actor,n);
        assert forall|key:Port| a.tables[n].dom().contains(key) && !a.control.fibers[actor].dependencies.contains(key)
            implies a.tables[n][key]==s::restore(model,tokens,a).tables[n][key] by {
            assert(next.tables[n].dom().contains(key));
            assert(!next.control.fibers[actor].dependencies.contains(key));
        }
    }
}

/// Lemma 59's table clause, including a foreign Unload's entire inverse stack.
pub proof fn foreign_table_step<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,actor:usize,rule:c::Rule,n:usize)
    requires p::well_formed(a),s::step(model,a,z,actor,rule),p::admissible_step(model,a,z,actor,rule),
        s::registered(a,n),actor!=n,
    ensures table_frame(a,z,actor,n),
{
    if e::lands(model,a,z,actor,rule) {
        let next=(model.iterate)(actor,a.iterators[actor].unwrap(),a).state;
        forward_table_frame(a,next,actor,n);
    } else if rule==c::Rule::Unload {
        restore_table_frame(model,a.accumulators[actor],a,actor,n);
    }
}

/// Pinning fixes the whole provider domain, not only one requested key. Value
/// movement remains possible, with the acting fiber declaring each changed key.
pub proof fn pinned_table_step<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,actor:usize,rule:c::Rule,consumer:usize,binding:Binding)
    requires p::well_formed(a),s::step(model,a,z,actor,rule),p::admissible_step(model,a,z,actor,rule),
        installed(a,consumer),a.control.fibers[consumer].committed.contains(binding),
        a.control.fibers[binding.provider].phase==Phase::Active || a.control.fibers[binding.provider].phase==Phase::Unloading,
    ensures s::registered(z,binding.provider),a.tables[binding.provider].dom()==z.tables[binding.provider].dom(),
        z.control.fibers[binding.provider].phase==Phase::Active || z.control.fibers[binding.provider].phase==Phase::Unloading,
        forall|key:Port| a.tables[binding.provider].dom().contains(key) && a.tables[binding.provider][key]!=z.tables[binding.provider][key]
            ==> actor!=binding.provider && a.control.fibers[actor].dependencies.contains(key),
{
    e::pinned_provider_phase_step(model,a,z,actor,rule,consumer,binding);
    if actor!=binding.provider {
        foreign_table_step(model,a,z,actor,rule,binding.provider);
    } else {
        assert(rule==c::Rule::Retire || rule==c::Rule::Leave);
        assert(a.tables==z.tables);
    }
}

pub proof fn pinned_prefix<V>(model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>,consumer:usize,binding:Binding,b:int,t:int)
    requires trace(model,states,labels),0<=b<=t<states.len(),
        forall|i:int| b<=i<=t ==> installed(states[i],consumer),
        states[b].control.fibers[consumer].committed.contains(binding),
        states[b].control.fibers[binding.provider].phase==Phase::Active,
    ensures s::registered(states[t],binding.provider),
        states[t].control.fibers[binding.provider].phase==Phase::Active || states[t].control.fibers[binding.provider].phase==Phase::Unloading,
        states[t].tables[binding.provider].dom()==states[b].tables[binding.provider].dom(),
    decreases t-b,
{
    p::execution_preservation(model,states,labels);
    if t>b {
        pinned_prefix(model,states,labels,consumer,binding,b,t-1);
        committed_prefix(model,states,labels,consumer,b,t-1);
        pinned_table_step(model,states[t-1],states[t],labels[t-1].0,labels[t-1].1,consumer,binding);
    }
}

/// Theorem 70(1,3): derive both the frozen commitment and every historical
/// binding-presence/write condition from the opening Begin and real full trace.
pub proof fn dependency_lifetime<V>(model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>,consumer:usize,binding:Binding,b:int,u:int)
    requires trace(model,states,labels),episode(states,consumer,b,u),
        states[b].control.fibers[consumer].committed.contains(binding),
    ensures forall|t:int| b<=t<=u ==> {
        &&& states[t].control.fibers[consumer].committed==states[b].control.fibers[consumer].committed
        &&& s::registered(states[t],binding.provider)
        &&& (states[t].control.fibers[binding.provider].phase==Phase::Active || states[t].control.fibers[binding.provider].phase==Phase::Unloading)
        &&& states[t].tables[binding.provider].dom()==states[b].tables[binding.provider].dom()
        &&& states[t].tables[binding.provider].dom().contains(Port{key:binding.key,realm:binding.realm})
        &&& (t<labels.len() ==> {
            &&& !(labels[t]==(binding.provider,c::Rule::Unload))
            &&& forall|key:Port| states[t].tables[binding.provider].dom().contains(key)
                && states[t].tables[binding.provider][key]!=states[t+1].tables[binding.provider][key]
                ==> labels[t].0!=binding.provider && states[t].control.fibers[labels[t].0].dependencies.contains(key)
        })
    },
{
    p::execution_preservation(model,states,labels);
    episode_boundaries(model,states,labels,consumer,b,u);
    e::begin_establishes_provider_pin(model,states[b-1],states[b],consumer,binding);
    assert forall|t:int| b<=t<=u implies {
        &&& states[t].control.fibers[consumer].committed==states[b].control.fibers[consumer].committed
        &&& s::registered(states[t],binding.provider)
        &&& (states[t].control.fibers[binding.provider].phase==Phase::Active || states[t].control.fibers[binding.provider].phase==Phase::Unloading)
        &&& states[t].tables[binding.provider].dom()==states[b].tables[binding.provider].dom()
        &&& states[t].tables[binding.provider].dom().contains(Port{key:binding.key,realm:binding.realm})
        &&& (t<labels.len() ==> {
            &&& !(labels[t]==(binding.provider,c::Rule::Unload))
            &&& forall|key:Port| states[t].tables[binding.provider].dom().contains(key)
                && states[t].tables[binding.provider][key]!=states[t+1].tables[binding.provider][key]
                ==> labels[t].0!=binding.provider && states[t].control.fibers[labels[t].0].dependencies.contains(key)
        })
    } by {
        committed_prefix(model,states,labels,consumer,b,t);
        pinned_prefix(model,states,labels,consumer,binding,b,t);
        if t<labels.len() {
            pinned_table_step(model,states[t],states[t+1],labels[t].0,labels[t].1,consumer,binding);
            e::committed_provider_blocks_unload(model,states[t],states[t+1],consumer,binding.provider,binding);
        }
    }
}

/// Theorem 70(2): the containing provider episode starts strictly earlier and,
/// when it closes within this trace, finishes strictly after the consumer's.
pub proof fn episode_order<V>(model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>,consumer:usize,binding:Binding,b:int,u:int,pb:int,pu:int)
    requires trace(model,states,labels),episode(states,consumer,b,u),
        states[b].control.fibers[consumer].committed.contains(binding),
        episode(states,binding.provider,pb,pu),pb<=b<=pu,
    ensures pb<b,pu<labels.len() ==> u<pu,
{
    episode_boundaries(model,states,labels,consumer,b,u);
    episode_boundaries(model,states,labels,binding.provider,pb,pu);
    p::execution_preservation(model,states,labels);
    e::begin_establishes_provider_pin(model,states[b-1],states[b],consumer,binding);
    if pb==b {assert(states[b].control.fibers[binding.provider].phase==Phase::Loading);}
    if pu<labels.len() && pu<=u {
        dependency_lifetime(model,states,labels,consumer,binding,b,u);
        assert(labels[pu]==(binding.provider,c::Rule::Unload));
        assert(!(labels[pu]==(binding.provider,c::Rule::Unload)));
    }
}

/// Within one installed episode, neither Active nor Unloading can re-enter
/// Loading. Exiting Loading is the actual Finish/Divert choice, including the
/// branch where a Divert aborts rather than landing an operation.
pub proof fn phase_step<V>(model:s::Model<V>,a:s::State<V>,z:s::State<V>,actor:usize,rule:c::Rule,n:usize)
    requires p::well_formed(a),s::step(model,a,z,actor,rule),p::admissible_step(model,a,z,actor,rule),
        installed(a,n),installed(z,n),
    ensures a.control.fibers[n].phase!=Phase::Loading ==> z.control.fibers[n].phase!=Phase::Loading,
        a.control.fibers[n].phase==Phase::Unloading ==> z.control.fibers[n].phase==Phase::Unloading,
        a.control.fibers[n].phase==Phase::Loading && z.control.fibers[n].phase!=Phase::Loading ==> {
            &&& actor==n
            &&& ((rule==c::Rule::Finish && z.control.fibers[n].phase==Phase::Active)
                || (rule==c::Rule::Divert && z.control.fibers[n].phase==Phase::Unloading))
        },
{
    installation_step(model,a,z,actor,rule,n);
    if e::lands(model,a,z,actor,rule) {
        p::forward_preservation(a,(model.iterate)(actor,a.iterators[actor].unwrap(),a).state,actor);
    } else if rule==c::Rule::Unload {
        p::restore_preservation(model,a.accumulators[actor],a,actor);
    }
}

pub proof fn no_loading_reentry<V>(model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>,n:usize,b:int,t:int)
    requires trace(model,states,labels),0<=b<=t<states.len(),
        forall|i:int| b<=i<=t ==> installed(states[i],n),
        states[b].control.fibers[n].phase!=Phase::Loading,
    ensures states[t].control.fibers[n].phase!=Phase::Loading,
        states[b].control.fibers[n].phase==Phase::Unloading ==> states[t].control.fibers[n].phase==Phase::Unloading,
    decreases t-b,
{
    if t>b {
        no_loading_reentry(model,states,labels,n,b,t-1);
        p::execution_preservation(model,states,labels);
        phase_step(model,states[t-1],states[t],labels[t-1].0,labels[t-1].1,n);
    }
}

/// Locate the final Loading state by inspecting the actual finite history.
pub open spec fn loading_end<V>(states:Seq<s::State<V>>,n:usize,b:int,u:int)->int
    decreases if b<=u {u-b} else {0},
{
    if b<u && states[b+1].control.fibers[n].phase==Phase::Loading {loading_end(states,n,b+1,u)} else {b}
}

pub proof fn loading_end_bounds<V>(states:Seq<s::State<V>>,n:usize,b:int,u:int)
    requires 0<=b<=u<states.len(),states[b].control.fibers[n].phase==Phase::Loading,
    ensures b<=loading_end(states,n,b,u)<=u,
        forall|t:int| b<=t<=loading_end(states,n,b,u) ==> states[t].control.fibers[n].phase==Phase::Loading,
        loading_end(states,n,b,u)<u ==> states[loading_end(states,n,b,u)+1].control.fibers[n].phase!=Phase::Loading,
    decreases u-b,
{
    if b<u && states[b+1].control.fibers[n].phase==Phase::Loading {
        loading_end_bounds(states,n,b+1,u);
    }
}

pub proof fn loading_shape<V>(model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>,n:usize,b:int,u:int)
    requires trace(model,states,labels),episode(states,n,b,u),
    ensures {
        let r=loading_end(states,n,b,u);
        &&& b<=r<=u
        &&& forall|t:int| b<=t<=u ==> (states[t].control.fibers[n].phase==Phase::Loading)==(t<=r)
        &&& (r<u ==> {
            &&& ((labels[r]==(n,c::Rule::Finish) && states[r+1].control.fibers[n].phase==Phase::Active)
                || (labels[r]==(n,c::Rule::Divert) && states[r+1].control.fibers[n].phase==Phase::Unloading))
            &&& states[r+1].control.fibers[n].committed==states[b].control.fibers[n].committed
        })
    },
{
    episode_boundaries(model,states,labels,n,b,u);
    loading_end_bounds(states,n,b,u);
    p::execution_preservation(model,states,labels);
    let r=loading_end(states,n,b,u);
    assert forall|t:int| b<=t<=u implies (states[t].control.fibers[n].phase==Phase::Loading)==(t<=r) by {
        if t>r {no_loading_reentry(model,states,labels,n,r+1,t);}
    }
    if r<u {
        phase_step(model,states[r],states[r+1],labels[r].0,labels[r].1,n);
        committed_prefix(model,states,labels,n,b,r+1);
    }
}

pub proof fn iteration_resolution<V>(model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>,n:usize,b:int,t:int)
    requires trace(model,states,labels),0<=b<=t<labels.len(),
        forall|i:int| b<=i<=t ==> installed(states[i],n),
        labels[t]==(n,c::Rule::Iter) || labels[t]==(n,c::Rule::Finish),
    ensures s::target(states[t],n,states[b].control.fibers[n].committed),
{
    committed_prefix(model,states,labels,n,b,t);
    assert(s::step(model,states[t],states[t+1],n,labels[t].1));
    assert(s::coherent(states[t],n));
}

/// Theorem 71's phase and resolution assertions for arbitrary full traces.
/// This does not infer eventual Unload from a finite prefix or from an arbitrary
/// callback; terminal recovery additionally needs its actual recovery theorem.
pub proof fn coherent_loading_interval<V>(model:s::Model<V>,states:Seq<s::State<V>>,labels:Seq<(usize,c::Rule)>,n:usize,b:int,u:int)
    requires trace(model,states,labels),episode(states,n,b,u),
    ensures {
        let r=loading_end(states,n,b,u);
        &&& b<=r<=u
        &&& forall|t:int| b<=t<=u ==> (states[t].control.fibers[n].phase==Phase::Loading)==(t<=r)
        &&& forall|t:int| b<=t<=r && t<labels.len()
            && (labels[t]==(n,c::Rule::Iter) || labels[t]==(n,c::Rule::Finish))
            ==> s::target(states[t],n,states[b].control.fibers[n].committed)
        &&& (r<u ==> {
            &&& ((labels[r]==(n,c::Rule::Finish) && states[r+1].control.fibers[n].phase==Phase::Active)
                || (labels[r]==(n,c::Rule::Divert) && states[r+1].control.fibers[n].phase==Phase::Unloading))
            &&& states[r+1].control.fibers[n].committed==states[b].control.fibers[n].committed
        })
    },
{
    loading_shape(model,states,labels,n,b,u);
    let r=loading_end(states,n,b,u);
    assert forall|t:int| b<=t<=r && t<labels.len()
        && (labels[t]==(n,c::Rule::Iter) || labels[t]==(n,c::Rule::Finish))
        implies s::target(states[t],n,states[b].control.fibers[n].committed) by {
        iteration_resolution(model,states,labels,n,b,t);
    }
}

} // verus!
